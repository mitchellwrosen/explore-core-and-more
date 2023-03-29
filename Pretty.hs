module Pretty where

import Control.Monad.Writer.CPS qualified as Writer
import Data.Char (isUpper)
import Data.Foldable (fold)
import Data.Function ((&))
import Data.Maybe (mapMaybe)
import Data.Monoid (Endo (..))
import Data.Text (Text)
import Data.Text qualified as Text
import Expr
import Prettyprinter
import Prettyprinter.Render.Terminal
import Type

omitTypes :: Bool
omitTypes = True

liftLocalDefinitions :: Bool
liftLocalDefinitions = True

-- TODO rename prettyDefn or something
prettyExpr :: Text -> Expr Text -> Text
prettyExpr ident defn =
  renderStrict (layoutPretty opts (styleAnn <$> doc))
  where
    opts = LayoutOptions {layoutPageWidth = AvailablePerLine 160 1}

    doc :: Doc Ann
    doc = render ident defn

render :: Text -> Expr Text -> Doc Ann
render ident defn =
  let (doc, layers) = runAccum (renderDefn [] ident defn)
   in loop doc layers
  where
    loop :: Doc Ann -> [([Text], [LocalDefn])] -> Doc Ann
    loop acc = \case
      [] -> acc
      (context, defns) : layers ->
        let (doc, moreLayers) = runAccum (renderLayer context defns)
         in loop (acc <> hardline <> hardline <> doc) (layers ++ moreLayers)

renderLayer :: [Text] -> [LocalDefn] -> Accum ([Text], [LocalDefn]) (Doc Ann)
renderLayer context localDefns = do
  localDefnDocs <- traverse (renderLocalDefn context) localDefns
  pure (fold (punctuate (hardline <> hardline) localDefnDocs))

renderLocalDefn :: [Text] -> LocalDefn -> Accum ([Text], [LocalDefn]) (Doc Ann)
renderLocalDefn context = \case
  Let (LetBinding ident defn) -> renderDefn context ident defn
  -- FIXME reduce duplication, this check mark tweaking should only happen once no?
  Join (JoinPoint ident bindings defn) -> renderDefn context (ident <> "✓") (ELam bindings defn)

renderDefn :: [Text] -> Text -> Expr Text -> Accum ([Text], [LocalDefn]) (Doc Ann)
renderDefn context ident defn =
  case runAccum (defnDoc (Text.intercalate "/" (context ++ [ident])) defn) of
    (doc, []) -> pure doc
    (doc, localDefns) -> do
      accum (context ++ [ident], localDefns)
      pure doc

data Ann
  = AnnColor Color
  | AnnConstructor
  | AnnPattern
  | AnnDefinition
  | AnnKeyword
  | AnnLiteral
  | AnnType

styleAnn :: Ann -> AnsiStyle
styleAnn = \case
  AnnColor c -> color c
  AnnConstructor -> color Cyan
  AnnPattern -> colorDull Yellow <> bold
  AnnDefinition -> color Green <> bold
  AnnKeyword -> bold
  AnnLiteral -> color Magenta
  AnnType -> color Blue

defnDoc :: Text -> Expr Text -> M (Doc Ann)
defnDoc ident = \case
  ELam bindings body -> go bindings body
  expr -> go [] expr
  where
    go :: [Var Text] -> Expr Text -> M (Doc Ann)
    go bindings body = do
      bodyDoc <- exprDoc body
      pure (group (hang 2 (annotate AnnDefinition (pretty ident) <> space <> bindingsDoc bindings <> line <> bodyDoc)))

bindingsDoc :: [Var Text] -> Doc Ann
bindingsDoc =
  (<> "=") . f . map varDoc . mungeVars
  where
    f = \case
      [] -> mempty
      bindings -> hsep bindings <> space

type M a =
  Accum LocalDefn a

type Accum w a =
  Writer.Writer (Endo [w]) a

runAccum :: Accum w a -> (a, [w])
runAccum m =
  let (x, ws) = Writer.runWriter m
   in (x, appEndo ws [])

accum :: w -> Accum w ()
accum w =
  Writer.tell (Endo (w :))

data LocalDefn
  = Let (LetBinding Text)
  | Join (JoinPoint Text)

exprDoc :: Expr Text -> M (Doc Ann)
exprDoc =
  exprDoc_ False

exprDoc_ :: Bool -> Expr Text -> M (Doc Ann)
exprDoc_ addParensIfSpaces = \case
  EId ident0@Ident {name = name0} ->
    pure do
      ( if isUpper (Text.head name1)
          || name1 == "𝘤𝘰𝘯𝘴"
          || name1 == "𝘯𝘪𝘭"
          || name1 == "𝘵"
          || name1 == "𝘵#"
          then annotate AnnConstructor
          else id
        )
        (identDoc ident1)
    where
      -- rename ghc-prim:GHC.Prim.(##) and ghc-prim:GHC.Tuple.() at print-time
      name1
        | name0 == "()" = "𝘵"
        | name0 == "(##)" = "𝘵#"
        | otherwise = name0
      ident1 = ident0 {name = name1}
  ELit lit -> pure (annotate AnnLiteral (litDoc lit))
  (slurpListExpr -> Just (expr, exprs)) ->
    if expr == eNil
      then exprDoc_ addParensIfSpaces eNil
      else exprDoc_ addParensIfSpaces (EApp eCons expr exprs)
  EApp EJump (EVar ident) zs -> exprAppDoc addParensIfSpaces (EVar (ident <> "✓")) zs
  EApp x y zs -> exprAppDoc addParensIfSpaces x (y : zs)
  ELam bindings body -> do
    bodyDoc <- exprDoc body
    pure $
      parenify addParensIfSpaces $
        nest 2 ("\\" <> hsep (map varDoc (mungeVars bindings)) <> " →" <> line <> bodyDoc)
  ECase scrutinee whnf alternatives -> exprCaseDoc addParensIfSpaces scrutinee whnf alternatives
  EJump -> error "EJump"
  ETy ty -> pure (annotate AnnType ("@" <> typeDoc_ True ty))
  ELet binding body -> exprLetDoc addParensIfSpaces binding body
  ELetrec bindings body -> exprLetrecDoc addParensIfSpaces bindings body
  EJoin point body -> exprJoinDoc addParensIfSpaces point body
  EJoinrec points body -> exprJoinrecDoc addParensIfSpaces points body
  ETuple x y zs -> exprDoc_ addParensIfSpaces (EApp (EVar "𝘵") x (y : zs))
  ETupleU (expr : exprs) -> exprDoc_ addParensIfSpaces (EApp (EVar "𝘵#") expr exprs)
  ETupleU exprs -> error ("ETupleU " ++ show exprs)

exprAppDoc :: Bool -> Expr Text -> [Expr Text] -> M (Doc Ann)
exprAppDoc addParensIfSpaces x ys = do
  let args = mapMaybe p ys
  docs <- traverse (exprDoc_ True) (x : args)
  pure (parenify (addParensIfSpaces && not (null args)) (group (nest 2 (vsep docs))))
  where
    p :: Expr Text -> Maybe (Expr Text)
    p expr =
      if omitTypes
        then case expr of
          ETy _ -> Nothing
          _ -> Just expr
        else Just expr

-- case <scrutinee> of {
--   <alternative> -> <body>
-- }
exprCaseDoc :: Bool -> Expr Text -> Maybe Text -> [(Alternative Text, Expr Text)] -> M (Doc Ann)
exprCaseDoc addParensIfSpaces scrutinee Nothing [(alternative, body)] = do
  scrutineeDoc <- exprDoc scrutinee
  bodyDoc <- exprDoc body
  pure $
    parenify addParensIfSpaces $
      ( case alternative of
          ADef -> group (annotate (AnnColor Red) "‼" <> scrutineeDoc)
          _ ->
            alternativeDoc False alternative
              <> " ← "
              <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> scrutineeDoc))
      )
        <> hardline
        <> bodyDoc
-- case scrutinee of whnf {
--   alternative -> body
-- }
exprCaseDoc addParensIfSpaces scrutinee (Just whnf) [(alternative, body)] = do
  scrutineeDoc <- exprDoc scrutinee
  bodyDoc <- exprDoc body
  pure $
    parenify addParensIfSpaces $
      pretty whnf
        <> ( case alternative of
               ADef -> mempty
               _ -> " = " <> alternativeDoc False alternative
           )
        <> " ← "
        <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> scrutineeDoc))
        <> hardline
        <> bodyDoc
-- case scrutinee of [whnf] {
-- }
exprCaseDoc addParensIfSpaces scrutinee whnf [] = do
  scrutineeDoc <- exprDoc scrutinee
  pure $
    parenify addParensIfSpaces $
      ( case whnf of
          Nothing -> group (annotate (AnnColor Red) "‼" <> scrutineeDoc)
          Just s -> pretty s <> " ← " <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> scrutineeDoc))
      )
-- case scrutinee of [whnf] {
--   alternative1 -> body1
--   alternative2 -> body2
-- }
exprCaseDoc addParensIfSpaces scrutinee whnf alternatives = do
  scrutineeDoc <- exprDoc scrutinee
  altsDoc <- alternativesDoc alternatives
  pure $
    parenify addParensIfSpaces $
      ( case whnf of
          Nothing ->
            group
              ( flatAlt
                  (annotate (AnnColor Red) "‼" <> scrutineeDoc <> hardline <> annotate AnnKeyword "switch")
                  ( annotate AnnKeyword "switch"
                      <> space
                      <> nest 2 (line' <> annotate (AnnColor Red) "‼" <> scrutineeDoc)
                  )
              )
          Just s ->
            group
              ( flatAlt
                  ( pretty s
                      <> " ← "
                      <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> scrutineeDoc))
                      <> hardline
                      <> annotate AnnKeyword "switch"
                  )
                  ( annotate AnnKeyword "switch"
                      <> space
                      <> pretty s
                      <> " = "
                      <> annotate (AnnColor Red) "‼"
                      <> scrutineeDoc
                  )
              )
      )
        <> hardline
        <> altsDoc

exprLetDoc :: Bool -> LetBinding Text -> Expr Text -> M (Doc Ann)
exprLetDoc addParensIfSpaces binding@(LetBinding ident _) body =
  if liftLocalDefinitions
    then do
      accum (Let binding)
      bodyDoc <- exprDoc body
      pure (parenify addParensIfSpaces ((annotate AnnDefinition (pretty ident) <> " = ...") <> hardline <> bodyDoc))
    else do
      letDoc <- letBindingDoc binding
      bodyDoc <- exprDoc body
      pure (parenify addParensIfSpaces (group letDoc <> hardline <> bodyDoc))

exprLetrecDoc :: Bool -> [LetBinding Text] -> Expr Text -> M (Doc Ann)
exprLetrecDoc addParensIfSpaces bindings body = do
  bodyDoc <- exprDoc body
  pure $
    parenify addParensIfSpaces $
      -- group (fold (punctuate hardline (map letBindingDoc bindings)))
      ( bindings
          & map (\(LetBinding ident _) -> annotate AnnDefinition (pretty ident) <> " = ...")
          & punctuate hardline
          & fold
      )
        <> hardline
        <> bodyDoc

exprJoinDoc :: Bool -> JoinPoint Text -> Expr Text -> M (Doc Ann)
exprJoinDoc addParensIfSpaces point body = do
  if liftLocalDefinitions
    then do
      accum (Join point)
      bodyDoc <- exprDoc body
      pure $
        parenify addParensIfSpaces $
          ( case point of
              JoinPoint ident _ _ -> annotate AnnDefinition (pretty (ident <> "✓")) <> " = ..."
          )
            <> hardline
            <> bodyDoc
    else do
      pointDoc <- joinPointDoc point
      bodyDoc <- exprDoc body
      pure (parenify addParensIfSpaces (group pointDoc <> hardline <> bodyDoc))

exprJoinrecDoc :: Bool -> [JoinPoint Text] -> Expr Text -> M (Doc Ann)
exprJoinrecDoc addParensIfSpaces points body = do
  bodyDoc <- exprDoc body
  pure $
    parenify addParensIfSpaces $
      -- group (fold (punctuate hardline (map joinPointDoc points)))
      ( points
          & map (\(JoinPoint ident _ _) -> annotate AnnDefinition (pretty (ident <> "✓")) <> " = ...")
          & punctuate hardline
          & fold
      )
        <> hardline
        <> bodyDoc

-- if this is a list, slurp it into its non-empty exprs
--
--   []         => Just (nil, [])
--   x : []     => Just (x, [nil])
--   x : xs     => Just (x, [xs])
--   x : y : ys => Just (x, y:ys)
slurpListExpr :: Expr Text -> Maybe (Expr Text, [Expr Text])
slurpListExpr = \case
  EApp (EVar "[]") (ETy _) [] -> Just (eNil, [])
  EApp (EVar ":") (ETy _) [lhs, rhs] -> Just (lhs, slurp rhs)
  _ -> Nothing
  where
    slurp :: Expr Text -> [Expr Text]
    slurp = \case
      EApp (EVar "[]") (ETy _) [] -> [eNil]
      EApp (EVar ":") (ETy _) [lhs, rhs] -> lhs : slurp rhs
      expr -> [expr]

alternativeDoc :: Bool -> Alternative Text -> Doc Ann
alternativeDoc addParensIfSpaces = \case
  ACon con0 vars ->
    parenify addParensIfSpaces $
      hsep (annotate AnnPattern (identDoc con) : map varDoc (mungeVars vars))
    where
      con =
        case identVar con0 of
          "[]" -> varIdent "𝘯𝘪𝘭"
          ":" -> varIdent "𝘤𝘰𝘯𝘴"
          _ -> con0
  ADef -> annotate AnnPattern "𝘥𝘦𝘧𝘢𝘶𝘭𝘵"
  ALit lit -> annotate AnnPattern (litDoc lit)
  ATuple var0 var1 vars -> alternativeDoc addParensIfSpaces (ACon (varIdent "𝘵") (var0 : var1 : vars))
  ATupleU vars -> alternativeDoc addParensIfSpaces (ACon (varIdent "𝘵#") vars)
  AUnit -> annotate AnnPattern "𝘵"

alternativesDoc :: [(Alternative Text, Expr Text)] -> M (Doc Ann)
alternativesDoc =
  go . moveDefaultToBottom
  where
    go :: [(Alternative Text, Expr Text)] -> M (Doc Ann)
    go alts = do
      altsDocs <- traverse f alts
      pure (fold (punctuate hardline altsDocs))

    f :: (Alternative Text, Expr Text) -> M (Doc Ann)
    f (alternative, body) = do
      bodyDoc <- exprDoc body
      pure $
        group $
          nest 2 $
            annotate AnnKeyword "case"
              <> space
              <> alternativeDoc False alternative
              <> " →"
              <> line
              <> bodyDoc

    moveDefaultToBottom :: [(Alternative var, Expr Text)] -> [(Alternative var, Expr Text)]
    moveDefaultToBottom = \case
      x@(ADef {}, _) : xs -> xs ++ [x]
      xs -> xs

identDoc :: Ident Text -> Doc Ann
identDoc Ident {name} =
  pretty name

letBindingDoc :: LetBinding Text -> M (Doc Ann)
letBindingDoc (LetBinding name defn) =
  defnDoc name defn

joinPointDoc :: JoinPoint Text -> M (Doc Ann)
joinPointDoc (JoinPoint name bindings defn) =
  defnDoc (name <> "✓") (ELam bindings defn)

-- remove "#" suffixes because they aren't very informative
litDoc :: Lit -> Doc Ann
litDoc = \case
  LInt n -> pretty n
  LIntU n -> pretty n
  LStrU s -> "\"" <> pretty (Text.replace "\"" "\\\"" s) <> "\""
  LWordU n -> pretty n
  LWord64U n -> pretty n

typeDoc :: Type -> Doc Ann
typeDoc =
  typeDoc_ False

typeDoc_ :: Bool -> Type -> Doc Ann
typeDoc_ addParensIfSpaces = \case
  TApp x y zs ->
    parenify addParensIfSpaces $
      group (nest 2 (vsep (map (typeDoc_ True) (x : y : zs))))
  TForall _ _ -> error "TForall"
  TFun _ _ -> error "TFun"
  TId ident -> pretty ident
  TTuple _ _ _ -> error "TTuple"

varDoc :: Var Text -> Doc Ann
varDoc = \case
  Tyvar var _kind -> annotate AnnType ("@" <> pretty var)
  Var var _type -> pretty var

eCons :: Expr Text
eCons =
  EVar "𝘤𝘰𝘯𝘴"

eNil :: Expr Text
eNil =
  EVar "𝘯𝘪𝘭"

parenify :: Bool -> Doc ann -> Doc ann
parenify addParensIfSpaces inner =
  if addParensIfSpaces
    then group (flatAlt ("( " <> align inner <> line <> ")") (parens inner))
    else group inner

mungeVars :: [Var Text] -> [Var Text]
mungeVars =
  if omitTypes
    then mapMaybe \case
      Tyvar {} -> Nothing
      var@Var {} -> Just var
    else id
