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
prettyExpr :: N Text -> Expr (N Text) -> Text
prettyExpr ident defn =
  renderStrict (layoutPretty opts (styleAnn <$> indent 2 doc))
  where
    opts = LayoutOptions {layoutPageWidth = AvailablePerLine 120 1}

    doc :: Doc Ann
    doc = render ident defn

render :: N Text -> Expr (N Text) -> Doc Ann
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
  Join (JoinPoint (N ident i) bindings defn) -> renderDefn context (N (ident <> "✓") i) (ELam bindings defn)

renderDefn :: [Text] -> N Text -> Expr (N Text) -> Accum ([Text], [LocalDefn]) (Doc Ann)
renderDefn context ident defn =
  case runAccum (defnDoc (zeroth (Text.intercalate "/" (context ++ [showN ident]))) defn) of
    (doc, []) -> pure doc
    (doc, localDefns) -> do
      accum (context ++ [showN ident], localDefns)
      pure doc

showN :: N Text -> Text
showN = \case
  N s 0 -> s
  N s i -> s <> Text.pack (show i)

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

defnDoc :: N Text -> Expr (N Text) -> M (Doc Ann)
defnDoc ident = \case
  ELam bindings body -> go bindings body
  expr -> go [] expr
  where
    go :: [Var (N Text)] -> Expr (N Text) -> M (Doc Ann)
    go bindings body = do
      bodyDoc <- exprDoc body
      pure $
        group $
          hang
            2
            ( annotate AnnDefinition (pretty (showN ident))
                <> space
                <> bindingsDoc bindings
                <> line
                <> bodyDoc
            )

bindingsDoc :: [Var (N Text)] -> Doc Ann
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
  = Let (LetBinding (N Text))
  | Join (JoinPoint (N Text))

exprDoc :: Expr (N Text) -> M (Doc Ann)
exprDoc =
  exprDoc_ False

exprDoc_ :: Bool -> Expr (N Text) -> M (Doc Ann)
exprDoc_ addParensIfSpaces = \case
  EId ident0@Ident {name = name0} ->
    pure ((if isConstructor name1 then annotate AnnConstructor else id) (identDoc ident1))
    where
      -- rename ghc-prim:GHC.Prim.(##) and ghc-prim:GHC.Tuple.() at print-time
      name1 =
        case name0 of
          N "()" i -> N "𝘵" i
          N "(##)" i -> N "𝘵#" i
          _ -> name0
      ident1 = ident0 {name = name1}

      isConstructor :: N Text -> Bool
      isConstructor (N s _) =
        isUpper (Text.head s)
          || s == "𝘤𝘰𝘯𝘴"
          || s == "𝘯𝘪𝘭"
          || s == "𝘵"
          || s == "𝘵#"
  ELit lit -> pure (annotate AnnLiteral (litDoc lit))
  (slurpListExpr -> Just (expr, exprs)) ->
    if expr == eNil
      then exprDoc_ addParensIfSpaces eNil
      else exprDoc_ addParensIfSpaces (EApp eCons expr exprs)
  EApp EJump (EVar (N ident i)) zs ->
    exprAppDoc1 addParensIfSpaces (annotate AnnKeyword "jump") (EVar (N (ident <> "✓") i) : zs)
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
  ETuple x y zs -> exprDoc_ addParensIfSpaces (EApp (EVar (zeroth "𝘵")) x (y : zs))
  ETupleU (expr : exprs) -> exprDoc_ addParensIfSpaces (EApp (EVar (zeroth "𝘵#")) expr exprs)
  ETupleU exprs -> error ("ETupleU " ++ show exprs)

exprAppDoc :: Bool -> Expr (N Text) -> [Expr (N Text)] -> M (Doc Ann)
exprAppDoc addParensIfSpaces x ys = do
  doc <- exprDoc_ True x
  exprAppDoc1 addParensIfSpaces doc ys

exprAppDoc1 :: Bool -> Doc Ann -> [Expr (N Text)] -> M (Doc Ann)
exprAppDoc1 addParensIfSpaces doc ys = do
  let args = mapMaybe p ys
  docs <- traverse (exprDoc_ True) args
  pure (parenify (addParensIfSpaces && not (null args)) (group (nest 2 (vsep (doc : docs)))))
  where
    p :: Expr (N Text) -> Maybe (Expr (N Text))
    p expr =
      if omitTypes
        then case expr of
          ETy _ -> Nothing
          _ -> Just expr
        else Just expr

-- case <scrutinee> of {
--   <alternative> -> <body>
-- }
exprCaseDoc :: Bool -> Expr (N Text) -> Maybe (N Text) -> [(Alternative (N Text), Expr (N Text))] -> M (Doc Ann)
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
      pretty (showN whnf)
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
          Just s -> pretty (showN s) <> " ← " <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> scrutineeDoc))
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
                  ( pretty (showN s)
                      <> " ← "
                      <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> scrutineeDoc))
                      <> hardline
                      <> annotate AnnKeyword "switch"
                  )
                  ( annotate AnnKeyword "switch"
                      <> space
                      <> pretty (showN s)
                      <> " = "
                      <> annotate (AnnColor Red) "‼"
                      <> scrutineeDoc
                  )
              )
      )
        <> hardline
        <> altsDoc

exprLetDoc :: Bool -> LetBinding (N Text) -> Expr (N Text) -> M (Doc Ann)
exprLetDoc addParensIfSpaces binding@(LetBinding ident _) body =
  if liftLocalDefinitions
    then do
      accum (Let binding)
      bodyDoc <- exprDoc body
      pure $
        parenify
          addParensIfSpaces
          ((annotate AnnDefinition (pretty (showN ident)) <> " = ...") <> hardline <> bodyDoc)
    else do
      letDoc <- letBindingDoc binding
      bodyDoc <- exprDoc body
      pure (parenify addParensIfSpaces (group letDoc <> hardline <> bodyDoc))

exprLetrecDoc :: Bool -> [LetBinding (N Text)] -> Expr (N Text) -> M (Doc Ann)
exprLetrecDoc addParensIfSpaces bindings body = do
  bodyDoc <- exprDoc body
  pure $
    parenify addParensIfSpaces $
      -- group (fold (punctuate hardline (map letBindingDoc bindings)))
      ( bindings
          & map (\(LetBinding ident _) -> annotate AnnDefinition (pretty (showN ident)) <> " = ...")
          & punctuate hardline
          & fold
      )
        <> hardline
        <> bodyDoc

exprJoinDoc :: Bool -> JoinPoint (N Text) -> Expr (N Text) -> M (Doc Ann)
exprJoinDoc addParensIfSpaces point body = do
  if liftLocalDefinitions
    then do
      accum (Join point)
      bodyDoc <- exprDoc body
      pure $
        parenify addParensIfSpaces $
          ( case point of
              JoinPoint (N ident i) _ _ -> annotate AnnDefinition (pretty (showN (N (ident <> "✓") i))) <> " = ..."
          )
            <> hardline
            <> bodyDoc
    else do
      pointDoc <- joinPointDoc point
      bodyDoc <- exprDoc body
      pure (parenify addParensIfSpaces (group pointDoc <> hardline <> bodyDoc))

exprJoinrecDoc :: Bool -> [JoinPoint (N Text)] -> Expr (N Text) -> M (Doc Ann)
exprJoinrecDoc addParensIfSpaces points body = do
  bodyDoc <- exprDoc body
  pure $
    parenify addParensIfSpaces $
      -- group (fold (punctuate hardline (map joinPointDoc points)))
      ( points
          & map
            ( \(JoinPoint (N ident i) _ _) ->
                annotate AnnDefinition (pretty (showN (N (ident <> "✓") i))) <> " = ..."
            )
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
slurpListExpr :: Expr (N Text) -> Maybe (Expr (N Text), [Expr (N Text)])
slurpListExpr = \case
  EApp (EVar (N "[]" _)) (ETy _) [] -> Just (eNil, [])
  EApp (EVar (N ":" _)) (ETy _) [lhs, rhs] -> Just (lhs, slurp rhs)
  _ -> Nothing
  where
    slurp :: Expr (N Text) -> [Expr (N Text)]
    slurp = \case
      EApp (EVar (N "[]" _)) (ETy _) [] -> [eNil]
      EApp (EVar (N ":" _)) (ETy _) [lhs, rhs] -> lhs : slurp rhs
      expr -> [expr]

alternativeDoc :: Bool -> Alternative (N Text) -> Doc Ann
alternativeDoc addParensIfSpaces = \case
  ACon con0 vars ->
    parenify addParensIfSpaces $
      hsep (annotate AnnPattern (identDoc con) : map varDoc (mungeVars vars))
    where
      con =
        case con0 of
          Ident _package _modules (N "[]" _) -> varIdent (zeroth "𝘯𝘪𝘭")
          Ident _package _modules (N ":" _) -> varIdent (zeroth "𝘤𝘰𝘯𝘴")
          _ -> con0
  ADef -> annotate AnnPattern "𝘥𝘦𝘧𝘢𝘶𝘭𝘵"
  ALit lit -> annotate AnnPattern (litDoc lit)
  ATuple var0 var1 vars -> alternativeDoc addParensIfSpaces (ACon (varIdent (zeroth "𝘵")) (var0 : var1 : vars))
  ATupleU vars -> alternativeDoc addParensIfSpaces (ACon (varIdent (zeroth "𝘵#")) vars)
  AUnit -> annotate AnnPattern "𝘵"

alternativesDoc :: [(Alternative (N Text), Expr (N Text))] -> M (Doc Ann)
alternativesDoc =
  go . moveDefaultToBottom
  where
    go :: [(Alternative (N Text), Expr (N Text))] -> M (Doc Ann)
    go alts = do
      altsDocs <- traverse f alts
      pure (fold (punctuate hardline altsDocs))

    f :: (Alternative (N Text), Expr (N Text)) -> M (Doc Ann)
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

    moveDefaultToBottom :: [(Alternative var, expr)] -> [(Alternative var, expr)]
    moveDefaultToBottom = \case
      x@(ADef {}, _) : xs -> xs ++ [x]
      xs -> xs

identDoc :: Ident (N Text) -> Doc Ann
identDoc Ident {name} =
  pretty (showN name)

letBindingDoc :: LetBinding (N Text) -> M (Doc Ann)
letBindingDoc (LetBinding name defn) =
  defnDoc name defn

joinPointDoc :: JoinPoint (N Text) -> M (Doc Ann)
joinPointDoc (JoinPoint (N name i) bindings defn) =
  defnDoc (N (name <> "✓") i) (ELam bindings defn)

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

varDoc :: Var (N Text) -> Doc Ann
varDoc = \case
  Tyvar var _kind -> annotate AnnType ("@" <> pretty (showN var))
  Var var _type -> pretty (showN var)

eCons :: Expr (N Text)
eCons =
  EVar (zeroth "𝘤𝘰𝘯𝘴")

eNil :: Expr (N Text)
eNil =
  EVar (zeroth "𝘯𝘪𝘭")

parenify :: Bool -> Doc ann -> Doc ann
parenify addParensIfSpaces inner =
  if addParensIfSpaces
    then group (flatAlt ("( " <> align inner <> line <> ")") (parens inner))
    else group inner

mungeVars :: [Var var] -> [Var var]
mungeVars =
  if omitTypes
    then mapMaybe \case
      Tyvar {} -> Nothing
      var@Var {} -> Just var
    else id
