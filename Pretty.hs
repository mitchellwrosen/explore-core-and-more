module Pretty where

import Control.Monad.Writer.CPS qualified as Writer
import Data.Char (isUpper)
import Data.Foldable (fold)
import Data.Function ((&))
import Data.Maybe (mapMaybe)
import Data.Monoid (Endo (..))
import Data.String (IsString (fromString))
import Data.Text (Text)
import Data.Text qualified as Text
import Expr
import Prettyprinter
import Prettyprinter.Render.Terminal
import Type

omitTypes :: Bool
omitTypes = True

liftLocalDefinitions :: Bool
liftLocalDefinitions = False

-- show matches like: Foobar _ _ <- !!sup
showRedundantPatterns :: Bool
showRedundantPatterns = False

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
  Letrec bindings -> renderLayer context (map Let bindings)
  -- FIXME reduce duplication, this check mark tweaking should only happen once no?
  Join (JoinPoint (N ident i) bindings defn) -> renderDefn context (N (ident <> "✓") i) (ELam bindings defn)
  Joinrec points -> renderLayer context (map Join points)

renderDefn :: [Text] -> N Text -> Expr (N Text) -> Accum ([Text], [LocalDefn]) (Doc Ann)
renderDefn context ident defn =
  case runAccum (defnDoc (zeroth (Text.intercalate "|" (context ++ [showVar ident]))) defn) of
    (doc, []) -> pure doc
    (doc, localDefns) -> do
      accum (context ++ [showVar ident], localDefns)
      pure doc

renderVar :: N Text -> Doc a
renderVar =
  pretty . showVar

showVar :: N Text -> Text
showVar = \case
  N s 0 -> unmangle s
  N s i -> unmangle s <> Text.pack (show i)
  where
    unmangle s
      | Text.isPrefixOf "$j_" s = Text.drop 3 s <> mathy "/joinpoint"
      | Text.isPrefixOf "$s" s = Text.drop 2 s <> mathy "/specialized"
      | Text.isPrefixOf "$w$j_" s = Text.drop 5 s <> mathy "/joinpoint/worker"
      | Text.isPrefixOf "$w" s = Text.drop 2 s <> mathy "/worker"
      | Text.isPrefixOf "C:" s = Text.drop 2 s <> mathy "Dict"
      | otherwise = s

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
            ( annotate AnnDefinition (renderVar ident)
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
  | Letrec [LetBinding (N Text)]
  | Join (JoinPoint (N Text))
  | Joinrec [JoinPoint (N Text)]

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
          N "()" i -> N (mathy "t") i
          N "(##)" i -> N (mathy "t#") i
          _ -> name0
      ident1 = ident0 {name = name1}

      isConstructor :: N Text -> Bool
      isConstructor (N s _) =
        isUpper (Text.head s)
          || s == mathy "cons"
          || s == mathy "nil"
          || s == mathy "t"
          || s == mathy "t#"
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
      ( let verbose =
              let ignorable = \case
                    -- FIXME not actually ignorable for the purpose of understanding the meaning of a program, because
                    -- might bind tyvars here that we reference later
                    Tyvar _ _ -> True
                    Var ident _ ->
                      case ident of
                        N "_" _ -> True
                        _ -> False
                  treatAsIgnorable bindings =
                    if showRedundantPatterns
                      then False
                      else all ignorable bindings
               in case alternative of
                    ACon _con bindings -> not (treatAsIgnorable bindings)
                    ADef -> False
                    ALit _lit -> showRedundantPatterns
                    ATuple x y zs -> not (treatAsIgnorable (x : y : zs))
                    ATupleU xs -> not (treatAsIgnorable xs)
                    AUnit -> showRedundantPatterns
         in if verbose
              then
                alternativeDoc False alternative
                  <> " ← "
                  <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> scrutineeDoc))
              else group (annotate (AnnColor Red) "‼" <> scrutineeDoc)
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
      renderVar whnf
        <> ( -- don't even know if GHC will ever write 'case foo of _ {'
             case alternative of
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
          Just s -> renderVar s <> " ← " <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> scrutineeDoc))
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
                  ( renderVar s
                      <> " ← "
                      <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> scrutineeDoc))
                      <> hardline
                      <> annotate AnnKeyword "switch"
                  )
                  ( annotate AnnKeyword "switch"
                      <> space
                      <> renderVar s
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
          ((annotate AnnDefinition (renderVar ident) <> " = ...") <> hardline <> bodyDoc)
    else do
      letDoc <- letBindingDoc binding
      bodyDoc <- exprDoc body
      pure (parenify addParensIfSpaces (group letDoc <> hardline <> bodyDoc))

exprLetrecDoc :: Bool -> [LetBinding (N Text)] -> Expr (N Text) -> M (Doc Ann)
exprLetrecDoc addParensIfSpaces bindings body = do
  if liftLocalDefinitions
    then do
      accum (Letrec bindings)
      bodyDoc <- exprDoc body
      pure $
        parenify addParensIfSpaces $
          ( bindings
              & map (\(LetBinding ident _) -> annotate AnnDefinition (renderVar ident) <> " = ...")
              & punctuate hardline
              & fold
          )
            <> hardline
            <> bodyDoc
    else do
      letDocs <- traverse letBindingDoc bindings
      bodyDoc <- exprDoc body
      pure $
        parenify addParensIfSpaces $
          group (fold (punctuate hardline letDocs))
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
              JoinPoint (N ident i) _ _ -> annotate AnnDefinition (renderVar (N (ident <> "✓") i)) <> " = ..."
          )
            <> hardline
            <> bodyDoc
    else do
      pointDoc <- joinPointDoc point
      bodyDoc <- exprDoc body
      pure (parenify addParensIfSpaces (group pointDoc <> hardline <> bodyDoc))

exprJoinrecDoc :: Bool -> [JoinPoint (N Text)] -> Expr (N Text) -> M (Doc Ann)
exprJoinrecDoc addParensIfSpaces points body = do
  if liftLocalDefinitions
    then do
      accum (Joinrec points)
      bodyDoc <- exprDoc body
      pure $
        parenify addParensIfSpaces $
          ( points
              & map
                ( \(JoinPoint (N ident i) _ _) ->
                    annotate AnnDefinition (renderVar (N (ident <> "✓") i)) <> " = ..."
                )
              & punctuate hardline
              & fold
          )
            <> hardline
            <> bodyDoc
    else do
      pointDocs <- traverse joinPointDoc points
      bodyDoc <- exprDoc body
      pure $
        parenify addParensIfSpaces $
          group (fold (punctuate hardline pointDocs))
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
          Ident _package _modules (N "[]" _) -> varIdent (zeroth (mathy "nil"))
          Ident _package _modules (N ":" _) -> varIdent (zeroth (mathy "cons"))
          _ -> con0
  ADef -> annotate AnnPattern "𝘥𝘦𝘧𝘢𝘶𝘭𝘵"
  ALit lit -> annotate AnnPattern (litDoc lit)
  ATuple var0 var1 vars -> alternativeDoc addParensIfSpaces (ACon (varIdent (zeroth (mathy "t"))) (var0 : var1 : vars))
  ATupleU vars -> alternativeDoc addParensIfSpaces (ACon (varIdent (zeroth (mathy "t#"))) vars)
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
  renderVar name

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
  TConstraint {} -> error "TConstraint"
  TForall _ _ -> error "TForall"
  TFun _ _ -> error "TFun"
  TId ident -> pretty ident
  TTuple _ _ _ -> error "TTuple"
  TTupleU _ -> error "TTupleU"

varDoc :: Var (N Text) -> Doc Ann
varDoc = \case
  Tyvar var _kind -> annotate AnnType ("@" <> renderVar var)
  Var var _type -> renderVar var

eCons :: Expr (N Text)
eCons =
  EVar (zeroth (mathy "cons"))

eNil :: Expr (N Text)
eNil =
  EVar (zeroth (mathy "nil"))

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

mathy :: IsString s => [Char] -> s
mathy =
  fromString . map go
  where
    go = \case
      'a' -> '𝘢'
      'b' -> '𝘣'
      'c' -> '𝘤'
      'd' -> '𝘥'
      'e' -> '𝘦'
      'f' -> '𝘧'
      'g' -> '𝘨'
      'h' -> '𝘩'
      'i' -> '𝘪'
      'j' -> '𝘫'
      'k' -> '𝘬'
      'l' -> '𝘭'
      'm' -> '𝘮'
      'n' -> '𝘯'
      'o' -> '𝘰'
      'p' -> '𝘱'
      'q' -> '𝘲'
      'r' -> '𝘳'
      's' -> '𝘴'
      't' -> '𝘵'
      'u' -> '𝘶'
      'v' -> '𝘷'
      'w' -> '𝘸'
      'x' -> '𝘹'
      'y' -> '𝘺'
      'z' -> '𝘻'
      -- TODO rest of capital alphabet
      'D' -> '𝘋'
      c -> c

-- -- These derived variables have a prefix that no Haskell value could have
-- mkDataConWrapperOcc = mk_simple_deriv varName  "$W"
-- mkWorkerOcc         = mk_simple_deriv varName  "$w"
-- mkMatcherOcc        = mk_simple_deriv varName  "$m"
-- mkBuilderOcc        = mk_simple_deriv varName  "$b"
-- mkDefaultMethodOcc  = mk_simple_deriv varName  "$dm"
-- mkClassOpAuxOcc     = mk_simple_deriv varName  "$c"
-- mkDictOcc           = mk_simple_deriv varName  "$d"
-- mkIPOcc             = mk_simple_deriv varName  "$i"
-- mkSpecOcc           = mk_simple_deriv varName  "$s"
-- mkForeignExportOcc  = mk_simple_deriv varName  "$f"
-- mkRepEqOcc          = mk_simple_deriv tvName   "$r"   -- In RULES involving Coercible
-- mkClassDataConOcc   = mk_simple_deriv dataName "C:"   -- Data con for a class
-- mkNewTyCoOcc        = mk_simple_deriv tcName   "N:"   -- Coercion for newtypes
-- mkInstTyCoOcc       = mk_simple_deriv tcName   "D:"   -- Coercion for type functions
-- mkEqPredCoOcc       = mk_simple_deriv tcName   "$co"

-- -- Used in derived instances for the names of auxiliary bindings.
-- -- See Note [Auxiliary binders] in GHC.Tc.Deriv.Generate.
-- mkCon2TagOcc        = mk_simple_deriv varName  "$con2tag_"
-- mkTag2ConOcc        = mk_simple_deriv varName  "$tag2con_"
-- mkMaxTagOcc         = mk_simple_deriv varName  "$maxtag_"
-- mkDataTOcc          = mk_simple_deriv varName  "$t"
-- mkDataCOcc          = mk_simple_deriv varName  "$c"

-- -- TyConRepName stuff; see Note [Grand plan for Typeable] in GHC.Tc.Instance.Typeable
-- mkTyConRepOcc occ = mk_simple_deriv varName prefix occ
--   where
--     prefix | isDataOcc occ = "$tc'"
--            | otherwise     = "$tc"

-- -- Generic deriving mechanism
-- mkGenR   = mk_simple_deriv tcName "Rep_"
-- mkGen1R  = mk_simple_deriv tcName "Rep1_"

-- -- Overloaded record field selectors
-- mkRecFldSelOcc :: String -> OccName
-- mkRecFldSelOcc s = mk_deriv varName "$sel" [fsLit s]
