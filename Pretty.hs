module Pretty where

import Data.Char (isUpper)
import Data.Foldable (fold)
import Data.Function ((&))
import Data.Maybe (mapMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import Expr
import Prettyprinter
import Prettyprinter.Render.Terminal
import Type

omitTypes :: Bool
omitTypes = True

prettyExpr :: Text -> Expr -> Text
prettyExpr ident expr =
  renderStrict (layoutPretty opts (styleAnn <$> defnDoc ident expr))
  where
    opts = LayoutOptions {layoutPageWidth = AvailablePerLine 160 1}

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

defnDoc :: Text -> Expr -> Doc Ann
defnDoc ident = \case
  ELam bindings body -> go bindings body
  expr -> go [] expr
  where
    go :: [Var] -> Expr -> Doc Ann
    go bindings body =
      group (hang 2 (annotate AnnDefinition (pretty ident) <> space <> bindingsDoc bindings <> line <> exprDoc body))

bindingsDoc :: [Var] -> Doc Ann
bindingsDoc =
  (<> "=") . f . map varDoc . mungeVars
  where
    f = \case
      [] -> mempty
      bindings -> hsep bindings <> space

exprDoc :: Expr -> Doc Ann
exprDoc =
  exprDoc_ False

pattern LastElement :: a -> [a]
pattern LastElement x <- (safeLast -> Just x)

safeLast :: [a] -> Maybe a
safeLast = \case
  [] -> Nothing
  [x] -> Just x
  _ : xs -> safeLast xs

exprDoc_ :: Bool -> Expr -> Doc Ann
exprDoc_ addParensIfSpaces = \case
  EId ident0@Ident {name = name0} ->
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
  ELit lit -> annotate AnnLiteral (litDoc lit)
  (slurpListExpr -> Just (expr, exprs)) ->
    if expr == eNil
      then exprDoc_ addParensIfSpaces eNil
      else exprDoc_ addParensIfSpaces (EApp eCons expr exprs)
  EApp EJump (EVar ident) zs -> exprAppDoc addParensIfSpaces (EVar (ident <> "✓")) zs
  EApp x y zs -> exprAppDoc addParensIfSpaces x (y : zs)
  ELam bindings body ->
    parenify addParensIfSpaces $
      nest 2 ("\\" <> hsep (map varDoc (mungeVars bindings)) <> " →" <> line <> exprDoc body)
  ECase scrutinee whnf alternatives -> exprCaseDoc addParensIfSpaces scrutinee whnf alternatives
  EJump -> error "EJump"
  ETy ty -> annotate AnnType ("@" <> typeDoc_ True ty)
  ELet binding body -> exprLetDoc addParensIfSpaces binding body
  ELetrec bindings body -> exprLetrecDoc addParensIfSpaces bindings body
  EJoin point body -> exprJoinDoc addParensIfSpaces point body
  EJoinrec points body -> exprJoinrecDoc addParensIfSpaces points body
  ETuple x y zs -> exprDoc_ addParensIfSpaces (EApp (EVar "𝘵") x (y : zs))
  ETupleU (expr : exprs) -> exprDoc_ addParensIfSpaces (EApp (EVar "𝘵#") expr exprs)
  ETupleU exprs -> error ("ETupleU " ++ show exprs)

exprAppDoc :: Bool -> Expr -> [Expr] -> Doc Ann
exprAppDoc addParensIfSpaces x ys =
  let args = mapMaybe p ys
   in parenify (addParensIfSpaces && not (null args)) $
        group (nest 2 (vsep (map (exprDoc_ True) (x : args))))
  where
    p :: Expr -> Maybe Expr
    p expr =
      if omitTypes
        then case expr of
          ETy _ -> Nothing
          _ -> Just expr
        else Just expr

-- case <scrutinee> of {
--   <alternative> -> <body>
-- }
exprCaseDoc :: Bool -> Expr -> Maybe Text -> [(Alternative, Expr)] -> Doc Ann
exprCaseDoc addParensIfSpaces scrutinee Nothing [(alternative, body)] =
  parenify addParensIfSpaces $
    ( case alternative of
        ADef -> group (annotate (AnnColor Red) "‼" <> exprDoc scrutinee)
        _ ->
          alternativeDoc False alternative
            <> " ← "
            <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> exprDoc scrutinee))
    )
      <> hardline
      <> exprDoc body
-- case scrutinee of whnf {
--   alternative -> body
-- }
exprCaseDoc addParensIfSpaces scrutinee (Just whnf) [(alternative, body)] =
  parenify addParensIfSpaces $
    pretty whnf
      <> ( case alternative of
             ADef -> mempty
             _ -> " = " <> alternativeDoc False alternative
         )
      <> " ← "
      <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> exprDoc scrutinee))
      <> hardline
      <> exprDoc body
-- case scrutinee of [whnf] {
-- }
exprCaseDoc addParensIfSpaces scrutinee whnf [] =
  parenify addParensIfSpaces $
    ( case whnf of
        Nothing -> group (annotate (AnnColor Red) "‼" <> exprDoc scrutinee)
        Just s -> pretty s <> " ← " <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> exprDoc scrutinee))
    )
-- case scrutinee of [whnf] {
--   alternative1 -> body1
--   alternative2 -> body2
-- }
exprCaseDoc addParensIfSpaces scrutinee whnf alternatives =
  parenify addParensIfSpaces $
    ( case whnf of
        Nothing ->
          group
            ( flatAlt
                (annotate (AnnColor Red) "‼" <> exprDoc scrutinee <> hardline <> annotate AnnKeyword "switch")
                (annotate AnnKeyword "switch" <> space <> nest 2 (line' <> annotate (AnnColor Red) "‼" <> exprDoc scrutinee))
            )
        Just s ->
          group
            ( flatAlt
                ( pretty s
                    <> " ← "
                    <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> exprDoc scrutinee))
                    <> hardline
                    <> annotate AnnKeyword "switch"
                )
                (annotate AnnKeyword "switch" <> space <> pretty s <> " = " <> annotate (AnnColor Red) "‼" <> exprDoc scrutinee)
            )
    )
      <> hardline
      <> alternativesDoc alternatives

exprLetDoc :: Bool -> LetBinding -> Expr -> Doc Ann
exprLetDoc addParensIfSpaces binding body =
  parenify addParensIfSpaces $
    -- group (letBindingDoc binding)
    ( case binding of
        LetBinding ident _ -> annotate AnnDefinition (pretty ident) <> " = ..."
    )
      <> hardline
      <> exprDoc body

exprLetrecDoc :: Bool -> [LetBinding] -> Expr -> Doc Ann
exprLetrecDoc addParensIfSpaces bindings body =
  parenify addParensIfSpaces $
    -- group (fold (punctuate hardline (map letBindingDoc bindings)))
    ( bindings
        & map (\(LetBinding ident _) -> annotate AnnDefinition (pretty ident) <> " = ...")
        & punctuate hardline
        & fold
    )
      <> hardline
      <> exprDoc body

exprJoinDoc :: Bool -> JoinPoint -> Expr -> Doc Ann
exprJoinDoc addParensIfSpaces point body =
  parenify addParensIfSpaces $
    -- group (joinPointDoc point)
    ( case point of
        JoinPoint ident _ _ -> annotate AnnDefinition (pretty ident) <> " = ..."
    )
      <> hardline
      <> exprDoc body

exprJoinrecDoc :: Bool -> [JoinPoint] -> Expr -> Doc Ann
exprJoinrecDoc addParensIfSpaces points body =
  parenify addParensIfSpaces $
    -- group (fold (punctuate hardline (map joinPointDoc points)))
    ( points
        & map (\(JoinPoint ident _ _) -> annotate AnnDefinition (pretty ident) <> " = ...")
        & punctuate hardline
        & fold
    )
      <> hardline
      <> exprDoc body

-- if this is a list, slurp it into its non-empty exprs
--
--   []         => Just (nil, [])
--   x : []     => Just (x, [nil])
--   x : xs     => Just (x, [xs])
--   x : y : ys => Just (x, y:ys)
slurpListExpr :: Expr -> Maybe (Expr, [Expr])
slurpListExpr = \case
  EApp (EVar "[]") (ETy _) [] -> Just (eNil, [])
  EApp (EVar ":") (ETy _) [lhs, rhs] -> Just (lhs, slurp rhs)
  _ -> Nothing
  where
    slurp :: Expr -> [Expr]
    slurp = \case
      EApp (EVar "[]") (ETy _) [] -> [eNil]
      EApp (EVar ":") (ETy _) [lhs, rhs] -> lhs : slurp rhs
      expr -> [expr]

alternativeDoc :: Bool -> Alternative -> Doc Ann
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

alternativesDoc :: [(Alternative, Expr)] -> Doc Ann
alternativesDoc =
  go . moveDefaultToBottom
  where
    go :: [(Alternative, Expr)] -> Doc Ann
    go =
      fold . punctuate hardline . map f

    f :: (Alternative, Expr) -> Doc Ann
    f (alternative, body) =
      group $
        nest 2 $
          annotate AnnKeyword "case"
            <> space
            <> alternativeDoc False alternative
            <> " →"
            <> line
            <> exprDoc body

    moveDefaultToBottom :: [(Alternative, Expr)] -> [(Alternative, Expr)]
    moveDefaultToBottom = \case
      x@(ADef {}, _) : xs -> xs ++ [x]
      xs -> xs

identDoc :: Ident -> Doc Ann
identDoc Ident {name} =
  pretty name

letBindingDoc :: LetBinding -> Doc Ann
letBindingDoc (LetBinding name defn) =
  defnDoc name defn

joinPointDoc :: JoinPoint -> Doc Ann
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

varDoc :: Var -> Doc Ann
varDoc = \case
  Tyvar var _kind -> annotate AnnType ("@" <> pretty var)
  Var var _type -> pretty var

eCons :: Expr
eCons =
  EVar "𝘤𝘰𝘯𝘴"

eNil :: Expr
eNil =
  EVar "𝘯𝘪𝘭"

parenify :: Bool -> Doc ann -> Doc ann
parenify addParensIfSpaces inner =
  if addParensIfSpaces
    then group (flatAlt ("( " <> align inner <> line <> ")") (parens inner))
    else group inner

mungeVars :: [Var] -> [Var]
mungeVars =
  if omitTypes
    then mapMaybe \case
      Tyvar {} -> Nothing
      var@Var {} -> Just var
    else id
