module Pretty where

import Data.Char (isUpper)
import Data.Foldable (fold)
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
    opts = LayoutOptions {layoutPageWidth = AvailablePerLine 120 1}

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
    go bindings0 body =
      let varsDoc =
            case map varDoc (mungeVars bindings0) of
              [] -> mempty
              bindings -> hsep bindings <> space
       in hang 2 (annotate AnnDefinition (pretty ident) <> space <> varsDoc <> "=" <> line <> exprDoc body)

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
        || name1 == "list∙"
        || name1 == "tuple∙"
        || name1 == "tuple#∙"
        then annotate AnnConstructor
        else id
    )
      (identDoc ident1)
    where
      -- rename ghc-prim:GHC.Prim.(##) and ghc-prim:GHC.Tuple.() at print-time
      name1
        | name0 == "()" = "tuple∙"
        | name0 == "(##)" = "tuple#∙"
        | otherwise = name0
      ident1 = ident0 {name = name1}
  ELit lit -> annotate AnnLiteral (litDoc lit)
  (slurpListExpr -> Just (expr, exprs)) ->
    exprDoc_ addParensIfSpaces (EApp (EVar "list∙") expr exprs)
  EApp (EVar ":") (ETy _) zs@(LastElement (EApp (EVar "[]") (ETy _) [])) ->
    annotate AnnConstructor "["
      <> hsep (punctuate (annotate AnnConstructor ",") (map exprDoc (init zs)))
      <> annotate AnnConstructor "]"
  EApp EJump (EVar ident) zs -> exprAppDoc addParensIfSpaces (EVar (ident <> "✓")) zs
  EApp x y zs -> exprAppDoc addParensIfSpaces x (y : zs)
  ELam bindings body ->
    parenify addParensIfSpaces $
      nest 2 ("\\" <> hsep (map varDoc (mungeVars bindings)) <> " →" <> line <> exprDoc body)
  -- case scrutinee of {
  --   alternative -> body
  -- }
  ECase scrutinee Nothing [(alternative, body)] ->
    parenify addParensIfSpaces $
      ( case alternative of
          ADef -> group (nest 2 (annotate (AnnColor Red) "‼" <> exprDoc scrutinee))
          _ ->
            alternativeDoc False alternative
              <> " = "
              <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> exprDoc scrutinee))
      )
        <> hardline
        <> exprDoc body
  -- case scrutinee of whnf {
  --   alternative -> body
  -- }
  ECase scrutinee (Just whnf) [(alternative, body)] ->
    parenify addParensIfSpaces $
      pretty whnf
        <> ( case alternative of
               ADef -> mempty
               ACon {} -> "@" <> alternativeDoc True alternative
           )
        <> " = "
        <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> exprDoc scrutinee))
        <> hardline
        <> exprDoc body
  -- case scrutinee of [whnf] {
  -- }
  ECase scrutinee whnf [] ->
    parenify addParensIfSpaces $
      ( case whnf of
          Nothing -> group (nest 2 (annotate (AnnColor Red) "‼" <> exprDoc scrutinee))
          Just s -> pretty s <> " = " <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> exprDoc scrutinee))
      )
  -- case scrutinee of [whnf] {
  --   alternative1 -> body1
  --   alternative2 -> body2
  -- }
  ECase scrutinee whnf alternatives ->
    parenify addParensIfSpaces $
      ( case whnf of
          Nothing ->
            group
              ( flatAlt
                  (annotate (AnnColor Red) "‼" <> exprDoc scrutinee <> hardline <> annotate AnnKeyword "switch")
                  (annotate AnnKeyword "switch" <> space <> nest 2 (line' <> annotate (AnnColor Red) "‼" <> exprDoc scrutinee))
              )
          Just s ->
            pretty s
              <> " = "
              <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> exprDoc scrutinee))
              <> hardline
              <> annotate AnnKeyword "switch"
      )
        <> alternativesDoc alternatives
  EJump -> error "EJump"
  ETy ty -> annotate AnnType ("@" <> typeDoc_ True ty)
  ELet ident defn body ->
    parenify addParensIfSpaces $
      group (defnDoc ident defn)
        <> hardline
        <> exprDoc body
  EJoin point body ->
    parenify addParensIfSpaces $
      group (joinPointDoc point)
        <> hardline
        <> exprDoc body
  EJoinrec defns body ->
    parenify addParensIfSpaces $
      nest 2 (hsep (map joinPointDoc defns))
        <> hardline
        <> exprDoc body
  ETupleU (expr : exprs) -> exprDoc_ addParensIfSpaces (EApp (EVar "tuple#∙") expr exprs)
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

-- if this is a list, slurp it into its non-empty exprs. the empty list literal [] is the last such expr
slurpListExpr :: Expr -> Maybe (Expr, [Expr])
slurpListExpr = \case
  EApp (EVar "[]") (ETy _) [] -> Just (EVar "[]", [])
  EApp (EVar ":") (ETy _) [lhs, rhs] -> Just (lhs, slurp rhs)
  _ -> Nothing
  where
    slurp :: Expr -> [Expr]
    slurp = \case
      EApp (EVar "[]") (ETy _) [] -> [EVar "[]"]
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
          "[]" -> varIdent "nil"
          ":" -> varIdent "cons"
          _ -> con0
  ADef -> annotate AnnPattern "default"
  ALit lit -> annotate AnnPattern (litDoc lit)
  -- ATupleU vars ->
  --   annotate AnnPattern "(#"
  --     <> space
  --     <> hsep (punctuate (annotate AnnPattern ",") (map varDoc (mungeVars vars)))
  --     <> space
  --     <> annotate AnnPattern "#)"
  ATupleU vars -> alternativeDoc addParensIfSpaces (ACon (varIdent "tuple#") vars)

alternativesDoc :: [(Alternative, Expr)] -> Doc Ann
alternativesDoc alts =
  nest 2 (hardline <> go (moveDefaultToBottom alts))
  where
    go :: [(Alternative, Expr)] -> Doc Ann
    go =
      fold . punctuate hardline . map f

    f :: (Alternative, Expr) -> Doc Ann
    f (alternative, body) =
      nest 2 (alternativeDoc False alternative <> " →" <> group (line <> exprDoc body))

    moveDefaultToBottom :: [(Alternative, Expr)] -> [(Alternative, Expr)]
    moveDefaultToBottom = \case
      x@(ADef {}, _) : xs -> xs ++ [x]
      xs -> xs

identDoc :: Ident -> Doc Ann
identDoc Ident {name} =
  pretty name

joinPointDoc :: JoinPoint -> Doc Ann
joinPointDoc (JoinPoint name bindings body) =
  defnDoc (name <> "✓") (ELam bindings body)

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
  TForall _ _ -> undefined
  TFun _ _ -> undefined
  TId ident -> pretty ident

varDoc :: Var -> Doc Ann
varDoc = \case
  Tyvar var _kind -> annotate AnnType ("@" <> pretty var)
  Var var _type -> pretty var

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
