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
  EId ident@Ident {name} ->
    if isUpper (Text.head name) || name == ":" || name == "[]" || name == "()" || name == "(##)"
      then annotate AnnConstructor (identDoc ident)
      else identDoc ident
  ELit lit -> annotate AnnLiteral (litDoc lit)
  EApp (EVar ":") (ETy _) zs@(LastElement (EApp (EVar "[]") (ETy _) [])) ->
    annotate AnnConstructor "["
      <> hsep (punctuate (annotate AnnConstructor ",") (map exprDoc (init zs)))
      <> annotate AnnConstructor "]"
  EApp EJump (EVar ident) zs -> exprAppDoc addParensIfSpaces (EVar (ident <> "🗸")) zs
  EApp x y zs -> exprAppDoc addParensIfSpaces x (y : zs)
  ELam bindings body ->
    (if addParensIfSpaces then (\s -> group ("(" <> s <> line' <> ")")) else group) $
      nest 2 ("\\" <> hsep (map varDoc (mungeVars bindings)) <> " →" <> line <> exprDoc body)
  -- case scrutinee of {
  --   alternative -> body
  -- }
  ECase scrutinee Nothing [(alternative, body)] ->
    (if addParensIfSpaces then parens else id) $
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
    (if addParensIfSpaces then parens else id) $
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
    (if addParensIfSpaces then parens else id) $
      ( case whnf of
          Nothing -> group (nest 2 (annotate (AnnColor Red) "‼" <> exprDoc scrutinee))
          Just s -> pretty s <> " = " <> group (nest 2 (line' <> annotate (AnnColor Red) "‼" <> exprDoc scrutinee))
      )
  -- case scrutinee of [whnf] {
  --   alternative1 -> body1
  --   alternative2 -> body2
  -- }
  ECase scrutinee whnf alternatives ->
    (if addParensIfSpaces then parens else id) $
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
    (if addParensIfSpaces then parens else id) $
      group (defnDoc ident defn)
        <> hardline
        <> exprDoc body
  EJoin point body ->
    (if addParensIfSpaces then parens else id) $
      group (joinPointDoc point)
        <> hardline
        <> exprDoc body
  EJoinrec defns body ->
    (if addParensIfSpaces then parens else id) $
      nest 2 (hsep (map joinPointDoc defns))
        <> hardline
        <> exprDoc body
  ETupleU (expr : exprs) ->
    group $
      hang 1 $
        annotate AnnConstructor "(#"
          <> space
          <> hang 2 (exprDoc expr)
          <> line'
          <> annotate AnnConstructor ","
          <> space
          <> fold (punctuate (line' <> annotate AnnConstructor ",") (map (align . exprDoc) exprs))
          <> line
          <> annotate AnnConstructor "#)"
  ETupleU exprs -> error ("ETupleU " ++ show exprs)

exprAppDoc :: Bool -> Expr -> [Expr] -> Doc Ann
exprAppDoc addParensIfSpaces x ys =
  let args = mapMaybe p ys
   in (if addParensIfSpaces && not (null args) then parens else id) $
        group (nest 2 (vsep (map (exprDoc_ True) (x : args))))
  where
    p :: Expr -> Maybe Expr
    p expr =
      if omitTypes
        then case expr of
          ETy _ -> Nothing
          _ -> Just expr
        else Just expr

alternativeDoc :: Bool -> Alternative -> Doc Ann
alternativeDoc addParensIfSpaces = \case
  ACon con vars ->
    (if addParensIfSpaces then parens else id) $
      hsep (annotate AnnPattern (identDoc con) : map varDoc (mungeVars vars))
  ADef -> annotate AnnPattern "default"
  ALit lit -> annotate AnnPattern (litDoc lit)
  ATupleU vars ->
    annotate AnnPattern "(#"
      <> space
      <> hsep (punctuate (annotate AnnPattern ",") (map varDoc (mungeVars vars)))
      <> space
      <> annotate AnnPattern "#)"

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
  defnDoc (name <> "🗸") (ELam bindings body)

litDoc :: Lit -> Doc Ann
litDoc = \case
  LInt n -> pretty n
  LIntU n -> pretty n <> "#"
  LStrU s -> "\"" <> pretty (Text.replace "\"" "\\\"" s) <> "\"#"
  LWord64U n -> pretty n <> "#" -- eh, ##64 looks ugly and isn't very informative

typeDoc :: Type -> Doc Ann
typeDoc =
  typeDoc_ False

typeDoc_ :: Bool -> Type -> Doc Ann
typeDoc_ addParensIfSpaces = \case
  TApp x y zs ->
    (if addParensIfSpaces then parens else id) $
      group (nest 2 (vsep (map (typeDoc_ True) (x : y : zs))))
  TForall _ _ -> undefined
  TFun _ _ -> undefined
  TId ident -> pretty ident

varDoc :: Var -> Doc Ann
varDoc = \case
  Tyvar var _kind -> annotate AnnType ("@" <> pretty var)
  Var var _type -> pretty var

mungeVars :: [Var] -> [Var]
mungeVars =
  if omitTypes
    then mapMaybe \case
      Tyvar {} -> Nothing
      var@Var {} -> Just var
    else id
