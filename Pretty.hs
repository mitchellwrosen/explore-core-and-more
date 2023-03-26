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
  = AnnConstructor
  | AnnKeyword
  | AnnLiteral
  | AnnType

styleAnn :: Ann -> AnsiStyle
styleAnn = \case
  AnnConstructor -> colorDull Yellow <> bold
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
      hang 2 (pretty ident <> space <> hsep (map varDoc (mungeVars bindings)) <> " =" <> line <> exprDoc body)

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
  EId ident ->
    if isUpper (Text.head ident) || ident == ":" || ident == "[]" || ident == "(##)"
      then annotate AnnConstructor (pretty ident)
      else pretty ident
  ELit lit -> litDoc lit
  EApp (EId ":") (ETy _) zs@(LastElement (EApp (EId "[]") (ETy _) [])) ->
    annotate AnnConstructor "["
      <> hsep (punctuate (annotate AnnConstructor ",") (map exprDoc (init zs)))
      <> annotate AnnConstructor "]"
  EApp x y zs ->
    let args = mapMaybe p (y : zs)
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
  ELam bindings body ->
    (if addParensIfSpaces then parens else id) $
      nest 2 $
        "\\" <> hsep (map varDoc (mungeVars bindings)) <> " ->" <> line <> exprDoc body
  -- Made-up straight-line syntax for single-alternative case (to reduce nesting)
  ECase scrutinee whnf [(alternative, body)] ->
    (if addParensIfSpaces then parens else id) $
      ( case (alternative, whnf) of
          (ADef, Just s) -> pretty s
          _ ->
            case whnf of
              Nothing -> alternativeDoc False alternative
              Just s -> pretty s <> "@" <> alternativeDoc True alternative
      )
        <> " = "
        <> group (nest 2 (line' <> annotate AnnKeyword "case" <> space <> align (exprDoc scrutinee)))
        <> hardline
        <> exprDoc body
  ECase scrutinee whnf alternatives ->
    (if addParensIfSpaces then parens else id) $
      nest 2 $
        fold
          [ annotate AnnKeyword "case",
            space,
            group (exprDoc scrutinee),
            space,
            annotate AnnKeyword "of",
            maybe mempty (\s -> space <> pretty s) whnf,
            alternativesDoc alternatives
          ]
  EJump -> annotate AnnKeyword "jump"
  ETy ty -> annotate AnnType ("@" <> typeDoc_ True ty)
  ELet ident defn body ->
    (if addParensIfSpaces then parens else id) $
      annotate AnnKeyword "let"
        <> space
        <> group (defnDoc ident defn)
        <> hardline
        <> exprDoc body
  EJoin point body ->
    (if addParensIfSpaces then parens else id) $
      annotate AnnKeyword "join"
        <> space
        <> group (joinPointDoc point)
        <> hardline
        <> exprDoc body
  EJoinrec defns body ->
    (if addParensIfSpaces then parens else id) $
      nest 2 (annotate AnnKeyword "joinrec" <> line <> hsep (map joinPointDoc defns))
        <> hardline
        <> exprDoc body
  ETupleU exprs ->
    annotate AnnConstructor "(#"
      <> space
      <> hsep (punctuate (annotate AnnConstructor ",") (map exprDoc exprs))
      <> space
      <> annotate AnnConstructor "#)"

alternativeDoc :: Bool -> Alternative -> Doc Ann
alternativeDoc addParensIfSpaces = \case
  ACon con vars ->
    (if addParensIfSpaces then parens else id) $
      hsep (annotate AnnConstructor (pretty con) : map varDoc (mungeVars vars))
  ADef -> "_"
  ALit lit -> litDoc lit
  ATupleU vars ->
    annotate AnnConstructor "(#"
      <> space
      <> hsep (punctuate (annotate AnnConstructor ",") (map varDoc (mungeVars vars)))
      <> space
      <> annotate AnnConstructor "#)"

alternativesDoc :: [(Alternative, Expr)] -> Doc Ann
alternativesDoc = \case
  [] -> mempty
  alts -> line <> go (moveDefaultToBottom alts)
  where
    go :: [(Alternative, Expr)] -> Doc Ann
    go =
      fold . punctuate hardline . map f

    f :: (Alternative, Expr) -> Doc Ann
    f (alternative, body) =
      nest 2 (alternativeDoc False alternative <> " ->" <> group (line <> exprDoc body))

    moveDefaultToBottom :: [(Alternative, Expr)] -> [(Alternative, Expr)]
    moveDefaultToBottom = \case
      x@(ADef {}, _) : xs -> xs ++ [x]
      xs -> xs

inDoc :: Expr -> Doc Ann
inDoc expr =
  annotate AnnKeyword "in"
    <> space
    <> align (exprDoc expr)

joinPointDoc :: JoinPoint -> Doc Ann
joinPointDoc (JoinPoint name bindings body) =
  defnDoc name (ELam bindings body)

litDoc :: Lit -> Doc Ann
litDoc =
  annotate AnnLiteral . \case
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
