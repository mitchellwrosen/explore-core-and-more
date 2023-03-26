module Pretty where

import Data.Foldable (fold)
import Data.Text (Text)
import qualified Data.Text as Text
import Expr
import Prettyprinter
import Prettyprinter.Render.Terminal
import Type

prettyExpr :: Text -> Expr -> Text
prettyExpr ident expr =
  renderStrict (layoutPretty opts (styleAnn <$> doc))
  where
    opts = LayoutOptions {layoutPageWidth = Unbounded}
    doc = nest 2 (pretty ident <> " =" <> line <> exprDoc expr)

data Ann
  = AnnKeyword
  | AnnType

styleAnn :: Ann -> AnsiStyle
styleAnn = \case
  AnnKeyword -> bold
  AnnType -> color Blue

exprDoc :: Expr -> Doc Ann
exprDoc =
  exprDoc_ False

exprDoc_ :: Bool -> Expr -> Doc Ann
exprDoc_ addParensIfSpaces = \case
  EId ident -> pretty ident
  ELit lit -> litDoc lit
  EApp x y zs ->
    (if addParensIfSpaces then parens else id) $
      nest 2 (vsep (map (exprDoc_ True) (x : y : zs)))
  ELam bindings body ->
    (if addParensIfSpaces then parens else id) $
      nest 2 $
        "\\" <> hsep (map varDoc bindings) <> " ->" <> line <> exprDoc body
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
        <> annotate AnnKeyword "case"
        <> space
        <> group (exprDoc scrutinee)
        <> line
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
  ETy ty -> annotate AnnType ("@" <> typeDoc_ True ty)
  ELet ident defn body ->
    (if addParensIfSpaces then parens else id) $
      annotate AnnKeyword "let"
        <> space
        <> hang 2 (pretty ident <> " =" <> line <> exprDoc defn)
        <> line
        <> annotate AnnKeyword "in"
        <> space
        <> align (exprDoc body)
  EJoin {} -> "EJOIN"
  EJoinrec defns body ->
    (if addParensIfSpaces then parens else id) $
      nest 2 (annotate AnnKeyword "joinrec" <> line <> hsep (map joinPointDoc defns))
        <> line
        <> nest 2 (annotate AnnKeyword "in" <> line <> exprDoc body)
  ETupleU {} -> "ETUPLEU"

alternativeDoc :: Bool -> Alternative -> Doc Ann
alternativeDoc addParensIfSpaces = \case
  ACon con vars ->
    (if addParensIfSpaces then parens else id) $
      hsep (pretty con : map varDoc vars)
  ADef -> "_"
  ALit lit -> litDoc lit
  ATupleU vars -> "(# " <> hsep (punctuate "," (map varDoc vars)) <> " #)"

alternativesDoc :: [(Alternative, Expr)] -> Doc Ann
alternativesDoc = \case
  [] -> mempty
  alts -> line <> go (moveDefaultToBottom alts)
  where
    go :: [(Alternative, Expr)] -> Doc Ann
    go =
      vsep
        . map
          ( \(alternative, body) ->
              nest 2 (alternativeDoc False alternative <> " ->" <> line <> exprDoc body)
          )

    moveDefaultToBottom :: [(Alternative, Expr)] -> [(Alternative, Expr)]
    moveDefaultToBottom = \case
      x@(ADef {}, _) : xs -> xs ++ [x]
      xs -> xs

joinPointDoc :: JoinPoint -> Doc Ann
joinPointDoc (JoinPoint name bindings body) =
  nest 2 (pretty name <> space <> hsep (map varDoc bindings) <> " =" <> line <> exprDoc body)

litDoc :: Lit -> Doc ann
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
      nest 2 (vsep (map (typeDoc_ True) (x : y : zs)))
  TForall _ _ -> undefined
  TFun _ _ -> undefined
  TId ident -> pretty ident

varDoc :: Var -> Doc Ann
varDoc = \case
  Tyvar var _kind -> annotate AnnType ("@" <> pretty var)
  Var var _type -> pretty var
