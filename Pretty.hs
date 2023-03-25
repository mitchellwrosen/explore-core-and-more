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
  | AnnTyvar -- bound tyvar

styleAnn :: Ann -> AnsiStyle
styleAnn = \case
  AnnKeyword -> bold
  AnnTyvar -> color Blue

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
  ECase scrutinee whnf alternatives ->
    (if addParensIfSpaces then parens else id) $
      nest 2 $
        fold
          [ annotate AnnKeyword "case",
            space,
            group (exprDoc scrutinee),
            space,
            annotate AnnKeyword "of",
            maybe mempty (\s -> " " <> pretty s) whnf,
            alternativesDoc alternatives
          ]
  ETy ty -> "@" <> typeDoc_ True ty

alternativeDoc :: Alternative -> Doc Ann
alternativeDoc = \case
  ACon con vars body -> go (hsep (pretty con : map varDoc vars)) body
  ADef body -> go "_" body
  ALit {} -> "ALIT"
  where
    go lhs rhs =
      nest 2 (lhs <> " ->" <> line <> exprDoc rhs)

alternativesDoc :: [Alternative] -> Doc Ann
alternativesDoc = \case
  [] -> mempty
  alts -> line <> go alts
  -- go -- . moveDefaultToBottom
  where
    go :: [Alternative] -> Doc Ann
    go =
      vsep . map alternativeDoc

    moveDefaultToBottom :: [Alternative] -> [Alternative]
    moveDefaultToBottom = \case
      x@ADef {} : xs -> xs ++ [x]
      xs -> xs

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
  Tyvar var _kind -> annotate AnnTyvar ("@" <> pretty var)
  Var var _type -> pretty var
