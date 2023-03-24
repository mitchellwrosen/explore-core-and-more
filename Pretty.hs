module Pretty where

import Data.Foldable (fold)
import Data.Text (Text)
import Expr
import Prettyprinter
import Prettyprinter.Render.Terminal

prettyExpr :: Expr -> Text
prettyExpr =
  renderStrict . layoutPretty LayoutOptions {layoutPageWidth = Unbounded} . fmap styleAnn . exprDoc

data Ann
  = Keyword

-- \| Modules

styleAnn :: Ann -> AnsiStyle
styleAnn = \case
  Keyword -> bold

exprDoc :: Expr -> Doc Ann
exprDoc =
  exprDoc_ False

exprDoc_ :: Bool -> Expr -> Doc Ann
exprDoc_ addParensIfSpaces = \case
  EId modules ident -> idDoc modules ident
  ELit _ -> "LIT" -- Text
  EApp x y zs ->
    (if addParensIfSpaces then parens else id) $
      nest 2 (vsep (map (exprDoc_ True) (x : y : zs)))
  ELam bindings body ->
    (if addParensIfSpaces then parens else id) $
      nest 2 $
        "\\" <> hsep (map pretty bindings) <> " ->" <> line <> exprDoc body
  ECase scrutinee whnf alternatives ->
    (if addParensIfSpaces then parens else id) $
      nest 2 $
        fold
          [ annotate Keyword "case",
            space,
            group (exprDoc scrutinee),
            space,
            annotate Keyword "of",
            maybe mempty (\s -> " " <> pretty s) whnf,
            alternativesDoc alternatives
          ]

alternativeDoc :: Alternative -> Doc Ann
alternativeDoc = \case
  ACon {} -> "ACON"
  ADef body ->
    nest 2 ("_ -> " <> line <> exprDoc body)
  ALit {} -> "ALIT"

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

idDoc :: [Text] -> Text -> Doc Ann
idDoc modules ident =
  if null modules
    then pretty ident
    else (foldMap (\m -> pretty m <> ".") modules) <> pretty ident
