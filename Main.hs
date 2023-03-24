module Main where

import Control.Applicative (asum)
import Control.Monad (when)
import qualified Data.ByteString as ByteString
import Data.Char
import Data.Foldable (for_)
import Data.Functor (void, (<&>))
import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Text.IO as Text
import Data.Void (Void)
import Expr
import Pretty (prettyExpr)
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer (decimal)
import Text.Megaparsec.Debug
import Text.Pretty.Simple
import Type

main :: IO ()
main = do
  contents <- Text.decodeUtf8 <$> ByteString.readFile "Scope.dump-simpl"
  case runParser parser "" contents of
    Left err -> putStrLn (errorBundlePretty err)
    Right (result, rest) -> do
      pPrintForceColor result
      Text.putStrLn ""
      for_ (declarations result) \Term {expr} -> Text.putStrLn (prettyExpr expr)
      Text.putStrLn ("\n" <> Text.pack (show rest))

type P = Parsec Void Text

data Dump = Dump
  { size :: CoreSize,
    declarations :: [Declaration]
  }
  deriving stock (Show)

parser :: P (Dump, Text)
parser = do
  space1
  string_ "==================== Tidy Core ===================="
  _ <- takeWhile1P Nothing (/= '\n') -- timestamp
  space1
  string_ "Result size of Tidy Core"
  char_ '='
  size <- coreSizeP
  declarations <- many declarationP

  rest <- takeRest
  pure (Dump {size, declarations}, Text.take 60 rest <> " ...")

data CoreSize = CoreSize
  { terms :: Int,
    types :: Int,
    coercions :: Int,
    joins :: (Int, Int)
  }
  deriving stock (Show)

coreSizeP :: P CoreSize
coreSizeP = do
  char_ '{'
  string_ "terms:"
  terms <- decimalWithCommas
  string_ "types:"
  types <- decimalWithCommas
  string_ "coercions:"
  coercions <- decimalWithCommas
  string_ "joins:"
  joins1 <- decimal
  _ <- char '/'
  joins2 <- decimal
  char_ '}'
  pure CoreSize {terms, types, coercions, joins = (joins1, joins2)}

type Declaration = Term

declarationP :: P Declaration
declarationP = termP

data Term = Term
  { size :: CoreSize,
    identifier :: ([Text], Text),
    props :: [Text],
    scope :: Scope,
    details :: Maybe Details,
    arity :: Maybe Int,
    calledArity :: Maybe Int,
    refersToAtLeastOneCAF :: Bool,
    strictness :: Maybe Text,
    cpr :: Maybe Text,
    unfolding :: Maybe Text,
    expr :: Expr
  }
  deriving stock (Show)

termP :: P Term
termP = do
  string_ "-- RHS size:"
  size <- coreSizeP
  identifier <- idP
  props <- do
    optional (char '[') >>= \case
      Nothing -> pure []
      Just _ -> do
        let propP :: P Text
            propP = do
              fmap Text.concat do
                some do
                  let flatchunk = takeWhile1P Nothing (\c -> c /= ' ' && c /= ']' && c /= '[')
                  let bracketchunk = do
                        x <- string "["
                        y <- takeWhile1P Nothing (/= ']')
                        z <- string "]"
                        pure (x <> y <> z)
                  flatchunk <|> bracketchunk
        props <- some (propP <* space)
        char_ ']'
        pure props
  string_ "::"
  _ <- takeWhile1P Nothing (/= '[')
  string_ "["
  scope <- scopeP
  details <-
    optional (string_ "[") >>= \case
      Nothing -> pure Nothing
      Just () -> Just <$> detailsP <* string_ "]" <* optional (string_ ",")
  arity <-
    optional (string_ "Arity=") >>= \case
      Nothing -> pure Nothing
      Just () -> Just <$> decimal <* optional (string_ ",")
  calledArity <-
    optional (string_ "CallArity=") >>= \case
      Nothing -> pure Nothing
      Just () -> Just <$> decimal <* optional (string_ ",")
  refersToAtLeastOneCAF <-
    optional (string_ "Caf=") >>= \case
      Nothing -> pure True
      Just () -> False <$ string_ "NoCafRefs" <* optional (string_ ",")
  strictness <-
    optional (string_ "Str=") >>= \case
      Nothing -> pure Nothing
      Just () -> Just <$> takeWhile1P Nothing (\c -> c /= ',' && c /= ']') <* optional (string_ ",")
  cpr <-
    optional (string_ "Cpr=") >>= \case
      Nothing -> pure Nothing
      Just () -> Just <$> takeWhile1P Nothing (\c -> c /= ',' && c /= ']') <* optional (string_ ",")
  unfolding <-
    optional (string_ "Unf=") >>= \case
      Nothing -> pure Nothing
      Just () -> dbg "Unfolding" do
        x <- string "Unf{"
        y <- do
          let nonBracketHunk = takeWhile1P Nothing (\c -> c /= '{' && c /= '}')
              bracketHunk = do
                x0 <- string "{"
                y0 <- hunks
                z0 <- string "}"
                pure (x0 <> y0 <> z0)
              hunks = Text.concat <$> many (nonBracketHunk <|> bracketHunk)
          hunks
        z <- string "}"
        _ <- optional (string_ ",")
        pure (Just (x <> y <> z))
  string_ "]"
  _ <- identifierP
  string_ "="
  expr <- exprP
  pure
    Term
      { size,
        identifier,
        props,
        scope,
        details,
        arity,
        calledArity,
        refersToAtLeastOneCAF,
        strictness,
        cpr,
        unfolding,
        expr
      }

qualifiedP :: P a -> P ([Text], a)
qualifiedP p = do
  modules <- many (try (takeWhile1P Nothing isAlphaNum <* char '.'))
  x <- p
  pure (modules, x)

type Identifier = [Text]

identifierP :: P Identifier
identifierP = do
  takeWhile1P Nothing (\c -> isAlphaNum c || c == '$') `sepBy1` char '.' <* space

typeP :: P Type
typeP =
  typeP_ >>= \case
    TApp x y zs -> undefined -- Type Type [Type]
    TForall vars ty -> undefined -- [Text] Type
    TFun x y -> undefined -- Type Type
    TId ss s -> undefined

-- asum
--   [ do
--       string_ "forall"
--       vars <- some (takeWhile1P Nothing isLower <* space)
--       string_ "."
--       ty <- typeP
--       pure (TForall vars ty),
--     do
--       lhs <-
--         asum
--           [ string_ "(" *> typeP <* string_ ")",
--             some (takeWhile1P Nothing isAlphaNum <* space) <&> \case
--               lit0 : lit1 : lits -> TApp lit0 lit1 lits
--               lits -> TVar (head lits)
--           ]
--       optional (string_ "%1 ->") >>= \case
--         Nothing -> pure lhs
--         Just () -> do
--           rhs <- typeP
--           pure (TFun lhs rhs)
--   ]

typeP_ :: P Type
typeP_ =
  asum
    [ do
        string_ "forall"
        vars <- some (takeWhile1P Nothing isLower <* space)
        string_ "."
        ty <- typeP
        pure (TForall vars ty),
      string_ "(" *> typeP <* string_ ")",
      do
        (modules, var) <- idP
        pure (TId modules var)
    ]

data Scope
  = Exported
  | Global
  | Local
  deriving stock (Show)

scopeP :: P Scope
scopeP =
  asum
    [ Global <$ string_ "GblId"
    ]

data Details
  = DataConstructorWrapper
  deriving stock (Show)

detailsP :: P Details
detailsP =
  asum
    [ DataConstructorWrapper <$ string_ "DataConWrapper"
    ]

exprP :: P Expr
exprP = do
  expr <- exprP_
  case expr of
    ELam {} -> pure expr
    EId {} ->
      many exprP_ <&> \case
        [] -> expr
        e : es -> (EApp expr e es)
    ELit {} -> error "ELit"
    EApp {} -> error "EApp"
    ECase {} -> pure expr

exprP_ :: P Expr
exprP_ =
  asum
    [ do
        string_ "\\"
        bindings <- some bindingP
        string_ "->"
        body <- exprP
        pure (ELam bindings body),
      string_ "(" *> exprP <* string_ ")",
      do
        string_ "case"
        scrutinee <- exprP
        string_ "of"
        whnfScrutinee <- optional (varP <* takeWhileP Nothing (/= '{'))
        string_ "{"
        alternatives <- many alternativeP
        string_ "}"
        pure (ECase scrutinee whnfScrutinee alternatives),
      do
        (modules, var) <- idP
        pure (EId modules var)
    ]

idP :: P ([Text], Text)
idP = do
  do
    var <- lookAhead varP
    when (Set.member var keywords) empty
  modules <- many (try (takeWhile1P Nothing isAlphaNum <* char '.'))
  var <- varP
  pure (modules, var)

varP :: P Text
varP = do
  _ <- lookAhead (satisfy (\c -> isAlpha c || c == '_' || c == '@' || c == '$'))
  ident <- takeWhile1P (Just "var") (\c -> isAlphaNum c || c == '_' || c == '@' || c == '$')
  space
  pure ident

bindingP :: P Text
bindingP = do
  string_ "("
  var <- varP
  _props <-
    optional (string "[") >>= \case
      Nothing -> pure Nothing
      Just lb -> do
        props <- takeWhile1P Nothing (/= ']')
        rb <- string "]"
        space
        pure (Just (lb <> props <> rb))
  _ty <-
    optional (string_ "::") >>= \case
      Nothing -> pure Nothing
      Just () -> Just <$> typeP
  string_ ")"
  pure var

alternativeP :: P Alternative
alternativeP = do
  alt <-
    asum
      [ do
          string_ "__DEFAULT"
          string_ "->"
          expr <- exprP
          pure (ADef expr)
      ]
  _ <- optional (string_ ";")
  pure alt

decimalWithCommas :: P Int
decimalWithCommas = do
  digits <- many (satisfy isDigit <* optional (char_ ','))
  pure (foldl' (\acc i -> acc * 10 + digitToInt i) 0 digits)

char_ :: Char -> P ()
char_ c = void (char c) <* space

string_ :: Text -> P ()
string_ s = void (string s) <* space

keywords :: Set Text
keywords =
  Set.fromList
    [ "case",
      "let",
      "of"
    ]
