module Main where

import Control.Applicative (asum)
import qualified Data.ByteString as ByteString
import Data.Char
import Data.Functor (void, (<&>))
import Data.List (foldl')
import Data.Maybe (fromMaybe)
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Text.IO as Text
import Data.Void (Void)
import Expr
import Type
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer (decimal)
import Text.Pretty.Simple

main :: IO ()
main = do
  contents <- Text.decodeUtf8 <$> ByteString.readFile "Scope.dump-simpl"
  case runParser parser "" contents of
    Left err -> putStrLn (errorBundlePretty err)
    Right (result, rest) -> do
      pPrintForceColor result
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
    identifier :: Qualified Identifier,
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
  identifier <- qualifiedP identifierP
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
      Just () -> do
        x <- string "Unf{"
        y <-
          fmap Text.concat do
            many do
              asum
                [ takeWhile1P Nothing (\c -> c /= '{' && c /= '}'),
                  do
                    x0 <- string "{"
                    y0 <- takeWhileP Nothing (\c -> c /= '}')
                    z0 <- string "}"
                    pure (x0 <> y0 <> z0)
                ]
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

qualifiedP :: P a -> P (Qualified a)
qualifiedP p = do
  modules <- many (try (takeWhile1P Nothing isAlphaNum <* char '.'))
  x <- p
  pure (Qualified modules x)

type Identifier = [Text]

identifierP :: P Identifier
identifierP = do
  takeWhile1P Nothing (\c -> isAlphaNum c || c == '$') `sepBy1` char '.' <* space

-- data Type
--   = App [Text]
--   | Arrow Type Type
--   | Forall [Text] Type
--   | Lit Text
--   deriving stock (Show)

-- typeP :: P Type
-- typeP =
--   asum
--     [ do
--         string_ "forall"
--         vars <- some (takeWhile1P Nothing isLower <* space)
--         string_ "."
--         ty <- typeP
--         pure (Forall vars ty),
--       do
--         lhs <-
--           asum
--             [ string_ "(" *> typeP <* string_ ")",
--               some (takeWhile1P Nothing isAlphaNum <* space) <&> \case
--                 lits@(_ : _ : _) -> App lits
--                 lits -> Lit (head lits)
--             ]
--         optional (string_ "%1 ->") >>= \case
--           Nothing -> pure lhs
--           Just () -> do
--             rhs <- typeP
--             pure (Arrow lhs rhs)
--     ]

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
exprP =
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
        pure (ECase scrutinee whnfScrutinee alternatives),
      EId <$> idP
    ]

idP :: P (Qualified Text)
idP =
  qualifiedP varP

varP :: P Text
varP = do
  _ <- lookAhead (satisfy (\c -> isLower c || c == '_' || c == '@' || c == '$'))
  ident <- takeWhile1P (Just "identifier") (\c -> isAlphaNum c || c == '_' || c == '@' || c == '$')
  space
  pure ident

bindingP :: P Binding
bindingP = do
  string_ "("
  var <- varP
  props <-
    optional (string "[") >>= \case
      Nothing -> pure Nothing
      Just lb -> do
        props <- takeWhile1P Nothing (/= ']')
        rb <- string "]"
        space
        pure (Just (lb <> props <> rb))
  _ <- takeWhileP Nothing (/= ')')
  string_ ")"
  pure (Binding var props Nothing)

alternativeP :: P Alternative
alternativeP = 
  asum
    [ do
        string_ "__DEFAULT"
        string_ "->"
        ADef <$> exprP
    ]

decimalWithCommas :: P Int
decimalWithCommas = do
  digits <- many (satisfy isDigit <* optional (char_ ','))
  pure (foldl' (\acc i -> acc * 10 + digitToInt i) 0 digits)

char_ :: Char -> P ()
char_ c = void (char c) <* space

string_ :: Text -> P ()
string_ s = void (string s) <* space
