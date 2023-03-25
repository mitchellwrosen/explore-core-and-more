module Main where

import Control.Applicative (asum)
import Control.Monad (guard, when)
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
import Debug.Trace
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
  contents <- Text.decodeUtf8 <$> ByteString.readFile ".simpl/Scope.dump-simpl"
  case runParser parser "" contents of
    Left err -> putStrLn (errorBundlePretty err)
    Right (result, rest) -> do
      pPrintForceColor result
      Text.putStrLn ""
      let putTerm Term {identifier, expr} = do
            Text.putStrLn (prettyExpr identifier expr)
            Text.putStrLn ""
      for_ (declarations result) \case
        DeclTerm term -> putTerm term
        DeclRec terms -> for_ terms putTerm
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

data Declaration
  = DeclTerm Term
  | DeclRec [Term]
  deriving stock (Show)

declarationP :: P Declaration
declarationP =
  optional (string_ "Rec {") >>= \case
    Nothing -> DeclTerm <$> termP
    Just () -> do
      let loop acc =
            optional (string_ "end Rec }") >>= \case
              Nothing -> do
                term <- termP
                loop (term : acc)
              Just () -> pure (reverse acc)
      terms <- loop []
      pure (DeclRec terms)

data Term = Term
  { identifier :: Text,
    expr :: Expr
  }
  deriving stock (Show)

termP :: P Term
termP = do
  _ <- modulePrefixP
  identifier <- eidentStrP
  string_ "::"
  _typeText <- do
    let grabLine = takeWhile1P Nothing (/= '\n') <* char '\n'
    let loop :: [Text] -> P Text
        loop acc =
          optional (lookAhead (satisfy isUpper)) >>= \case
            Nothing -> do
              line <- grabLine
              loop (line : acc)
            Just _ -> pure (Text.unwords (reverse acc))
    line <- grabLine
    loop [line]
  -- repeated identifier from type sig line
  _ <- modulePrefixP
  _ <- eidentStrP
  string_ "="
  expr <- exprP
  pure
    Term
      { identifier,
        expr
      }

typeP :: P Type
typeP = do
  ty0 <- typeP_
  case ty0 of
    TApp {} -> funtimes ty0
    TForall {} -> funtimes ty0
    TFun {} -> undefined -- Type Type
    TId {} -> do
      ty1 <-
        many typeP_ <&> \case
          [] -> ty0
          t : ts -> (TApp ty0 t ts)
      funtimes ty1
  where
    funtimes ty = do
      _ <- optional (string_ "%1")
      optional (string_ "->") >>= \case
        Nothing -> pure ty
        Just () -> do
          ty2 <- typeP
          pure (TFun ty ty2)

typeP_ :: P Type
typeP_ =
  asum
    [ do
        string_ "forall"
        vars <- do
          let tyvar = do
                c0 <- satisfy (\c -> isLower c || c == '_')
                cs <- takeWhileP Nothing (\c -> isAlphaNum c || c == '_')
                pure (Text.cons c0 cs)
          some do
            asum
              [ do
                  var <- tyvar
                  space
                  pure (var, Nothing),
                do
                  string_ "{"
                  var <- tyvar
                  string_ "::"
                  ty <- typeP
                  string_ "}"
                  pure (var, Just ty)
              ]
        string_ "."
        ty <- typeP
        pure (TForall vars ty),
      do
        char_ '['
        ty <- typeP
        char_ ']'
        pure (TApp (TId "[]") ty []),
      TId "(# #)" <$ string_ "(# #)",
      char_ '(' *> typeP <* char_ ')',
      do
        ident <- tidentP
        pure (TId ident)
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
  expr0 <- exprP_
  expr1 <-
    case expr0 of
      ELam {} -> pure expr0
      EId {} ->
        many exprP_ <&> \case
          [] -> expr0
          e : es -> (EApp expr0 e es)
      ELit {} -> pure expr0
      EApp {} -> error "EApp"
      ECase {} -> pure expr0
  -- throw away: `cast` <Co:4> :: ...
  _ <-
    optional do
      string_ "`cast` <Co:"
      _ <- takeWhile1P Nothing isDigit
      string_ "> :: ..."
  pure expr1

exprP_ :: P Expr
exprP_ = do
  asum
    [ do
        char_ '\\'
        bindings <- some bindingP
        string_ "->"
        body <- exprP
        pure (ELam bindings body),
      char_ '(' *> exprP <* char_ ')',
      do
        char_ '@'
        lookAhead anySingle >>= \case
          '(' -> ETy <$> typeP
          _ -> ETy . TId <$> tidentP,
      do
        string_ "case"
        scrutinee <- exprP
        string_ "of"
        whnf <- optional (eidentP <* takeWhileP Nothing (/= '{'))
        string_ "{"
        alternatives <- many alternativeP
        string_ "}"
        pure (ECase scrutinee whnf alternatives),
      ELit <$> litP,
      EId <$> eidentP
    ]

eidentP :: P Text
eidentP = do
  -- we don't want to accept identifiers at column 1 here
  SourcePos {sourceColumn} <- getSourcePos
  when (sourceColumn == pos1) empty

  try do
    -- skip package identifier
    _ <- optional packagePrefixP
    _ <- modulePrefixP
    ident <- eidentStrP
    guard (not (Set.member ident keywords))
    pure ident

packagePrefixP :: P Text
packagePrefixP =
  try (packageIdentifierP <* char ':')

packageIdentifierP :: P Text
packageIdentifierP = do
  c0 <- satisfy isLower
  cs <- takeWhile1P Nothing (\c -> isAlphaNum c || c == '-')
  pure (Text.cons c0 cs)

eidentStrP :: P Text
eidentStrP =
  asum
    [ do
        c0 <- satisfy \c -> isAlpha c || isOperator c || c == '_'
        cs <-
          takeWhileP
            Nothing
            (\c -> isAlphaNum c || isOperator c || c == '_' || c == ':')
        space
        pure (Text.cons c0 cs),
      "[]" <$ string_ "[]",
      "(##)" <$ string_ "(##)"
    ]
  where
    isOperator c =
      c == '#' || c == '*' || c == '>' || c == '=' || c == '$'

modulePrefixP :: P [Text]
modulePrefixP =
  many do
    try do
      c0 <- satisfy isUpper
      cs <- takeWhileP Nothing isAlphaNum
      _ <- char '.'
      pure (Text.cons c0 cs)

tidentP :: P Text
tidentP = do
  -- skip package identifier
  _ <- optional packagePrefixP
  _ <- modulePrefixP
  c0 <- satisfy \c -> isAlpha c || c == '_' || c == '*'
  cs <- takeWhileP Nothing (\c -> isAlphaNum c || c == '_')
  let ident = Text.cons c0 cs
  -- tyvars sometimes have some skolem info like @a[sk:1]
  when (isLower (Text.head ident)) do
    try (char '[' *> void (takeWhileP Nothing (/= ']')) <* char ']') <|> pure ()
  space
  pure (Text.cons c0 cs)

varP :: P Var
varP = do
  (satisfy \c -> isAlpha c || c == '_' || c == '$' || c == '@') >>= \case
    '@' -> do
      lookAhead anySingle >>= \case
        '(' -> do
          string_ "("
          var <- tyvar
          ty <- tysig
          string_ ")"
          pure (Tyvar var (Just ty))
        _ -> do
          var <- tyvar
          pure (Tyvar var Nothing)
    c0 -> do
      cs <- takeWhileP Nothing (\c -> isAlphaNum c || c == '_' || c == '$')
      space
      ty <- optional tysig
      pure (Var (Text.cons c0 cs) ty)
  where
    tyvar :: P Text
    tyvar = do
      c0 <- satisfy (\c -> isLower c || c == '_')
      cs <- takeWhileP Nothing (\c -> isAlphaNum c || c == '_')
      space
      pure (Text.cons c0 cs)

    tysig :: P Type
    tysig = do
      string_ "::"
      typeP

bindingP :: P Var
bindingP = do
  asum
    [ do
        string_ "("
        var <- varP
        string_ ")"
        pure var,
      Var "_" Nothing <$ string_ "_"
    ]

litP :: P Lit
litP =
  asum
    [ do
        char '"'
        let hunk :: P Text
            hunk = takeWhileP Nothing (\c -> c /= '"' && c /= '\\')
        let hunks :: [Text] -> P Text
            hunks acc = do
              anySingle >>= \case
                '"' -> pure (Text.concat (reverse acc))
                '\\' -> undefined
                c -> error (show c)
        s <- hunk
        str <- hunks [s]
        optional (char_ '#') <&> \case
          Nothing -> error "TODO non-# string"
          Just () -> LStrU str,
      do
        c0 <- satisfy isDigit
        cs <- takeWhileP Nothing isDigit
        optional (string_ "##64") >>= \case
          Nothing ->
            optional (string_ "#") >>= \case
              Nothing -> pure (LInt (Text.cons c0 cs))
              Just () -> pure (LIntU (Text.cons c0 cs))
          Just () -> pure (LWord64U (Text.cons c0 cs))
    ]

alternativeP :: P Alternative
alternativeP = do
  mkAlt <-
    asum
      [ do
          _ <- lookAhead (satisfy isAlpha)
          constructor <- eidentP
          bindings <- many varP
          pure (ACon constructor bindings),
        do
          string_ "__DEFAULT"
          pure ADef
      ]
  string_ "->"
  expr <- exprP
  _ <- optional (string_ ";")
  pure (mkAlt expr)

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
