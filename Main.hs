module Main where

import Control.Applicative (asum)
import Control.Monad (guard, when)
import Data.ByteString qualified as ByteString
import Data.Char
import Data.Foldable (for_)
import Data.Functor (void, ($>), (<&>))
import Data.List (foldl')
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Text.IO qualified as Text
import Data.Void (Void)
import Debug.Trace
import Expr
import Pretty (prettyDefn)
import System.Directory qualified as Directory
import System.Environment (getArgs)
import System.Exit (exitFailure, exitSuccess)
import System.Process qualified as Process
import Text.Megaparsec
import Text.Megaparsec.Char
import Text.Megaparsec.Char.Lexer (decimal)
import Text.Megaparsec.Debug
import Type

main :: IO ()
-- main = pure ()
main = theMain

theMain :: IO ()
theMain = do
  let ghcArgs =
        Text.unwords
          [ "-ddump-simpl",
            "-ddump-to-file",
            "-dsuppress-coercion-types",
            "-dsuppress-coercions",
            "-dsuppress-core-sizes",
            "-dsuppress-idinfo",
            "-dsuppress-timestamps",
            "-dsuppress-type-signatures",
            "-dsuppress-unfoldings"
          ]

  getArgs >>= \case
    ["ghc-args"] -> do
      Text.putStrLn ghcArgs
      exitSuccess
    [file] ->
      Directory.doesPathExist file >>= \case
        True -> do
          contents <- Text.decodeUtf8 <$> ByteString.readFile file
          case runParser parser "" contents of
            Left err -> putStrLn (errorBundlePretty err)
            Right (result, rest) -> do
              -- pPrintForceColor result
              -- Text.putStrLn ""
              let putTerm term@Term {identifier, expr} =
                    when (not (boringTerm term)) do
                      Text.putStrLn (prettyDefn (N identifier 0) (optimizeExpression expr))
                      Text.putStrLn ""
              for_ (declarations result) \case
                DeclTerm term -> putTerm term
                DeclRec terms -> for_ terms putTerm
              when (rest /= Text.empty) do
                Text.putStrLn ("\nTrailing input: " <> Text.pack (show rest))
        False -> do
          Text.putStrLn "No such file!"
          exitFailure
    _ -> do
      (Text.putStrLn . Text.unlines)
        [ "Hello and welcome to your janky tool friend *explore-core-and-more*!",
          "",
          "I'm sort of able to parse and pretty-print stringy Core that's been rendered with the following options:",
          "",
          " " <> ghcArgs,
          "",
          "You can run me with a single arg \"ghc-args\" and I'll return those in a string, for you to use in a command like",
          "",
          "  cabal build my-package:bench:benchmarks --ghc-options=\"-fforce-recomp $(explore-core-and-more ghc-args)\"",
          "",
          "You can invoke me with a single argument: a file path to a .dump-simpl file.",
          "Since you don't seem to know that, though, I'll list them all for you (using hard-coded dependency on `fd` lol...):"
        ]

      files <- lines <$> Process.readProcess "fd" ["-H", "-I", ".dump-simpl"] ""
      Text.putStrLn (Text.unlines (map Text.pack files))
  where
    boringTerm :: Term -> Bool
    boringTerm Term {identifier, expr} =
      or
        [ -- KindRep
          Text.isPrefixOf "$krep" identifier,
          -- typeable TyCon
          Text.isPrefixOf "$tc" identifier,
          -- typeable Module
          Text.isPrefixOf "$tr" identifier,
          case expr of
            EId _ -> True
            _ -> False
        ]
      -- False

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
  pure (Dump {size, declarations}, Text.take 60 rest)

data CoreSize = CoreSize
  { terms :: Int,
    types :: Int,
    coercions :: Int,
    joins :: (Int, Int)
  }
  deriving stock (Show)

coreSizeP :: P CoreSize
coreSizeP =
  label "core size" do
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
  label "declaration" do
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
    expr :: Expr Text
  }
  deriving stock (Show)

-- Parse an identifier like
--
--   foo = ...
--       ^
--
-- leaving the parse state at the first token after 'foo'. This isn't always an '=' token; join points are written with
-- a number of parameters to the left of the '=' corresponding to the join arity, e.g.
--
--   foo (x :: Type) = ...
--       ^
identifierP :: P Text
identifierP =
  label "identifier" do
    _ <- modulePrefixP
    eidentStrP

termP :: P Term
termP =
  label "term" do
    identifier <- identifierP
    string_ "="
    expr <- exprP
    pure
      Term
        { identifier,
          expr
        }

typeP :: P Type
typeP =
  label "type" do
    ty0 <- typeHeadP
    case ty0 of
      TApp {} -> funtimes ty0
      TConstraint {} -> error "TConstraint"
      TForall {} -> funtimes ty0
      TFun {} -> funtimes ty0
      TId {} -> do
        ty1 <-
          many typeHeadP <&> \case
            [] -> ty0
            t : ts -> (TApp ty0 t ts)
        funtimes ty1
      TTuple {} -> funtimes ty0
      TTupleU {} -> funtimes ty0
  where
    funtimes ty = do
      asum
        [ do
            _ <- optional (string_ "%1")
            string_ "->"
            ty2 <- typeP
            pure (TFun ty ty2),
          do
            string_ "=>"
            ty2 <- typeP
            pure (TConstraint ty ty2),
          pure ty
        ]

typeHeadP :: P Type
typeHeadP =
  label "type head" do
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
        typeAtomP
      ]

typeAtomP :: P Type
typeAtomP =
  label "type atom" do
    asum
      [ do
          char_ '['
          ty <- typeP
          char_ ']'
          pure (TApp (TId "[]") ty []),
        TId "()" <$ string_ "()",
        do
          string_ "(# "
          tys <- sepBy typeP (char_ ',')
          string_ "#)"
          pure (TTupleU tys),
        do
          char_ '('
          ty0 <- typeP
          ty1 <-
            lookAhead anySingle >>= \case
              ',' -> do
                _ <- anySingle
                space
                tys <- sepBy1 typeP (char_ ',')
                pure (TTuple ty0 (head tys) (tail tys))
              _ -> pure ty0
          char_ ')'
          pure ty1,
        TId <$> tidentP
      ]

data Scope
  = Exported
  | Global
  | Local
  deriving stock (Show)

scopeP :: P Scope
scopeP =
  label "scope" do
    asum
      [ Global <$ string_ "GblId"
      ]

data Details
  = DataConstructorWrapper
  deriving stock (Show)

detailsP :: P Details
detailsP =
  label "details" do
    asum
      [ DataConstructorWrapper <$ string_ "DataConWrapper"
      ]

exprP :: P (Expr Text)
exprP =
  label "expression" do
    -- expressions can't be at column 1
    SourcePos {sourceColumn} <- getSourcePos
    when (sourceColumn == pos1) empty

    expr0 <- exprP_
    case expr0 of
      -- this can happen:
      --
      --   ((f x `cast` Coercion) y)
      --
      -- which we want to become:
      --
      --   f x y
      EApp e0 e1 es0 -> do
        es1 <- many exprP_
        pure (EApp e0 e1 (es0 ++ es1))
      ECase {} -> pure expr0
      EId {} ->
        many exprP_ <&> \case
          [] -> expr0
          e : es -> (EApp expr0 e es)
      EJoin {} -> pure expr0
      EJoinrec {} -> pure expr0
      EJump ->
        many exprP_ <&> \case
          [] -> expr0
          e : es -> (EApp expr0 e es)
      ELam {} -> pure expr0
      ELet {} -> pure expr0
      ELetrec {} -> pure expr0
      ELit {} -> pure expr0
      ETuple {} -> pure expr0
      ETupleU {} -> pure expr0
      ETy {} -> error "ETy"

exprP_ :: P (Expr Text)
exprP_ = do
  -- expressions can't be at column 1
  SourcePos {sourceColumn} <- getSourcePos
  when (sourceColumn == pos1) empty

  label "expression head" do
    asum
      [ do
          char_ '\\'
          bindings <- some bindingP
          string_ "->"
          body <- exprP
          pure (ELam bindings body),
        do
          char_ '@'
          ETy <$> typeAtomP,
        do
          ekeywordP "case"
          scrutinee <- exprP
          ekeywordP "of"
          whnf <- optional (eidentP <* takeWhileP Nothing (/= '{'))
          string_ "{"
          alternatives <- many alternativeP
          string_ "}"
          pure (ECase scrutinee ((\Ident {name} -> name) <$> whnf) alternatives),
        do
          ekeywordP "letrec"
          string_ "{"
          bindings <- some letBindingP
          string_ "}"
          ekeywordP "in"
          expr <- exprP
          pure (ELetrec bindings expr),
        do
          ekeywordP "let"
          string_ "{"
          binding <- letBindingP
          string_ "}"
          ekeywordP "in"
          expr <- exprP
          pure (ELet binding expr),
        do
          ekeywordP "joinrec"
          string_ "{"
          points <- some joinPointP
          string_ "}"
          ekeywordP "in"
          expr <- exprP
          pure (EJoinrec points expr),
        do
          ekeywordP "join"
          string_ "{"
          point <- joinPointP
          string_ "}"
          ekeywordP "in"
          body <- exprP
          pure (EJoin point body),
        EJump <$ ekeywordP "jump",
        do
          string_ "(# "
          exprs <- sepBy exprP (char_ ',')
          string_ "#)"
          pure (ETupleU exprs),
        ELit <$> litP,
        EId <$> eidentP <* ignoreCast,
        do
          char_ '('
          expr0 <- exprP
          expr1 <-
            lookAhead anySingle >>= \case
              ',' -> do
                _ <- anySingle
                space
                exprs <- sepBy1 exprP (char_ ',')
                pure (ETuple expr0 (head exprs) (tail exprs))
              _ -> do
                ignoreCast
                pure expr0
          char_ ')'
          ignoreCast
          pure expr1
      ]
  where
    -- throw away: `cast` <Co:4> :: ...
    ignoreCast =
      void do
        optional do
          string_ "`cast` <Co:"
          _ <- takeWhile1P Nothing isDigit
          string_ "> :: ..."

letBindingP :: P (LetBinding Text)
letBindingP =
  label "let binding" do
    ident <- identifierP
    string_ "="
    expr <- exprP
    _ <- optional (string_ ";")
    pure (LetBinding ident expr)

joinPointP :: P (JoinPoint Text)
joinPointP =
  label "join point" do
    ident <- identifierP
    bindings <- many bindingP
    string_ "="
    expr <- exprP
    _ <- optional (string_ ";")
    pure (JoinPoint ident bindings expr)

eidentP :: P (Ident Text)
eidentP =
  label "expression identifier" do
    -- identifiers can't be at column 1
    SourcePos {sourceColumn} <- getSourcePos
    when (sourceColumn == pos1) empty

    try do
      -- skip package identifier
      _ <- optional packagePrefixP
      _ <- modulePrefixP
      ident <- eidentStrP
      guard (ident /= "=" && not (Set.member ident keywords))
      pure (Ident Nothing [] ident)

packagePrefixP :: P Text
packagePrefixP =
  try (packageIdentifierP <* char ':')

packageIdentifierP :: P Text
packageIdentifierP = do
  c0 <- satisfy isLower
  cs <- takeWhile1P Nothing (\c -> isAlphaNum c || c == '-')
  pure (Text.cons c0 cs)

eidentStrP :: P Text
eidentStrP = do
  asum
    [ do
        -- make sure we don't treat '#' like an operator if it's followed by right paren
        notFollowedBy (string "#)")

        ident <- do
          let hunks =
                many do
                  asum
                    [ takeWhile1P Nothing \c -> isAlphaNum c || isOperator c || c == '_' || c == '\'' || c == ':',
                      string "(,)"
                    ]
          asum
            [ do
                c0 <- satisfy \c -> isAlpha c || isOperator c || c == '_' || c == '\''
                cs <- hunks
                pure (Text.cons c0 (Text.concat cs)),
              do
                _ <- string "{__ffi_static_ccall_unsafe "
                ident <- eidentP
                string_ "::"
                _ty <- typeP
                _ <- char '}'
                cs <- hunks
                pure (identVar ident <> Text.concat cs)
            ]
        space
        pure ident,
      ":" <$ string_ ":", -- fixme couldn't this be an operator or something, not cons
      "[]" <$ string_ "[]",
      "()" <$ string_ "()",
      "(##)" <$ string_ "(##)"
    ]

ekeywordP :: Text -> P ()
ekeywordP s =
  try do
    _ <- string s
    notFollowedBy (satisfy (\c -> isAlphaNum c || c == '_' || c == '\''))
    space

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
  -- make sure we don't treat '#' like an operator if it's followed by right paren
  notFollowedBy (string "#)")

  tick <- string "'" <|> pure ""
  -- skip package identifier
  _ <- optional packagePrefixP
  _ <- modulePrefixP
  c0 <- satisfy \c -> isAlpha c || c == ':' || c == '*' || c == '_' || c == '\''
  cs <- takeWhileP Nothing \c -> isAlphaNum c || isOperator c || c == '_' || c == '\''
  let ident = tick <> Text.cons c0 cs
  -- tyvars sometimes have some skolem info like @a[sk:1]
  when (isLower (Text.head ident)) do
    try (char '[' *> void (takeWhileP Nothing (/= ']')) <* char ']') <|> pure ()
  space
  pure ident

varP :: P (Var Text)
varP = do
  (satisfy \c -> isAlpha c || c == '_' || c == '$' || c == '@') >>= \case
    '@' -> do
      lookAhead anySingle >>= \case
        '(' -> do
          _ <- anySingle
          space
          var <- tyvar
          ty <- tysig
          string_ ")"
          pure (Tyvar var (Just ty))
        _ -> do
          var <- tyvar
          pure (Tyvar var Nothing)
    c0 -> do
      cs <- takeWhileP Nothing (\c -> isAlphaNum c || c == '_' || c == '\'' || c == '$' || c == '#')
      space
      ty <- pure Nothing -- optional tysig
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

bindingP :: P (Var Text)
bindingP = do
  asum
    [ varP,
      -- old varP parser always put parens cause they had typesigs
      -- do
      --   string_ "("
      --   var <- varP
      --   string_ ")"
      --   pure var,
      Var "_" Nothing <$ string_ "_"
    ]

litP :: P Lit
litP =
  asum
    [ do
        _ <- char '"'
        let hunk :: P Text
            hunk = takeWhileP Nothing (\c -> c /= '"' && c /= '\\')
        let hunks :: [Text] -> P Text
            hunks acc = do
              anySingle >>= \case
                '"' -> pure (Text.concat (reverse acc))
                '\\' ->
                  anySingle >>= \case
                    '\\' -> do
                      s <- hunk
                      hunks (s : "\\" : acc)
                    _ -> undefined
                c -> error (show c)
        s <- hunk
        str <- hunks [s]
        optional (char_ '#') <&> \case
          Nothing -> error "TODO non-# string"
          Just () -> LString str,
      do
        sign <- signP
        n0 <- intP
        n1 <-
          asum
            [ do
                x1 <- string "."
                x2 <- intP
                x3 <-
                  asum
                    [ do
                        x4 <- string "e"
                        x5 <- signP
                        x6 <- intP
                        pure (x4 <> x5 <> x6),
                      pure ""
                    ]
                pure (x1 <> x2 <> x3),
              pure ""
            ]

        suffix <-
          asum
            [ string "#Word64",
              string "##",
              string "#"
            ]
        space
        pure (LNumber (sign <> n0 <> n1) suffix)
    ]
  where
    signP :: P Text
    signP = string "-" <|> pure ""

    intP :: P Text
    intP = takeWhile1P Nothing isDigit

alternativeP :: P (Alternative Text, Expr Text)
alternativeP = do
  alt <-
    asum
      [ do
          string_ "__DEFAULT"
          pure ADef,
        ALit <$> litP,
        do
          string_ "(#"
          bindings <- sepBy varP (char_ ',')
          string_ "#)"
          pure (ATupleU bindings),
        AUnit <$ string_ "()",
        do
          char_ '('
          binding0 <- varP <* char_ ','
          binding1 <- varP
          bindings <- many (char_ ',' *> varP)
          char_ ')'
          pure (ATuple binding0 binding1 bindings),
        do
          constructor <- eidentP
          bindings <- many varP
          pure (ACon constructor bindings)
      ]
  string_ "->"
  expr <- exprP
  _ <- optional (string_ ";")
  pure (alt, expr)

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
      "jump",
      "let",
      "of"
    ]

isOperator :: Char -> Bool
isOperator c =
  c == '!'
    || c == '#'
    || c == '$'
    || c == '%'
    || c == '&'
    || c == '*'
    || c == '+'
    || c == '-'
    || c == '.'
    || c == '/'
    || c == ':'
    || c == '<'
    || c == '='
    || c == '>'
    || c == '?'
    || c == '@'
    || c == '\\'
    || c == '^'
    || c == '|'
    || c == '~'
