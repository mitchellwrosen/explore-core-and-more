module Expr where

import Data.Text (Text)
import Type

data Expr
  = EId Text
  | ELit Lit
  | EApp Expr Expr [Expr] -- f a b c d ...
  | ELam [Var] Expr
  | -- | Let   (Bind b) (Expr b)
    ECase Expr (Maybe Text) [(Alternative, Expr)]
  | ELet Text Expr Expr
  | EJoin JoinPoint Expr
  | EJoinrec [JoinPoint] Expr
  | ETy Type
  | ETupleU [Expr]
  -- \| Cast  (Expr b) CoercionR
  -- \| Tick  CoreTickish (Expr b)
  -- \| Type  Type
  -- \| Coercion Coercion
  deriving stock (Show)

-- TODO use this in EId
data Ident = Ident
  { package :: Maybe Text,
    modules :: [Text],
    name :: Text
  }

data JoinPoint
  = JoinPoint Text [Var] Expr
  deriving stock (Show)

data Lit
  = LInt Text -- 0
  | LIntU Text -- 0#
  | LStrU Text -- "foobar"#
  | LWord64U Text -- 0##64
  deriving stock (Show)

data Var
  = Tyvar Text (Maybe Type) -- '@foo'
  | Var Text (Maybe Type) -- 'Foo.Bar.baz'
  deriving stock (Show)

data Alternative
  = ACon Text [Var]
  | ATupleU [Var]
  | ALit Lit
  | ADef
  deriving stock (Show)
