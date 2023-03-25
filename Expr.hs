module Expr where

import Data.Text (Text)
import Type

data Expr
  = EId Text
  | ELit Lit
  | EApp Expr Expr [Expr] -- f a b c d ...
  | ELam [Var] Expr
  | -- | Let   (Bind b) (Expr b)
    ECase Expr (Maybe Text) [Alternative]
  | ETy Type
  -- \| Cast  (Expr b) CoercionR
  -- \| Tick  CoreTickish (Expr b)
  -- \| Type  Type
  -- \| Coercion Coercion
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
  = ACon Text [Var] Expr
  | ALit Text Expr
  | ADef Expr
  deriving stock (Show)
