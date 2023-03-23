module Expr where

import Data.Text (Text)
import Type

data Expr
  = EId (Qualified Text)
  | ELit Text
  | EApp Expr [Expr]
  | ELam [Binding] Expr
  | -- | Let   (Bind b) (Expr b)
    ECase Expr (Maybe Text) [Alternative]
  -- \| Cast  (Expr b) CoercionR
  -- \| Tick  CoreTickish (Expr b)
  -- \| Type  Type
  -- \| Coercion Coercion
  deriving stock (Show)

data Alternative
  = ACon Text [Text] Expr
  | ALit Text Expr
  | ADef Expr
  deriving stock (Show)

data Binding = Binding
  { var :: Text,
    props :: Maybe Text,
    ty :: Maybe Text
  }
  deriving stock (Show)

-- TODO move this
data Qualified a
  = Qualified [Text] a
  deriving stock (Show)

