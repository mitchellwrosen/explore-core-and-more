module Expr where

import Data.Text (Text)
import Type

data Expr
  = EId [Text] Text -- A.B.C.xyz = [A,B,C] xyz
  | ELit Text
  | EApp Expr Expr [Expr] -- f a b c d ...
  | ELam [Text] Expr
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
