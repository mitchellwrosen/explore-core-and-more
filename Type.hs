module Type where

import Data.Text (Text)

data Type
  = TApp Type Type [Type]
  | TConstraint Type Type
  | TForall [(Text, Maybe Type)] Type
  | TFun Type Type
  | TId Text
  | TTuple Type Type [Type] -- 2+ elements
  | TTupleU [Type] -- 0+ elements: (# #), (# ty #), (# ty, ty2 #), etc
  deriving stock (Eq, Ord, Show)
