module Type where

import Data.Text (Text)

data Type
  = TApp Type Type [Type]
  | TForall [(Text, Maybe Type)] Type
  | TFun Type Type
  | TId Text
  | TTupleU [Type]
  deriving stock (Eq, Ord, Show)
