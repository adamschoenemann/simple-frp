
module FRP.Pretty
  ( module Text.PrettyPrint
  , Pretty(..)
  ) where

import Text.PrettyPrint

class Pretty p where
  ppr :: Int -> p -> Doc
  pp :: p -> Doc
  pp = ppr 0

  ppshow :: p -> String
  ppshow = render . ppr 0

