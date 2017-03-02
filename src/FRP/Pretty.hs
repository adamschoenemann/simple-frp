
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

  ppputStrLn :: p -> IO ()
  ppputStrLn = putStrLn . ppshow

instance (Pretty a, Pretty b) => Pretty (Either a b) where
  ppr n = \case
    Left l  -> ppr n l
    Right r -> ppr n r

instance (Pretty a, Pretty b) => Pretty (a,b) where
  ppr n (f,s) = parens (ppr n f <> char ',' <+> ppr n s)
