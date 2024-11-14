{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE ViewPatterns #-}

module Main where

import Data.Maybe
import GHC (SrcSpan (RealSrcSpan))
import GHC.Parser.Lexer (ParseResult (POk))
import GHC.Plugins hiding ((<>))
import Generics.SYB
import HsSoup
import Test.Hspec
import Test.Hspec.Golden
import Text.Show.Pretty

main = hspec do
  golden "k" $ return $ show $ case runGhcParser "module Main where main = return ()" of
    POk _ x -> gshow x
  golden "n" $ return $ show $ case runGhcParser "f x = x + 3" of
    POk _ (everything (<>) ((: []) . spanCat) -> x) -> map (\(RealSrcSpan a _, b) -> (srcspan4 a, b)) $ catMaybes x
  golden "m" $ return $ show $ tagHs "f x = x + 3\ng (Just x) = x"

srcspan4 s = (srcSpanStartLine s, srcSpanStartCol s, srcSpanEndLine s, srcSpanEndCol s)
