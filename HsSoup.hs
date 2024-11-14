{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# OPTIONS_GHC -Wno-typed-holes #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use first" #-}

module HsSoup where

import Data.Data (typeOf)
import Data.Function (on)
import Data.IntMap (IntMap)
import qualified Data.IntMap as M
import Data.List (groupBy)
import Data.Maybe (catMaybes)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.These (These (..))
import Data.Zip (Semialign (align))
import GHC
  ( GenLocated (L),
    GhcPs,
    HsExpr,
    HsModule,
    HsType,
    Located,
    Pat,
    RealSrcSpan,
    SrcSpan (RealSrcSpan),
    SrcSpanAnn' (..),
    srcSpanEndCol,
    srcSpanEndLine,
    srcSpanStartCol,
    srcSpanStartLine,
  )
import qualified GHC.Data.EnumSet as EnumSet
import GHC.Data.FastString (mkFastString)
import qualified GHC.Data.Strict as S
import GHC.Data.StringBuffer (stringToStringBuffer)
import GHC.Hs (SrcSpanAnnN)
import GHC.Parser (parseModule)
import GHC.Parser.Lexer
  ( P (unP),
    ParseResult (POk),
    initParserState,
    mkParserOpts,
  )
import GHC.Plugins (defaultSDocContext, parsedResultModule)
import GHC.Types.SrcLoc
  ( GenLocated (L),
    Located,
    RealSrcSpan,
    SrcSpan (RealSrcSpan),
    mkRealSrcLoc,
    srcSpanEndCol,
    srcSpanEndLine,
    srcSpanStartCol,
    srcSpanStartLine,
  )
import GHC.Utils.Error (DiagOpts (DiagOpts))
import Generics.SYB
  ( Data (gmapQ, gmapQi),
    GenericQ,
    Proxy (..),
    Typeable,
    cast,
    everything,
    typeOf,
    typeRep,
  )

-- * Public API

data Cat
  = -- | 'HsExpr'
    IsExp
  | -- | 'Pat'
    IsPat
  | -- | 'HsType'
    IsType
  deriving (Eq, Ord, Show)

-- | tag the input string with ghc's syntax tree
--
-- > id == map snd . taggedFileContents
tagHs :: String -> [(Maybe Cat, String)]
tagHs = map (\(a, b) -> (fmap snd a, b)) . tagHs_

-- | tagHs with the 'RealSrcSpan' referencing the <interactive> file
tagHs_ :: String -> [(Maybe (RealSrcSpan, Cat), String)]
tagHs_ str = case runGhcParser str of
  POk _ (spanCats -> x) ->
    map (\xs -> (fst (head xs), map snd xs)) $
      groupBy (on (==) fst) $
        map (\(k, c) -> (smmLookup k x, c)) $
          rowcol str
  _ -> []
  where
    rowcol :: String -> [((Int, Int), Char)]
    rowcol xs = concat $ zipWith (\i -> zipWith (\j e -> ((i, j), e)) [1 ..]) [1 ..] $ lines xs

-- | adapts the example in "GHC.Parser"
runGhcParser :: String -> ParseResult (Located (HsModule GhcPs))
runGhcParser str = unP GHC.Parser.parseModule parseState
  where
    filename = "<interactive>"
    location = mkRealSrcLoc (mkFastString filename) 1 1
    buffer = stringToStringBuffer str
    parseState = initParserState opts buffer location
    opts = mkParserOpts (EnumSet.fromList [minBound .. maxBound]) dopts [] False True True False
    dopts = DiagOpts mempty mempty False False Nothing defaultSDocContext

-- * Implementation

-- ** Generic programming

-- | Apply 'spanCat' to every node in the syntax tree and union the results
spanCats :: GenericQ (SMM Cat)
spanCats = everything smmUnion (maybe mempty f . spanCat)
  where
    f (RealSrcSpan s _, c) = smmSingleton s c

-- | maybe assign a 'Cat' to part of ghc's syntax tree
--
-- the straightforward way to do this is to use 'mkQ' and 'extQ' as below,
-- but a concrete type for the `l` in `L l a :: GenLocated (SrcSpanAnn' l) a`
-- is needed, and it seems that there isn't a single one that can work.
--
-- > spanCat = mkQ Nothing (\(L s (a :: HsExpr GhcPs)) -> Just (locA s, IsExp)) `extQ` ...
spanCat :: GenericQ (Maybe (SrcSpan, Cat))
spanCat x = do
  2 <- Just (nfields x)
  (,)
    <$> gmapQi
      0
      ( \y -> do
          2 <- Just (nfields y)
          gmapQi 1 cast y
      )
      x
    <*> gmapQi 1 castCat x
  where
    nfields :: (Data a) => a -> Int
    nfields x = length $ gmapQ (const ()) x

castCat :: (Typeable a) => a -> Maybe Cat
castCat x = lookup (typeOf x) table
  where
    table =
      [ (typeRep (Proxy :: Proxy (HsExpr GhcPs)), IsExp),
        (typeRep (Proxy :: Proxy (Pat GhcPs)), IsPat),
        (typeRep (Proxy :: Proxy (HsType GhcPs)), IsType)
      ]

-- * segment tree

-- | an interval is the same element stored at start and end points
--
-- The hgeometry package has a segment tree. That might be more efficient
-- if many intervals overlap. This one is relatively simple. Moreover,
-- the segment tree is only 1D while this one is 2D.
data SMM a = SMM {_startPoint, _endPoint :: MM (RealSrcSpan, a)}
  deriving (Show)

instance (Ord a) => Semigroup (SMM a) where
  (<>) = smmUnion

instance (Ord a) => Monoid (SMM a) where
  mempty = SMM M.empty M.empty

-- | The outer key is the line number, the inner key is the column number
type MM a = IntMap (IntMap (Set a))

-- | Should return the smallest span that contains the point.
-- Perhaps it should return a list which would be sorted by distance
-- to the farthest endpoint of the span?
smmLookup :: (Ord a) => (Int, Int) -> SMM a -> Maybe (RealSrcSpan, a)
smmLookup k (SMM m n) = go Set.empty $ concatMap (Set.toList . snd) $ catThese $ lookupLE k m `align` lookupGE k n
  where
    -- optimization: keep a sLeft and sRight?
    go s [] = Nothing
    go s (x : xs)
      | Set.member x s = Just x
      | otherwise = go (Set.insert x s) xs

catThese :: [These a a] -> [a]
catThese = concatMap \case
  This x -> [x]
  That x -> [x]
  These x y -> [x, y]

lookupLE :: (Int, Int) -> MM a -> [((Int, Int), Set a)]
lookupLE (l, c) m =
  let (u, mr, _) = M.splitLookup l m
      consMR = maybe id (\r rest -> (l, r) : rest) mr
   in catMaybes
        [ f <$> M.lookupLE c r
          | (k, r) <- consMR $ M.toDescList u,
            let f (a, b) = ((k, a), b)
        ]

lookupGE :: (Int, Int) -> MM a -> [((Int, Int), Set a)]
lookupGE (l, c) m =
  let (u, mr, _) = M.splitLookup l m
      consMR = maybe id (\r rest -> (l, r) : rest) mr
   in catMaybes
        [ f <$> M.lookupGE c r
          | (k, r) <- consMR $ M.toAscList u,
            let f (a, b) = ((k, a), b)
        ]

smmUnion :: (Ord a) => SMM a -> SMM a -> SMM a
smmUnion (SMM m n) (SMM m' n') = SMM (mmUnion m m') (mmUnion n n')

mmUnion :: (Ord a) => MM a -> MM a -> MM a
mmUnion = M.unionWith (M.unionWith Set.union)

smmSingleton :: RealSrcSpan -> a -> SMM a
smmSingleton s v =
  let m = mmSingleton (srcSpanStartLine s) (srcSpanStartCol s) (s, v)
      n = mmSingleton (srcSpanEndLine s) (srcSpanEndCol s) (s, v)
   in SMM m n

mmSingleton :: Int -> Int -> a -> MM a
mmSingleton k k' v = M.singleton k (M.singleton k' (Set.singleton v))
