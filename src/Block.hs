{-# language BangPatterns #-}
{-# language DataKinds #-}
{-# language LambdaCase #-}
{-# language KindSignatures #-}
{-# language GADTs #-}
{-# language StandaloneKindSignatures #-}
{-# language RankNTypes #-}
{-# language NamedFieldPuns #-}

-- | A block of instructions that are executed contiguously. This is commonly
--   known as a \"basic block\". There should be no branching
--   instructions in a basic block. This library provides a subset of what
--   @hoopl@ does, but this library is more minimal. It is unconcerned
--   with block graphs and consequently does not deal with block labels.
--   Additionally, some of the types are simpler. The @Block@
--   type in @hoopl@ has 8 data constructors, but the similar @Builder@ type
--   from this library has only 5 data constructors. Two important design
--   decisions made in this library:
--
--   * The 'Builder' type has a data constructor 'Empty'. If 'Append' is
--     is understood as categorical composition, then 'Empty' is the
--     categorical identity. By pattern matching on 'Builder' (which
--     is not recommended), it is possible to distiguish @Append a Empty@
--     from @a@. However, the 'run' function erases 'Empty', causing
--     the 'Block' values resulting from those two expressions to be
--     identical. Technically, 'Empty' could have been omitted from
--     the 'Builder' type, but in practice, it is desirable to have
--     a 'Builder' with \"no-op\" semantics. In a recursive function or
--     a fold that produces an instruction sequence, the base case
--     is often a no-op action. By including 'Empty' in 'Builder'
--     rather than requiring the underlying @instr@ type to supply
--     a no-op instruction, it is possible to make 'run' recognize it
--     and remove it.
--
--   * Entry and exit must be separate intructions. That is,
--     a value of type @instr 'Closed 'Closed@ cannot be lifted into
--     a 'Builder'. This is enforced by the type system. This limitation
--     keeps the 'Block' type simple. If closed-closed instructions
--     were allowed, then 'Block' would not be guaranteed to have both
--     @entry@ and @exit@ fields. In practice, closed-closed instructions
--     are nonexistent, so this limitation comes at no practical cost.
module Block
  ( -- * Types
    Openness(..)
  , Block(..)
  , Builder(..)
    -- * Run Builder
  , run
    -- * Analyze Block
  , fold
  ) where

import Control.Monad.ST (ST)
import Control.Monad.ST.Run (runSmallArrayST)
import Data.Kind (Type)
import Data.Primitive (SmallArray,SmallMutableArray)

import qualified Data.Primitive as PM

type Openness :: Type

-- | If a block is open on one side, it means that more instructions
-- can be appended to that side. If it is closed, then no more
-- instructions can be appended.
data Openness = Open | Closed

type Block :: (Openness -> Openness -> Type) -> Type

-- | A closed block. This should be considered read-only since
-- it can not be cheaply modified.
data Block :: (Openness -> Openness -> Type) -> Type where
  Block ::
    { entry :: !(instr 'Closed 'Open)
    , middle :: !(SmallArray (instr 'Open 'Open))
    , exit :: !(instr 'Open 'Closed)
    } -> Block instr

type Builder :: (Openness -> Openness -> Type) -> Openness -> Openness -> Type

-- | A block builder. This may be open on either the entry or exit
-- side. The openness is tracked by types. Concatenation is O(1).
data Builder :: (Openness -> Openness -> Type) -> Openness -> Openness -> Type where
  -- | A no-op. This is erased by 'run'.
  Empty ::
    Builder instr 'Open 'Open
  -- | Lift an open-open instruction into a builder.
  Middle ::
       instr 'Open 'Open
    -> Builder instr 'Open 'Open
  -- | Lift a closed-open instruction into a builder
  Entry ::
       instr 'Closed 'Open
    -> Builder instr 'Closed 'Open
  -- | Lift an open-closed instruction into a builder.
  Exit ::
       instr 'Open 'Closed
    -> Builder instr 'Open 'Closed
  -- | Concatenate two builders
  Append ::
       Builder instr s 'Open
    -> Builder instr 'Open e
    -> Builder instr s e

-- | Run a builder, producing a 'Block' that can no longer be cheaply
-- modified. 
run ::
     Builder instr 'Closed 'Closed
  -> Block instr
run bldr = Block
  { exit = findExit bldr
  , entry = findEntry bldr
  , middle = findMiddle bldr
  }

findExit :: Builder instr s 'Closed -> instr 'Open 'Closed
findExit = \case
  Append _ b -> findExit b
  Exit x -> x

findEntry :: Builder instr 'Closed e -> instr 'Closed 'Open
findEntry = \case
  Append a _ -> findEntry a
  Entry x -> x

findMiddle :: Builder instr s e -> SmallArray (instr 'Open 'Open)
findMiddle bldr = runSmallArrayST $ do
  let !len = findMiddleLen bldr
  dst <- PM.newSmallArray len findMiddleError
  ixFinal <- pasteMiddle dst (len - 1) bldr
  case ixFinal of
    (-1) -> PM.unsafeFreezeSmallArray dst
    _ -> findMiddleError

findMiddleError :: a
{-# noinline findMiddleError #-}
findMiddleError = errorWithoutStackTrace "Block:run[findMiddle] implementation mistake"

-- index counts downward
pasteMiddle :: SmallMutableArray s (instr 'Open 'Open) -> Int -> Builder instr start e -> ST s Int
pasteMiddle !dst !ix = \case
  Exit{} -> pure ix
  Entry{} -> pure ix
  Empty -> pure ix
  Middle instr -> if ix >= 0
    then do
      PM.writeSmallArray dst ix instr
      pure (ix - 1)
    else findMiddleError
  Append a b -> do
    ix' <- pasteMiddle dst ix b
    pasteMiddle dst ix' a
  
findMiddleLen :: Builder instr s e -> Int
findMiddleLen = \case
  Empty -> 0
  Entry{} -> 0
  Exit{} -> 0
  Middle{} -> 1
  Append a b -> findMiddleLen a + findMiddleLen b

-- | Fold over all instrutions in a closed block.
fold :: Monoid m => (forall s e. instr s e -> m) -> Block instr -> m
fold f Block{entry,middle,exit} =
  f entry <> foldMap f middle <> f exit

