-- | Behavioural oracles for "Circuit.STM".
--
-- Each witness states the exact observable of a queue strategy: which write
-- blocks, which write overwrites, and what a reader sees afterwards.  A
-- strategy that quietly changed to a different buffering discipline fails
-- here; there is no appeal to "the existing behaviour".
module Main (main) where

import Circuit.Axioma.Test (check)
import Circuit.Category (K (..), runK)
import Circuit.Machine (Poles (..), pipe, polesK)
import Circuit.STM
import Control.Concurrent (threadDelay)
import Control.Concurrent.Async (async, cancel, poll, waitSTM)
import Control.Concurrent.STM hiding (check)
import Control.Concurrent.STM qualified as STM
import Control.Monad (unless)
import Data.Functor (($>))
import Data.Maybe (isNothing)
import System.Exit (exitFailure)
import System.Timeout (timeout)
import Prelude hiding (read)

-- | Delay used to decide that an operation has blocked.
patience :: Int
patience = 50000

-- | Generous delay for a pipelined read, which waits on a pump thread.
patienceIO :: Int
patienceIO = 1000000

-- | Write end of an STM pair.
writeEnd :: Poles () (K STM) a a -> a -> STM ()
writeEnd e = runK (commit e)

-- | Read end of an STM pair.
readEnd :: Poles () (K STM) a a -> STM a
readEnd e = runK (emit e) ()

-- | Write end of an IO pair.
writeEndIO :: Poles () (K IO) a a -> a -> IO ()
writeEndIO e = runK (commit e)

-- | Read end of an IO pair.
readEndIO :: Poles () (K IO) a a -> IO a
readEndIO e = runK (emit e) ()

-- | Whether the transaction fails to complete within 'patience'.
blocksSTM :: STM a -> IO Bool
blocksSTM act = do
  delay <- registerDelay patience
  atomically $
    (act $> False) `orElse` ((readTVar delay >>= STM.check) $> True)

-- | Whether the action fails to complete within 'patience'.
blocksIO :: IO a -> IO Bool
blocksIO act = do
  a <- async act
  threadDelay patience
  r <- poll a
  case r of
    Nothing -> cancel a $> True
    Just _ -> pure False

queueTopic :: IO [Bool]
queueTopic =
  sequence
    [ do
        e <- atomically (openSTM (Unbounded :: Queue Int))
        w1 <- blocksSTM (writeEnd e 1)
        w2 <- blocksSTM (writeEnd e 2)
        w3 <- blocksSTM (writeEnd e 3)
        xs <- atomically (sequence [readEnd e, readEnd e, readEnd e])
        check "Unbounded: no write blocks and every token is read in FIFO order" $
          not (w1 || w2 || w3) && xs == [1, 2, 3],
      do
        e <- atomically (openSTM (Bounded 1 :: Queue Int))
        atomically (writeEnd e 1)
        w <- async (atomically (writeEnd e 2))
        threadDelay patience
        pending <- poll w
        first <- atomically (readEnd e)
        atomically (waitSTM w)
        second <- atomically (readEnd e)
        check "Bounded 1: the second write blocks until a read, then delivers the first" $
          isNothing pending && first == 1 && second == 2,
      do
        e <- atomically (openSTM (Single :: Queue Int))
        atomically (writeEnd e 1)
        w <- async (atomically (writeEnd e 2))
        threadDelay patience
        pending <- poll w
        first <- atomically (readEnd e)
        atomically (waitSTM w)
        second <- atomically (readEnd e)
        check "Single: the second write blocks until a read, then delivers the first" $
          isNothing pending && first == 1 && second == 2,
      do
        e <- atomically (openSTM (SwapQ :: Queue Int))
        w1 <- blocksSTM (writeEnd e 1)
        w2 <- blocksSTM (writeEnd e 2)
        x <- atomically (readEnd e)
        emptied <- blocksSTM (readEnd e)
        check "SwapQ: the second write replaces the unread first and a read empties the slot" $
          not (w1 || w2) && x == 2 && emptied,
      do
        e <- atomically (openSTM (Latest 0 :: Queue Int))
        w1 <- blocksSTM (writeEnd e 1)
        w2 <- blocksSTM (writeEnd e 2)
        xs <- atomically (sequence [readEnd e, readEnd e])
        check "Latest: writes never block, the newest wins, and reads do not empty" $
          not (w1 || w2) && xs == [2, 2],
      do
        e <- atomically (openSTM (Newest 2 :: Queue Int))
        w1 <- blocksSTM (writeEnd e 1)
        w2 <- blocksSTM (writeEnd e 2)
        w3 <- blocksSTM (writeEnd e 3)
        xs <- atomically (sequence [readEnd e, readEnd e])
        check "Newest 2: an overflowing write drops the oldest token, never blocks" $
          not (w1 || w2 || w3) && xs == [2, 3],
      do
        e <- atomically (openChannelSTM (Linear :: ChannelPolicy Int))
        blocked <- blocksSTM (writeEnd e 7)
        x <- atomically (readEnd e)
        check "ChannelPolicy Linear is an unbounded FIFO channel" $
          not blocked && x == 7,
      do
        e <- atomically (openChannelSTM (SwapOne :: ChannelPolicy Int))
        atomically (writeEnd e 1)
        atomically (writeEnd e 2)
        x <- atomically (readEnd e)
        check "ChannelPolicy SwapOne replaces an unread token" $
          x == 2,
      do
        e <- openIO (Bounded 1 :: Queue Int)
        emptyBlocked <- blocksIO (readEndIO e)
        writeEndIO e 5
        x <- readEndIO e
        check "openIO: a read blocks on an empty queue and sees a written token" $
          emptyBlocked && x == 5
    ]

haltTopic :: IO [Bool]
haltTopic =
  sequence
    [ do
        h <- atomically openHaltChannel
        absent <- blocksSTM (readHaltChannel h)
        atomically (writeHaltChannel h (42 :: Int))
        x <- atomically (readHaltChannel h)
        consumed <- blocksSTM (readHaltChannel h)
        check "a halt channel blocks on absence and consumes the token it reads" $
          absent && x == 42 && consumed,
      do
        unit <- atomically (runK (commit unitEndsSTM) () *> runK (emit unitEndsSTM) ())
        check "unitEndsSTM writes and reads the unit token" $
          unit == ()
    ]

-- | A two-read consumer: it needs both tokens before it can answer.
pairSumEnds :: TQueue Int -> Poles () (K IO) Int Int
pairSumEnds q =
  polesK (atomically . writeTQueue q) (atomically $ (+) <$> readTQueue q <*> readTQueue q)

pipeTopic :: IO [Bool]
pipeTopic =
  sequence
    [ do
        -- The degeneracy that earns the queue: 'pipe' composes through the
        -- unit carrier, so the intermediate wire is read once and a consumer
        -- that needs two tokens never completes.
        e1 <- openLinearChannel :: IO (Poles () (K IO) Int Int)
        q <- newTQueueIO
        let composed = pipe e1 (pairSumEnds q)
        writeEndIO composed 1
        writeEndIO composed 2
        serial <- timeout patienceIO (readEndIO composed)
        check "pipe over allocated ends serialises the intermediate read" $
          isNothing serial,
      do
        e1 <- openLinearChannel :: IO (Poles () (K IO) Int Int)
        (pipeline, shutdown) <- pipeEnds e1 (pure . pairSumEnds)
        writeEndIO pipeline 1
        writeEndIO pipeline 2
        total <- timeout patienceIO (readEndIO pipeline)
        shutdown
        check "pipeEnds pumps both tokens, so the two-read consumer answers 3" $
          total == Just 3,
      do
        left <- openLinearChannel :: IO (Poles () (K IO) Int Int)
        (composite, shutdown) <-
          pipeEnds left $ \q ->
            pure (polesK (atomically . writeTQueue q) (atomically (readTQueue q)))
        writeEndIO composite 1
        writeEndIO composite 2
        x <- readEndIO composite
        y <- readEndIO composite
        shutdown
        check "pipeEnds: the pump moves tokens through the intermediate queue in order" $
          x == 1 && y == 2,
      do
        left <- openLinearChannel :: IO (Poles () (K IO) Int Int)
        (composite, shutdown) <-
          pipeEnds left $ \q ->
            pure (polesK (atomically . writeTQueue q) (atomically (readTQueue q)))
        shutdown
        writeEndIO composite 3
        stalled <- blocksIO (readEndIO composite)
        check "pipeEnds: closing cancels the pump, so later writes are never read" stalled
    ]

main :: IO ()
main = do
  results <- concat <$> sequence [queueTopic, haltTopic, pipeTopic]
  unless (and results) $ do
    putStrLn "Some tests failed."
    exitFailure
  putStrLn "\nAll tests passed."
