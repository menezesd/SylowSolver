module DebugLog
  ( setDebugEnabled
  , dtrace
  , dputStrLn
  ) where

import System.IO.Unsafe (unsafePerformIO)
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import qualified Debug.Trace as DTrace

{-# NOINLINE debugRef #-}
debugRef :: IORef Bool
debugRef = unsafePerformIO (newIORef False)

setDebugEnabled :: Bool -> IO ()
setDebugEnabled = writeIORef debugRef

{-# INLINE debugEnabled #-}
debugEnabled :: Bool
debugEnabled = unsafePerformIO (readIORef debugRef)

{-# INLINE dtrace #-}
dtrace :: String -> a -> a
dtrace msg x = if debugEnabled then DTrace.trace msg x else x

dputStrLn :: String -> IO ()
dputStrLn msg = if debugEnabled then DTrace.traceIO msg else pure ()
