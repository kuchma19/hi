{-# LANGUAGE BlockArguments #-}

module HW3.Action where

import Control.Exception.Base (Exception)
import Data.Set (Set)
import GHC.Base (ap, liftM)

data HiPermission =
    AllowRead
  | AllowWrite
  | AllowTime
  deriving (Eq, Show, Ord, Enum, Bounded)

newtype PermissionException = PermissionRequired HiPermission
  deriving (Eq, Show)

instance Exception PermissionException

newtype HIO a = HIO { runHIO :: Set HiPermission -> IO a }

instance Functor HIO where
  fmap = liftM

instance Applicative HIO where
  pure = return
  (<*>) = ap

instance Monad HIO where
  return a = HIO \_ -> return a
  ma >>= ama = HIO \setPermission ->
    do
      a <- runHIO ma setPermission
      runHIO (ama a) setPermission



