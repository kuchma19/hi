{-# LANGUAGE BlockArguments     #-}
{-# LANGUAGE DeriveAnyClass     #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE FlexibleInstances  #-}

module HW3.Base where

import Codec.Serialise (Serialise)
import Control.Exception (throwIO)
import Control.Monad (filterM)
import Data.ByteString (ByteString)
import qualified Data.ByteString as DB (readFile, writeFile)
import Data.Map (Map)
import qualified Data.Sequence as DS
import qualified Data.Set as S
import qualified Data.Text as T
import Data.Text.Encoding (decodeUtf8')
import Data.Time.Clock (UTCTime, getCurrentTime)
import GHC.Generics (Generic)
import HW3.Action
import System.Directory (createDirectory, doesDirectoryExist, doesFileExist, doesPathExist,
                         getCurrentDirectory, listDirectory, setCurrentDirectory)
import System.FilePath.Posix ((</>))
import System.Random (getStdRandom, randomR)

data HiFun
  = HiFunDiv
  | HiFunMul
  | HiFunAdd
  | HiFunSub
  | HiFunNot
  | HiFunAnd
  | HiFunOr
  | HiFunLessThan
  | HiFunGreaterThan
  | HiFunEquals
  | HiFunNotLessThan
  | HiFunNotGreaterThan
  | HiFunNotEquals
  | HiFunIf
  | HiFunLength
  | HiFunToUpper
  | HiFunToLower
  | HiFunReverse
  | HiFunTrim
  | HiFunList
  | HiFunRange
  | HiFunFold
  | HiFunPackBytes
  | HiFunUnpackBytes
  | HiFunEncodeUtf8
  | HiFunDecodeUtf8
  | HiFunZip
  | HiFunUnzip
  | HiFunSerialise
  | HiFunDeserialise
  | HiFunRead
  | HiFunWrite
  | HiFunMkDir
  | HiFunChDir
  | HiFunParseTime
  | HiFunRand
  | HiFunEcho
  | HiFunCount
  | HiFunKeys
  | HiFunValues
  | HiFunInvert
  deriving (Show, Eq, Ord)
  deriving stock (Generic)
  deriving anyclass (Serialise)

data HiValue
  = HiValueBool Bool
  | HiValueNumber Rational
  | HiValueFunction HiFun
  | HiValueNull
  | HiValueString T.Text
  | HiValueList (DS.Seq HiValue)
  | HiValueBytes ByteString
  | HiValueAction HiAction
  | HiValueTime UTCTime
  | HiValueDict (Map HiValue HiValue)
  deriving (Show, Eq, Ord)
  deriving stock (Generic)
  deriving anyclass (Serialise)

data HiExpr
  = HiExprValue HiValue
  | HiExprApply HiExpr [HiExpr]
  | HiExprRun HiExpr
  | HiExprDict [(HiExpr, HiExpr)]
  deriving (Show, Eq)

data HiError
  = HiErrorInvalidArgument
  | HiErrorInvalidFunction
  | HiErrorArityMismatch
  | HiErrorDivideByZero
  deriving (Show, Eq)

data HiAction =
    HiActionRead  FilePath
  | HiActionWrite FilePath ByteString
  | HiActionMkDir FilePath
  | HiActionChDir FilePath
  | HiActionCwd
  | HiActionNow
  | HiActionRand Int Int
  | HiActionEcho T.Text
  deriving (Show, Eq, Ord)
  deriving stock (Generic)
  deriving anyclass (Serialise)

class Monad m => HiMonad m where
  runAction :: HiAction -> m HiValue

ifPathExistsDo :: FilePath -> IO HiValue -> IO HiValue
ifPathExistsDo path doSmt = do
  ifExist <- doesPathExist path
  if ifExist
  then doSmt
  else return HiValueNull

checkPermission :: S.Set HiPermission -> [HiPermission] -> IO a -> IO a
checkPermission permissions needPermission doSmt = do
  let diff = S.difference (S.fromList needPermission) permissions
  if S.null diff
  then doSmt
  else throwIO $ PermissionRequired $ S.findMin diff

instance HiMonad HIO where
  runAction HiActionCwd = HIO \permissions ->
    checkPermission permissions [AllowRead] $ HiValueString . T.pack <$> getCurrentDirectory
  runAction (HiActionRead path) = HIO \permissions ->
    checkPermission permissions [AllowRead] $ ifPathExistsDo path $ do
    ifFile <- doesFileExist path
    if ifFile
    then do
      bytes <- DB.readFile path
      let eitherStr = decodeUtf8' bytes
      return $ case eitherStr of
        Left _    -> HiValueBytes bytes
        Right str -> HiValueString str
    else do
      listDir <- listDirectory path
      valsListDir <- filterM (doesDirectoryExist . (path </>)) listDir
      return $ HiValueList $ DS.fromList $ map (HiValueString . T.pack) valsListDir
  runAction (HiActionWrite path bytes) = HIO \permissions ->
    checkPermission permissions [AllowWrite] $ HiValueNull <$ DB.writeFile path bytes
  runAction (HiActionChDir path) = HIO \permissions ->
    checkPermission permissions [AllowRead] $ ifPathExistsDo path $ HiValueNull <$ setCurrentDirectory path
  runAction (HiActionMkDir path) = HIO \permissions ->
    checkPermission permissions [AllowWrite, AllowRead] $ do
      ifExist <- doesDirectoryExist path
      if ifExist
      then return HiValueNull
      else HiValueNull <$ createDirectory path
  runAction HiActionNow = HIO \permission ->
    checkPermission permission [AllowTime] $ HiValueTime <$> getCurrentTime
  runAction (HiActionRand l r) = HIO \permission ->
    checkPermission permission [] $ do
      g <- getStdRandom $ randomR (l, r)
      return $ HiValueNumber $ toRational g
  runAction (HiActionEcho str) = HIO \permission ->
    checkPermission permission [AllowWrite] $ HiValueNull <$ putStrLn (T.unpack str)

strToBoolean :: String -> Bool
strToBoolean s = case s of
  "true"  -> True
  "false" -> False
  _       -> error "unnoun boolean type"

strToHiFun :: String -> HiFun
strToHiFun s = case s of
  "div"              -> HiFunDiv
  "mul"              -> HiFunMul
  "add"              -> HiFunAdd
  "sub"              -> HiFunSub
  "not"              -> HiFunNot
  "and"              -> HiFunAnd
  "or"               -> HiFunOr
  "less-than"        -> HiFunLessThan
  "greater-than"     -> HiFunGreaterThan
  "equals"           -> HiFunEquals
  "not-less-than"    -> HiFunNotLessThan
  "not-greater-than" -> HiFunNotGreaterThan
  "not-equals"       -> HiFunNotEquals
  "if"               -> HiFunIf
  "length"           -> HiFunLength
  "to-upper"         -> HiFunToUpper
  "to-lower"         -> HiFunToLower
  "reverse"          -> HiFunReverse
  "trim"             -> HiFunTrim
  "list"             -> HiFunList
  "range"            -> HiFunRange
  "fold"             -> HiFunFold
  "pack-bytes"       -> HiFunPackBytes
  "unpack-bytes"     -> HiFunUnpackBytes
  "zip"              -> HiFunZip
  "unzip"            -> HiFunUnzip
  "encode-utf8"      -> HiFunEncodeUtf8
  "decode-utf8"      -> HiFunDecodeUtf8
  "serialise"        -> HiFunSerialise
  "deserialise"      -> HiFunDeserialise
  "read"             -> HiFunRead
  "write"            -> HiFunWrite
  "mkdir"            -> HiFunMkDir
  "cd"               -> HiFunChDir
  "parse-time"       -> HiFunParseTime
  "rand"             -> HiFunRand
  "echo"             -> HiFunEcho
  "count"            -> HiFunCount
  "keys"             -> HiFunKeys
  "values"           -> HiFunValues
  "invert"           -> HiFunInvert
  _                  -> error "unnoun function"

hiFunToStr :: HiFun -> String
hiFunToStr hi = case hi of
  HiFunDiv            -> "div"
  HiFunMul            -> "mul"
  HiFunAdd            -> "add"
  HiFunSub            -> "sub"
  HiFunNot            -> "not"
  HiFunAnd            -> "and"
  HiFunOr             -> "or"
  HiFunLessThan       -> "less-than"
  HiFunGreaterThan    -> "greater-than"
  HiFunEquals         -> "equals"
  HiFunNotLessThan    -> "not-less-than"
  HiFunNotGreaterThan -> "not-greater-than"
  HiFunNotEquals      -> "not-equals"
  HiFunIf             -> "if"
  HiFunLength         -> "length"
  HiFunToUpper        -> "to-upper"
  HiFunToLower        -> "to-lower"
  HiFunReverse        -> "reverse"
  HiFunTrim           -> "trim"
  HiFunList           -> "list"
  HiFunRange          -> "range"
  HiFunFold           -> "fold"
  HiFunPackBytes      -> "pack-bytes"
  HiFunUnpackBytes    -> "unpack-bytes"
  HiFunZip            -> "zip"
  HiFunUnzip          -> "unzip"
  HiFunEncodeUtf8     -> "encode-utf8"
  HiFunDecodeUtf8     -> "decode-utf8"
  HiFunSerialise      -> "serialise"
  HiFunDeserialise    -> "deserialise"
  HiFunRead           -> "read"
  HiFunWrite          -> "write"
  HiFunMkDir          -> "mkdir"
  HiFunChDir          -> "cd"
  HiFunParseTime      -> "parse-time"
  HiFunRand           -> "rand"
  HiFunEcho           -> "echo"
  HiFunCount          -> "count"
  HiFunKeys           -> "keys"
  HiFunValues         -> "values"
  HiFunInvert         -> "invert"

containsInClass :: [HiFun] -> HiFun -> Bool
containsInClass clazz hi = hi `elem` clazz

isBinaryOperator :: HiFun -> Bool
isBinaryOperator =
  containsInClass
    [ HiFunDiv,
      HiFunMul,
      HiFunAdd,
      HiFunSub
    ]

isUnaryBool :: HiFun -> Bool
isUnaryBool =
  containsInClass
    [ HiFunNot
    ]

isBinaryBool :: HiFun -> Bool
isBinaryBool =
  containsInClass
    [ HiFunAnd,
      HiFunOr
    ]

isBinaryTypeToBool :: HiFun -> Bool
isBinaryTypeToBool =
  containsInClass
    [ HiFunLessThan,
      HiFunGreaterThan,
      HiFunEquals,
      HiFunNotLessThan,
      HiFunNotGreaterThan,
      HiFunNotEquals
    ]

isIfFunc :: HiFun -> Bool
isIfFunc =
  containsInClass
    [ HiFunIf
    ]

isStringLengthFunc :: HiFun -> Bool
isStringLengthFunc =
  containsInClass
    [ HiFunLength
    ]

isStringListFunc :: HiFun -> Bool
isStringListFunc =
  containsInClass
    [ HiFunToUpper,
      HiFunToLower,
      HiFunReverse,
      HiFunTrim
    ]

isByteFunc :: HiFun -> Bool
isByteFunc =
  containsInClass
    [ HiFunPackBytes
    , HiFunUnpackBytes
    , HiFunZip
    , HiFunUnzip
    , HiFunEncodeUtf8
    , HiFunDecodeUtf8
    , HiFunSerialise
    , HiFunDeserialise
    ]
