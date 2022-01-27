{-# LANGUAGE FlexibleInstances #-}

module HW3.Evaluator (eval) where

import Codec.Compression.Zlib
import Codec.Serialise
import Control.Monad.Cont (lift)
import Control.Monad.Trans.Except
import qualified Data.ByteString as B
import Data.ByteString.Lazy (fromStrict, toStrict)
import qualified Data.ByteString.Lazy.Internal as BytesLazy
import Data.Foldable
import Data.Map ((!))
import qualified Data.Map as DM
import Data.Ratio
import Data.Semigroup (stimes)
import Data.Sequence (Seq (..), fromList, (><))
import qualified Data.Sequence as S (drop, index, length, reverse, singleton, take)
import Data.Text (Text, index, pack)
import qualified Data.Text as T
import Data.Text.Encoding (decodeUtf8', encodeUtf8)
import Data.Time.Clock (UTCTime, addUTCTime, diffUTCTime)
import Data.Word (Word8)
import HW3.Base
import qualified Prelude.SafeEnum as SafeEnum (fromEnum)
import qualified Text.Read as TR (readMaybe)

-- I ended up with a very bad solution(
-- I am very sorry

-- | General class for String, List and ByteString
class GeneralSLB a where
  -- | Count elements in given object
  count :: a -> Int
  -- | Take the current number of elements
  takeElems :: Int -> a -> a
  -- | Drop the current number of elements
  dropElems :: Int -> a -> a
  -- | Corresponding @HiValue@
  hiValue :: a -> HiValue
  -- | Reverse
  freverse :: a -> a

  slice :: Int -> Int -> a -> a
  slice x y a = takeElems (y - x) (dropElems x a)

instance GeneralSLB T.Text where
  count = T.length
  takeElems = T.take
  dropElems = T.drop
  hiValue = HiValueString
  freverse = T.reverse

instance GeneralSLB (Seq HiValue) where
  count = S.length
  takeElems = S.take
  dropElems = S.drop
  hiValue list = HiValueList list
  freverse = S.reverse

instance GeneralSLB B.ByteString where
  count = B.length
  takeElems = B.take
  dropElems = B.drop
  hiValue = HiValueBytes
  freverse = B.reverse

evalJustValue :: HiMonad m => HiValue -> m (Either HiError HiValue)
evalJustValue = return . Right

-- | Function argument distributor
hiFunToDo
  :: HiMonad m
  => [HiExpr]                   -- ^ Arguments function
  -> HiFun                      -- ^ Current function
  -> ExceptT HiError m HiValue  -- ^ The result after applying the function to the arguments
hiFunToDo args hiF
  | isBinaryOperator hiF = jobWithBinaryOperator args hiF
  | isUnaryBool hiF = getOneArgumentWithDoSmt args $ \arg -> do
    x <- evalWithTo toBool arg
    return $ HiValueBool $ not x
  | isBinaryBool hiF = do
    case args of
      [x, y] -> do
        case hiF of
          HiFunAnd -> applyAndOrOrFunc x y id
          HiFunOr  -> applyAndOrOrFunc x y not
          _        -> throwE HiErrorInvalidFunction
      _ -> throwE HiErrorArityMismatch
  | isBinaryTypeToBool hiF = do
    goodArgs <- mapM (evalWithTo return) args
    case goodArgs of
      [x, y] -> do
        binaryFunctionByHiFunRationalBool <- getBinaryFunctionByHiFunRationalBool hiF
        return $ HiValueBool $ binaryFunctionByHiFunRationalBool x y
      _      -> throwE HiErrorArityMismatch
  | isIfFunc hiF = applyIfFunction args
  | isStringLengthFunc hiF = getOneArgumentWithDoSmt args $ \x -> do
    evalX <- evalE x
    case evalX of
      HiValueString str  -> jobWithUnarySEvalLength str
      HiValueList lst    -> jobWithUnarySEvalLength lst
      HiValueBytes bytes -> jobWithUnarySEvalLength bytes
      _                  -> throwInvalidArgument
  | isStringListFunc hiF = getOneArgumentWithDoSmt args $ \x -> do
    evalX <- evalE x
    case evalX of
     HiValueString str  -> jobWithUnarySEval str hiF getUnaryFunctionByHiFunString
     HiValueList lst    -> jobWithUnarySEval lst hiF getReverseFunction
     HiValueBytes bytes -> jobWithUnarySEval bytes hiF getReverseFunction
     _                  -> throwInvalidArgument
  | isByteFunc hiF = getOneArgumentWithDoSmt args $ \x -> do
    evalX <- evalE x
    case hiF of
      HiFunPackBytes   -> packArgument evalX
      HiFunUnpackBytes -> unpackArgument evalX
      HiFunZip         -> zipArgument evalX
      HiFunUnzip       -> unZipArgument evalX
      HiFunEncodeUtf8  -> encodeUtf8Argument evalX
      HiFunDecodeUtf8  -> decodeUtf8Argument evalX
      HiFunSerialise   -> serializeArgument evalX
      HiFunDeserialise -> deserialiseArgument evalX
      _                -> throwE HiErrorInvalidFunction
  | otherwise = do
    case hiF of
      HiFunRead      -> abstractApplyPathFunction args HiActionRead
      HiFunWrite     -> applyWrite args
      HiFunMkDir     -> abstractApplyPathFunction args HiActionMkDir
      HiFunChDir     -> abstractApplyPathFunction args HiActionChDir
      HiFunParseTime -> applyTime args
      HiFunRand      -> applyRand args
      HiFunEcho      -> applyEcho args
      HiFunKeys      -> applyKeyOrVals DM.keys args
      HiFunValues    -> applyKeyOrVals DM.elems args
      HiFunCount     -> applyCount args
      HiFunInvert    -> applyInvert args
      _              -> throwE HiErrorInvalidFunction

-- | Takes only one element from the list of arguments, otherwise throws an error. And then do something
getOneArgumentWithDoSmt
  :: HiMonad m
  => [t]                        -- ^ Arguments
  -> (t -> ExceptT HiError m b) -- ^ do function
  -> ExceptT HiError m b        -- ^ Result
getOneArgumentWithDoSmt args doSmt = do
  arg <- getOneArgument args
  doSmt arg

-- | Invert dictionary in arguments
applyInvert
  :: HiMonad m
  => [HiExpr]                   -- ^ Arguments. If more one argument or argument isn't dictionary - throw error
  -> ExceptT HiError m HiValue  -- ^ Result dictionary
applyInvert args = getOneArgumentWithDoSmt args $ \arg -> do
  dict <- evalWithTo toDict arg
  return $ HiValueDict $ invertDict dict

-- | Invert dictionary
invertDict :: DM.Map HiValue HiValue -> DM.Map HiValue HiValue
invertDict dict = DM.map HiValueList (DM.fromListWith (><) (map (\(a, b) -> (b, S.singleton a)) (DM.toList dict)))

-- | Counts unique values in arguments
applyCount
  :: HiMonad m
  => [HiExpr]                   -- ^ Arguments. If more one argument or argument isn't String, List and Bytes - throw error
  -> ExceptT HiError m HiValue  -- ^ Result count dictionary
applyCount args = getOneArgumentWithDoSmt args $ \arg -> do
  evalX <- evalE arg
  case evalX of
    HiValueString str -> do
      listString <- stringToListString str
      countElemsHiValue listString
    HiValueList list -> countElemsHiValue $ toList list
    HiValueBytes bytes -> countElemsHiValue $ map (HiValueNumber . toRational) (B.unpack bytes)
    _ -> throwInvalidArgument

-- | For each element, counts the number of its occurrences in the list
countElems :: (Ord a) => [a] -> DM.Map a Integer
countElems = DM.fromListWith (+) . flip zip (repeat 1)

countElemsHiValue :: HiMonad m => [HiValue] -> ExceptT HiError m HiValue
countElemsHiValue list = return $ HiValueDict $ DM.map (HiValueNumber . toRational) (countElems list)

-- | Convert string to list with string
--  Example: "abcd" -> ["a", "b", "c", "d"]
stringToListString :: HiMonad m => T.Text -> ExceptT HiError m [HiValue]
stringToListString = return . map (HiValueString . T.pack . return) . T.unpack

-- | Returns the keys or values of a dictionary
applyKeyOrVals
  :: HiMonad m
  => (DM.Map HiValue HiValue -> [HiValue]) -- ^ Keys or values function
  -> [HiExpr]                              -- ^ Arguments. If the arguments are not a dictionary, then an error is thrown
  -> ExceptT HiError m HiValue             -- ^ Keys or values result
applyKeyOrVals fromDict args = getOneArgumentWithDoSmt args $ \arg -> do
  dict <- evalWithTo toDict arg
  return $ HiValueList $ fromList $ fromDict dict

-- | Apply @echo@ function
applyEcho
  :: HiMonad m
  => [HiExpr]                   -- ^ Arguments. If the arguments are not a string, then an error is thrown
  -> ExceptT HiError m HiValue  -- ^ Returns action for echo
applyEcho args = getOneArgumentWithDoSmt args $ \arg -> do
  str <- evalWithTo toString arg
  return $ HiValueAction $ HiActionEcho str

-- | Apply @rand@ function. Similar behavior as for @applyEcho@, only for rand
applyRand :: HiMonad m => [HiExpr] -> ExceptT HiError m HiValue
applyRand args = do
  _ <- getFirstInBinary args
  allGood <- mapM (evalWithTo rationalToInt) args
  lft <- getFirstInBinary allGood
  rnd <- getSecondInBinary allGood
  if lft <= rnd
  then return $ HiValueAction $ HiActionRand lft rnd
  else return HiValueNull

-- | Apply @parse-time@ function. Similar behavior as for @applyEcho@, only for time
applyTime :: HiMonad m => [HiExpr] -> ExceptT HiError m HiValue
applyTime args = getOneArgumentWithDoSmt args $ \arg -> do
  timeStr <- evalWithTo  toString arg
  let timeMaybe = TR.readMaybe $ T.unpack timeStr :: Maybe UTCTime
  case timeMaybe of
    Nothing   -> return HiValueNull
    Just time -> return $ HiValueTime time

-- | Apply @mkdir@, @read@ or @cd@ function.
abstractApplyPathFunction
  :: HiMonad m
  => [HiExpr]                   -- ^ Arguments. If the arguments are not a string, then an error is thrown
  -> (String -> HiAction)       -- ^ The corresponding function that returns the action
  -> ExceptT HiError m HiValue  -- ^ Returns action
abstractApplyPathFunction args wrapAction = getOneArgumentWithDoSmt args $ \arg -> do
  path <- evalWithTo toString arg
  return $ HiValueAction $ wrapAction $ T.unpack path

-- | Apply @write@ function.
applyWrite :: HiMonad m => [HiExpr] -> ExceptT HiError m HiValue
applyWrite args = do
  pathExpr <- getFirstInBinary args
  messageExpr <- getSecondInBinary args
  path <- evalWithTo toString pathExpr
  message <- evalE messageExpr
  case message of
    HiValueBytes bytes ->
      return $ HiValueAction $ HiActionWrite (T.unpack path) bytes
    _ -> do
      bytesVal <- encodeUtf8Argument message
      bytes <- toByteString bytesVal
      return $ HiValueAction $ HiActionWrite (T.unpack path) bytes

-- | Apply extend @and@ or @or@ function.
applyAndOrOrFunc
  :: HiMonad m
  => HiExpr                     -- ^ Left expression
  -> HiExpr                     -- ^ Right expression
  -> (Bool -> Bool)             -- ^ @not@ or @id@ function, depending on whether it is an @and@ or a @or@
  -> ExceptT HiError m HiValue  -- ^ Return true or false
applyAndOrOrFunc x y ifF = do
  evalX <- evalE x
  boolX <- toBoolExtended evalX
  if ifF boolX
  then evalE y
  else return evalX

-- | Evaluate expression and then applies "to" function
evalWithTo
  :: HiMonad m
  => (HiValue -> ExceptT HiError m b) -- ^ "to" function
  -> HiExpr                           -- ^ Expression for evaluate
  -> ExceptT HiError m b              -- ^ Result or error
evalWithTo toFunc expr = do
  evalExpr <- evalE expr
  toFunc evalExpr

serializeArgument :: HiMonad m => HiValue -> ExceptT HiError m HiValue
serializeArgument val = return $ HiValueBytes $ toStrict $ serialise val

deserialiseArgument :: HiMonad m => HiValue -> ExceptT HiError m HiValue
deserialiseArgument val = do
  bytes <- toByteString val
  return $ deserialise $ fromStrict bytes

zipUnzipArgument
  :: HiMonad m
  => (BytesLazy.ByteString -> BytesLazy.ByteString)
  -> HiValue
  -> ExceptT HiError m HiValue
zipUnzipArgument zipUnzipFunc value = do
  bytes <- toByteString value
  let change = zipUnzipFunc (fromStrict bytes)
  return $ HiValueBytes $ toStrict change

unZipArgument :: HiMonad m => HiValue -> ExceptT HiError m HiValue
unZipArgument = zipUnzipArgument decompress

zipArgument :: HiMonad m => HiValue -> ExceptT HiError m HiValue
zipArgument = zipUnzipArgument $ compressWith (defaultCompressParams {compressLevel = bestCompression})

decodeUtf8Argument :: HiMonad m => HiValue -> ExceptT HiError m HiValue
decodeUtf8Argument value = do
  bytes <- toByteString value
  return $ case decodeUtf8' bytes of
    Right str -> HiValueString str
    Left _    -> HiValueNull

encodeUtf8Argument :: HiMonad m => HiValue ->  ExceptT HiError m HiValue
encodeUtf8Argument value = do
  str <- toString value
  return $ HiValueBytes $ encodeUtf8 str

unpackArgument :: HiMonad m => HiValue -> ExceptT HiError m HiValue
unpackArgument evalExpr = do
  byteString <- toByteString evalExpr
  return $ HiValueList $ fromList $ map (HiValueNumber . toRational) (B.unpack byteString)

packArgument :: HiMonad m => HiValue -> ExceptT HiError m HiValue
packArgument evalExpr = do
  list <- toHiList evalExpr
  numbers <- mapM toNumber list
  goodNumbers <- mapM checkNumberForPack numbers
  return $ HiValueBytes $ B.pack $ toList goodNumbers

checkNumberForPack :: HiMonad m => Rational -> ExceptT HiError m Word8
checkNumberForPack r =
  if denominator r == 1 && 0 <= r && r < 256
  then notThrowE (fromInteger $ numerator r)
  else throwInvalidArgument

-- | Returns one argument, checking that there are exactly one argument in the arguments
getOneArgument :: HiMonad m => [a] -> ExceptT HiError m a
getOneArgument args = case args of
  [x] -> notThrowE x
  _   -> throwE HiErrorArityMismatch

-- | Returns first argument, checking that there are exactly two arguments in the arguments
getFirstInBinary :: HiMonad m => [a] -> ExceptT HiError m a
getFirstInBinary args = case args of
  [x, _] -> notThrowE x
  _      -> throwE HiErrorArityMismatch

-- | Returns second argument, checking that there are exactly two arguments in the arguments
getSecondInBinary :: HiMonad m => [a] -> ExceptT HiError m a
getSecondInBinary args = case args of
  [_, y] -> notThrowE y
  _      -> throwE HiErrorArityMismatch

-- | Return first element in list or @HiValueNull@
getTypeArgs :: [HiValue] -> HiValue
getTypeArgs (x:_) = x
getTypeArgs []    = HiValueNull

-- | Check denominator
checkDivide :: HiMonad m => Rational -> ExceptT HiError m ()
checkDivide y = if y == 0 then throwE HiErrorDivideByZero else notThrowE ()

-- | Applies a binary operator (add, sub, mul or add) on various elements
jobWithBinaryOperator :: HiMonad m => [HiExpr] -> HiFun -> ExceptT HiError m HiValue
jobWithBinaryOperator args hiF = do
  goodArgs <- mapM (evalWithTo return) args
  let typeArgs = getTypeArgs goodArgs
  case typeArgs of
    (HiValueNumber _) -> do
      rationalArgs <- mapM toNumber goodArgs
      case rationalArgs of
        [x, y] -> do
          _ <- case hiF of
            HiFunDiv -> checkDivide y
            _        -> notThrowE ()
          binaryFunctionByHiFunRational <- getBinaryFunctionByHiFunRational hiF
          return $ HiValueNumber $ binaryFunctionByHiFunRational x y
        _      -> throwE HiErrorArityMismatch
    (HiValueString _) -> case hiF of
      HiFunMul -> jobWithRightMultiplication goodArgs toString
      HiFunDiv -> jobWithDivOrAddS HiFunDiv goodArgs toString getBinaryFunctionByHiFunString
      HiFunAdd -> jobWithDivOrAddS HiFunAdd goodArgs toString getBinaryFunctionByHiFunString
      _        -> throwE HiErrorInvalidFunction
    (HiValueList _) -> case hiF of
      HiFunMul -> jobWithRightMultiplication goodArgs toHiList
      HiFunAdd -> jobWithDivOrAddS HiFunAdd goodArgs toHiList getBinaryFunctionByHiFunS
      _        -> throwE HiErrorInvalidFunction
    (HiValueBytes _) -> case hiF of
      HiFunMul -> jobWithRightMultiplication goodArgs toByteString
      HiFunAdd -> jobWithDivOrAddS HiFunAdd goodArgs toByteString getBinaryFunctionByHiFunS
      _        -> throwE HiErrorInvalidFunction
    (HiValueTime _) -> case hiF of
      HiFunAdd -> applyAddNumberToTime args
      HiFunSub -> applySubTime args
      _        -> throwE HiErrorInvalidFunction
    _ -> throwInvalidArgument

-- | Counts the time difference
applySubTime :: HiMonad m => [HiExpr] -> ExceptT HiError m HiValue
applySubTime args = do
  evalArgs <- mapM (evalWithTo return) args
  a <- getFirstInBinary evalArgs
  b <- getSecondInBinary evalArgs
  timeLeft <- toOurTime a
  timeRight <- toOurTime b
  return $ HiValueNumber $ toRational $ diffUTCTime timeLeft timeRight

-- | Adds number to time
applyAddNumberToTime :: HiMonad m => [HiExpr] -> ExceptT HiError m HiValue
applyAddNumberToTime args = do
  evalArgs <- mapM (evalWithTo return) args
  a <- getFirstInBinary evalArgs
  b <- getSecondInBinary evalArgs
  time <- toOurTime a
  addToTime <- rationalToInteger b
  return $ HiValueTime $ addUTCTime (fromInteger addToTime) time

-- | String, list or bytesString multiplication to constant or throw error
jobWithRightMultiplication
  :: (HiMonad m, Semigroup t, GeneralSLB t)
  => [HiValue]                            -- ^ Arguments
  -> (HiValue -> ExceptT HiError m t)     -- ^ "to" function for String, list or byteString
  -> ExceptT HiError m HiValue            -- ^ Result after multiplication or throw error
jobWithRightMultiplication args toLeft =
  case args of
    [x, y] -> do
     goodX <- toLeft x
     goodY <- toGoodMulToGeneralSLB y
     return $ hiValue $ stimes goodY goodX
    _ -> throwE HiErrorArityMismatch

-- | General function for add or div string, list or byteString
jobWithDivOrAddS
  :: (HiMonad m, GeneralSLB t)
  => HiFun                                          -- ^ HiFunDiv or HiFunAdd
  -> [HiValue]                                      -- ^ Evaluate arguments
  -> (HiValue -> ExceptT HiError m t)               -- ^ "to" function for string, list or byteString
  -> (HiFun -> ExceptT HiError m (t -> t -> t))     -- ^ Getter for binary function
  -> ExceptT HiError m HiValue
jobWithDivOrAddS hi hiValues toGeneralSLB getBinary = case hiValues of
  [x, y] -> do
    goodX <- toGeneralSLB x
    goodY <- toGeneralSLB y
    binary <- getBinary hi
    return $ hiValue $ binary goodX goodY
  _ -> throwE HiErrorArityMismatch

-- | Calculates its length by the generalSLB object
jobWithUnarySEvalLength :: (HiMonad m, GeneralSLB f) => f -> ExceptT HiError m HiValue
jobWithUnarySEvalLength goodArg = do
  return $ HiValueNumber $ (fromInteger . toInteger . count) goodArg

-- | Applies a unary function to string, list or byteString. Functions like reverse (trim, to-upper or to-lower for list)
jobWithUnarySEval :: (HiMonad m, GeneralSLB f) => t1 -> t2 -> (t2 -> ExceptT HiError m (t1 -> f)) -> ExceptT HiError m HiValue
jobWithUnarySEval goodArg hiF getFunc = do
  func <- getFunc hiF
  return $ hiValue $ func goodArg

-- ^ Check is int a good in slice element
toGoodBorder
  :: HiMonad m
  => Int                    -- ^ Return this value if current HiValue is HiValueNull
  -> Int                    -- ^ Length GeneralSLB object
  -> HiValue                -- ^ Checked HiValue if it good slice element
  -> ExceptT HiError m Int  -- ^ return -1 if not good slice element otherwise this good element
toGoodBorder ifNull len val =
  case val of
    HiValueNull -> except $ Right ifNull
    _ -> do
      bord <- rationalToInt val
      let positive = min (if bord >= 0 then bord else bord + len) len
      if 0 <= positive && positive <= len
      then  except $ Right positive
      else  except $ Right (-1)

-- | Checked current HiValue is good @Integer@
rationalToInteger :: HiMonad m => HiValue -> ExceptT HiError m Integer
rationalToInteger value = do
  r <- toNumber value
  if denominator r == 1
  then notThrowE $ numerator r
  else throwInvalidArgument

-- | Checked current HiValue is good @Int@
rationalToInt :: HiMonad m => HiValue -> ExceptT HiError m Int
rationalToInt value = do
  r <- rationalToInteger value
  let maybeInt = SafeEnum.fromEnum r
  maybe throwInvalidArgument notThrowE maybeInt

-- | Eval arguments and check is a good index or good slise elements
--   If hiExprs not numbers or not integer number - throw error
--   If one element then if the index is in an array,
--            then we simply return the array from this index, otherwise we return an empty list
--   If there are two arguments, then apply the @toGoodBorder@ for them if @toGoodBorder@ return -1 then return [0,0]
getArgsInGoodView :: HiMonad m => [HiExpr] -> Int -> ExceptT HiError m [Int]
getArgsInGoodView args len = case args of
  [x] -> do
    ind <- evalWithTo rationalToInt x
    if 0 <= ind && ind < len
    then return [ind]
    else return []
  [x, y] -> do
    goodX <- evalWithTo (toGoodBorder 0 len) x
    if goodX == -1
    then return [0, 0]
    else do
      goodY <- evalWithTo (toGoodBorder len len) y
      if goodY == -1 || goodX > goodY
      then return [0, 0]
      else return [goodX, goodY]
  _ -> throwE HiErrorArityMismatch

-- | Constructs an expression that should be evaluated if the @fold@ runs
makeExprToFold :: HiValue -> Seq HiValue -> HiExpr
makeExprToFold fun vals = foldl1 (func exprFun) exprVals
  where
    func exprFunc x y = HiExprApply exprFunc [x, y]
    exprFun = HiExprValue fun
    exprVals = fmap HiExprValue vals

-- | Checks if the arguments can be applied to the given expression, if so applies
checkNumberArguments :: HiMonad m => ExceptT HiError m HiValue -> [HiExpr] -> ExceptT HiError m HiValue
checkNumberArguments evalApplyFunc args = do
  val <- evalApplyFunc
  case val of
    HiValueFunction fun -> case fun of
      HiFunList -> do
        evalArgs <- mapM (evalWithTo return) args
        return $ HiValueList $ fromList evalArgs
      HiFunRange -> do
        goodArgs <- mapM (evalWithTo toNumber) args
        case goodArgs of
          [x, y] -> return $ HiValueList $ fromList $ map HiValueNumber (enumFromTo x y)
          _      -> throwE HiErrorArityMismatch
      HiFunFold -> do
        case args of
          [x, y] -> do
            goodX <- evalE x
            goodY <- evalWithTo toHiList y
            case goodY of
              Empty -> return HiValueNull
              _     -> evalE $ makeExprToFold goodX goodY
          _ -> throwE HiErrorArityMismatch
      _ -> do
        numberOfArguments <- getNumberOfArguments fun
        if length args /= numberOfArguments
        then throwE HiErrorArityMismatch
        else hiFunToDo args fun
    HiValueString text -> workWithGeneralSLB args text (\x -> HiValueString $ pack [index text x]) HiValueString
    HiValueList lst -> workWithGeneralSLB args lst (S.index lst) HiValueList
    HiValueBytes bytes -> workWithGeneralSLB args bytes (HiValueNumber . toRational . B.index bytes) HiValueBytes
    HiValueDict mapa -> getOneArgumentWithDoSmt args $ \arg -> do
      evalArg <- evalE arg
      if evalArg `DM.member` mapa
      then return $ mapa ! evalArg
      else return HiValueNull
    _ -> throwE HiErrorInvalidFunction

-- | Tries to apply arguments to objects of class @GeneralSLB@
workWithGeneralSLB :: (HiMonad m, GeneralSLB t) => [HiExpr] -> t -> (Int -> HiValue) -> (t -> HiValue) -> ExceptT HiError m HiValue
workWithGeneralSLB args folds indexFunc wrapHiValue = do
  argsGood <- getArgsInGoodView args (count folds)
  case argsGood of
    []     -> except $ Right HiValueNull
    [x]    -> except $ Right $ indexFunc x
    [x, y] -> except $ Right $ wrapHiValue $ slice x y folds
    _      -> throwE HiErrorArityMismatch

-- | Many "to" functions

toBool :: HiMonad m => HiValue -> ExceptT HiError m Bool
toBool hiVal =
  case hiVal of
    HiValueBool bool -> return bool
    _                -> throwInvalidArgument

-- | Extended to bool
toBoolExtended :: HiMonad m => HiValue -> ExceptT HiError m Bool
toBoolExtended hiVal =
  case hiVal of
   HiValueBool bool -> return bool
   HiValueNull      -> return False
   _                -> return True

toString :: HiMonad m => HiValue -> ExceptT HiError m Text
toString hiVal =
  case hiVal of
    HiValueString str -> return str
    _                 -> throwInvalidArgument

toNumber :: HiMonad m => HiValue -> ExceptT HiError m Rational
toNumber hiVal =
  case hiVal of
    HiValueNumber num -> return num
    _                 -> throwInvalidArgument

toGoodMulToGeneralSLB :: HiMonad m => HiValue -> ExceptT HiError m Integer
toGoodMulToGeneralSLB hiVal = do
  num <- toNumber hiVal
  if num <= 0 || denominator num /= 1
  then throwInvalidArgument
  else return $ numerator num

toHiList :: HiMonad m => HiValue -> ExceptT HiError m (Seq HiValue)
toHiList hiVal =
  case hiVal of
    HiValueList ss -> return ss
    _              -> throwInvalidArgument

toByteString :: HiMonad m => HiValue -> ExceptT HiError m B.ByteString
toByteString hiVal =
  case hiVal of
    HiValueBytes ss -> return ss
    _               -> throwInvalidArgument

toOurTime :: HiMonad m => HiValue -> ExceptT HiError m UTCTime
toOurTime hiVal =
  case hiVal of
    HiValueTime time -> return time
    _                -> throwInvalidArgument

toDict :: HiMonad m => HiValue -> ExceptT HiError m (DM.Map HiValue HiValue)
toDict hiVal =
  case hiVal of
    HiValueDict dict -> return dict
    _                -> throwInvalidArgument

throwInvalidArgument :: HiMonad m => ExceptT HiError m a
throwInvalidArgument = throwE HiErrorInvalidArgument

applyIfFunction :: HiMonad m => [HiExpr] -> ExceptT HiError m HiValue
applyIfFunction [boolExpr, x, y] = do
  bool <- evalWithTo toBool boolExpr
  if bool
  then ExceptT $ eval x
  else ExceptT $ eval y
applyIfFunction _ = throwE HiErrorArityMismatch

tryApplyFunc :: HiMonad m => HiExpr -> [HiExpr] -> ExceptT HiError m HiValue
tryApplyFunc applyFunc = checkNumberArguments (ExceptT $ eval applyFunc)

notThrowE :: (HiMonad m) => a -> ExceptT HiError m a
notThrowE = except . Right

-- | Returns arity current function
getNumberOfArguments :: HiMonad m => HiFun -> ExceptT HiError m Int
getNumberOfArguments hi = case hi of
  HiFunDiv            -> notThrowE 2
  HiFunMul            -> notThrowE 2
  HiFunAdd            -> notThrowE 2
  HiFunSub            -> notThrowE 2
  HiFunNot            -> notThrowE 1
  HiFunAnd            -> notThrowE 2
  HiFunOr             -> notThrowE 2
  HiFunLessThan       -> notThrowE 2
  HiFunGreaterThan    -> notThrowE 2
  HiFunEquals         -> notThrowE 2
  HiFunNotLessThan    -> notThrowE 2
  HiFunNotGreaterThan -> notThrowE 2
  HiFunNotEquals      -> notThrowE 2
  HiFunIf             -> notThrowE 3
  HiFunLength         -> notThrowE 1
  HiFunToUpper        -> notThrowE 1
  HiFunToLower        -> notThrowE 1
  HiFunReverse        -> notThrowE 1
  HiFunTrim           -> notThrowE 1
  HiFunRange          -> notThrowE 2
  HiFunFold           -> notThrowE 2
  HiFunPackBytes      -> notThrowE 1
  HiFunUnpackBytes    -> notThrowE 1
  HiFunEncodeUtf8     -> notThrowE 1
  HiFunDecodeUtf8     -> notThrowE 1
  HiFunZip            -> notThrowE 1
  HiFunUnzip          -> notThrowE 1
  HiFunSerialise      -> notThrowE 1
  HiFunDeserialise    -> notThrowE 1
  HiFunRead           -> notThrowE 1
  HiFunWrite          -> notThrowE 2
  HiFunMkDir          -> notThrowE 1
  HiFunChDir          -> notThrowE 1
  HiFunParseTime      -> notThrowE 1
  HiFunRand           -> notThrowE 2
  HiFunEcho           -> notThrowE 1
  HiFunCount          -> notThrowE 1
  HiFunKeys           -> notThrowE 1
  HiFunValues         -> notThrowE 1
  HiFunInvert         -> notThrowE 1
  HiFunList           -> throwInvalidArgument

getBinaryFunctionByHiFunRational :: HiMonad m => HiFun -> ExceptT HiError m (Rational -> Rational -> Rational)
getBinaryFunctionByHiFunRational hi = case hi of
  HiFunDiv -> notThrowE (/)
  HiFunMul -> notThrowE (*)
  HiFunAdd -> notThrowE (+)
  HiFunSub -> notThrowE (-)
  _        -> throwInvalidArgument

getBinaryFunctionByHiFunString :: HiMonad m => HiFun -> ExceptT HiError m (T.Text -> T.Text -> T.Text)
getBinaryFunctionByHiFunString hi = case hi of
  HiFunDiv -> notThrowE $ \a b -> a <> T.pack "/" <> b
  HiFunAdd -> getBinaryFunctionByHiFunS HiFunAdd
  _        -> throwInvalidArgument

getBinaryFunctionByHiFunS :: (HiMonad m, Semigroup a) => HiFun -> ExceptT HiError m (a -> a -> a)
getBinaryFunctionByHiFunS hi = case hi of
  HiFunAdd -> notThrowE (<>)
  _        -> throwInvalidArgument

getBinaryFunctionByHiFunRationalBool :: (HiMonad m, Ord a) => HiFun -> ExceptT HiError m (a -> a -> Bool)
getBinaryFunctionByHiFunRationalBool hi = case hi of
  HiFunLessThan       -> notThrowE (<)
  HiFunGreaterThan    -> notThrowE (>)
  HiFunEquals         -> notThrowE (==)
  HiFunNotLessThan    -> notThrowE (>=)
  HiFunNotGreaterThan -> notThrowE (<=)
  HiFunNotEquals      -> notThrowE (/=)
  _                   -> throwInvalidArgument

getReverseFunction :: (HiMonad m, GeneralSLB f) => HiFun -> ExceptT HiError m (f -> f)
getReverseFunction hi = case hi of
  HiFunReverse -> notThrowE freverse
  _            -> throwInvalidArgument

getUnaryFunctionByHiFunString :: HiMonad m => HiFun -> ExceptT HiError m (T.Text -> T.Text)
getUnaryFunctionByHiFunString hi = case hi of
  HiFunToUpper -> notThrowE T.toUpper
  HiFunToLower -> notThrowE T.toLower
  HiFunReverse -> notThrowE freverse
  HiFunTrim    -> notThrowE T.strip
  _            -> throwInvalidArgument

-- | Apply action function
applyAction :: HiMonad m => HiExpr -> ExceptT HiError m HiValue
applyAction expression = do
  val <- evalE expression
  case val of
    (HiValueAction action) -> lift $ runAction action
    _                      -> throwInvalidArgument

evalPair :: HiMonad m => (HiExpr, HiExpr) -> ExceptT HiError m (HiValue, HiValue)
evalPair (a, b) = do
  evalA <- evalE a
  evalB <- evalE b
  return (evalA, evalB)

evalKeysValuesDict :: HiMonad m => [(HiExpr, HiExpr)] -> ExceptT HiError m HiValue
evalKeysValuesDict list = do
  evalList <- mapM evalPair list
  return $ HiValueDict $ DM.fromList evalList

evalE :: HiMonad m => HiExpr -> ExceptT HiError m HiValue
evalE = ExceptT . eval

eval :: HiMonad m => HiExpr -> m (Either HiError HiValue)
eval (HiExprValue val)            = evalJustValue val
eval (HiExprApply applyFunc args) = runExceptT $ tryApplyFunc applyFunc args
eval (HiExprRun expression)       = runExceptT $ applyAction expression
eval (HiExprDict listKeyValue)    = runExceptT $ evalKeysValuesDict listKeyValue

