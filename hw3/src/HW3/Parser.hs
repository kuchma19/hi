{-# LANGUAGE BlockArguments #-}

module HW3.Parser where

import Control.Applicative (liftA2, many)
import Control.Monad.Combinators (sepEndBy)
import Control.Monad.Combinators.Expr (Operator (..), makeExprParser)
import Control.Monad.Identity (Identity)
import Data.ByteString (ByteString)
import qualified Data.ByteString as DB (pack)
import Data.Char (digitToInt, isAlpha, isAlphaNum)
import Data.Maybe (fromMaybe)
import Data.Scientific
import Data.Text (Text, pack)
import Data.Void (Void)
import Data.Word (Word8)
import HW3.Base
import Text.Megaparsec (Parsec, choice, label, optional, sepBy)
import qualified Text.Megaparsec as TM (ParsecT, eof, manyTill, notFollowedBy, parse, satisfy, try, sepBy1)
import Text.Megaparsec.Byte (string)
import Text.Megaparsec.Char (char, space, space1)
import qualified Text.Megaparsec.Char.Lexer as L
import Text.Megaparsec.Error
import Data.List (intercalate)

type Parser = Parsec Void String

parserWithSkipSpace :: Parser a -> Parser a
parserWithSkipSpace pars = space *> pars <* space

funParserByString :: String -> Parser HiValue
funParserByString = liftA2 (<$) (HiValueFunction . strToHiFun) string

boolParserByString :: String -> Parser HiValue
boolParserByString = liftA2 (<$) (HiValueBool . strToBoolean) string

stringParser :: Parser Text
stringParser = char '"' *> (pack <$> TM.manyTill L.charLiteral (char '"'))

singleCharByteParser :: Parser Word8
singleCharByteParser = do
  c <- choice $ map char (['0'..'9'] <> ['a'..'f'])
  return $ fromInteger $ toInteger (digitToInt c)

byteParser :: Parser Word8
byteParser = do
  first <- singleCharByteParser
  second <- singleCharByteParser
  return $ 16 * first + second

bytesParser :: Parser [Word8]
bytesParser = sepEndBy byteParser space1 <* optional space

parseCwdAction :: Parser HiAction
parseCwdAction = HiActionCwd <$ string "cwd"

parseNowAction :: Parser HiAction
parseNowAction = HiActionNow <$ string "now"

byteStringParser :: Parser ByteString
byteStringParser = string "[#" <* optional space *> (DB.pack <$> bytesParser) <* string "#]"

pairMapParser :: Parser (HiExpr, HiExpr)
pairMapParser = do
  right <- infixParser
  _ <- parserWithSkipSpace $ char ':'
  left <- infixParser
  return (right, left)

mapArgsParser :: Parser [(HiExpr, HiExpr)]
mapArgsParser = sepBy pairMapParser (parserWithSkipSpace (char ','))

valueFun :: Parser HiValue
valueFun = label "function"
  $ choice $ map funParserByString
  [ "div", "mul", "add", "sub", "and", "or", "less-than", "greater-than", "equals"
  , "not-less-than", "not-greater-than", "not-equals", "not", "if", "length", "to-upper"
  , "to-lower", "reverse", "trim", "list", "range", "fold", "pack-bytes", "unpack-bytes"
  , "zip", "unzip", "encode-utf8", "decode-utf8", "serialise", "deserialise", "read", "write"
  , "mkdir", "cd", "parse-time", "rand", "echo", "count", "keys", "values", "invert"
  ]

valueBool :: Parser HiValue
valueBool = label "bool"
  $ choice $ map boolParserByString [ "true", "false" ]

valueCwd :: Parser HiValue
valueCwd = label "cwd" $ HiValueAction <$> parseCwdAction

valueNow :: Parser HiValue
valueNow = label "now" $ HiValueAction <$> parseNowAction

valueNull :: Parser HiValue
valueNull = label "null" $ HiValueNull <$ string "null"

valueString :: Parser HiValue
valueString = label "string" $ HiValueString <$> stringParser

valueBytes :: Parser HiValue
valueBytes = label "bytes" $ HiValueBytes <$> byteStringParser

-- | Separate parser for '/' because there are problems with parse '/='
binaryDiv :: Operator Parser HiExpr
binaryDiv = InfixL (binaryConstructor HiFunDiv <$ divParse)

divParse :: Parser String
divParse = TM.try (string "/" <* TM.notFollowedBy (char '='))

-- | General function for binary operators operators
binary
  :: (TM.ParsecT Void String Identity (HiExpr -> HiExpr -> HiExpr) -> Operator Parser HiExpr)
                                        -- ^ Constructor for @Operator@. @InfixR@, @InfixN@ or @InfixL@
  -> String                             -- ^ String form binary operator
  -> HiFun                              -- ^ @HiFun@ of the corresponding binary operator
  -> Operator Parser HiExpr             -- ^ Actually - a @Operator@
binary infx name f = infx $ binaryConstructor f <$ parserWithSkipSpace (string name)

binaryConstructor :: HiFun -> HiExpr -> HiExpr -> HiExpr
binaryConstructor func a b = constructApply func [a, b]

constructApply :: HiFun -> [HiExpr] -> HiExpr
constructApply = HiExprApply . HiExprValue . HiValueFunction

operatorTable :: [[Operator Parser HiExpr]]
operatorTable =
  [ [ binaryDiv
    , binary InfixL "*" HiFunMul
    ]
  , [ binary InfixL "+" HiFunAdd
    , binary InfixL "-" HiFunSub
    ]
  , [ binary InfixN "==" HiFunEquals
    , binary InfixN "/=" HiFunNotEquals
    , binary InfixN "<=" HiFunNotGreaterThan
    , binary InfixN ">=" HiFunNotLessThan
    , binary InfixN ">" HiFunGreaterThan
    , binary InfixN "<" HiFunLessThan
    ]
  , [ binary InfixR "&&" HiFunAnd
    ]
  , [ binary InfixR "||" HiFunOr
    ]
  ]

infixParser :: Parser HiExpr
infixParser = makeExprParser expr operatorTable

-- | A parser that wraps the result of a given HiValue parser into a HiExpr
abstractExpr
  :: Parser HiValue -- ^ Given HiValue parser
  -> Parser HiExpr  -- ^ HiExpr parser
abstractExpr hiP = HiExprValue <$> parserWithSkipSpace hiP

boolExpr :: Parser HiExpr
boolExpr = abstractExpr valueBool

nullExpr :: Parser HiExpr
nullExpr = abstractExpr valueNull

stringExpr :: Parser HiExpr
stringExpr = abstractExpr valueString

funExpr :: Parser HiExpr
funExpr = abstractExpr valueFun

cwdExpr :: Parser HiExpr
cwdExpr = abstractExpr valueCwd

nowExpr :: Parser HiExpr
nowExpr = abstractExpr valueNow

listExpr :: Parser HiExpr
listExpr = constructApply HiFunList <$> abstractIn "[" "]"

bytesExpr :: Parser HiExpr
bytesExpr = abstractExpr valueBytes

dictExpr :: Parser HiExpr
dictExpr = HiExprDict <$> abstractInAnotherArgs mapArgsParser "{" "}"

exponentParser :: Parser Int
exponentParser = do
  _ <- char 'e'
  int <- L.signed space L.decimal
  return $ fromInteger int

numeric :: Parser Rational
numeric = do
  scientificValue <- L.signed space L.scientific
  maybeExponentValue <- optional exponentParser
  let exponentValue = fromMaybe 0 maybeExponentValue
  return $ toRational (scientificValue * scientific 1 exponentValue)

number :: Parser HiValue
number = label "number" $ HiValueNumber <$> parserWithSkipSpace numeric

numberExpr :: Parser HiExpr
numberExpr = abstractExpr number

-- | List arguments parser
argsParser :: Parser [HiExpr]
argsParser = sepBy infixParser (parserWithSkipSpace $ char ',')

abstractInAnotherArgs
  :: Parser a -- ^ Given parser
  -> String   -- ^ Parse should be done before parse given parser
  -> String   -- ^ Parse should be done after parse given parser
  -> Parser a -- ^ Result parser with before and after part
abstractInAnotherArgs prse left right = parserWithSkipSpace $ string left *> parserWithSkipSpace prse <* string right

-- | Argument list parser with given parentheses
abstractIn :: String -> String -> Parser [HiExpr]
abstractIn = abstractInAnotherArgs argsParser

argsWithParents :: Parser [HiExpr]
argsWithParents = abstractIn "(" ")"

-- | An expression parser that ignores arguments, run and dot style
exprWithoutArgsRunPoint :: Parser HiExpr
exprWithoutArgsRunPoint = do
  maybeParent <- optional $ parserWithSkipSpace $ char '('
  case maybeParent of
    Nothing -> choice $ map TM.try
        [ numberExpr
        , nullExpr
        , cwdExpr
        , nowExpr
        , stringExpr
        , boolExpr
        , funExpr
        , bytesExpr
        , listExpr
        , dictExpr
        ]
    (Just _) -> do
      val <- infixParser
      _ <- parserWithSkipSpace $ char ')'
      return val

expr :: Parser HiExpr
expr = do
  expression <- parserWithSkipSpace exprWithoutArgsRunPoint
  runArgsPoint expression

parsePointStile :: Parser [String]
parsePointStile = ((:) <$> TM.satisfy isAlpha <*> many (TM.satisfy isAlphaNum)) `TM.sepBy1` char '-'

-- | A parser that, according to a given expression,
--  determines if he has a certain number of arguments, run or dot style
runArgsPoint :: HiExpr -> Parser HiExpr
runArgsPoint expression = do
  run <- optional (parserWithSkipSpace $ char '!')
  case run of
    Nothing -> do
      argsMaybe <- optional argsWithParents
      case argsMaybe of
        Nothing -> do
          strMaybe <- optional (char '.' *> parsePointStile)
          case strMaybe of
            Nothing -> return expression
            Just str ->
              runArgsPoint $ HiExprApply expression [HiExprValue (HiValueString $ pack (intercalate "-" str))]
        Just args ->
          runArgsPoint $ HiExprApply expression args
    Just _ ->
      runArgsPoint $ HiExprRun expression

parse :: String -> Either (ParseErrorBundle String Void) HiExpr
parse = TM.parse (parserWithSkipSpace infixParser <* TM.eof) ""
