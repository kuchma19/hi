module HW3.Pretty where

import Data.ByteString as T (unpack)
import qualified Data.ByteString as DB (null)
import Data.Char (toLower)
import Data.Map as M (null, toList)
import Data.Maybe (isNothing)
import Data.Ratio (denominator, numerator)
import Data.Scientific (FPFormat (Fixed), formatScientific, fromRationalRepetendUnlimited)
import Data.Sequence (Seq (..))
import HW3.Base
import Numeric (showHex)
import Prettyprinter.Internal (Doc, pretty, viaShow, (<+>))
import Prettyprinter.Render.Terminal (AnsiStyle)

prettyValue :: HiValue -> Doc AnsiStyle
prettyValue (HiValueFunction fun) = pretty $ hiFunToStr fun
prettyValue (HiValueNumber r)
  | den == 1 = pretty num
  | isNothing b = pretty $ formatScientific Fixed Nothing a
  | quo == 0 = printFraction id
  | otherwise = pretty quo <+> pretty sgn <+> printFraction abs
  where
    num = numerator r
    den = denominator r
    (a, b) = fromRationalRepetendUnlimited r
    (quo, re) = quotRem num den
    sgn = if signum re < 0 then '-' else '+'
    printFraction funcWithRe = pretty (funcWithRe re) <> pretty '/' <> pretty den
prettyValue (HiValueBool bool) = pretty $ map toLower (show bool)
prettyValue (HiValueString str) = viaShow str
prettyValue HiValueNull = pretty "null"
prettyValue (HiValueList hiValues) = case hiValues of
  Empty -> pretty "[ ]"
  _     -> showLists "[ " "]" ((<+>) . (<> pretty ",")) (fmap prettyValue hiValues)
prettyValue (HiValueBytes byteList) =
  if not $ DB.null byteList
  then showLists "[# " "#]" (<+>) (map (pretty . goodViewWord) (unpack byteList))
  else pretty "[# #]"
prettyValue (HiValueAction action) = actionToPretty action
prettyValue (HiValueTime time) = pretty "parse-time" <> inParent (viaShow (show time))
prettyValue (HiValueDict mapa) =
  if M.null mapa
  then pretty "{" <+> pretty "}"
  else showLists "{ " "}" ((<+>) . (<> pretty ",")) (map prettyKeyValue (M.toList mapa))

prettyKeyValue :: (HiValue, HiValue) -> Doc AnsiStyle
prettyKeyValue (key, val) =  prettyValue key <> pretty ":" <+> prettyValue val

showError :: HiError -> Doc AnsiStyle
showError = pretty . show

showLists :: (Foldable t) => String -> String -> (Doc ann -> Doc ann -> Doc ann) -> t (Doc ann) -> Doc ann
showLists open close foldFunc hiValues =
      pretty open
  <> foldl1 foldFunc hiValues
  <+> pretty close

goodViewWord :: (Integral a, Show a) => a -> String
goodViewWord i = case i `showHex` "" of
  [x] -> ['0', x]
  m   -> m

inParent :: Doc AnsiStyle -> Doc AnsiStyle
inParent p = pretty "(" <> p <> pretty ")"

prettyWithPath :: String -> FilePath -> Doc AnsiStyle
prettyWithPath str path = pretty str <> inParent (viaShow path)

actionToPretty :: HiAction -> Doc AnsiStyle
actionToPretty action = case action of
   HiActionRead path -> prettyWithPath "read" path
   HiActionWrite path bytes -> pretty "write" <> inParent (viaShow path <> pretty "," <+> prettyValue (HiValueBytes bytes))
   HiActionMkDir path -> prettyWithPath "mkdir" path
   HiActionChDir path ->  prettyWithPath "cd" path
   HiActionCwd -> pretty "cwd"
   HiActionNow -> pretty "now"
   HiActionRand a b -> pretty "rand" <> inParent (pretty a <> pretty "," <+> pretty b)
   HiActionEcho str -> pretty "echo" <> inParent (viaShow str)
