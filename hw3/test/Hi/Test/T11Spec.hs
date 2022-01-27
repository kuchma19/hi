{-# LANGUAGE QuasiQuotes #-}
module Hi.Test.T11Spec (spec) where

import Text.RawString.QQ

import HW3.Base
import Hi.Test.Common

spec :: Spec
-- spec = emptyTest
spec = do
  describe "dictionaries" $ do
    it "dict literal" $ do
      [r|{ "width": 120, "height": 80 }|] ~=?? Ok [r|{ "height": 80, "width": 120 }|]
      [r|{}|] ~=?? Ok [r|{ }|]
      [r|  { "a"  : 0 }  |] ~=?? Ok [r|{ "a": 0 }|]
      [r|{ 1 + 2 : 1 + 2 }|] ~=?? Ok [r|{ 3: 3 }|]
    it "dict func" $ do
      [r|{ "width": 120, "height": 80 }("width")|] ~=?? Ok "120"
    it "dict null" $ do
      [r|{ "width": 120, "height": 80 }("aaaa")|] ~=?? Ok "null"
    it "dict dot" $ do
      [r|{ "width": 120, "height": 80 }.width|] ~=?? Ok "120"
      [r|{ "complex-ke-a1": 30 }.complex-ke-a1|] ~=?? Ok "30"
--      [r|{ "a-1": 1}.a-1|] ~=?? ParseError "" -- i don't know about that
      [r|{ "a": echo}.a.b!|] ~=?? Ok "null"
      [r|{ "a": echo}.a.b !|] ~=?? ParseError ""
      [r|{ "a": echo}.a. b!|] ~=?? ParseError ""
      [r|{ "a": echo}.a .b!|] ~=?? ParseError ""
      [r|{ "a": echo}. a.b!|] ~=?? ParseError ""
      [r|{ "a": echo} .a.b!|] ~=?? ParseError ""
      [r|{ "a": echo}.a. b !|] ~=?? ParseError ""
      [r|{ "a": echo}.a . b !|] ~=?? ParseError ""
      [r|{ "a": echo}.a .b !|] ~=?? ParseError ""
      [r|{ "a": echo}. a.b !|] ~=?? ParseError ""
      [r|{ "a": echo} .a.b !|] ~=?? ParseError ""
      [r|{ "a": echo} .a .b !|] ~=?? ParseError ""
      [r|{ "a": echo} . a .b !|] ~=?? ParseError ""
      [r|{ "a": echo} .a . b !|] ~=?? ParseError ""
      [r|{ "a": echo} . a . b !|] ~=?? ParseError ""
    it "keys and values" $ do
      [r|keys({ "width": 120, "height": 80 })|] ~=?? Ok [r|[ "height", "width" ]|]
      [r|values({ "width": 120, "height": 80 })|] ~=?? Ok [r|[ 80, 120 ]|]
    it "count" $ do
      [r|count("XXXOX")|] ~=?? Ok [r|{ "O": 1, "X": 4 }|]
      [r|count([true, true, false, true])|] ~=?? Ok [r|{ false: 1, true: 3 }|]
    it "invert" $ do
      [r|invert({ "x": 1, "y" : 2, "z": 1 })|] ~=?? Ok [r|{ 1: [ "z", "x" ], 2: [ "y" ] }|]
    it "int-index" $ do
      [r|count("Hello World").o|] ~=?? Ok "2"
      [r|invert(count("big blue bag"))|] ~=?? Ok [r|{ 1: [ "u", "l", "i", "e", "a" ], 2: [ "g", " " ], 3: [ "b" ] }|]
      [r|fold(add, values(count("Hello, World!")))|] ~=?? Ok "13"
    it "inhereted" $ do
      [r|{ "a": count }.a.helllo.l|] ~=?? Ok "3"
      [r|{ "a": {"b": echo} }.a.b.hello!|] ~=?? Ok "null"
      [r|{ "a": {"b": echo} }.a.b.hello!.h|] ~=?? EvalError HiErrorInvalidFunction
    it "OH SHEAT" $ do
      [r|count.hello-world(invert(count.hello-world)(3)(0))|] ~=?? Ok "3"
      [r|{      "add"     : add   }.add(1, 10)|] ~=?? Ok "11"
      [r|{"kek" : kek}..kek!|] ~=?? ParseError ""
      [r|{"add" : add}.add("kek", "lol")(1, null)|] ~=?? Ok [r|"eklol"|]
