{-# LANGUAGE BlockArguments #-}

module Main where

import Control.Monad.Cont (liftIO)
import Control.Monad.Trans.Class (lift)
import GHC.Exts (fromList)
import HW3.Action
import HW3.Evaluator (eval)
import HW3.Parser (parse)
import HW3.Pretty (prettyValue, showError)
import Prettyprinter.Internal (line, pretty)
import Prettyprinter.Render.Terminal (putDoc)
import System.Console.Haskeline (InputT, defaultSettings, getInputLine, runInputT)
import Text.Megaparsec.Error (errorBundlePretty)

main :: IO ()
main = runInputT defaultSettings loop
  where
    loop :: InputT IO ()
    loop = do
      minput <- getInputLine "hi> "
      case minput of
        Nothing -> return ()
        Just input -> do
          case parse input of
            Left err -> lift $ putDoc $ pretty $ errorBundlePretty err
            Right expr -> do
              res <- liftIO $ runHIO (eval expr) (fromList [AllowTime, AllowWrite, AllowRead])
              lift $ putDoc case res of
                Left err    -> showError err <> line
                Right expr' -> prettyValue expr' <> line
          loop
