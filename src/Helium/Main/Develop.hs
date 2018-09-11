{- USE withArgs ["../Develop/Hello.hs", "-b"] main -}
module Helium.Main.Develop where
import System.Directory
import System.Process
import System.FilePath
import System.Environment

import Control.Monad

import Main
import Helium.Main.Compile
import Helium.Main.Args

compileFile :: String -> IO ()
compileFile s = do
    pwc <- getCurrentDirectory
    putStrLn pwc
    let developLocation = "../Develop"
    let file = developLocation ++ "/" ++ s
    let lvmFile = fst (splitExtension file) ++ ".lvm"
    let preludePath = "../lib"
    compile developLocation file [Overloading, Verbose] [preludePath, developLocation] []
    (x, res, err) <- readProcessWithExitCode "lvmrun" ["-P../lib:"++developLocation, lvmFile] ""
    putStrLn("Exit code: " ++ show x)
    putStrLn "Program result:"
    putStrLn res
    unless (null err) $ do
        putStrLn "Program error"
        putStrLn err
