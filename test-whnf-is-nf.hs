{-# LANGUAGE TemplateHaskell, CPP #-}

module Main where

import Data.Int
import Data.Word
import System.Exit   (exitFailure)
import Test.WhnfIsNf

assertTypeWhnfIsNf :: String -> Maybe Bool -> IO ()
assertTypeWhnfIsNf msg (Just True) = do
    putStrLn $ "assertTypeWhnfIsNf     " ++ msg ++ "...PASS!"
assertTypeWhnfIsNf msg res = do
    putStrLn $ "assertTypeWhnfIsNf     " ++ msg ++ "...FAIL! (w/ " ++ show res ++ ")"
    exitFailure

assertTypeWhnfIsNotNf :: String -> Maybe Bool -> IO ()
assertTypeWhnfIsNotNf msg (Just True) = do
    putStrLn $ "assertTypeWhnfIsNotNf  " ++ msg ++ "...FAIL!"
    exitFailure
assertTypeWhnfIsNotNf msg res = do
    putStrLn $ "assertTypeWhnfIsNotNf  " ++ msg ++ "...PASS! (w/ " ++ show res ++ ")"

#define posAss(S,T) assertTypeWhnfIsNf S $(typeWhnfIsNfExp =<< [t| T |])
#define negAss(S,T) assertTypeWhnfIsNotNf S $(typeWhnfIsNfExp =<< [t| T |])


data Foo a = Foo1
           | Foo2 !Int !String
           | Foo3 (Foo a)
           | Foo4 { fX :: Int, fY :: Char }
           | Foo5 !Bar
           | Foo6 !(String->Int)
           | Foo a :--: !Bool

data Bar = Bar0 | Bar1 !Char | Bar2 !Int !Int | Bar3 !Bar | !Bar :---: !Bar

data Doo = Doo0 | Doo1 Bar

data Zoo = Zoo0 | Zoo1 !Bar

data Goo = Goo0 | Goo1 !Doo

main :: IO ()
main = do
    posAss("()",     ())
    posAss("Bool",   Bool)
    posAss("Char",   Char)
    posAss("Int",    Int)
    posAss("Int8",   Int8)
    posAss("Int16",  Int16)
    posAss("Int32",  Int32)
    posAss("Int64",  Int64)
    posAss("Word",   Word)
    posAss("Word8",  Word8)
    posAss("Word16", Word16)
    posAss("Word32", Word32)
    posAss("Word64", Word64)

    posAss("Int->Int",            Int->Int)
    posAss("String->(Char,Int)",  String->(Char,Int))

    negAss("Doo",       Doo)
    posAss("Zoo",       Zoo)
    negAss("Goo",       Goo)
    posAss("Bar",       Bar)
    negAss("Foo",       Foo)
    negAss("Foo Int",   Foo Int)

    negAss("String",         String)
    negAss("[Char]",         [Char])
    negAss("[Int]",          [Int])
    negAss("[()]",           [()])
    negAss("Maybe Bool",     Maybe Bool)
