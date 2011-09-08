{-# LANGUAGE TemplateHaskell #-}

module Test.WhnfIsNf where

import Control.DeepSeq.TH
import Language.Haskell.TH

typeWhnfIsNfExp :: Type -> Q Exp
typeWhnfIsNfExp t = do
    r <- typeWhnfIsNf t
    case r of
        Nothing    -> [e|Nothing|]
        Just True  -> [e|Just True|]
        Just False -> [e|Just False|]
