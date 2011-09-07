{-# LANGUAGE TemplateHaskell #-}

module Control.DeepSeq.TH
    ( deriveNFData
    , deriveNFDatas
    , whnfIsNf
    ) where

import Control.DeepSeq     (NFData(rnf),deepseq)
import Control.Monad       (mzero,liftM,mplus)
import Data.List
import Data.Maybe          (fromMaybe, isJust, catMaybes)
import Language.Haskell.TH

-- |Try to infer whether type has the property that WHNF=NF for its
-- values.
--
-- A result of @Nothing@ means it is not known whether the
-- property holds for the given type. @Just True@ means that the
-- property holds.
--
-- This function has currently a very limited knowledge and returns
-- @Nothing@ most of the time except for some primitive types.
whnfIsNf :: Type -> Maybe Bool
whnfIsNf (ConT x)
    | x `elem` [''Int, ''Double, ''Float, ''Char, ''Bool, ''()] = Just True
whnfIsNf (AppT ListT _) = Just False -- [a]
whnfIsNf (AppT (TupleT _) _) = Just False -- [a]
whnfIsNf _ = Nothing

-- Wrapper for 'whnfIsNf' defaulting to 'False'
whnfIsNf' :: Type -> Bool
whnfIsNf' = fromMaybe False . whnfIsNf

-- | Derive 'NFData' instance for simple @Data@-declarations
--
-- Example usage for deriving 'NFData' instance for the type @TypeName@:
--
-- > $(deriveNFData ''TypeName)
--
-- The derivation tries to avoid evaluation of strict fields whose
-- types have the WHNF=NF property (see also 'whnfIsNf'). For
-- instance, consider the following type @Foo@:
--
-- > data Foo a = Foo1
-- >            | Foo2 !Int !String
-- >            | Foo3 (Foo a)
-- >            | Foo4 { fX :: Int, fY :: Char }
-- >            | Foo a :--: !Bool
--
-- By invoking @$(deriveNFData ''Foo)@ the generated 'NFData' instance
-- will be equivalent to:
--
-- > instance NFData a => NFData (Foo a) where
-- >     rnf Foo1       = ()
-- >     rnf (Foo2 _ x) = x `deepseq` ()
-- >     rnf (Foo3 x)   = x `deepseq` ()
-- >     rnf (Foo4 x y) = x `deepseq` y `deepseq` ()
-- >     rnf (x :--: _) = x `deepseq` ()
--
-- Known issues/limitations:
--
--  * @TypeName@ must be a proper @data@ typename (use the
--    @GeneralizedNewtypeDeriving@ extension for @newtype@ names)
--
--  * Does not support existential types yet (i.e. use of the @forall@
--    keyword)
--
--  * Does not always detect phantom type variables (e.g. for @data
--    Foo a = Foo0 | Foo1 (Foo a)@) which causes those to require
--    'NFData' instances.
--
deriveNFData :: Name -> Q [Dec]
deriveNFData tn = do
    dec <- reify tn

    case dec of
        TyConI (DataD _ctx _tn tvs ctors _) -> do
            clauses_names <- mapM con2rnf ctors
            let clauses = map fst clauses_names
                names   = nub $ concat $ map snd clauses_names
                ctxt    = [ClassP ''NFData [VarT n] | n <- names ]
            let ity = foldl (\t tvn -> AppT t (VarT tvn)) (ConT tn) $ map tyvarname tvs

            return [ InstanceD ctxt (AppT (ConT ''NFData) ity) [FunD 'rnf clauses] ]

        TyConI (NewtypeD {}) -> do
            fail $ "deriveNFData ''" ++ show tn ++ ": please use GeneralizedNewtypeDeriving " ++
                   "for deriving NFData instances for newtype"

        TyConI (TySynD {}) -> do
            fail $ "deriveNFData ''" ++ show tn ++ ": cannot derive for type-alias"

        TyConI _ -> do
            fail $ "deriveNFData ''" ++ show tn ++ ": argument must be a proper 'data'-type"

        _ -> do
            fail $ "deriveNFData ''" ++ show tn ++ ": argument must be a type-level entity"

  where
    tyvarname (PlainTV n)    = n
    tyvarname (KindedTV n _) = n

    tys2vars = mapM (\t -> if isJust t then liftM VarP (newName "x") else return WildP)

    con2rnf :: Con -> Q (Clause, [Name])
    con2rnf (NormalC n ts)   = genCon2Rnf n ts
    con2rnf (RecC n vts)     = genCon2Rnf n [ (tst,tt) | (_,tst,tt) <- vts ]
    con2rnf (InfixC tl n tr) = genCon2Rnf n [tl,tr]
    con2rnf (ForallC {})     = fail "deriveNFData: 'forall' not supported in constructor declaration"

    -- generic per-constructor function generator
    genCon2Rnf :: Name -> [(Strict,Type)] -> Q (Clause, [Name])
    genCon2Rnf n ts = do
      let vns = concatMap getFreeTyVars $ catMaybes ts'
          ts' = [ if tst == NotStrict || not (whnfIsNf' tt) then Just tt else Nothing | (tst,tt) <- ts ]
      vars <- tys2vars ts'
      return (Clause [ConP n vars] (NormalB $ mkDeepSeqExpr [ n' | VarP n' <- vars ]) [], vns)


-- |Plural version of 'deriveNFData'
--
-- Convenience wrapper for 'deriveNFData' which allows to derive
-- multiple 'NFData' instances for a list of @TypeName@s, e.g.:
--
-- > $(deriveNFData [''TypeName1, ''TypeName2, ''TypeName3])
--
deriveNFDatas :: [Name] -> Q [Dec]
deriveNFDatas = liftM concat . mapM deriveNFData

-- FIXME: there should be a ready-to-use TH function which does this already
getFreeTyVars :: Type -> [Name]
getFreeTyVars (AppT t1 t2)      = getFreeTyVars t1 `mplus` getFreeTyVars t2
getFreeTyVars (ArrowT)          = mzero
getFreeTyVars (ConT _)          = mzero
getFreeTyVars (ForallT {})      = error "getFreeTyVars: ForallT not supported yet"
getFreeTyVars (ListT)           = mzero
getFreeTyVars (SigT t1 _)       = getFreeTyVars t1
getFreeTyVars (TupleT _)        = mzero
getFreeTyVars (UnboxedTupleT _) = mzero
getFreeTyVars (VarT n)          = return n

-- helper
mkDeepSeqExpr :: [Name] -> Exp
mkDeepSeqExpr = foldr deepSeqE (ConE '())
  where
    deepSeqE :: Name -> Exp -> Exp
    deepSeqE lhs rhs = AppE (AppE (VarE 'deepseq) (VarE lhs)) rhs
