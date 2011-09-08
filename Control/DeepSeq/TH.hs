{-# LANGUAGE TemplateHaskell #-}

-- |Module providing Template Haskell based 'NFData' instance
-- generators and WHNF=NF type inspectors.
--
-- To use this module enable the @TemplateHaskell@ extension and
-- import "Control.DeepSeq.TH":
--
-- > {-# LANGUAGE TemplateHaskell #-}
-- > import Control.DeepSeq.TH
--
module Control.DeepSeq.TH
    ( deriveNFData
    , deriveNFDatas
    , typeWhnfIsNf
    , decWhnfIsNf
    ) where

import Control.DeepSeq     (NFData(rnf),deepseq)
import Control.Monad       (mzero,liftM,mplus)
import Data.List
import Data.Maybe          (fromMaybe, isJust, catMaybes)
import Language.Haskell.TH

-- |Try to infer whether 'Type' has the property that WHNF=NF for its
-- values.
--
-- A result of @Nothing@ means it is not known whether the
-- property holds for the given type. @Just True@ means that the
-- property holds.
--
-- This function has currently a rather limited knowledge and returns
-- @Nothing@ most of the time except for some primitive types and
-- other simple cases.
--
-- See also 'decWhnfIsNf'
typeWhnfIsNf :: Type -> Q (Maybe Bool)
typeWhnfIsNf = typeWhnfIsNf2 []

typeWhnfIsNf2 :: [Name] -> Type -> Q (Maybe Bool)
typeWhnfIsNf2 seen (ConT x)
    | x `elem` [''Int, ''Double, ''Float, ''Char, ''Bool, ''()] = return $ Just True
    | x `elem` seen = return $ Just True  -- FIXME: check whether this correct
                      -- e.g. it might break with parametrized types (which we don't handle yet anyway)
    | otherwise = do
        t <- reify x
        case t of
            TyConI dec -> decWhnfIsNf2 (x:seen) dec
            _          -> return Nothing

typeWhnfIsNf2 _ (AppT (AppT ArrowT _) _) = return $ Just True -- a -> b
typeWhnfIsNf2 _ (AppT ListT _)           = return $ Just False -- [a]
typeWhnfIsNf2 _ (AppT (TupleT _) _)      = return $ Just False -- (a,b,...)
typeWhnfIsNf2 _ _                        = return  Nothing

-- |Try to infer whether a 'Dec' which defines a type which has the
-- property that WHNF=NF for its values. This property is derived
-- statically via the following simple rules:
--
--  * @newtype@s are WHNF=NF if the wrapped type is WHNF=NF
--
--  * @type@s are WHNF=NF if the aliased type is WHNF=NF
--
--  * Types defined by @data@ are WHNF=NF if all constructors contain
--    only strict fields with WHNF=NF types
--
-- Known limitations:
--
--  * Doesn't work properly with parametrized declarations (in which
--    case @Nothing@ is returned) or existential types
--
-- See also 'typeWhnfIsNf'
decWhnfIsNf :: Dec -> Q (Maybe Bool)
decWhnfIsNf = decWhnfIsNf2 []

decWhnfIsNf2 :: [Name] -> Dec -> Q (Maybe Bool)
decWhnfIsNf2 seen (NewtypeD _ _ _ (NormalC _ [(NotStrict, t)]) _) = typeWhnfIsNf2 seen t
decWhnfIsNf2 seen (NewtypeD _ _ _ (RecC  _ [(_,NotStrict, t)]) _) = typeWhnfIsNf2 seen t
decWhnfIsNf2 seen (TySynD _ _ t)                                  = typeWhnfIsNf2 seen t
decWhnfIsNf2 _    (DataD _ _ _ [] _)                              = return Nothing
decWhnfIsNf2 seen (DataD _ _ _ cons _)                            = reduce `liftM` mapM conWhnfIsNf cons
  where
    conWhnfIsNf :: Con -> Q (Maybe Bool)
    conWhnfIsNf con
        | allStrict  = do
            ms <- mapM (typeWhnfIsNf2 seen) fTypes
            return $ reduce ms
        | otherwise  = return $ Just False
      where
        allStrict = all (== IsStrict) fStricts
        (fStricts, fTypes) = unzip $ con2types con

    con2types (NormalC _ ts)   = ts
    con2types (RecC _ vts)     = [ (tst,tt) | (_,tst,tt) <- vts ]
    con2types (InfixC tl _ tr) = [tl,tr]
    con2types (ForallC {})     = [] -- FIXME

    reduce :: [Maybe Bool] -> Maybe Bool
    reduce ms | all (==Just True)  ms  = Just True
              | any (==Just False) ms  = Just False
              | otherwise              = Nothing

decWhnfIsNf2 _    _                                               = return Nothing

-- | Derive 'NFData' instance for simple @Data@-declarations
--
-- Example usage for deriving 'NFData' instance for the type @TypeName@:
--
-- > $(deriveNFData ''TypeName)
--
-- The derivation tries to avoid evaluation of strict fields whose
-- types have the WHNF=NF property (see also 'typeWhnfIsNf' and
-- 'decWhnfIsNf'). For instance, consider the following types @Foo@
-- and @Bar@:
--
-- > data Foo a = Foo1
-- >            | Foo2 !Int !String
-- >            | Foo3 (Foo a)
-- >            | Foo4 { fX :: Int, fY :: Char }
-- >            | Foo5 !Bar
-- >            | Foo6 !(String -> Int)
-- >            | Foo a :--: !Bool
-- >
-- > data Bar = Bar0 | Bar1 !Char | Bar2 !Int !Int | Bar3 !Bar
--
-- By invoking @$(deriveNFData ''Foo)@ the generated 'NFData' instance
-- will be equivalent to:
--
-- > instance NFData a => NFData (Foo a) where
-- >     rnf Foo1       = ()
-- >     rnf (Foo2 _ x) = x `deepseq` ()
-- >     rnf (Foo3 x)   = x `deepseq` ()
-- >     rnf (Foo4 x y) = x `deepseq` y `deepseq` ()
-- >     rnf (Foo5 _)   = ()
-- >     rnf (Foo6 _)   = ()
-- >     rnf (x :--: _) = x `deepseq` ()
--
-- Whereas @$(deriveNFData ''Bar)@ generates the following default
-- 'NFData' instance since @Bar@ is inferred as a WHNF=NF type:
--
-- > instance NFData Bar
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
        TyConI idec@(DataD _ctx _tn tvs ctors _) -> do
            clauses_names <- mapM con2rnf ctors
            let clauses = map fst clauses_names
                names   = nub $ concat $ map snd clauses_names
                ctxt    = [ClassP ''NFData [VarT n] | n <- names ]
            let ity = foldl (\t tvn -> AppT t (VarT tvn)) (ConT tn) $ map tyvarname tvs

            isWhnfEqNf <- decWhnfIsNf idec

            return $ case isWhnfEqNf of -- short-cut if data-type is strict as a whole
                Just True -> [ InstanceD ctxt (AppT (ConT ''NFData) ity) [] ] -- default NFData instance
                _         -> [ InstanceD ctxt (AppT (ConT ''NFData) ity) [FunD 'rnf clauses] ]

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
        ts' <- mapM hlp ts
        let vns = concatMap getFreeTyVars $ catMaybes ts'
        vars <- tys2vars ts'
        return (Clause [ConP n vars] (NormalB $ mkDeepSeqExpr [ n' | VarP n' <- vars ]) [], vns)
      where
        hlp (NotStrict, fieldType) = return $ Just fieldType
        hlp (IsStrict, fieldType) = do
            tmp <- typeWhnfIsNf fieldType
            return $ if fromMaybe False tmp then Nothing else Just fieldType

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
