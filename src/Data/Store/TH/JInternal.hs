{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MagicHash #-}
{-# LANGUAGE ParallelListComp #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Store.TH.JInternal
    (makeJStore,makeDataType, makeDataTypeDeriving, makeJStoreIdentity
    ) where

import           Control.Applicative
import           Data.Complex ()
import           Data.Generics.Aliases (extT, mkQ, extQ)
import           Data.Generics.Schemes (listify, everywhere, something)
import           Data.List (find)
import qualified Data.Map as M
import           Data.Maybe (fromMaybe, isJust, mapMaybe)
import           Data.Primitive.ByteArray
import           Data.Primitive.Types
import           Data.Store.Core
import           Data.Store.Impl
import qualified Data.Text as T
import           Data.Traversable (forM)
import qualified Data.Vector.Primitive as PV
import qualified Data.Vector.Unboxed as UV
import           Data.Word
import           Foreign.Storable (Storable)
import           GHC.Types (Int(..))
import           Language.Haskell.TH
import           Language.Haskell.TH.ReifyMany.Internal (TypeclassInstance(..), getInstances, unAppsT)
import           Language.Haskell.TH.Syntax (lift, Name, OccName)
import           Prelude
import           Safe (headMay)
import           TH.Derive (Deriver(..))
import           TH.ReifySimple
import           TH.Utilities (expectTyCon1, dequalify, plainInstanceD, appsT)
import           Control.Exception (Exception(..), throwIO, try)
import           Foreign.Ptr
import           Control.Monad (when)
import           Control.Exception (Exception(..), throwIO, try)
import           Foreign.Ptr
import           Data.Store.Internal
import           Data.List

-- instance Deriver (Store a) where
--     runDeriver _ preds ty = do
--         argTy <- expectTyCon1 ''Store ty
--         dt <- reifyDataTypeSubstituted argTy
--         (:[]) <$> deriveStore preds argTy (dtCons dt)

-- | Given the name of a type, generate a Store instance for it,
-- assuming that all type variables also need to be Store instances.
--
-- Note that when used with datatypes that require type variables, the
-- ScopedTypeVariables extension is required.
requiredSuffix :: String
requiredSuffix = "TH"

makeJStoreIdentity :: Name -> Q [Dec]
makeJStoreIdentity  = makeJStoreInternal True

makeJStore :: Name -> Q [Dec]
makeJStore = makeJStoreInternal False

makeJStoreInternal ::  Bool -> Name -> Q [Dec]
makeJStoreInternal higherKindIdentity name = do
    dt <- reifyDataType name
    newName <- getNameSuffixRemoved name requiredSuffix
    let preds = []
        argTy = if higherKindIdentity 
                    then AppT (ConT newName) (ConT $ mkName "Identity")
                    else ConT newName
    (:[]) <$> deriveStore preds argTy (dtCons dt) higherKindIdentity

getNameSuffixRemoved :: Name -> String -> Q Name
getNameSuffixRemoved name suffix
    | let dtName = nameBase name, isSuffixOf suffix dtName = fromMaybe name <$> lookupTypeName (take (length dtName - length suffix) dtName)
    | otherwise = return $ name

makeDataTypeDeriving :: Name -> [String] -> Q [Dec]
makeDataTypeDeriving name dcs = do
    info <- reify name
    case info of
       TyConI (DataD ctx dtName tyVBs mkind ((RecC recName varBangTypes):[]) _) -> do 
           return $ (DataD ctx (removeSuffix dtName requiredSuffix) tyVBs mkind ((RecC (removeSuffix recName requiredSuffix) (removeDeprecated varBangTypes)):[]) [DerivClause Nothing (map (ConT . mkName) dcs)]):[]
       _                                                -> return []
    where 
        removeDeprecated varBangTypes = [(nm,bg,ty) | (nm,bg,ty) <- varBangTypes, notDeprecated ty]

makeDataType :: Name -> Q [Dec]
makeDataType name = do
    info <- reify name
    case info of
       TyConI (DataD ctx dtName tyVBs mkind ((RecC recName varBangTypes):[]) dcs) -> do 
           return $ (DataD ctx (removeSuffix dtName requiredSuffix) tyVBs mkind ((RecC (removeSuffix recName requiredSuffix) (removeDeprecated varBangTypes)):[]) dcs):[]
       _                                                -> return []
    where 
        removeDeprecated varBangTypes = [(nm,bg,ty) | (nm,bg,ty) <- varBangTypes, notDeprecated ty]



getDeriveEqShow :: [DerivClause]
getDeriveEqShow = [DerivClause Nothing [ConT $ mkName "Generic",ConT $ mkName "B.Beamable"]] -- ConT $ mkName "Eq",ConT $ mkName "Show",ConT $ mkName "ToJSON",ConT $ mkName "FromJSON"

removeSuffix :: Name -> String -> Name
removeSuffix name1 suffix
    | let nameStr = nameBase name1, isSuffixOf suffix nameStr = mkName $ take (length nameStr - length suffix) nameStr
    | otherwise = name1

notDeprecated :: Type -> Bool
notDeprecated (AppT ty ((AppT (ConT con) _))) = (not (nameBase con == "Deprecated")) && (case ty of
                                                                                          ConT con2 ->  not (nameBase con2 == "Deprecated")
                                                                                          _         ->  True)
notDeprecated (AppT (ConT con) _) = not (nameBase con == "Deprecated")
notDeprecated _ = True

deriveStore :: Cxt -> Type -> [DataCon] -> Bool -> Q Dec
deriveStore preds headTy cons0 higherKindIdentity =
    makeStoreInstance preds headTy
        <$> sizeExpr
        <*> peekExpr
        <*> pokeExpr
  where
    cons :: [(Name, [(Name, Type, Int)])]
    cons =
      [ ( removeSuffix (dcName dc) requiredSuffix
        , [ (mkName ("c" ++ show ixc ++ "f" ++ show ixf), ty, ixf)
          | (ty,ixf) <- zipWith (\(_,ty) i -> (ty,i)) (dcFields dc) ints, notDeprecated ty
          ]
        )
      | ixc <- ints
      | dc <- cons0
      ]
    --   (ty,i) <- zipWith (\(_,ty) i -> (ty,i)) (dcFields dc) ([0..] :: [Int]), notDeprecated ty
    -- NOTE: tag code duplicated in th-storable.
    (tagType, _, tagSize) =
        fromMaybe (error "Too many constructors") $
        find (\(_, maxN, _) -> maxN >= length cons) tagTypes
    tagTypes :: [(Name, Int, Int)] -- correct this logic
    tagTypes =
        [ ('(), 1, 0)
        , (''Word8, fromIntegral (maxBound :: Word8), 1)
        , (''Word16, fromIntegral (maxBound :: Word16), 2)
        , (''Word32, fromIntegral (maxBound :: Word32), 4)
        , (''Word64, fromIntegral (maxBound :: Word64), 8)
        ]
    fName ix = mkName ("f" ++ show ix)
    ints = [0..] :: [Int]
    fNames = map fName ints
    sizeNames = zipWith (\_ -> mkName . ("sz" ++) . show) cons ints
    tagName = mkName "tag"
    valName = mkName "val"
    sizeExpr = varSizeExpr
      where
        sizeAtType :: (Name, Type, Int) -> ExpQ
        sizeAtType (_, ty, _) = 
            if higherKindIdentity 
                then case ty of 
                        AppT (AppT (ConT x) (VarT y)) ty'  -> if nameBase x == "C" then [| size :: Size $(return ty') |] else fail $ "Not in form1 of B.C f"
                        _               -> fail $ show ty
                else [| size :: Size $(return ty) |]
        matchVarSize :: MatchQ
        matchVarSize = do
            match (tupP (map (\(n, _, _) -> varP n) (concatMap snd cons)))
                  (normalB varSizeExpr)
                  []
        varSizeExpr :: ExpQ
        varSizeExpr =
            [| VarSize $ \x -> $(caseE [| x |] (map matchVar cons)) |]
        matchVar :: (Name, [(Name, Type, Int)]) -> MatchQ
        matchVar (cname, []) = 
            let consSize = getSize $ T.pack $ nameBase cname in 
            match (conP cname []) (normalB  $ [| consSize |]) []
        matchVar (cname, fields) =
            match (conP cname (zipWith (\_ fn -> varP fn) fields fNames))
                  body
                  []
          where
            body = let consSize = getSize $ T.pack $ nameBase cname in  normalB $ 
                foldl (\l r -> [| $(l) + $(r)|]) [|consSize|]
                (zipWith (\(sizeName, ty, i) fn -> if isMaybeType ty then [| getSizeOfMaybe $(varE fn) i |] else [| getSize $(varE fn) + 4 + (getSize (i :: Int)) |])
                         fields
                         fNames)
    -- Choose a tag size large enough for this constructor count.
    -- Expression used for the definition of peek.
    peekExpr = case cons of
        [] -> [| error ("Attempting to peek type with no constructors (" ++ $(lift (show headTy)) ++ ")") |]
        -- [con] -> peekCon con
        _ -> doE
            [ bindS (varP tagName) [| peek |]
            , noBindS (caseE (sigE (varE tagName) (conT ''T.Text))
                      (map peekMatch cons ++ [peekErr]))
            ]
    peekMatch con = match (litP (StringL (nameBase (fst con)))) (normalB (peekCon con)) []
    peekErr = match wildP (normalB
        [| peekException $ T.pack $ "Found invalid tag while peeking (" ++ $(lift (show headTy)) ++ ")" |]) []
    peekCon (cname, fields) =
        case fields of
            [] -> [| pure $(conE cname) |]
            _ -> [| Peek $ \end $(varP ptr) -> let endPtr = peekStateEndPtr end in $(doE $
                    -- [letS [ ValD (VarP (mkName "endPtr")) (normalB (peekStateEndPtr end))]] ++
                    map (\(fn, ty, i) -> bindS [p|PeekResult $(varP ptr) $(varP fn)|] (if isMaybeType ty then [| runPeek (peekyMaybe i endPtr peek) end $(varE ptr) |] else [| runPeek (peeky i endPtr peek) end $(varE ptr) |])) fields ++
                    [noBindS $ appE (varE 'return) $ appE (appE (conE 'PeekResult) (varE 'endPtr)) $ appsE $ conE cname : map (\(fn, _, _) -> varE fn) fields])
                    |]
    pokeExpr = lamE [varP valName] $ caseE (varE valName) $ map pokeCon cons
    pokeCon :: (Name, [(Name, Type, Int)]) -> MatchQ
    pokeCon (cname, fields) =
        match (conP cname (map (\(fn, _, _) -> varP fn) fields)) body []
      where
        body = normalB $ doE (pokeTag (nameBase cname) : map pokeField fields)
    pokeTag ix = noBindS [| poke (ix :: $(conT ''T.Text)) |]
    pokeField (fn, ty, i) =  if isMaybeType ty then  noBindS [| pokeyMaybe i $(varE fn) |] else noBindS [| pokey i $(varE fn) |]
    ptr = mkName "ptr"

isMaybeType :: Type -> Bool
isMaybeType (AppT ty ((AppT (ConT con) _))) = (nameBase con == "Maybe") || (case ty of
                                                                              ConT con2 ->  nameBase con2 == "Maybe"
                                                                              _         ->  False)
isMaybeType (AppT (ConT con) _) =  (nameBase con == "Maybe")
isMaybeType _ = False

{- What the generated code looks like

data Foo = Foo Int Double Float

instance Store Foo where
    size =
        case (size :: Size Int, size :: Size Double, size :: Size Float) of
            (ConstSize c0f0, ConstSize c0f1, ConstSize c0f2) -> ConstSize (0 + sz0)
              where
                sz0 = c0f0 + c0f1 + c0f2
            (c0f0, c0f1, c0f2)
                VarSize $ \(Foo f0 f1 f2) -> 0 +
                    getSizeWith c0f0 f0 + getSizeWith c0f1 f1 + getSizeWith c0f2 f2
    peek = do
        f0 <- peek
        f1 <- peek
        f2 <- peek
        return (Foo f0 f1 f2)
    poke (Foo f0 f1 f2) = do
        poke f0
        poke f1
        poke f2

data Bar = Bar Int | Baz Double

instance Store Bar where
    size =
        case (size :: Size Int, size :: Size Double) of
            (ConstSize c0f0, ConstSize c1f0) | sz0 == sz1 -> ConstSize (1 + sz0)
              where
                sz0 = c0f0
                sz1 = c1f0
            (c0f0, c1f0) -> VarSize $ \x -> 1 +
                case x of
                    Bar f0 -> getSizeWith c0f0 f0
                    Baz f0 -> getSizeWith c1f0 f0
    peek = do
        tag <- peek
        case (tag :: Word8) of
            0 -> do
                f0 <- peek
                return (Bar f0)
            1 -> do
                f0 <- peek
                return (Baz f0)
            _ -> peekException "Found invalid tag while peeking (Bar)"
    poke (Bar f0) = do
        poke 0
        poke f0
    poke (Bar f0) = do
        poke 1
        poke f0
-}

------------------------------------------------------------------------
-- Generic

deriveTupleStoreInstance :: Int -> Dec
deriveTupleStoreInstance n =
    deriveGenericInstance (map storePred tvs)
                          (foldl1 AppT (TupleT n : tvs))
  where
    tvs = take n (map (VarT . mkName . (:[])) ['a'..'z'])

deriveGenericInstance :: Cxt -> Type -> Dec
deriveGenericInstance cs ty = plainInstanceD cs (AppT (ConT ''Store) ty) []

deriveGenericInstanceFromName :: Name -> Q Dec
deriveGenericInstanceFromName n = do
    tvs <- map VarT . dtTvs <$> reifyDataType n
    return $ deriveGenericInstance (map storePred tvs) (appsT (ConT n) tvs)

------------------------------------------------------------------------
-- Storable

-- TODO: Generate inline pragmas? Probably not necessary

deriveManyStoreFromStorable :: (Type -> Bool) -> Q [Dec]
deriveManyStoreFromStorable p = do
    storables <- postprocess . instancesMap <$> getInstances ''Storable
    stores <- postprocess . instancesMap <$> getInstances ''Store
    return $ M.elems $ flip M.mapMaybe (storables `M.difference` stores) $
        \(TypeclassInstance cs ty _) ->
        let argTy = head (tail (unAppsT ty))
            tyNameLit = LitE (StringL (pprint ty)) in
        if p argTy && not (superclassHasStorable cs)
            then Just $ makeStoreInstance cs argTy
                (AppE (VarE 'sizeStorableTy) tyNameLit)
                (AppE (VarE 'peekStorableTy) tyNameLit)
                (VarE 'pokeStorable)
            else Nothing

-- See #143. Often Storable superclass constraints should instead be
-- Store constraints, so instead it just warns for these.
superclassHasStorable :: Cxt -> Bool
superclassHasStorable = isJust . something (mkQ Nothing justStorable `extQ` ignoreStrings)
  where
    justStorable :: Type -> Maybe ()
    justStorable (ConT n) | n == ''Storable = Just ()
    justStorable _ = Nothing
    ignoreStrings :: String -> Maybe ()
    ignoreStrings _ = Nothing

------------------------------------------------------------------------
-- Vector

deriveManyStorePrimVector :: Q [Dec]
deriveManyStorePrimVector = do
    prims <- postprocess . instancesMap <$> getInstances ''PV.Prim
    stores <- postprocess . instancesMap <$> getInstances ''Store
    let primInsts =
            M.mapKeys (map (AppT (ConT ''PV.Vector))) prims
            `M.difference`
            stores
    forM (M.toList primInsts) $ \primInst -> case primInst of
        ([_], TypeclassInstance cs ty _) -> do
            let argTy = head (tail (unAppsT ty))
            sizeExpr <- [|
                VarSize $ \x ->
                    I# $(primSizeOfExpr (ConT ''Int)) +
                    I# $(primSizeOfExpr argTy) * PV.length x
                |]
            peekExpr <- [| do
                len <- peek
                let sz = I# $(primSizeOfExpr argTy)
                array <- peekToByteArray $(lift ("Primitive Vector (" ++ pprint argTy ++ ")"))
                                         (len * sz)
                return (PV.Vector 0 len array)
                |]
            pokeExpr <- [| \(PV.Vector offset len (ByteArray array)) -> do
                let sz = I# $(primSizeOfExpr argTy)
                poke len
                pokeFromByteArray array (offset * sz) (len * sz)
                |]
            return $ makeStoreInstance cs (AppT (ConT ''PV.Vector) argTy) sizeExpr peekExpr pokeExpr
        _ -> fail "Invariant violated in derivemanyStorePrimVector"


primSizeOfExpr :: Type -> ExpQ
primSizeOfExpr ty = [| $(varE 'sizeOf#) (error "sizeOf# evaluated its argument" :: $(return ty)) |]

-- TODO: Add something for this purpose to TH.ReifyDataType

getUnboxInfo :: Q [(Cxt, Type, [DataCon])]
getUnboxInfo = do
    FamilyI _ insts <- reify ''UV.Vector
    return (map (everywhere (id `extT` dequalVarT)) $ mapMaybe go insts)
  where
#if MIN_VERSION_template_haskell(2,15,0)
    go (NewtypeInstD preds _ lhs _ con _)
      | [_, ty] <- unAppsT lhs
      = toResult preds ty [con]
    go (DataInstD preds _ lhs _ cons _)
      | [_, ty] <- unAppsT lhs
      = toResult preds ty cons
#elif MIN_VERSION_template_haskell(2,11,0)
    go (NewtypeInstD preds _ [ty] _ con _) = toResult preds ty [con]
    go (DataInstD preds _ [ty] _ cons _) = toResult preds ty cons
#else
    go (NewtypeInstD preds _ [ty] con _) = toResult preds ty [con]
    go (DataInstD preds _ [ty] cons _) = toResult preds ty cons
#endif
    go x = error ("Unexpected result from reifying Unboxed Vector instances: " ++ pprint x)
    toResult :: Cxt -> Type -> [Con] -> Maybe (Cxt, Type, [DataCon])
    toResult _ _ [NormalC conName _]
      | nameBase conName `elem` skippedUnboxConstructors = Nothing
    toResult preds ty cons
      = Just (preds, ty, concatMap conToDataCons cons)
    dequalVarT :: Type -> Type
    dequalVarT (VarT n) = VarT (dequalify n)
    dequalVarT ty = ty

-- See issue #174
skippedUnboxConstructors :: [String]
skippedUnboxConstructors = ["MV_UnboxAs", "V_UnboxAs", "MV_UnboxViaPrim", "V_UnboxViaPrim"]

------------------------------------------------------------------------
-- Utilities

-- Filters out overlapping instances and instances with more than one
-- type arg (should be impossible).
postprocess :: M.Map [Type] [a] -> M.Map [Type] a
postprocess =
    M.mapMaybeWithKey $ \tys xs ->
        case (tys, xs) of
            ([_ty], [x]) -> Just x
            _ -> Nothing

makeStoreInstance :: Cxt -> Type -> Exp -> Exp -> Exp -> Dec
makeStoreInstance cs ty sizeExpr peekExpr pokeExpr =
    plainInstanceD
        cs
        (AppT (ConT ''Store) ty)
        [ ValD (VarP 'size) (NormalB sizeExpr) []
        , ValD (VarP 'peek) (NormalB peekExpr) []
        , ValD (VarP 'poke) (NormalB pokeExpr) []
        ]

-- TODO: either generate random types that satisfy instances with
-- variables in them, or have a check that there's at least a manual
-- check for polymorphic instances.

getAllInstanceTypes :: Name -> Q [[Type]]
getAllInstanceTypes n =
    map (\(TypeclassInstance _ ty _) -> drop 1 (unAppsT ty)) <$>
    getInstances n

getAllInstanceTypes1 :: Name -> Q [Type]
getAllInstanceTypes1 n =
    fmap (fmap (fromMaybe (error "getAllMonoInstances1 expected only one type argument") . headMay))
         (getAllInstanceTypes n)

isMonoType :: Type -> Bool
isMonoType = null . listify isVarT

isVarT :: Type -> Bool
isVarT VarT{} = True
isVarT _ = False

-- TOOD: move these to th-reify-many

-- | Get a map from the 'getTyHead' type of instances to
-- 'TypeclassInstance'.
instancesMap :: [TypeclassInstance] -> M.Map [Type] [TypeclassInstance]
instancesMap =
    M.fromListWith (++) .
    map (\ti -> (map getTyHead (instanceArgTypes ti), [ti]))

instanceArgTypes :: TypeclassInstance -> [Type]
instanceArgTypes (TypeclassInstance _ ty _) = drop 1 (unAppsT ty)

getTyHead :: Type -> Type
getTyHead (SigT x _) = getTyHead x
getTyHead (ForallT _ _ x) = getTyHead x
getTyHead (AppT l _) = getTyHead l
getTyHead x = x

storePred :: Type -> Pred
storePred ty =
#if MIN_VERSION_template_haskell(2,10,0)
        AppT (ConT ''Store) ty
#else
        ClassP ''Store [ty]
#endif

{-# INLINE peeky #-}
peeky :: Word32 -> Ptr Word8 -> Peek a -> Peek a
peeky tagNum endPtr m = do
    -- (currentTagNum :: Word32) <- peek
    -- (size :: Int) <- peek
    Peek $ \end ptr -> do
        -- print $ show ptr <> " " <> show endPtr <> " " <> show tagNum 
        when (ptr >= endPtr) $ 
            throwIO $ PeekException 0 "error"
        PeekResult ptr1 (currentTagNum :: Word32) <- runPeek (peek) end ptr
        PeekResult ptr2 (size :: Int) <- runPeek (peek) end ptr1
        let endPtr' = ptr2 `plusPtr` size
        if tagNum == currentTagNum
            then do
                result <- decodeIOWithFromPtr (isolate size m) ptr2 size
                return $ PeekResult endPtr' result
            else if tagNum > currentTagNum
                then do
                    PeekResult ptr' _ <- runPeek (skip size) end ptr2 
                    runPeek (peeky tagNum endPtr m) end ptr'
                else throwIO $ PeekException 0 "error"

{-# INLINE peekyMaybe #-}
peekyMaybe :: Word32 -> Ptr Word8 -> Peek a -> Peek (Maybe a)
peekyMaybe tagNum endPtr m = do
    -- (currentTagNum :: Word32) <- peek
    -- (size :: Int) <- peek
    Peek $ \end ptr -> do
        -- print $ show ptr <> " " <> show endPtr <> " " <> show tagNum 
        if (ptr >= endPtr) 
            then return $ PeekResult ptr Nothing
            else do
                PeekResult ptr1 (currentTagNum :: Word32) <- runPeek (peek) end ptr
                PeekResult ptr2 (size :: Int) <- runPeek (peek) end ptr1
                let endPtr' = ptr2 `plusPtr` size
                if (tagNum == currentTagNum)
                    then do
                        result <- decodeIOWithFromPtr (isolate size m) ptr2 size
                        return $ PeekResult endPtr' (Just result)
                    else if tagNum > currentTagNum
                        then do
                            PeekResult ptr' _ <- runPeek (skip size) end ptr2
                            runPeek (peekyMaybe tagNum endPtr m) end ptr'
                        else return $ PeekResult ptr Nothing

-- optimise fromIntegral conversions
{-# INLINE pokeyMaybe #-}
pokeyMaybe :: Store a => Word32 -> Maybe a -> Poke ()
pokeyMaybe tagNum (Just val) = poke tagNum >> poke (getSize val) >> poke val
pokeyMaybe tagNum Nothing    = Poke $ \_ptr offset -> pure (offset, ())

-- optimise fromIntegral conversions
{-# INLINE pokey #-}
pokey :: Store a => Word32 -> a -> Poke ()
pokey tagNum val = poke tagNum >> poke (getSize val) >> poke val

{-# INLINE getSizeOfMaybe #-}
getSizeOfMaybe :: Store a => (Maybe a) -> Int -> Int
getSizeOfMaybe (Just val) tagNum = getSize val + 4 + getSize tagNum
getSizeOfMaybe Nothing _         = 0

--  Peek $ \end ptr -> do
--     runPeek (do
--         a <- peeky 1 end peek
--         b <- peeky 2 end peek
--         c <- peeky 3 end peek
--         d <- peeky 4 end peek
--         e <- peeky 5 end peek
--         f <- peeky 6 end peek

--     ) end ptr

