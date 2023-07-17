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
    (makeJStore, makeJStoreIdentity
    ) where

import           Control.Applicative
import           Data.Complex ()
import           Data.Generics.Aliases (extT, mkQ, extQ)
import           Data.Generics.Schemes (listify, everywhere, something)
import           Data.List (find)
import qualified Data.Map as M
import           Data.Maybe (fromMaybe, isJust, mapMaybe, fromJust)
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
import qualified Data.ByteString.Char8 as BSC
import qualified Data.ByteString as BS
import qualified Data.ByteString.Internal as BS
import qualified Data.Digest.XXHash as XXHash

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

makeJStoreIdentity :: Name -> Q [Dec]
makeJStoreIdentity  = makeJStoreInternal $ Just $ mkName "Identity"

makeJStore :: Name -> Q [Dec]
makeJStore = makeJStoreInternal Nothing

makeJStoreInternal ::  Maybe Name -> Name -> Q [Dec]
makeJStoreInternal higherKind name = do
    dt <- reifyDataType name
    let preds = []
        argTy = case higherKind of
                    Just v -> AppT (ConT name) (ConT v)
                    Nothing -> ConT name
    (:[]) <$> deriveStore preds argTy (dtCons dt)

calculateFieldNameHash :: Maybe Name -> Word32
calculateFieldNameHash name = calculateHash $ nameBase $ fromJust name

calculateHash :: String -> Word32
calculateHash = XXHash.xxHash' . BSC.pack

getCollisions :: [(Name, [(Name, Type)],[(Name, Type, Word32)])] -> [(String, [[String]])]
getCollisions cons = foldl' (\ans (cname,_,fields) -> 
                                case collidingFields fields of 
                                    [] -> ans
                                    el -> (nameBase cname,el):ans) [] cons
    where
        collidingFields :: [(Name, Type, Word32)] -> [[String]]
        collidingFields [] = []
        collidingFields ((f0,_,hash0):xs) = filter (\arr -> length arr > 1) $ fst $
                                            foldl' (\(prevArr:ans,prevHash) (fn,_,hashn) -> if hashn == prevHash then ((nameBase fn:prevArr):ans,hashn) else ([nameBase fn]:prevArr:ans,hashn)
                                                 ) ([[nameBase f0]],hash0) xs

deriveStore :: Cxt -> Type -> [DataCon] -> Q Dec
deriveStore preds headTy cons0 =
    case getCollisions cons of 
        []  ->  makeStoreInstance preds headTy
                    <$> sizeExpr
                    <*> peekExpr
                    <*> pokeExpr
        arr ->  fail $ "Collision detected for the following fields " ++ show arr
  where
    cons :: [(Name, [(Name, Type)],[(Name, Type, Word32)])] -- [(constructorName,[array of fieldNames and types],[array of fieldNames sorted on their hash])]
    cons =
      [ (dcName dc
        , [ (mkName $ nameBase $ fromJust fn, ty)
          | (fn,ty) <- dcFields dc
          ]
          -- sorted order fields based on hash
        , [ (mkName $ nameBase $ fromJust fn, ty, hash)
          | (fn,ty,hash) <- sortOn (\(_,_,hash)->hash) $ map (\(fn,ty) -> (fn, ty, calculateFieldNameHash fn)) (dcFields dc)
          ]
        )
      | dc <- cons0
      ]
    tagName = mkName "tag"
    valName = mkName "val"
    sizeExpr = varSizeExpr
      where
        varSizeExpr :: ExpQ
        varSizeExpr =
            [| VarSize $ \x -> $(caseE [| x |] (map matchVar cons)) |]
        matchVar :: (Name, [(Name, Type)],[(Name, Type, Word32)]) -> MatchQ
        matchVar (cname, [],_) = 
            let consSize = getSize $ T.pack $ nameBase cname in 
            match (conP cname []) (normalB  $ [| consSize |]) []
        matchVar (cname, fields, sortedFields) =
            match (conP cname (map (\(fn,_) -> varP fn) fields))
                  body
                  []
          where
            body = let consSize = getSize $ T.pack $ nameBase cname in  normalB $ 
                foldl (\l r -> [| $(l) + $(r)|]) [|consSize|]
                (map (\(fn, ty,i) -> if isMaybeType ty then [| getSizeOfMaybe $(varE fn) |] else [| getSize $(varE fn) + 8 |])
                         sortedFields)
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
    peekMatch con@(cname,_,_) = match (litP (StringL (nameBase cname))) (normalB (peekCon con)) []
    peekErr = match wildP (normalB
        [| peekException $ T.pack $ "Found invalid tag while peeking (" ++ $(lift (show headTy)) ++ ")" |]) []
    peekCon (cname, fields, sortedFields) =
        case fields of
            [] -> [| pure $(conE cname) |]
            _ -> [| Peek $ \end $(varP ptr) -> let endPtr = peekStateEndPtr end in $(doE $
                    -- [letS [ ValD (VarP (mkName "endPtr")) (normalB (peekStateEndPtr end))]] ++
                    map (\(fn, ty, i) -> bindS [p|PeekResult $(varP ptr) $(varP fn)|] (if isMaybeType ty then [| runPeek (peekyMaybe i endPtr peek) end $(varE ptr) |] else [| runPeek (peeky i endPtr peek) end $(varE ptr) |])) sortedFields ++
                    [noBindS $ appE (varE 'return) $ appE (appE (conE 'PeekResult) (varE 'endPtr)) $ appsE $ conE cname : map (\(fn, _) -> varE fn) fields])
                    |]
    pokeExpr = lamE [varP valName] $ caseE (varE valName) $ map pokeCon cons
    pokeCon :: (Name, [(Name, Type)],[(Name, Type, Word32)]) -> MatchQ
    pokeCon (cname, fields, sortedFields) =
        match (conP cname (map (\(fn, _) -> varP fn) fields)) body []
      where
        body = normalB $ doE (pokeTag (nameBase cname) : map pokeField sortedFields)
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
        PeekResult ptr2 (size' :: Word32) <- runPeek (peek) end ptr1
        let size = fromIntegral size'
            endPtr' = ptr2 `plusPtr` size
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
                PeekResult ptr2 (size' :: Word32) <- runPeek (peek) end ptr1
                let size = fromIntegral size'
                    endPtr' = ptr2 `plusPtr` size
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
pokeyMaybe tagNum (Just val) = poke tagNum >> poke ((fromIntegral (getSize val)) :: Word32) >> poke val
pokeyMaybe tagNum Nothing    = Poke $ \_ptr offset -> pure (offset, ())

-- optimise fromIntegral conversions
{-# INLINE pokey #-}
pokey :: Store a => Word32 -> a -> Poke ()
pokey tagNum val = poke tagNum >> poke ((fromIntegral (getSize val)) :: Word32) >> poke val

{-# INLINE getSizeOfMaybe #-}
getSizeOfMaybe :: Store a => (Maybe a) -> Int
getSizeOfMaybe (Just val) = getSize val + 8
getSizeOfMaybe Nothing    = 0

-- this copies data of bytestring into buffer
{-# INLINE pokePlainByteString #-}
pokePlainByteString :: BS.ByteString -> Poke ()
pokePlainByteString x = do
    let (sourceFp, sourceOffset, sourceLength) = BS.toForeignPtr x
    -- poke sourceLength -- this where this differs from poke impl of BS.Bystring
    pokeFromForeignPtr sourceFp sourceOffset sourceLength