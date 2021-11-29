{-# LANGUAGE QuasiQuotes #-}
{-# language TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

module Data.Diff.TH
  ( -- * Diff Generation
    mkDiff
  , mkDiffMany
    -- * Diff Customization
  , MkDiffOptions
  , defaultDiffOptions
    -- * Re-exports
  , module Data.Diff
  ) where

import Control.Monad
import Data.Diff
import Data.List (foldl')
import Data.Traversable
import Language.Haskell.TH

-- | This function generates @Diff@ types for the type name you provide.
-- See the module "Data.Diff" for more information on the specifics.
--
-- A @Diff@ on a primitive type is a 'ValueDiff' - it is simply a new
-- value, as it doesn't make sense to say anything other than "the value
-- was changed." Primitive types are things like 'Int' and 'Char'.
--
-- A @Diff@ on a product type is a custom type, where each field in the
-- original type has a corresponding field in the Diff type that carries
-- a Diff of the field's type.
--
-- A @Diff@ on a sum type is a custom type. For each constructor in the sum
-- type, we have a way of saying:
--
-- * The constructor is the same, and carries a diff of the fields of the
--   sum.
-- * The constructor is changed, and here are the fresh values for the
--   fields of the sum.
--
-- A @Diff@ on a collection is a little different - while we could
-- represent lists using the "sum type" logic, that would be terribly
-- annoying. Instead, we create an "edit list", describing how to transform
-- one collection into another.
mkDiff :: Name -> MkDiffOptions -> DecsQ
mkDiff nm opts = do
  info <- reify nm

  -- we only care about types, if you try to make a diff on a function or
  -- value that's silly
  nmDec <-
    case info of
      TyConI dec ->
        pure dec
      _ -> do
        fail "You can only use mkDiff on a type."

  -- likewise, we only care about datatypes. diffing a class doesn't make
  -- sense
  case nmDec of
    DataD _cxt name tyvars _mkind constrs _derives ->
      case constrs of
        [] ->
          fail
            "yo excuse me sir/maan/esteemed colleague, you can't diff a void boy"
        [constr] ->
          mkProductDiff name tyvars constr
        _ | simple constrs ->
              deriveDiff name
          | otherwise ->
              mkSumDiff name tyvars constrs
    NewtypeD _cxt name tyvars _mkind constr _derives ->
      mkProductDiff name tyvars constr
    TySynD _name _tyvars typ ->  do
      underlying <- getUnderlyingTypeName typ
      mkDiff underlying opts
    _ ->
      fail "You can only use mkDiff on a datatype."

-- | Use this to make a 'Diffable' instance for many types.
mkDiffMany :: MkDiffOptions -> [Name] -> DecsQ
mkDiffMany d xs = concat <$> traverse (`mkDiff` d) xs

simple :: [Con] -> Bool
simple = all isSimpleEnum
  where
    isSimpleEnum con =
      case con of
        NormalC _ [] ->
          True
        RecC _ [] ->
          True
        _ ->
          False

getUnderlyingTypeName :: Type -> Q Name
getUnderlyingTypeName a = go a
  where
    go x =
      case x of
        ConT name ->
          pure name
        ForallT _binders _cxt typ ->
          go typ
        AppT t _ ->
          go t
        AppKindT t _ ->
          go t
        SigT t _ ->
          go t
        VarT e ->
          fail
            $ "Can't make a diff on a 'VarT' type: "
            <> show e
            <> " in a context: "
            <> show a
        PromotedT n ->
          fail
            $ "Can't make a diff on a promoted type: "
            <> show n
            <> " in a context: "
            <> show a

        InfixT _lhs op _rhs ->
          pure op
        UInfixT _ op _ ->
          pure op

        ParensT t ->
          go t
        TupleT i ->
          pure $ tupleTypeName i
        UnboxedTupleT i ->
          pure $ unboxedTupleTypeName i
        UnboxedSumT i ->
          pure $ unboxedSumTypeName i
        ArrowT ->
          fail "sorry i don't support function types"
        EqualityT ->
          fail "sorry i don't support type equalities"
        ListT ->
          pure listName
        PromotedTupleT _ ->
          fail "nope not gonna touch this one"
        PromotedNilT ->
          fail "not gonna diff a datakind lol"
        PromotedConsT ->
          fail "not gonna diff a datakind lol"
        StarT ->
          fail "can't diff a kind sorry"
        ConstraintT ->
          fail "can't diff a constraint"
        LitT _ ->
          fail "can't diff a type level natural sorry"
        WildCardT ->
          fail "not even possible???"
        ImplicitParamT _ _ ->
          fail "you used an implicit param, that's not okay"

listName :: Name
listName = ''[]

-- | Diffs can be customized. So we have an options record.
--
-- Except currently we don't support any customization. But I'd rather have
-- this around in case you wanted to use it
data MkDiffOptions = MkDiffOptions

defaultDiffOptions :: MkDiffOptions
defaultDiffOptions = MkDiffOptions

mkSumDiff :: Name -> [TyVarBndr] -> [Con] -> DecsQ
mkSumDiff name tyvars cons = do
  sdt <- mkSumDiffType name tyvars cons
  let
    originalType =
      reapplyTypeVariables name tyvars
    diffTypeInstance =
      TySynEqn Nothing (applyDiffOfT originalType) (sumDiffTypeType sdt)

  diffClauses <- mkSumDiffClauses sdt
  patchClauses <- mkSumPatchClauses sdt
  pure
    [ DataD [] (sumDiffTypeName sdt) tyvars Nothing (sumDiffTypeConstructorsPlain sdt) []
    , InstanceD Nothing (mkDiffableContext tyvars) (ConT ''Diffable `AppT` originalType)
      [ TySynInstD diffTypeInstance
      , FunD 'diff diffClauses
      , FunD 'patch patchClauses
      ]
    ]

-- | okay let's think through this:
--
-- * For each origional constructor: con
--   * We generate two clauses:
--     1. If the constructor is the same, then the result is the ConstrDiff
--     2. If the constructor is different, then the result is the ConstrSet
mkSumDiffClauses :: SumDiffType -> Q [Clause]
mkSumDiffClauses sdt = concat <$> do
  for (sumDiffTypeConstructors sdt) $ \sdc -> do
    vars <- mkPatternMatchVars (sdcOriginal sdc)
    let
      originalConstrName =
        getConstrName (sdcOriginal sdc)
      diffBody =
        let
          diffConstr =
            ConE $ getConstrName $ sdcDiff sdc
          fields =
            zipFieldsWithFunction 'diff vars
         in
          foldl' AppE diffConstr fields

      setBody =
        let
          setConstr =
            ConE $ getConstrName $ sdcSet sdc
          fields =
            map (VarE . snd) vars
         in
          foldl' AppE setConstr fields

    pure
      [ Clause
        [ ConP originalConstrName (map (VarP . fst) vars)
        , ConP originalConstrName (map (VarP . snd) vars)
        ] (NormalB diffBody)
        []
      , Clause
        [ WildP
        , ConP originalConstrName (map (VarP . snd) vars)
        ]
        (NormalB setBody)
        []
      ]

-- | OK, here's the trickiest part of the whole thing, I think.
--
-- Basically our pattern looks like:
--
-- @
-- patch _ (Constr0Set a b c) =
--   pure $ Constr0 a b c
-- patch (Constr0 a b c) (Constr0Diff a' b' c') =
--   Constr0 <$> patch a a' <*> patch b b' <*> patch c c'
--
-- patch _ (Constr1Set a b c) =
--   pure $ Constr1 a b c
-- patch (Constr1 a b c) (Constr1Diff a' b' c') =
--   Constr1 <$> patch a a' <*> patch b b' <*> patch c c'
--
-- ...
--
-- patch _ (ConstrNSet a b c) =
--   pure $ ConstrN a b c
-- patch (ConstrN a b c) (ConstrNDiff a' b' c') =
--   ConstrN <$> patch a a' <*> patch b b' <*> patch c c'
--
-- patch _ _ =
--   Nothing
-- @
--
-- That last wildcard case should handle all of the cases where we have
-- something like:
--
-- @
-- patch (Constr0 a b c) (Constr1Diff x y) = ...
-- @
--
-- which are totally incompatible.
mkSumPatchClauses :: SumDiffType -> Q [Clause]
mkSumPatchClauses sdt = do
  goodClauses <- for (sumDiffTypeConstructors sdt) $ \sdc -> do
    abNames <- mkPatternMatchVars (sdcOriginal sdc)
    let
      setPattern =
        ConP (getConstrName (sdcSet sdc)) (map (VarP . snd) abNames)
      setExpr =
        VarE 'pure
          `AppE`
            foldl'
              AppE
              (ConE (getConstrName (sdcOriginal sdc)))
              (map (VarE . snd) abNames)
      originalPattern =
        ConP (getConstrName (sdcOriginal sdc)) (map (VarP . fst) abNames)
      diffPattern =
        ConP (getConstrName (sdcDiff sdc)) (map (VarP . snd) abNames)

    pbStart <- [e|pure $(conE (getConstrName (sdcOriginal sdc)))|]
    patchExpr <-
      foldM
        (\acc x -> [e|$(pure acc) <*> $(pure x)|])
        pbStart
        (zipFieldsWithFunction 'patch abNames)

    pure
      [ Clause [WildP, setPattern] (NormalB setExpr) []
      , Clause [originalPattern, diffPattern] (NormalB patchExpr) []
      ]

  let
    failClause =
      Clause [WildP, WildP] (NormalB (ConE 'Nothing)) []
  pure (join goodClauses ++ [failClause])

data SumDiffType = SumDiffType
  { sumDiffTypeName :: Name
  , sumDiffTypeConstructors :: [SumDiffConstr]
  , sumDiffTypeType :: Type
  }

data SumDiffConstr = SumDiffConstr
  { sdcOriginal :: Con
  , sdcDiff :: Con
  , sdcSet :: Con
  }

sumDiffTypeConstructorsPlain
  :: SumDiffType
  -> [Con]
sumDiffTypeConstructorsPlain =
  concatMap (\(SumDiffConstr _ b c) -> [b, c]) . sumDiffTypeConstructors

mkSumDiffType :: Name -> [TyVarBndr] -> [Con] -> Q SumDiffType
mkSumDiffType name tyvars cons = do
  newConstrs <- traverse mkCons cons
  pure SumDiffType
    { sumDiffTypeName =
        mkDiffName name
    , sumDiffTypeConstructors =
        newConstrs
    , sumDiffTypeType =
        reapplyTypeVariables (mkDiffName name) tyvars
    }
  where
    mkCons con = uncurry (SumDiffConstr con) <$> case con of
      NormalC n fields ->
        pure
          ( NormalC (mkDiffName n) (map mkDiffType fields)
          , NormalC (suffixName "Set" n) fields
          )
      RecC n fields ->
        pure
          ( RecC (mkDiffName n) (map mkVarDiffType fields)
          , RecC (suffixName "Set" n) fields
          )
      InfixC lhs n rhs ->
        pure
          ( InfixC (mkDiffType lhs) (suffixName "!!!" n) (mkDiffType rhs)
          , InfixC lhs (suffixName "???" n) rhs
          )
      _ ->
        fail "illegal complex constructor"

deriveDiff :: Name -> DecsQ
deriveDiff name = [d|deriving instance Diffable $(conT name)|]

reapplyTypeVariables :: Name -> [TyVarBndr] -> Type
reapplyTypeVariables name tyvars =
  foldl' appendTyVar (ConT name) tyvars
  where
    appendTyVar acc tyvar =
      acc `AppT` case tyvar of
        PlainTV nm ->
          VarT nm
        KindedTV nm _kind ->
          VarT nm

mkDiffName :: Name -> Name
mkDiffName = suffixName "Diff"

suffixName :: String -> Name -> Name
suffixName s n = mkName $ nameBase n ++ s

diffOfT :: Type
diffOfT = ConT ''DiffOf

applyDiffOfT :: Type -> Type
applyDiffOfT t = diffOfT `AppT` t

mkDiffType :: (a, Type) -> (a, Type)
mkDiffType = fmap applyDiffOfT

mkVarDiffType :: (Name, a, Type) -> (Name, a, Type)
mkVarDiffType (n, bang_, typ) =
  (mkDiffName n, bang_, applyDiffOfT typ)

mkDiffableContext :: [TyVarBndr] -> [Type]
mkDiffableContext =
  map (AppT (ConT ''Diffable) . VarT . getTyVarBndrName)

getTyVarBndrName :: TyVarBndr -> Name
getTyVarBndrName tvb =
  case tvb of
    PlainTV n -> n
    KindedTV n _ -> n

-- | This function takes a 'Con'structor and returns a list of pairs of names
-- that would be the result of binding a pair of the constructors in a function
-- body. For example, given a type:
--
-- @
-- data Foo = Foo Int Char String
-- @
--
-- this would create a list of 3 elements, suitable for use like:
--
-- @
-- x (Foo a0 a1 a2) (Foo b0 b1 b2) =
--   ...
-- @
mkPatternMatchVars :: Con -> Q [(Name, Name)]
mkPatternMatchVars con = do
  let
    fieldCount =
      case con of
        NormalC _ bangTypes -> do
          length bangTypes
        RecC _ varBangTypes -> do
          length varBangTypes
        InfixC {} ->
          2
        _ ->
          error "illegal constructor"
  replicateM fieldCount ((,) <$> newName "a" <*> newName "b")

mkProductDiff :: Name -> [TyVarBndr] -> Con -> DecsQ
mkProductDiff name tyvars con = do
  let
    originalType =
      reapplyTypeVariables name tyvars
    diffName =
      mkDiffName name
    diffType =
      reapplyTypeVariables diffName tyvars
    diffTypeInstance =
      TySynEqn Nothing (applyDiffOfT originalType) diffType
    mkDiffConstructor c =
      case c of
        NormalC n bangTypes ->
          pure $ NormalC (mkDiffName n) (map mkDiffType bangTypes)
        RecC n varBangTypes ->
          pure $ RecC (mkDiffName n) (map mkVarDiffType varBangTypes)
        InfixC bangTypeLhs n bangTypeRhs ->
          pure $
            InfixC
              (applyDiffOfT <$> bangTypeLhs)
              (suffixName "!!!" n)
              (applyDiffOfT <$> bangTypeRhs)
        ForallC _binders _cxt _con ->
          fail "no fancy types in the diff, please"
        GadtC _names _bangTypes _retTyp ->
          fail "no fancy types in the diff, please"
        RecGadtC _names _varBangTypes _retType ->
          fail "no fancy types in the diff, please"

  abNames <- mkPatternMatchVars con

  let
    constrName = getConstrName con
    (aNames, bNames) = unzip abNames

  cons' <- mkDiffConstructor con
  let
    diffConstructorName =
      getConstrName cons'
    diffBody =
      foldl'
        AppE
        (ConE (getConstrName cons'))
        (zipFieldsWithFunction 'diff abNames)
    diffPatterns =
      [ ConP constrName (VarP <$> aNames)
      , ConP constrName (VarP <$> bNames)
      ]

    patchPatterns =
      [ ConP constrName (VarP <$> aNames)
      , ConP diffConstructorName (VarP <$> bNames)
      ]

  pbStart <- [e|pure $(conE constrName)|]
  patchBody <-
    foldM
      (\acc x -> [e|$(pure acc) <*> $(pure x)|])
      pbStart
      (zipFieldsWithFunction 'patch abNames)
  pure
    [ DataD [] diffName tyvars Nothing [cons'] []
    , InstanceD Nothing (mkDiffableContext tyvars) (ConT ''Diffable `AppT` originalType)
      [ TySynInstD diffTypeInstance
      , FunD 'diff
        [ Clause diffPatterns (NormalB diffBody) []
        ]
      , FunD 'patch
        [ Clause patchPatterns (NormalB patchBody) []
        ]
      ]
    ]

zipFieldsWithFunction :: Name -> [(Name, Name)] -> [Exp]
zipFieldsWithFunction nm (unzip -> (as, bs)) =
  zipWith (\a b -> VarE nm `AppE` VarE a `AppE` VarE b) as bs

getConstrName :: Con -> Name
getConstrName c =
  case c of
    NormalC n _ ->
      n
    RecC n _ ->
      n
    InfixC _ n _ ->
      n
    _ ->
      error "fancy constructor not allowed"
