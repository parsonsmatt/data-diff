{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE TypeFamilyDependencies #-}

-- | This module contains a type class, examples, and helpers for "diffing" your
-- data. These diff types can be used to determine how two values differ, as
-- well as applying the resulting patch to the original datatype.
--
-- Design goals:
--
-- 1) @'diff' :: 'Diffable' a => a -> a -> 'DiffOf' a@. This function is the
--    starting point. It should highlight how the two values differ in a minimal
--    way.
--
--    For primitive types (eg 'Int', 'Char', etc) it should simply be the new
--    value. So a 'DiffOf' for an 'Int' should just be 'Int' - a new value. It
--    is probably not meaningful or desirable to represent more fine-grained
--    operations, like @(+3)@ or @(*2)@ since we don't know how the two values
--    came to have their differing values.
--
--    But we still need a way to say whether or not it changed. So a 'DiffOf'
--    for an 'Int' would need to have the shape @Unchanged | Different Int@.
--
--    This gives us the type @data 'ValueDiff' a = 'Unchanged' | 'Different' a@.
--
--    For record types, we set each field to be a 'DiffOf field'.
--
--    For sum types, we have two possibilities for each constructor in the sum:
--      a) The constructor changed, so we @Set@ to the new constructor with the
--         new values.
--      b) The constructor is the same, so we @Diff@ each field in the
--         constructor.
--
-- 2) @'patch' :: 'Diffable' a => a -> 'DiffOf' a -> 'Maybe' a@. Once you've
--    applied 'diff'  to your values, you'll have a @'DiffOf' a@. Now, we can
--    use 'patch' to apply that 'diff' to a value and potentially receive a new
--    value back.
--
--    However, it's possible that the diff just isn't compatible, or doesn't make much sense.
--    That's why the return type has Maybe. For example, suppose we try to
--    'diff' two lists:
--
--    @
--    >>> let listDiff = diff [1,2,3] [1,2]
--    ['Keep', 'Keep', 'Delete']
--    @
--
--    That @listDiff@ value instructs us how to go from @[1,2,3] => [1,2]@. If
--    we tried patching a list that only has two elements, then we'd be deleting
--    the end - nonsense!
--
--    Likewise, if we have a sum type, we might have a diff like:
--
--    @
--    >>> let maybeDiff = diff (Just 3) (Just 4)
--    'JustDiff' ('Different' 4)
--    @
--
--    If we try to apply this to a 'Nothing' constructor, then this is
--    incompatible - so we cannot succesfully perform this diff.
--
-- 3) Ideally, the resulting 'DiffOf' type should be amenable to serialization
--    type classes. It'd be good to have 'DiffOf' information available on the
--    front-end, or potentially stored in databases.
--
-- The module contains a lot of somewhat redundant code. This is because the
-- module is meant to serve as a guide on how the resulting code was created and
-- discovered.
module Data.Diff where

import Data.Text (Text)

-- | We use a type class 'Diffable' to represent values that can have diffs and
-- patches applied. Currently, this is limited to "simple" datatypes - so no
-- functions, GADTs, existentials, etc are allowed!
--
-- "Why use a type class?" you might ask. That's a great question! I tried to
-- avoid using a type class at first, and instead have concrete monomorphic
-- @diffType@ functions. However, we run into a problem with type variables.
-- With concrete types, we can simply use the appropriate @DiffType@:
-- 'ValueDiff' for simple types, 'MaybeDiff' for 'Maybe', and other custom diff
-- types where appropriate. But - consider @'Maybe' a@ - we need to know what the
-- @DiffType@ is for @a@! So we actually need to have *two* type parameters, one
-- of which is a higher kinded type.
--
-- It turns out, it dramatically simplifies the 'DiffOf' types to represent this
-- as a type class, because we have a first-class means of saying "The 'DiffOf'
-- type." The definition for a non-type-family approach on a 'Maybe' diff looks
-- like:
--
-- @
-- data MaybeDiff diffOf a
--   = NothingSet
--   | NothingDiff
--   | JustSet a
--   | JustDiff (diffOf a)
-- @
--
-- The extra type parameter is required for every single type, so 'Either' looks
-- much worse:
--
-- @
-- data EitherDiff diffOfL diffOfR l r
--   = LeftSet l
--   | LeftDiff (diffOfL l)
--   | RightSet r
--   | RightDiff (diffOfR r)
-- @
--
-- With the associated type 'DiffOf', this is much simpler:
--
-- @
-- data EiherDiff l r
--   = LeftSet l
--   | LeftDiff (DiffOf l)
--   | RightSet r
--   | RightDiff (DiffOf r)
-- @
--
-- The class can be derived with @anyclass@ deriving strategy, provided that the
-- type has an 'Eq' instance. This is useful for primitive types, like 'Bool',
-- 'Int', 'Char'. You can use the simple derivation if you don't want higher
-- resolution diffs than "The whole value changed."
class Eq a => Diffable a where
  -- | The associated type has an injectivity annotation to signal that the
  -- 'DiffOf' for a type must be unique. This type represents the "difference"
  -- of the original type.
  --
  -- For very simple cases (eg the default implementations), we use 'ValueDiff'.
  -- This type is extremely simple - it supports 'Unchanged' and @'Different' x@
  -- where @x@ is the new value to put in the place. This provides a very low
  -- resolution diff - only that something is changed or not.
  --
  -- For a more powerful and precise diff type, you will want to create a new
  -- datatype. The module "Data.Diff.TH" contains Template Haskell helpers, but
  -- this module has several example datatypes that are hand-written that do the
  -- job nicely.
  type DiffOf a = x | x -> a
  type DiffOf a = ValueDiff a

  -- | This function produces a 'DiffOf' for the type.
  --
  -- The default relies on the 'Eq' instance for the underlying type, and
  -- provides a simple 'ValueDiff' result. This is not great for complex types,
  -- but for a simple type like 'Int' or 'Double' it works great.
  diff :: a -> a -> DiffOf a

  default diff :: (DiffOf a ~ ValueDiff a, Eq a) => a -> a -> DiffOf a
  diff = diffEq

  -- | This function can attempt to patch an @a@ with a 'DiffOf' that type and
  -- yield a value. It's not guaranteed that a patch will succeed.
  patch :: a -> DiffOf a -> Maybe a
  default patch :: (DiffOf a ~ ValueDiff a, Eq a) => a -> DiffOf a -> Maybe a
  patch = patchEq

-- | This type is isomorphic to 'Maybe', but it has a different semantic
-- meaning. Primitive values, like 'Int', will use this as a 'DiffOf' type.
data ValueDiff a
  = Unchanged
  | Different a
  deriving Show

diffInt :: Int -> Int -> ValueDiff Int
diffInt x y
  | x == y = Unchanged
  | otherwise = Different y

patchInt :: Int -> ValueDiff Int -> Maybe Int
patchInt i d =
  Just $ case d of
    Unchanged -> i
    Different x -> x

diffChar :: Char -> Char -> ValueDiff Char
diffChar a b
  | a == b = Unchanged
  | otherwise = Different b

patchChar :: Char -> ValueDiff Char -> Maybe Char
patchChar i d =
  Just $ case d of
    Unchanged -> i
    Different x -> x

-- | OK, you get the gist, for simple things, we can write a function generic on
-- 'Eq' that does the obvious thing. This also never fails, so you may
-- rightfully wonder "Why bother with the 'Maybe'?" As good of a question as
-- that is, I only have my intuition to guide me. I suspect that the general
-- function shape:
--
-- @
-- diffThing :: a -> 'DiffOf' a -> 'Maybe' a
-- @
--
-- will be easier to work with than making the optionality optional conditional
-- on the input type.
patchEq :: (Diffable a, DiffOf a ~ ValueDiff a) => a -> ValueDiff a -> Maybe a
patchEq a b =
  Just $ case b of
    Unchanged -> a
    Different x -> x

-- | Likewise, the diffs for simple 'Eq' values is easy.
diffEq :: Eq a => a -> a -> ValueDiff a
diffEq a b =
  if a == b
    then Unchanged
    else Different b

-- | Thanks to this 'Eq' based diff/patch, we can write empty instances for
-- types that we want to have the simple/primitive instances.
instance Diffable Double
instance Diffable Int
instance Diffable Integer
instance Diffable Char

-- | This one should probably use @'EditList' 'Char'@ like the String instance,
-- but that violates the injectivity constraint! So we'll just do this for now
-- :|
instance Diffable Text

-- | Alas, we can't get away with the simple approach here. We actually do want
-- to be able to say that a list differs with some kind of 'edit script'. We
-- want to be able to say "This list is the same as this other list, but with
-- X element removed."
--
-- We return an 'EditList', which is a list of 'EditListItem'. This "edit
-- script" tells us how to modify a list to produce the second one. These
-- patches are the first patches that can fail, and we'lll see how in
-- 'patchList'.
--
-- The implementation of this is from this paper: http://eelco.lempsink.nl/thesis.pdf
diffList :: Diffable a => [a] -> [a] -> EditList a
diffList xs ys
  | xs == ys = [] -- no edits = no change
diffList [] [] = []
diffList [] xs = map Add xs
diffList xs [] = map (const Delete) xs
diffList (x : xs) (y : ys) =
  if x == y
    then best3
    else best2
  where
    best2 =
      (Delete : diffList xs (y : ys))
      `lowestCost`
      (Add y : diffList (x:xs) ys)
      `lowestCost`
      (Modify (diff x y) : diffList xs ys)

    best3 =
      (Keep : diffList xs ys)
      `lowestCost`
      best2

    lowestCost dx dy =
      if cost dx <= cost dy then dx else dy

    cost = length

-- | Patching a list can have two basic actions:
--
-- * Either the list is completely unchanged.
-- * Or there are some edits to the list.
--
-- I chose to use @[EditListItem a]@ for this. I could have also done the
-- isomorphic and more explicit:
--
-- @
-- data EditListItem a
--   = SameList
--   | EditList (NonEmpty (EditListItem a))
-- @
--
-- but that felt a little more awkward while writing the code. Might be useful
-- and clarifying to refactor with this redundant type.
type EditList a =
  [EditListItem a]

-- | When we are editing a list, we have a few possibilities on how we'll
-- approach each element. This datatype represents these things.
data EditListItem a
  = Keep
  -- ^ We may decide to just keep the element in question, if the element is
  -- shared between two lists.
  | Delete
  -- ^ Likewise, we may just need to remove an item from a list.
  | Add a
  -- ^ If there are fresh, wholesale items in the list that need to be added,
  -- this is the constructor that gets used.
  | Modify (DiffOf a)
  -- ^ Finally, we may want to modify a list item, and provide a diff for it.
  -- The algorithm in 'diffList' will try to produce the shortest edit list
  -- possible, and a 'Modify' is shorter than a 'Delete' and 'Add' pair.

-- | This is how we get to derive instances for these types. It's a little
-- annoying needing to specify the context manually, but it's ultimately
-- straightforward.
deriving instance (Show a, Show (DiffOf a)) => Show (EditListItem a)

-- | Patching a list is the first patch in the module that might fail. If the
-- 'EditList' is empty, then we have an unchanged list, and we return the list
-- as-is.
--
-- If we are patching an empty list, and we run into a 'Keep', 'Delete', or
-- 'Modify' constructor, then we fail, returning 'Nothing'.
--
-- We can fail to diff a list if we fail to diff an item in the list.
--
-- Otherwise, 'Add'ing an item to a list always succeeds. 'Delete'ing or
-- 'Keep'ing an item from a non-empty list always succeed.
patchList :: Diffable a => [a] -> EditList a -> Maybe [a]
patchList xs [] = Just xs
patchList list edits = go list edits
  where
    go xs [] =
      Just xs
    go [] (Keep : _rest) =
      Nothing
    go [] (Delete : _rest) =
      Nothing
    go [] (Modify _ : _rest) =
      Nothing
    go (x : xs) (Keep : rest) =
      (x :) <$> go xs rest
    go (_ : xs) (Delete : rest) =
      go xs rest
    -- Modifying a list item
    go (a : xs) (Modify d : rest) = do
      a' <- patch a d
      (a' :) <$> go xs rest
    go xs (Add a : rest) =
      (a :) <$> go xs rest

-- | For diffing product types, we'll actually create a new product type that
-- contains diffs of it's fields. This is an example product type that we might
-- perform a diff on. It's relatively simple: only 'terminal' values.
data ExampleProduct = ExampleProduct
  { epName :: String
  , epAge :: Int
  , epDogs :: [Char]
  }
  deriving Eq

-- | The resulting datatype is easy and mechanical to write, and the Template
-- Haskell helperes in "Data.Diff.TH" will generate exactly this code. We suffix
-- the type name, constructor name, and field names with @Diff@, and the field
-- types have the 'DiffOf' type family applied to them.
data ExampleProductDiff = ExampleProductDiff
  { epNameDiff :: DiffOf String
  , epAgeDiff :: DiffOf Int
  , epDogsDiff :: DiffOf [Char]
  }

-- | The function to diff the product type is easy to mechanically generate, as
-- well. We extract each field and call 'diff' on the fields.
diffExampleProduct
  :: ExampleProduct
  -> ExampleProduct
  -> ExampleProductDiff
diffExampleProduct ep0 ep1 =
  ExampleProductDiff
    { epNameDiff = diff (epName ep0) (epName ep1)
    , epAgeDiff = diff (epAge ep0) (epAge ep1)
    , epDogsDiff = diff (epDogs ep0) (epDogs ep1)
    }

-- | Patching is also pretty mechanical. We call 'patch' on all the fields in
-- the datatype, and apply the constructor to the results. This happens in the
-- 'Maybe' monad, though the Template Haskell generators use the Applicative
-- notation instead.
patchExampleProduct
  :: ExampleProduct
  -> ExampleProductDiff
  -> Maybe ExampleProduct
patchExampleProduct ep diffEp = do
  name <- patch (epName ep) (epNameDiff diffEp)
  age <- patch (epAge ep) (epAgeDiff diffEp)
  dogs <- patch (epDogs ep) (epDogsDiff diffEp)
  pure $ ExampleProduct name age dogs

-- | With these things equipped, we can now write our instance of 'Diffable' for
-- the 'ExampleProduct' type.
instance Diffable ExampleProduct where
  type DiffOf ExampleProduct = ExampleProductDiff

  diff = diffExampleProduct
  patch = patchExampleProduct



-- | Diffing and patching sum types is a little more complicated. So let's do
-- 'Maybe' first. This isn't the real implementation - just a brief example of
-- what it might be like if we follow the default/'Eq' approach.
--
-- While it works for the very simplest case - it's unsatisfying, because we
-- don't have a way of expressing anything more complicated than "the underlying
-- value is different - here's the whole thing." We'd like to be able to say
-- *how* the underlying value is different.
diffMaybe0 :: Eq a => Maybe a -> Maybe a -> ValueDiff (Maybe a)
diffMaybe0 m0 m1 =
  case m0 of
    Nothing ->
      case m1 of
        Nothing ->
          Unchanged
        Just a ->
          Different (Just a)
    Just a ->
      case m1 of
        Nothing ->
          Different Nothing
        Just b ->
          if a == b
            then Unchanged
            else Different (Just b)

-- | If we want to provide a richer 'DiffOf' type for 'Maybe', then we need to
-- account for a few things:
--
-- * If the constructor is the same, we want to 'diff' the fields on the
--   constructor.
-- * If the constructor is different, then we want to @Set@ the fields with the
--   new constructor.
--
-- For nullary constructors, like 'Nothing', this can be a bit awkward
-- - 'NothingDiff' means that the constructor was the same, while 'NothingSet'
-- means that the constructor changed. They carry the same information, and are
-- isomorphic to each other, but they have different semantic meaning.
data MaybeDiff a
  = NothingDiff
  -- ^ This is the constructor when we call @'diff' 'Nothing' 'Nothing'@.
  | NothingSet
  -- ^ This is the constructor when we call @'diff' ('Just' _) 'Nothing'@.
  --
  -- We keep two constructors here, because we generate two constructors for
  -- every sum type's constructor with all the fields intact. We could feasibly
  -- just say 'NothingSet', but then we lose the ability to assert "It was
  -- 'Nothing' and is now still 'Nothing' - no change" vs "It was 'Just' and is
  -- now 'Nothing' - changed."
  | JustDiff (DiffOf a)
  -- ^ If we call @'diff' ('Just' a) ('Just' b)@, then this is the constructor
  -- we'll get - specifically, @'JustDiff' ('diff' a b)@.
  | JustSet a
  -- ^ Finally, if we call @'diff' 'Nothing' ('Just' a)@, we get @'JustSet' a@.
  --
  -- The two constructors for 'Just' allow us to differentiate between "the
  -- constructor changed" and "the underlying value changed, but the constructor
  -- remained the same."

diffMaybe
  :: Diffable a
  => Maybe a
  -> Maybe a
  -> MaybeDiff a
diffMaybe m0 m1 =
  case (m0, m1) of
    (Nothing, Nothing) ->
      NothingDiff
    (_, Nothing) ->
      NothingSet

    (Just a, Just b) ->
      JustDiff (diff a b)
    (_, Just a) ->
      JustSet a

-- | Patching a 'Maybe' can fail - if we have a 'NothingDiff' patching a 'Just',
-- that means the original constructor was 'Nothing', and it was supposed to
-- remain the same. We fail in this case, even though it would be possible to
-- just set the value to 'Nothing'. It is consistent with the next case we'll
-- study - which must fail!
--
-- The other failing case is calling:
--
-- @
-- 'patchMaybe' 'Nothing' ('JustDiff' diffOfA)
-- @
--
-- This necessarily fails because we can't produce a @'Maybe' a@ with merely
-- a @'DiffOf' a@. The only way to get an @a@ out of a @'DiffOf' a@ is to call
-- 'patch'.
--
-- The other cases always succeed - setting a constructor is assumed to always
-- succeed, even though it may make sense to only succeed if a 'Set' is paired
-- with a different constructor. For example, cosnider:
--
-- @
-- patchMaybe (Just a) (JustSet b)
-- @
--
-- This succeeds with @Just (Just b)@. But it also makes sense to fail. Perhaps
-- a future version of this will have a notion of lenient vs strict patching.
patchMaybe
  :: Diffable a
  => Maybe a
  -> MaybeDiff a
  -> Maybe (Maybe a)
patchMaybe ma mdiff =
  case (ma, mdiff) of
    -- If we have same constructors, it's easy!
    (Nothing, NothingDiff) ->
      Just Nothing
    (Just a, JustDiff vdiff) ->
      Just (patch a vdiff)
    -- If the constructors are changed, it's also easy!
    (Just _, NothingSet) ->
      Just Nothing
    (Nothing, JustSet a) ->
      Just (Just a)
    -- But it gets a little hairy if we have an 'incompatible diff'. If we have
    -- 'NothingSet' as our diff, and 'Nothing' as our value, then it's... not
    -- semantically valid. We'd need 'NothingDiff' for the diff to be
    -- compatible.
    --
    -- So how much do we care about that compatibility? For Maybe, it seems
    -- pretty innocuous to just let it slide.
    (Nothing, NothingSet) ->
      Just Nothing
    (Just _, JustSet a) ->
      Just (Just a)

    -- And these are obviously bad.
    (Nothing, JustDiff _) ->
      Nothing
    (Just _, NothingDiff) ->
      Nothing

-- | So here's a slightly more complicated sum type. This one has three
-- constructors, each of which contains different field counts. We'll manually
-- create a diff type for it, 'ExSum0Diff', that will mirror the type generated
-- by the Template Haskell code.
--
--
-- But first, we'll explore a bad implementation, because it is edifying.
data ExSum0
  = ExSumNullary
  | ExSumUnitary Int
  | ExSumBinary Char [Int]

-- | If we just walk over the sum type and apply a suitable @Diff@ type to each
-- payload, we get this type. It has some problems, which we'll explore in the
-- diff and patch implementations.
data DiffExSum0
  = DiffExSumNullary
  | DiffExSumUnitary (DiffOf Int)
  | DiffExSumBinary (DiffOf Char) (DiffOf [Int])

-- | Comments for this are in the body of the function - view source to see it.
diffExSum0 :: ExSum0 -> ExSum0 -> DiffExSum0
diffExSum0 e0 e1 =
  case (e0, e1) of
    -- If the latter is nullary, then we just provide nullary as the diff. This
    -- is assumed to mean either "no change if already nullary" or "set to
    -- nullary." Having two meanings is a little unsatisfying to me.
    (_, ExSumNullary) ->
      DiffExSumNullary

    -- If the new value is Unitary, and the old value is Unitary, then we do
    -- a diff on the two values.
    (ExSumUnitary i, ExSumUnitary j) ->
      DiffExSumUnitary (diffInt i j)
    -- But if the new value is Unitary and the old is a different constructor,
    -- then we want to just *set* it to be the new value. This result is
    -- identical to the previous case where the values are different, so it's
    -- a little unsatisfying to lose that information - is it just that the
    -- constructor changed and we set a new value, or did we have the same
    -- constructor and got a different value?
    (_, ExSumUnitary i) ->
      DiffExSumUnitary (Different i)

    -- The binary case follows the prior pattern, and we have the same issue of
    -- losing resolution on when the constructor changed vs when values in the
    -- constructor are changed.
    (ExSumBinary c is, ExSumBinary c' is') ->
      DiffExSumBinary (diff c c') (diff is is')
    (_, ExSumBinary c is) ->
      DiffExSumBinary (Different c) (diff [] is)

-- | So we have two sources of frustration here:
--
-- 1) The first formulation has some redundant cases, but provides complete
--    information.
-- 2) The second formulation omits some information, but has no overlapping
--    cases.
--
-- Let's try the first formulation on 'ExSum0'.
data ExSum0Diff
  = NullaryDiff
  | NullarySet
  -- ^ For nullary constructors, setting and same are semantically identical,
  -- but can be useful in demonstrating "no change" vs "change".
  | UnitaryDiff (DiffOf Int)
  -- ^ If the constructor is the same, we want to provide a 'ValueDiff' on the
  -- underlying payload.
  | UnitarySet Int
  -- ^ But if the constructor is different, then we are only setting a new
  -- value.
  | BinaryDiff (DiffOf Char) (DiffOf [Int])
  | BinarySet Char [Int]
  -- ^ We follow the pattern above. A @Set@ constructor that takes fresh values,
  -- and a @Same@ constructor that takes diffs on those values.

-- | This is still a little unsatisfactory, but I'm starting to lean towards
-- providing more information with possible overlaps than less information with
-- no overlap.
--
-- If you have a better idea, please comment :D
diffExSum0' :: ExSum0 -> ExSum0 -> ExSum0Diff
diffExSum0' e0 e1 =
  case e0 of
    ExSumNullary ->
      case e1 of
        ExSumNullary ->
          -- If the constructors are the same, we use the @Diff@ constructor to
          -- say that.
          NullaryDiff
          -- Otherwise, we use the @Set@ constructor to indicate the change.
        ExSumUnitary i ->
          UnitarySet i
        ExSumBinary a b ->
          BinarySet a b
    ExSumUnitary i ->
      case e1 of
        ExSumNullary ->
          NullarySet
        ExSumUnitary j ->
          UnitaryDiff (diff i j)
        ExSumBinary a b ->
          BinarySet a b
    ExSumBinary a b ->
      case e1 of
        ExSumNullary ->
          NullarySet
        ExSumUnitary i ->
          UnitarySet i
        ExSumBinary c d ->
          BinaryDiff (diff a c) (diff b d)

-- | Patching is mechanical.
--
-- If we have a @Set@ constructor, then we set the value and succeed.
--
-- If we have a @Diff@ constructor, we check to ensure that the constructor is
-- the same. If it is, then we patch the payloads.
patchExSum0 :: ExSum0 -> ExSum0Diff -> Maybe ExSum0
patchExSum0 es0 es0d =
  case es0d of
    NullarySet ->
      Just ExSumNullary
    NullaryDiff ->
      case es0 of
        ExSumNullary ->
          Just ExSumNullary
        _ ->
          Nothing

    UnitarySet i ->
      Just (ExSumUnitary i)
    UnitaryDiff di ->
      case es0 of
        ExSumUnitary i ->
          ExSumUnitary <$> patch i di
        _ ->
          Nothing

    BinarySet a b ->
      Just (ExSumBinary a b)
    BinaryDiff da db ->
      case es0 of
        ExSumBinary a b ->
          ExSumBinary <$> patch a da <*> patch b db
        _ ->
          Nothing

-- | OK, let's do Either now! This one is a little more complicated, because we
-- have two unitary constructors.
data EitherDiff l r
  = LeftDiff (DiffOf l)
  | LeftSet l
  | RightDiff (DiffOf r)
  | RightSet r

diffEither
  :: Diffable l
  => Diffable r
  => Either l r
  -> Either l r
  -> EitherDiff l r
diffEither e0 e1 =
  case (e0, e1) of
    (Left l0, Left l1) ->
      LeftDiff (diff l0 l1)
    (Right r0, Right r1) ->
      RightDiff (diff r0 r1)
    (_, Left l) ->
      LeftSet l
    (_, Right r) ->
      RightSet r

patchEither
  :: Diffable l => Diffable r
  => Either l r
  -> EitherDiff l r
  -> Maybe (Either l r)
patchEither elr eitherDiff =
  case (elr, eitherDiff) of
    (Left l, LeftDiff ldiff) ->
      Left <$> patch l ldiff
    (Left _, RightSet r) ->
      Just $ Right r
    (Right r, RightDiff rdiff) ->
      Right <$> patch r rdiff
    (Right _, LeftSet l) ->
      Just $ Left l
    -- Here are the innocuous incompatibilities:
    (Left _, LeftSet l) ->
      Just $ Left l
    (Right _, RightSet r) ->
      Just $ Right r
    -- And the nocuous mpatibilities:
    (Right _, LeftDiff _) ->
      Nothing
    (Left _, RightDiff _) ->
      Nothing

instance Diffable a => Diffable [a] where
  type DiffOf [a] = EditList a

  diff = diffList
  patch = patchList

instance Diffable a => Diffable (Maybe a) where
  type DiffOf (Maybe a) = MaybeDiff a

  diff = diffMaybe
  patch = patchMaybe

instance (Diffable a, Diffable b) => Diffable (Either a b) where
  type DiffOf (Either a b) = EitherDiff a b

  diff = diffEither
  patch = patchEither
