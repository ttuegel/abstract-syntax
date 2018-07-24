{-# LANGUAGE TemplateHaskell #-}

module Lambda where

import Bound
import qualified Bound.Scope as Scope
import Control.Lens
import Control.Monad (ap)
import Data.Deriving (deriveRead1, deriveShow1)
import Data.Functor.Classes
import Data.Functor.Foldable
import Data.Monoid ((<>))

data SyntaxF term bind name note fvar r
    = PureF note fvar
    | TermF note (term r)
    | BindF note (fvar -> Maybe name) (bind r)
  deriving (Functor)

data Syntax
    term  {-^ base functor of terms -}
    bind  {-^ base functor of bindings -}
    name  {-^ bound names -}
    note  {-^ annotation -}
    fvar  {-^ free variables, or subterms more generally -}
    = Pure note fvar
    | Term note (term (Syntax term bind name note fvar))
    | Bind note (bind (Scope name (Syntax term bind name note) fvar))
  deriving (Foldable, Functor, Traversable)

deriveRead1 ''Syntax
instance
    ( Read1 term
    , Read1 bind
    , Read name
    , Read note
    , Read fvar
    ) =>
    Read (Syntax term bind name note fvar)
  where
    readsPrec = readsPrec1

deriveShow1 ''Syntax
instance
    ( Show1 term
    , Show1 bind
    , Show name
    , Show note
    , Show fvar
    ) =>
    Show (Syntax term bind name note fvar)
  where
    showsPrec = showsPrec1

{-| @note@ does not participate in equality.
 -}
instance
    ( Eq1 term, Functor term
    , Eq1 bind, Functor bind
    , Eq name
    , Monoid note
    ) =>
    Eq1 (Syntax term bind name note)
  where
    liftEq eq a b =
      case a of
        Pure _ fvara ->
          case b of
            Pure _ fvarb -> eq fvara fvarb
            _ -> False
        Term _ terma ->
          case b of
            Term _ termb -> liftEq (liftEq eq) terma termb
            _ -> False
        Bind _ scopea ->
          case b of
            Bind _ scopeb -> liftEq (liftEq eq) scopea scopeb
            _ -> False

{-| @note@ does not participate in equality.
 -}
instance
    ( Eq1 term, Functor term
    , Eq1 bind, Functor bind
    , Eq name
    , Monoid note
    , Eq fvar
    ) =>
    Eq (Syntax term bind name note fvar)
  where
    (==) = eq1

{-| @note@ does not participate in comparison.
 -}
instance
    ( Functor term, Ord1 term
    , Functor bind, Ord1 bind
    , Eq name, Ord name
    , Monoid note
    ) =>
    Ord1 (Syntax term bind name note)
  where
    liftCompare compare_ a b =
      case a of
        Pure _ fvara ->
          case b of
            Pure _ fvarb -> compare_ fvara fvarb
            Term {} -> LT
            Bind {} -> LT
        Term _ terma ->
          case b of
            Pure {} -> GT
            Term _ termb -> liftCompare (liftCompare compare_) terma termb
            Bind {} -> LT
        Bind _ scopea ->
          case b of
            Pure {} -> GT
            Term {} -> GT
            Bind _ scopeb -> liftCompare (liftCompare compare_) scopea scopeb

{-| @note@ does not participate in comparison.
 -}
instance
    ( Functor term, Ord1 term
    , Functor bind, Ord1 bind
    , Eq name, Ord name
    , Monoid note
    , Ord fvar
    ) =>
    Ord (Syntax term bind name note fvar)
  where
    compare = compare1

type instance Base (Syntax term bind name note fvar) = SyntaxF term bind name note fvar

instance
    (Functor term, Functor bind, Monoid note) =>
    Recursive (Syntax term bind name note (Fix (Var name)))
  where
    project =
      \case
        Pure note a -> PureF note a
        Term note term -> TermF note term
        Bind note scope -> BindF note abst (Scope.instantiate inst <$> scope)
      where
        abst =
          \case
            Fix (B name) -> Just name
            _ -> Nothing
        inst = pure . Fix . B

instance
    (Functor term, Functor bind, Monoid note) =>
    Corecursive (Syntax term bind name note fvar)
  where
    embed =
      \case
        PureF note a         -> Pure note a
        TermF note term      -> Term note term
        BindF note abst expr -> Bind note (Scope.abstract abst <$> expr)

annotation :: Lens' (Syntax term bind name note fvar) note
annotation = lens get1 set1
  where
    get1 =
      \case
        Pure note _ -> note
        Term note _ -> note
        Bind note _ -> note
    set1 syn note =
      case syn of
        Pure _ a     -> Pure note a
        Term _ term  -> Term note term
        Bind _ scope -> Bind note scope

data LambdaF a = Apply a a
  deriving (Eq, Foldable, Functor, Traversable)

type Lambda = Syntax LambdaF Identity ()

instance
    ( Functor term
    , Functor bind
    , Monoid note
    ) =>
    Applicative (Syntax term bind name note)
  where
    pure = Pure mempty
    (<*>) = ap

instance
    ( Functor term
    , Functor bind
    , Monoid note
    ) =>
    Monad (Syntax term bind name note)
  where
    return = pure
    (>>=) syn sub =
      case syn of
        Pure note a     -> over annotation (note <>) (sub a)
        Term note term  -> Term note (( >>= sub) <$> term )
        Bind note scope -> Bind note ((>>>= sub) <$> scope)

lam :: Eq a => a -> Lambda () a -> Lambda () a
lam v b = (Bind () . pure) (abstract1 v b)
