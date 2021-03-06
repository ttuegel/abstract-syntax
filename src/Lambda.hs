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

data SyntaxF term bind bvar note fvar r
    = PureF note fvar
    | TermF note (term r)
    | BindF note (fvar -> Maybe bvar) (bind r)
  deriving (Foldable, Functor, Traversable)

{-| 'Syntax' generically represents abstract syntax trees with binding.

@term@ is a functor representing the non-binding terms of the syntax. @bind@ is
a functor representing the binders of the syntax. @bvar@ is the type of bound
variables; see "Bound.Name" to give bound variables names that do not
participate in equality. @note@ is the type of annotations given to each node in
the abstract syntax tree. @fvar@ is the type of subterms of the tree; typically
this is specialized to the type of free variables.

 -}
data Syntax
    term  {-^ base functor of terms -}
    bind  {-^ base functor of bindings -}
    bvar  {-^ bound variables -}
    note  {-^ annotation -}
    fvar  {-^ subterms (typically free variables -}
    = Pure note fvar
    | Term note (term (Syntax term bind bvar note fvar))
    | Bind note (bind (Scope bvar (Syntax term bind bvar note) fvar))
  deriving (Foldable, Functor, Traversable)

deriveRead1 ''Syntax
instance
    ( Read1 term
    , Read1 bind
    , Read bvar
    , Read note
    , Read fvar
    ) =>
    Read (Syntax term bind bvar note fvar)
  where
    readsPrec = readsPrec1

deriveShow1 ''Syntax
instance
    ( Show1 term
    , Show1 bind
    , Show bvar
    , Show note
    , Show fvar
    ) =>
    Show (Syntax term bind bvar note fvar)
  where
    showsPrec = showsPrec1

{-| @note@ does not participate in equality.
 -}
instance
    ( Eq1 term, Functor term
    , Eq1 bind, Functor bind
    , Eq bvar
    , Monoid note
    ) =>
    Eq1 (Syntax term bind bvar note)
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
    , Eq bvar
    , Monoid note
    , Eq fvar
    ) =>
    Eq (Syntax term bind bvar note fvar)
  where
    (==) = eq1

{-| @note@ does not participate in comparison.
 -}
instance
    ( Functor term, Ord1 term
    , Functor bind, Ord1 bind
    , Eq bvar, Ord bvar
    , Monoid note
    ) =>
    Ord1 (Syntax term bind bvar note)
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
    , Eq bvar, Ord bvar
    , Monoid note
    , Ord fvar
    ) =>
    Ord (Syntax term bind bvar note fvar)
  where
    compare = compare1

type instance Base (Syntax term bind bvar note fvar) = SyntaxF term bind bvar note fvar

instance
    (Functor term, Functor bind, Monoid note) =>
    Recursive (Syntax term bind bvar note (Fix (Var bvar)))
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
    Corecursive (Syntax term bind bvar note fvar)
  where
    embed =
      \case
        PureF note a         -> Pure note a
        TermF note term      -> Term note term
        BindF note abst expr -> Bind note (Scope.abstract abst <$> expr)

annotation :: Lens' (Syntax term bind bvar note fvar) note
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
    Applicative (Syntax term bind bvar note)
  where
    pure = Pure mempty
    (<*>) = ap

instance
    ( Functor term
    , Functor bind
    , Monoid note
    ) =>
    Monad (Syntax term bind bvar note)
  where
    return = pure
    (>>=) syn sub =
      case syn of
        Pure note a     -> over annotation (note <>) (sub a)
        Term note term  -> Term note (( >>= sub) <$> term )
        Bind note scope -> Bind note ((>>>= sub) <$> scope)

lam :: Eq a => a -> Lambda () a -> Lambda () a
lam v b = (Bind () . pure) (abstract1 v b)
