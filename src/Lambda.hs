module Lambda where

import Bound
import qualified Bound.Scope as Scope
import Control.Lens
import Control.Monad (ap)
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

type instance Base (Syntax term bind name note fvar) = SyntaxF term bind name note fvar

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
  deriving (Foldable, Functor, Traversable)

type Lambda = Syntax LambdaF Identity ()

instance (Functor term, Functor bind) => Functor (Syntax term bind name note) where
    fmap f =
      \case
        Pure note a     -> Pure note (f a)
        Term note term  -> Term note (fmap (fmap f) term )
        Bind note scope -> Bind note (fmap (fmap f) scope)

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
