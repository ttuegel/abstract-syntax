module Lambda where

import Bound
import qualified Bound.Scope as Scope
import Control.Lens
import Control.Monad (ap)
import Data.Functor.Foldable
import Data.Monoid ((<>))

data SyntaxF term bind name note fvar rec
    = PureF note fvar
    | TermF note (term rec)
    | BindF note (fvar -> Maybe name) (bind rec)

instance (Functor b, Functor f) => Functor (SyntaxF f b n s a) where
    fmap f =
      \case
        PureF s a -> PureF s a
        TermF s r -> TermF s (f <$> r)
        BindF s abst r -> BindF s abst (f <$> r)

data Syntax
    term  {-^ base functor of terms -}
    bind  {-^ base functor of bindings -}
    name  {-^ bound names -}
    note  {-^ annotation -}
    fvar  {-^ free variables, or subterms more generally -}
    = Pure note fvar
    | Term note (term (Syntax term bind name note fvar))
    | Bind note (bind (Scope name (Syntax term bind name note) fvar))

type instance Base (Syntax f b n s v) = SyntaxF f b n s v

instance (Functor b, Functor f, Monoid s) => Corecursive (Syntax f b n s a) where
  embed =
    \case
      PureF s a -> Pure s a
      TermF s term -> Term s term
      BindF s abst expr -> Bind s (Scope.abstract abst <$> expr)

ann :: Lens' (Syntax term bind name note fvar) note
ann = lens get1 set1
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

instance (Functor f, Functor b) => Functor (Syntax f b n s) where
    fmap f =
      \case
        Pure note a     -> Pure note (f a)
        Term note term  -> Term note (fmap (fmap f) term )
        Bind note scope -> Bind note (fmap (fmap f) scope)

instance (Functor f, Functor b, Monoid s) => Applicative (Syntax f b n s) where
    pure = Pure mempty
    (<*>) = ap

instance (Functor f, Functor b, Monoid s) => Monad (Syntax f b n s) where
    return = pure
    (>>=) syn sub =
      case syn of
        Pure note a     -> over ann (note <>) (sub a)
        Term note term  -> Term note (( >>= sub) <$> term )
        Bind note scope -> Bind note ((>>>= sub) <$> scope)

lam :: Eq a => a -> Lambda () a -> Lambda () a
lam v b = (Bind () . pure) (abstract1 v b)
