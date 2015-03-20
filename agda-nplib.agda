module agda-nplib where
{-
import Algebra.Field
import Algebra.Field.Reflection
import Algebra.Field.Solver
-}
import Algebra.FunctionProperties.Derived
import Algebra.FunctionProperties.Eq
import Algebra.FunctionProperties.NP
import Algebra.Group
import Algebra.Group.Abelian
import Algebra.Group.Homomorphism
import Algebra.Monoid
import Algebra.Monoid.Homomorphism
import Algebra.NP
import Category
import Category.Applicative.NP
import Category.Functor.NP
import Category.Kleisli
import Category.Monad.Continuation.Alias
import Category.Monad.Continuation.Record
import Category.Monad.NP
import Category.Monad.Partiality.NP
import Category.Profunctor
import Data.Atom
import Data.Bit
import Data.Bits
import Data.Bits.Bits2
import Data.Bits.Bits4
import Data.Bits.OperationSyntax
import Data.Bits.Properties
import Data.Bool.NP
import Data.Bool.So
import Data.Char.NP
import Data.Default
import Data.Fin.Logical
import Data.Fin.NP
import Data.Fin.Store
import Data.Indexed
import Data.Indexed.Vec
import Data.Integer.NP
import Data.LR
import Data.Label
import Data.List.NP
import Data.List.Properties.NP
import Data.Maybe.NP
import Data.Maybe.Param.Binary.NP
import Data.Nat.Ack
import Data.Nat.BoundedMonoInj-is-Id
import Data.Nat.Distance
import Data.Nat.HyperOperators
import Data.Nat.Logical
import Data.Nat.NP
import Data.Nat.NameLess
import Data.Nat.Positive
import Data.One
import Data.Product.K
import Data.Product.NP
import Data.Product.Param.Binary.NP
import Data.RGB
import Data.ShapePolymorphism
import Data.Star.NP
import Data.Stream.NP
import Data.Sum.Logical
import Data.Sum.NP
import Data.Tree.Binary
import Data.Tree.Binary.Perfect
import Data.Tree.Binary.Perfect.Any
import Data.Two
import Data.Two.Base
import Data.Two.Equality
import Data.Two.Logical
import Data.Vec.Bijection
import Data.Vec.N-ary.NP
import Data.Vec.NP
import Data.Vec.Permutation
import Data.Zero
import Function.Bijection.NP
import Function.Bijection.SyntaxKit
import Function.Extensionality
import Function.Im
import Function.Injection.NP
import Function.InstanceArguments
import Function.Inverse.NP
import Function.NP
import Function.Param.Binary.NP
import Function.Param.Unary.NP
import Function.Related.TypeIsomorphisms.NP
import HoTT
import Irrelevance.NP
import Lens.Getter
import Lens.Internal
import Lens.Iso
import Lens.Prism
import Lens.Setter
import Lens.Structures
import Lens.Type
import Level.NP
import Opaque
{-
import Reflection.Decode
import Reflection.Decoding
import Reflection.Printer
import Reflection.Scoped
import Reflection.Scoped.Param
import Reflection.Scoped.Translation
import Reflection.Simple
-}
import Relation.Binary.Bijection
import Relation.Binary.Equivalence
import Relation.Binary.Logical
import Relation.Binary.Logical.Iso
import Relation.Binary.Logical.LEM
import Relation.Binary.NP
import Relation.Binary.On.NP
import Relation.Binary.Permutation
import Relation.Binary.PropositionalEquality.K
import Relation.Binary.PropositionalEquality.NP
import Relation.Binary.Sum.NP
import Relation.Binary.ToNat
import Relation.Nullary.NP
import Relation.Unary.Logical
import Relation.Unary.NP
import Text.Parser
import Text.Parser.Partial
import Text.Printer
import Text.Show
import Type
import Type.Identities
import Universe.NP
