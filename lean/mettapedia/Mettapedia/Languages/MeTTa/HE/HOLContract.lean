import Mettapedia.Languages.MeTTa.HE.HOLContract.Signature
import Mettapedia.Languages.MeTTa.HE.HOLContract.Products
import Mettapedia.Languages.MeTTa.HE.HOLContract.Agreement
import Mettapedia.Languages.MeTTa.HE.HOLContract.Curried
import Mettapedia.Languages.MeTTa.HE.HOLContract.Gradual
import Mettapedia.Languages.MeTTa.HE.HOLContract.Dependent
import Mettapedia.Languages.MeTTa.HE.HOLContract.DependentChecker
import Mettapedia.Languages.MeTTa.HE.HOLContract.Runtime
import Mettapedia.Languages.MeTTa.HE.HOLContract.Principal
import Mettapedia.Languages.MeTTa.HE.HOLContract.PrincipalNative
import Mettapedia.Languages.MeTTa.HE.HOLContract.PrincipalReuse
import Mettapedia.Languages.MeTTa.HE.TypeGrounding.MetaTypes

/-!
# The HOL contract of HE type declarations

HE's type declarations mean a theory of Church-style higher-order logic, the contract, which
depends on no implementation of MeTTa's types.  The contract is HE's theory of first-order
prenex schemes hosted in HOL: every HE type is a base type, an arrow of n parameters is applied
by its own application constant, and every declaration is its own constant.

* `Signature`: the contract's types, its constants (each declaration at its instances, the
  application constants, and the pairing, projections and unit of products), its terms, contract
  typing, and HE's first-order rule, which contract typing is (`typed_iff_firstOrder`).
* `Products`: in every model of the contract the compound types are products; the projection
  and surjective-pairing laws are theorems, and models with genuine products exist over any
  interpretation of the declared and application constants.
* `Agreement`: on HE's static, tuple and first-order schematic fragments, HE's typing is
  contract typing.
* `Curried`: the curried view of HE's arrows as HOL function types, which agrees with the
  contract on saturated terms and parts from it on the separating judgments.
* `Gradual`: `%Undefined%` read beside the contract, through concretization.
* `Dependent`: the boundary on the other side.  A telescope `(-> (: $x A) B)` read dependently
  types terms by their arguments, and no declaration-invariant relation agrees with that
  reading: neither the contract nor any compositional contract whose leaves are typed by their
  declarations.
  `DependentChecker` computes that reading as the dependent route does, substituting the
  arguments for the binders and comparing each argument's type with its binder's, and proves
  the computation decides it: its answer is the only type, and no answer means no type.
* `Runtime`: what the contract licenses a runtime to do instead of checking every call: keep
  judgments per declaration revision, with the subtype declarations in the key of a cache of
  HE's answers; answer from a native checker that decides the contract; omit the argument
  checks of a statically typed call whose result type is determined by its arguments; and cache
  one answer per derivation.
* `Principal`: a computable native checker.  First-order unification over type terms computes
  the principal type of each way of typing an expression, overloads included, and decides the
  contract with them.  `PrincipalNative` proves it an admitted native checker of `Runtime`,
  with one answer per way of typing, and with the instances of HE's candidate where that
  answers.  `PrincipalReuse` makes its answer a read-certified query that reads only
  declarations, so recorded answers are reused exactly and no equation invalidates them.
* `TypeGrounding.MetaTypes`: the meta-types as the classification theory of atoms.

Two bridges sit outside this family, so that the contract depends on neither:
`HOLContract.Guest` relates contract typing to the hosted HOL Light checker and its model, and
`HOLContract.Backend` admits replaceable backends.
-/
