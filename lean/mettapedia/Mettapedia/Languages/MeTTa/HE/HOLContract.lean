import Mettapedia.Languages.MeTTa.HE.HOLContract.Signature
import Mettapedia.Languages.MeTTa.HE.HOLContract.Products
import Mettapedia.Languages.MeTTa.HE.HOLContract.Agreement
import Mettapedia.Languages.MeTTa.HE.HOLContract.Gradual
import Mettapedia.Languages.MeTTa.HE.TypeGrounding.MetaTypes

/-!
# The HOL contract of HE type declarations

HE's type declarations mean a theory of Church-style higher-order logic, the
contract, which depends on no implementation of MeTTa's types.

* `Signature`: the contract's types (the HOL reading of HE types, faithful on
  the contract types), its constants (declared constants at instances, and the
  pairing, projections and unit of products), its terms, and contract typing.
* `Products`: in every model of the contract the compound non-arrow types are
  products; the projection and surjective-pairing laws are theorems, and
  models with genuine products exist over any interpretation of the
  declarations.
* `Agreement`: on HE's static, tuple and first-order schematic fragments, HE's
  typing is contract typing.
* `Gradual`: `%Undefined%` read beside the contract, through concretization.
* `TypeGrounding.MetaTypes`: the meta-types as the classification theory of
  atoms.

Two bridges sit outside this family, so that the contract depends on neither:
`HOLContract.Guest` relates contract typing to the hosted HOL Light checker
and its model, and `HOLContract.Backend` admits replaceable backends.
-/
