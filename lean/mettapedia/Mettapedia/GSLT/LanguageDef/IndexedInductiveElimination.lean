import Mettapedia.GSLT.LanguageDef.IndexedInductive
import Mettapedia.TypeTheory.IndexedPolynomialInduction

/-!
# Elimination for admitted constructor inventories

Constructor methods consume the original ordered telescope arguments. The
compiled polynomial implements these methods, and its fold computes exactly
the source method with every recursive child replaced by its recursive result.
Dependent elimination uses the existing displayed-algebra interface, with a
computation and uniqueness theorem quantified over all source constructors.
These semantic equations do not grant guest judgmental conversion authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.TypeTheory.IndexedPolynomial.Description

universe u v w

namespace Admitted

variable {I : Interface.{u}} {context : List I.SortCode}
variable (admitted : Admitted I context)

abbrev polynomial := inventoryPolynomial admitted.constructors

abbrev Family := Fix admitted.polynomial

/-- Construct a value using its authored occurrence and ordered arguments. -/
def construct {environment : Env I.Value context} {index : I.Index}
    (arguments : InventoryArguments admitted.constructors environment
      (admitted.Family environment) index) : admitted.Family environment index :=
  Fix.rollExtension admitted.polynomial (inventoryEncode admitted.constructors arguments)

/-- Methods indexed by the source inventory, not a second constructor list. -/
abbrev Methods (carrier : Env I.Value context → I.Index → Type v) :=
  ∀ environment index, InventoryArguments admitted.constructors environment
    (carrier environment) index → carrier environment index

def algebra {carrier : Env I.Value context → I.Index → Type v}
    (methods : admitted.Methods carrier) : Algebra admitted.polynomial carrier where
  act := fun environment index layer => methods environment index
    (inventoryDecode admitted.constructors layer)

noncomputable def fold {carrier : Env I.Value context → I.Index → Type v}
    (methods : admitted.Methods carrier) :
    ∀ environment index, admitted.Family environment index → carrier environment index :=
  Fix.fold admitted.polynomial (admitted.algebra methods).act

theorem fold_construct {carrier : Env I.Value context → I.Index → Type v}
    (methods : admitted.Methods carrier)
    {environment : Env I.Value context} {index : I.Index}
    (arguments : InventoryArguments admitted.constructors environment
      (admitted.Family environment) index) :
    admitted.fold methods environment index (admitted.construct arguments) =
      methods environment index
        (InventoryArguments.map admitted.constructors (admitted.fold methods environment) arguments) := by
  change (admitted.algebra methods).act environment index
    (Extension.map admitted.polynomial (fun _ index value =>
      admitted.fold methods environment index value)
      (inventoryEncode admitted.constructors arguments)) = _
  rw [← inventoryEncode_map]
  change methods environment index
    (inventoryDecode admitted.constructors
      (inventoryEncode admitted.constructors _)) = _
  rw [inventoryDecode_encode]

/-- The dependent eliminator is derived from initiality and the supplied
constructor methods. It is not another admission assumption. -/
noncomputable def eliminate
    {motive : ∀ environment index, admitted.Family environment index → Sort v}
    (methods : Algebra.Displayed (Algebra.initial admitted.polynomial) motive) :=
  methods.initialSection

theorem eliminate_construct
    {motive : ∀ environment index, admitted.Family environment index → Sort v}
    (methods : Algebra.Displayed (Algebra.initial admitted.polynomial) motive)
    {environment : Env I.Value context} {index : I.Index}
    (arguments : InventoryArguments admitted.constructors environment
      (admitted.Family environment) index) :
    (admitted.eliminate methods).toFun environment index (admitted.construct arguments) =
      methods.act environment index (inventoryEncode admitted.constructors arguments).1
        (inventoryEncode admitted.constructors arguments).2
        (fun position => (admitted.eliminate methods).toFun environment _
          ((inventoryEncode admitted.constructors arguments).2 position)) := by
  exact methods.initialSection_roll _ _ _ _

/-- Constructor coverage is sufficient for uniqueness: the equations must
hold at every authored occurrence and every well-indexed argument tuple. -/
theorem eliminate_unique
    {motive : ∀ environment index, admitted.Family environment index → Sort v}
    (methods : Algebra.Displayed (Algebra.initial admitted.polynomial) motive)
    (candidate : ∀ environment index value, motive environment index value)
    (computes : ∀ environment index
      (arguments : InventoryArguments admitted.constructors environment
        (admitted.Family environment) index),
      candidate environment index (admitted.construct arguments) =
        methods.act environment index (inventoryEncode admitted.constructors arguments).1
          (inventoryEncode admitted.constructors arguments).2
          (fun position => candidate environment _
            ((inventoryEncode admitted.constructors arguments).2 position)))
    (environment : Env I.Value context) (index : I.Index)
    (value : admitted.Family environment index) :
    candidate environment index value = (admitted.eliminate methods).toFun environment index value := by
  apply methods.initialSection_unique ⟨candidate, ?_⟩ environment index value
  intro environment index shape children
  have computed := computes environment index
    (inventoryDecode admitted.constructors ⟨shape, children⟩)
  have same := inventoryEncode_decode admitted.constructors
    (family := admitted.Family environment) (environment := environment)
    (index := index) ⟨shape, children⟩
  unfold construct at computed
  rw [same] at computed
  exact computed

end Admitted
end Mettapedia.GSLT.LanguageDef.IndexedInductive
