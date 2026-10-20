import Mettapedia.GSLT.LanguageDef.IndexedInductiveVectorArray
import Mettapedia.OSLF.NativeTypes.Decision.Spatial.BagCardinality
import Mettapedia.OSLF.NativeTypes.Decision.Spatial.Execution
import Mettapedia.OSLF.NativeTypes.Instances.SpatialBag
import Mettapedia.OSLF.NativeTypes.Executable

/-!
# Native length observations of authored vector append

The public shared checker asks a derived spatial cardinality formula about
the completed vector's elements. The comparison starts from the original
polynomial vectors and the independent array realization. Forgetting order
is appropriate for this length observation only; it does not replace the
separate complete ordered-payload contract.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Consumers.IndexedAppend

open Mettapedia.GSLT.LanguageDef IndexedInductive IndexedInductiveNatVec
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Decision.Spatial
open Mettapedia.OSLF.NativeTypes.Decision.Admission
open Instances

def arrayBag {A : Type} (payload : A → Pattern) (values : Array A) : List Pattern :=
  values.toList.map payload

noncomputable def sourceBag {A : Type} (payload : A → Pattern) {length : Natural.Carrier}
    (values : Vectors.Vector A length) : List Pattern :=
  (Vectors.toList values).val.map payload

theorem array_length_iff {A : Type} (payload : A → Pattern) (values : Array A) (count : Nat) :
    BagModel.holds (BagModel.sizeExactly count) (arrayBag payload values) ↔ values.size = count := by
  simp only [BagModel.sizeExactly_iff, arrayBag, List.length_map, Array.length_toList]

theorem source_length_iff {A : Type} (payload : A → Pattern) {length : Natural.Carrier}
    (values : Vectors.Vector A length) (count : Nat) :
    BagModel.holds (BagModel.sizeExactly count) (sourceBag payload values) ↔
      Natural.toNat length = count := by
  rw [BagModel.sizeExactly_iff]
  simp only [sourceBag, List.length_map, (Vectors.toList values).property]

theorem representation_observation {A : Type} (payload : A → Pattern) {length : Natural.Carrier}
    (values : Vectors.Vector A length) : arrayBag payload (VectorArray.encode values).val =
      sourceBag payload values := by
  rfl

theorem append_source_length_iff {A : Type} (payload : A → Pattern) {n m : Natural.Carrier}
    (left : Vectors.Vector A n) (right : Vectors.Vector A m) (count : Nat) :
    BagModel.holds (BagModel.sizeExactly count) (sourceBag payload (Vectors.append left right)) ↔
      Natural.toNat n + Natural.toNat m = count := by
  rw [source_length_iff, Natural.toNat_add]

theorem atLeastSize_formed (count : Nat) :
    Formed SpatialBag.driver.generated.logicFragment SpatialBag.driver.leafAdmission
      (BagModel.atLeastSize count) := by
  induction count with
  | zero => exact .top rfl
  | succ count ih => exact .separating rfl rfl (.neg rfl (.atom BagModel.Leaf.emp trivial)) ih

theorem sizeExactly_formed (count : Nat) :
    Formed SpatialBag.driver.generated.logicFragment SpatialBag.driver.leafAdmission
      (BagModel.sizeExactly count) :=
  .conj rfl (atLeastSize_formed count) (.neg rfl (atLeastSize_formed (count + 1)))

theorem atLeastSize_admitted (count : Nat) : Execution.admitted (BagModel.atLeastSize count) = true := by
  induction count with
  | zero => rfl
  | succ count ih => simpa [BagModel.atLeastSize, BagModel.nonempty, Execution.admitted] using ih

theorem sizeExactly_admitted (count : Nat) : Execution.admitted (BagModel.sizeExactly count) = true := by
  simp [BagModel.sizeExactly, Execution.admitted, atLeastSize_admitted]

def check (count : Nat) (items : List Pattern) (budget : Nat) :=
  Executable.search SpatialBag.installed (BagModel.sizeExactly count) (BagModel.encode items) budget

theorem public_meaning (count : Nat) (items : List Pattern) :
    Runtime.Description.Meaning SpatialBag.driver (BagModel.sizeExactly count) (BagModel.encode items) ↔
      items.length = count :=
  (SpatialBag.meaning_at_bag _ _).trans (BagModel.sizeExactly_iff count items)

theorem positive (count : Nat) (items : List Pattern) (budget : Nat)
    (accepted : (check count items budget).readout = .judgment (.decided true)) :
    items.length = count := (public_meaning count items).mp (Runtime.positive _ accepted)

theorem negative (count : Nat) (items : List Pattern) (budget : Nat)
    (refuted : (check count items budget).readout = .judgment (.decided false)) :
    items.length ≠ count := fun correct =>
  Runtime.negative _ refuted ((public_meaning count items).mpr correct)

def decoded (items : List Pattern) : SpatialBag.driver.Decoded (BagModel.encode items) :=
  ⟨items, trivial, rfl⟩

theorem complete (count : Nat) (items : List Pattern) (budget : Nat)
    (enough : Runtime.decisionBound SpatialBag.driver SpatialBag.engine
      (BagModel.sizeExactly count) (decoded items) ≤ budget) :
    ∃ answer, (check count items budget).readout = .judgment (.decided answer) :=
  Runtime.check_complete SpatialBag.driver SpatialBag.engine (BagModel.sizeExactly count)
    (decoded items) (sizeExactly_formed count) SpatialBag.admitted_profile budget enough

theorem check_iff (count : Nat) (items : List Pattern) (budget : Nat)
    (enough : Runtime.decisionBound SpatialBag.driver SpatialBag.engine
      (BagModel.sizeExactly count) (decoded items) ≤ budget) :
    (check count items budget).readout = .judgment (.decided true) ↔ items.length = count := by
  constructor
  · exact positive count items budget
  · intro correct
    obtain ⟨answer, concluded⟩ := complete count items budget enough
    cases answer with
    | false => exact False.elim (negative count items budget concluded correct)
    | true => exact concluded

theorem check_resume (count : Nat) (items : List Pattern) (first more : Nat) :
    check count items (first + more) = Executable.resume more (check count items first) :=
  Runtime.search_resume SpatialBag.driver SpatialBag.engine (BagModel.sizeExactly count)
    (BagModel.encode items) first more

theorem array_append_positive {A : Type} (payload : A → Pattern) (left right : Array A)
    (count budget : Nat)
    (accepted : (check count (arrayBag payload (left ++ right)) budget).readout =
      .judgment (.decided true)) : left.size + right.size = count := by
  have correct := positive count _ budget accepted
  simpa only [arrayBag, List.length_map, Array.length_toList, Array.size_append] using correct

#print axioms check_iff
#print axioms append_source_length_iff

end Mettapedia.OSLF.NativeTypes.Consumers.IndexedAppend
