import Mettapedia.TypeTheory.IndexedPolynomialDataRepresentation
import Mettapedia.TypeTheory.IndexedPolynomialRecursiveSpacePredicate

/-!
# Constructor-data forms of indexed predicate guards

First-order inventories compute tags, active-slot bounds and recursive child
indices directly from their environment-independent data tuples. The equations
below identify these computations with the shape-based guards, retaining the
original telescope evaluation. No native source representation is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial.Description.DataRepresentation

open IndexedPolynomial.RecursiveSpaceRepresentation
universe u
variable {I : Interface.{u}} {context : List I.SortCode}
variable (constructors : List (NamedConstructor I context))

def dataShapeGuard (tag : Nat) (payload : Payload constructors) : Prop :=
  match payload with
  | none => False
  | some data => tag = data.1.val

def dataActiveGuard (payload : Payload constructors) (slot : Nat) : Prop :=
  match payload with
  | none => False
  | some data => slot < recursiveCount (constructors.get data.1).body

def dataChildIndex (environment : Env I.Value context)
    (payload : Payload constructors) (slot : Nat) : Option I.Index :=
  match payload with
  | none => none
  | some data =>
      if inside : slot < recursiveCount (constructors.get data.1).body then
        some (dataRecursiveIndexAt (constructors.get data.1).body environment data.2 ⟨slot, inside⟩)
      else none

theorem shapeGuard_data (environment : Env I.Value context) (tag : Nat)
    (payload : RecursivePayload (recursiveSpacePresentation constructors) environment) :
    shapeGuard (recursiveSpacePresentation constructors) tag payload ↔
      dataShapeGuard constructors tag (payloadEquivalence constructors environment payload) := by
  cases payload with
  | none => rfl
  | some point => rfl

theorem activeGuard_data (environment : Env I.Value context)
    (payload : RecursivePayload (recursiveSpacePresentation constructors) environment)
    (slot : Nat) :
    activeGuard (recursiveSpacePresentation constructors) payload slot ↔
      dataActiveGuard constructors (payloadEquivalence constructors environment payload) slot := by
  cases payload with
  | none => rfl
  | some point =>
      change (∃ position, (SlotEncoding.finite
        (positionEquivFin (constructors.get point.2.1).body point.2.2)).decode slot = some position) ↔
          slot < recursiveCount (constructors.get point.2.1).body
      simp only [SlotEncoding.finite]
      split
      · rename_i inside
        exact ⟨fun _ => inside, fun _ => ⟨_, rfl⟩⟩
      · rename_i outside
        constructor
        · rintro ⟨_, impossible⟩
          cases impossible
        · intro inside
          exact False.elim (outside inside)

theorem dataChildIndex_none_iff (environment : Env I.Value context)
    (payload : Payload constructors) (slot : Nat) :
    dataChildIndex constructors environment payload slot = none ↔
      ¬ dataActiveGuard constructors payload slot := by
  cases payload with
  | none => exact ⟨fun _ impossible => impossible.elim, fun _ => rfl⟩
  | some data =>
      change (if inside : slot < recursiveCount (constructors.get data.1).body then
        some (dataRecursiveIndexAt (constructors.get data.1).body environment data.2 ⟨slot, inside⟩)
        else none) = none ↔ ¬ slot < recursiveCount (constructors.get data.1).body
      simp

theorem dataChildIndex_at_position (environment : Env I.Value context)
    (point : Σ index, (inventoryPolynomial constructors).Shape environment index)
    (position : (inventoryPolynomial constructors).Position point.2) :
    dataChildIndex constructors environment
      (payloadEquivalence constructors environment (some point))
      (((recursiveSpacePresentation constructors).coding point.2).encode position) =
      some ((inventoryPolynomial constructors).next point.2 position) := by
  change (if inside : (positionToFin (constructors.get point.2.1).body point.2.2 position).val <
      recursiveCount (constructors.get point.2.1).body then
    some (dataRecursiveIndexAt (constructors.get point.2.1).body environment
      (dataFromShape (constructors.get point.2.1).body point.2.2)
      ⟨(positionToFin (constructors.get point.2.1).body point.2.2 position).val, inside⟩)
    else none) = _
  rw [dif_pos (positionToFin (constructors.get point.2.1).body point.2.2 position).isLt]
  exact congrArg some ((recursive_index_from_data (constructors.get point.2.1).body point.2.2 _).trans
    (recursiveIndexAt_toFin (constructors.get point.2.1).body point.2.2 position))

theorem dataChildIndex_decoded (environment : Env I.Value context)
    (point : Σ index, (inventoryPolynomial constructors).Shape environment index)
    (slot : Nat) (position : (inventoryPolynomial constructors).Position point.2)
    (decoded : ((recursiveSpacePresentation constructors).coding point.2).decode slot = some position) :
    dataChildIndex constructors environment
      (payloadEquivalence constructors environment (some point)) slot =
      some ((inventoryPolynomial constructors).next point.2 position) := by
  rw [← ((recursiveSpacePresentation constructors).coding point.2).encode_decode slot position decoded]
  exact dataChildIndex_at_position constructors environment point position

theorem edgeGuard_data (environment : Env I.Value context)
    (payload : RecursivePayload (recursiveSpacePresentation constructors) environment)
    (slot : Nat)
    (child : Mettapedia.TypeTheory.RecursiveSpace.Tree
      (RecursivePayload (recursiveSpacePresentation constructors) environment)) :
    edgeGuard (recursiveSpacePresentation constructors) payload slot child ↔
      ∃ index, dataChildIndex constructors environment
        (payloadEquivalence constructors environment payload) slot = some index ∧
        HasRootIndex (recursiveSpacePresentation constructors) child index := by
  cases payload with
  | none =>
      change False ↔ ∃ index, (none : Option I.Index) = some index ∧ _
      simp only [reduceCtorEq, false_and, exists_false]
  | some point =>
      constructor
      · rintro ⟨position, decoded, root⟩
        exact ⟨_, dataChildIndex_decoded constructors environment point slot position decoded, root⟩
      · rintro ⟨index, present, root⟩
        have active : dataActiveGuard constructors
            (payloadEquivalence constructors environment (some point)) slot := by
          by_contra inactive
          have absent := (dataChildIndex_none_iff constructors environment _ slot).mpr inactive
          rw [absent] at present
          cases present
        obtain ⟨position, decoded⟩ := (activeGuard_data constructors environment (some point) slot).mpr active
        have same := Option.some.inj
          ((dataChildIndex_decoded constructors environment point slot position decoded).symm.trans present)
        exact ⟨position, decoded, same.symm ▸ root⟩

#print axioms shapeGuard_data
#print axioms activeGuard_data
#print axioms dataChildIndex_decoded
#print axioms edgeGuard_data

end Mettapedia.TypeTheory.IndexedPolynomial.Description.DataRepresentation
