import Mettapedia.Logic.HOL.VectorContainerPositionPrograms
import Mettapedia.Logic.HOL.OrderedPositionPrograms
import Mettapedia.TypeTheory.IndexedPositiveContainerPositions
import Mettapedia.Logic.HOL.SuccessorOrder
import Mettapedia.TypeTheory.IndexedPositiveContainerRecursiveSpace

/-!
# Position guards for the registered indexed Vector container

The generated program uses successor-closure order. Its relation agrees with
the actual registered code's selected natural-slot decoder and child index.
Lengths zero, two and three distinguish an empty position fibre and a boundary
that moves with constructor data. The Boolean false index is refused.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorContainerPositionControls
open Mettapedia.Logic.HOL
open Mettapedia.TypeTheory
open IndexedPositiveContainer
open IndexedConstructorGuards FiniteConstructorEncoding

abbrev number : Ty Unit := .base ()
inductive Symbol : Ty Unit → Type where
  | zero : Symbol number
  | successor : Symbol (number ⇒ number)

def model : HenkinModel.{0,0,0} Unit Symbol :=
  .standard (fun _ => ULift.{1} Nat) (fun symbol => match symbol with
    | .zero => .up 0
    | .successor => fun n => .up (n.down + 1))
def values : model.Valuation [] := fun impossible => nomatch impossible
theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _
def successor : ClosedTerm Symbol (number ⇒ number) := .const .successor
def numeral : Nat → ClosedTerm Symbol number
  | 0 => .const .zero
  | n + 1 => .app successor (numeral n)

def constructors := VectorContainerPositionPrograms.constructors number numeral
def positions := VectorContainerPositionPrograms.positions number numeral (SuccessorOrder.less successor)
def data (length : Nat) : constructors.Data model := ⟨⟨0, by decide⟩, ULift.up length, PUnit.unit⟩
def packed (length : Nat) := constructors.packedData model (data length)

theorem relation_iff (length slot : Nat) (index : Ty.denote model.Carrier Ty.prop) :
    positions.related model values (data length) (ULift.up slot) index ↔
      slot < length ∧ index = ULift.up True := by
  have order := SuccessorOrder.less_iff model full successor values Equiv.ulift.symm
    (fun _ => rfl) (ULift.up slot) (ULift.up length)
  exact (VectorContainerPositionPrograms.related_iff model full number numeral
    (SuccessorOrder.less successor) values (ULift.up length) (ULift.up slot) index).trans
      (and_congr order Iff.rfl)

theorem allowed (length : Nat) : constructors.dataAllowed model values (data length) := True.intro

theorem active_iff (length slot : Nat) :
    (model.denote positions.activeProgram values (packed length) (ULift.up slot)).down ↔ slot < length := by
  rw [positions.activeProgram_denote model full]
  constructor
  · rintro ⟨other, ⟨_, index, relation⟩, agrees⟩
    have same : data length = other :=
      TypeTheory.FiniteConstructorEncoding.encode_injective _ _
        (((payloadEquivalence model constructors.fields).apply_symm_apply _).symm.trans agrees)
    cases same
    exact ((relation_iff length slot index).mp relation).1
  · intro inside
    exact ⟨data length, ⟨allowed length, ULift.up True, (relation_iff length slot _).mpr ⟨inside, rfl⟩⟩,
      (payloadEquivalence model constructors.fields).apply_symm_apply _⟩

theorem child_iff (length slot : Nat) (index : Ty.denote model.Carrier Ty.prop) :
    (model.denote positions.childProgram values (packed length) (ULift.up slot) index).down ↔
      slot < length ∧ index = ULift.up True := by
  rw [positions.childProgram_denote model full]
  constructor
  · rintro ⟨other, ⟨_, relation⟩, agrees⟩
    have same : data length = other :=
      TypeTheory.FiniteConstructorEncoding.encode_injective _ _
        (((payloadEquivalence model constructors.fields).apply_symm_apply _).symm.trans agrees)
    cases same
    exact (relation_iff length slot index).mp relation
  · intro valid
    exact ⟨data length, ⟨allowed length, (relation_iff length slot index).mpr valid⟩,
      (payloadEquivalence model constructors.fields).apply_symm_apply _⟩

noncomputable def sourcePresentation :=
  IndexedPositiveContainer.RecursiveSpaceRepresentation.codePresentation VectorControl.orderedFinitary VectorControl.code

def indexValue (_index : Unit) : Ty.denote.{0,0} model.Carrier Ty.prop := ULift.up True

theorem source_position_exact (length slot : Nat) (index : Ty.denote model.Carrier Ty.prop) :
    (model.denote positions.childProgram values (packed length) (ULift.up slot) index).down ↔
      ∃ position, (sourcePresentation.coding (VectorControl.shapeAt length)).decode slot = some position ∧
        index = indexValue (Code.next VectorControl.code (VectorControl.shapeAt length) position) := by
  rw [child_iff]
  constructor
  · rintro ⟨inside, same⟩
    obtain ⟨position, decoded⟩ := (IndexedPositiveContainer.RecursiveSpaceRepresentation.vector_active_iff length slot).mpr inside
    exact ⟨position, decoded, same⟩
  · rintro ⟨position, decoded, same⟩
    exact ⟨(IndexedPositiveContainer.RecursiveSpaceRepresentation.vector_active_iff length slot).mp ⟨position, decoded⟩, same⟩

theorem original_position_preserved (length : Nat)
    (position : Code.Position VectorControl.code (VectorControl.shapeAt length)) :
    (model.denote positions.childProgram values (packed length)
      (ULift.up ((sourcePresentation.coding (VectorControl.shapeAt length)).encode position))
      (indexValue (Code.next VectorControl.code (VectorControl.shapeAt length) position))).down := by
  apply (source_position_exact length _ _).mpr
  exact ⟨position, (sourcePresentation.coding (VectorControl.shapeAt length)).decode_encode position, rfl⟩

noncomputable def secondPosition : Code.Position VectorControl.code (VectorControl.shapeAt 2) :=
  Code.orderedPositionEquiv VectorControl.orderedFinitary VectorControl.code (VectorControl.shapeAt 2)
    ⟨1, by rw [IndexedPositiveContainer.RecursiveSpaceRepresentation.vector_ordered_length]; decide⟩

theorem original_second_position :
    (model.denote positions.childProgram values (packed 2) (ULift.up 1) (ULift.up True)).down := by
  have kept := original_position_preserved 2 secondPosition
  have slot := IndexedPositiveContainer.RecursiveSpaceRepresentation.code_position_order
    VectorControl.orderedFinitary VectorControl.code (VectorControl.shapeAt 2)
    ⟨1, by rw [IndexedPositiveContainer.RecursiveSpaceRepresentation.vector_ordered_length]; decide⟩
  change (sourcePresentation.coding (VectorControl.shapeAt 2)).encode secondPosition = 1 at slot
  rw [slot] at kept
  exact kept

theorem two_accepts_one : (model.denote positions.activeProgram values (packed 2) (ULift.up 1)).down :=
  (active_iff 2 1).mpr (by decide)
theorem two_refuses_two : ¬ (model.denote positions.activeProgram values (packed 2) (ULift.up 2)).down :=
  fun valid => Nat.lt_irrefl 2 ((active_iff 2 2).mp valid)
theorem three_accepts_two : (model.denote positions.activeProgram values (packed 3) (ULift.up 2)).down :=
  (active_iff 3 2).mpr (by decide)
theorem zero_refuses_all (slot : Nat) : ¬ (model.denote positions.activeProgram values (packed 0) (ULift.up slot)).down :=
  fun valid => Nat.not_lt_zero slot ((active_iff 0 slot).mp valid)
theorem wrong_index_refused :
    ¬ (model.denote positions.childProgram values (packed 2) (ULift.up 1) (ULift.up False)).down := by
  intro valid
  have same := ((child_iff 2 1 _).mp valid).2
  exact (congrArg ULift.down same).mpr True.intro

namespace Ordered
open OrderedPositionPrograms

def plans (occurrence : Fin constructors.fields.length) :
    FieldPlan Symbol [] (constructors.fields.get occurrence) number .prop :=
  Fin.cases [(.lam (.var .vz), .lam .top)] (fun impossible => Fin.elim0 impossible) occurrence

def compiled := PositionPrograms.ofSegments constructors (.const .zero) successor plans

theorem relation_exact (length slot : Nat) (index : Ty.denote.{0,0} model.Carrier .prop) :
    compiled.related model values (data length) (ULift.up slot) index ↔
      slot < length ∧ index = ULift.up True := by
  have law := PositionPrograms.ofSegments_related constructors (.const .zero) successor plans
    model Equiv.ulift.symm full values rfl (fun _ => rfl) values (data length) (ULift.up slot) index
  apply law.trans
  change (Mettapedia.TypeTheory.OrderedPositionSegments.flatten [(length, ULift.up True)])[slot]? = some index ↔ _
  by_cases inside : slot < length <;>
    simp [Mettapedia.TypeTheory.OrderedPositionSegments.flatten, inside, eq_comm]

theorem source_position_exact (length slot : Nat) (index : Ty.denote.{0,0} model.Carrier .prop) :
    compiled.related model values (data length) (ULift.up slot) index ↔
      ∃ position, (sourcePresentation.coding (VectorControl.shapeAt length)).decode slot = some position ∧
        index = indexValue (Code.next VectorControl.code (VectorControl.shapeAt length) position) :=
  (relation_exact length slot index).trans ((child_iff length slot index).symm.trans
    (IndexedVectorContainerPositionControls.source_position_exact length slot index))

theorem source_segment_length (length : Nat) :
    (Mettapedia.TypeTheory.OrderedPositionSegments.flatten
      (Code.positionSegments VectorControl.orderedFinitary VectorControl.code (VectorControl.shapeAt length))).length = length := by
  rw [Code.flatten_positionSegments, List.length_map,
    IndexedPositiveContainer.RecursiveSpaceRepresentation.vector_ordered_length]

theorem source_segment_lookup (length slot : Nat) :
    (Mettapedia.TypeTheory.OrderedPositionSegments.flatten
      (Code.positionSegments VectorControl.orderedFinitary VectorControl.code (VectorControl.shapeAt length)))[slot]? =
        some () ↔ slot < length := by
  rw [Code.lookup_positionSegments]
  constructor
  · rintro ⟨position, decoded, _⟩
    exact (IndexedPositiveContainer.RecursiveSpaceRepresentation.vector_active_iff length slot).mp ⟨position, decoded⟩
  · intro inside
    obtain ⟨position, decoded⟩ :=
      (IndexedPositiveContainer.RecursiveSpaceRepresentation.vector_active_iff length slot).mpr inside
    exact ⟨position, decoded, Subsingleton.elim (α := Unit) _ _⟩

def openPlan : Plan Symbol [number, number] number number :=
  [(.var (.vs .vz), .var .vz), (.var .vz, .var (.vs .vz))]

def close : Subst Symbol [number, number] []
  | _, .vz => numeral 1
  | _, .vs .vz => numeral 2
  | _, .vs (.vs impossible) => nomatch impossible

theorem closing_preserves_program :
    Mettapedia.Logic.HOL.subst close (graph (.const .zero) successor openPlan) =
      graph (.const .zero) successor [(numeral 2, numeral 1), (numeral 1, numeral 2)] :=
  graph_substitute (.const .zero) successor openPlan close

/-- Different child indices occur in an ordered constructor with a data-sized
middle segment. The zero-length segment contributes no child. -/
def mixedConstructors : ConstructorPrograms Symbol [] where
  fields := [[number]]
  number := number
  index := number
  numeral := numeral
  allowed := constructors.allowed
  result := fun occurrence => Fin.cases (.lam (weaken (numeral 0))) (fun impossible => Fin.elim0 impossible) occurrence

def mixedPlan : FieldPlan Symbol [] [number] number number :=
  [(.lam (weaken (numeral 1)), .lam (weaken (numeral 0))),
   (.lam (weaken (numeral 0)), .lam (weaken (numeral 3))),
   (.lam (.var .vz), .lam (weaken (numeral 1))),
   (.lam (weaken (numeral 1)), .lam (weaken (numeral 0)))]

def mixedPlans (occurrence : Fin mixedConstructors.fields.length) :
    FieldPlan Symbol [] (mixedConstructors.fields.get occurrence) number number :=
  Fin.cases mixedPlan (fun impossible => Fin.elim0 impossible) occurrence

def mixed := PositionPrograms.ofSegments mixedConstructors (.const .zero) successor mixedPlans

theorem mixed_exact (length slot : Nat) (index : Ty.denote.{0,0} model.Carrier number) :
    mixed.related model values (data length) (ULift.up slot) index ↔
      ([ULift.up 0] ++ List.replicate length (ULift.up 1) ++ [ULift.up 0])[slot]? = some index := by
  have law := PositionPrograms.ofSegments_related mixedConstructors (.const .zero) successor mixedPlans
    model Equiv.ulift.symm full values rfl (fun _ => rfl) values (data length) (ULift.up slot) index
  apply law.trans
  change (Mettapedia.TypeTheory.OrderedPositionSegments.flatten
    [(1, ULift.up 0), (0, ULift.up 3), (length, ULift.up 1), (1, ULift.up 0)])[slot]? = some index ↔ _
  simp [Mettapedia.TypeTheory.OrderedPositionSegments.flatten]

theorem first_position : mixed.related model values (data 2) (ULift.up 0) (ULift.up 0) :=
  (mixed_exact 2 0 _).mpr rfl

theorem middle_position : mixed.related model values (data 2) (ULift.up 2) (ULift.up 1) :=
  (mixed_exact 2 2 _).mpr rfl

theorem repeated_index_retains_position :
    mixed.related model values (data 2) (ULift.up 3) (ULift.up 0) :=
  (mixed_exact 2 3 _).mpr rfl

theorem empty_segment_creates_no_slot :
    ¬ mixed.related model values (data 2) (ULift.up 1) (ULift.up 3) := by
  intro present
  have impossible := (mixed_exact 2 1 _).mp present
  cases impossible

theorem wrong_offset_refused : ¬ mixed.related model values (data 2) (ULift.up 2) (ULift.up 0) := by
  intro present
  have impossible := (mixed_exact 2 2 _).mp present
  cases impossible

theorem outside_refused (index : Ty.denote.{0,0} model.Carrier number) :
    ¬ mixed.related model values (data 2) (ULift.up 4) index := by
  intro present
  have impossible := (mixed_exact 2 4 _).mp present
  cases impossible

#print axioms source_position_exact
#print axioms source_segment_length
#print axioms source_segment_lookup
#print axioms closing_preserves_program
#print axioms mixed_exact
#print axioms first_position
#print axioms repeated_index_retains_position
#print axioms wrong_offset_refused
#print axioms outside_refused
end Ordered

#print axioms source_position_exact
#print axioms original_position_preserved
#print axioms original_second_position
#print axioms two_accepts_one
#print axioms two_refuses_two
#print axioms three_accepts_two
#print axioms zero_refuses_all
#print axioms wrong_index_refused
end Mettapedia.GSLT.LanguageDef.IndexedVectorContainerPositionControls
