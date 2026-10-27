import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTermControls
import Mettapedia.Logic.HOL.IndexedConstructorGuardCompilation
import Mettapedia.Logic.HOL.FixedConstructorPositionPrograms

/-!
# Guards generated from the admitted Vector constructors

The controls use the original Vector description and natural arithmetic
interpretation. The element field is interpreted as Boolean truth. A cons
payload at length one has result index two, child index one and exactly slot
zero. Its constructor tag is distinct from nil's; nil has no active slot.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductiveGuardControls

open Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open IndexedInductiveNatVec IndexedInductiveHOLTerms
open IndexedInductiveHOLTerms.Controls (Symbol number model empty)
open FiniteConstructorEncoding

def arithmetic : Arithmetic Symbol :=
  ⟨number, .prop, .const .zero, .const .successor, .const .addition⟩

def numeral : Nat → ClosedTerm Symbol number
  | 0 => arithmetic.zero
  | n + 1 => .app arithmetic.successor (numeral n)

noncomputable def inventory : IndexedConstructorGuards.Inventory Symbol [] :=
  IndexedConstructorGuardCompilation.inventory (arithmetic.reading Bool) (Vectors.constructors Bool)
    number numeral (fun _ => CurriedPredicates.constant _ .top)

def nilOccurrence : Fin inventory.fields.length := ⟨0, by change 0 < 2; decide⟩
def consOccurrence : Fin inventory.fields.length := ⟨1, by change 1 < 2; decide⟩

def fields : FiniteConstructorEncoding.Arguments Symbol [] (inventory.fields.get consOccurrence) :=
  (numeral 1, .top, PUnit.unit)

def nilFields : FiniteConstructorEncoding.Arguments Symbol [] (inventory.fields.get nilOccurrence) :=
  PUnit.unit

noncomputable def consPayload : ClosedTerm Symbol (payloadType inventory.fields) :=
  encode inventory.fields consOccurrence fields

noncomputable def nilPayload : ClosedTerm Symbol (payloadType inventory.fields) :=
  encode inventory.fields nilOccurrence nilFields

theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _

theorem all_data_allowed (data : inventory.toConstructorPrograms.Data model) : inventory.toConstructorPrograms.dataAllowed model empty data := by
  change CurriedPredicates.holds model _ (CurriedPredicates.constant _ .top) empty data.2
  exact (CurriedPredicates.constant_holds model _ .top empty data.2).mpr True.intro

noncomputable def nilTagProof : ProofSyntax Symbol [] (inventory.toConstructorPrograms.shapeGuard (numeral 0) nilPayload) :=
  ConstructorDataPredicates.introduce inventory.fields (inventory.toConstructorPrograms.shapeCondition (numeral 0))
    nilOccurrence nilFields (.andI .topI (.eqRefl (numeral 0)))

theorem nilTagProof_free : nilTagProof.FunctionExtensionalityFree :=
  ConstructorDataPredicates.introduce_free _ _ _ _ _ ⟨True.intro, True.intro⟩

theorem result_program : inventory.result consOccurrence = arithmetic.resultProgram Bool := by
  rfl

theorem child_program : inventory.child consOccurrence ⟨0, by change 0 < 1; decide⟩ =
    arithmetic.childProgram Bool := by
  rfl

theorem result_value : inventory.toConstructorPrograms.resultValue model empty
    ⟨consOccurrence, denoteArguments model _ fields empty⟩ = model.denote (numeral 2) empty := by
  unfold IndexedConstructorGuards.ConstructorPrograms.resultValue
  rw [result_program, Arithmetic.resultProgram_body]
  rfl

theorem child_value : inventory.childValue model empty
    ⟨consOccurrence, denoteArguments model _ fields empty⟩ ⟨0, by change 0 < 1; decide⟩ =
      model.denote (numeral 1) empty := by
  unfold IndexedConstructorGuards.Inventory.childValue
  rw [child_program, Arithmetic.childProgram_body]
  rfl

theorem cons_tag : (model.denote (inventory.toConstructorPrograms.shapeGuard (numeral 1) consPayload) empty).down := by
  apply (ConstructorDataPredicates.guard_on_encoded model full inventory.fields
    (inventory.toConstructorPrograms.shapeCondition (numeral 1)) consOccurrence fields empty).mpr
  apply (inventory.toConstructorPrograms.shapeCondition_holds model full (numeral 1) empty _).mpr
  exact ⟨all_data_allowed _, rfl⟩

theorem nil_tag_refused : ¬ (model.denote (inventory.toConstructorPrograms.shapeGuard (numeral 0) consPayload) empty).down := by
  intro valid
  have observed := (ConstructorDataPredicates.guard_on_encoded model full inventory.fields
    (inventory.toConstructorPrograms.shapeCondition (numeral 0)) consOccurrence fields empty).mp valid
  have same := ((inventory.toConstructorPrograms.shapeCondition_holds model full (numeral 0) empty _).mp observed).2
  have impossible := congrArg (fun value => Natural.toNat value.down) same
  change (0 : Nat) = 1 at impossible
  cases impossible

theorem result_two : (model.denote (inventory.toConstructorPrograms.resultGuard consPayload (numeral 2)) empty).down := by
  apply (ConstructorDataPredicates.guard_on_encoded model full inventory.fields
    (inventory.toConstructorPrograms.resultCondition (numeral 2)) consOccurrence fields empty).mpr
  apply (inventory.toConstructorPrograms.resultCondition_holds model full (numeral 2) empty _).mpr
  exact ⟨all_data_allowed _, result_value⟩

theorem child_zero_one :
    (model.denote (inventory.childGuard consPayload (numeral 0) (numeral 1)) empty).down := by
  apply (ConstructorDataPredicates.guard_on_encoded model full inventory.fields
    (inventory.childCondition (numeral 0) (numeral 1)) consOccurrence fields empty).mpr
  apply (inventory.childCondition_holds model full (numeral 0) (numeral 1) empty _).mpr
  exact ⟨all_data_allowed _, ⟨0, by change 0 < 1; decide⟩, rfl, child_value⟩

theorem result_cannot_be_child :
    ¬ (model.denote (inventory.childGuard consPayload (numeral 0) (numeral 2)) empty).down := by
  intro valid
  have observed := (ConstructorDataPredicates.guard_on_encoded model full inventory.fields
    (inventory.childCondition (numeral 0) (numeral 2)) consOccurrence fields empty).mp valid
  obtain ⟨_, position, _, same⟩ :=
    (inventory.childCondition_holds model full (numeral 0) (numeral 2) empty _).mp observed
  have position_zero : position = ⟨0, by change 0 < 1; decide⟩ := by
    apply Fin.ext
    change position.val = 0
    have bound := position.isLt
    change position.val < 1 at bound
    omega
  subst position
  rw [child_value] at same
  have impossible := congrArg (fun value => Natural.toNat value.down) same
  change (1 : Nat) = 2 at impossible
  cases impossible

theorem cons_has_slot_zero : (model.denote (inventory.activeGuard consPayload (numeral 0)) empty).down := by
  apply (ConstructorDataPredicates.guard_on_encoded model full inventory.fields
    (inventory.activeCondition (numeral 0)) consOccurrence fields empty).mpr
  apply (inventory.activeCondition_holds model full (numeral 0) empty _).mpr
  exact ⟨all_data_allowed _, ⟨0, by change 0 < 1; decide⟩, rfl⟩

theorem position_adapter_active :
    (model.denote (inventory.toPositionPrograms.activeGuard consPayload (numeral 0)) empty).down :=
  (inventory.active_agreement model full consPayload (numeral 0) empty).mpr cons_has_slot_zero

theorem position_adapter_child :
    (model.denote (inventory.toPositionPrograms.childGuard consPayload (numeral 0) (numeral 1)) empty).down :=
  (inventory.child_agreement model full consPayload (numeral 0) (numeral 1) empty).mpr child_zero_one

theorem position_adapter_refuses_result_index :
    ¬ (model.denote (inventory.toPositionPrograms.childGuard consPayload (numeral 0) (numeral 2)) empty).down :=
  fun accepted => result_cannot_be_child
    ((inventory.child_agreement model full consPayload (numeral 0) (numeral 2) empty).mp accepted)

theorem nil_has_no_active_slot (slot : ClosedTerm Symbol number) :
    ¬ (model.denote (inventory.activeGuard nilPayload slot) empty).down := by
  intro valid
  have observed := (ConstructorDataPredicates.guard_on_encoded model full inventory.fields
    (inventory.activeCondition slot) nilOccurrence nilFields empty).mp valid
  obtain ⟨_, position, _⟩ := (inventory.activeCondition_holds model full slot empty _).mp observed
  exact Fin.elim0 position

noncomputable def encodeDataValue := arithmetic.encodeData Bool model ULift.up
  (fun value : Bool => ULift.up (value = true))

theorem compiled_result_agreement :
    CurriedPredicates.applyValues model _
      (model.denote (IndexedConstructorGuardCompilation.result
        (arithmetic.reading Bool) (Vectors.constructors Bool) consOccurrence) empty)
      (IndexedConstructorGuardCompilation.nativeData (arithmetic.reading Bool) (Vectors.constructors Bool)
        model encodeDataValue consOccurrence IndexedInductiveHOLTerms.Controls.consData) =
      ULift.up (Natural.succ (Natural.succ Natural.zero)) := by
  have generated := IndexedConstructorGuardCompilation.result_denote
    (arithmetic.reading Bool) (Vectors.constructors Bool) model encodeDataValue ULift.up empty
    (arithmetic.term_denote Bool model ULift.up (fun value : Bool => ULift.up (value = true))
      rfl (fun _ => rfl) (fun _ _ => rfl))
    consOccurrence PUnit.unit IndexedInductiveHOLTerms.Controls.consData
  exact generated

theorem compiled_child_agreement :
    CurriedPredicates.applyValues model _
      (model.denote (IndexedConstructorGuardCompilation.child
        (arithmetic.reading Bool) (Vectors.constructors Bool) consOccurrence ⟨0, by change 0 < 1; decide⟩) empty)
      (IndexedConstructorGuardCompilation.nativeData (arithmetic.reading Bool) (Vectors.constructors Bool)
        model encodeDataValue consOccurrence IndexedInductiveHOLTerms.Controls.consData) =
      ULift.up (Natural.succ Natural.zero) := by
  have generated := IndexedConstructorGuardCompilation.child_denote
    (arithmetic.reading Bool) (Vectors.constructors Bool) model encodeDataValue ULift.up empty
    (arithmetic.term_denote Bool model ULift.up (fun value : Bool => ULift.up (value = true))
      rfl (fun _ => rfl) (fun _ _ => rfl))
    consOccurrence ⟨0, by change 0 < 1; decide⟩ PUnit.unit IndexedInductiveHOLTerms.Controls.consData
  exact generated

#print axioms cons_tag
#print axioms nil_tag_refused
#print axioms result_two
#print axioms child_zero_one
#print axioms result_cannot_be_child
#print axioms nil_has_no_active_slot
#print axioms compiled_result_agreement
#print axioms compiled_child_agreement
#print axioms nilTagProof
#print axioms nilTagProof_free

end Mettapedia.GSLT.LanguageDef.IndexedInductiveGuardControls
