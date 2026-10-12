import Mettapedia.OSLF.Syntax.RhoScopedFiringSubstitution
import Mettapedia.OSLF.Syntax.RhoScopedConstructorInventory
import Mettapedia.OSLF.Syntax.RhoScopedInstanceReadout
import Mettapedia.OSLF.Syntax.RhoScopedParallelReactiveControls

/-!
# Original communication loses leastness under actual channel identification

Two distinct open channels supply a genuine original least-labelled firing.
Closing both names to the same quotation preserves the complete enabled
event, while its mapped label and surrounding input now overlap. The mapped
complete receipt is therefore not admitted as an IPO receipt with those same
readouts. An identity-labelled firing remains admitted under that closing.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.RhoScopedFiringSubstitutionControls

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoScopedParallelEvents RhoScopedParallelReactiveSystem RhoScopedParallelInventory
open RhoScopedInstanceReadout RhoScopedFiringSubstitution RhoScopedConstructorInventory
open RhoIntrinsicCanonicalBag RhoIntrinsicReadback MeTTaIL.Syntax

local instance (context : Ctx sig) : DecidableEq (Prime context) := Classical.decEq _

def context : Ctx sig := [Srt.nm, Srt.nm]
def firstName : Name context := project (.var .zero)
def secondName : Name context := project (.var (.succ .zero))

theorem original_names_distinct : firstName ≠ secondName := by
  intro same
  have encoded := congrArg RhoSchema.IntrinsicEncoding.encodeEquationClass same
  change (Pattern.bvar 0 : Pattern) = Pattern.bvar 1 at encoded
  cases encoded

def firstInput : Process context := inputClass firstName (zero (Srt.nm :: context))
def secondInput : Process context := inputClass secondName (zero (Srt.nm :: context))
def output : Process context := outputClass firstName (zero context)

theorem input_inventories_disjoint : read firstInput ∩ read secondInput = 0 := by
  apply Multiset.inter_eq_zero_iff_disjoint.mpr
  apply Multiset.disjoint_left.mpr
  intro prime firstMember secondMember
  have firstPattern : prime.val ∈ components firstInput := by
    rw [← values_read]
    exact Multiset.mem_map.mpr ⟨prime, firstMember, rfl⟩
  have secondPattern : prime.val ∈ components secondInput := by
    rw [← values_read]
    exact Multiset.mem_map.mpr ⟨prime, secondMember, rfl⟩
  rw [firstInput, input_components, Multiset.mem_singleton] at firstPattern
  rw [secondInput, input_components, Multiset.mem_singleton] at secondPattern
  have names := congrArg Prod.fst
    (inputPattern_injective context (firstPattern.symm.trans secondPattern))
  exact original_names_distinct names

def originalRoot : Root sourceRules core context :=
  ⟨⟨.communication, trivial⟩, communication (.var .zero) null null⟩

theorem original_source : originalRoot.source = join output firstInput :=
  Communication.source_class originalRoot.2

theorem original_target : originalRoot.target = zero context := rfl

def initial : Process context := join output secondInput
def target : Process context := secondInput

def supplied : Firing (rules := sourceRules) (admitted := core) initial firstInput target where
  root := originalRoot
  surrounding := secondInput
  square := by
    rw [original_source]
    apply read_injective context
    simp only [initial, read_join]
    ac_rfl
  least := input_inventories_disjoint
  target := (join_zero_left secondInput).symm

def identify : Sub sig context [] := fun _ position =>
  match position with
  | .zero => quoteRaw null
  | .succ .zero => quoteRaw null

def closedInput : Process [] := inputClass (quote (zero [])) (zero [Srt.nm])

theorem mapped_inputs_coincide :
    bindQ identify firstInput = closedInput ∧ bindQ identify secondInput = closedInput := by
  constructor <;> rfl

theorem closed_input_nonzero : read closedInput ≠ 0 := by
  intro empty
  have componentsEmpty : components closedInput = 0 := by
    rw [← values_read, empty]
    rfl
  rw [closedInput, input_components] at componentsEmpty
  have counted := congrArg Multiset.card componentsEmpty
  simp only [Multiset.card_singleton, Multiset.card_zero] at counted
  cases counted

theorem mapped_inventory_admission_fails : ¬ LeastAdmission identify supplied := by
  intro admitted
  change read (bindQ identify firstInput) ∩ read (bindQ identify secondInput) = 0 at admitted
  rw [mapped_inputs_coincide.1, mapped_inputs_coincide.2, ← Multiset.inf_eq_inter, inf_idem] at admitted
  exact closed_input_nonzero admitted

theorem complete_ipo_receipt_cannot_keep_both_mapped_readouts :
    ¬ ∃ mapped : Firing (rules := sourceRules) (admitted := core)
        (bindQ identify initial) (bindQ identify firstInput) (bindQ identify target),
      mapped.root = supplied.root.map identify ∧
        mapped.surrounding = bindQ identify supplied.surrounding := by
  rw [complete_map_admission_iff]
  exact mapped_inventory_admission_fails

theorem mapped_event_really_fires :
    RhoScopedParallelEvents.Step (rules := sourceRules) (admitted := core)
      (join (bindQ identify initial) (bindQ identify firstInput)) (bindQ identify target) :=
  enabled_after_filling_mapped_label identify supplied

def identityReceipt : Firing (rules := sourceRules) (admitted := core)
    originalRoot.source (zero context) originalRoot.target where
  root := originalRoot
  surrounding := zero context
  square := rfl
  least := by rw [read_zero, Multiset.zero_inter]
  target := (join_zero_right originalRoot.target).symm

def mappedIdentityReceipt : Firing (rules := sourceRules) (admitted := core)
    (bindQ identify originalRoot.source) (zero []) (bindQ identify originalRoot.target) :=
  mapIdentity identify identityReceipt

theorem mapped_identity_keeps_original_rule : mappedIdentityReceipt.root.1 = originalRoot.1 := rfl

end Mettapedia.OSLF.Binding.RhoScopedFiringSubstitutionControls
