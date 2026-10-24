import Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeGuestControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedFamilyChecking

/-!
# Receipt-only and raw-authority boundary for the nested SearchTree guest

Canonical typed receipts license checked substitution instances.  The raw
iota witness family is intentionally broader: it can be instantiated with
untyped terms.  This module exhibits that separation and defines the safe
receipt-only profile, whose judgmental root relation is empty.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeGuest

open Presentation Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Presentation.Declaration.IndexedFamily
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

noncomputable def schemas : Checking.Schemas baseRules signature iotaComputation :=
  [⟨5, solvedSchema⟩, ⟨5, branchSchema⟩]

/-- The current safe profile retains both typed receipts without installing
either equation as raw judgmental conversion. -/
noncomputable def receiptOnlyProfile : Checking.Profile schemas where
  eliminationTarget := fun _ => true
  identity := fun _ => ⟨false, false⟩
  iota := fun _ => ⟨true, false, false⟩
  judgmentalHasReceipt := by
    intro index impossible
    cases impossible

@[simp] theorem receiptOnly_enabled (index : Fin (Checking.table schemas).length) :
    receiptOnlyProfile.enabled index = false := rfl

/-- Receipt retention alone adds no root step to definitional conversion. -/
theorem receiptOnly_no_root {n : Nat} {left right : Tower.Tm n} :
    ¬ receiptOnlyProfile.rules.computation.step left right := by
  rintro ⟨evidence⟩
  cases evidence with
  | instantiate index permitted substitution =>
      simp only [receiptOnly_enabled] at permitted
      exact Bool.noConfusion permitted

def missingName : DeclName := `Generated.SearchTree.untypedArgument

theorem missing_lookup : rules.constantType missingName = none := by
  decide +kernel

def untypedAssignment : Sub Tower.Head 5 0 :=
  fun _ => .const missingName

/-- Raw syntax can instantiate the branch equation without a typing
certificate.  This is evidence of a syntactic root shape only. -/
def untypedBranchEvidence : IotaEvidence 0
    (subst untypedAssignment branchLeft)
    (subst untypedAssignment branchRight) :=
  (IotaEvidence.branch (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)).substitute
    untypedAssignment

/-- The same substitution cannot instantiate the typed branch schema: its
oldest argument is an undeclared constant where a universe is required. -/
theorem untypedAssignment_not_typed :
    ¬ CtxMor rules branchContext .nil untypedAssignment := by
  intro typed
  have oldest := typed (4 : Fin 5)
  exact oldest.constantImpossibleWhenMissing missing_lookup

/-- Exact separation between raw iota evidence and a checked schema
instance. -/
theorem rawEvidence_not_typedInstance :
    Nonempty (IotaEvidence 0
      (subst untypedAssignment branchLeft)
      (subst untypedAssignment branchRight)) ∧
      ¬ CtxMor rules branchContext .nil untypedAssignment :=
  ⟨⟨untypedBranchEvidence⟩, untypedAssignment_not_typed⟩

#print axioms receiptOnly_no_root
#print axioms missing_lookup
#print axioms untypedAssignment_not_typed
#print axioms rawEvidence_not_typedInstance

end Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeGuest
