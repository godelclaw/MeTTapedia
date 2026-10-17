import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusSession

/-!
# Finite semantic arguments read from actual scoped event frames

The same decoder reads generated index and rely slots for every language.
Index arguments retain one fixed typed value; each rely domain contains the
ordered values in the supplied frames. Cartesian coverage is still checked:
reading two responses does not assert that their product is covered.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusChecking

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.NativeTypes.Modal
open FocusMeaning

variable {installed : Joined.Installed} {index : installed.Index} {ambient : List String}

def Parameters.atAnchor (parameters : Parameters installed index ambient)
    (anchor : ScopedRuleMatching.Assignment) : Parameters installed index ambient :=
  {parameters with
    target := fun values assignment target =>
      decide (∀ name ∈ (installed.indexed.schema index).matchedNames,
        ScopedRuleMatching.lookup assignment name = ScopedRuleMatching.lookup anchor name) &&
          parameters.target values assignment target}

theorem anchored_target_captures (parameters : Parameters installed index ambient)
    (anchor : ScopedRuleMatching.Assignment) (values : RelyValues installed index ambient)
    (assignment : ScopedRuleMatching.Assignment) (target : Pattern)
    (accepted : (parameters.atAnchor anchor).target values assignment target = true) :
    (∀ name ∈ (installed.indexed.schema index).matchedNames,
      ScopedRuleMatching.lookup assignment name = ScopedRuleMatching.lookup anchor name) ∧
      parameters.target values assignment target = true := by
  simpa only [Parameters.atAnchor, Bool.and_eq_true, decide_eq_true_eq] using accepted

def parametersFromFrames
    (frames : List (SemanticReceipts.Frame installed.indexed installed.semantic index ambient))
    (target : RelyValues installed index ambient → ScopedRuleMatching.Assignment → Pattern → Bool) :
    Option (Parameters installed index ambient) := do
  let first ← frames.head?
  let indices ← NativeBindingModalAdmission.allFin? (fun position : IndexPosition installed index => do
    let value ← NativeBindingSchemaCaptures.readSlot (installed.indexed.schema index) first.point
      installed.indexed.headers[index].indices[position].slot
    pure (⟨fun other => other = value, value, rfl⟩ : IndexArgument installed index ambient position))
  let relies ← NativeBindingModalAdmission.allFin? (fun position : RelyPosition installed index =>
    NativeSignature.decodeList (fun frame => NativeBindingSchemaCaptures.readSlot
      (installed.indexed.schema index) frame.point
      installed.indexed.operational.modal[installed.indexed.headers[index].origin].rely[position].slot) frames)
  pure ((⟨indices, relies, target⟩ : Parameters installed index ambient).atAnchor first.point.val.receipt.completed)

structure CertifiedMembership (parameters : Parameters installed index ambient) (focus : Pattern) where
  certificate : List Witness
  accepted : check parameters focus certificate = true

def verify? (parameters : Parameters installed index ambient) (focus : Pattern) (certificate : List Witness) :
    Option (CertifiedMembership parameters focus) :=
  if accepted : check parameters focus certificate = true then some ⟨certificate, accepted⟩ else none

theorem CertifiedMembership.sound {parameters : Parameters installed index ambient} {focus : Pattern}
    (membership : CertifiedMembership parameters focus) : Inhabits parameters.meaning focus :=
  check_sound parameters focus membership.certificate membership.accepted

/-- Execute the checked family's response function. The result is recovered
by finite search in the retained certificate, without choosing data from an
existential proof. Its complete receipt is rechecked at the requested input. -/
def CertifiedMembership.respond {parameters : Parameters installed index ambient} {focus : Pattern}
    (membership : CertifiedMembership parameters focus) (values : RelyValues installed index ambient)
    (requested : Requested parameters.meaning values) : Response parameters.meaning focus values :=
  let selected := membership.certificate.find? (accepts parameters focus values)
  have present : selected.isSome := by
    obtain ⟨_, all⟩ := (check_exact parameters focus membership.certificate).mp membership.accepted
    obtain ⟨witness, member, valid⟩ := all values requested
    exact List.find?_isSome.mpr ⟨witness, member, (accepts_exact parameters focus values witness).mpr valid⟩
  let witness := selected.get present
  have accepted : accepts parameters focus values witness = true :=
    List.find?_some (Option.some_get present).symm
  (checkResponse parameters.meaning focus values witness.source witness.payload).get accepted

def CertifiedMembership.family {parameters : Parameters installed index ambient} {focus : Pattern}
    (membership : CertifiedMembership parameters focus) : Family parameters.meaning focus where
  admitted := ((check_exact parameters focus membership.certificate).mp membership.accepted).1
  respond := membership.respond

theorem verify?_exact (parameters : Parameters installed index ambient) (focus : Pattern)
    (certificate : List Witness) :
    (verify? parameters focus certificate).isSome = true ↔ check parameters focus certificate = true := by
  unfold verify?
  split <;> simp_all

theorem verified_membership_iff (parameters : Parameters installed index ambient) (focus : Pattern) :
    (∃ certificate, (verify? parameters focus certificate).isSome = true) ↔ Inhabits parameters.meaning focus := by
  simp only [verify?_exact]
  exact certificate_exists_iff parameters focus

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.FiniteFocusChecking
