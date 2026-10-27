import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.JudgmentCompleteness
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Validity

/-!
# Finite formation evidence for annotated contexts

Each binder supplies an ordinary annotated typing certificate at an explicit
universe. Replay checks its complete context, domain and universe against the
actual telescope. This is separate from judgment replay because the original
variable rule alone does not certify a formed context.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality.Annotated.Checking

open Mettapedia.Logic

inductive ContextCode (Head : Type) (Witness : Type) : Nat → Type where
  | nil : ContextCode Head Witness 0
  | snoc {n : Nat} (prior : ContextCode Head Witness n) (level : Head)
      (domain : Logic.Derivation (CStatement Head) Witness) : ContextCode Head Witness (n + 1)

variable {Head : Type} {R : Rules Head} (P : ChurchRules R) [DecidableEq Head]
    [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative]
    [DecidableRel R.headEq]

def checkContext (decoder : RootDecoder P.computation) :
    {n : Nat} → (context : CCtx Head n) → ContextCode Head (interface P decoder).W n → Bool
  | _, .nil, .nil => true
  | _, .snoc context domain, .snoc prior level evidence =>
      checkContext decoder context prior && decide (R.isUniverse level) &&
        evidence.valid (interface P decoder) && decide (evidence.concl = .typing context domain (.head level))

theorem checkContext_sound (decoder : RootDecoder P.computation) {n : Nat} {context : CCtx Head n}
    (code : ContextCode Head (interface P decoder).W n)
    (accepted : checkContext P decoder context code = true) : CCtxFormed P context := by
  induction code with
  | nil => cases context; exact .nil
  | snoc prior level evidence ih =>
      cases context with
      | snoc context domain =>
          simp only [checkContext, Bool.and_eq_true, decide_eq_true_eq] at accepted
          obtain ⟨⟨⟨prefixChecked, allowed⟩, evidenceChecked⟩, conclusion⟩ := accepted
          have typed := derives_sound P decoder (evidence.valid_sound (interface P decoder) evidenceChecked)
          rw [conclusion] at typed
          exact .snoc (ih prefixChecked) ⟨level, allowed, typed⟩

theorem checkContext_complete (decoder : RootDecoder P.computation) {n : Nat} {context : CCtx Head n}
    (formed : CCtxFormed P context) :
    ∃ code : ContextCode Head (interface P decoder).W n, checkContext P decoder context code = true := by
  induction formed with
  | nil => exact ⟨.nil, rfl⟩
  | @snoc n context domain _ typeDomain ih =>
      obtain ⟨level, allowed, typed⟩ := typeDomain
      obtain ⟨prior, prefixChecked⟩ := ih
      obtain ⟨evidence, evidenceChecked, conclusion⟩ :=
        (derivable_iff_checked_tree P decoder (.typing context domain (.head level))).mp typed
      exact ⟨.snoc prior level evidence, by simp [checkContext, prefixChecked, allowed, evidenceChecked, conclusion]⟩

#print axioms checkContext_sound
#print axioms checkContext_complete

end TypedEquality.Annotated.Checking
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
