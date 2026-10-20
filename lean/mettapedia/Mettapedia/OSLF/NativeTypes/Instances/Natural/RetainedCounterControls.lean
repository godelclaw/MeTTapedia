import Mettapedia.OSLF.NativeTypes.Instances.Natural.RetainedCounter
import Mettapedia.GSLT.LanguageDef.IntegerRepresentationRetainedCallControls

/-! Retained-state recurrence and the availability counterexample. -/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.Natural.RetainedCounter.Controls

open Mettapedia.GSLT.LanguageDef IntegerRepresentationExternalCall
open Retained.Controls
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Decision
open Mettapedia.OSLF.NativeTypes.Executable
open Reference.Core (Outcome)

theorem available : Available encode decode provider := by
  intro value _
  exact ⟨_, rfl⟩

def large : Value decode := ⟨.inr ⟨2^128, 7⟩, by decide +kernel⟩

theorem recurring_large :
    BuchiPath (transitionSystem (span encode decode provider)) .future (accepting decode {0}) large := by
  apply (check_buchi_iff encode decode roundtrip provider provider_sound available {0} 1000 large
    (by decide +kernel)).mp
  decide +kernel

def exhausted : Value decode := ⟨.inr ⟨7, 4⟩, by decide +kernel⟩

theorem limited_unavailable : ¬ Available encode decode limited := by
  intro complete
  obtain ⟨value, returned⟩ := complete exhausted rfl
  have failed : limited .add (Retained.stored encode exhausted.val)
      (Retained.stored encode (.inl 1)) = .error "resource-exhausted" := rfl
  rw [failed] at returned
  cases returned

/-- A true parity verdict for the mathematical counter does not manufacture
an execution for a provider which cannot take even its first step. -/
theorem parity_verdict_without_provider_path :
    (Finite.check Counter.table (Formula.buchi .future) (fun _ => {0})
      1000 (Counter.phase (number decode exhausted))).map Outcome.answer = some (some true) ∧
    ¬ BuchiPath (transitionSystem (span encode decode limited)) .future (accepting decode {0}) exhausted := by
  refine ⟨by decide +kernel, ?_⟩
  rintro ⟨path, starts, steps, _⟩
  obtain ⟨edge, source, _⟩ := steps 0
  have same : edge.val.1 = exhausted := source.trans starts
  have returned := edge.property
  rw [same] at returned
  have failed : Retained.add encode limited exhausted.val (.inl 1) = .error "resource-exhausted" := rfl
  rw [failed] at returned
  cases returned

#print axioms recurring_large
#print axioms parity_verdict_without_provider_path

end Mettapedia.OSLF.NativeTypes.Instances.Natural.RetainedCounter.Controls
