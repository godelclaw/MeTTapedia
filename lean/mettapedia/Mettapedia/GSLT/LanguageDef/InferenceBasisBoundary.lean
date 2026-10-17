import Mettapedia.Logic.InferenceBasis
import Mettapedia.GSLT.LanguageDef.KernelAuthority

/-!
# Removing a primitive can be an undecidable question

A two-rule family suffices. One rule asserts the judgment `0`; the other
requires finite checked evidence that a supplied program halts. Both rule
witnesses are decidable. Eliminating the assertion rule while preserving its
consequences is nevertheless equivalent to the halting problem.

This is a concrete obstruction to a general effective basis minimizer. It
does not prevent proving minimality for a particular kernel or a restricted
class. The evaluation bound is a witness for `Code.evaln`, not a machine clock.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.InferenceBasisBoundary

open Mettapedia.Logic Mettapedia.Logic.InferenceBasis
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Nat.Partrec (Code)

inductive Operation where
  | assertZero
  | witnessedHalt
deriving DecidableEq, Repr

def family (code : Code) : RuleFamily Operation Nat
  | .assertZero, premises, conclusion => premises = [] ∧ conclusion = 0
  | .witnessedHalt, premises, conclusion =>
      premises = [] ∧ conclusion = 0 ∧ HaltingMeaning code

/-- Both rule kinds have finite, decidable evidence. The bound is inspected
only by the witnessed computation rule. -/
def checkInstance (code : Code) (operation : Operation) (bound : Nat)
    (premises : List Nat) (conclusion : Nat) : Bool :=
  decide (premises = [] ∧ conclusion = 0) &&
    match operation with
    | .assertZero => true
    | .witnessedHalt => haltingTrustBoundaryChecker.check code bound

theorem checkInstance_exact (code : Code) (operation : Operation)
    (premises : List Nat) (conclusion : Nat) :
    (∃ bound, checkInstance code operation bound premises conclusion = true) ↔
      family code operation premises conclusion := by
  cases operation with
  | assertZero => simp [checkInstance, family]
  | witnessedHalt =>
      simp only [checkInstance, Bool.and_eq_true, decide_eq_true_eq, family]
      constructor
      · rintro ⟨bound, ⟨rfl, rfl⟩, accepted⟩
        exact ⟨rfl, rfl, haltingTrustBoundaryChecker_sound code bound accepted⟩
      · rintro ⟨rfl, rfl, halts⟩
        obtain ⟨bound, accepted⟩ := haltingTrustBoundaryChecker_complete code halts
        exact ⟨bound, ⟨rfl, rfl⟩, accepted⟩

def retained : Finset Operation := {.witnessedHalt}
def requested : Finset Operation := {.assertZero}

theorem retained_zero_iff (code : Code) :
    From (family code) retained [] 0 ↔ HaltingMeaning code := by
  constructor
  · intro derived
    apply derived.least (fun _ => HaltingMeaning code)
    intro premises conclusion rule _
    rcases rule with ⟨_, impossible⟩ | ⟨operation, member, step⟩
    · simp at impossible
    · have same : operation = .witnessedHalt := by simpa [retained] using member
      cases same
      exact step.2.2
  · intro halts
    exact apply_rule (family := family code) (premises := []) (operation := Operation.witnessedHalt) (by simp [retained]) ⟨rfl, rfl, halts⟩ (by simp)

/-- Deciding whether this primitive is eliminable decides actual halting. -/
theorem generates_iff_halts (code : Code) :
    Generates (family code) retained requested ↔ HaltingMeaning code := by
  constructor
  · intro generated
    exact (retained_zero_iff code).mp
      (generated .assertZero (by simp [requested]) [] 0 ⟨rfl, rfl⟩)
  · intro halts operation member premises conclusion step
    have same : operation = .assertZero := by simpa [requested] using member
    cases same
    rcases step with ⟨rfl, rfl⟩
    exact (retained_zero_iff code).mpr halts

theorem elimination_not_computable :
    ¬ ComputablePred (fun code : Code => Generates (family code) retained requested) := by
  intro computable
  apply haltingMeaning_not_computable
  exact computable.of_eq generates_iff_halts

/-- A terminating original program gives a genuine removable primitive. -/
theorem zero_rule_eliminable : Generates (family .zero) retained requested := by
  apply (generates_iff_halts _).mpr
  exact Part.some_dom 0

/-- Every nonhalting program supplies a counterexample to elimination. -/
theorem nonhalting_rule_indispensable (code : Code) (diverges : ¬ HaltingMeaning code) :
    ¬ Generates (family code) retained requested :=
  fun generated => diverges ((generates_iff_halts code).mp generated)

/-- Searching for a zero from the constant-one program never succeeds. -/
theorem constant_one_search_diverges : ¬ HaltingMeaning (.rfind' (.const 1)) := by
  simp [HaltingMeaning, Code.eval, Nat.unpaired, Code.eval_const]
  intro halts
  obtain ⟨n, found, _⟩ := Nat.rfind_dom.mp halts
  simp at found

theorem constant_one_rule_indispensable :
    ¬ Generates (family (.rfind' (.const 1))) retained requested :=
  nonhalting_rule_indispensable _ constant_one_search_diverges

end Mettapedia.GSLT.LanguageDef.InferenceBasisBoundary
