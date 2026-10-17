import Mettapedia.Languages.Megalodon.BorrowedProofCursor
import Mettapedia.Languages.Megalodon.FuelledConversionProfile

/-!
# Proof validity independent of the checking budget

A successful local check remains successful as normalization fuel increases.
Different rows may therefore use different bounds without changing the logic.
Every finite derivation assembled this way has a common finite bound and an
original Mathdata proof. No finite default bound or termination assertion for
arbitrary unchecked environments is introduced.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.BudgetIndependent
open MathdataKernel BorrowedProofCursor ProofJudgment
open Mettapedia.Logic Mettapedia.Logic.DerivationGraph

theorem delta_mono (environment : Environment) (term normal : Tm) {first second : Nat}
    (increased : first ≤ second) (accepted : deltaNormalize environment first term = some normal) :
    deltaNormalize environment second term = some normal := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le increased
  clear increased
  induction extra with
  | zero => simpa using accepted
  | succ extra ih => exact FuelledConversionProfile.delta_mono_succ environment (first + extra) term normal ih

theorem rules_mono {environment : Environment} {first second : Nat} {premises : List Judgment}
    {conclusion : Judgment} (increased : first ≤ second) (rule : Rules environment first premises conclusion) :
    Rules environment second premises conclusion := by
  cases rule with
  | hyp found => exact .hyp found
  | known found normalized => exact .known found (FuelledConversionProfile.normalize_mono _ _ _ increased normalized)
  | termApp typed unfolded normalized =>
      exact .termApp typed (delta_mono _ _ _ increased unfolded)
        (FuelledConversionProfile.normalize_mono _ _ _ increased normalized)
  | proofApp => exact .proofApp
  | termLam formed => exact .termLam formed
  | proofLam typed normalized => exact .proofLam typed (FuelledConversionProfile.normalize_mono _ _ _ increased normalized)
  | typeApp => exact .typeApp
  | typeLam terms hypotheses => exact .typeLam terms hypotheses

theorem derives_mono {environment : Environment} {first second : Nat} {conclusion : Judgment}
    (increased : first ≤ second) (derived : Derives (Rules environment first) conclusion) :
    Derives (Rules environment second) conclusion :=
  derived.mono (fun _ _ rule => rules_mono increased rule)

def UnboundedRules (environment : Environment) (premises : List Judgment) (conclusion : Judgment) : Prop :=
  ∃ fuel, Rules environment fuel premises conclusion

def interface (environment : Environment) : RuleWitness (UnboundedRules environment) where
  W := Nat × Witness
  isInstance request := (BorrowedProofCursor.interface environment request.1).isInstance request.2
  sound request premises conclusion accepted :=
    ⟨request.1, (BorrowedProofCursor.interface environment request.1).sound request.2 premises conclusion accepted⟩
  complete premises conclusion rule := by
    obtain ⟨fuel, rule⟩ := rule
    obtain ⟨witness, accepted⟩ := (BorrowedProofCursor.interface environment fuel).complete premises conclusion rule
    exact ⟨⟨fuel, witness⟩, accepted⟩

private theorem common_bound (environment : Environment) (premises : List Judgment)
    (bounded : ∀ premise ∈ premises, ∃ fuel, Derives (Rules environment fuel) premise) :
    ∃ fuel, ∀ premise ∈ premises, Derives (Rules environment fuel) premise := by
  induction premises with
  | nil => exact ⟨0, by simp⟩
  | cons first rest ih =>
      obtain ⟨firstFuel, firstProof⟩ := bounded first (by simp)
      obtain ⟨restFuel, restProof⟩ := ih (fun premise member => bounded premise (by simp [member]))
      refine ⟨max firstFuel restFuel, ?_⟩
      intro premise member
      rcases List.mem_cons.mp member with same | later
      · subst premise
        exact derives_mono (Nat.le_max_left _ _) firstProof
      · exact derives_mono (Nat.le_max_right _ _) (restProof premise later)

theorem finite_common_bound {environment : Environment} {conclusion : Judgment}
    (derived : Derives (UnboundedRules environment) conclusion) :
    ∃ fuel, Derives (Rules environment fuel) conclusion := by
  induction derived with
  | node premises conclusion rule _ ih =>
      obtain ⟨ruleFuel, rule⟩ := rule
      obtain ⟨parentFuel, parents⟩ := common_bound environment premises ih
      exact ⟨max ruleFuel parentFuel, .node premises conclusion
        (rules_mono (Nat.le_max_left _ _) rule)
        (fun premise member => derives_mono (Nat.le_max_right _ _) (parents premise member))⟩

theorem original_iff (environment : Environment) (conclusion : Judgment) :
    Derives (UnboundedRules environment) conclusion ↔
      ∃ fuel proof, inferProof environment fuel conclusion.context.typeDepth conclusion.context.terms
        conclusion.context.hypotheses proof = some conclusion.proposition := by
  constructor
  · intro derived
    obtain ⟨fuel, bounded⟩ := finite_common_bound derived
    obtain ⟨proof, checked⟩ := (derives_iff_original environment fuel conclusion).mp bounded
    exact ⟨fuel, proof, checked⟩
  · rintro ⟨fuel, proof, checked⟩
    exact ((derives_iff_original environment fuel conclusion).mpr ⟨proof, checked⟩).mono
      (fun _ _ rule => ⟨fuel, rule⟩)

theorem root_has_original {environment : Environment}
    (root : CheckedJudgment (UnboundedRules environment)) :
    ∃ fuel proof, inferProof environment fuel root.judgment.context.typeDepth root.judgment.context.terms
      root.judgment.context.hypotheses proof = some root.judgment.proposition :=
  (original_iff environment root.judgment).mp root.valid

theorem no_forgery_from_changing_bounds {environment : Environment} {conclusion : Judgment}
    (impossible : ∀ fuel proof, inferProof environment fuel conclusion.context.typeDepth conclusion.context.terms
      conclusion.context.hypotheses proof ≠ some conclusion.proposition) :
    ¬ Derives (UnboundedRules environment) conclusion := by
  intro derived
  obtain ⟨fuel, proof, accepted⟩ := (original_iff environment conclusion).mp derived
  exact impossible fuel proof accepted

end Mettapedia.Languages.Megalodon.BudgetIndependent
