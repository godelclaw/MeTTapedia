import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mathlib.Computability.Primrec.List

/-!
# Effective search for total and partial proof checkers

A supplied code checks a pair `(claim, certificate)`; output `1` denotes
acceptance. Rejection and divergence are both distinct from acceptance.
An additional bounded-evaluation witness makes checking a submitted
certificate total even when the original checker is partial.

Search enumerates both certificates and evaluation bounds. It therefore
cannot get stuck running a divergent candidate. Its completeness is for
the acceptance relation of the supplied code. Semantic completeness needs
a separate theorem connecting that relation to the intended model class.

The `evaln` parameter is an evaluation bound, not an original-machine clock.
No polynomial time or polynomial certificate expansion is asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.EffectiveKernelSearch

open Nat.Partrec (Code)
open Mettapedia.GSLT.LanguageDef.KernelAuthority

/-- Acceptance by the original, possibly partial, checking program. -/
def Accepted (code : Code) (claim certificate : Nat) : Prop :=
  1 ∈ code.eval (Nat.pair claim certificate)

/-- A certificate together with an untrusted bounded-evaluation witness. -/
abbrev ClockedEvidence := Nat × Nat

def clockedCheck (code : Code) (claim : Nat) (evidence : ClockedEvidence) : Bool :=
  decide (code.evaln evidence.2 (Nat.pair claim evidence.1) = some 1)

def clockedChecker (code : Code) : Checker Nat ClockedEvidence :=
  ⟨clockedCheck code⟩

theorem clocked_sound (code : Code) (claim : Nat) (evidence : ClockedEvidence)
    (accepted : clockedCheck code claim evidence = true) :
    Accepted code claim evidence.1 := by
  apply Code.evaln_sound
  simpa only [clockedCheck, decide_eq_true_eq, Option.mem_def] using accepted

theorem clocked_complete (code : Code) (claim certificate : Nat)
    (accepted : Accepted code claim certificate) :
    ∃ bound, clockedCheck code claim (certificate, bound) = true := by
  obtain ⟨bound, ran⟩ := Code.evaln_complete.mp accepted
  exact ⟨bound, by simpa only [clockedCheck, decide_eq_true_eq, Option.mem_def] using ran⟩

theorem clocked_iff (code : Code) (claim certificate : Nat) :
    (∃ bound, clockedCheck code claim (certificate, bound) = true) ↔
      Accepted code claim certificate :=
  ⟨fun ⟨_, accepted⟩ => clocked_sound code claim _ accepted,
    clocked_complete code claim certificate⟩

/-- The clocked checker is primitive recursive, including rejected inputs. -/
theorem clockedCheck_primrec (code : Code) :
    Primrec (fun input : Nat × ClockedEvidence =>
      clockedCheck code input.1 input.2) := by
  have evaluated : Primrec (fun input : Nat × ClockedEvidence =>
      code.evaln input.2.2 (Nat.pair input.1 input.2.1)) :=
    Code.primrec_evaln.comp
      (((Primrec.snd.comp Primrec.snd).pair (Primrec.const code)).pair
        (Primrec₂.natPair.comp Primrec.fst (Primrec.fst.comp Primrec.snd)))
  exact Primrec.beq.comp evaluated (Primrec.const (some 1))

/-- Every finite pair is eventually proposed, regardless of other candidates. -/
def candidate (code : Code) (claim index : Nat) : Option ClockedEvidence :=
  let evidence := Nat.unpair index
  if clockedCheck code claim evidence then some evidence else none

theorem candidate_sound (code : Code) (claim index : Nat)
    (evidence : ClockedEvidence) (found : candidate code claim index = some evidence) :
    clockedCheck code claim evidence = true := by
  dsimp only [candidate] at found
  split at found
  · rename_i accepted
    cases Option.some.inj found
    exact accepted
  · cases found

theorem candidate_complete (code : Code) (claim : Nat) (evidence : ClockedEvidence)
    (accepted : clockedCheck code claim evidence = true) :
    candidate code claim (Nat.pair evidence.1 evidence.2) = some evidence := by
  simp only [candidate, Nat.unpair_pair, accepted, ite_true]

set_option backward.isDefEq.respectTransparency false in
theorem candidate_computable (code : Code) : Computable₂ (candidate code) := by
  have evidence : Computable (fun input : Nat × Nat => Nat.unpair input.2) :=
    Primrec.unpair.to_comp.comp Computable.snd
  have checked : Computable (fun input : Nat × Nat =>
      clockedCheck code input.1 (Nat.unpair input.2)) :=
    Computable.comp (f := fun input : Nat × ClockedEvidence =>
      clockedCheck code input.1 input.2)
      (g := fun input : Nat × Nat => (input.1, Nat.unpair input.2))
      (clockedCheck_primrec code).to_comp (Computable.fst.pair evidence)
  have result : Computable (fun input : Nat × Nat =>
      cond (clockedCheck code input.1 (Nat.unpair input.2))
        (some (Nat.unpair input.2)) none) :=
    checked.cond (Primrec.option_some.to_comp.comp evidence) (Computable.const none)
  exact result.of_eq fun input => by simp only [candidate, Bool.cond_eq_ite]

/-- Fair, partial proof search. The returned finite witness is independently
checked by `clockedCheck`; the search history is not part of its authority. -/
def search (code : Code) (claim : Nat) : Part ClockedEvidence :=
  Nat.rfindOpt (candidate code claim)

theorem search_partrec (code : Code) : Partrec (search code) :=
  Partrec.rfindOpt (candidate_computable code)

theorem search_sound (code : Code) (claim : Nat) (evidence : ClockedEvidence)
    (found : evidence ∈ search code claim) :
    clockedCheck code claim evidence = true := by
  obtain ⟨index, atIndex⟩ := Nat.rfindOpt_spec found
  exact candidate_sound code claim index evidence (by simpa [Option.mem_def] using atIndex)

/-- Successful fair search is exactly the existence of an accepted original
certificate, even when some other certificates make the checker diverge. -/
theorem search_dom_iff (code : Code) (claim : Nat) :
    (search code claim).Dom ↔ ∃ certificate, Accepted code claim certificate := by
  rw [search, Nat.rfindOpt_dom]
  constructor
  · rintro ⟨index, evidence, found⟩
    exact ⟨evidence.1, clocked_sound code claim evidence
      (candidate_sound code claim index evidence (by simpa [Option.mem_def] using found))⟩
  · rintro ⟨certificate, accepted⟩
    obtain ⟨bound, checked⟩ := clocked_complete code claim certificate accepted
    exact ⟨Nat.pair certificate bound, (certificate, bound), by
      simpa [Option.mem_def] using candidate_complete code claim _ checked⟩

theorem provability_re (code : Code) :
    REPred (fun claim => ∃ certificate, Accepted code claim certificate) :=
  (search_partrec code).dom_re.of_eq (search_dom_iff code)

section Semantics

variable (code : Code) (Derivable Meaning : Nat → Prop)
  (replay : ∀ claim, (∃ certificate, Accepted code claim certificate) ↔ Derivable claim)

include replay

theorem search_iff_derivable (claim : Nat) :
    (search code claim).Dom ↔ Derivable claim :=
  (search_dom_iff code claim).trans (replay claim)

/-- Soundness suffices for trusting found proofs. Model-theoretic
completeness is not needed for this implication. -/
theorem found_is_meaningful (sound : ∀ claim, Derivable claim → Meaning claim)
    (claim : Nat) (evidence : ClockedEvidence) (found : evidence ∈ search code claim) :
    Meaning claim :=
  sound claim ((replay claim).mp
    ⟨evidence.1, clocked_sound code claim evidence (search_sound code claim evidence found)⟩)

theorem semantic_search_exact (complete : ∀ claim, Meaning claim ↔ Derivable claim)
    (claim : Nat) : (search code claim).Dom ↔ Meaning claim :=
  (search_iff_derivable code Derivable replay claim).trans (complete claim).symm

/-- A true but underivable claim has no successful search run in this
calculus. This leaves soundness of all found proofs intact. -/
theorem semantic_gap_unreachable (claim : Nat) (gap : ¬ Derivable claim) :
    ¬ (search code claim).Dom :=
  fun found => gap ((search_iff_derivable code Derivable replay claim).mp found)

end Semantics

/-- A semantics that is not recursively enumerable cannot have an effective
checker that is both sound and certificate-complete for all its validities. -/
theorem no_effective_exact_checker (code : Code) (Meaning : Nat → Prop)
    (notRE : ¬ REPred Meaning) :
    ¬ (∀ claim, (∃ certificate, Accepted code claim certificate) ↔ Meaning claim) := by
  intro exact
  exact notRE ((provability_re code).of_eq exact)

namespace Controls

/-- Finding the certificate is separate from bounded verification. -/
theorem right_accepted : clockedCheck .right 0 (1, 10) = true := by
  have small : Nat.pair 0 1 ≤ 9 := by decide
  simp [clockedCheck, Code.evaln, small, Nat.unpair_pair]

theorem wrong_result_refused : clockedCheck .right 0 (2, 10) = false := by
  have small : Nat.pair 0 2 ≤ 9 := by decide
  simp [clockedCheck, Code.evaln, small, Nat.unpair_pair]

theorem insufficient_bound_unknown : clockedCheck .right 0 (1, 0) = false := by
  simp [clockedCheck, Code.evaln]

theorem accepted_despite_small_bound_failure : Accepted .right 0 1 :=
  clocked_sound .right 0 (1, 10) right_accepted

theorem fair_search_finds_witness : (search .right 0).Dom :=
  (search_dom_iff .right 0).mpr ⟨1, accepted_despite_small_bound_failure⟩

end Controls

end Mettapedia.GSLT.LanguageDef.EffectiveKernelSearch
