import Mettapedia.Logic.ProofSearch.CertificateBounds

/-!
# Effective budgets for partial proof producers

A partial-recursive producer emits a natural-number certificate, which is
then checked independently. A computable budget sufficient on every positive
query would decide the original meaning: unsuccessful bounded evaluation or
a refused candidate supplies the negative branch of that decision procedure.
Consequently an undecidable meaning has no such budget for a complete producer.

The clock here is Mathlib's original `Code.evaln` evaluation budget. No claim
identifies that budget with TM2 steps or wall-clock time. Executed TM2 producer,
translator and checker composition is provided separately by `SearchTransport`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ProofSearch.SearchBounds

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Nat.Partrec (Code)

variable {Claim : Type}

/-- Poll the original partial producer and independently validate its result.
`false` is a bounded observation, not a theorem of nonderivability. -/
def poll (checker : Checker Claim Nat) (producer : Code) (input : Claim → Nat)
    (claim : Claim) (budget : Nat) : Bool :=
  match Code.evaln budget producer (input claim) with
  | none => false
  | some certificate => checker.check claim certificate

theorem poll_eq_true (checker : Checker Claim Nat) (producer : Code)
    (input : Claim → Nat) (claim : Claim) (budget : Nat) :
    poll checker producer input claim budget = true ↔
      ∃ certificate, Code.evaln budget producer (input claim) = some certificate ∧
        checker.check claim certificate = true := by
  cases evaluated : Code.evaln budget producer (input claim) <;>
    simp [poll, evaluated]

theorem poll_sound (checker : Checker Claim Nat) (producer : Code)
    (input : Claim → Nat) {Meaning : Claim → Prop} (sound : checker.Sound Meaning)
    (claim : Claim) (budget : Nat)
    (accepted : poll checker producer input claim budget = true) : Meaning claim := by
  obtain ⟨certificate, _, checked⟩ := (poll_eq_true checker producer input claim budget).mp accepted
  exact sound claim certificate checked

/-- Increasing the budget preserves a previously observed accepted result. -/
theorem poll_mono (checker : Checker Claim Nat) (producer : Code)
    (input : Claim → Nat) (claim : Claim) {small large : Nat} (bound : small ≤ large)
    (accepted : poll checker producer input claim small = true) :
    poll checker producer input claim large = true := by
  obtain ⟨certificate, evaluated, checked⟩ :=
    (poll_eq_true checker producer input claim small).mp accepted
  exact (poll_eq_true checker producer input claim large).mpr
    ⟨certificate, Code.evaln_mono bound evaluated, checked⟩

theorem poll_computable [Primcodable Claim] (checker : Checker Claim Nat)
    (checkerComputable : Computable (fun pair : Claim × Nat => checker.check pair.1 pair.2))
    (producer : Code) (input : Claim → Nat) (inputComputable : Computable input) :
    Computable (fun pair : Claim × Nat => poll checker producer input pair.1 pair.2) := by
  have evaluated : Computable (fun pair : Claim × Nat => Code.evaln pair.2 producer (input pair.1)) :=
    Code.primrec_evaln.to_comp.comp
      ((Computable.snd.pair (Computable.const producer)).pair
        (inputComputable.comp Computable.fst))
  apply (Computable.option_casesOn evaluated (Computable.const false)
    (checkerComputable.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂).of_eq
  intro pair
  cases result : Code.evaln pair.2 producer (input pair.1) <;> simp [poll, result]

/-- Eventual discovery is exactly eventual accepted bounded observation.
An arbitrary output from the producer does not bypass checking. -/
theorem eventually_poll (checker : Checker Claim Nat) (producer : Code)
    (input : Claim → Nat) (claim : Claim) :
    (∃ certificate, certificate ∈ Code.eval producer (input claim) ∧
      checker.check claim certificate = true) ↔
    ∃ budget, poll checker producer input claim budget = true := by
  constructor
  · rintro ⟨certificate, produced, checked⟩
    obtain ⟨budget, evaluated⟩ := Code.evaln_complete.mp produced
    exact ⟨budget, (poll_eq_true checker producer input claim budget).mpr
      ⟨certificate, evaluated, checked⟩⟩
  · rintro ⟨budget, accepted⟩
    obtain ⟨certificate, evaluated, checked⟩ :=
      (poll_eq_true checker producer input claim budget).mp accepted
    exact ⟨certificate, Code.evaln_sound evaluated, checked⟩

/-- A computable budget covering every positive query turns the original
partial search plus total replay into a computable decision procedure. -/
theorem computableMeaning_of_budget [Primcodable Claim] (checker : Checker Claim Nat)
    (checkerComputable : Computable (fun pair : Claim × Nat => checker.check pair.1 pair.2))
    (producer : Code) (input : Claim → Nat) (inputComputable : Computable input)
    {Meaning : Claim → Prop} (sound : checker.Sound Meaning)
    (budget : Claim → Nat) (budgetComputable : Computable budget)
    (covers : ∀ claim, Meaning claim → poll checker producer input claim (budget claim) = true) :
    ComputablePred Meaning := by
  rw [ComputablePred.computable_iff]
  refine ⟨fun claim => poll checker producer input claim (budget claim),
    (poll_computable checker checkerComputable producer input inputComputable).comp
      (Computable.id.pair budgetComputable), ?_⟩
  funext claim
  exact propext ⟨covers claim, poll_sound checker producer input sound claim (budget claim)⟩

theorem no_computable_success_budget [Primcodable Claim] (checker : Checker Claim Nat)
    (checkerComputable : Computable (fun pair : Claim × Nat => checker.check pair.1 pair.2))
    (producer : Code) (input : Claim → Nat) (inputComputable : Computable input)
    {Meaning : Claim → Prop} (sound : checker.Sound Meaning)
    (undecidableMeaning : ¬ ComputablePred Meaning) :
    ¬ ∃ budget : Claim → Nat, Computable budget ∧
      ∀ claim, Meaning claim → poll checker producer input claim (budget claim) = true := by
  rintro ⟨budget, computable, covers⟩
  exact undecidableMeaning (computableMeaning_of_budget checker checkerComputable
    producer input inputComputable sound budget computable covers)

namespace Controls

def zeroChecker : Checker Unit Nat where
  check _ certificate := decide (certificate = 0)

theorem exhausted_before_success :
    poll zeroChecker .zero (fun _ => 0) () 0 = false ∧
      poll zeroChecker .zero (fun _ => 0) () 1 = true := by
  simp [poll, Code.evaln, zeroChecker]

/-- Termination producing a candidate alone is insufficient for success. -/
theorem refused_candidate : poll zeroChecker .succ (fun _ => 0) () 1 = false := by
  simp [poll, Code.evaln, zeroChecker]

/-- The obstruction applies to every proposed effective producer for the
existing halting authority, not only to exhaustive certificate enumeration. -/
theorem halting_has_no_computable_success_budget (producer : Code)
    (input : Code → Nat) (inputComputable : Computable input) :
    ¬ ∃ budget : Code → Nat, Computable budget ∧
      ∀ claim, Checker.HaltingMeaning claim →
        poll Checker.haltingTrustBoundaryChecker producer input claim (budget claim) = true :=
  no_computable_success_budget Checker.haltingTrustBoundaryChecker
    Checker.haltingTrustBoundaryChecker_computable producer input inputComputable
    Checker.haltingTrustBoundaryChecker_sound Checker.haltingMeaning_not_computable

end Controls

end Mettapedia.Logic.ProofSearch.SearchBounds
