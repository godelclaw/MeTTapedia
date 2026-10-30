import Mettapedia.Languages.HOLLight.CachedHypothesisList

/-!
# Publication controls for cached source premises

Two different proved equalities close a theorem with both as hypotheses.
Repeating one source, citing a missing cache entry, or supplying an open
assumption cannot publish the conditional result as a closed theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.CachedHypothesisList.Controls
open Mettapedia.Languages.OpenTheory
open GraphExpansion HypothesisExpansion
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def first : Theorem := EqualityExpansion.reflexivity DerivedRules.truthTerm
def second : Theorem := EqualityExpansion.reflexivity first.sequent.concl
def conditional : Theorem := addAssumptionResult first.sequent.concl (assumption second.sequent.concl)
def cache : ProofExecution.State := start [first, second, conditional, assumption first.sequent.concl]

theorem first_checked : checkRefl DerivedRules.truthTerm = some first :=
  EqualityExpansion.reflexivity_checked _

theorem second_checked : checkRefl first.sequent.concl = some second :=
  EqualityExpansion.reflexivity_checked _

theorem different_premises : first.sequent.concl ≠ second.sequent.concl := by decide +kernel

def received := closeAndRequire? emptyAxiomPolicy cache [0, 1] 2 ("cached-list-control", 0)
def repeated := closeAndRequire? emptyAxiomPolicy cache [0, 0] 2 ("cached-list-control", 1)
def missing := closeAndRequire? emptyAxiomPolicy cache [0, 19] 2 ("cached-list-control", 2)
def stillOpen := closeAndRequire? emptyAxiomPolicy cache [3, 1] 2 ("cached-list-control", 3)

theorem received_closed : received.isSome = true := by decide +kernel
theorem repeated_refused : repeated = none := by decide +kernel
theorem missing_refused : missing = none := by decide +kernel
theorem open_source_refused : stillOpen = none := by
  obtain ⟨after, root, computed, _, found, _, _⟩ :=
    close_checked [(3, assumption first.sequent.concl), (1, second)]
      (state := cache) (inputRoot := 2) (input := conditional)
      (start_checked emptyAxiomPolicy _) rfl
      (by intro item member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> rfl)
      (by intro item member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> rfl)
      ("cached-list-control", 3)
  simp only [stillOpen, closeAndRequire?, List.map_cons, List.map_nil] at computed ⊢
  rw [computed]
  apply CachedHypothesisDischarge.requireClosed_hypothesis_refused after root _ found
  apply Finset.ne_empty_of_mem (a := first.sequent.concl)
  simp [result, proveHypResult, Theorem.unionResult, conditional, addAssumptionResult,
    assumption, Theorem.emptyResult, Theorem.preserveAxiomsResult,
    show second.sequent.hyp = ∅ from rfl, different_premises]

theorem received_claim :
    (received.bind fun result => result.1.cache[result.2]?).map (fun fact => (fact.sequent.hyp.card, fact.sequent.concl)) =
      some (0, second.sequent.concl) := by decide +kernel

theorem four_receipts : (received.map (fun result => result.1.receipts.size)) = some 4 := by decide +kernel

theorem checked_publication :
    ∃ after root,
      received = some (after, root) ∧
      BuildChecked emptyAxiomPolicy [first, second, conditional, assumption first.sequent.concl] after ∧
      after.cache[root]? = some (result [first, second] conditional) ∧
      (result [first, second] conditional).sequent.hyp = ∅ ∧ after.receipts.size = 4 := by
  exact closeAndRequire_checked [(0, first), (1, second)]
    (state := cache) (inputRoot := 2) (input := conditional)
    (start_checked emptyAxiomPolicy _) rfl
    (by intro item member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> rfl)
    (by intro item member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> rfl)
    (by intro item member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> rfl)
    (by simp [conditional, addAssumptionResult, assumption, Theorem.emptyResult, Theorem.preserveAxiomsResult])
    ("cached-list-control", 0)

#print axioms received_closed
#print axioms repeated_refused
#print axioms open_source_refused
#print axioms received_claim
#print axioms checked_publication
end Mettapedia.Languages.HOLLight.CachedHypothesisList.Controls
