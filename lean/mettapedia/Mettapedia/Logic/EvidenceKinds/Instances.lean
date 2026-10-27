import Mettapedia.Logic.EvidenceKinds.Dependencies
import Mettapedia.PLN.WorldModel.EvidenceContracts

/-!
# Tested results: instances, coverage, and test cases as observations

A test runs a claim's predicate on chosen cases. A passing test establishes the instance at that
case, under whatever the run rests on (the harness is an executor, so a test is an admitted run of
an instance). It says nothing about the cases that were not run. This module states the laws of
tested results in two readings: as instance results, and as PLN evidence for the universal claim.

## Tests as instance results

* **Tests of one claim combine by union of cases** (`Tested.union`); a proof of the universal
  claim gives every test inside its domain (`Tested.of_universal`).
* **Coverage is exactly what turns tests into a proof** (`tested_to_universal_iff`): tests of
  `cases` license the universal claim over `domain` for every predicate exactly when
  `domain ⊆ cases`. With a proof of coverage under its own dependencies, the step is sound under
  the union (`universal_of_cover_sound`). So "tested" never becomes "proved" without a coverage
  proof, and on an infinite domain never (`Controls.tested_not_universal`).
* **A failing case refutes the universal claim** (`failing_case_refutes`): the asymmetry between
  passing and failing tests.

## Tests as observations

Each case is an identified observation of the predicate at that case (`testEvidence`, the ledger
evidence of `EvidenceContracts`). Then:

* **Rerunning a case adds nothing** (`testEvidence_rerun`), while adding the counts of a rerun
  counts it twice (`rerun_added_double_counts`).
* **Passing tests give one positive observation per case** (`testEvidence_of_tested`).
* **On a finite domain a proof of the universal claim is the exhaustive ledger**
  (`testEvidence_of_universal`): it absorbs every test inside the domain by union
  (`exhaustive_absorbs_tests`), and adding its counts to those of a test counts the tested case
  twice (`exhaustive_plus_tests_double_counts`). This is the lawful sense of "a proof gives
  evidence of maximal strength": a ledger, not a count to be added.
* **A failing test against a proof refutes one of the proof's dependencies**
  (`failing_test_refutes_dependency`): the proof is not contradicted, its assumptions are.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.EvidenceKinds

open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceSpaces.Evidence
open Mettapedia.PLN.WorldModel.EvidenceContracts

universe u v

section Instances

variable {X : Type u}

/-- A claim over a domain: the predicate holds at every element of the domain. -/
def Universal (domain : Set X) (P : X → Prop) : Prop := ∀ x ∈ domain, P x

/-- **Tested**: the predicate holds at every case that was run. -/
def Tested (cases : Finset X) (P : X → Prop) : Prop := ∀ x ∈ cases, P x

theorem Tested.union [DecidableEq X] {first second : Finset X} {P : X → Prop}
    (h₁ : Tested first P) (h₂ : Tested second P) : Tested (first ∪ second) P := by
  intro x member
  rcases Finset.mem_union.mp member with inFirst | inSecond
  · exact h₁ x inFirst
  · exact h₂ x inSecond

theorem Tested.of_universal {domain : Set X} {cases : Finset X} {P : X → Prop}
    (inside : (↑cases : Set X) ⊆ domain) (proved : Universal domain P) : Tested cases P :=
  fun x member => proved x (inside member)

theorem universal_of_cover {domain : Set X} {cases : Finset X} {P : X → Prop}
    (cover : domain ⊆ ↑cases) (tested : Tested cases P) : Universal domain P :=
  fun x member => tested x (cover member)

/-- **Coverage is exactly what turns tests into a proof.** -/
theorem tested_to_universal_iff {domain : Set X} {cases : Finset X} :
    (∀ P : X → Prop, Tested cases P → Universal domain P) ↔ domain ⊆ ↑cases := by
  constructor
  · intro licensed x member
    exact licensed (fun y => y ∈ cases) (fun _ inCases => inCases) x member
  · intro cover P tested
    exact universal_of_cover cover tested

/-- **A failing case refutes the universal claim.** -/
theorem failing_case_refutes {domain : Set X} {P : X → Prop} {x : X} (member : x ∈ domain)
    (fails : ¬ P x) : ¬ Universal domain P :=
  fun proved => fails (proved x member)

/-- With dependencies: tests under the harness's dependencies and a coverage proof under its own
give the universal claim under the union. -/
theorem universal_of_cover_sound {World : Type v} {Dep : Type u} [DecidableEq Dep]
    {holdsAtom : World → Dep → Prop} {domain : World → Set X} {cases : Finset X}
    {P : World → X → Prop} {testDeps coverDeps : Finset Dep}
    (tested : Sound holdsAtom (fun world => Tested cases (P world)) testDeps)
    (cover : Sound holdsAtom (fun world => domain world ⊆ ↑cases) coverDeps) :
    Sound holdsAtom (fun world => Universal (domain world) (P world)) (testDeps ∪ coverDeps) :=
  Sound.rule (fun _ testedHere coverHere => universal_of_cover coverHere testedHere) tested cover

end Instances

/-! ## Tests as observations -/

section Observations

variable {X : Type u} [DecidableEq X]

/-- **Test outcomes as identified observations**: each case is one observation of the predicate
at that case. -/
def testEvidence (P : X → Bool) (cases : Finset X) : Evidence ℕ := ledgerEvidence id P cases

/-- **Rerunning a case adds nothing.** -/
theorem testEvidence_rerun (P : X → Bool) (cases : Finset X) :
    testEvidence P (cases ∪ cases) = testEvidence P cases := by
  rw [Finset.union_idempotent]

/-- **Adding the counts of a rerun counts it twice.** -/
theorem rerun_added_double_counts (P : X → Bool) {cases : Finset X} (nonempty : cases.Nonempty) :
    testEvidence P cases + testEvidence P cases ≠ testEvidence P (cases ∪ cases) := by
  intro exact
  have disjoint := (additive_revision_exact_iff_disjoint id P cases cases).mp exact
  rw [disjoint_self, Finset.bot_eq_empty] at disjoint
  exact nonempty.ne_empty disjoint

omit [DecidableEq X] in
/-- Each passing case is one positive observation. -/
theorem testEvidence_of_tested {P : X → Bool} {cases : Finset X}
    (tested : Tested cases fun x => P x = true) : testEvidence P cases = ⟨cases.card, 0⟩ := by
  unfold testEvidence ledgerEvidence
  rw [Finset.sum_congr rfl fun x member => by
    show sampleEvidence P (id x) = positive
    simp [sampleEvidence, tested x member]]
  rw [Finset.sum_const]
  show cases.card • (⟨1, 0⟩ : Evidence ℕ) = _
  rw [nsmul_mk]
  simp

omit [DecidableEq X] in
/-- **On a finite domain, a proof of the universal claim is the exhaustive ledger.** -/
theorem testEvidence_of_universal {P : X → Bool} {domain : Finset X}
    (proved : Universal (↑domain) fun x => P x = true) :
    testEvidence P domain = ⟨domain.card, 0⟩ :=
  testEvidence_of_tested (Tested.of_universal subset_rfl proved)

/-- **The exhaustive ledger absorbs every test inside the domain.** -/
theorem exhaustive_absorbs_tests (P : X → Bool) {domain cases : Finset X} (inside : cases ⊆ domain) :
    testEvidence P (domain ∪ cases) = testEvidence P domain := by
  rw [Finset.union_eq_left.mpr inside]

/-- **Adding a proof's counts to a test's counts counts the tested cases twice.** -/
theorem exhaustive_plus_tests_double_counts (P : X → Bool) {domain cases : Finset X}
    (inside : cases ⊆ domain) (nonempty : cases.Nonempty) :
    testEvidence P domain + testEvidence P cases ≠ testEvidence P (domain ∪ cases) := by
  intro exact
  have disjoint := (additive_revision_exact_iff_disjoint id P domain cases).mp exact
  obtain ⟨x, member⟩ := nonempty
  exact Finset.disjoint_left.mp disjoint (inside member) member

omit [DecidableEq X] in
/-- **A failing test against a proof refutes one of the proof's dependencies.** -/
theorem failing_test_refutes_dependency {World : Type v} {Dep : Type u}
    {holdsAtom : World → Dep → Prop} {domain : World → Set X} {P : World → X → Prop}
    {deps : Finset Dep} (proof : Sound holdsAtom (fun world => Universal (domain world) (P world)) deps)
    {world : World} {x : X} (member : x ∈ domain world) (fails : ¬ P world x) :
    ∃ atom ∈ deps, ¬ holdsAtom world atom :=
  proof.counterexample (failing_case_refutes member fails)

end Observations

/-! ## Controls -/

namespace Controls

/-- **Passing tests do not prove the universal claim**: `n < 5` passes on the cases `0, …, 4` and
fails at `5`. -/
theorem tested_not_universal :
    Tested (Finset.range 5) (fun n => n < 5) ∧ ¬ Universal Set.univ (fun n : ℕ => n < 5) := by
  refine ⟨fun _ member => Finset.mem_range.mp member, ?_⟩
  exact failing_case_refutes (Set.mem_univ 5) (by decide)

/-- **On a covered finite domain, the same tests are a proof.** -/
theorem tested_universal_on_covered_domain :
    Universal (↑(Finset.range 5)) (fun n : ℕ => n < 5) :=
  universal_of_cover subset_rfl fun _ member => Finset.mem_range.mp member

/-- The tested cases as observations: five positive observations, and a rerun adds none. -/
theorem five_observations :
    testEvidence (fun n : ℕ => decide (n < 5)) (Finset.range 5) = ⟨5, 0⟩ ∧
      testEvidence (fun n : ℕ => decide (n < 5)) (Finset.range 5 ∪ Finset.range 5) = ⟨5, 0⟩ := by
  have five : testEvidence (fun n : ℕ => decide (n < 5)) (Finset.range 5) = ⟨5, 0⟩ := by
    rw [testEvidence_of_tested (fun n member => by simpa using Finset.mem_range.mp member)]
    simp
  exact ⟨five, (testEvidence_rerun _ _).trans five⟩

/-- A failing case is a negative observation. -/
theorem failing_case_negative :
    testEvidence (fun n : ℕ => decide (n < 5)) {5} = ⟨0, 1⟩ := by
  simp [testEvidence, ledgerEvidence, sampleEvidence, negative]

end Controls

end Mettapedia.Logic.EvidenceKinds
