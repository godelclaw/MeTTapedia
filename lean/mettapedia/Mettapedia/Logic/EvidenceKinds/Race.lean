import Mettapedia.Logic.EvidenceKinds.Dependencies
import Mettapedia.Logic.EvidenceKinds.Verdicts

/-!
# Racing proofs: what a race publishes

Several solvers race to close one goal. The goal is one linear occurrence, taken by exactly one
closing commit, which publishes the closing proof's result. Each solver's proof is an alternative
derivation of the goal, so the laws of alternatives in `Dependencies` decide what may be published.

## What the race publishes

* **The closing proof's dependency set is publishable** (`published_sound`, `published_forced`):
  it is sound in every model in which the racers' proofs are.
* **The union of all racers' sets is sound but no better than any racer** (`union_forced`); the
  intersection is unsound unless the sets are nested (`intersection_sound_iff`).
* **The published set depends on the schedule, not only on the goal**
  (`Controls.published_depends_on_schedule`): two schedules close one goal with different
  dependency sets. A consumer that guards revision by dependency sets reads the published set; it
  cannot recompute it from the goal.
* **A later receipt with fewer dependencies is strictly stronger** (`later_receipt_stronger`); a
  store that keeps every receipt and publishes a minimal one gains from it.

## Checks of proofs give verdicts on the goal

A check of a proof decides the judgment "this proof proves the goal" (`checkProof`). Its verdict
on the goal itself is established when the proof checks and unknown otherwise (`goalVerdict`):

* **a rejected proof refutes the proof, never the goal** (`Controls.rejected_proof_not_goal`);
* **an exhausted check is unknown, and is decided by a larger budget**
  (`Controls.identity_steps_need_fuel`); its verdict refines with the budget (`checkProof_refines`);
* a cancelled or crashed racer contributes unknown, which merges away (`Verdict.merge_unknown_left`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.EvidenceKinds

universe u v

/-! ## What the race publishes -/

section Publish

variable {Dep : Type u}

/-- The closing commit of a race: the index of the racer whose proof closed the goal. -/
abbrev Closing (racers : List (Finset Dep)) := Fin racers.length

/-- The dependency set the closing commit publishes. -/
def published {racers : List (Finset Dep)} (closing : Closing racers) : Finset Dep := racers.get closing

/-- **The closing proof's set is publishable in every model.** -/
theorem published_forced {racers : List (Finset Dep)} (closing : Closing racers) :
    AlternativesListSound racers (published closing) :=
  alternativesList_forced.mpr ⟨racers.get closing, List.get_mem racers closing, subset_rfl⟩

theorem published_sound {World : Type u} {holdsAtom : World → Dep → Prop} {claim : World → Prop}
    {racers : List (Finset Dep)} (sounds : ∀ deps ∈ racers, Sound holdsAtom claim deps)
    (closing : Closing racers) : Sound holdsAtom claim (published closing) :=
  published_forced closing World holdsAtom claim sounds

variable [DecidableEq Dep]

/-- The union of the racers' sets. -/
def unionAll : List (Finset Dep) → Finset Dep
  | [] => ∅
  | deps :: rest => deps ∪ unionAll rest

theorem le_unionAll {racers : List (Finset Dep)} {deps : Finset Dep} (member : deps ∈ racers) :
    deps ⊆ unionAll racers := by
  induction racers with
  | nil => simp at member
  | cons head rest ih =>
      rcases List.mem_cons.mp member with rfl | inRest
      · exact Finset.subset_union_left
      · exact (ih inRest).trans Finset.subset_union_right

/-- **The union is sound, and it is no stronger than any single racer.** -/
theorem union_forced {racers : List (Finset Dep)} (nonempty : racers ≠ []) :
    AlternativesListSound racers (unionAll racers) ∧
      ∀ deps ∈ racers, Entails (unionAll racers) deps → unionAll racers = deps := by
  obtain ⟨head, rest, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  refine ⟨alternativesList_forced.mpr ⟨head, List.mem_cons_self, le_unionAll List.mem_cons_self⟩,
    fun deps member entails => ?_⟩
  exact Finset.Subset.antisymm (entails_iff.mp entails) (le_unionAll member)

omit [DecidableEq Dep] in
/-- **A later receipt with fewer dependencies is strictly stronger.** -/
theorem later_receipt_stronger {publishedDeps later : Finset Dep} (sub : later ⊂ publishedDeps) :
    Entails later publishedDeps ∧ ¬ Entails publishedDeps later :=
  ⟨entails_iff.mpr sub.subset, fun entails => sub.not_subset (entails_iff.mp entails)⟩

end Publish

/-! ## Checks of proofs -/

/-- Proofs of evenness: zero, two more, and an identity step that does nothing. -/
inductive EvenProof where
  | zero
  | plusTwo (inner : EvenProof)
  | identity (inner : EvenProof)
  deriving DecidableEq, Repr

namespace EvenProof

/-- The number of steps a check of the proof takes. -/
def size : EvenProof → ℕ
  | zero => 1
  | plusTwo inner => inner.size + 1
  | identity inner => inner.size + 1

/-- Whether the proof proves that `n` is even. -/
def proves : EvenProof → ℕ → Bool
  | zero, n => n == 0
  | plusTwo inner, n => 2 ≤ n && inner.proves (n - 2)
  | identity inner, n => inner.proves n

/-- **A proof that checks is a proof.** -/
theorem proves_sound : ∀ (proof : EvenProof) (n : ℕ), proof.proves n = true → n % 2 = 0
  | zero, n, h => by simp [proves] at h; omega
  | plusTwo inner, n, h => by
      simp only [proves, Bool.and_eq_true, decide_eq_true_eq] at h
      have := proves_sound inner (n - 2) h.2
      omega
  | identity inner, n, h => proves_sound inner n h

end EvenProof

open Verdict

/-- **A fuelled check of the judgment "this proof proves `n` even"**: established, refuted, or
unknown when the fuel runs out first. -/
def checkProof (fuel : ℕ) (proof : EvenProof) (n : ℕ) : Verdict :=
  if fuel < proof.size then .unknown else if proof.proves n then .established else .refuted

theorem checkProof_reads (fuel : ℕ) (proof : EvenProof) (n : ℕ) :
    Reads (checkProof fuel proof n) (proof.proves n = true) := by
  unfold checkProof
  split_ifs with short valid
  · trivial
  · exact valid
  · exact valid

/-- **The check's verdict refines with the fuel.** -/
theorem checkProof_refines (proof : EvenProof) (n : ℕ) {small large : ℕ} (le : small ≤ large) :
    Refines (checkProof small proof n) (checkProof large proof n) := by
  unfold checkProof Refines
  by_cases h : small < proof.size
  · simp [h]
  · have : ¬ large < proof.size := by omega
    simp [h, this]

/-- **The verdict on the goal from one proof**: established when the proof checks, otherwise
unknown. A rejected proof is not a refutation of the goal. -/
def goalVerdict (fuel : ℕ) (proof : EvenProof) (n : ℕ) : Verdict :=
  match checkProof fuel proof n with
  | .established => .established
  | _ => .unknown

theorem goalVerdict_reads (fuel : ℕ) (proof : EvenProof) (n : ℕ) :
    Reads (goalVerdict fuel proof n) (n % 2 = 0) := by
  unfold goalVerdict
  have reads := checkProof_reads fuel proof n
  split
  · next h => rw [h] at reads; exact proof.proves_sound n reads
  · trivial

namespace Controls

/-- The atoms of the race: the checker's profile, and an assumption one solver used. -/
inductive RaceAtom where
  | checkerProfile
  | solverLemma
  deriving DecidableEq, Repr

/-- **The published set depends on the schedule**: one racer's proof rests on the checker alone,
the other's on the checker and a lemma. Either may close the goal. -/
theorem published_depends_on_schedule :
    published (racers := [({.checkerProfile} : Finset RaceAtom), {.checkerProfile, .solverLemma}])
        ⟨0, by decide⟩ = {.checkerProfile} ∧
      published (racers := [({.checkerProfile} : Finset RaceAtom), {.checkerProfile, .solverLemma}])
        ⟨1, by decide⟩ = {.checkerProfile, .solverLemma} ∧
      ({.checkerProfile} : Finset RaceAtom) ≠ {.checkerProfile, .solverLemma} := by
  refine ⟨rfl, rfl, by decide⟩

/-- The two proofs of `even 4` and the bogus one of the race. -/
def direct : EvenProof := .plusTwo (.plusTwo .zero)
def padded : EvenProof := .identity (.identity (.plusTwo (.plusTwo .zero)))
def bogus : EvenProof := .plusTwo .zero

/-- **A rejected proof refutes the proof, never the goal.** -/
theorem rejected_proof_not_goal :
    checkProof 3 bogus 4 = .refuted ∧ goalVerdict 3 bogus 4 = .unknown ∧ 4 % 2 = 0 :=
  ⟨by decide, by decide, rfl⟩

/-- **An exhausted check is unknown, and a larger budget decides it**: the padded proof needs five
steps; at budget three it is unknown, at budget six it is established. -/
theorem identity_steps_need_fuel :
    checkProof 3 padded 4 = .unknown ∧ checkProof 6 padded 4 = .established ∧
      checkProof 3 direct 4 = .established :=
  ⟨by decide, by decide, by decide⟩

/-- **The race's verdict on the goal**: the cancelled padded racer is unknown at budget three and
merges away; the direct racer establishes the goal. -/
theorem race_verdict :
    merge (goalVerdict 3 padded 4) (goalVerdict 3 direct 4) = some .established :=
  by decide

end Controls

end Mettapedia.Logic.EvidenceKinds
