import Mettapedia.TypeTheory.GradedCheck

/-!
# Verdicts: established, refuted, unknown

A verdict records what a check said about a claim: it was established, it was refuted, or nothing
was learned (`Verdict`). Its meaning is what it licenses (`Verdict.Reads`): an established verdict
licenses the claim, a refuted one its negation, an unknown one nothing. An unknown verdict is an
exhausted budget, a run outside the checker's fragment, or a run that began and never finished; it
is never a refutation.

## The tables are forced

* **Strong Kleene conjunction and disjunction are sound** (`both_reads`, `either_reads`) **and are
  the most informative sound tables** (`both_most_informative`, `either_most_informative`): every
  table that reads the conjunction (disjunction) of what its arguments read either answers
  unknown or agrees with Kleene's. So an unknown conjunct with an established one is unknown, and
  with a refuted one is refuted; nothing else is licensed.
* **Two verdicts on one claim merge as a join** with unknown as the unit (`merge`, `merge_reads`).
  An established and a refuted verdict on one claim conflict; under sound checkers this cannot
  happen (`merge_conflict_unsound`).
* **Unknown becomes refuted only by a refutation** (`unknown_refuted_only_by_refutation`), and the
  closed-world reading of unknown as false is unsound (`closedWorld_unsound`).

## Checkers give verdicts

* The verdict of an authorized outcome reads soundly (`ofOutcome_reads`); an operational fault of a
  run is unknown (`ofRun_reads`).
* **More budget and a stronger authority only refine the verdict** (`budgetRefines_refines`,
  `authorityRefines_refines`, `graded_refines`): unknown may become decided, a decided verdict stays.

## Controls

A bounded search for a square root of `n` among the numbers below its budget is sound at every
budget (`Controls.squareSearch_reads`), monotone in the budget (`Controls.squareSearch_refines`),
unknown for `4` at budget `1` and established at budget `3` (`Controls.four_unknown_then_established`),
and refutes `3` once the budget passes it (`Controls.three_refuted`). Reading its unknown at budget `1`
as false would refute a true claim.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.EvidenceKinds

universe u v w x y z

/-- What a check said about a claim. -/
inductive Verdict where
  | established
  | refuted
  | unknown
  deriving DecidableEq, Repr

namespace Verdict

/-- **What a verdict licenses.** -/
def Reads : Verdict → Prop → Prop
  | established, claim => claim
  | refuted, claim => ¬ claim
  | unknown, _ => True

/-- Strong Kleene conjunction. -/
def both : Verdict → Verdict → Verdict
  | refuted, _ => refuted
  | _, refuted => refuted
  | established, established => established
  | _, _ => unknown

/-- Strong Kleene disjunction. -/
def either : Verdict → Verdict → Verdict
  | established, _ => established
  | _, established => established
  | refuted, refuted => refuted
  | _, _ => unknown

/-- Negation exchanges the decided verdicts. -/
def negate : Verdict → Verdict
  | established => refuted
  | refuted => established
  | unknown => unknown

theorem both_reads {first second : Verdict} {p q : Prop} (hp : Reads first p) (hq : Reads second q) :
    Reads (both first second) (p ∧ q) := by
  cases first <;> cases second <;> simp_all [Reads, both]

theorem either_reads {first second : Verdict} {p q : Prop} (hp : Reads first p) (hq : Reads second q) :
    Reads (either first second) (p ∨ q) := by
  cases first <;> cases second <;> simp_all [Reads, either]

theorem negate_reads {verdict : Verdict} {p : Prop} (hp : Reads verdict p) :
    Reads (negate verdict) (¬ p) := by
  cases verdict <;> simp_all [Reads, negate]

/-- A table for conjunction is sound when it reads the conjunction of what its arguments read. -/
def SoundConjunction (table : Verdict → Verdict → Verdict) : Prop :=
  ∀ first second (p q : Prop), Reads first p → Reads second q → Reads (table first second) (p ∧ q)

/-- A table for disjunction is sound when it reads the disjunction of what its arguments read. -/
def SoundDisjunction (table : Verdict → Verdict → Verdict) : Prop :=
  ∀ first second (p q : Prop), Reads first p → Reads second q → Reads (table first second) (p ∨ q)

theorem both_sound : SoundConjunction both := fun _ _ _ _ => both_reads

theorem either_sound : SoundDisjunction either := fun _ _ _ _ => either_reads

/-- The claim "the verdict is established" is licensed by the verdict. -/
theorem reads_isEstablished (verdict : Verdict) : Reads verdict (verdict = established) := by
  cases verdict <;> simp [Reads]

/-- The claim "the verdict is not refuted" is licensed by the verdict. -/
theorem reads_notRefuted (verdict : Verdict) : Reads verdict (verdict ≠ refuted) := by
  cases verdict <;> simp [Reads]

/-- **Strong Kleene conjunction is the most informative sound table.** -/
theorem both_most_informative {table : Verdict → Verdict → Verdict} (sound : SoundConjunction table)
    (first second : Verdict) : table first second = unknown ∨ table first second = both first second := by
  rcases h : table first second with _ | _ | _
  · -- established: both arguments must be established
    have reads := sound first second _ _ (reads_isEstablished first) (reads_isEstablished second)
    rw [h] at reads
    obtain ⟨rfl, rfl⟩ := reads
    exact Or.inr rfl
  · -- refuted: one argument must be refuted
    have reads := sound first second _ _ (reads_notRefuted first) (reads_notRefuted second)
    rw [h] at reads
    right
    by_cases hf : first = refuted
    · subst hf; rfl
    · have hs : second = refuted := by
        by_contra hs
        exact reads ⟨hf, hs⟩
      subst hs
      cases first <;> rfl
  · exact Or.inl rfl

/-- **Strong Kleene disjunction is the most informative sound table.** -/
theorem either_most_informative {table : Verdict → Verdict → Verdict} (sound : SoundDisjunction table)
    (first second : Verdict) : table first second = unknown ∨ table first second = either first second := by
  rcases h : table first second with _ | _ | _
  · -- established: one argument must be established
    have reads := sound first second _ _ (reads_isEstablished first) (reads_isEstablished second)
    rw [h] at reads
    right
    rcases reads with rfl | rfl
    · rfl
    · cases first <;> rfl
  · -- refuted: both arguments must be refuted
    have reads := sound first second _ _ (reads_notRefuted first) (reads_notRefuted second)
    rw [h] at reads
    simp only [Reads, not_or, ne_eq, not_not] at reads
    obtain ⟨rfl, rfl⟩ := reads
    exact Or.inr rfl
  · exact Or.inl rfl

/-! ## Two verdicts on one claim -/

/-- **Merging two verdicts on one claim**: unknown is the unit; `none` is a conflict. -/
def merge : Verdict → Verdict → Option Verdict
  | unknown, verdict => some verdict
  | verdict, unknown => some verdict
  | established, established => some established
  | refuted, refuted => some refuted
  | _, _ => none

@[simp] theorem merge_unknown_left (verdict : Verdict) : merge unknown verdict = some verdict := by
  cases verdict <;> rfl

@[simp] theorem merge_unknown_right (verdict : Verdict) : merge verdict unknown = some verdict := by
  cases verdict <;> rfl

theorem merge_comm (first second : Verdict) : merge first second = merge second first := by
  cases first <;> cases second <;> rfl

theorem merge_self (verdict : Verdict) : merge verdict verdict = some verdict := by
  cases verdict <;> rfl

/-- Two sound verdicts on one claim merge to a sound verdict. -/
theorem merge_reads {first second : Verdict} {p : Prop} (hf : Reads first p) (hs : Reads second p) :
    ∃ verdict, merge first second = some verdict ∧ Reads verdict p := by
  cases first <;> cases second <;> simp_all [Reads, merge]

/-- **A conflict means an unsound verdict.** -/
theorem merge_conflict_unsound {first second : Verdict} {p : Prop} (hf : Reads first p)
    (hs : Reads second p) : merge first second ≠ none := by
  obtain ⟨verdict, same, _⟩ := merge_reads hf hs
  rw [same]
  exact Option.some_ne_none verdict

/-- **Unknown becomes refuted only by a refutation.** -/
theorem unknown_refuted_only_by_refutation (verdict : Verdict) :
    merge unknown verdict = some refuted ↔ verdict = refuted := by
  simp

/-- **Reading unknown as false is unsound.** -/
theorem closedWorld_unsound : ¬ ∀ p : Prop, Reads unknown p → Reads refuted p := by
  intro closed
  exact closed True trivial trivial

/-- The information order: unknown below every verdict. -/
def Refines (before after : Verdict) : Prop := before = unknown ∨ before = after

theorem Refines.refl (verdict : Verdict) : Refines verdict verdict := Or.inr rfl

theorem Refines.trans {first second third : Verdict} (h₁ : Refines first second)
    (h₂ : Refines second third) : Refines first third := by
  rcases h₁ with rfl | rfl
  · exact Or.inl rfl
  · exact h₂

/-- A merge refines both of its arguments. -/
theorem merge_refines {first second verdict : Verdict} (merged : merge first second = some verdict) :
    Refines first verdict ∧ Refines second verdict := by
  cases first <;> cases second <;> simp_all [merge, Refines]

end Verdict

/-! ## Checkers give verdicts -/

open Mettapedia.TypeTheory.AuthorityTheory

section Outcomes

variable {Established : Sort u} {Refuted : Sort v} {Boundary : Type w} {Incomplete : Type x}

/-- The verdict of an outcome. -/
def Verdict.ofOutcome : Outcome Established Refuted Boundary Incomplete → Verdict
  | .established _ => .established
  | .refuted _ => .refuted
  | .outsideFragment _ => .unknown
  | .incomplete _ => .unknown

/-- **More budget only refines the verdict.** -/
theorem Verdict.budgetRefines_refines {before after : Outcome Established Refuted Boundary Incomplete}
    (refines : Outcome.BudgetRefines before after) :
    Verdict.Refines (Verdict.ofOutcome before) (Verdict.ofOutcome after) := by
  cases refines <;> simp [Verdict.ofOutcome, Verdict.Refines]

/-- **A stronger authority only refines the verdict.** -/
theorem Verdict.authorityRefines_refines {before after : Outcome Established Refuted Boundary Incomplete}
    (refines : Outcome.AuthorityRefines before after) :
    Verdict.Refines (Verdict.ofOutcome before) (Verdict.ofOutcome after) := by
  cases refines <;> simp [Verdict.ofOutcome, Verdict.Refines]

end Outcomes

section Authorized

variable {Judgment : Type u} (authority : Authority.{u, v, w} Judgment)
  {Boundary : Type x} {Incomplete : Type y} {Failure : Type z}

/-- **The verdict of an authorized outcome reads soundly.** -/
theorem Verdict.ofOutcome_reads {judgment : Judgment}
    (outcome : AuthorizedOutcome authority Boundary Incomplete judgment) :
    Verdict.Reads (Verdict.ofOutcome outcome) (authority.Holds judgment) := by
  cases outcome with
  | established evidence => exact authority.evidenceSound judgment evidence
  | refuted obstruction => exact authority.obstructionSound judgment obstruction
  | outsideFragment _ => trivial
  | incomplete _ => trivial

/-- The verdict of a run: an operational fault is unknown. -/
def Verdict.ofRun {judgment : Judgment} :
    RunResult Failure (AuthorizedOutcome authority Boundary Incomplete judgment) → Verdict
  | .ok outcome => Verdict.ofOutcome outcome
  | .fault _ => .unknown

theorem Verdict.ofRun_reads {judgment : Judgment}
    (result : RunResult Failure (AuthorizedOutcome authority Boundary Incomplete judgment)) :
    Verdict.Reads (Verdict.ofRun authority result) (authority.Holds judgment) := by
  cases result with
  | ok outcome => exact Verdict.ofOutcome_reads authority outcome
  | fault _ => trivial

open Mettapedia.TypeTheory.GradedChecking in
/-- **A graded check's verdict only refines as its budget grows.** -/
theorem Verdict.graded_refines (check : GradedCheck authority Boundary Incomplete) (judgment : Judgment)
    {small large : ℕ} (le : small ≤ large) :
    Verdict.Refines (Verdict.ofOutcome (check.run small judgment))
      (Verdict.ofOutcome (check.run large judgment)) :=
  Verdict.budgetRefines_refines (check.mono judgment le)

end Authorized

/-! ## Controls -/

namespace Controls

open Verdict

/-- Search for a square root of `n` among the numbers below the budget. Once the budget passes
`n`, every candidate has been tried. -/
def squareSearch (budget n : ℕ) : Verdict :=
  if (List.range budget).any (fun k => k * k == n) then .established
  else if n < budget then .refuted
  else .unknown

theorem le_self_mul_self (k : ℕ) (hk : 1 ≤ k) : k ≤ k * k := Nat.le_mul_of_pos_left k hk

/-- **The search is sound at every budget.** -/
theorem squareSearch_reads (budget n : ℕ) : Reads (squareSearch budget n) (∃ k, k * k = n) := by
  unfold squareSearch
  split_ifs with found below
  · simp only [List.any_eq_true, List.mem_range, beq_iff_eq] at found
    obtain ⟨k, _, hk⟩ := found
    exact ⟨k, hk⟩
  · simp only [List.any_eq_true, List.mem_range, beq_iff_eq, not_exists, not_and] at found
    rintro ⟨k, hk⟩
    have kle : k ≤ n := by
      rcases Nat.eq_zero_or_pos k with rfl | pos
      · exact Nat.zero_le n
      · exact hk ▸ le_self_mul_self k pos
    exact found k (by omega) hk
  · trivial

/-- **The search only refines as its budget grows.** -/
theorem squareSearch_refines (n : ℕ) {small large : ℕ} (le : small ≤ large) :
    Refines (squareSearch small n) (squareSearch large n) := by
  unfold squareSearch Refines
  by_cases foundSmall : (List.range small).any (fun k => k * k == n) = true
  · have foundLarge : (List.range large).any (fun k => k * k == n) = true := by
      simp only [List.any_eq_true, List.mem_range, beq_iff_eq] at foundSmall ⊢
      obtain ⟨k, lt, hk⟩ := foundSmall
      exact ⟨k, by omega, hk⟩
    simp [foundSmall, foundLarge]
  · by_cases below : n < small
    · have notFoundLarge : ¬ (List.range large).any (fun k => k * k == n) = true := by
        simp only [List.any_eq_true, List.mem_range, beq_iff_eq, not_exists, not_and] at foundSmall ⊢
        intro k _ hk
        have kle : k ≤ n := by
          rcases Nat.eq_zero_or_pos k with rfl | pos
          · exact Nat.zero_le n
          · exact hk ▸ le_self_mul_self k pos
        exact foundSmall k (by omega) hk
      simp [foundSmall, notFoundLarge, below, show n < large by omega]
    · simp [foundSmall, below]

/-- **Unknown at a small budget, established at a larger one**: reading the first answer as false
would refute a true claim. -/
theorem four_unknown_then_established :
    squareSearch 1 4 = .unknown ∧ squareSearch 3 4 = .established ∧ (∃ k, k * k = 4) :=
  ⟨by decide, by decide, ⟨2, rfl⟩⟩

/-- A refutation, once every candidate has been tried. -/
theorem three_refuted : squareSearch 4 3 = .refuted ∧ ¬ ∃ k, k * k = 3 :=
  ⟨by decide, squareSearch_reads 4 3⟩

/-- **Refines, negative**: a decided verdict is maximal in the information order; `established`
does not refine to `refuted`. (`Refines.refl` and `unknown` below every verdict are positive.) -/
theorem established_not_refined_to_refuted : ¬ Refines .established .refuted := by
  unfold Refines; decide

end Controls

end Mettapedia.Logic.EvidenceKinds
