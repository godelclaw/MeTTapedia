import Mettapedia.GSLT.Causality.FactLinearResources

/-!
# Realizing a rule by a match, a removal and an addition

A program can realize one firing of a rule in three steps:

1. **match**: read the rule's reads from the space as it is now, remembering the match;
2. **take**: remove the rule's consumption, failing when it is not all present;
3. **add**: publish the rule's production.

Other programs run between the steps. The take is one atomic removal of the whole consumption, and it fails
on absence. The match is never checked again.

## When this realization is exact

Suppose no rule consumes a declared fact and every read of every rule is a fact. Then:

* **Every state the program reaches stands for a state of the rule system** (`realized_simulated`). The
  state it stands for is its atoms plus the productions it still owes. In particular, once nothing is
  pending, the program's space is a state the rules reach (`completed_reachable`).
* **Every firing of the rule system is realized** by its three steps (`fire_realized`).

The reason is that facts only accumulate: a read made at an earlier snapshot still holds when the take
commits, so a stale match never matters.

## Where it is not exact

* **Linear reads: write skew** (`writeSkew_realized`, `writeSkew_atomic_never`). One rule reads `x` and takes
  `y`; another reads `y` and takes `x`. Atomically, whichever fires first disables the other. Realized, both
  match first and then both take, ending with both results. The takes are exclusive; the failure is that the
  reads are not validated.
* **A removal that does not report absence: double spend** (`blind_double_spend`). Two consumers match one
  token; the first removal takes it, the second removes nothing and continues, and both produce.
* **A consumption taken in several removals** deadlocks (`FactLinearControls.sequential_deadlock`), and
  giving back a half-held resource turns the deadlock into a cycle that never yields a result
  (`releasing_cycle`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

universe uRes uRule

namespace System

variable {R : Type uRes} [DecidableEq R] (S : System.{uRes, uRule} R) [DecidableEq S.Entry]

/-! ## The realization -/

/-- A state of the realization: the space's atoms, the matches made and not yet taken, and the firings that
have taken and not yet added. -/
structure Realized where
  atoms : Multiset R
  matched : Multiset S.Entry
  owed : Multiset S.Entry

/-- **The steps of the realization**, with a removal that fails on absence. -/
inductive RealizedStep : S.Realized → S.Realized → Prop
  /-- Match: the reads are present now; remember the match. -/
  | matched (state : S.Realized) (entry : S.Entry) (reads : S.read entry.2 ≤ state.atoms) :
      RealizedStep state ⟨state.atoms, entry ::ₘ state.matched, state.owed⟩
  /-- Take: a remembered match removes its consumption, which must all be present. Its reads are not
  checked again. -/
  | taken (state : S.Realized) (entry : S.Entry) (remembered : entry ∈ state.matched)
      (present : S.consume entry.2 ≤ state.atoms) :
      RealizedStep state ⟨state.atoms - S.consume entry.2, state.matched.erase entry,
        entry ::ₘ state.owed⟩
  /-- Add: a firing that took publishes its production. -/
  | added (state : S.Realized) (entry : S.Entry) (taken : entry ∈ state.owed) :
      RealizedStep state ⟨state.atoms + S.produce entry.2, state.matched, state.owed.erase entry⟩

/-- A space with nothing pending. -/
def embed (M : Multiset R) : S.Realized := ⟨M, 0, 0⟩

/-- **What a realized state stands for**: its atoms, plus the productions it still owes. -/
def abstraction (state : S.Realized) : Multiset R :=
  state.atoms + state.owed.bind fun entry => S.produce entry.2

omit [DecidableEq R] [DecidableEq S.Entry] in
@[simp] theorem abstraction_embed (M : Multiset R) : S.abstraction (S.embed M) = M := by
  simp [abstraction, embed]

/-! ## Exactness when every read is a fact -/

section Exact

variable {fact : R → Prop}

/-- The invariant: every remembered match's reads are still present. -/
def MatchesHold (state : S.Realized) : Prop :=
  ∀ entry ∈ state.matched, S.read entry.2 ≤ state.atoms

omit [DecidableEq S.Entry] in
/-- Removing a consumption that holds no fact keeps every bag of facts that was present. -/
theorem facts_le_sub (respects : S.ConsumesNoFacts fact) {M F : Multiset R} {entry : S.Entry}
    (allFacts : ∀ r ∈ F, fact r) (le : F ≤ M) : F ≤ M - S.consume entry.2 := by
  rw [Multiset.le_iff_count] at le ⊢
  intro r
  by_cases inF : r ∈ F
  · have none : (S.consume entry.2).count r = 0 :=
      Multiset.count_eq_zero.mpr fun member => respects entry.2 r member (allFacts r inF)
    rw [Multiset.count_sub, none, Nat.sub_zero]
    exact le r
  · rw [Multiset.count_eq_zero.mpr inF]
    exact Nat.zero_le _

omit [DecidableEq S.Entry] in
/-- A consumption without facts and reads that are all facts, each present, are present together. -/
theorem enables_of_parts (respects : S.ConsumesNoFacts fact) {M : Multiset R} {entry : S.Entry}
    (readsFacts : ∀ r ∈ S.read entry.2, fact r) (consumed : S.consume entry.2 ≤ M)
    (reads : S.read entry.2 ≤ M) : S.Enables M entry.2 := by
  unfold Enables
  rw [Multiset.le_iff_count] at consumed reads ⊢
  intro r
  rw [Multiset.count_add]
  by_cases inReads : r ∈ S.read entry.2
  · have none : (S.consume entry.2).count r = 0 :=
      Multiset.count_eq_zero.mpr fun member => respects entry.2 r member (readsFacts r inReads)
    rw [none, Nat.zero_add]
    exact reads r
  · rw [Multiset.count_eq_zero.mpr inReads, Nat.add_zero]
    exact consumed r

omit [DecidableEq R] in
theorem bind_erase_add {owed : Multiset S.Entry} {entry : S.Entry} (member : entry ∈ owed) :
    S.produce entry.2 + (owed.erase entry).bind (fun e => S.produce e.2) =
      owed.bind fun e => S.produce e.2 := by
  conv_rhs => rw [← Multiset.cons_erase member]
  rw [Multiset.cons_bind]

/-- **One step of the realization is a stutter or one firing**, and it keeps the invariant. -/
theorem realizedStep_simulated (respects : S.ConsumesNoFacts fact)
    (readsFacts : ∀ (entry : S.Entry), ∀ r ∈ S.read entry.2, fact r) {state next : S.Realized}
    (step : S.RealizedStep state next) (holds : S.MatchesHold state) :
    (S.abstraction next = S.abstraction state ∨
      S.theory.rewrites (S.abstraction state) (S.abstraction next)) ∧ S.MatchesHold next := by
  cases step with
  | matched entry reads =>
      refine ⟨Or.inl rfl, ?_⟩
      intro other member
      rcases Multiset.mem_cons.mp member with rfl | earlier
      · exact reads
      · exact holds other earlier
  | taken entry remembered present =>
      refine ⟨Or.inr ⟨entry.1, entry.2, ?_, ?_⟩, ?_⟩
      · exact le_trans (S.enables_of_parts respects (readsFacts entry) present
          (holds entry remembered)) (Multiset.le_add_right _ _)
      · simp only [abstraction, fire, Multiset.cons_bind]
        rw [← tsub_add_eq_add_tsub present, add_assoc]
        exact congrArg _ (add_comm _ _)
      · intro other member
        exact S.facts_le_sub respects (readsFacts other) (holds other (Multiset.mem_of_mem_erase member))
  | added entry taken =>
      refine ⟨Or.inl ?_, ?_⟩
      · simp only [abstraction]
        rw [← S.bind_erase_add taken]
        abel
      · intro other member
        exact le_trans (holds other member) (Multiset.le_add_right _ _)

/-- **Every state the realization reaches stands for a state of the rule system**, when no rule consumes a
fact and every read is a fact. -/
theorem realized_simulated (respects : S.ConsumesNoFacts fact)
    (readsFacts : ∀ (entry : S.Entry), ∀ r ∈ S.read entry.2, fact r) {M : Multiset R}
    {state : S.Realized} (run : Relation.ReflTransGen S.RealizedStep (S.embed M) state) :
    Relation.ReflTransGen S.theory.rewrites M (S.abstraction state) ∧ S.MatchesHold state := by
  induction run with
  | refl =>
      refine ⟨by rw [abstraction_embed]; exact Relation.ReflTransGen.refl, ?_⟩
      intro entry member
      simp [embed] at member
  | tail _ step previous =>
      obtain ⟨reach, holds⟩ := previous
      obtain ⟨moved, holdsNext⟩ := S.realizedStep_simulated respects readsFacts step holds
      refine ⟨?_, holdsNext⟩
      rcases moved with same | fired
      · rw [same]
        exact reach
      · exact reach.tail fired

/-- **Once nothing is pending, the program's space is a state the rules reach.** -/
theorem completed_reachable (respects : S.ConsumesNoFacts fact)
    (readsFacts : ∀ (entry : S.Entry), ∀ r ∈ S.read entry.2, fact r) {M N : Multiset R}
    (run : Relation.ReflTransGen S.RealizedStep (S.embed M) (S.embed N)) :
    Relation.ReflTransGen S.theory.rewrites M N := by
  have reach := (S.realized_simulated respects readsFacts run).1
  rwa [abstraction_embed] at reach

end Exact

/-- **Every firing is realized** by a match, a take and an addition. -/
theorem fire_realized {M : Multiset R} {site : S.Site} {i : S.Instance site} (enabled : S.Enables M i) :
    Relation.ReflTransGen S.RealizedStep (S.embed M) (S.embed (S.fire M i)) := by
  have reads : S.read i ≤ M := le_trans (Multiset.le_add_left _ _) enabled
  have consumed : S.consume i ≤ M := le_trans (Multiset.le_add_right _ _) enabled
  let entry : S.Entry := ⟨site, i⟩
  have first := RealizedStep.matched (S := S) (S.embed M) entry reads
  have second := RealizedStep.taken (S := S) ⟨M, entry ::ₘ 0, 0⟩ entry
    (Multiset.mem_cons_self entry 0) consumed
  have third := RealizedStep.added (S := S)
    ⟨M - S.consume i, (entry ::ₘ (0 : Multiset S.Entry)).erase entry, entry ::ₘ 0⟩ entry
    (Multiset.mem_cons_self entry 0)
  have done : S.embed (S.fire M i) =
      ⟨M - S.consume i + S.produce entry.2, (entry ::ₘ (0 : Multiset S.Entry)).erase entry,
        (entry ::ₘ (0 : Multiset S.Entry)).erase entry⟩ := by
    simp [embed, fire, entry]
  rw [done]
  exact ((Relation.ReflTransGen.single first).tail second).tail third

/-! ## A removal that does not report absence -/

/-- **The steps of the realization with a removal that never fails**: removing what is absent removes
nothing, and the program continues. -/
inductive BlindStep : S.Realized → S.Realized → Prop
  | matched (state : S.Realized) (entry : S.Entry) (reads : S.read entry.2 ≤ state.atoms) :
      BlindStep state ⟨state.atoms, entry ::ₘ state.matched, state.owed⟩
  | taken (state : S.Realized) (entry : S.Entry) (remembered : entry ∈ state.matched) :
      BlindStep state ⟨state.atoms - S.consume entry.2, state.matched.erase entry, entry ::ₘ state.owed⟩
  | added (state : S.Realized) (entry : S.Entry) (taken : entry ∈ state.owed) :
      BlindStep state ⟨state.atoms + S.produce entry.2, state.matched, state.owed.erase entry⟩

end System

/-! ## Controls -/

namespace MatchRemoveControls

open Mettapedia.GSLT.Causality.ResourceInteraction.System

/-! ### Write skew -/

/-- Resources: two shared atoms and two results. -/
inductive Skew where
  | x | y | p | q
  deriving DecidableEq, Repr

open Skew

/-- Rule `true` reads `x` and takes `y`, producing `p`; rule `false` reads `y` and takes `x`, producing
`q`. -/
def skew : System Skew where
  Site := Unit
  Instance := fun _ => Bool
  consume := fun (first : Bool) => match first with
    | true => {y}
    | false => {x}
  read := fun (first : Bool) => match first with
    | true => {x}
    | false => {y}
  produce := fun (first : Bool) => match first with
    | true => {p}
    | false => {q}

instance : DecidableEq skew.Entry := inferInstanceAs (DecidableEq (Σ _ : Unit, Bool))

def ruleA : skew.Entry := ⟨(), true⟩
def ruleB : skew.Entry := ⟨(), false⟩

theorem skew_reachable {M : Multiset Skew}
    (run : Relation.ReflTransGen skew.theory.rewrites ({x, y} : Multiset Skew) M) :
    M = {x, y} ∨ M = {x, p} ∨ M = {y, q} := by
  induction run with
  | refl => exact Or.inl rfl
  | tail _ step previous =>
    obtain ⟨site, first, enabled, rfl⟩ := step
    cases site
    rcases previous with rfl | rfl | rfl <;> cases first <;> revert enabled <;>
      unfold System.Enables System.fire <;> decide

/-- **Atomically, the two results never appear together.** -/
theorem writeSkew_atomic_never {M : Multiset Skew}
    (run : Relation.ReflTransGen skew.theory.rewrites ({x, y} : Multiset Skew) M) : ¬ (p ∈ M ∧ q ∈ M) := by
  rcases skew_reachable run with rfl | rfl | rfl <;> decide

/-- **Realized by match, take and add, both results appear**: both rules match first, then both take. Each
take succeeds, since each removes a different atom. -/
theorem writeSkew_realized :
    Relation.ReflTransGen skew.RealizedStep (skew.embed {x, y}) (skew.embed {p, q}) := by
  have s1 := RealizedStep.matched (S := skew) (skew.embed {x, y}) ruleA (by decide)
  have s2 := RealizedStep.matched (S := skew) ⟨{x, y}, {ruleA}, 0⟩ ruleB (by decide)
  have s3 := RealizedStep.taken (S := skew) ⟨{x, y}, {ruleB, ruleA}, 0⟩ ruleA (by decide) (by decide)
  have s4 := RealizedStep.taken (S := skew) ⟨({x, y} : Multiset Skew) - {y}, ({ruleB, ruleA} : Multiset skew.Entry).erase ruleA, {ruleA}⟩
    ruleB (by decide) (by decide)
  have s5 := RealizedStep.added (S := skew)
    ⟨({x, y} : Multiset Skew) - {y} - {x}, (({ruleB, ruleA} : Multiset skew.Entry).erase ruleA).erase ruleB, {ruleB, ruleA}⟩
    ruleA (by decide)
  have s6 := RealizedStep.added (S := skew)
    ⟨({x, y} : Multiset Skew) - {y} - {x} + {p}, (({ruleB, ruleA} : Multiset skew.Entry).erase ruleA).erase ruleB,
      ({ruleB, ruleA} : Multiset skew.Entry).erase ruleA⟩
    ruleB (by decide)
  have done : skew.embed {p, q} =
      ⟨({x, y} : Multiset Skew) - {y} - {x} + {p} + {q}, (({ruleB, ruleA} : Multiset skew.Entry).erase ruleA).erase ruleB,
        (({ruleB, ruleA} : Multiset skew.Entry).erase ruleA).erase ruleB⟩ := by
    simp only [embed, Realized.mk.injEq]
    refine ⟨by decide, by decide, by decide⟩
  rw [done]
  exact (((((Relation.ReflTransGen.single s1).tail s2).tail s3).tail s4).tail s5).tail s6

/-- The reads of the skew rules are not facts: each reads what the other takes. -/
theorem skew_reads_linear : ¬ ∃ fact : Skew → Prop, skew.ConsumesNoFacts fact ∧
    ∀ (entry : skew.Entry), ∀ r ∈ skew.read entry.2, fact r := by
  rintro ⟨fact, respects, readsFacts⟩
  exact respects (site := ()) false x (by decide) (readsFacts ruleA x (by decide))

/-! ### Double spend with a removal that never fails -/

/-- Resources: a token and two receipts. -/
inductive Spend where
  | token | left | right
  deriving DecidableEq, Repr

/-- Two consumers of the token. -/
def spend : System Spend where
  Site := Unit
  Instance := fun _ => Bool
  consume := fun _ => {Spend.token}
  read := fun _ => 0
  produce := fun (first : Bool) => match first with
    | true => {Spend.left}
    | false => {Spend.right}

instance : DecidableEq spend.Entry := inferInstanceAs (DecidableEq (Σ _ : Unit, Bool))

def consumerL : spend.Entry := ⟨(), true⟩
def consumerR : spend.Entry := ⟨(), false⟩

/-- **Atomically, one token yields one receipt.** -/
theorem spend_atomic_one {M : Multiset Spend}
    (run : Relation.ReflTransGen spend.theory.rewrites ({Spend.token} : Multiset Spend) M) :
    ¬ (Spend.left ∈ M ∧ Spend.right ∈ M) := by
  have reach : M = {Spend.token} ∨ M = {Spend.left} ∨ M = {Spend.right} := by
    induction run with
    | refl => exact Or.inl rfl
    | tail _ step previous =>
      obtain ⟨site, first, enabled, rfl⟩ := step
      cases site
      rcases previous with rfl | rfl | rfl <;> cases first <;> revert enabled <;>
        unfold System.Enables System.fire <;> decide
  rcases reach with rfl | rfl | rfl <;> decide

/-- **With a removal that fails on absence, the second consumer cannot take**: after the first take, the
token is gone. -/
theorem reporting_second_take_refused :
    ¬ spend.consume consumerR.2 ≤ ({Spend.token} : Multiset Spend) - spend.consume consumerL.2 := by
  decide

/-- **With a removal that never fails, one token yields both receipts.** -/
theorem blind_double_spend :
    Relation.ReflTransGen spend.BlindStep (spend.embed {Spend.token})
      (spend.embed {Spend.left, Spend.right}) := by
  have s1 := BlindStep.matched (S := spend) (spend.embed {Spend.token}) consumerL (by decide)
  have s2 := BlindStep.matched (S := spend) ⟨{Spend.token}, {consumerL}, 0⟩ consumerR (by decide)
  have s3 := BlindStep.taken (S := spend) ⟨{Spend.token}, {consumerR, consumerL}, 0⟩ consumerL (by decide)
  have s4 := BlindStep.taken (S := spend)
    ⟨({Spend.token} : Multiset Spend) - {Spend.token},
      ({consumerR, consumerL} : Multiset spend.Entry).erase consumerL, {consumerL}⟩ consumerR (by decide)
  have s5 := BlindStep.added (S := spend)
    ⟨({Spend.token} : Multiset Spend) - {Spend.token} - {Spend.token},
      (({consumerR, consumerL} : Multiset spend.Entry).erase consumerL).erase consumerR,
      {consumerR, consumerL}⟩ consumerL (by decide)
  have s6 := BlindStep.added (S := spend)
    ⟨({Spend.token} : Multiset Spend) - {Spend.token} - {Spend.token} + {Spend.left},
      (({consumerR, consumerL} : Multiset spend.Entry).erase consumerL).erase consumerR,
      ({consumerR, consumerL} : Multiset spend.Entry).erase consumerL⟩ consumerR (by decide)
  have done : spend.embed {Spend.left, Spend.right} =
      ⟨({Spend.token} : Multiset Spend) - {Spend.token} - {Spend.token} + {Spend.left} + {Spend.right},
        (({consumerR, consumerL} : Multiset spend.Entry).erase consumerL).erase consumerR,
        (({consumerR, consumerL} : Multiset spend.Entry).erase consumerL).erase consumerR⟩ := by
    simp only [embed, Realized.mk.injEq]
    refine ⟨by decide, by decide, by decide⟩
  rw [done]
  exact (((((Relation.ReflTransGen.single s1).tail s2).tail s3).tail s4).tail s5).tail s6

/-! ### Crossed joins that give back what they hold -/

open FactLinearControls FactLinearControls.Crossed

/-- The half steps of the crossed joins, and the two steps that give back a held input. -/
inductive ReleaseStep where
  | half (step : HalfStep)
  | release₁ | release₂
  deriving DecidableEq, Repr

/-- **Crossed joins that give back what they hold**: each join takes one input at a time, and a join holding
one input may return it. -/
def releasing : System Crossed where
  Site := Unit
  Instance := fun _ => ReleaseStep
  consume := fun (step : ReleaseStep) => match step with
    | .half step => sequential.consume (site := ()) step
    | .release₁ => {holder₁}
    | .release₂ => {holder₂}
  read := fun _ => 0
  produce := fun (step : ReleaseStep) => match step with
    | .half step => sequential.produce (site := ()) step
    | .release₁ => {receiver₁, a}
    | .release₂ => {receiver₂, b}

/-- **Giving back turns the deadlock into a cycle**: a run from the start reaches the state where each join
holds half, and returns to the start; no state on it holds a result. Repeating it gives runs of every length
that never yield a result. -/
theorem releasing_cycle :
    Relation.ReflTransGen releasing.theory.rewrites start ({holder₁, holder₂} : Multiset Crossed) ∧
      Relation.ReflTransGen releasing.theory.rewrites ({holder₁, holder₂} : Multiset Crossed) start ∧
      ¬ HasResult ({holder₁, holder₂} : Multiset Crossed) ∧
      ¬ HasResult ({holder₁, receiver₂, b} : Multiset Crossed) ∧
      ¬ HasResult ({receiver₁, a, holder₂} : Multiset Crossed) ∧ ¬ HasResult start := by
  refine ⟨?_, ?_, by decide, by decide, by decide, by decide⟩
  · refine Relation.ReflTransGen.tail (b := ({holder₁, receiver₂, b} : Multiset Crossed)) ?_
      ⟨(), .half HalfStep.take₂b, by unfold System.Enables; decide, by unfold System.fire; decide⟩
    exact Relation.ReflTransGen.single
      ⟨(), .half HalfStep.take₁a, by unfold System.Enables; decide, by unfold System.fire; decide⟩
  · refine Relation.ReflTransGen.tail (b := ({receiver₁, a, holder₂} : Multiset Crossed)) ?_
      ⟨(), .release₂, by unfold System.Enables; decide, by unfold System.fire start; decide⟩
    exact Relation.ReflTransGen.single
      ⟨(), .release₁, by unfold System.Enables; decide, by unfold System.fire; decide⟩

end MatchRemoveControls

end Mettapedia.GSLT.Causality.ResourceInteraction
