import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder.WaveTranslation
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Isolation

/-!
# Committed answers, and reading a count back

`countsEachOnce` is not the subject here. Two claims about a joint committed
run fail, and each failure has a form that holds. A count read back from `k`
copies is `k` times the source, and a `Splits` quotient returns the source.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Logic.HostingStyles.Weighted
open Mettapedia.GSLT.Dynamics.JoinAggregation
open Mettapedia.Logic.EvidenceStateInsufficiency

section Runs

variable {Location : Type} {Value Answer : Type}
  [DecidableEq Location] [Zero Value] [Add Value] [SepAlgebra Value]

/-- No `step` constructor anywhere in the region. -/
def stepFree : Region Location Value Answer → Prop
  | .fail => True
  | .answer _ => True
  | .step _ _ => False
  | .orElse left right => stepFree left ∧ stepFree right

/-- On every `orElse`, earlier writes miss both later reads and later writes.
A `step` node asks this only of what follows it. -/
def footprintsOrdered : Region Location Value Answer → Prop
  | .fail => True
  | .answer _ => True
  | .step _ rest => footprintsOrdered rest
  | .orElse left right =>
      footprintsOrdered left ∧ footprintsOrdered right ∧
        Disjoint left.writes (right.reads ∪ right.writes)

/-- **Positive.** With no step anywhere, branch-local answers are the committed
answers and the committed state is the snapshot. -/
theorem stepFree_committed_eq (region : Region Location Value Answer) :
    stepFree region → ∀ world : Location → Value,
      (region.branchLocal world).map Prod.fst = (region.committed world).1 ∧
        (region.committed world).2 = world := by
  induction region with
  | fail =>
    intro _ world
    simp [Region.branchLocal, Region.committed]
  | answer _ =>
    intro _ world
    simp [Region.branchLocal, Region.committed]
  | step _ _ _ =>
    intro free
    unfold stepFree at free
    exact False.elim free
  | orElse left right ihL ihR =>
    intro free world
    rcases free with ⟨freeL, freeR⟩
    rcases ihL freeL world with ⟨ansL, stateL⟩
    rcases ihR freeR world with ⟨ansR, stateR⟩
    refine ⟨?answers, ?state⟩
    · calc
        ((Region.orElse left right).branchLocal world).map Prod.fst
            = (left.branchLocal world).map Prod.fst ++
                (right.branchLocal world).map Prod.fst := by
              simp [Region.branchLocal, List.map_append]
        _ = (left.committed world).1 ++ (right.committed world).1 := by
              rw [ansL, ansR]
        _ = (left.committed world).1 ++
              (right.committed (left.committed world).2).1 := by
              rw [stateL]
        _ = ((Region.orElse left right).committed world).1 := by
              simp [Region.committed]
    · calc
        ((Region.orElse left right).committed world).2
            = (right.committed (left.committed world).2).2 := by
              simp [Region.committed]
        _ = (right.committed world).2 := by rw [stateL]
        _ = world := stateR

/-- States that agree on the footprint have the same committed answers, leave
states that still agree there, and change nothing outside the writes. -/
theorem ordered_states (region : Region Location Value Answer) :
    footprintsOrdered region →
      ∀ {source framed : Location → Value},
        AgreesOn (region.reads ∪ region.writes) source framed →
          (region.committed source).1 = (region.committed framed).1 ∧
            AgreesOn (region.reads ∪ region.writes)
              (region.committed source).2 (region.committed framed).2 ∧
            PreservesOutside region.writes source (region.committed source).2 ∧
            PreservesOutside region.writes framed (region.committed framed).2 := by
  induction region with
  | fail =>
    intro _ source framed agree
    exact ⟨rfl, agree, fun _ _ => rfl, fun _ _ => rfl⟩
  | answer readout =>
    intro _ source framed agree
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact congrArg (fun value => [value])
        (readout.value_local fun loc mem => agree loc (Finset.mem_union_left _ mem))
    · simp [Region.committed]
      exact agree
    · simp [Region.committed]
      intro _ _
      rfl
    · simp [Region.committed]
      intro _ _
      rfl
  | step first rest ih =>
    intro ordered source framed agree
    have restOrd : footprintsOrdered rest := ordered
    cases fired : first.fire source with
    | none =>
      cases firedF : first.fire framed with
      | some nextF =>
        have back : AgreesOn (first.rule.reads ∪ first.rule.writes) framed source := by
          intro loc mem
          rcases Finset.mem_union.mp mem with h | h
          · exact (agree loc (Finset.mem_union_left _ (Finset.mem_union_left _ h))).symm
          · exact (agree loc (Finset.mem_union_right _ (Finset.mem_union_left _ h))).symm
        obtain ⟨nextS, firedS, _⟩ :=
          (Step.effectFootprinted first).frame firedF source back
        have boom : (none : Option (Location → Value)) = some nextS := by
          rw [fired] at firedS
          exact firedS
        cases boom
      | none =>
        refine ⟨?_, ?_, ?_, ?_⟩
        · simp [Region.committed, fired, firedF]
        · simpa [Region.committed, fired, firedF] using agree
        · simp [Region.committed, fired]
          intro _ _
          rfl
        · simp [Region.committed, firedF]
          intro _ _
          rfl
    | some nextS =>
      have onStep : AgreesOn (first.rule.reads ∪ first.rule.writes) source framed := by
        intro loc mem
        rcases Finset.mem_union.mp mem with h | h
        · exact agree loc (Finset.mem_union_left _ (Finset.mem_union_left _ h))
        · exact agree loc (Finset.mem_union_right _ (Finset.mem_union_left _ h))
      obtain ⟨nextF, firedF, onWrites, preserveF⟩ :=
        (Step.effectFootprinted first).frame fired framed onStep
      have preserveS := (Step.effectFootprinted first).preserves fired
      have restAgree : AgreesOn (rest.reads ∪ rest.writes) nextS nextF := by
        intro loc mem
        by_cases hwrite : loc ∈ first.rule.writes
        · exact onWrites loc hwrite
        · have big : loc ∈ (Region.step first rest).reads ∪ (Region.step first rest).writes := by
            rcases Finset.mem_union.mp mem with hin | hin
            · exact Finset.mem_union_left _ (Finset.mem_union_right _ hin)
            · exact Finset.mem_union_right _ (Finset.mem_union_right _ hin)
          calc
            nextS loc = source loc := preserveS loc hwrite
            _ = framed loc := agree loc big
            _ = nextF loc := (preserveF loc hwrite).symm
      rcases ih restOrd restAgree with ⟨answersEq, outputsAgree, presNextS, presNextF⟩
      have redS : ((Region.step first rest).committed source).2 = (rest.committed nextS).2 := by
        simp [Region.committed, fired]
      have redF : ((Region.step first rest).committed framed).2 = (rest.committed nextF).2 := by
        simp [Region.committed, firedF]
      refine ⟨?_, ?_, ?_, ?_⟩
      · simpa [Region.committed, fired, firedF] using answersEq
      · intro loc mem
        by_cases inRest : loc ∈ rest.reads ∪ rest.writes
        · have eqAt := outputsAgree loc inRest
          rw [redS, redF]
          exact eqAt
        · have notRestWrite : loc ∉ rest.writes :=
            fun written => inRest (Finset.mem_union_right _ written)
          by_cases hwrite : loc ∈ first.rule.writes
          · calc
              ((Region.step first rest).committed source).2 loc
                  = nextS loc := by
                    rw [redS]; exact presNextS loc notRestWrite
              _ = nextF loc := onWrites loc hwrite
              _ = ((Region.step first rest).committed framed).2 loc := by
                    rw [redF]; exact (presNextF loc notRestWrite).symm
          · calc
              ((Region.step first rest).committed source).2 loc
                  = nextS loc := by
                    rw [redS]; exact presNextS loc notRestWrite
              _ = source loc := preserveS loc hwrite
              _ = framed loc := agree loc mem
              _ = nextF loc := (preserveF loc hwrite).symm
              _ = ((Region.step first rest).committed framed).2 loc := by
                    rw [redF]; exact (presNextF loc notRestWrite).symm
      · intro loc outside
        have notFirst : loc ∉ first.rule.writes :=
          fun written => outside (Finset.mem_union_left _ written)
        have notRest : loc ∉ rest.writes :=
          fun written => outside (Finset.mem_union_right _ written)
        calc
          ((Region.step first rest).committed source).2 loc
              = nextS loc := by
                rw [redS]; exact presNextS loc notRest
          _ = source loc := preserveS loc notFirst
      · intro loc outside
        have notFirst : loc ∉ first.rule.writes :=
          fun written => outside (Finset.mem_union_left _ written)
        have notRest : loc ∉ rest.writes :=
          fun written => outside (Finset.mem_union_right _ written)
        calc
          ((Region.step first rest).committed framed).2 loc
              = nextF loc := by
                rw [redF]; exact presNextF loc notRest
          _ = framed loc := preserveF loc notFirst
  | orElse left right ihL ihR =>
    intro ordered source framed agree
    rcases ordered with ⟨leftOrd, rightOrd, apart⟩
    have leftAgree : AgreesOn (left.reads ∪ left.writes) source framed := by
      intro loc mem
      rcases Finset.mem_union.mp mem with h | h
      · exact agree loc (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      · exact agree loc (Finset.mem_union_right _ (Finset.mem_union_left _ h))
    rcases ihL leftOrd leftAgree with ⟨ansL, outL, presLS, presLF⟩
    have rightAgree :
        AgreesOn (right.reads ∪ right.writes)
          (left.committed source).2 (left.committed framed).2 := by
      intro loc mem
      have outside : loc ∉ left.writes :=
        fun written => (Finset.disjoint_left.mp apart) written mem
      calc
        (left.committed source).2 loc = source loc := presLS loc outside
        _ = framed loc := agree loc
            (by
              rcases Finset.mem_union.mp mem with h | h
              · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
              · exact Finset.mem_union_right _ (Finset.mem_union_right _ h))
        _ = (left.committed framed).2 loc := (presLF loc outside).symm
    rcases ihR rightOrd rightAgree with ⟨ansR, outR, presRS, presRF⟩
    have redS :
        ((Region.orElse left right).committed source).2 =
          (right.committed (left.committed source).2).2 := by
      simp [Region.committed]
    have redF :
        ((Region.orElse left right).committed framed).2 =
          (right.committed (left.committed framed).2).2 := by
      simp [Region.committed]
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Region.committed]
      rw [ansL, ansR]
    · intro loc mem
      by_cases inRight : loc ∈ right.reads ∪ right.writes
      · rw [redS, redF]
        exact outR loc inRight
      · have notRightWrite : loc ∉ right.writes :=
          fun written => inRight (Finset.mem_union_right _ written)
        have inLeft : loc ∈ left.reads ∪ left.writes := by
          rcases Finset.mem_union.mp mem with h | h
          · rcases Finset.mem_union.mp h with hleft | hright
            · exact Finset.mem_union_left _ hleft
            · exact absurd hright (fun member => inRight (Finset.mem_union_left _ member))
          · rcases Finset.mem_union.mp h with hleft | hright
            · exact Finset.mem_union_right _ hleft
            · exact absurd hright notRightWrite
        calc
          ((Region.orElse left right).committed source).2 loc
              = (left.committed source).2 loc := by
                rw [redS]; exact presRS loc notRightWrite
          _ = (left.committed framed).2 loc := outL loc inLeft
          _ = ((Region.orElse left right).committed framed).2 loc := by
                rw [redF]; exact (presRF loc notRightWrite).symm
    · intro loc outside
      have notLeft : loc ∉ left.writes :=
        fun written => outside (Finset.mem_union_left _ written)
      have notRight : loc ∉ right.writes :=
        fun written => outside (Finset.mem_union_right _ written)
      calc
        ((Region.orElse left right).committed source).2 loc
            = (left.committed source).2 loc := by
              rw [redS]; exact presRS loc notRight
        _ = source loc := presLS loc notLeft
    · intro loc outside
      have notLeft : loc ∉ left.writes :=
        fun written => outside (Finset.mem_union_left _ written)
      have notRight : loc ∉ right.writes :=
        fun written => outside (Finset.mem_union_right _ written)
      calc
        ((Region.orElse left right).committed framed).2 loc
            = (left.committed framed).2 loc := by
              rw [redF]; exact presRF loc notRight
        _ = framed loc := presLF loc notLeft

/-- **The form that holds.** Ordered footprints make the branch-local answers
the committed answers. -/
theorem footprintsOrdered_bag_eq (region : Region Location Value Answer) :
    footprintsOrdered region → ∀ world : Location → Value,
      (region.branchLocal world).map Prod.fst = (region.committed world).1 := by
  induction region with
  | fail =>
    intro _ world
    simp [Region.branchLocal, Region.committed]
  | answer _ =>
    intro _ world
    simp [Region.branchLocal, Region.committed]
  | step first rest ih =>
    intro ordered world
    have restOrd : footprintsOrdered rest := ordered
    cases fired : first.fire world with
    | none => simp [Region.branchLocal, Region.committed, fired]
    | some next =>
      simpa [Region.branchLocal, Region.committed, fired, List.map_map, Function.comp_def] using
        ih restOrd next
  | orElse left right ihL ihR =>
    intro ordered world
    rcases ordered with ⟨leftOrd, rightOrd, apart⟩
    have self : AgreesOn (left.reads ∪ left.writes) world world := fun _ _ => rfl
    have presL := (ordered_states left leftOrd self).2.2.1
    have agreeRight :
        AgreesOn (right.reads ∪ right.writes) world (left.committed world).2 := by
      intro loc mem
      exact (presL loc (fun written => (Finset.disjoint_left.mp apart) written mem)).symm
    have ansRight := (ordered_states right rightOrd agreeRight).1
    simp only [Region.branchLocal, Region.committed, List.map_append]
    rw [ihL leftOrd world, ihR rightOrd world, ansRight]

end Runs

section Witnesses

open SharedSpace

/-- **Negative.** A failing writer is not explored, so every explored proposal
has no step, but the committed read sees the atom and the branch-local read
does not. -/
def hiddenWrite : Region Unit (Multiset Seen) (Multiset Seen) :=
  .orElse (.step (Step.addAtom () .a) .fail) (.answer (Readout.valueAt ()))

theorem hiddenWrite_refutes_explored_steps :
    (∀ proposal ∈ hiddenWrite.proposals, proposal.steps = []) ∧
      ¬ stepFree hiddenWrite ∧
      (hiddenWrite.branchLocal empty).map Prod.fst = [(0 : Multiset Seen)] ∧
      (hiddenWrite.committed empty).1 = [{.a}] ∧
      (hiddenWrite.branchLocal empty).map Prod.fst ≠ (hiddenWrite.committed empty).1 := by
  refine ⟨?explored, ?notFree, ?branch, ?committed, ?differ⟩
  · decide
  · intro free
    unfold hiddenWrite stepFree at free
    exact free.1
  · decide
  · decide
  · decide

/-- **Positive.** Two answers, and no step: the branch-local list is the
committed list, and the state stays. -/
theorem two_answers_match (left right : Bool) (world : Unit → Multiset Seen) :
    let region :=
      Region.orElse (.answer (Readout.const left)) (.answer (Readout.const right))
    stepFree region ∧
      (region.branchLocal world).map Prod.fst = (region.committed world).1 ∧
      (region.committed world).2 = world := by
  intro region
  refine ⟨?free, ?eq⟩
  · unfold stepFree
    exact ⟨trivial, trivial⟩
  · exact stepFree_committed_eq region (by unfold stepFree; exact ⟨trivial, trivial⟩) world

/-- **Positive.** The same two answers have ordered footprints. -/
theorem two_answers_ordered (left right : Bool) :
    footprintsOrdered
      (Region.orElse (.answer (Readout.const left))
        (.answer (Readout.const right)) : Region Unit (Multiset Seen) Bool) := by
  exact ⟨trivial, trivial, Finset.disjoint_empty_left _⟩

/-- Add an atom, then remove it. The remover reads nothing. -/
def consumeAfterAdd : Region Unit (Multiset Seen) Bool :=
  .orElse
    (.step (Step.addAtom () .a) (.answer (Readout.const true)))
    (.step (Step.removeAtom () .a) (.answer (Readout.const false)))

/-- **Negative.** Disjointness of earlier writes from later reads holds, and
the bags still differ: branch-local answers `[true]`, committed answers
`[true, false]`. -/
theorem reads_miss_the_write :
    Disjoint
        (Region.step (Step.addAtom () Seen.a) (.answer (Readout.const true))).writes
        (Region.step (Step.removeAtom () Seen.a) (.answer (Readout.const false))).reads ∧
      (consumeAfterAdd.branchLocal empty).map Prod.fst = [true] ∧
      (consumeAfterAdd.committed empty).1 = [true, false] ∧
      (consumeAfterAdd.branchLocal empty).map Prod.fst ≠
        (consumeAfterAdd.committed empty).1 := by
  decide

/-- **Negative.** The same region is not footprint-ordered: both siblings write
the one location. -/
theorem consumeAfterAdd_not_ordered : ¬ footprintsOrdered consumeAfterAdd := by
  intro ordered
  unfold footprintsOrdered consumeAfterAdd at ordered
  have apart := ordered.2.2
  have addWrites :
      () ∈ (Region.step (Step.addAtom () Seen.a) (.answer (Readout.const true))).writes := by
    simp [Region.writes, Step.addAtom, Step.ofBagRule, SpaceRules.addAtom, LocalRule.unguarded]
  have removeWrites :
      () ∈ (Region.step (Step.removeAtom () Seen.a) (.answer (Readout.const false))).writes := by
    simp [Region.writes, Step.removeAtom, Step.ofBagRule, SpaceRules.removeAtom,
      LocalRule.unguarded]
  exact (Finset.disjoint_left.mp apart) addWrites (Finset.mem_union_right _ removeWrites)

/-- **Probe p1, one alternative.** Sibling `.b` committed alone equals its
branch-local path `[{.b}]`, so that sibling committed alone does not differ
from its branch-local path. On the existing probe the joint committed list
`[{.a}, {.a, .b}]` differs from the branch-local paths `[{.a}, {.b}]`. -/
theorem probe_p1_one_alternative :
    ((sibling .b).committed empty).1 = [{.b}] ∧
      ((sibling .b).branchLocal empty).map Prod.fst = [{.b}] ∧
      ((sibling .b).committed empty).1 =
        ((sibling .b).branchLocal empty).map Prod.fst ∧
      ((Region.alternatives [sibling .a, sibling .b]).committed empty).1 =
        [{.a}, {.a, .b}] ∧
      ((Region.alternatives [sibling .a, sibling .b]).branchLocal empty).map Prod.fst =
        [{.a}, {.b}] ∧
      ((Region.alternatives [sibling .a, sibling .b]).committed empty).1 ≠
        ((Region.alternatives [sibling .a, sibling .b]).branchLocal empty).map Prod.fst := by
  refine ⟨?_, ?_, ?_, committed_answers.1, branchLocal_answers.1, ?_⟩
  · decide
  · decide
  · decide
  · rw [committed_answers.1, branchLocal_answers.1]
    decide

end Witnesses

section ReadBack

theorem groupSum_weight_agree {α Y K : Type} [DecidableEq Y] [AddCommMonoid K]
    (key : α → Y) {w1 w2 : α → K} (l : List α) (y : Y)
    (agree : ∀ a ∈ l, w1 a = w2 a) : groupSum key w1 l y = groupSum key w2 l y := by
  induction l with
  | nil => simp [groupSum]
  | cons head tail ih =>
    rw [groupSum_cons, groupSum_cons]
    have headEq :
        (if key head = y then w1 head else 0) = if key head = y then w2 head else 0 := by
      by_cases same : key head = y
      · simp [same, agree head List.mem_cons_self]
      · simp [same]
    rw [headEq, ih fun a mem => agree a (List.mem_cons_of_mem head mem)]

theorem mul_eq_self_iff (k a : ℕ) : k * a = a ↔ k = 1 ∨ a = 0 := by
  constructor
  · intro eq
    cases k with
    | zero =>
      simp at eq
      exact Or.inr eq.symm
    | succ k =>
      cases k with
      | zero => exact Or.inl rfl
      | succ k =>
        cases a with
        | zero => exact Or.inr rfl
        | succ a =>
          exfalso
          have expand : (k + 2) * (a + 1) = (a + 1) + (k + 1) * (a + 1) := by
            rw [show k + 2 = (k + 1) + 1 from rfl, Nat.succ_mul, Nat.add_comm]
          have zeroRest : (k + 1) * (a + 1) = 0 := by
            apply Nat.add_left_cancel
            calc
              (a + 1) + (k + 1) * (a + 1) = (k + 2) * (a + 1) := expand.symm
              _ = a + 1 := eq
              _ = (a + 1) + 0 := (Nat.add_zero _).symm
          exact Nat.mul_ne_zero (Nat.succ_ne_zero k) (Nat.succ_ne_zero a) zeroRest
  · rintro (rfl | rfl)
    · simp
    · simp

/-- **Read-back.** For every source count and every multiplicity, the Boolean
fibre sum is that multiple of the source. It is the source exactly when the
multiplicity is one or the source is empty. A `Splits` quotient on each arm
reads the source weight back. -/
theorem multiplicity_read_back (p n k : ℕ) :
    readBackCounts (fun x : Bool × Fin k => x.1) (fun x => if x.1 then p else n)
        (bothCopies k) = ⟨k * p, k * n⟩ ∧
      ((⟨k * p, k * n⟩ : Counts) = ⟨p, n⟩ ↔ k = 1 ∨ (p = 0 ∧ n = 0)) ∧
      ∀ splitP : Splits ℚ k (p : ℚ), ∀ splitN : Splits ℚ k (n : ℚ),
        weightPreserving (fun b : Bool => if b then (p : ℚ) else (n : ℚ))
          (fun x : Bool × Fin k => x.1)
          (fun x => if x.1 then splitP.quotient else splitN.quotient)
          (bothCopies k) := by
  let key : Bool × Fin k → Bool := fun x => x.1
  let weight : Bool × Fin k → ℕ := fun x => if x.1 then p else n
  have posMatch :
      groupSum key weight (List.ofFn fun i : Fin k => (true, i)) true = k * p := by
    have agree : ∀ x ∈ List.ofFn fun i : Fin k => (true, i), weight x = p := by
      intro x hx
      obtain ⟨_, rfl⟩ := List.mem_ofFn.mp hx
      simp [weight]
    rw [groupSum_weight_agree key (agree := agree)]
    exact groupSum_one_copy k p true
  have posMiss :
      groupSum key weight (List.ofFn fun i : Fin k => (false, i)) true = 0 := by
    refine groupSum_eq_zero _ ?_
    intro x hx
    obtain ⟨_, rfl⟩ := List.mem_ofFn.mp hx
    exact Bool.false_ne_true
  have posSum : groupSum key weight (bothCopies k) true = k * p := by
    rw [bothCopies, groupSum_append, posMatch, posMiss, Nat.add_zero]
  have negMiss :
      groupSum key weight (List.ofFn fun i : Fin k => (true, i)) false = 0 := by
    refine groupSum_eq_zero _ ?_
    intro x hx
    obtain ⟨_, rfl⟩ := List.mem_ofFn.mp hx
    intro same
    cases same
  have negMatch :
      groupSum key weight (List.ofFn fun i : Fin k => (false, i)) false = k * n := by
    have agree : ∀ x ∈ List.ofFn fun i : Fin k => (false, i), weight x = n := by
      intro x hx
      obtain ⟨_, rfl⟩ := List.mem_ofFn.mp hx
      simp [weight]
    rw [groupSum_weight_agree key (agree := agree)]
    exact groupSum_one_copy k n false
  have negSum : groupSum key weight (bothCopies k) false = k * n := by
    rw [bothCopies, groupSum_append, negMiss, negMatch, Nat.zero_add]
  refine ⟨?counts, ?iff, ?splits⟩
  · unfold readBackCounts
    rw [posSum, negSum]
  · constructor
    · intro eq
      have hp : k * p = p := congrArg Counts.pos eq
      have hn : k * n = n := congrArg Counts.neg eq
      rcases (mul_eq_self_iff k p).mp hp with rfl | hp0
      · exact Or.inl rfl
      · rcases (mul_eq_self_iff k n).mp hn with rfl | hn0
        · exact Or.inl rfl
        · exact Or.inr ⟨hp0, hn0⟩
    · rintro (rfl | ⟨rfl, rfl⟩)
      · simp
      · simp
  · intro splitP splitN event
    let quot : Bool × Fin k → ℚ :=
      fun x => if x.1 then splitP.quotient else splitN.quotient
    cases event with
    | true =>
      have matchArm :
          groupSum key quot (List.ofFn fun i : Fin k => (true, i)) true =
            (k : ℚ) * splitP.quotient := by
        have agree : ∀ x ∈ List.ofFn fun i : Fin k => (true, i), quot x = splitP.quotient := by
          intro x hx
          obtain ⟨_, rfl⟩ := List.mem_ofFn.mp hx
          simp [quot]
        rw [groupSum_weight_agree key (agree := agree)]
        exact groupSum_one_copy k splitP.quotient true
      have missArm :
          groupSum key quot (List.ofFn fun i : Fin k => (false, i)) true = 0 := by
        refine groupSum_eq_zero _ ?_
        intro x hx
        obtain ⟨_, rfl⟩ := List.mem_ofFn.mp hx
        exact Bool.false_ne_true
      have summed : groupSum key quot (bothCopies k) true = (k : ℚ) * splitP.quotient := by
        rw [bothCopies, groupSum_append, matchArm, missArm, add_zero]
      exact splitP.equation.symm.trans summed.symm
    | false =>
      have missArm :
          groupSum key quot (List.ofFn fun i : Fin k => (true, i)) false = 0 := by
        refine groupSum_eq_zero _ ?_
        intro x hx
        obtain ⟨_, rfl⟩ := List.mem_ofFn.mp hx
        intro same
        cases same
      have matchArm :
          groupSum key quot (List.ofFn fun i : Fin k => (false, i)) false =
            (k : ℚ) * splitN.quotient := by
        have agree : ∀ x ∈ List.ofFn fun i : Fin k => (false, i), quot x = splitN.quotient := by
          intro x hx
          obtain ⟨_, rfl⟩ := List.mem_ofFn.mp hx
          simp [quot]
        rw [groupSum_weight_agree key (agree := agree)]
        exact groupSum_one_copy k splitN.quotient false
      have summed : groupSum key quot (bothCopies k) false = (k : ℚ) * splitN.quotient := by
        rw [bothCopies, groupSum_append, missArm, matchArm, zero_add]
      exact splitN.equation.symm.trans summed.symm

/-- **Positive.** One copy of `⟨2, 3⟩` reads that count back. -/
theorem read_back_one_is_source :
    readBackCounts (fun x : Bool × Fin 1 => x.1) (fun x => if x.1 then 2 else 3) (bothCopies 1) =
      ⟨2, 3⟩ := by
  simpa using (multiplicity_read_back 2 3 1).1

/-- **Negative.** The empty count reads back as itself at multiplicity 2, so
equality with the source is not exactly the condition `k = 1`. -/
theorem empty_count_reads_back_at_two :
    readBackCounts (fun x : Bool × Fin 2 => x.1) (fun x => if x.1 then 0 else 0) (bothCopies 2) =
      ⟨0, 0⟩ ∧ 2 ≠ 1 := by
  exact ⟨(multiplicity_read_back 0 0 2).1, by decide⟩

/-- **Negative.** Two copies are not the source count. -/
theorem read_back_two_ne_source :
    readBackCounts (fun x : Bool × Fin 2 => x.1) (fun x => if x.1 then 2 else 3) (bothCopies 2) ≠
      ⟨2, 3⟩ := by
  intro eq
  have scaled := (multiplicity_read_back 2 3 2).1
  have same : (⟨4, 6⟩ : Counts) = ⟨2, 3⟩ := by
    rw [← scaled]
    exact eq
  have : (4 : ℕ) = 2 := congrArg Counts.pos same
  omega

end ReadBack

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder
