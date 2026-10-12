import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder.RevisionOrder
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.Claims
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.PatternFootprints.Deltas
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.DeltaMerge
import Mettapedia.Logic.EvidenceStateInsufficiency

/-!
# One location holds a count

`oneLocationPair` writes `Store.space` while the count is folded elsewhere.
Here the one location holds a `Counts`. The counts are a separation algebra
under addition. Two proposals each add one observation at that location.

On that pair, `Proposal.Independent` fails, `Policy.publishWave` returns
`none`, and publishing the two in either order gives one world, the sum.
Deltas and Claims accept the pair. `waveMerge` does not: the premise it is
missing is `Pairwise Proposal.Independent`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.AddOnly
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Controls
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.FootprintedSpaceTransactions
open Mettapedia.GSLT.SeparationAlgebra
open Mettapedia.Logic.EvidenceStateInsufficiency

/-- Componentwise addition of evidence counts. -/
def countAdd (a b : Counts) : Counts :=
  ⟨a.pos + b.pos, a.neg + b.neg⟩

/-- The empty count. -/
def countZero : Counts :=
  ⟨0, 0⟩

/-- Repeated addition of one count. -/
def countNsmul (n : ℕ) (a : Counts) : Counts :=
  ⟨n * a.pos, n * a.neg⟩

theorem countAdd_assoc (a b c : Counts) :
    countAdd (countAdd a b) c = countAdd a (countAdd b c) := by
  cases a with
  | mk ap an =>
    cases b with
    | mk bp bn =>
      cases c with
      | mk cp cn =>
        show Counts.mk ((ap + bp) + cp) ((an + bn) + cn) =
          Counts.mk (ap + (bp + cp)) (an + (bn + cn))
        rw [Nat.add_assoc, Nat.add_assoc]

theorem count_zero_add (a : Counts) : countAdd countZero a = a := by
  cases a with
  | mk p n =>
    show Counts.mk (0 + p) (0 + n) = Counts.mk p n
    rw [Nat.zero_add, Nat.zero_add]

theorem count_add_zero (a : Counts) : countAdd a countZero = a := by
  cases a with
  | mk p n =>
    show Counts.mk (p + 0) (n + 0) = Counts.mk p n
    rw [Nat.add_zero, Nat.add_zero]

theorem countNsmul_zero (a : Counts) : countNsmul 0 a = countZero := by
  cases a with
  | mk p n =>
    show Counts.mk (0 * p) (0 * n) = Counts.mk 0 0
    rw [Nat.zero_mul, Nat.zero_mul]

theorem countNsmul_succ (n : ℕ) (a : Counts) :
    countNsmul (n + 1) a = countAdd (countNsmul n a) a := by
  cases a with
  | mk p ncount =>
    show Counts.mk ((n + 1) * p) ((n + 1) * ncount) =
      Counts.mk (n * p + p) (n * ncount + ncount)
    rw [Nat.succ_mul, Nat.succ_mul]

theorem countAdd_comm (a b : Counts) : countAdd a b = countAdd b a := by
  cases a with
  | mk ap an =>
    cases b with
    | mk bp bn =>
      show Counts.mk (ap + bp) (an + bn) = Counts.mk (bp + ap) (bn + an)
      rw [Nat.add_comm ap bp, Nat.add_comm an bn]

instance : AddCommMonoid Counts where
  add := countAdd
  add_assoc := countAdd_assoc
  zero := countZero
  zero_add := count_zero_add
  add_zero := count_add_zero
  nsmul := countNsmul
  nsmul_zero := countNsmul_zero
  nsmul_succ := countNsmul_succ
  add_comm := countAdd_comm

instance : SepAlgebra Counts :=
  ofAddCommMonoid Counts

instance : AllSeparate Counts :=
  ⟨fun _ _ => trivial⟩

/-- **Positive.** Addition of the two one-observation counts is their componentwise sum. -/
theorem counts_one_each_sum :
    (⟨1, 0⟩ : Counts) + ⟨0, 1⟩ = ⟨1, 1⟩ := by
  rfl

/-- **Negative.** Adding a true observation twice is not one true observation. -/
theorem counts_two_true_ne_one :
    (⟨1, 0⟩ : Counts) + ⟨1, 0⟩ ≠ ⟨1, 0⟩ := by
  decide

/-- The count of one Boolean observation. -/
def oneObservation (observation : Bool) : Counts :=
  if observation then ⟨1, 0⟩ else ⟨0, 1⟩

theorem oneObservation_distinguishes :
    oneObservation true = ⟨1, 0⟩ ∧ oneObservation false = ⟨0, 1⟩ ∧
      oneObservation true ≠ oneObservation false := by
  unfold oneObservation
  decide

/-- The store whose one location is empty. -/
def emptyCount : Unit → Counts :=
  fun _ => 0

/-- The store whose one location holds one true and one false observation. -/
def summedCount : Unit → Counts :=
  fun _ => ⟨1, 1⟩

theorem emptyCount_zero (observation : Bool) :
    emptyCount () + oneObservation observation = oneObservation observation := by
  rw [emptyCount]
  exact zero_add _

theorem summedCount_ne_empty : summedCount () ≠ emptyCount () := by
  decide

/-- Firing that adds one observation at the only location. -/
def addOneFire (observation : Bool) (state : Unit → Counts) : Option (Unit → Counts) :=
  some (state + fun _ => oneObservation observation)

/-- Add one observation at the only location. -/
def addOne (observation : Bool) : Step Unit Counts where
  rule := LocalRule.unguarded (0 : Unit → Counts) (fun _ => oneObservation observation) {()}
    (fun _ _ => rfl)
    (fun location outside => by
      cases location
      exact absurd (Finset.mem_singleton_self ()) outside)
  fire := addOneFire observation
  fire_eq_some_iff := by
    intro source target
    constructor
    · intro fired
      have eqTarget : source + (fun _ => oneObservation observation) = target := by
        simpa [addOneFire] using fired
      refine ⟨?_, source, SepAlgebra.zero_separate source, AllSeparate.separate _ _, ?_, ?_⟩
      · simp [LocalRule.unguarded]
      · simp [LocalRule.unguarded]
      · rw [← eqTarget]
        exact (AllSeparate.add_comm _ _).symm
    · rintro ⟨_, frame, _, _, sourceEq, targetEq⟩
      have sourceFrame : source = frame := by
        simpa [LocalRule.unguarded, SepAlgebra.zero_add] using sourceEq
      have targetFrame : target = (fun _ => oneObservation observation) + frame := by
        simpa [LocalRule.unguarded] using targetEq
      have joined : source + (fun _ => oneObservation observation) = target := by
        calc
          source + (fun _ => oneObservation observation)
              = frame + (fun _ => oneObservation observation) := by rw [sourceFrame]
          _ = (fun _ => oneObservation observation) + frame := AllSeparate.add_comm _ _
          _ = target := targetFrame.symm
      simpa [addOneFire] using congrArg some joined

/-- A proposal that adds one observation and reads a constant answer. -/
def countProposal (observation : Bool) : Proposal Unit Counts Unit :=
  ⟨[addOne observation], Readout.const ()⟩

/-- The proposal that records one true observation. -/
def trueProposal : Proposal Unit Counts Unit :=
  countProposal true

/-- The proposal that records one false observation. -/
def falseProposal : Proposal Unit Counts Unit :=
  countProposal false

theorem addOne_true_fires :
    (addOne true).fire emptyCount = some (fun _ => ⟨1, 0⟩) := by
  unfold addOne addOneFire emptyCount oneObservation
  rfl

theorem addOne_false_on_true :
    (addOne false).fire (fun _ => ⟨1, 0⟩) = some summedCount := by
  unfold addOne addOneFire oneObservation summedCount
  rfl

theorem addOne_false_fires :
    (addOne false).fire emptyCount = some (fun _ => ⟨0, 1⟩) := by
  unfold addOne addOneFire emptyCount oneObservation
  rfl

theorem addOne_true_on_false :
    (addOne true).fire (fun _ => ⟨0, 1⟩) = some summedCount := by
  unfold addOne addOneFire oneObservation summedCount
  rfl

theorem trueProposal_isDelta : trueProposal.IsDelta := by
  intro step member
  obtain rfl := List.mem_singleton.mp member
  rfl

theorem falseProposal_isDelta : falseProposal.IsDelta := by
  intro step member
  obtain rfl := List.mem_singleton.mp member
  rfl

/-- The two additions are stable under each other: a guard of `True` stays. -/
theorem count_pair_deltaIndependent :
    trueProposal.DeltaIndependent falseProposal := by
  constructor
  · intro step member _state _guarded
    obtain rfl := List.mem_singleton.mp member
    simp [addOne, LocalRule.unguarded]
  · intro step member _state _guarded
    obtain rfl := List.mem_singleton.mp member
    simp [addOne, LocalRule.unguarded]

theorem count_pair_not_independent :
    ¬ trueProposal.Independent falseProposal := by
  intro independent
  have writtenTrue : () ∈ trueProposal.writes := by
    unfold Proposal.writes trueProposal countProposal stepsWrites
    simp only [addOne, LocalRule.unguarded]
    exact Finset.mem_singleton_self ()
  have writtenFalse : () ∈ falseProposal.writes := by
    unfold Proposal.writes falseProposal countProposal stepsWrites
    simp only [addOne, LocalRule.unguarded]
    exact Finset.mem_singleton_self ()
  exact (Finset.disjoint_left.mp independent.1) writtenTrue
    (Finset.mem_union_right _ writtenFalse)

theorem count_pair_not_pairwise :
    ¬ [trueProposal, falseProposal].Pairwise Proposal.Independent := by
  intro pairwise
  exact count_pair_not_independent
    ((List.pairwise_cons.mp pairwise).1 falseProposal (List.mem_singleton_self _))

/-- On this one pair, together: independence fails, the wave policy returns
`none`, and either order publishes the sum. -/
theorem count_pair_together :
    ¬ trueProposal.Independent falseProposal ∧
      Policy.publishWave.change [((), trueProposal), ((), falseProposal)] emptyCount = none ∧
      publish [addOne true, addOne false] emptyCount = some summedCount ∧
      publish [addOne false, addOne true] emptyCount = some summedCount := by
  refine ⟨count_pair_not_independent, ?wave, ?trueFirst, ?falseFirst⟩
  · have notPair :
        ¬ ([((), trueProposal), ((), falseProposal)].map Prod.snd).Pairwise
            Proposal.Independent := by
      simpa using count_pair_not_pairwise
    simp only [Policy.publishWave]
    exact if_neg notPair
  · rw [publish_cons, addOne_true_fires, Option.bind_some, publish_cons,
      addOne_false_on_true, Option.bind_some, publish_nil]
  · rw [publish_cons, addOne_false_fires, Option.bind_some, publish_cons,
      addOne_true_on_false, Option.bind_some, publish_nil]

/-- **Deltas accepts the pair**, by `publishAll_perm_of_deltaIndependent`. -/
theorem deltas_accept_count_pair :
    publishAll [falseProposal, trueProposal] emptyCount =
      publishAll [trueProposal, falseProposal] emptyCount := by
  have indep : [trueProposal, falseProposal].Pairwise Proposal.DeltaIndependent := by
    rw [List.pairwise_cons]
    refine ⟨?_, List.pairwise_singleton _ _⟩
    intro other member
    obtain rfl := List.mem_singleton.mp member
    exact count_pair_deltaIndependent
  have explored :
      ∀ proposal ∈ [trueProposal, falseProposal], (publish proposal.steps emptyCount).isSome := by
    intro proposal member
    rcases List.mem_cons.mp member with rfl | later
    · rw [trueProposal, countProposal, publish_cons, addOne_true_fires, Option.bind_some, publish_nil]
      rfl
    · obtain rfl := List.mem_singleton.mp later
      rw [falseProposal, countProposal, publish_cons, addOne_false_fires, Option.bind_some,
        publish_nil]
      rfl
  exact publishAll_perm_of_deltaIndependent
    (fun proposal member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact trueProposal_isDelta
      · obtain rfl := List.mem_singleton.mp later
        exact falseProposal_isDelta)
    indep explored (List.Perm.swap trueProposal falseProposal []).symm

/-- **Claims accepts the pair.** The steps are positive because the guard is
`True`, so `hasClaims_of_deltas` and `HasClaims.publishAll_perm` apply. -/
theorem claims_accept_count_pair :
    publishAll [falseProposal, trueProposal] emptyCount =
      publishAll [trueProposal, falseProposal] emptyCount := by
  have deltas : ∀ proposal ∈ [trueProposal, falseProposal], proposal.IsDelta := by
    intro proposal member
    rcases List.mem_cons.mp member with rfl | later
    · exact trueProposal_isDelta
    · obtain rfl := List.mem_singleton.mp later
      exact falseProposal_isDelta
  have explored :
      ∀ proposal ∈ [trueProposal, falseProposal], (publish proposal.steps emptyCount).isSome := by
    intro proposal member
    rcases List.mem_cons.mp member with rfl | later
    · rw [trueProposal, countProposal, publish_cons, addOne_true_fires, Option.bind_some,
        publish_nil]
      rfl
    · obtain rfl := List.mem_singleton.mp later
      rw [falseProposal, countProposal, publish_cons, addOne_false_fires, Option.bind_some,
        publish_nil]
      rfl
  have claims := hasClaims_of_deltas deltas explored
  have positive :
      ∀ proposal ∈ [trueProposal, falseProposal], ∀ step ∈ proposal.steps, step.Positive := by
    intro proposal member step stepMember
    rcases List.mem_cons.mp member with rfl | later
    · obtain rfl := List.mem_singleton.mp stepMember
      intro _state _added _guarded
      simp [addOne, LocalRule.unguarded]
    · obtain rfl := List.mem_singleton.mp later
      obtain rfl := List.mem_singleton.mp stepMember
      intro _state _added _guarded
      simp [addOne, LocalRule.unguarded]
  have forward := claims.publishAll_perm positive (List.Perm.refl _)
  have backward := claims.publishAll_perm positive (List.Perm.swap _ _ []).symm
  exact backward.symm.trans forward

/-- `oneLocationPair` writes `Store.space` and folds the count by `Counts.revise`
off that location. The same two observations, added at the count location, are
the value that location holds. -/
theorem oneLocationPair_count_sits_off_the_store :
    ((oneLocationPair.branchLocal noAtoms).map fun outcome => outcome.2.writes) =
        [{Store.space}, {Store.space}] ∧
      (oneLocationPair.observe Policy.publishWave noAtoms).2 = none ∧
      ((⟨0, 0⟩ : Counts).revise true).revise false = summedCount () ∧
      emptyCount () + oneObservation true + oneObservation false = summedCount () := by
  have old := one_location_publications_conflict
  refine ⟨old.2.2.1, old.2.2.2.2.2.2.2, ?revised, ?added⟩
  · unfold Counts.revise summedCount
    rfl
  · unfold emptyCount oneObservation summedCount
    rfl

/-- **DeltaMerge does not accept the pair.** `waveMerge` returns `none`.
The premise it is missing is exactly `Pairwise Proposal.Independent`: both
proposals write the one location, so the write sets are not disjoint. -/
theorem deltaMerge_misses_count_pair :
    waveMerge.merge [trueProposal.delta, falseProposal.delta] = none ∧
      ¬ [trueProposal, falseProposal].Pairwise Proposal.Independent := by
  refine ⟨?none, count_pair_not_pairwise⟩
  · have same :
        ([trueProposal, falseProposal].map Proposal.delta).Pairwise
            FootprintedDelta.Independent ↔
          [trueProposal, falseProposal].Pairwise Proposal.Independent :=
      List.pairwise_map
    simp only [waveMerge]
    exact if_neg fun independent =>
      count_pair_not_pairwise (same.mp independent)

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder
