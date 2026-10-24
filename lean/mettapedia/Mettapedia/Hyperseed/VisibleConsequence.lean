import Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure

/-!
# Visible consequences and inference restriction

Observation intersects a consequence set with a region. Restricting inference
also removes hidden premises and rules; these operations need not agree.
For the existing unary rules at a fixed state, agreement for every seed is
equivalent to backward closure of the region under active rules. The same
condition gives correspondence at every synchronous execution round.
-/

namespace Mettapedia.Hyperseed

open Mettapedia.PLN.Evidence.EvidenceClass Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure

variable {State Query : Type*} [EvidenceType State] [BinaryWorldModel State Query]

/-- The original rules whose two query endpoints are visible. -/
def visibleRules (R : RuleSet State Query) (V : Set Query) : RuleSet State Query :=
  {r ∈ R | r.premise ∈ V ∧ r.conclusion ∈ V}

/-- An active rule cannot enter the visible region from a hidden premise. -/
def BackwardClosedAt (R : RuleSet State Query) (W : State) (V : Set Query) : Prop :=
  ∀ r ∈ R, r.side W → r.conclusion ∈ V → r.premise ∈ V

theorem BackwardClosedAt.empty (R : RuleSet State Query) (W : State) :
    BackwardClosedAt R W ∅ := fun _ _ _ h => h.elim

theorem BackwardClosedAt.univ (R : RuleSet State Query) (W : State) :
    BackwardClosedAt R W Set.univ := fun _ _ _ _ => Set.mem_univ _

theorem BackwardClosedAt.inter {R : RuleSet State Query} {W : State} {V U : Set Query}
    (hv : BackwardClosedAt R W V) (hu : BackwardClosedAt R W U) :
    BackwardClosedAt R W (V ∩ U) :=
  fun r hr hs h => ⟨hv r hr hs h.1, hu r hr hs h.2⟩

/-- Observing one full inference step equals a restricted inference step. -/
theorem immediateStep_inter_visible (R : RuleSet State Query) (W : State) (V : Set Query)
    (closed : BackwardClosedAt R W V) (seed S : Set Query) :
    immediateStep R W seed S ∩ V =
      immediateStep (visibleRules R V) W (seed ∩ V) (S ∩ V) := by
  ext q
  constructor
  · rintro ⟨previous | derived, visible⟩
    · rcases previous with old | initial
      · exact Or.inl (Or.inl ⟨old, visible⟩)
      · exact Or.inl (Or.inr ⟨initial, visible⟩)
    · rcases derived with ⟨r, hr, hs, hp, rfl⟩
      have premise := closed r hr hs visible
      exact Or.inr ⟨r, ⟨hr, premise, visible⟩, hs, ⟨hp, premise⟩, rfl⟩
  · intro result
    rcases result with previous | derived
    · rcases previous with old | initial
      · exact ⟨Or.inl (Or.inl old.1), old.2⟩
      · exact ⟨Or.inl (Or.inr initial.1), initial.2⟩
    · rcases derived with ⟨r, hr, hs, hp, rfl⟩
      exact ⟨Or.inr ⟨r, hr.1, hs, hp.1, rfl⟩, hr.2.2⟩

theorem immediateIter_inter_visible (R : RuleSet State Query) (W : State) (V : Set Query)
    (closed : BackwardClosedAt R W V) (seed : Set Query) (n : ℕ) :
    immediateIter R W seed n ∩ V = immediateIter (visibleRules R V) W (seed ∩ V) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [immediateIter, immediateStep_inter_visible R W V closed, ih]
    rfl

/-- Unary consequence rules cannot produce any fact without a seed. -/
theorem leastRuleClosure_empty (R : RuleSet State Query) (W : State) :
    leastRuleClosure R W ∅ = ∅ := by
  apply Set.Subset.antisymm
  · exact leastRuleClosure_least_of_seed_and_rules R W ∅ ∅ (Set.Subset.refl _)
      (fun _ _ _ h => h.elim)
  · exact Set.empty_subset _

theorem visibleClosure_subset_region (R : RuleSet State Query) (W : State)
    (V seed : Set Query) : leastRuleClosure (visibleRules R V) W (seed ∩ V) ⊆ V :=
  leastRuleClosure_least_of_seed_and_rules _ _ _ _ Set.inter_subset_right
    (fun _ hr _ _ => hr.2.2)

/-- Backward closure preserves visible conclusions, without a finite query assumption. -/
theorem leastRuleClosure_inter_visible (R : RuleSet State Query) (W : State) (V : Set Query)
    (closed : BackwardClosedAt R W V) (seed : Set Query) :
    leastRuleClosure R W seed ∩ V = leastRuleClosure (visibleRules R V) W (seed ∩ V) := by
  classical
  let target := leastRuleClosure (visibleRules R V) W (seed ∩ V)
  have full_subset : leastRuleClosure R W seed ⊆ target ∪ Vᶜ := by
    apply leastRuleClosure_least_of_seed_and_rules
    · intro q hq
      by_cases visible : q ∈ V
      · exact Or.inl (seed_subset_leastRuleClosure _ _ _ ⟨hq, visible⟩)
      · exact Or.inr visible
    · intro r hr hs hp
      by_cases visible : r.conclusion ∈ V
      · have premise := closed r hr hs visible
        have prior : r.premise ∈ target := hp.resolve_right (fun hidden => hidden premise)
        exact Or.inl (leastRuleClosure_rule_closed _ _ _ ⟨hr, premise, visible⟩ hs prior)
      · exact Or.inr visible
  apply Set.Subset.antisymm
  · intro q hq
    exact (full_subset hq.1).resolve_right (fun hidden => hidden hq.2)
  · have target_subset : target ⊆ leastRuleClosure R W seed :=
      leastRuleClosure_least_of_seed_and_rules _ _ _ _
        (fun _ h => seed_subset_leastRuleClosure _ _ _ h.1)
        (fun _ hr hs hp => leastRuleClosure_rule_closed R W seed hr.1 hs hp)
    exact Set.subset_inter target_subset (visibleClosure_subset_region R W V seed)

/-- Uniform preservation of visible conclusions characterizes backward closure. -/
theorem backwardClosedAt_iff_closure_observation (R : RuleSet State Query) (W : State)
    (V : Set Query) : BackwardClosedAt R W V ↔
      ∀ seed, leastRuleClosure R W seed ∩ V =
        leastRuleClosure (visibleRules R V) W (seed ∩ V) := by
  classical
  refine ⟨fun h => leastRuleClosure_inter_visible R W V h, ?_⟩
  intro preserved r hr hs visible
  by_contra hidden
  have reached : r.conclusion ∈ leastRuleClosure R W {r.premise} ∩ V :=
    ⟨leastRuleClosure_rule_closed R W _ hr hs (seed_subset_leastRuleClosure _ _ _ (by simp)), visible⟩
  have empty : ({r.premise} : Set Query) ∩ V = ∅ := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, member⟩
    exact hidden member
  rw [preserved, empty, leastRuleClosure_empty] at reached
  exact reached

end Mettapedia.Hyperseed
