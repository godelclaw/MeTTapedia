import Mettapedia.Algorithms.LazyCartesianRanks

/-!
# Lazy extraction across alternative derivation families

A candidate records a physical family position and an ordered child-rank
vector. Different families and tied vectors retain different identities.
Only each family's zero vector enters the frontier; coordinate increments
are admitted when a candidate is extracted. The independent finite source
is the disjoint union of all the family's Cartesian combinations.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.LazyRankFamilies

open Mettapedia.GSLT.Core.BranchingTemporal
open MonotoneRankEnumeration

structure Family where
  axes : List LazyCartesianRanks.Axis
  baseCost : Nat

abbrev Candidate (families : List Family) :=
  (index : Fin families.length) × LazyCartesianRanks.Point families[index].axes

instance candidateDecidableEq (families : List Family) : DecidableEq (Candidate families) :=
  inferInstanceAs (DecidableEq (Sigma fun index : Fin families.length =>
    LazyCartesianRanks.Point families[index].axes))

instance candidateFintype (families : List Family) : Fintype (Candidate families) :=
  inferInstanceAs (Fintype (Sigma fun index : Fin families.length =>
    LazyCartesianRanks.Point families[index].axes))

def cost (families : List Family) (candidate : Candidate families) : Nat :=
  families[candidate.1].baseCost +
    LazyCartesianRanks.cost families[candidate.1].axes candidate.2

def neighbors (families : List Family) (candidate : Candidate families) :
    List (Candidate families) :=
  (LazyCartesianRanks.neighbors families[candidate.1].axes candidate.2).map
    (fun next => ⟨candidate.1, next⟩)

def roots (families : List Family) : List (Candidate families) :=
  (List.finRange families.length).map
    (fun index => ⟨index, LazyCartesianRanks.zero families[index].axes⟩)

def graph (families : List Family) : Graph (Candidate families) :=
  ⟨neighbors families, cost families⟩

theorem monotone (families : List Family) :
    MonotoneRankEnumeration.Monotone (graph families) := by
  intro parent child member
  obtain ⟨next, adjacent, same⟩ := List.mem_map.mp member
  subst child
  exact Nat.add_le_add_left
    (LazyCartesianRanks.neighbors_monotone families[parent.1].axes
      parent.2 next adjacent) _

theorem candidate_reachable (families : List Family) (candidate : Candidate families) :
    Source (graph families) (roots families) candidate := by
  rcases candidate with ⟨index, point⟩
  have reachable := LazyCartesianRanks.every_point_reachable families[index].axes point
  induction reachable with
  | @root origin member =>
      have same : origin = LazyCartesianRanks.zero families[index].axes :=
        List.mem_singleton.mp member
      subst origin
      apply Generated.root
      exact List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩
  | @successor parent child previous adjacent ih =>
      apply Generated.successor ih
      exact List.mem_map.mpr ⟨child, adjacent, rfl⟩

def extract (families : List Family) (requested allowance : Nat) :
    State (Candidate families) × Nat :=
  (demandMachine (graph families) requested).runSlice allowance (initial (roots families))

def completePrefix (families : List Family) (requested : Nat) : List (Candidate families) :=
  (extract families requested requested).1.published

theorem extract_best (families : List Family) (requested allowance : Nat) :
    (extract families requested allowance).1.published.Nodup ∧
    (extract families requested allowance).1.published.Pairwise
      (fun first second => cost families first ≤ cost families second) ∧
    ∀ first ∈ (extract families requested allowance).1.published,
      ∀ other : Candidate families,
        other ∉ (extract families requested allowance).1.published →
          cost families first ≤ cost families other := by
  have valid := DerivationPrefix.demand_prefix_correct (graph families) (monotone families)
    (roots families) requested allowance
  exact ⟨valid.distinct, valid.ordered, fun first member other remaining =>
    (valid.omitted other (candidate_reachable families other) remaining).2 first member⟩

theorem completePrefix_bound (families : List Family) (requested : Nat) :
    (completePrefix families requested).length ≤ requested :=
  demand_no_overshoot (graph families) requested _ _
    (by simp [MonotoneRankEnumeration.initial])

theorem completePrefix_exhausted_or_full (families : List Family) (requested : Nat) :
    (completePrefix families requested).length = requested ∨
      ∀ candidate : Candidate families, candidate ∈ completePrefix families requested := by
  rcases (DerivationPrefix.demand_prefix_correct (graph families) (monotone families)
    (roots families) requested requested).full_or_exhaustive with full | all
  · exact Or.inl (by simpa only [Nat.min_self, completePrefix, extract, graph] using full)
  · exact Or.inr fun candidate => all candidate (candidate_reachable families candidate)

/-- Omission certifies a full requested prefix, rather than an incomplete
allowance. Every selected candidate is no dearer than the omitted one. -/
theorem omitted_completePrefix (families : List Family) (requested : Nat)
    (candidate : Candidate families) (omitted : candidate ∉ completePrefix families requested) :
    (completePrefix families requested).length = requested ∧
      ∀ selected ∈ completePrefix families requested,
        cost families selected ≤ cost families candidate := by
  simpa only [Nat.min_self, completePrefix, extract, graph] using
    (DerivationPrefix.demand_prefix_correct (graph families) (monotone families)
      (roots families) requested requested).omitted candidate (candidate_reachable families candidate)
      omitted

namespace Controls

def families : List Family :=
  [⟨[LazyCartesianRanks.Controls.twoCosts, LazyCartesianRanks.Controls.twoCosts], 2⟩,
    ⟨[], 3⟩]

example : (roots families).length = 2 := by decide
example : (completePrefix families 5).map (cost families) = [2, 3, 3, 3, 4] := by decide
example : (completePrefix families 3).length = 3 := by decide
example : (completePrefix families 6).length = 5 := by decide

/-- Equal-cost proofs from a binary family and a nullary family are retained. -/
example : ((completePrefix families 5).filter (fun candidate => cost families candidate == 3)).length
    = 3 := by decide

end Controls

end Mettapedia.Algorithms.LazyRankFamilies
