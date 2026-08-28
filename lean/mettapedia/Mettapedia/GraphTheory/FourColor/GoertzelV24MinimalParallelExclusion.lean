import Mettapedia.GraphTheory.FourColor.GoertzelV24DigonSpliceNormalization

/-!
# Parallel-edge exclusion for a least Tait counterexample

The digon splice is stated for explicit `DigonPatchData`.  This file closes
the small representation gap between that local witness and the intrinsic
statement that two rotation-system edges have the same endpoint set.

In a cubic rotation system, two distinct parallel edges use two of the three
edges incident with each common endpoint.  Choosing the remaining incident
edge at each endpoint produces well-formed digon data.  The already-proved
digon splice then excludes the parallel pair in a vertex-minimal Tait
counterexample.  Equivalently, its endpoint map is injective, which is the
exact input required by the canonical primal-simple-graph presentation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace RotationSystem

open GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationEdgeBridge
open GoertzelV24TwoEdgeCutMinimality

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- At a cubic vertex, two distinct incident edges have a third companion,
and the three edges exhaust the incident-edge set. -/
theorem exists_incidentEdge_triple_eq_of_isCubic
    (RS : RotationSystem V E) (hCubic : RS.IsCubic)
    {vertex : V} {first second : E} (hne : first ≠ second)
    (hfirst : first ∈ RS.incidentEdges vertex)
    (hsecond : second ∈ RS.incidentEdges vertex) :
    ∃ third : E,
      RS.incidentEdges vertex = {third, first, second} := by
  classical
  have hnotSubset :
      ¬ RS.incidentEdges vertex ⊆ ({first, second} : Finset E) := by
    intro hsubset
    have hcard := Finset.card_le_card hsubset
    rw [RS.incidentEdges_card_eq_three_of_isCubic hCubic vertex,
      Finset.card_pair hne] at hcard
    omega
  rw [Finset.not_subset] at hnotSubset
  rcases hnotSubset with ⟨third, hthird, hthirdPair⟩
  have hthirdFirst : third ≠ first := by
    intro heq
    apply hthirdPair
    simp [heq]
  have hthirdSecond : third ≠ second := by
    intro heq
    apply hthirdPair
    simp [heq]
  have htripleSubset :
      ({third, first, second} : Finset E) ⊆ RS.incidentEdges vertex := by
    intro edge hedge
    simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
    rcases hedge with rfl | rfl | rfl
    · exact hthird
    · exact hfirst
    · exact hsecond
  refine ⟨third, (Finset.eq_of_subset_of_card_le htripleSubset ?_).symm⟩
  rw [RS.incidentEdges_card_eq_three_of_isCubic hCubic vertex]
  simp [hthirdFirst, hthirdSecond, hne]

/-- Every intrinsic parallel pair in a cubic rotation system canonically
extends to the explicit local data consumed by digon suppression. -/
theorem exists_wellFormed_digonPatchData_of_areParallelEdges
    (RS : RotationSystem V E) (hCubic : RS.IsCubic)
    {first second : E} (hparallel : RS.AreParallelEdges first second) :
    ∃ D : @DigonPatchData V E, D.WellFormed RS := by
  classical
  rcases RS.dartsOn_nonempty first with ⟨dart, hdart⟩
  let u := RS.vertOf dart
  let v := RS.vertOf (RS.alpha dart)
  have huv : u ≠ v := by
    simpa [u, v] using RS.no_self_loops dart
  have huFirstEndpoint : u ∈ RS.endpoints first := by
    rw [RS.endpoints_eq_pair_of_mem hdart]
    simp [u]
  have hvFirstEndpoint : v ∈ RS.endpoints first := by
    rw [RS.endpoints_eq_pair_of_mem hdart]
    simp [v]
  have huSecondEndpoint : u ∈ RS.endpoints second := by
    simpa [hparallel.2] using huFirstEndpoint
  have hvSecondEndpoint : v ∈ RS.endpoints second := by
    simpa [hparallel.2] using hvFirstEndpoint
  have huFirst : first ∈ RS.incidentEdges u :=
    (RS.mem_endpoints_iff_mem_incidentEdges).1 huFirstEndpoint
  have huSecond : second ∈ RS.incidentEdges u :=
    (RS.mem_endpoints_iff_mem_incidentEdges).1 huSecondEndpoint
  have hvFirst : first ∈ RS.incidentEdges v :=
    (RS.mem_endpoints_iff_mem_incidentEdges).1 hvFirstEndpoint
  have hvSecond : second ∈ RS.incidentEdges v :=
    (RS.mem_endpoints_iff_mem_incidentEdges).1 hvSecondEndpoint
  rcases RS.exists_incidentEdge_triple_eq_of_isCubic hCubic
      hparallel.1 huFirst huSecond with ⟨outerU, houterU⟩
  rcases RS.exists_incidentEdge_triple_eq_of_isCubic hCubic
      hparallel.1 hvFirst hvSecond with ⟨outerV, houterV⟩
  let D : @DigonPatchData V E :=
    { u := u
      v := v
      e := first
      f := second
      outerU := outerU
      outerV := outerV }
  exact ⟨D, huv, hparallel, houterU, houterV⟩

/-- A vertex-minimal Tait counterexample has an injective endpoint map: two
literal edges never represent the same undirected primal edge. -/
theorem endpoints_injective_of_minimal
    {V E : Type u} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem.{u, u, u} V E)
    (hclass : BridgelessSphericalCubicMapData RS)
    (htwoSided : OrbitFacesTwoSided RS)
    (hnot : ¬ RotationSystemTaitColorable RS)
    (hsmaller :
      ∀ {V' E' : Type u}
        [Fintype V'] [DecidableEq V'] [Fintype E'] [DecidableEq E']
        (candidate : RotationSystem.{u, u, u} V' E'),
        Fintype.card V' < Fintype.card V →
        BridgelessSphericalCubicMapData candidate →
        RotationSystemTaitColorable candidate) :
    Function.Injective RS.endpoints := by
  intro first second heq
  by_contra hne
  have hparallel : RS.AreParallelEdges first second := ⟨hne, heq⟩
  rcases RS.exists_wellFormed_digonPatchData_of_areParallelEdges
      hclass.spherical.cubic hparallel with ⟨D, hD⟩
  exact False.elim
    (RS.no_wellFormed_digonPatchData_of_minimal
      hclass htwoSided hnot hsmaller D hD)

end

end RotationSystem

/-! Publication-facing aliases. -/

alias GoertzelV24MinimalParallelExclusion.exists_wellFormed_digonPatchData :=
  RotationSystem.exists_wellFormed_digonPatchData_of_areParallelEdges

alias GoertzelV24MinimalParallelExclusion.endpoints_injective_of_minimal :=
  RotationSystem.endpoints_injective_of_minimal

end Mettapedia.GraphTheory.FourColor
