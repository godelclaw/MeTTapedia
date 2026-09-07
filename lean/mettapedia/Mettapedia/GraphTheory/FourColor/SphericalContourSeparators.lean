import Mettapedia.GraphTheory.FourColor.SphericalDistanceContours
import Mettapedia.GraphTheory.FourColor.VertexSeparatorBond
import Mettapedia.GraphTheory.FourColor.GoertzelV24PlanarBondBoundaryOrder

/-!
# Complete bounded bonds between the actual spherical distance contours

The terminal sets are the entire mixed frontiers, whose cycles were
constructed from the ambient rotation system. A vertex separator between
them yields two connected primal shores and a full edge boundary of size
at most three times the separator size. The planar-bond theorem then
computes touched-face uniqueness and opposite first-return boundary orders.

This constructs the small-separator branch, not the separator/linkage
alternative itself, a laminar family, or a recursive branch decomposition.
In particular there is no assumption that the contour lengths are bounded.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalContourSeparators

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24OrbitFaceTwoSided GoertzelV24TwoEdgeCutMinimality
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24DeletedRegionRotationSplice GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24PlanarBondBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open SphericalDistanceContours FaceDistanceFrontiers VertexSeparatorBond

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- All vertices on the depth frontier, with literal ambient face incidence. -/
def frontier (data : Data G) (root far : OrbitFace data.toRotationSystem)
    (depth : ℕ) : Set V :=
  {v | Mixed (vertexFaces data) (deepRegion (orbitFaceDualGraph data) root far depth) v}

/-- Every exposed port is charged to its own original crossing edge. -/
theorem card_boundaryDart_le_edgeBoundary (data : Data G) (S : Set V) :
    Fintype.card (BoundaryDart data.toRotationSystem (· ∈ S)) ≤
      (edgeBoundary G S).card := by
  classical
  let f : BoundaryDart data.toRotationSystem (· ∈ S) →
      {e // e ∈ edgeBoundary G S} := fun d =>
    ⟨d.1.1.edge, by
      apply Finset.mem_filter.mpr
      refine ⟨G.mem_edgeFinset.mpr d.1.1.edge_mem, d.1.1.fst, ?_, d.1.2,
        d.1.1.snd, ?_, d.2⟩ <;> simp [SimpleGraph.Dart.edge]⟩
  have hf : Function.Injective f := by
    intro d e h
    apply boundaryDart_eq_of_edgeOf_eq data.toRotationSystem (· ∈ S) d e
    apply Subtype.ext
    change d.1.1.edge = e.1.1.edge
    exact congrArg (fun q : {e // e ∈ edgeBoundary G S} => q.val) h
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- Connected terminal geometry is derived, not added as a supply premise. -/
theorem frontier_connected (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) (depth : ℕ)
    (hd : depth < (orbitFaceDualGraph data).dist root far) :
    (G.induce (frontier data root far depth)).Connected := by
  obtain ⟨a, p, _hp, _he, hv⟩ := exists_distance_contour data hclass htwo root far depth hd
  have heq : {v | v ∈ p.support} = frontier data root far depth := by
    ext v
    exact hv v
  rw [← heq]
  exact p.connected_induce_support

/-- A separator of two actual contours constructs the complete bounded bond. -/
theorem exists_bounded_bond_between_frontiers (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) {i j : ℕ} (hij : i ≠ j)
    (hi : i < (orbitFaceDualGraph data).dist root far)
    (hj : j < (orbitFaceDualGraph data).dist root far)
    (X : Finset V) (hX : Separates G (frontier data root far i) (frontier data root far j) X) :
    ∃ S : Set V, frontier data root far i ⊆ S ∧ frontier data root far j ⊆ Sᶜ ∧
      (G.induce S).Connected ∧ (G.induce Sᶜ).Connected ∧
      (edgeBoundary G S).card ≤ 3 * X.card := by
  have hG : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using hclass.primalConnected
  apply exists_bounded_bond G hG
    (frontier_connected data hclass htwo root far i hi)
    (frontier_connected data hclass htwo root far j hj)
    (distance_frontiers_disjoint data hclass htwo root far hij) X hX 3
  intro v _hv
  exact ((data.toRotationSystem_isCubic_iff.mp hclass.spherical.cubic) v).le

/-- The constructed cut has the actual complementary first-return orders
and touches each crossing face only once on either shore. -/
theorem exists_ordered_bond_between_frontiers (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) {i j : ℕ} (hij : i ≠ j)
    (hi : i < (orbitFaceDualGraph data).dist root far)
    (hj : j < (orbitFaceDualGraph data).dist root far)
    (X : Finset V) (hX : Separates G (frontier data root far i) (frontier data root far j) X) :
    ∃ deleted : Finset V,
      frontier data root far i ⊆ {v | deletedRegionKeep deleted v} ∧
      frontier data root far j ⊆ {v | ¬ deletedRegionKeep deleted v} ∧
      (G.induce {v | deletedRegionKeep deleted v}).Connected ∧
      (G.induce {v | ¬ deletedRegionKeep deleted v}).Connected ∧
      (edgeBoundary G {v | deletedRegionKeep deleted v}).card ≤ 3 * X.card ∧
      Fintype.card (BoundaryDart data.toRotationSystem (deletedRegionKeep deleted)) ≤ 3 * X.card ∧
      CutFacesHaveUniqueRetainedBoundaryDart data.toRotationSystem deleted ∧
      retainedRegionBoundarySuccessor data.toRotationSystem (deletedRegionKeep deleted) =
        (deletedRegionBoundarySuccessor data.toRotationSystem deleted)⁻¹ := by
  classical
  obtain ⟨S, hAS, hBS, hS, hSc, hbound⟩ :=
    exists_bounded_bond_between_frontiers data hclass htwo root far hij hi hj X hX
  let deleted := Sᶜ.toFinset
  have hkeep : {v | deletedRegionKeep deleted v} = S := by
    ext v
    simp [deletedRegionKeep, deleted]
  have hnotkeep : {v | ¬ deletedRegionKeep deleted v} = Sᶜ := by
    change {v | deletedRegionKeep deleted v}ᶜ = Sᶜ
    rw [hkeep]
  have hret : (G.induce {v | deletedRegionKeep deleted v}).Connected := hkeep ▸ hS
  have hdel : (G.induce {v | ¬ deletedRegionKeep deleted v}).Connected := hnotkeep ▸ hSc
  have hG : G.Connected := by
    simpa only [rotationPrimalGraph_toRotationSystem_eq] using hclass.primalConnected
  refine ⟨deleted, hkeep ▸ hAS, hnotkeep ▸ hBS, hret, hdel, hkeep ▸ hbound, ?_, ?_, ?_⟩
  · have hedge : (edgeBoundary G {v | deletedRegionKeep deleted v}).card ≤ 3 * X.card := by
      simpa only [hkeep] using hbound
    exact (card_boundaryDart_le_edgeBoundary data {v | deletedRegionKeep deleted v}).trans hedge
  · exact cutFacesHaveUniqueRetainedBoundaryDart_of_planar_bond data deleted
      hclass.spherical htwo hG hclass.vertexRotationCyclic hret hdel
  · exact retained_boundarySuccessor_eq_deleted_inverse_of_planar_bond data deleted
      hclass.spherical htwo hG hclass.vertexRotationCyclic hret hdel

end
end Mettapedia.GraphTheory.FourColor.SphericalContourSeparators
