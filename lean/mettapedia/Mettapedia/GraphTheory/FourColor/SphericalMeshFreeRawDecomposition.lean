import Mettapedia.GraphTheory.FourColor.SphericalCotreePathChain
import Mettapedia.GraphTheory.FourColor.GoertzelV24FixedMeshWidthFactorization

/-!
# The exact mesh-free raw-decomposition premise

The cotree path argument bounds the vertices of a mesh-free least
counterexample. A complete edge-labelled comb then supplies a raw branch
decomposition: every middle set is a subset of the vertex set. This is a
deliberately coarse adapter to the existing headline, not a general planar
grid theorem and not a proof of fixed-mesh exclusion or the finite base.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalMeshFreeRawDecomposition

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24ConnectedBranchDecompositionForest
open GoertzelV24ConnectedBranchDecompositionAdapter GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24FixedMeshWidthFactorization GoertzelV24SphericalReductiveAssembly
open GoertzelV24SimpleGraphTaitBridge SphericalCotreePathChain

noncomputable section

universe u

/-- Every nonempty finite list is exactly the leaf list of a full binary tree. -/
theorem exists_tree_with_leafList {E : Type u} (l : List E) (hl : l ≠ []) :
    ∃ t : EdgeLeafTree E, t.leafList = l := by
  induction l with
  | nil => exact (hl rfl).elim
  | cons a l ih =>
      by_cases h : l = []
      · subst l
        exact ⟨.leaf a, rfl⟩
      · obtain ⟨t, ht⟩ := ih h
        exact ⟨.fork (.leaf a) t, by simp [ht]⟩

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Three or more edges admit the literal rooted complete leaf encoding. -/
theorem exists_rooted_decomposition (hcard : 3 ≤ Fintype.card G.edgeSet) :
    Nonempty (RootedBranchDecomposition (G := G)) := by
  classical
  let l := (Finset.univ : Finset G.edgeSet).toList
  have hlen : 3 ≤ l.length := by simpa [l] using hcard
  have hn : l.Nodup := Finset.nodup_toList _
  have hc : l.toFinset = Finset.univ := by simp [l]
  obtain ⟨r, s, t, rest, heq⟩ : ∃ r s t rest, l = r :: s :: t :: rest := by
    cases he : l with
    | nil => simp [he] at hlen
    | cons r l =>
      rw [he] at hlen
      cases l with
      | nil => simp at hlen
      | cons s l =>
        cases l with
        | nil => simp at hlen
        | cons t rest => exact ⟨r, s, t, rest, rfl⟩
  obtain ⟨tree, ht⟩ := exists_tree_with_leafList (t :: rest) (by simp)
  refine ⟨⟨r, .leaf s, tree, ?_, ?_⟩⟩
  · simpa [ht, ← heq] using hn
  · simpa [ht, ← heq] using hc

/-- The whole vertex set bounds every middle set in every leaf tree. -/
theorem everyCutWidthAtMost_of_card_le (w : ℕ) (hw : Fintype.card V ≤ w)
    (t : EdgeLeafTree G.edgeSet) : EveryCutWidthAtMost (G := G) w t := by
  have hc : ∀ s : Finset G.edgeSet, (edgeShoreMiddleVertices G s).card ≤ w :=
    fun s => (Finset.card_le_univ _).trans hw
  induction t with
  | leaf e => exact hc _
  | fork l r hl hr => exact ⟨hc _, hl, hr⟩

theorem widthAtMost_of_card_le (d : RootedBranchDecomposition (G := G))
    (w : ℕ) (hw : Fintype.card V ≤ w) : d.WidthAtMost w :=
  ⟨(Finset.card_le_univ _).trans hw,
    everyCutWidthAtMost_of_card_le w hw d.left,
    everyCutWidthAtMost_of_card_le w hw d.right⟩

/-- Discharge the existing exact target-class decomposition premise. -/
theorem rawDecompositionOfNoInjectiveMesh (a b : ℕ) (ha : 2 ≤ a) :
    RawDecompositionOfNoInjectiveMesh.{u} a b (meshFreeVertexBound a b) := by
  intro V _ _ G _ data minimal hno
  classical
  letI : G.LocallyFinite := fun _ => Subtype.fintype _
  have hsize := vertex_card_le_of_no_injectiveMesh data minimal a b ha hno
  have hthree : 3 ≤ Fintype.card G.edgeSet := by
    let v := data.toRotationSystem.vertOf data.toRotationSystem.outer
    have hc := incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic
      data minimal.spherical.cubic v
    exact hc ▸ Finset.card_le_univ (incidentEdgeFinset G v)
  obtain ⟨d⟩ := exists_rooted_decomposition hthree
  exact ⟨d, widthAtMost_of_card_le d _ hsize⟩

/-- Only fixed-mesh exclusion and the route-native base remain in this specialization. -/
theorem combinatorialFourColorStatement_of_fixedMeshExclusion_and_base
    (a b : ℕ) (ha : 2 ≤ a)
    (exclude : FixedInjectiveMeshExclusion.{u} a b)
    (base : TaitBaseVerifiedAt.{u}
      (rawVertexBound (meshFreeVertexBound a b) (meshFreeVertexBound a b))) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} :=
  GoertzelV24FixedMeshWidthFactorization.combinatorialFourColorStatement_of_fixedMeshExclusion_and_base
    a b (meshFreeVertexBound a b) exclude (rawDecompositionOfNoInjectiveMesh a b ha) base

/-- Feed the Count-derived size bound directly to the base, avoiding a second expansion. -/
theorem combinatorialFourColorStatement_of_fixedMeshExclusion_and_direct_base
    (a b : ℕ) (ha : 2 ≤ a)
    (exclude : FixedInjectiveMeshExclusion.{u} a b)
    (base : TaitBaseVerifiedAt.{u} (meshFreeVertexBound a b)) :
    GoertzelV24SphericalGraphPresentation.CombinatorialFourColorStatement.{u} := by
  apply GoertzelV24SphericalGraphPresentation.combinatorialFourColorStatement_iff_spherical.mpr
  apply GoertzelV24SphericalMinimalCounterexampleSelection.sphericalFourColorStatement_of_no_minimal
  intro V _ _ G _ data minimal
  classical
  letI : G.LocallyFinite := fun _ => Subtype.fintype _
  exact minimal.notColorable (base data minimal.toBridgelessSphericalCubicMapData
    (vertex_card_le_of_no_injectiveMesh data minimal a b ha (exclude data minimal)))

end
end Mettapedia.GraphTheory.FourColor.SphericalMeshFreeRawDecomposition
