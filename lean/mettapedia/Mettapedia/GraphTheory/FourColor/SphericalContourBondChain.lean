import Mettapedia.GraphTheory.FourColor.ContourBondNesting
import Mettapedia.GraphTheory.FourColor.NestedCyclicCutStrictness

/-!
# Mesh exclusion and dual distance construct a strictly nested bond chain

Split a face-dual distance into consecutive windows of a depths. The
mesh-or-bond theorem constructs a complete bounded bond in each window;
mesh exclusion forces the bond alternative. Localization makes all these
independently chosen bonds strictly nested, both as vertex shores and as
full incident-edge shores. Width and order receipts are unchanged.

The output is not assumed as input. `SphericalContourNodeChain` converts
these bonds to exact Count nodes and bounds their number. Global largeness
must still supply distance or the other geometric case.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalContourSeparators

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24OrbitFaceTwoSided GoertzelV24TwoEdgeCutMinimality
open GoertzelV24DeletedRegionRotationSplice GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24RetainedRegionBoundaryOrder GoertzelV24ComplementaryRegionBoundaryOrder
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationMultigraphAdapter GoertzelV24MeshIsoperimetry
open GoertzelV24InjectiveMeshWidthExclusion GoertzelV24ConnectedVertexSideEdgeShore
open VertexSeparatorBond

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Receipts on a constructed whole-ambient bond, not extra supply assumptions. -/
structure OrderedContourBond (data : Data G) (root far : OrbitFace data.toRotationSystem)
    (lo hi width : ℕ) where
  deleted : Finset V
  first : frontier data root far lo ⊆ {v | deletedRegionKeep deleted v}
  last : frontier data root far hi ⊆ {v | ¬ deletedRegionKeep deleted v}
  connected : (G.induce {v | deletedRegionKeep deleted v}).Connected
  complement_connected : (G.induce {v | ¬ deletedRegionKeep deleted v}).Connected
  edge_bound : (edgeBoundary G {v | deletedRegionKeep deleted v}).card ≤ width
  port_bound : Fintype.card (BoundaryDart data.toRotationSystem (deletedRegionKeep deleted)) ≤ width
  face_unique : CutFacesHaveUniqueRetainedBoundaryDart data.toRotationSystem deleted
  opposite_order : retainedRegionBoundarySuccessor data.toRotationSystem (deletedRegionKeep deleted) =
    (deletedRegionBoundarySuccessor data.toRotationSystem deleted)⁻¹

/-- Large dual distance in an exact mesh-free map constructs all n bonds,
their complete width/order receipts, and both forms of strict nesting. -/
theorem exists_nested_contour_bonds (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root far : OrbitFace data.toRotationSystem) (a b n : ℕ)
    (ha : 2 ≤ a) (hd : n * a ≤ (orbitFaceDualGraph data).dist root far)
    (hno : ¬ ∃ M : Mesh (toMultigraph data.toRotationSystem) a b, IsVertexInjective M) :
    ∃ cuts : (t : Fin n) → OrderedContourBond data root far
        (t.val * a) (t.val * a + a - 1) (3 * (b - 1)),
      ∀ i j, i < j →
        {v | deletedRegionKeep (cuts i).deleted v} ⊂
          {v | deletedRegionKeep (cuts j).deleted v} ∧
        incidentEdgeShore G (deletedRegionKeep (cuts i).deleted) ⊂
          incidentEdgeShore G (deletedRegionKeep (cuts j).deleted) := by
  classical
  have hdepth (t : Fin n) : t.val * a + a ≤ (orbitFaceDualGraph data).dist root far := by
    have hmul := Nat.mul_le_mul_right a (Nat.succ_le_of_lt t.isLt)
    calc
      t.val * a + a = (t.val + 1) * a := by simp [Nat.add_mul]
      _ ≤ n * a := hmul
      _ ≤ _ := hd
  have hcut (t : Fin n) : Nonempty (OrderedContourBond data root far
      (t.val * a) (t.val * a + a - 1) (3 * (b - 1))) := by
    obtain ⟨deleted, hfirst, hlast, hconn, hcomp, hedge, hport, hface, horder⟩ :=
      exists_ordered_bond_of_no_injectiveMesh data hclass htwo root far
        (t.val * a) a b ha (hdepth t) hno
    exact ⟨⟨deleted, hfirst, hlast, hconn, hcomp, hedge, hport, hface, horder⟩⟩
  let cuts := fun t : Fin n => Classical.choice (hcut t)
  refine ⟨cuts, ?_⟩
  intro i j hij
  have hmul := Nat.mul_le_mul_right a (Nat.succ_le_of_lt hij)
  simp only [Nat.succ_mul] at hmul
  have hstrict : {v | deletedRegionKeep (cuts i).deleted v} ⊂
      {v | deletedRegionKeep (cuts j).deleted v} :=
    contour_bonds_strict data hclass htwo root far
      (i := i.val * a) (j := i.val * a + a - 1)
      (p := j.val * a) (q := j.val * a + a - 1)
      (by omega) (by omega) (by omega) (by have := hdepth j; omega)
      (cuts i).connected (cuts j).complement_connected
      (cuts i).first (cuts i).last (cuts j).first (cuts j).last
  refine ⟨hstrict, ?_⟩
  obtain ⟨x, hx, hxold⟩ := Set.exists_of_ssubset hstrict
  obtain ⟨y⟩ := (cuts j).complement_connected.nonempty
  exact NestedCyclicCutStrictness.incidentEdgeShore_ssubset
    (fun _ h => hstrict.subset h) ⟨x, hx, hxold⟩ ⟨y, y.property⟩
    (cuts i).complement_connected.preconnected

end
end Mettapedia.GraphTheory.FourColor.SphericalContourSeparators
