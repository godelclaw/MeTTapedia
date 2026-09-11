import Mettapedia.GraphTheory.FourColor.ProtectedContourBand
import Mettapedia.GraphTheory.FourColor.SphericalMeshFreeSeam

/-!
# Preserve the constructed contours in the large-map alternative

The original supplier projected a linkage across actual distance contours
to an ordered mesh. That projection forgets the facial regions needed for
geometric surgery. Here the same contour-versus-cotree proof retains them.
From sufficiently many rows, a whole unmarked band and equally many confined
columns are constructed. The other branch remains the existing strict
ordinary zero-Count replacement, with all designated edges preserved.

Neither a linkage nor a clean region is an input assumption. The linked-band
branch is not asserted to be reducible, of bounded width, or periodic.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalProtectedLinkedBand

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24PrimalCycleFacialBond
open GoertzelV24OrbitFaceTwoSided GoertzelV24TwoEdgeCutMinimality
open GoertzelV24RotationMultigraphAdapter GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24MajorityShorePhysicalReplacement
open SphericalContourSeparators SphericalDistanceContours FaceDistanceFrontiers
open SphericalMeshFreeSeam SphericalMarkedCotreeChain MarkedSeamState MarkedCotreeSeam
open ProtectedContourBand

noncomputable section
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
  {M : Type v} [Fintype M]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Preserve the source of the mesh projection: complete distance contours
and a linkage in the original ambient graph. -/
structure LinkedContours (data : Data G) (rows columns : Nat) where
  root : OrbitFace data.toRotationSystem
  far : OrbitFace data.toRotationSystem
  lo : Nat
  depth : lo + rows ≤ (orbitFaceDualGraph data).dist root far
  linkage : VertexSplitCut.Linkage G (frontier data root far lo)
    (frontier data root far (lo + rows - 1)) columns

/-- The complete closed band and every retained column avoid the marks. -/
structure LinkedBand (data : Data G) (marks : Finset V) (rows columns : Nat)
    extends LinkedContours data rows columns where
  confined : ∀ i z, z ∈ (linkage.walk i).support → z ∈ band data root far lo (lo + rows - 1)
  unmarked : ∀ z ∈ marks, z ∉ band data root far lo (lo + rows - 1)

omit [G.LocallyFinite] in
/-- Construct a clean sub-band using disjoint closed regions, then trim all
columns into it. No assumption about abstract mesh cells is involved. -/
theorem exists_linkedBand (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (marks : Finset V) (a n : Nat) (ha : 2 ≤ a)
    (frame : LinkedContours data ((marks.card + 1) * a) n) :
    Nonempty (LinkedBand data marks a n) := by
  obtain ⟨t, ht⟩ := exists_unmarked_band data ambient htwo frame.root frame.far
    marks frame.lo a (marks.card + 1) (by omega) (Nat.lt_succ_self _)
  have hmul := Nat.mul_le_mul_right a (Nat.succ_le_of_lt t.isLt)
  have hsum : t.val * a + a ≤ (marks.card + 1) * a := by nlinarith
  have hdepth : frame.lo + t.val * a + a ≤ (orbitFaceDualGraph data).dist frame.root frame.far :=
    by simpa only [Nat.add_assoc] using (Nat.add_le_add_left hsum frame.lo).trans frame.depth
  obtain ⟨L, hL⟩ := exists_confined_linkage data ambient htwo frame.root frame.far
    (lo := frame.lo + t.val * a) (hi := frame.lo + t.val * a + a - 1)
    (by omega) (by omega) (by omega) frame.linkage
  exact ⟨{
    root := frame.root, far := frame.far, lo := frame.lo + t.val * a
    depth := hdepth, linkage := L, confined := hL, unmarked := ht }⟩

/-- Re-run the actual radius/contour/cotree construction, retaining a linkage
whenever that branch occurs. An unrelated pre-existing mesh is not returned. -/
theorem exists_linkedContours_or_seamPair (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (a b : Nat) (ha : 2 ≤ a) (marks : Finset V) (mark : M → G.Dart)
    (hlarge : sizeBound a b marks.card (Fintype.card M) < Fintype.card V) :
    Nonempty (LinkedContours data a (orderedLinkageSize a b)) ∨
      ∃ w, w ≤ widthBound a b marks.card (Fintype.card M) ∧
        Nonempty (SeamPair data marks mark w) := by
  classical
  let root := dartOrbitFace data.toRotationSystem data.toRotationSystem.outer
  let c := contourWidth a b
  let n := stateBound c (Fintype.card M)
  let N := contourLength a b marks.card (Fintype.card M)
  let h := radiusBound a b marks.card (Fintype.card M)
  by_cases hradius : ∀ f, (orbitFaceDualGraph data).dist f root ≤ h
  · exact Or.inr ⟨2 * h + 1, le_max_right _ _,
      MarkedCotreeSeam.exists_seamPair_of_large_card data ambient htwo root h marks mark hradius hlarge⟩
  · obtain ⟨far, hfar⟩ := not_forall.mp hradius
    have hdepth : N * a ≤ (orbitFaceDualGraph data).dist far root := (Nat.lt_of_not_ge hfar).le
    have hwindow (t : Fin N) : t.val * a + a ≤ (orbitFaceDualGraph data).dist far root := by
      have hm := Nat.mul_le_mul_right a (Nat.succ_le_of_lt t.isLt)
      simp only [Nat.succ_mul] at hm
      exact hm.trans hdepth
    by_cases hlink : ∃ t : Fin N, Nonempty (VertexSplitCut.Linkage G
        (frontier data far root (t.val * a))
        (frontier data far root (t.val * a + a - 1)) (orderedLinkageSize a b))
    · obtain ⟨t, ⟨L⟩⟩ := hlink
      exact Or.inl ⟨⟨far, root, t.val * a, hwindow t, L⟩⟩
    · have hcut (t : Fin N) : Nonempty (OrderedContourBond data far root
          (t.val * a) (t.val * a + a - 1) c) := by
        obtain ⟨deleted, hf, hl, hc, hcc, he, hp, hface, horder⟩ :=
          (exists_linkage_or_ordered_bond data ambient htwo far root
            (i := t.val * a) (j := t.val * a + a - 1)
            (by omega) (by have := hwindow t; omega) (by have := hwindow t; omega)
            (orderedLinkageSize a b)).resolve_left (fun hL => hlink ⟨t, hL⟩)
        exact ⟨⟨deleted, hf, hl, hc, hcc, he, hp, hface, horder⟩⟩
      let cuts := fun t => Classical.choice (hcut t)
      have hnested := ordered_contour_bonds_nested data ambient htwo far root a N c ha hdepth cuts
      let raw := fun t => (cuts t).toConnectedNode data ambient htwo far root
        (by have := hwindow t; omega) (by have := hwindow t; omega)
      have hraw : ∀ i j, i < j → (raw i).shore ⊂ (raw j).shore :=
        fun i j hij => (hnested i j hij).2
      obtain ⟨nodes, hnest, hmarks, hstar⟩ := exists_marked_nodes_of_nested_nodes
        data ambient c n marks raw hraw
      exact Or.inr ⟨c, le_max_left _ _, exists_seamPair_of_marked_nodes
        data ambient c marks mark nodes hnest hmarks hstar⟩

/-- The replacement alternative now exposes a genuine wholly protected band,
not merely paths avoiding marks. The linked-band reduction is still open. -/
theorem exists_linkedBand_or_marked_replacement (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (hzero : ¬ RotationSystemTaitColorable data.toRotationSystem)
    (a b : Nat) (ha : 2 ≤ a) (marks : Finset V) (mark : M → G.Dart)
    (hmarks : ∀ m, (mark m).fst ∈ marks)
    (hclosed : ∀ m, ∃ m', data.toRotationSystem.alpha (mark m) = mark m')
    (hlarge : sizeBound ((marks.card + 1) * a) b marks.card (Fintype.card M) < Fintype.card V) :
    Nonempty (LinkedBand data marks a (orderedLinkageSize ((marks.card + 1) * a) b)) ∨
      ∃ w, w ≤ widthBound ((marks.card + 1) * a) b marks.card (Fintype.card M) ∧
        ∃ pair : SeamPair data marks mark w,
          Nonempty (StrictPhysicalReplacementData data pair.outer.shore pair.inner.shore
            pair.outer.outsideOuter pair.inner.innerOuter pair.width pair.outerWidth pair.innerWidth) ∧
          ∀ m, ∃ d : pair.candidate.D, pair.ambientDart d = mark m ∧
            pair.ambientDart (pair.candidate.alpha d) = data.toRotationSystem.alpha (mark m) := by
  have hA : 2 ≤ (marks.card + 1) * a := by nlinarith
  rcases exists_linkedContours_or_seamPair data ambient htwo ((marks.card + 1) * a) b hA
      marks mark hlarge with hframe | ⟨w, hw, ⟨pair⟩⟩
  · obtain ⟨frame⟩ := hframe
    exact Or.inl (exists_linkedBand data ambient htwo marks a _ ha frame)
  · exact Or.inr ⟨w, hw, pair, ⟨pair.replacement ambient htwo hzero⟩,
      pair.marked_edge_survives hmarks hclosed⟩

omit [G.LocallyFinite] in
/-- The retained row data reconstructs complete simple cycles with exact
ambient edge coverage, not the boundary of a selected path subgraph. -/
theorem LinkedBand.complete_contour (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    {marks : Finset V} {a n : Nat} (B : LinkedBand data marks a n) (i : Fin a) :
    ∃ start, ∃ cycle : G.Walk start start, cycle.IsCycle ∧
      (∀ d : data.toRotationSystem.D, (data.toRotationSystem.edgeOf d).val ∈ cycle.edges ↔
        ((dartOrbitFace data.toRotationSystem d ∈
            deepRegion (orbitFaceDualGraph data) B.root B.far (B.lo + i.val) ∧
          dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∉
            deepRegion (orbitFaceDualGraph data) B.root B.far (B.lo + i.val)) ∨
         (dartOrbitFace data.toRotationSystem d ∉
            deepRegion (orbitFaceDualGraph data) B.root B.far (B.lo + i.val) ∧
          dartOrbitFace data.toRotationSystem (data.toRotationSystem.alpha d) ∈
            deepRegion (orbitFaceDualGraph data) B.root B.far (B.lo + i.val)))) ∧
      (∀ z, z ∈ cycle.support ↔ z ∈ frontier data B.root B.far (B.lo + i.val)) ∧
      (∀ z ∈ cycle.support, z ∉ marks) := by
  obtain ⟨s, c, hc, he, hv⟩ := exists_distance_contour data ambient htwo B.root B.far
    (B.lo + i.val) (by have := B.depth; omega)
  refine ⟨s, c, hc, he, hv, ?_⟩
  intro z hz hm
  exact B.unmarked z hm (frontier_subset_band data B.root B.far
    (lo := B.lo) (d := B.lo + i.val) (hi := B.lo + a - 1)
    (by omega) (by omega) ((hv z).mp hz))

omit [G.LocallyFinite] in
theorem LinkedBand.columns_avoid_marks (data : Data G)
    {marks : Finset V} {a n : Nat} (B : LinkedBand data marks a n) :
    ∀ i z, z ∈ (B.linkage.walk i).support → z ∉ marks := by
  intro i z hz hm
  exact B.unmarked z hm (B.confined i z hz)

omit [G.LocallyFinite] in
/-- Boundary localization concerns every original edge, including edges
absent from all selected columns. -/
theorem LinkedBand.full_boundary_localized (data : Data G)
    {marks : Finset V} {a n : Nat} (B : LinkedBand data marks a n) {x y : V}
    (hxy : G.Adj x y) (hx : x ∈ band data B.root B.far B.lo (B.lo + a - 1))
    (hy : y ∉ band data B.root B.far B.lo (B.lo + a - 1)) :
    x ∈ frontier data B.root B.far B.lo ∨ x ∈ frontier data B.root B.far (B.lo + a - 1) :=
  boundary_based_on_contours data B.root B.far hxy hx hy

omit [G.LocallyFinite] in
/-- A nonempty linkage connects the whole band, including lateral material. -/
theorem LinkedBand.connected (data : Data G)
    (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    {marks : Finset V} {a n : Nat} (B : LinkedBand data marks a n)
    (ha : 0 < a) (hn : 0 < n) :
    (G.induce (band data B.root B.far B.lo (B.lo + a - 1))).Connected := by
  exact band_connected data ambient htwo B.root B.far
    (by omega) (by have := B.depth; omega) (B.linkage.walk ⟨0, hn⟩)
    (B.linkage.start_mem ⟨0, hn⟩) (B.linkage.finish_mem ⟨0, hn⟩) (B.confined ⟨0, hn⟩)

end
end Mettapedia.GraphTheory.FourColor.SphericalProtectedLinkedBand
