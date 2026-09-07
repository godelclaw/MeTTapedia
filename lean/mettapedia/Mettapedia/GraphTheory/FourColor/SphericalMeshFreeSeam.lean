import Mettapedia.GraphTheory.FourColor.SphericalOrderedMeshReduction
import Mettapedia.GraphTheory.FourColor.MarkedCotreeSeam

/-!
# A full physical seam from ordered-mesh exclusion

A distant face supplies complete contour bonds in disjoint depth windows.
If there is no distant face, the complete dual-radius bound needed by the
cotree construction holds. Both branches supply actual nested literal
shores, strict unmarked material and a repeated full marked seam state.

The geometric construction uses neither minimality nor zero Count. Zero
Count is needed only by the existing physical replacement consumer. Fixed
ordered-mesh exclusion remains open; this theorem does not prove it, and
named-edge preservation is not a frozen-colour or designated-hole theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalMeshFreeSeam

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided GoertzelV24PrimalCycleFacialBond
open GoertzelV24RotationMultigraphAdapter GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24ConnectedShoreLiteralNode GoertzelV24SimpleGraphTaitBridge
open GoertzelV24MajorityShorePhysicalReplacement
open SphericalContourSeparators SphericalOrderedMeshReduction
open SphericalMarkedCotreeChain MarkedSeamState MarkedCotreeSeam

noncomputable section
universe u v

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
  {M : Type v} [Fintype M]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Complete contour-bond width after ordered linkage extraction. -/
def contourWidth (a b : ℕ) : ℕ := 3 * (orderedLinkageSize a b - 1)

/-- Enough depth windows to space the cuts, avoid marked transitions and
force repetition of the full marked state. -/
def contourLength (a b vertices darts : ℕ) : ℕ :=
  (6 * contourWidth a b + 1) * ((vertices + 1) * stateBound (contourWidth a b) darts) + 1

/-- The threshold distinguishing the two geometric constructions. -/
def radiusBound (a b vertices darts : ℕ) : ℕ :=
  contourLength a b vertices darts * a

/-- A uniform width covering both possible outputs. -/
def widthBound (a b vertices darts : ℕ) : ℕ :=
  max (contourWidth a b) (2 * radiusBound a b vertices darts + 1)

/-- Size sufficient for the cotree branch; the contour branch needs no
separate vertex-count assumption. -/
def sizeBound (a b vertices darts : ℕ) : ℕ :=
  MarkedCotreeSeam.vertexBound (radiusBound a b vertices darts) vertices darts

/-- Construct the complete seam from largeness and ordered-mesh exclusion.
The root, radius alternative and all cuts are produced internally. -/
theorem exists_seamPair_of_no_orderedMesh (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (a b : ℕ) (ha : 2 ≤ a) (marks : Finset V) (mark : M → G.Dart)
    (hno : ¬ Nonempty (OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a b))
    (hlarge : sizeBound a b marks.card (Fintype.card M) < Fintype.card V) :
    ∃ w, w ≤ widthBound a b marks.card (Fintype.card M) ∧
      Nonempty (SeamPair rotation marks mark w) := by
  classical
  let root := dartOrbitFace rotation.toRotationSystem rotation.toRotationSystem.outer
  let c := contourWidth a b
  let n := stateBound c (Fintype.card M)
  let N := contourLength a b marks.card (Fintype.card M)
  let h := radiusBound a b marks.card (Fintype.card M)
  by_cases hradius : ∀ f, (orbitFaceDualGraph rotation).dist f root ≤ h
  · refine ⟨2 * h + 1, le_max_right _ _, ?_⟩
    exact MarkedCotreeSeam.exists_seamPair_of_large_card rotation ambient htwo
      root h marks mark hradius hlarge
  · obtain ⟨far, hfar⟩ := not_forall.mp hradius
    have hdepth : N * a ≤ (orbitFaceDualGraph rotation).dist far root :=
      (Nat.lt_of_not_ge hfar).le
    obtain ⟨raw, hraw⟩ := exists_nested_nodes_of_no_orderedMesh_of_spherical
      rotation ambient htwo far root a b N ha hdepth hno
    obtain ⟨nodes, hnest, hmarks, hstar⟩ := exists_marked_nodes_of_nested_nodes
      rotation ambient c n marks raw hraw
    exact ⟨c, le_max_left _ _, exists_seamPair_of_marked_nodes
      rotation ambient c marks mark nodes hnest hmarks hstar⟩

/-- A geometric alternative on every sufficiently large spherical cubic map:
an actual ordered mesh, or a complete seam with a strict unmarked star. -/
theorem exists_orderedMesh_or_seamPair (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (a b : ℕ) (ha : 2 ≤ a) (marks : Finset V) (mark : M → G.Dart)
    (hlarge : sizeBound a b marks.card (Fintype.card M) < Fintype.card V) :
    Nonempty (OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a b) ∨
      ∃ w, w ≤ widthBound a b marks.card (Fintype.card M) ∧
        Nonempty (SeamPair rotation marks mark w) := by
  classical
  by_cases hm : Nonempty (OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a b)
  · exact Or.inl hm
  · exact Or.inr (exists_seamPair_of_no_orderedMesh rotation ambient htwo a b ha marks mark hm hlarge)

/-- The same supplied seam has the existing smaller spherical, bridgeless,
cubic zero-Count certificate and preserves every designated edge pair.
Neither a dual-radius bound nor a minimal-counterexample hypothesis is used. -/
theorem exists_marked_replacement_of_no_orderedMesh (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hzero : ¬ RotationSystemTaitColorable rotation.toRotationSystem)
    (a b : ℕ) (ha : 2 ≤ a) (marks : Finset V) (mark : M → G.Dart)
    (hmarks : ∀ m, (mark m).fst ∈ marks)
    (hclosed : ∀ m, ∃ m', rotation.toRotationSystem.alpha (mark m) = mark m')
    (hno : ¬ Nonempty (OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a b))
    (hlarge : sizeBound a b marks.card (Fintype.card M) < Fintype.card V) :
    ∃ w, w ≤ widthBound a b marks.card (Fintype.card M) ∧
      ∃ pair : SeamPair rotation marks mark w,
        Nonempty (StrictPhysicalReplacementData rotation pair.outer.shore pair.inner.shore
          pair.outer.outsideOuter pair.inner.innerOuter pair.width pair.outerWidth pair.innerWidth) ∧
        ∀ m, ∃ d : pair.candidate.D, pair.ambientDart d = mark m ∧
          pair.ambientDart (pair.candidate.alpha d) = rotation.toRotationSystem.alpha (mark m) := by
  obtain ⟨w, hw, ⟨pair⟩⟩ :=
    exists_seamPair_of_no_orderedMesh rotation ambient htwo a b ha marks mark hno hlarge
  exact ⟨w, hw, pair, ⟨pair.replacement ambient htwo hzero⟩,
    pair.marked_edge_survives hmarks hclosed⟩

/-- The direct Count reduction alternative: an actual ordered mesh, or an
actual strictly smaller zero-Count map. This leaves precisely the mesh
branch open rather than assuming a radius bound or a supplied corridor. -/
theorem exists_orderedMesh_or_marked_replacement (rotation : Data G)
    (ambient : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (hzero : ¬ RotationSystemTaitColorable rotation.toRotationSystem)
    (a b : ℕ) (ha : 2 ≤ a) (marks : Finset V) (mark : M → G.Dart)
    (hmarks : ∀ m, (mark m).fst ∈ marks)
    (hclosed : ∀ m, ∃ m', rotation.toRotationSystem.alpha (mark m) = mark m')
    (hlarge : sizeBound a b marks.card (Fintype.card M) < Fintype.card V) :
    Nonempty (OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a b) ∨
      ∃ w, w ≤ widthBound a b marks.card (Fintype.card M) ∧
        ∃ pair : SeamPair rotation marks mark w,
          Nonempty (StrictPhysicalReplacementData rotation pair.outer.shore pair.inner.shore
            pair.outer.outsideOuter pair.inner.innerOuter pair.width pair.outerWidth pair.innerWidth) ∧
          ∀ m, ∃ d : pair.candidate.D, pair.ambientDart d = mark m ∧
            pair.ambientDart (pair.candidate.alpha d) = rotation.toRotationSystem.alpha (mark m) := by
  classical
  by_cases hm : Nonempty (OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a b)
  · exact Or.inl hm
  · exact Or.inr (exists_marked_replacement_of_no_orderedMesh
      rotation ambient htwo hzero a b ha marks mark hmarks hclosed hm hlarge)

end
end Mettapedia.GraphTheory.FourColor.SphericalMeshFreeSeam
