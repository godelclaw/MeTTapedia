import Mettapedia.GraphTheory.FourColor.GoertzelV24SpliceUnification
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceGraphGeometry

/-!
# Boundary simplicity after the literal ordered-cut splice

Addendum XXVII preserves noncrossing facial geometry when complementary
annular pieces are glued along simple ordered transversals.  This module
isolates the exact finite Lean receipt behind that statement.

Every output face either avoids the seam or contains one of its ordered
darts.  A seam-free non-hole face transports to a source-interior face, where
the Cell--3 geometry already proves a simple boundary.  Consequently the
global literal output obligation reduces to checking the finitely indexed
seam-root faces.  No global two-sidedness premise is used: it is false at the
degree-one hole boundaries of the source annulus.

This is one L1 post-splice topology reduction.  It does not construct the
seam-local receipt or the remaining internal-dual connectedness receipt.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedCutFaceOrbit
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24SeamFaceArc
open GoertzelV24SpliceUnification

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace GoertzelV24SpliceUnification.OrderedCutSpliceData

variable {RS : RotationSystem V E}
  {n terminalCount faceFragmentCount : Nat}

/-- The finite seam-local boundary-simplicity receipt.  Ordered seam
positions enumerate every seam dart, so this asks only about faces that can
change during the splice. -/
def SeamFacesBoundarySimple
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) : Prop :=
  ∀ position : OrderedSeamPosition n,
    let root := orderedSeamRoot RS data.keep
      data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses data.leftInjective
      data.rightInjective position
    (orbitFaceBoundary data.output (dartOrbitFace data.output root)).card =
      (orbitFaceDarts data.output (dartOrbitFace data.output root)).card

/-- The local topological form of the finite seam receipt.  On every output
face reached from an ordered seam dart, the two orientations of one edge lie
on different facial orbits.  Unlike global `OrbitFacesTwoSided`, this says
nothing about the two protected degree-one hole faces. -/
def SeamFacesTwoSided
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) : Prop :=
  ∀ position : OrderedSeamPosition n,
    let root := orderedSeamRoot RS data.keep
      data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses data.leftInjective
      data.rightInjective position
    ∀ point : data.output.D,
      data.output.phi.SameCycle root point →
        dartOrbitFace data.output point ≠
          dartOrbitFace data.output (data.output.alpha point)

/-- Seam-local two-sidedness is exactly strong enough to make the edge map
injective on every seam-root face.  This turns the source's noncrossing claim
into a pointwise alpha-side separation problem, rather than a cardinality
calculation on quotient faces. -/
theorem seamFacesBoundarySimple_of_twoSided
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (htwoSided : data.SeamFacesTwoSided) :
    data.SeamFacesBoundarySimple := by
  intro position
  let root := orderedSeamRoot RS data.keep
    data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective
    data.rightInjective position
  unfold orbitFaceBoundary
  apply Finset.card_image_iff.mpr
  intro left hleft right hright hedge
  rcases data.output.edge_fiber_two_cases rfl hedge.symm with heq | heq
  · exact heq.symm
  · exfalso
    apply htwoSided position left
    · change data.output.phi.SameCycle root left
      exact (Quotient.exact ((mem_orbitFaceDarts_iff data.output
        (dartOrbitFace data.output root) left).1 hleft)).symm
    · have hleftFace : dartOrbitFace data.output left =
          dartOrbitFace data.output root :=
        (mem_orbitFaceDarts_iff data.output
          (dartOrbitFace data.output root) left).1 hleft
      have hrightFace : dartOrbitFace data.output right =
          dartOrbitFace data.output root :=
        (mem_orbitFaceDarts_iff data.output
          (dartOrbitFace data.output root) right).1 hright
      rw [← heq, hleftFace, hrightFace]

/-- Conversely, a simple boundary at every seam root excludes an opposite
dart from the same seam face.  Thus the new pointwise receipt is not a
strengthening or a convenient wrapper: it is equivalent to the previous
finite cardinality statement. -/
theorem seamFacesTwoSided_of_boundarySimple
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hsimple : data.SeamFacesBoundarySimple) :
    data.SeamFacesTwoSided := by
  unfold SeamFacesTwoSided
  intro position
  let root := orderedSeamRoot RS data.keep
    data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective
    data.rightInjective position
  dsimp only
  intro point hcycle hsame
  have hinjective : Set.InjOn data.output.edgeOf
      (orbitFaceDarts data.output (dartOrbitFace data.output root)) := by
    apply Finset.card_image_iff.mp
    exact hsimple position
  have hpointMem : point ∈
      orbitFaceDarts data.output (dartOrbitFace data.output root) := by
    apply (mem_orbitFaceDarts_iff data.output
      (dartOrbitFace data.output root) point).2
    exact Quotient.sound hcycle.symm
  have halphaMem : data.output.alpha point ∈
      orbitFaceDarts data.output (dartOrbitFace data.output root) := by
    apply (mem_orbitFaceDarts_iff data.output
      (dartOrbitFace data.output root) (data.output.alpha point)).2
    exact hsame.symm.trans
      ((mem_orbitFaceDarts_iff data.output
        (dartOrbitFace data.output root) point).1 hpointMem)
  have heq := hinjective hpointMem halphaMem
    (data.output.edge_alpha point).symm
  exact data.output.alpha_fixfree point heq.symm

theorem seamFacesTwoSided_iff_boundarySimple
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :
    data.SeamFacesTwoSided ↔ data.SeamFacesBoundarySimple :=
  ⟨data.seamFacesBoundarySimple_of_twoSided,
    data.seamFacesTwoSided_of_boundarySimple⟩

/-- A source-simple face that does not touch the seam remains simple in the
literal retained-vertex splice.  The proof transports its complete dart cycle
back to the ambient face and uses the computed equality of retained output
edges with ambient edges. -/
theorem output_dartOrbitFace_boundarySimple_of_interior
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (root : data.output.D)
    (hsource :
      (orbitFaceBoundary RS
        (dartOrbitFace RS
          (matchedPartUnderlyingDart RS data.keep
            (orderedCut data.left.crossingEdge)
            (orderedCut data.right.crossingEdge) root))).card =
        (orbitFaceDarts RS
          (dartOrbitFace RS
            (matchedPartUnderlyingDart RS data.keep
              (orderedCut data.left.crossingEdge)
              (orderedCut data.right.crossingEdge) root))).card)
    (hinterior : ∀ point,
      data.output.phi.SameCycle root point →
      ∃ dart : InternalDart RS data.keep, point = Sum.inl dart) :
    (orbitFaceBoundary data.output (dartOrbitFace data.output root)).card =
      (orbitFaceDarts data.output (dartOrbitFace data.output root)).card := by
  let source := data.output.phi
  let forget := matchedPartUnderlyingDart RS data.keep
    (orderedCut data.left.crossingEdge) (orderedCut data.right.crossingEdge)
  have hcomm : ∀ point, source.SameCycle root point →
      forget (source point) = RS.phi (forget point) := by
    intro point hpoint
    rcases hinterior point hpoint with ⟨dart, rfl⟩
    exact orderedCutSplicePhi_interior_underlying RS data.keep
      data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses data.leftInjective
      data.rightInjective data.cover data.disjoint data.outer_kept dart
  have hambientCycle : ∀ point, source.SameCycle root point →
      RS.phi.SameCycle (forget root) (forget point) := by
    intro point hpoint
    rcases hpoint.exists_nat_pow_eq with ⟨power, hpower⟩
    have htransport := map_pow_of_map_apply_on_cycle source RS.phi
      forget root hcomm power
    rw [hpower] at htransport
    rw [htransport]
    exact (Equiv.Perm.sameCycle_pow_right).2
      (Equiv.Perm.SameCycle.refl RS.phi (forget root))
  unfold orbitFaceBoundary
  apply Finset.card_image_iff.mpr
  intro left hleft right hright hedge
  have hleftCycle : source.SameCycle root left := by
    change data.output.phi.SameCycle root left
    exact (Quotient.exact ((mem_orbitFaceDarts_iff data.output
      (dartOrbitFace data.output root) left).1 hleft)).symm
  have hrightCycle : source.SameCycle root right := by
    change data.output.phi.SameCycle root right
    exact (Quotient.exact ((mem_orbitFaceDarts_iff data.output
      (dartOrbitFace data.output root) right).1 hright)).symm
  rcases hinterior left hleftCycle with ⟨leftDart, rfl⟩
  rcases hinterior right hrightCycle with ⟨rightDart, rfl⟩
  have hambientEdge : RS.edgeOf leftDart.1.1 = RS.edgeOf rightDart.1.1 :=
    (retainedInternalSpliceEdge_eq_iff RS data.keep
      data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses data.leftInjective
      data.rightInjective data.cover data.disjoint data.outer_kept
      data.seamEndpoints leftDart rightDart).1 hedge
  let ambientFace := dartOrbitFace RS (forget root)
  have hleftAmbient : leftDart.1.1 ∈ orbitFaceDarts RS ambientFace := by
    apply (mem_orbitFaceDarts_iff RS ambientFace leftDart.1.1).2
    apply Quotient.sound
    exact (hambientCycle (Sum.inl leftDart) hleftCycle).symm
  have hrightAmbient : rightDart.1.1 ∈ orbitFaceDarts RS ambientFace := by
    apply (mem_orbitFaceDarts_iff RS ambientFace rightDart.1.1).2
    apply Quotient.sound
    exact (hambientCycle (Sum.inl rightDart) hrightCycle).symm
  have hinjective : Set.InjOn RS.edgeOf (orbitFaceDarts RS ambientFace) := by
    apply Finset.card_image_iff.mp
    exact hsource
  have hunderlying : leftDart.1.1 = rightDart.1.1 :=
    hinjective hleftAmbient hrightAmbient hambientEdge
  exact congrArg Sum.inl (Subtype.ext (Subtype.ext hunderlying))

/-- If a face meets the seam, the finite receipt at the corresponding ordered
seam root supplies its boundary simplicity.  No arbitrary finite enumeration
is introduced: ordered seam positions already enumerate the literal seam. -/
theorem output_dartOrbitFace_boundarySimple_of_meets_seam
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hseam : data.SeamFacesBoundarySimple)
    (root point : data.output.D)
    (hcycle : data.output.phi.SameCycle root point)
    (hpoint :
      (∃ dart : BoundaryDartOn RS data.keep
          (orderedCut data.left.crossingEdge),
        point = Sum.inr (Sum.inl dart)) ∨
      ∃ dart : BoundaryDartOn RS data.keep
          (orderedCut data.right.crossingEdge),
        point = Sum.inr (Sum.inr dart)) :
    (orbitFaceBoundary data.output (dartOrbitFace data.output root)).card =
      (orbitFaceDarts data.output (dartOrbitFace data.output root)).card := by
  have hpointSeam : IsSeamDart point := by
    rcases hpoint with ⟨left, rfl⟩ | ⟨right, rfl⟩ <;> trivial
  let seamEquiv := orderedSeamPositionEquiv RS data.keep
    data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective
    data.rightInjective
  let marked : {dart // IsSeamDart dart} := ⟨point, hpointSeam⟩
  let position : OrderedSeamPosition n := seamEquiv.symm marked
  have hrootAtPosition :
      orderedSeamRoot RS data.keep
          data.left.crossingEdge data.right.crossingEdge
          data.leftCrosses data.rightCrosses data.leftInjective
          data.rightInjective position = point := by
    exact congrArg Subtype.val (seamEquiv.apply_symm_apply marked)
  have hsameFace : dartOrbitFace data.output root =
      dartOrbitFace data.output
        (orderedSeamRoot RS data.keep
          data.left.crossingEdge data.right.crossingEdge
          data.leftCrosses data.rightCrosses data.leftInjective
          data.rightInjective position) := by
    apply Quotient.sound
    change data.output.phi.SameCycle root _
    simpa only [hrootAtPosition] using hcycle
  rw [hsameFace]
  exact hseam position

end GoertzelV24SpliceUnification.OrderedCutSpliceData

namespace GoertzelV24ClosedWebSpliceBoundarySimplicity

open GoertzelV24AnnularFrontierWeightedCurvature.AnnularFrontier
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebSpliceGraphAnnularEmbedding
open GoertzelV24ClosedWebSpliceGraphGeometry.Instance
open GoertzelV24FaceDualConnectedness
open GoertzelV24FramedAnnularExcess
open GoertzelV24OpenRegionOutputRestriction
open GoertzelV24OpenRegionOutputRestriction.OrderedCutSpliceData
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24SpliceUnification.OrderedCutSpliceData

variable {G : SimpleGraph V} [DecidableRel G.Adj]
  {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
  {n terminalCount faceFragmentCount : Nat}
  {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}


attribute [local instance]
  retainedVertexFintype retainedVertexDecidableEq

local instance sourceEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

local instance outputAdjDecidable
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount) :
    DecidableRel (rotationPrimalGraph splice.output).Adj :=
  Classical.decRel _

/-- Literal non-hole boundary simplicity reduces to the finite seam receipt.
Seam-free faces are transported to source interior faces; the two source hole
faces cannot occur because their protected output images were removed from the
literal interior-face carrier. -/
theorem outputRotation_internalBoundarySimple_of_seam
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole)
    (hseam : splice.SeamFacesBoundarySimple) :
    ∀ face ∈ outputRotationInteriorFaces splice hinner houter,
      (orbitFaceBoundary splice.output face).card =
        (orbitFaceDarts splice.output face).card := by
  intro face hface
  let root := face.out
  have hfaceRoot : dartOrbitFace splice.output root = face := Quotient.out_eq face
  rw [← hfaceRoot]
  rcases splicedFaceCycle_interior_or_meets_seam web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses splice.leftInjective
      splice.rightInjective splice.cover splice.disjoint splice.outer_kept root with
    hinterior | ⟨point, hcycle, hpoint⟩
  · rcases hinterior root (Equiv.Perm.SameCycle.refl splice.output.phi root) with
      ⟨internal, hroot⟩
    have hnotInner : face ≠
        (outputFaceOrbit_of_holeFaceKept splice
          web.annular.cellulation.innerHole hinner).1 := by
      intro heq
      apply (Finset.mem_sdiff.mp hface).2
      rw [heq]
      exact Finset.mem_insert_self _ _
    have hnotOuter : face ≠
        (outputFaceOrbit_of_holeFaceKept splice
          web.annular.cellulation.outerHole houter).1 := by
      intro heq
      apply (Finset.mem_sdiff.mp hface).2
      rw [heq]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    let ambientRoot := matchedPartUnderlyingDart web.annular.RS splice.keep
      (orderedCut splice.left.crossingEdge)
      (orderedCut splice.right.crossingEdge) root
    let ambientFace := dartOrbitFace web.annular.RS ambientRoot
    have hambientNotInner : ambientFace ≠
        web.annular.cellulation.innerHole := by
      intro hambient
      have hdart : dartOrbitFace web.annular.RS internal.1.1 =
          web.annular.cellulation.innerHole := by
        simpa [ambientFace, ambientRoot, hroot, matchedPartUnderlyingDart]
          using hambient
      have hout := outputFaceOrbit_of_holeFaceKept_eq_dartOrbitFace
        splice web.annular.cellulation.innerHole hinner internal.1 hdart
      rw [retainedDartEquivMatchedParts_of_internal splice internal] at hout
      apply hnotInner
      exact hfaceRoot.symm.trans (hroot.symm ▸ hout.symm)
    have hambientNotOuter : ambientFace ≠
        web.annular.cellulation.outerHole := by
      intro hambient
      have hdart : dartOrbitFace web.annular.RS internal.1.1 =
          web.annular.cellulation.outerHole := by
        simpa [ambientFace, ambientRoot, hroot, matchedPartUnderlyingDart]
          using hambient
      have hout := outputFaceOrbit_of_holeFaceKept_eq_dartOrbitFace
        splice web.annular.cellulation.outerHole houter internal.1 hdart
      rw [retainedDartEquivMatchedParts_of_internal splice internal] at hout
      apply hnotOuter
      exact hfaceRoot.symm.trans (hroot.symm ▸ hout.symm)
    have hambientInterior : ambientFace ∈
        web.annular.cellulation.interiorFaces := by
      simp [FramedAnnularCellulation.interiorFaces,
        FramedAnnularCellulation.holeFaces, hambientNotInner,
        hambientNotOuter]
    have hsource :
        (orbitFaceBoundary web.annular.RS ambientFace).card =
          (orbitFaceDarts web.annular.RS ambientFace).card := by
      exact web.geometry.internalBoundarySimple ambientFace hambientInterior
    exact output_dartOrbitFace_boundarySimple_of_interior splice root
      hsource hinterior
  · change splice.output.phi.SameCycle root point at hcycle
    exact output_dartOrbitFace_boundarySimple_of_meets_seam splice hseam
      root point hcycle hpoint

/-- The graph-backed output geometry now consumes only the finite seam-local
boundary receipt, plus the independently open literal internal-dual
connectedness receipt. -/
theorem outputGeometryOfSeamBoundarySimple
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole)
    (hsimple : OrderedCutEndpointSimple web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses)
    (hretained :
      (retainedAmbientPrimalGraph web.annular.RS splice.keep).Connected)
    (hbalance : splice.LocalEulerBalance)
    (hprofile : splice.SeamFacesMeetFive)
    (hseamBoundarySimple : splice.SeamFacesBoundarySimple)
    (hdualConnected :
      (interiorDualGraph (orbitFaceBoundary splice.output)
        (outputRotationInteriorFaces splice hinner houter)).Connected) :
    AnnularFrontierGeometry
      (outputAnnularEmbedding splice hinner houter hsimple hretained hbalance) := by
  exact outputGeometryOfLiteral splice hinner houter hsimple hretained
    hbalance hprofile
    (outputRotation_internalBoundarySimple_of_seam splice hinner houter
      hseamBoundarySimple)
    hdualConnected

end GoertzelV24ClosedWebSpliceBoundarySimplicity

end

end Mettapedia.GraphTheory.FourColor
