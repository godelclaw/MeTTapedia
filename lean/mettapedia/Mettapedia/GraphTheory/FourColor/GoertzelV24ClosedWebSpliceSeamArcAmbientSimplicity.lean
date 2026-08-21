import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceSeamArcNoncollision
import Mettapedia.GraphTheory.FourColor.GoertzelV24SeamArcAmbientFace

/-!
# Ambient-face simplicity of canonical splice seam arcs

Addendum XXVII attributes preservation of noncrossing to simple transversals
and the homeomorphic gluing of complementary pieces.  This module proves the
first finite half of that L1 statement: every canonical seam-return arc has
an injective output-edge trace.

Positive positions on an arc are transported to consecutive darts of one old
ambient face.  Source-face boundary simplicity therefore forbids a repeated
retained edge, while the new seam edge at position zero is disjoint from every
retained internal edge by the literal edge decomposition.  For the actual
closed-web annulus the two protected hole faces are seam-free, so the ambient
face is an interior face and the existing source geometry supplies its
simplicity.

This does not prove noncollision between distinct arcs and does not close L1.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedSpliceEdgeDecomposition
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor
open GoertzelV24SeamArcAmbientFace
open GoertzelV24SeamFaceArc
open GoertzelV24SeamFaceArcPartition
open GoertzelV24SpliceUnification

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace GoertzelV24SpliceUnification.OrderedCutSpliceData

variable {RS : RotationSystem V E}
  {n terminalCount faceFragmentCount : Nat}

/-- Every old ambient face occurrence traversed by a canonical seam arc has
an injective edge boundary.  This is the exact source-side input used below;
the closed-web specialization derives it from the existing annular geometry. -/
def SeamArcAmbientFacesBoundarySimple
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) : Prop :=
  ∀ root : data.SeamMarkedDart,
    let ambientRoot := orderedCutSpliceAmbientFaceRoot RS data.keep
      data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses data.leftInjective
      data.rightInjective data.cover data.disjoint data.outer_kept root.1
    (orbitFaceBoundary RS (dartOrbitFace RS ambientRoot)).card =
      (orbitFaceDarts RS (dartOrbitFace RS ambientRoot)).card

/-- The new seam edge at position zero of a canonical arc cannot reappear at
a positive position, since every positive position is an old retained edge. -/
theorem seamArcEdge_zero_ne_of_pos
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (root : data.SeamMarkedDart) (step : data.SeamArcStep root)
    (hstep : 0 < step.val) :
    data.seamArcEdge root ⟨0, by exact hstep.trans step.isLt⟩ ≠
      data.seamArcEdge root step := by
  rcases orderedCutSplicePhi_between_seams_is_interior RS data.keep
      data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses data.leftInjective
      data.rightInjective data.cover data.disjoint data.outer_kept
      root.1 root.2 hstep step.isLt with ⟨dart, hdart⟩
  have hpoint : data.seamArcPoint root step = Sum.inl dart := by
    exact hdart
  intro hedge
  let rewired := orderedCutRetainedVertexRewiredDartSystem RS data.keep
    data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective
    data.rightInjective data.cover data.disjoint data.outer_kept
    data.seamEndpoints
  have hedge' : rewired.edgeOf root.1 = rewired.edgeOf (Sum.inl dart) := by
    change data.output.edgeOf root.1 =
      data.output.edgeOf (data.seamArcPoint root step) at hedge
    rw [hpoint] at hedge
    exact hedge
  have hcases := (rewired.edgeOf_eq_edgeOf_iff _ _).1 hedge'
  rcases root with ⟨root, hroot⟩
  rcases root with internal | side
  · exact False.elim hroot
  · rcases side with left | right
    · simp [rewired,
        orderedCutRetainedVertexRewiredDartSystem,
        orderedCutRewiredDartSystem,
        MatchedSeam.Data.toRewiredDartSystem,
        orderedCutMatchedSeamData] at hcases
    · simp [rewired,
        orderedCutRetainedVertexRewiredDartSystem,
        orderedCutRewiredDartSystem,
        MatchedSeam.Data.toRewiredDartSystem,
        orderedCutMatchedSeamData] at hcases

/-- Source-face boundary simplicity makes every canonical seam-return arc
internally simple.  Positive positions transport to one old facial orbit;
position zero is separated from them by `seamArcEdge_zero_ne_of_pos`. -/
theorem seamArcsInternallySimple_of_ambientFacesBoundarySimple
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hsource : data.SeamArcAmbientFacesBoundarySimple) :
    data.SeamArcsInternallySimple := by
  intro root left right hedge
  by_cases hleftZero : left.val = 0
  · have hrightZero : right.val = 0 := by
      by_contra hright
      have hrightPos : 0 < right.val := Nat.pos_of_ne_zero hright
      have hleft : left = ⟨0, hrightPos.trans right.isLt⟩ := Fin.ext hleftZero
      exact data.seamArcEdge_zero_ne_of_pos root right hrightPos
        (by simpa [hleft] using hedge)
    exact Fin.ext (hleftZero.trans hrightZero.symm)
  · by_cases hrightZero : right.val = 0
    · have hleftPos : 0 < left.val := Nat.pos_of_ne_zero hleftZero
      have hright : right = ⟨0, hleftPos.trans left.isLt⟩ := Fin.ext hrightZero
      exact False.elim (data.seamArcEdge_zero_ne_of_pos root left hleftPos
        (by simpa [hright] using hedge.symm))
    · have hleftPos : 0 < left.val := Nat.pos_of_ne_zero hleftZero
      have hrightPos : 0 < right.val := Nat.pos_of_ne_zero hrightZero
      rcases orderedCutSplicePhi_between_seams_is_interior RS data.keep
          data.left.crossingEdge data.right.crossingEdge
          data.leftCrosses data.rightCrosses data.leftInjective
          data.rightInjective data.cover data.disjoint data.outer_kept
          root.1 root.2 hleftPos left.isLt with ⟨leftDart, hleftDart⟩
      rcases orderedCutSplicePhi_between_seams_is_interior RS data.keep
          data.left.crossingEdge data.right.crossingEdge
          data.leftCrosses data.rightCrosses data.leftInjective
          data.rightInjective data.cover data.disjoint data.outer_kept
          root.1 root.2 hrightPos right.isLt with ⟨rightDart, hrightDart⟩
      have hleftPoint : data.seamArcPoint root left = Sum.inl leftDart := by
        exact hleftDart
      have hrightPoint : data.seamArcPoint root right = Sum.inl rightDart := by
        exact hrightDart
      have hambientEdge : RS.edgeOf leftDart.1.1 =
          RS.edgeOf rightDart.1.1 := by
        apply (retainedInternalSpliceEdge_eq_iff RS data.keep
          data.left.crossingEdge data.right.crossingEdge
          data.leftCrosses data.rightCrosses data.leftInjective
          data.rightInjective data.cover data.disjoint data.outer_kept
          data.seamEndpoints leftDart rightDart).1
        change data.output.edgeOf (data.seamArcPoint root left) =
          data.output.edgeOf (data.seamArcPoint root right) at hedge
        rw [hleftPoint, hrightPoint] at hedge
        exact hedge
      let ambientRoot := orderedCutSpliceAmbientFaceRoot RS data.keep
        data.left.crossingEdge data.right.crossingEdge
        data.leftCrosses data.rightCrosses data.leftInjective
        data.rightInjective data.cover data.disjoint data.outer_kept root.1
      let ambientFace := dartOrbitFace RS ambientRoot
      have hinjective : Set.InjOn RS.edgeOf
          (orbitFaceDarts RS ambientFace) := by
        apply Finset.card_image_iff.mp
        exact hsource root
      have hleftTransport :=
        orderedCutSplicePhi_pow_underlying_eq_ambient_phi_pow RS data.keep
          data.left.crossingEdge data.right.crossingEdge
          data.leftCrosses data.rightCrosses data.leftInjective
          data.rightInjective data.cover data.disjoint data.outer_kept
          root.1 root.2 hleftPos (Nat.le_of_lt left.isLt)
      have hrightTransport :=
        orderedCutSplicePhi_pow_underlying_eq_ambient_phi_pow RS data.keep
          data.left.crossingEdge data.right.crossingEdge
          data.leftCrosses data.rightCrosses data.leftInjective
          data.rightInjective data.cover data.disjoint data.outer_kept
          root.1 root.2 hrightPos (Nat.le_of_lt right.isLt)
      have hleftAmbient : leftDart.1.1 ∈ orbitFaceDarts RS ambientFace := by
        apply (mem_orbitFaceDarts_iff RS ambientFace leftDart.1.1).2
        apply Quotient.sound
        rw [hleftDart] at hleftTransport
        change leftDart.1.1 = (RS.phi ^ left.val) ambientRoot at hleftTransport
        rw [hleftTransport]
        exact ((Equiv.Perm.sameCycle_pow_right).2
          (Equiv.Perm.SameCycle.refl RS.phi ambientRoot)).symm
      have hrightAmbient : rightDart.1.1 ∈ orbitFaceDarts RS ambientFace := by
        apply (mem_orbitFaceDarts_iff RS ambientFace rightDart.1.1).2
        apply Quotient.sound
        rw [hrightDart] at hrightTransport
        change rightDart.1.1 = (RS.phi ^ right.val) ambientRoot at hrightTransport
        rw [hrightTransport]
        exact ((Equiv.Perm.sameCycle_pow_right).2
          (Equiv.Perm.SameCycle.refl RS.phi ambientRoot)).symm
      have hunderlying : leftDart.1.1 = rightDart.1.1 :=
        hinjective hleftAmbient hrightAmbient hambientEdge
      have hpoints : data.seamArcPoint root left =
          data.seamArcPoint root right := by
        rw [hleftPoint, hrightPoint]
        exact congrArg Sum.inl (Subtype.ext (Subtype.ext hunderlying))
      have harcs :
          (⟨root, left⟩ : AllFirstHitArcPositions
            data.output.phi IsSeamDart) = ⟨root, right⟩ :=
        allFirstHitArcPoint_injective data.output.phi IsSeamDart hpoints
      cases harcs
      rfl

end GoertzelV24SpliceUnification.OrderedCutSpliceData

namespace GoertzelV24ClosedWebSpliceSeamArcAmbientSimplicity

open GoertzelV24AnnularFrontierWeightedCurvature.AnnularFrontier
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebAtGoodWord
open GoertzelV24ClosedWebAtGoodWord.Instance
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FramedAnnularExcess
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24SpliceUnification.OrderedCutSpliceData

variable {G : SimpleGraph V} [DecidableRel G.Adj]
  {data : AnnularBoundaryData G 5} {coloring : G.EdgeColoring Color}
  {n terminalCount faceFragmentCount : Nat}
  {web : GoertzelV24ClosedWebAtGoodWord.Instance data coloring}

attribute [-instance]
  GoertzelV24OpenRegionRotation.retainedVertexDecidableEq

attribute [local instance]
  retainedVertexFintype retainedVertexDecidableEq

local instance sourceEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- For the actual closed-web annulus, preservation of both hole faces makes
every seam-arc ambient root an interior face.  The already-constructed source
geometry therefore supplies internal simplicity of all canonical seam arcs. -/
theorem seamArcsInternallySimple
    (splice : OrderedCutSpliceData web.annular.RS n terminalCount
      faceFragmentCount)
    (hinner : HoleFaceKept splice web.annular.cellulation.innerHole)
    (houter : HoleFaceKept splice web.annular.cellulation.outerHole) :
    splice.SeamArcsInternallySimple := by
  apply splice.seamArcsInternallySimple_of_ambientFacesBoundarySimple
  intro root
  let ambientRoot := orderedCutSpliceAmbientFaceRoot web.annular.RS splice.keep
    splice.left.crossingEdge splice.right.crossingEdge
    splice.leftCrosses splice.rightCrosses splice.leftInjective
    splice.rightInjective splice.cover splice.disjoint splice.outer_kept root.1
  let ambientFace := dartOrbitFace web.annular.RS ambientRoot
  have hrootDeleted : ¬ splice.keep (web.annular.RS.vertOf ambientRoot) := by
    exact not_keep_orderedCutSpliceAmbientFaceRoot web.annular.RS splice.keep
      splice.left.crossingEdge splice.right.crossingEdge
      splice.leftCrosses splice.rightCrosses splice.leftInjective
      splice.rightInjective splice.cover splice.disjoint splice.outer_kept
      root.1 root.2
  have hnotInner : ambientFace ≠ web.annular.cellulation.innerHole := by
    intro hface
    exact hrootDeleted (hinner ambientRoot hface)
  have hnotOuter : ambientFace ≠ web.annular.cellulation.outerHole := by
    intro hface
    exact hrootDeleted (houter ambientRoot hface)
  have hinterior : ambientFace ∈
      web.annular.cellulation.interiorFaces := by
    simp [FramedAnnularCellulation.interiorFaces,
      FramedAnnularCellulation.holeFaces, hnotInner, hnotOuter]
  exact web.geometry.internalBoundarySimple ambientFace hinterior

end GoertzelV24ClosedWebSpliceSeamArcAmbientSimplicity

end

end Mettapedia.GraphTheory.FourColor
