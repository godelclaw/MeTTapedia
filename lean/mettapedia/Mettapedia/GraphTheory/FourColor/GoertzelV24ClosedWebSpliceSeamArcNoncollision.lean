import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebSpliceBoundarySimplicity

/-!
# Finite seam-arc noncollision for the literal ordered-cut splice

Addendum XXVII attributes preservation of noncrossing to gluing along simple
transversals and layer boundaries.  This module decomposes the remaining L1
seam-local two-sidedness receipt into the canonical finite arcs between
successive seam hits.

The exact finite condition has two parts: one arc never repeats an output
edge, and two distinct arcs belonging to the same completed face have
disjoint edge supports.  Their conjunction is proved equivalent to the
previous seam-boundary simplicity receipt.  This is a reindexing and
factorization of the open obligation, not its construction from the physical
source crosscuts.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24SeamFaceArc
open GoertzelV24SeamFaceArcPartition
open GoertzelV24SpliceUnification

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace GoertzelV24SpliceUnification.OrderedCutSpliceData

variable {RS : RotationSystem V E}
  {n terminalCount faceFragmentCount : Nat}

/-- Actual seam darts, before they are reindexed by ordered positions. -/
abbrev SeamMarkedDart
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :=
  { point : data.output.D // IsSeamDart point }

/-- Finite positions from a seam dart up to, but excluding, its next seam
hit in the completed output face. -/
abbrev SeamArcStep
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (root : data.SeamMarkedDart) :=
  Fin (firstPositiveHitTime data.output.phi IsSeamDart root.1 root.2)

/-- Literal output dart at one position of a canonical seam-return arc. -/
def seamArcPoint
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (root : data.SeamMarkedDart) (step : data.SeamArcStep root) :
    data.output.D :=
  (data.output.phi ^ step.val) root.1

/-- Literal output edge at one position of a canonical seam-return arc. -/
def seamArcEdge
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (root : data.SeamMarkedDart) (step : data.SeamArcStep root) :=
  data.output.edgeOf (data.seamArcPoint root step)

/-- Finite edge support of one canonical seam-return arc. -/
def seamArcEdges
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (root : data.SeamMarkedDart) :=
  Finset.univ.image (data.seamArcEdge root)

/-- The first finite half of L1 seam noncrossing: no individual canonical
return arc traverses one output edge twice. -/
def SeamArcsInternallySimple
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) : Prop :=
  ∀ root : data.SeamMarkedDart, Function.Injective (data.seamArcEdge root)

/-- The second finite half of L1 seam noncrossing: distinct canonical arcs
joined into one completed output face have disjoint edge supports. -/
def SeamArcsPairwiseEdgeDisjoint
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) : Prop :=
  ∀ first second : data.SeamMarkedDart,
    data.output.phi.SameCycle first.1 second.1 → first ≠ second →
      Disjoint (data.seamArcEdges first) (data.seamArcEdges second)

/-- Exact finite noncollision bundle for the canonical seam-return arcs. -/
def SeamArcNoncollision
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) : Prop :=
  data.SeamArcsInternallySimple ∧ data.SeamArcsPairwiseEdgeDisjoint

/-- Recover the fixed ordered seam coordinate of an actual marked dart. -/
def seamPositionOf
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (root : data.SeamMarkedDart) : OrderedSeamPosition n :=
  (orderedSeamPositionEquiv RS data.keep
    data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective
    data.rightInjective).symm root

@[simp]
theorem orderedSeamRoot_seamPositionOf
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (root : data.SeamMarkedDart) :
    orderedSeamRoot RS data.keep
        data.left.crossingEdge data.right.crossingEdge
        data.leftCrosses data.rightCrosses data.leftInjective
        data.rightInjective (data.seamPositionOf root) = root.1 := by
  exact congrArg Subtype.val
    ((orderedSeamPositionEquiv RS data.keep
      data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses data.leftInjective
      data.rightInjective).apply_symm_apply root)

/-- Internal simplicity and pairwise disjointness of the finite canonical
arcs make every seam-root output face boundary simple. -/
theorem seamFacesBoundarySimple_of_arcNoncollision
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hnoncollision : data.SeamArcNoncollision) :
    data.SeamFacesBoundarySimple := by
  intro position
  let root := orderedSeamRoot RS data.keep
    data.left.crossingEdge data.right.crossingEdge
    data.leftCrosses data.rightCrosses data.leftInjective
    data.rightInjective position
  have hroot : IsSeamDart root :=
    orderedSeamRoot_isSeam RS data.keep
      data.left.crossingEdge data.right.crossingEdge
      data.leftCrosses data.rightCrosses data.leftInjective
      data.rightInjective position
  unfold orbitFaceBoundary
  apply Finset.card_image_iff.mpr
  intro left hleft right hright hedge
  have hleftCycle : data.output.phi.SameCycle root left := by
    exact (Quotient.exact ((mem_orbitFaceDarts_iff data.output
      (dartOrbitFace data.output root) left).1 hleft)).symm
  have hrightCycle : data.output.phi.SameCycle root right := by
    exact (Quotient.exact ((mem_orbitFaceDarts_iff data.output
      (dartOrbitFace data.output root) right).1 hright)).symm
  have hleftArc : left ∈ allFirstHitArcDarts data.output.phi IsSeamDart :=
    mem_allFirstHitArcDarts_of_cycle_meets data.output.phi IsSeamDart left
      ⟨root, hroot, hleftCycle⟩
  have hrightArc : right ∈ allFirstHitArcDarts data.output.phi IsSeamDart :=
    mem_allFirstHitArcDarts_of_cycle_meets data.output.phi IsSeamDart right
      ⟨root, hroot, hrightCycle⟩
  rw [allFirstHitArcDarts] at hleftArc hrightArc
  rcases Finset.mem_image.1 hleftArc with
    ⟨⟨leftRoot, leftStep⟩, _, hleftPoint⟩
  rcases Finset.mem_image.1 hrightArc with
    ⟨⟨rightRoot, rightStep⟩, _, hrightPoint⟩
  by_cases hroots : leftRoot = rightRoot
  · subst rightRoot
    have hsteps : leftStep = rightStep := hnoncollision.1 leftRoot (by
      change data.output.edgeOf
          (allFirstHitArcPoint data.output.phi IsSeamDart
            ⟨leftRoot, leftStep⟩) =
        data.output.edgeOf
          (allFirstHitArcPoint data.output.phi IsSeamDart
            ⟨leftRoot, rightStep⟩)
      rw [hleftPoint, hrightPoint]
      exact hedge)
    subst rightStep
    exact hleftPoint.symm.trans hrightPoint
  · have hleftRootCycle : data.output.phi.SameCycle leftRoot.1 left := by
      rw [← hleftPoint]
      exact (Equiv.Perm.sameCycle_pow_right).2
        (Equiv.Perm.SameCycle.refl data.output.phi leftRoot.1)
    have hrightRootCycle : data.output.phi.SameCycle rightRoot.1 right := by
      rw [← hrightPoint]
      exact (Equiv.Perm.sameCycle_pow_right).2
        (Equiv.Perm.SameCycle.refl data.output.phi rightRoot.1)
    have hrootCycle : data.output.phi.SameCycle leftRoot.1 rightRoot.1 :=
      hleftRootCycle.trans (hleftCycle.symm.trans
        (hrightCycle.trans hrightRootCycle.symm))
    have hdisjoint := hnoncollision.2 leftRoot rightRoot hrootCycle hroots
    have hleftMem : data.output.edgeOf left ∈ data.seamArcEdges leftRoot := by
      apply Finset.mem_image.2
      refine ⟨leftStep, Finset.mem_univ _, ?_⟩
      change data.output.edgeOf
          (allFirstHitArcPoint data.output.phi IsSeamDart
            ⟨leftRoot, leftStep⟩) = data.output.edgeOf left
      rw [hleftPoint]
    have hrightMem : data.output.edgeOf right ∈ data.seamArcEdges rightRoot := by
      apply Finset.mem_image.2
      refine ⟨rightStep, Finset.mem_univ _, ?_⟩
      change data.output.edgeOf
          (allFirstHitArcPoint data.output.phi IsSeamDart
            ⟨rightRoot, rightStep⟩) = data.output.edgeOf right
      rw [hrightPoint]
    exact False.elim
      ((Finset.disjoint_left.1 hdisjoint) hleftMem (hedge ▸ hrightMem))

/-- Conversely, seam-boundary simplicity supplies both finite arc receipts.
Thus the bundle is a factorization of the old condition, not a strengthening. -/
theorem seamArcNoncollision_of_boundarySimple
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount)
    (hsimple : data.SeamFacesBoundarySimple) :
    data.SeamArcNoncollision := by
  constructor
  · intro root left right hedge
    have hinjective : Set.InjOn data.output.edgeOf
        (orbitFaceDarts data.output (dartOrbitFace data.output root.1)) := by
      apply Finset.card_image_iff.mp
      have hcard := hsimple (data.seamPositionOf root)
      unfold orbitFaceBoundary at hcard
      simpa using hcard
    have hleftMem : data.seamArcPoint root left ∈
        orbitFaceDarts data.output (dartOrbitFace data.output root.1) := by
      apply (mem_orbitFaceDarts_iff data.output
        (dartOrbitFace data.output root.1) (data.seamArcPoint root left)).2
      apply Quotient.sound
      exact ((Equiv.Perm.sameCycle_pow_right).2
        (Equiv.Perm.SameCycle.refl data.output.phi root.1)).symm
    have hrightMem : data.seamArcPoint root right ∈
        orbitFaceDarts data.output (dartOrbitFace data.output root.1) := by
      apply (mem_orbitFaceDarts_iff data.output
        (dartOrbitFace data.output root.1) (data.seamArcPoint root right)).2
      apply Quotient.sound
      exact ((Equiv.Perm.sameCycle_pow_right).2
        (Equiv.Perm.SameCycle.refl data.output.phi root.1)).symm
    have hpoints : data.seamArcPoint root left =
        data.seamArcPoint root right :=
      hinjective hleftMem hrightMem hedge
    have harcs :
        (⟨root, left⟩ : AllFirstHitArcPositions
          data.output.phi IsSeamDart) = ⟨root, right⟩ :=
      allFirstHitArcPoint_injective data.output.phi IsSeamDart hpoints
    cases harcs
    rfl
  · intro first second hcycle hne
    apply Finset.disjoint_left.2
    intro edge hfirstMem hsecondMem
    rcases Finset.mem_image.1 hfirstMem with
      ⟨firstStep, _, hfirstEdge⟩
    rcases Finset.mem_image.1 hsecondMem with
      ⟨secondStep, _, hsecondEdge⟩
    have hinjective : Set.InjOn data.output.edgeOf
        (orbitFaceDarts data.output (dartOrbitFace data.output first.1)) := by
      apply Finset.card_image_iff.mp
      have hcard := hsimple (data.seamPositionOf first)
      unfold orbitFaceBoundary at hcard
      simpa using hcard
    have hfirstPointCycle : data.output.phi.SameCycle first.1
        (data.seamArcPoint first firstStep) :=
      (Equiv.Perm.sameCycle_pow_right).2
        (Equiv.Perm.SameCycle.refl data.output.phi first.1)
    have hsecondPointCycle : data.output.phi.SameCycle first.1
        (data.seamArcPoint second secondStep) :=
      hcycle.trans ((Equiv.Perm.sameCycle_pow_right).2
        (Equiv.Perm.SameCycle.refl data.output.phi second.1))
    have hfirstPointMem : data.seamArcPoint first firstStep ∈
        orbitFaceDarts data.output (dartOrbitFace data.output first.1) := by
      apply (mem_orbitFaceDarts_iff data.output
        (dartOrbitFace data.output first.1)
        (data.seamArcPoint first firstStep)).2
      exact Quotient.sound hfirstPointCycle.symm
    have hsecondPointMem : data.seamArcPoint second secondStep ∈
        orbitFaceDarts data.output (dartOrbitFace data.output first.1) := by
      apply (mem_orbitFaceDarts_iff data.output
        (dartOrbitFace data.output first.1)
        (data.seamArcPoint second secondStep)).2
      exact Quotient.sound hsecondPointCycle.symm
    have hpoints : data.seamArcPoint first firstStep =
        data.seamArcPoint second secondStep := by
      apply hinjective hfirstPointMem hsecondPointMem
      exact hfirstEdge.trans hsecondEdge.symm
    have harcs :
        (⟨first, firstStep⟩ : AllFirstHitArcPositions
          data.output.phi IsSeamDart) = ⟨second, secondStep⟩ :=
      allFirstHitArcPoint_injective data.output.phi IsSeamDart hpoints
    exact hne (congrArg Sigma.fst harcs)

theorem seamArcNoncollision_iff_boundarySimple
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :
    data.SeamArcNoncollision ↔ data.SeamFacesBoundarySimple :=
  ⟨data.seamFacesBoundarySimple_of_arcNoncollision,
    data.seamArcNoncollision_of_boundarySimple⟩

theorem seamArcNoncollision_iff_twoSided
    (data : OrderedCutSpliceData RS n terminalCount faceFragmentCount) :
    data.SeamArcNoncollision ↔ data.SeamFacesTwoSided :=
  data.seamArcNoncollision_iff_boundarySimple.trans
    data.seamFacesTwoSided_iff_boundarySimple.symm

end GoertzelV24SpliceUnification.OrderedCutSpliceData

end

end Mettapedia.GraphTheory.FourColor
