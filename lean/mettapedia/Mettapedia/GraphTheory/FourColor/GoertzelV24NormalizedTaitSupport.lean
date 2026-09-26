import Mettapedia.GraphTheory.FourColor.GoertzelV24PhysicalClosedCountBridge

/-!
# A finite normalized Count receipt

The tree descent compares pieces whose literal boundary-dart carriers need not
be definitionally equal.  A coordinate equivalence from each carrier to
`Fin k` removes that irrelevant difference.  The receipt stored at the cut is
the finite set of genuine Tait words realized after this reindexing.

This file deliberately records only the colouring component of a typed seam
state.  The cyclic boundary order belongs to the separate seam-type component:
forgetting it here must not make an orientation-sensitive physical splice look
valid.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24NormalizedTaitSupport

open GoertzelV24OpenTangleComposition
open GoertzelV24PhysicalClosedCountBridge
open GoertzelV24RawNooseCountPumping
open GoertzelV24ClosedCountReplacement

universe u

variable {W J R : Type u} [Fintype W] [DecidableEq W]
  [Fintype J] [DecidableEq J] [Fintype R] [DecidableEq R]

/-- The standard `k`-port coordinate carrier, lifted into the universe of the
physical tangle. -/
abbrev StandardPort (k : Nat) := ULift.{u} (Fin k)

/-- The exact finite colouring receipt of an inner piece, after transporting
its boundary carrier to the standard coordinate type `Fin k`. -/
noncomputable def normalizedTaitInnerSupport (k : Nat)
    (right : OpenTangleData W J R) (coordinate : R ≃ StandardPort k) :
    Finset (CutWord (StandardPort k)) := by
  classical
  exact Finset.univ.filter fun word =>
    word ∈ taitInnerSupport
      (rightClosedPortTangle right coordinate.symm)

@[simp]
theorem mem_normalizedTaitInnerSupport (k : Nat)
    (right : OpenTangleData W J R) (coordinate : R ≃ StandardPort k)
    (word : CutWord (StandardPort k)) :
    word ∈ normalizedTaitInnerSupport k right coordinate ↔
      word ∈ taitInnerSupport
        (rightClosedPortTangle right coordinate.symm) := by
  simp [normalizedTaitInnerSupport]

/-- Equality of finite normalized receipts is exactly equality of the support
sets consumed by physical zero-Count replacement. -/
theorem taitInnerSupport_eq_of_normalized_eq (k : Nat)
    (right : OpenTangleData W J R) (coordinate : R ≃ StandardPort k)
    {W' J' R' : Type u} [Fintype W'] [DecidableEq W']
    [Fintype J'] [DecidableEq J'] [Fintype R'] [DecidableEq R']
    (right' : OpenTangleData W' J' R')
    (coordinate' : R' ≃ StandardPort k)
    (hsupport : normalizedTaitInnerSupport k right coordinate =
      normalizedTaitInnerSupport k right' coordinate') :
    taitInnerSupport (rightClosedPortTangle right coordinate.symm) =
      taitInnerSupport (rightClosedPortTangle right' coordinate'.symm) := by
  ext word
  have hmem := congrArg (fun support => word ∈ support) hsupport
  simpa using hmem

/-- A smaller inner support preserves zero Count: every boundary word of a
colouring of the replacement also extends through the original inner piece.
The inclusion points from the new piece to the old piece. -/
theorem not_composeRotationSystem_taitColorable_of_normalized_subset
    (k : Nat)
    {V I : Type u} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (left : OpenTangleData V I (StandardPort k))
    (right : OpenTangleData W J R) (coordinate : R ≃ StandardPort k)
    {W' J' R' : Type u} [Fintype W'] [DecidableEq W']
    [Fintype J'] [DecidableEq J'] [Fintype R'] [DecidableEq R']
    (right' : OpenTangleData W' J' R')
    (coordinate' : R' ≃ StandardPort k)
    (hsupport : normalizedTaitInnerSupport k right' coordinate' ⊆
      normalizedTaitInnerSupport k right coordinate)
    (hzero : ¬ ∃ coloring :
        (left.composeRotationSystem right coordinate.symm).EdgeColoring Color,
      (left.composeRotationSystem right coordinate.symm).IsTaitEdgeColoring
        coloring) :
    ¬ ∃ coloring :
        (left.composeRotationSystem right' coordinate'.symm).EdgeColoring Color,
      (left.composeRotationSystem right' coordinate'.symm).IsTaitEdgeColoring
        coloring := by
  intro hnew
  have hclosed := (closedColorable_iff_composeRotationSystem_taitColorable
    left right' coordinate'.symm).2 hnew
  obtain ⟨word, houter, hinner⟩ := (closedColorable_iff
    (leftClosedPortTangle left)
    (rightClosedPortTangle right' coordinate'.symm)).1 hclosed
  obtain ⟨taitWord, htait, hforget⟩ := exists_cutWord_of_mem_innerSupport
    (rightClosedPortTangle right' coordinate'.symm) hinner
  have hold := (mem_normalizedTaitInnerSupport k right coordinate taitWord).1
    (hsupport ((mem_normalizedTaitInnerSupport k right' coordinate' taitWord).2
      htait))
  apply hzero
  apply (closedColorable_iff_composeRotationSystem_taitColorable
    left right coordinate.symm).1
  apply (closedColorable_iff (leftClosedPortTangle left)
    (rightClosedPortTangle right coordinate.symm)).2
  refine ⟨word, houter, ?_⟩
  change cutWordColor taitWord ∈
    innerSupport (rightClosedPortTangle right coordinate.symm) at hold
  simpa only [hforget] using hold

/-- Equality is a sufficient special case of one-sided support replacement. -/
theorem not_composeRotationSystem_taitColorable_of_normalized_eq
    (k : Nat)
    {V I : Type u} [Fintype V] [DecidableEq V]
    [Fintype I] [DecidableEq I]
    (left : OpenTangleData V I (StandardPort k))
    (right : OpenTangleData W J R) (coordinate : R ≃ StandardPort k)
    {W' J' R' : Type u} [Fintype W'] [DecidableEq W']
    [Fintype J'] [DecidableEq J'] [Fintype R'] [DecidableEq R']
    (right' : OpenTangleData W' J' R')
    (coordinate' : R' ≃ StandardPort k)
    (hsupport : normalizedTaitInnerSupport k right coordinate =
      normalizedTaitInnerSupport k right' coordinate')
    (hzero : ¬ ∃ coloring :
        (left.composeRotationSystem right coordinate.symm).EdgeColoring Color,
      (left.composeRotationSystem right coordinate.symm).IsTaitEdgeColoring
        coloring) :
    ¬ ∃ coloring :
        (left.composeRotationSystem right' coordinate'.symm).EdgeColoring Color,
      (left.composeRotationSystem right' coordinate'.symm).IsTaitEdgeColoring
        coloring :=
  not_composeRotationSystem_taitColorable_of_normalized_subset
    k left right coordinate right' coordinate' hsupport.ge hzero

/-- The receipt type has the advertised raw size `2^(3^k)`.  Reachability
minimization may make it much smaller, but is not a logical premise. -/
theorem card_normalizedSupportType (k : Nat) :
    Fintype.card (Finset (CutWord (StandardPort.{u} k))) =
      2 ^ (3 ^ k) := by
  simpa [StandardPort] using
    (card_supports (J := StandardPort.{u} k))

end GoertzelV24NormalizedTaitSupport

end Mettapedia.GraphTheory.FourColor
