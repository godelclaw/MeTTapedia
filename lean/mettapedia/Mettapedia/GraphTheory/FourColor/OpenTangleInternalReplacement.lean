import Mettapedia.GraphTheory.FourColor.SmallCutReplacementCore
import Mettapedia.GraphTheory.FourColor.SerialTangleSmallCutTransfer

/-!
# Connected bridgeless interiors under serial sewing and replacement

The criteria refer to the actual interior-edge multigraph of an open
tangle. Serial sewing through at least two ports preserves the conditions.
In a closed sewing context, exchanging any two nonempty interiors with
these conditions preserves connectedness and bridge-freedom of the result.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleInternalReplacement

open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open GoertzelV24BoundaryEssentialGluing Multigraph
open BoundarySmallCutProfile SmallCutConnectedBridgeless SmallCutReplacementCore
open SerialTangleSmallCutTransfer OpenTangleCutDartSum
open GoertzelV24FaceDualConnectedness GoertzelV24RotationEdgeBridge

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W I J L P R : Type*}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype P]

/-- The seam must have at least two distinct edge identifiers. Port vertices
may coincide, and parallel seam edges are retained. -/
theorem serial_no_small_cut (A : TwoSidedOpenTangleData V I L P)
    (B : TwoSidedOpenTangleData W J P R)
    (hA : ¬ HasSmallCut (sideMultigraph (asOpen A)))
    (hB : ¬ HasSmallCut (sideMultigraph (asOpen B))) (hp : 2 ≤ Fintype.card P) :
    ¬ HasSmallCut (sideMultigraph (asOpen (A.serialCompose B (Equiv.refl P)))) := by
  rintro ⟨s, ⟨u, hu⟩, ⟨v, hv⟩, hs⟩
  let l := s ∘ Sum.inl
  let r := s ∘ Sum.inr
  have he : Sum.elim l r = s := by funext w; cases w <;> rfl
  have hsum := cutSize_serial A B l r
  rw [he] at hsum
  obtain ⟨b, hb⟩ := constant_of_small _ hA l (by omega)
  obtain ⟨c, hc⟩ := constant_of_small _ hB r (by omega)
  have hbc : b = c := by
    by_contra hne
    have hseam : (∑ p, bit (l (A.rightVert p)) (r (B.leftVert p))) = Fintype.card P := by
      simp [hb, hc, bit, hne]
    rw [hseam] at hsum
    omega
  have hall (w : V ⊕ W) : s w = b := by
    rcases w with w | w
    · exact hb w
    · exact (hc w).trans hbc.symm
  have hfalse := (hall u).trans (hall v).symm
  simp only [hu, hv, Bool.true_eq_false] at hfalse

section ClosedContext

variable {W' J' R' : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype W'] [DecidableEq W'] [Fintype J'] [DecidableEq J']
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  [Fintype R'] [DecidableEq R'] [Nonempty W] [Nonempty W']

omit [Fintype P] in
/-- Arbitrary fixed exteriors, literal rotation-system sewing, and possibly
different interior carriers and port placements. -/
theorem replacement_structural (outside : OpenTangleData V I L)
    (old : OpenTangleData W J R) (new : OpenTangleData W' J' R')
    (mo : L ≃ R) (mn : L ≃ R')
    (ho : (sideMultigraph old).Connected ∧ (sideMultigraph old).Bridgeless)
    (hn : (sideMultigraph new).Connected ∧ (sideMultigraph new).Bridgeless) :
    ((rotationPrimalGraph (outside.composeRotationSystem old mo)).Connected ∧
      EdgeBridgeFree (outside.composeRotationSystem old mo)) ↔
    ((rotationPrimalGraph (outside.composeRotationSystem new mn)).Connected ∧
      EdgeBridgeFree (outside.composeRotationSystem new mn)) := by
  rw [OpenTangleSmallCutReplacement.composite_structural_iff,
    OpenTangleSmallCutReplacement.composite_structural_iff]
  exact replacement_of_internal (sideMultigraph outside) (sideMultigraph old)
    (sideMultigraph new) outside.boundaryVert
    (fun l => old.boundaryVert (mo l)) (fun l => new.boundaryVert (mn l)) ho hn

end ClosedContext
end
end Mettapedia.GraphTheory.FourColor.OpenTangleInternalReplacement
