import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapOpenBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionBoundaryOrder

/-!
# Deleted-side boundary order of a facial pentagon cap

This is the cap-side half of C-2.  The five outward spokes have an exact
literal enumeration on the retained side.  Reversing that enumeration gives
the corresponding deleted-side boundary darts, on which the capped deleted
face permutation can be calculated from the oriented facial pentagon walk.

The later theorem which transfers this cycle to the retained-side first-return
permutation still needs the planar-bond hypotheses, notably connectedness of
the retained side. -/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapDeletedBoundaryCycle

open SimpleGraphDartRotation
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24PentagonCapOpening
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapOpenBoundary
open GoertzelV24RotationCutDartDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-! The two retained-vertex splice towers use extensionally identical subtype
carriers but intentionally distinct instance names.  This cap-side calculation
uses the ordinary subtype instances carried by the literal boundary data. -/
attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24RetainedVertexRotationSplice.retainedVertexDecidableEq

/-- The deleted-side orientation of a named cap spoke. -/
def capDeletedBoundaryDart (data : SimpleGraphDartRotation.Data G)
    (cap : GoertzelV24PentagonCapOpening.PentagonCap G)
    (step : Fin 5) :
    DeletedBoundaryHalfDart data.toRotationSystem cap.vertexSupport where
  val :=
    ⟨data.toRotationSystem.alpha
        (PentagonCap.openBoundaryDart data cap step).1.1, by
      change (data.toRotationSystem.alpha
        (PentagonCap.openBoundaryDart data cap step).1.1).fst ∈ cap.vertexSupport
      by_contra hnot
      exact (PentagonCap.openBoundaryDart data cap step).2 hnot⟩
  property := by
    change (data.toRotationSystem.alpha
      (data.toRotationSystem.alpha
        (PentagonCap.openBoundaryDart data cap step).1.1)).fst ∉ cap.vertexSupport
    rw [data.toRotationSystem.alpha_involutive]
    exact (PentagonCap.openBoundaryDart data cap step).1.2

/-- Reversing the retained-facing cap spoke yields its cap-based dart. -/
@[simp] theorem capDeletedBoundaryDart_val (data : SimpleGraphDartRotation.Data G)
    (cap : GoertzelV24PentagonCapOpening.PentagonCap G)
    (step : Fin 5) :
    (capDeletedBoundaryDart data cap step).1.1 =
      data.toRotationSystem.alpha
        (PentagonCap.openBoundaryDart data cap step).1.1 :=
  rfl

/-- Reversing a named deleted-side cap spoke recovers precisely the named
retained-side open-boundary dart. -/
theorem deletedBoundaryHalfDartEquiv_capDeletedBoundaryDart
    (data : SimpleGraphDartRotation.Data G)
    (cap : GoertzelV24PentagonCapOpening.PentagonCap G)
    (step : Fin 5) :
    deletedBoundaryHalfDartEquivBoundaryDart data.toRotationSystem
        cap.vertexSupport (capDeletedBoundaryDart data cap step) =
      PentagonCap.openBoundaryDart data cap step := by
  apply Subtype.ext
  apply Subtype.ext
  exact data.toRotationSystem.alpha_involutive _

/-- The five source positions are injective also on the cap side of the
literal opening. -/
theorem capDeletedBoundaryDart_injective
    (data : SimpleGraphDartRotation.Data G)
    (cap : GoertzelV24PentagonCapOpening.PentagonCap G) :
    Function.Injective (capDeletedBoundaryDart data cap) := by
  intro first second heq
  apply PentagonCap.openBoundaryDart_injective data cap
  rw [← deletedBoundaryHalfDartEquiv_capDeletedBoundaryDart data cap first,
    ← deletedBoundaryHalfDartEquiv_capDeletedBoundaryDart data cap second, heq]

/-- No unrecorded deleted-side half-dart occurs around a facial pentagon cap:
the five ordered cap positions enumerate the whole capped boundary carrier. -/
theorem exists_capDeletedBoundaryDart_eq
    (data : SimpleGraphDartRotation.Data G)
    (cap : GoertzelV24PentagonCapOpening.PentagonCap G)
    (boundary : DeletedBoundaryHalfDart data.toRotationSystem cap.vertexSupport) :
    ∃ step : Fin 5, boundary = capDeletedBoundaryDart data cap step := by
  obtain ⟨step, hstep⟩ := PentagonCap.exists_openBoundaryDart_eq data cap
    (deletedBoundaryHalfDartEquivBoundaryDart data.toRotationSystem
      cap.vertexSupport boundary)
  refine ⟨step, ?_⟩
  apply (deletedBoundaryHalfDartEquivBoundaryDart data.toRotationSystem
    cap.vertexSupport).injective
  rw [hstep, deletedBoundaryHalfDartEquiv_capDeletedBoundaryDart]

/-- The exact finite cap-side boundary carrier, in its source order. -/
def capDeletedBoundaryDartEquiv (data : SimpleGraphDartRotation.Data G)
    (cap : GoertzelV24PentagonCapOpening.PentagonCap G) :
    Fin 5 ≃ DeletedBoundaryHalfDart data.toRotationSystem cap.vertexSupport :=
  Equiv.ofBijective (capDeletedBoundaryDart data cap)
    ⟨capDeletedBoundaryDart_injective data cap, by
      intro boundary
      obtain ⟨step, hstep⟩ := exists_capDeletedBoundaryDart_eq data cap boundary
      exact ⟨step, hstep.symm⟩⟩

end

end GoertzelV24FacialPentagonCapDeletedBoundaryCycle

end Mettapedia.GraphTheory.FourColor
