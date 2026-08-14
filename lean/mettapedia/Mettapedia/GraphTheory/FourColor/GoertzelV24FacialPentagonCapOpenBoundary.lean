import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCap
import Mettapedia.GraphTheory.FourColor.GoertzelV24PentagonCapOpeningComparison
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationCutDartDecomposition

/-!
# The literal open boundary of a facial pentagon cap

Opening the manuscript-side cap deletes its five vertices and replaces every
edge from the retained graph into that cap by a degree-one stub.  This module
identifies those exposed darts on the *rotation-system* carrier: they are
exactly the five outward spokes, in their source order.  It is the graph-to-
rotation part of C-2.

This does not yet prove that the two sides of those five stub edges lie on one
opened facial orbit.  That is the remaining collar-orbit calculation; merely
knowing the boundary carrier must not be mistaken for that calculation.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapOpenBoundary

open SimpleGraphDartRotation
open GoertzelV24FacialPentagonCap
open GoertzelV24DeletedRegionSlitGraph
open GoertzelV24PentagonCapOpening
open GoertzelV24RotationCutDartDecomposition

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

namespace PentagonCap

/-- The retained side of the literal manuscript opening of one cap. -/
abbrev keep (cap : PentagonCap G) : V → Prop :=
  fun vertex => vertex ∉ cap.vertexSupport

/-- The source's outward orientation of a cap spoke is an exposed dart of the
literal retained open region. -/
def openBoundaryDart (data : Data G) (cap : PentagonCap G) (step : Fin 5) :
    BoundaryDart data.toRotationSystem (keep cap) where
  val := ⟨GoertzelV24PentagonCapOpeningComparison.PentagonCap.spokeBoundaryDart cap step, by
    change (GoertzelV24PentagonCapOpeningComparison.PentagonCap.spokeBoundaryDart cap step).fst ∉ cap.vertexSupport
    simpa using cap.spokeOuter_not_mem_vertexSupport step⟩
  property := by
    change ¬ (data.toRotationSystem.alpha
      (GoertzelV24PentagonCapOpeningComparison.PentagonCap.spokeBoundaryDart cap step)).fst ∉
      cap.vertexSupport
    rw [SimpleGraphDartRotation.Data.toRotationSystem_alpha]
    simpa using (cap.mem_vertexSupport_iff _).mpr ⟨step, rfl⟩

@[simp]
theorem openBoundaryDart_val (data : Data G) (cap : PentagonCap G)
    (step : Fin 5) :
    (openBoundaryDart data cap step).1.1 =
      GoertzelV24PentagonCapOpeningComparison.PentagonCap.spokeBoundaryDart cap step :=
  rfl

/-- The five ordered cap spokes remain distinct when regarded as exposed darts
of the literal open rotation. -/
theorem openBoundaryDart_injective (data : Data G) (cap : PentagonCap G) :
    Function.Injective (openBoundaryDart data cap) := by
  intro first second heq
  apply cap.vertex.injective
  have hdarts := congrArg
    (fun dart : BoundaryDart data.toRotationSystem (keep cap) => dart.1.1.snd)
    heq
  simpa [openBoundaryDart,
    GoertzelV24PentagonCapOpeningComparison.PentagonCap.spokeBoundaryDart] using hdarts

/-- No extra exposed dart is created by opening a pentagon cap: every literal
open-boundary dart is one of the five source-ordered spokes. -/
theorem exists_openBoundaryDart_eq (data : Data G) (cap : PentagonCap G)
    (boundary : BoundaryDart data.toRotationSystem (keep cap)) :
    ∃ step : Fin 5, boundary = openBoundaryDart data cap step := by
  let port : DeletedRegionBoundaryPort G cap.vertexSupport :=
    { dart := boundary.1.1
      retained := boundary.1.2
      removed := by
        by_contra hnot
        apply boundary.2
        change (data.toRotationSystem.alpha boundary.1.1).fst ∉
          cap.vertexSupport
        rw [SimpleGraphDartRotation.Data.toRotationSystem_alpha]
        simpa using hnot }
  obtain ⟨step, hport⟩ :=
    GoertzelV24PentagonCapOpeningComparison.PentagonCap.boundaryPort_eq_spokeBoundaryPort cap port
  refine ⟨step, ?_⟩
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg DeletedRegionBoundaryPort.dart hport

/-- The source's five cap positions enumerate the entire exposed boundary of
the literal open rotation.  This is an exact finite carrier result, not a
hole-orbit assertion. -/
def openBoundaryDartEquiv (data : Data G) (cap : PentagonCap G) :
    Fin 5 ≃ BoundaryDart data.toRotationSystem (keep cap) :=
  Equiv.ofBijective (openBoundaryDart data cap)
    ⟨openBoundaryDart_injective data cap, by
      intro boundary
      obtain ⟨step, hstep⟩ := exists_openBoundaryDart_eq data cap boundary
      exact ⟨step, hstep.symm⟩⟩

end PentagonCap

end

end GoertzelV24FacialPentagonCapOpenBoundary

end Mettapedia.GraphTheory.FourColor
