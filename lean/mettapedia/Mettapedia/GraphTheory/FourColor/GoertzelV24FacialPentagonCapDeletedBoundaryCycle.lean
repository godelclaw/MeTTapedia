import Mettapedia.GraphTheory.FourColor.GoertzelV24FacialPentagonCapOpenBoundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24DeletedRegionBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24LocalFaceCutCycleTurn

/-!
# Deleted-side boundary order of a facial pentagon cap

This is the cap-side half of C-2.  The five outward spokes have an exact
literal enumeration on the retained side.  Reversing that enumeration gives
the corresponding deleted-side boundary darts, on which the capped deleted
face permutation can be calculated from the oriented facial pentagon walk.

There are now two consumers of this calculation.  The closed-map laboratory
transfers the cycle with its planar-bond hypotheses.  Addendum V's frontier
carrier instead uses the exact local cut-face occurrence condition proved in
`GoertzelV24FrontierPentagonCapInnerFace`; neither consumer requires the cap
calculation itself to assume global cubicity. -/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCapDeletedBoundaryCycle

open SimpleGraphDartRotation
open GoertzelV24DeletedRegionBoundaryOrder
open GoertzelV24PentagonCapOpening
open GoertzelV24FacialPentagonCap
open GoertzelV24FacialPentagonCapOpenBoundary
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24FaceDualConnectedness

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-! The two retained-vertex splice towers use extensionally identical subtype
carriers but intentionally distinct instance names.  This cap-side calculation
uses the ordinary subtype instances carried by the literal boundary data. -/
attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype

/-- The collar calculation uses cubicity only at the five cap vertices.
Keeping that locality explicit lets the same proof run on Addendum V's
frontier tangle, whose pre-existing outer stubs make global cubicity false. -/
def CapVerticesCubic
    {data : SimpleGraphDartRotation.Data G}
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data) :
    Prop :=
  ∀ step : Fin 5,
    (data.toRotationSystem.dartsAt
      (walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertex
        step)).card = 3

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

/-- The reversed boundary dart is based at the named cap vertex. -/
@[simp] theorem capDeletedBoundaryDart_fst (data : SimpleGraphDartRotation.Data G)
    (cap : GoertzelV24PentagonCapOpening.PentagonCap G)
    (step : Fin 5) :
    (capDeletedBoundaryDart data cap step).1.1.fst = cap.vertex step := by
  simp [capDeletedBoundaryDart, PentagonCap.openBoundaryDart,
    SimpleGraphDartRotation.Data.toRotationSystem_alpha,
    GoertzelV24PentagonCapOpeningComparison.PentagonCap.spokeBoundaryDart]

/-- The other endpoint of the reversed cap-side dart is its named retained
spoke endpoint. -/
@[simp] theorem capDeletedBoundaryDart_snd (data : SimpleGraphDartRotation.Data G)
    (cap : GoertzelV24PentagonCapOpening.PentagonCap G)
    (step : Fin 5) :
    (capDeletedBoundaryDart data cap step).1.1.snd = cap.spokeOuter step := by
  simp [capDeletedBoundaryDart, PentagonCap.openBoundaryDart,
    SimpleGraphDartRotation.Data.toRotationSystem_alpha,
    GoertzelV24PentagonCapOpeningComparison.PentagonCap.spokeBoundaryDart]

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

namespace FacialPentagonCapBoundaryWalk

variable {data : SimpleGraphDartRotation.Data G}

/-- The recorded facial boundary walk really uses the consecutive named cap
vertices as the endpoints of each of its five darts. -/
theorem boundaryDart_edge_eq_vertices
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (step : Fin 5) :
    (walk.boundaryDart step).edge =
      s(walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertex step,
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertex
          (step + 1)) := by
  have hedge := congrArg Subtype.val (walk.boundaryDart_edge step)
  simpa [SimpleGraphDartRotation.Data.toRotationSystem_edgeOf,
    walk.toOrientedFacialPentagonCap.cycleEdge_eq_vertices step] using hedge

/-- Consecutive entries in the literal facial walk meet at the actual terminal
vertex of the preceding dart. -/
theorem boundaryDart_snd_eq_next_fst
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (step : Fin 5) :
    (walk.boundaryDart step).snd = (walk.boundaryDart (step + 1)).fst := by
  have hphi := congrArg (fun dart : G.Dart => dart.fst)
    (walk.boundaryDart_phi step)
  simpa [RotationSystem.phi_apply,
    SimpleGraphDartRotation.Data.toRotationSystem_rho,
    SimpleGraphDartRotation.Data.toRotationSystem_alpha,
    data.vertexRotation_fst] using hphi

/-- The face-successor equations rule out the reversed orientation at every
cap edge: a reversed dart would force one cap vertex to equal either its
successor or its next-successor. -/
theorem boundaryDart_fst_eq_vertex
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (step : Fin 5) :
    (walk.boundaryDart step).fst =
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertex step := by
  have hedge := boundaryDart_edge_eq_vertices walk step
  rw [SimpleGraph.dart_edge_eq_mk'_iff'] at hedge
  rcases hedge with hforward | hreverse
  · exact hforward.1
  · have hnext := boundaryDart_snd_eq_next_fst walk step
    have hedgeNext := boundaryDart_edge_eq_vertices walk (step + 1)
    rw [SimpleGraph.dart_edge_eq_mk'_iff'] at hedgeNext
    have hstep_ne_next : step ≠ step + 1 := by
      fin_cases step <;> decide
    have hstep_ne_nextNext : step ≠ (step + 1) + 1 := by
      fin_cases step <;> decide
    rcases hedgeNext with hnextForward | hnextReverse
    · exfalso
      apply hstep_ne_next
      apply walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertex.injective
      calc
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertex step =
            (walk.boundaryDart step).snd := hreverse.2.symm
        _ = (walk.boundaryDart (step + 1)).fst := hnext
        _ = walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertex
            (step + 1) := hnextForward.1
    · exfalso
      apply hstep_ne_nextNext
      apply walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertex.injective
      calc
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertex step =
            (walk.boundaryDart step).snd := hreverse.2.symm
        _ = (walk.boundaryDart (step + 1)).fst := hnext
        _ = walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertex
            ((step + 1) + 1) := hnextReverse.1

/-- The target vertex of each facial boundary dart is the next named cap
vertex. -/
theorem boundaryDart_snd_eq_next_vertex
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (step : Fin 5) :
    (walk.boundaryDart step).snd =
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertex
        (step + 1) := by
  rw [boundaryDart_snd_eq_next_fst, boundaryDart_fst_eq_vertex]

end FacialPentagonCapBoundaryWalk

variable {data : SimpleGraphDartRotation.Data G}

/-- Predecessor followed by successor is the identity on the five cap
positions.  Keeping this finite arithmetic explicit makes the subsequent
rotation calculation insensitive to the wraparound position. -/
private theorem fin5_sub_one_add_one (step : Fin 5) :
    (step - 1) + 1 = step := by
  fin_cases step <;> rfl

/-- The closed facial walk supplies the first of the three local rotations at
each cap vertex. -/
theorem boundaryDart_rho_alpha_pred_eq
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (step : Fin 5) :
    data.toRotationSystem.rho
        (data.toRotationSystem.alpha (walk.boundaryDart (step - 1))) =
      walk.boundaryDart step := by
  have hphi := walk.boundaryDart_phi (step - 1)
  rw [RotationSystem.phi_apply] at hphi
  simpa only [fin5_sub_one_add_one] using hphi

/-- The reversed cap-side boundary dart still lies over the named spoke edge. -/
theorem capDeletedBoundaryDart_edge_eq_spokeEdge
    (data : SimpleGraphDartRotation.Data G)
    (cap : GoertzelV24PentagonCapOpening.PentagonCap G)
    (step : Fin 5) :
    data.toRotationSystem.edgeOf (capDeletedBoundaryDart data cap step).1.1 =
      cap.spokeEdge step := by
  apply Subtype.ext
  rw [capDeletedBoundaryDart_val, data.toRotationSystem.edge_alpha]
  change (PentagonCap.openBoundaryDart data cap step).1.1.edge =
    (cap.spokeEdge step).1
  simp [PentagonCap.openBoundaryDart,
    GoertzelV24PentagonCapOpeningComparison.PentagonCap.spokeBoundaryDart,
    cap.spokeEdge_eq, Sym2.eq_swap]

/-- The cap-internal dart reached immediately after a named exposed spoke on
the capped deleted side.  It is the inward orientation of the preceding cap
edge in the literal facial walk. -/
def capInternalFaceDart
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (step : Fin 5) :
    DeletedBasedDart data.toRotationSystem
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport where
  val := data.toRotationSystem.alpha (walk.boundaryDart (step - 1))
  property := by
    change (walk.boundaryDart (step - 1)).snd ∈
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport
    rw [FacialPentagonCapBoundaryWalk.boundaryDart_snd_eq_next_vertex,
      fin5_sub_one_add_one]
    exact (walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.mem_vertexSupport_iff _).mpr
      ⟨step, rfl⟩

@[simp] theorem capInternalFaceDart_val
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (step : Fin 5) :
    (capInternalFaceDart walk step).1 =
      data.toRotationSystem.alpha (walk.boundaryDart (step - 1)) :=
  rfl

/-- The next ambient alpha step of this cap-internal dart remains in the cap,
so it is not an exposed deleted boundary dart. -/
theorem capInternalFaceDart_alpha_mem_vertexSupport
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (step : Fin 5) :
    data.toRotationSystem.vertOf
        (data.toRotationSystem.alpha (capInternalFaceDart walk step).1) ∈
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport := by
  change (walk.boundaryDart (step - 1)).fst ∈
    walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport
  rw [FacialPentagonCapBoundaryWalk.boundaryDart_fst_eq_vertex]
  exact (walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.mem_vertexSupport_iff _).mpr
    ⟨step - 1, rfl⟩

/-- At a facial cap, the local cubic rotation takes the outgoing cap spoke
to the incoming dart of the preceding cap edge.  This is the non-picture
local turn required for the deleted-side collar calculation. -/
theorem rho_capDeletedBoundaryDart_eq_alpha_boundaryPred
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (hcubic : CapVerticesCubic walk)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (step : Fin 5) :
    data.toRotationSystem.rho
        (capDeletedBoundaryDart data
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap step).1.1 =
      data.toRotationSystem.alpha (walk.boundaryDart (step - 1)) := by
  let RS := data.toRotationSystem
  let cap := walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
  have hpredSucc : (step - 1) + 1 = step := fin5_sub_one_add_one step
  have hfirstBase : RS.vertOf (RS.alpha (walk.boundaryDart (step - 1))) =
      cap.vertex step := by
    change (walk.boundaryDart (step - 1)).snd = cap.vertex step
    rw [FacialPentagonCapBoundaryWalk.boundaryDart_snd_eq_next_vertex,
      hpredSucc]
  have hsecondBase : RS.vertOf (walk.boundaryDart step) = cap.vertex step := by
    change (walk.boundaryDart step).fst = cap.vertex step
    exact FacialPentagonCapBoundaryWalk.boundaryDart_fst_eq_vertex walk step
  have hthirdBase : RS.vertOf (capDeletedBoundaryDart data cap step).1.1 =
      cap.vertex step := by
    change (capDeletedBoundaryDart data cap step).1.1.fst = cap.vertex step
    exact capDeletedBoundaryDart_fst data cap step
  have hfirstSecond : RS.alpha (walk.boundaryDart (step - 1)) ≠
      walk.boundaryDart step := by
    intro heq
    have hsnd := congrArg (fun dart : G.Dart => dart.snd) heq
    dsimp [RS] at hsnd
    have hne : step - 1 ≠ step + 1 := by
      fin_cases step <;> decide
    apply hne
    apply cap.vertex.injective
    simpa [SimpleGraphDartRotation.Data.toRotationSystem_alpha,
      FacialPentagonCapBoundaryWalk.boundaryDart_fst_eq_vertex,
      FacialPentagonCapBoundaryWalk.boundaryDart_snd_eq_next_vertex] using hsnd
  have hfirstThird : RS.alpha (walk.boundaryDart (step - 1)) ≠
      (capDeletedBoundaryDart data cap step).1.1 := by
    intro heq
    have hsnd := congrArg (fun dart : G.Dart => dart.snd) heq
    dsimp [RS] at hsnd
    apply cap.spokeOuter_not_mem_vertexSupport step
    apply (cap.mem_vertexSupport_iff _).mpr
    refine ⟨step - 1, ?_⟩
    simpa [SimpleGraphDartRotation.Data.toRotationSystem_alpha,
      FacialPentagonCapBoundaryWalk.boundaryDart_fst_eq_vertex] using hsnd
  have hsecondThird : walk.boundaryDart step ≠
      (capDeletedBoundaryDart data cap step).1.1 := by
    intro heq
    have hsnd := congrArg (fun dart : G.Dart => dart.snd) heq
    apply cap.spokeOuter_not_mem_vertexSupport step
    apply (cap.mem_vertexSupport_iff _).mpr
    refine ⟨step + 1, ?_⟩
    simpa [FacialPentagonCapBoundaryWalk.boundaryDart_snd_eq_next_vertex] using hsnd
  have hfirst : RS.rho (RS.alpha (walk.boundaryDart (step - 1))) =
      walk.boundaryDart step := by
    exact boundaryDart_rho_alpha_pred_eq walk step
  have hcycle := RotationSystem.rho_three_cycle_of_eq_second_of_card_dartsAt_eq_three
    RS hrotation
    (first := RS.alpha (walk.boundaryDart (step - 1)))
    (second := walk.boundaryDart step)
    (third := (capDeletedBoundaryDart data cap step).1.1)
    (by simpa only [hfirstBase] using hcubic step)
    (hsecondBase.trans hfirstBase.symm) (hthirdBase.trans hfirstBase.symm)
    hfirstSecond hfirstThird hsecondThird hfirst
  exact hcycle.2

/-- The other forced local cubic turn carries the current cap edge into its
outgoing spoke. -/
theorem rho_boundaryDart_eq_capDeletedBoundaryDart
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (hcubic : CapVerticesCubic walk)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (step : Fin 5) :
    data.toRotationSystem.rho (walk.boundaryDart step) =
      (capDeletedBoundaryDart data
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap step).1.1 := by
  let RS := data.toRotationSystem
  let cap := walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
  let first := RS.alpha (walk.boundaryDart (step - 1))
  let third := (capDeletedBoundaryDart data cap step).1.1
  have hpredSucc : (step - 1) + 1 = step := fin5_sub_one_add_one step
  have hfirstBase : RS.vertOf first = cap.vertex step := by
    change (walk.boundaryDart (step - 1)).snd = cap.vertex step
    rw [FacialPentagonCapBoundaryWalk.boundaryDart_snd_eq_next_vertex,
      hpredSucc]
  have hfirst : RS.rho first = walk.boundaryDart step := by
    exact boundaryDart_rho_alpha_pred_eq walk step
  have hthird : RS.rho third = first := by
    exact rho_capDeletedBoundaryDart_eq_alpha_boundaryPred
      walk hcubic hrotation step
  have hcard : (RS.dartsAt (RS.vertOf first)).card = 3 := by
    simpa only [hfirstBase] using hcubic step
  have hcube := rho_cube_apply_of_dartsAt_card_eq_three
    RS hrotation first hcard
  rw [hfirst] at hcube
  apply RS.rho.injective
  calc
    RS.rho (RS.rho (walk.boundaryDart step)) = first := hcube
    _ = RS.rho third := hthird.symm

/-- The capped deleted-side face permutation takes a named exposed spoke to
the preceding internal cap dart. -/
theorem deletedFacePerm_capDeletedBoundaryDart_eq_internal
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (hcubic : CapVerticesCubic walk)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (step : Fin 5) :
    deletedFacePerm data.toRotationSystem
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport
        (capDeletedBoundaryDart data
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap step).1 =
      capInternalFaceDart walk step := by
  let cap := walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
  apply Subtype.ext
  rw [deletedFacePerm, Equiv.Perm.mul_apply, deletedRho_val,
    deletedAlpha_apply_boundary data.toRotationSystem cap.vertexSupport
      (capDeletedBoundaryDart data cap step).1
      (capDeletedBoundaryDart data cap step).2]
  exact rho_capDeletedBoundaryDart_eq_alpha_boundaryPred walk hcubic hrotation step

/-- The following capped deleted-side face step exits the internal cap edge
through the preceding named spoke. -/
theorem deletedFacePerm_capInternalFaceDart_eq_previousBoundary
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (hcubic : CapVerticesCubic walk)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (step : Fin 5) :
    deletedFacePerm data.toRotationSystem
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport
        (capInternalFaceDart walk step) =
      (capDeletedBoundaryDart data
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap (step - 1)).1 := by
  let cap := walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap
  apply Subtype.ext
  rw [deletedFacePerm, Equiv.Perm.mul_apply, deletedRho_val,
    deletedAlpha_apply_internal data.toRotationSystem cap.vertexSupport
      (capInternalFaceDart walk step)
      (capInternalFaceDart_alpha_mem_vertexSupport walk step),
    capInternalFaceDart_val, data.toRotationSystem.alpha_involutive]
  exact rho_boundaryDart_eq_capDeletedBoundaryDart walk hcubic hrotation (step - 1)

/-- Two capped deleted-side face steps advance once around the five cap spokes
(in the reverse source direction). -/
theorem deletedFacePerm_sq_capDeletedBoundaryDart_eq_previous
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (hcubic : CapVerticesCubic walk)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (step : Fin 5) :
    (deletedFacePerm data.toRotationSystem
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport ^ 2)
        (capDeletedBoundaryDart data
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap step).1 =
      (capDeletedBoundaryDart data
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap (step - 1)).1 := by
  rw [pow_two, Equiv.Perm.mul_apply,
    deletedFacePerm_capDeletedBoundaryDart_eq_internal walk hcubic hrotation step,
    deletedFacePerm_capInternalFaceDart_eq_previousBoundary walk hcubic hrotation step]

/-- One two-step cap advance is a genuine same-cycle relation on the capped
deleted-side face permutation. -/
theorem capDeletedBoundaryDart_sameCycle_previous
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (hcubic : CapVerticesCubic walk)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (step : Fin 5) :
    (deletedFacePerm data.toRotationSystem
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport).SameCycle
        (capDeletedBoundaryDart data
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap step).1
        (capDeletedBoundaryDart data
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap (step - 1)).1 := by
  let f := deletedFacePerm data.toRotationSystem
    walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport
  have hsq := deletedFacePerm_sq_capDeletedBoundaryDart_eq_previous
    walk hcubic hrotation step
  change (f ^ 2) _ = _ at hsq
  have hp : (f ^ 2).SameCycle
      ((f ^ 2) (capDeletedBoundaryDart data
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap step).1)
      (capDeletedBoundaryDart data
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap (step - 1)).1 :=
    hsq.sameCycle (f ^ 2)
  have hpf : f.SameCycle
      ((f ^ 2) (capDeletedBoundaryDart data
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap step).1)
      (capDeletedBoundaryDart data
        walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap (step - 1)).1 :=
    Equiv.Perm.SameCycle.of_pow hp
  exact Equiv.Perm.sameCycle_pow_left.mp hpf

/-- Starting from cap position zero, every named deleted-side boundary dart
lies in the same capped face cycle.  The proof is the literal five-position
calculation, not a cardinality argument. -/
theorem capDeletedBoundaryDart_zero_sameCycle
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (hcubic : CapVerticesCubic walk)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (step : Fin 5) :
    (deletedFacePerm data.toRotationSystem
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport).SameCycle
        (capDeletedBoundaryDart data
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap 0).1
        (capDeletedBoundaryDart data
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap step).1 := by
  let previous := capDeletedBoundaryDart_sameCycle_previous walk hcubic hrotation
  fin_cases step
  · exact Equiv.Perm.SameCycle.rfl
  · exact (previous 1).symm
  · exact (previous 0).trans ((previous 4).trans (previous 3))
  · exact (previous 0).trans (previous 4)
  · exact previous 0

/-- All five named cap-side boundary darts are one actual cycle of the capped
deleted face permutation. -/
theorem capDeletedBoundaryDart_sameCycle
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (hcubic : CapVerticesCubic walk)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (first second : Fin 5) :
    (deletedFacePerm data.toRotationSystem
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport).SameCycle
        (capDeletedBoundaryDart data
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap first).1
        (capDeletedBoundaryDart data
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap second).1 := by
  exact (capDeletedBoundaryDart_zero_sameCycle walk hcubic hrotation first).symm.trans
    (capDeletedBoundaryDart_zero_sameCycle walk hcubic hrotation second)

/-- The computed first-return order on the retained boundary sees all five
named cap spokes in one cycle when read from the complementary capped side.
This is the finite cap-side input to the planar-bond transfer; it does not
yet assert the connected retained-side hypothesis required for that transfer. -/
theorem deletedRegionBoundarySuccessor_openBoundary_sameCycle
    (walk : GoertzelV24FacialPentagonCap.FacialPentagonCapBoundaryWalk data)
    (hcubic : CapVerticesCubic walk)
    (hrotation : VertexRotationCyclic data.toRotationSystem)
    (first second : Fin 5) :
    (deletedRegionBoundarySuccessor data.toRotationSystem
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.vertexSupport).SameCycle
        (PentagonCap.openBoundaryDart data
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap first)
        (PentagonCap.openBoundaryDart data
          walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap second) := by
  rw [← deletedBoundaryHalfDartEquiv_capDeletedBoundaryDart data
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap first,
    ← deletedBoundaryHalfDartEquiv_capDeletedBoundaryDart data
      walk.toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap second,
    deletedRegionBoundarySuccessor_sameCycle_iff]
  exact capDeletedBoundaryDart_sameCycle walk hcubic hrotation first second

end

end GoertzelV24FacialPentagonCapDeletedBoundaryCycle

end Mettapedia.GraphTheory.FourColor
