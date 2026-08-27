import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoDefectParity

/-!
# Framed completability is the zero-flux sector

The framed boundary does not turn the two-defect constraint into a reachability
problem.  Write the boundary flux as the total colour exposed at the frozen
outward interface.  Two facts then settle completability outright.

*The flux is a conserved quantity.*  A legal framed move is a Kempe switch whose
component is disjoint from the frozen interface, so it fixes every frozen edge
colour.  Every frozen edge is incident to a frozen stub, so the flux -- a sum of
Kirchhoff sums over exactly those stubs -- is unchanged by any legal move, hence
along any reachable sequence.

*The flux is exactly the completion defect.*  Two-defect parity says the two
missing colours and the flux sum to zero, so over the Klein group the missing
colours agree precisely when the flux vanishes.

Together: a colouring is completable iff its flux is already zero, and when it
is, the empty move sequence completes it.  Internal Kempe dynamics can neither
create nor destroy the obstruction.

This is a retirement result, not a route.  It says the framed trail's accepting
condition is static, so a genuinely relative Kauffman theory needs a different
accepting object rather than the present frozen frame.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedCompletionStatic

open SimpleGraph
open scoped BigOperators
open GoertzelV24FramedTrail
open GoertzelV24TwoDefectParity

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- **One legal move conserves the boundary flux.**  Every frozen edge is
incident to a frozen stub, and a legal move fixes every frozen edge colour, so
each stub's Kirchhoff summand is unchanged. -/
theorem frozenInterfaceColorSum_eq_of_step
    (data : FramedTrailData G) (hdata : data.WellFormed)
    {C C' : G.EdgeColoring Color}
    (hstep : FramedTangleLegalKempeStep data C C') :
    frozenInterfaceColorSum data C' = frozenInterfaceColorSum data C := by
  unfold frozenInterfaceColorSum
  refine Finset.sum_congr rfl ?_
  intro vertex hvertex
  unfold vertexKirchhoffSum
  refine Finset.sum_congr rfl ?_
  intro edge hedge
  exact framedTangleLegalKempeStep_eq_on_frozenInterface hstep
    ((hdata.frozen_edge_iff_incident_stub edge).2 ⟨vertex, hvertex, hedge⟩)

/-- **The flux is conserved along any reachable sequence.** -/
theorem frozenInterfaceColorSum_eq_of_reachable
    (data : FramedTrailData G) (hdata : data.WellFormed)
    {C C' : G.EdgeColoring Color}
    (hreach : FramedTangleKempeReachable data C C') :
    frozenInterfaceColorSum data C' = frozenInterfaceColorSum data C := by
  induction hreach with
  | refl => rfl
  | tail _ hstep ih =>
      exact (frozenInterfaceColorSum_eq_of_step data hdata hstep).trans ih

/-- Matching defect colours force zero flux, by two-defect parity. -/
theorem frozenInterfaceColorSum_eq_zero_of_hasMatchingDefectColors
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C)
    (hmatch : data.HasMatchingDefectColors C) :
    frozenInterfaceColorSum data C = 0 := by
  have hsum := defectSum_add_frozenInterfaceColorSum_eq_zero data hdata C hC
  have hzero : data.missingColorAt C 0 + data.missingColorAt C 1 = 0 :=
    (add_eq_zero_iff_eq _ _).2 hmatch
  rw [hzero, zero_add] at hsum
  exact hsum

/-- **Framed completability is the zero-flux sector.**

Both directions are static.  Zero flux already gives matching defect colours, so
the empty move sequence completes; and any completing sequence conserves the
flux, so its terminal state's matching colours force the flux to have been zero
all along. -/
theorem framedTangleCompletable_iff_frozenInterfaceColorSum_eq_zero
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    FramedTangleCompletable data C ↔ frozenInterfaceColorSum data C = 0 := by
  constructor
  · rintro ⟨C', hreach, hmatch⟩
    have hCTait : IsTaitEdgeColoring G C' :=
      framedTangleKempeReachable_preserves_isTaitEdgeColoring hreach hC
    have hzero : frozenInterfaceColorSum data C' = 0 :=
      frozenInterfaceColorSum_eq_zero_of_hasMatchingDefectColors data hdata C' hCTait hmatch
    rw [frozenInterfaceColorSum_eq_of_reachable data hdata hreach] at hzero
    exact hzero
  · intro hflux
    exact ⟨C, Relation.ReflTransGen.refl,
      hasMatchingDefectColors_of_frozenInterfaceColorSum_eq_zero data hdata C hC hflux⟩

/-- The empty move sequence already completes a zero-flux state: no Kempe
dynamics is needed, and none can help otherwise. -/
theorem hasMatchingDefectColors_iff_frozenInterfaceColorSum_eq_zero
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    data.HasMatchingDefectColors C ↔ frozenInterfaceColorSum data C = 0 :=
  ⟨frozenInterfaceColorSum_eq_zero_of_hasMatchingDefectColors data hdata C hC,
    hasMatchingDefectColors_of_frozenInterfaceColorSum_eq_zero data hdata C hC⟩

/-- **Kempe dynamics is inert here.**  A framed trail is completable exactly
when it is already complete, so the moves never repair a nonzero-flux state. -/
theorem framedTangleCompletable_iff_hasMatchingDefectColors
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    FramedTangleCompletable data C ↔ data.HasMatchingDefectColors C :=
  (framedTangleCompletable_iff_frozenInterfaceColorSum_eq_zero data hdata C hC).trans
    (hasMatchingDefectColors_iff_frozenInterfaceColorSum_eq_zero data hdata C hC).symm

end

end GoertzelV24FramedCompletionStatic

end Mettapedia.GraphTheory.FourColor
