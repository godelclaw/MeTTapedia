import Mettapedia.GraphTheory.FourColor.MinimalCounterexampleRegime

namespace Mettapedia.GraphTheory.FourColor

variable {V W : Type*}

namespace SmallCyclicEdgeCut

/-- Promote a bundled small cyclic cut to the checker-facing separator
candidate language. -/
def toCyclicSeparatorCandidate
    {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G) :
    CyclicSeparatorCandidate G where
  edgeCut := cut.edgeCut
  side := cut.side
  hcard_le_four := cut.hcard_le_four
  hcut_crosses := by
    intro e he
    exact (cut.hcut_eq e).1 he
  hinside_cycle := cut.hinside_cycle
  houtside_cycle := cut.houtside_cycle

@[simp] theorem toCyclicSeparatorCandidate_edgeCut
    {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G) :
    cut.toCyclicSeparatorCandidate.edgeCut = cut.edgeCut :=
  rfl

/-- A bundled small cyclic cut realizes its promoted separator candidate. -/
theorem toCyclicSeparatorCandidate_realizes
    {G : SimpleGraph V} (cut : SmallCyclicEdgeCut G) :
    cut.toCyclicSeparatorCandidate.Realizes := by
  intro e
  exact cut.hcut_eq e

end SmallCyclicEdgeCut

/--
Foundation target for an actual peeled collar: every small cyclic edge cut
seen inside the peeled collar lifts to a small cyclic edge cut in the ambient
normal-form graph, with no larger edge support.

This is the topological/duality statement still needed from the planar
infrastructure.  The bridge below proves that this target is exactly strong
enough to inherit cyclic five-edge-connectivity from the ambient regime.
-/
def PeeledCollarSmallCyclicCutLiftsToAmbient
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∀ cut : SmallCyclicEdgeCut H,
    ∃ ambientCut : SmallCyclicEdgeCut G,
      ambientCut.edgeCut.card <= cut.edgeCut.card

/--
Candidate-facing version of the same foundation target.  This form matches
the existing finite separator APIs: once a collar-side candidate realizes an
exact side cut, the planar lift must produce an ambient small cyclic cut of no
larger size.
-/
def PeeledCollarRealizedCandidateLiftsToAmbientSmallCut
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∀ candidate : CyclicSeparatorCandidate H,
    candidate.Realizes →
      ∃ ambientCut : SmallCyclicEdgeCut G,
        ambientCut.edgeCut.card <= candidate.edgeCut.card

/-- The candidate-facing cut-lift target implies the bundled-cut target. -/
theorem peeledCollarSmallCyclicCutLiftsToAmbient_of_realizedCandidateLift
    {G : SimpleGraph V} {H : SimpleGraph W}
    (hlift : PeeledCollarRealizedCandidateLiftsToAmbientSmallCut G H) :
    PeeledCollarSmallCyclicCutLiftsToAmbient G H := by
  intro cut
  simpa using
    hlift cut.toCyclicSeparatorCandidate cut.toCyclicSeparatorCandidate_realizes

/-- The bundled-cut lift target implies the candidate-facing lift target. -/
theorem peeledCollarRealizedCandidateLiftsToAmbientSmallCut_of_smallCutLift
    {G : SimpleGraph V} {H : SimpleGraph W}
    (hlift : PeeledCollarSmallCyclicCutLiftsToAmbient G H) :
    PeeledCollarRealizedCandidateLiftsToAmbientSmallCut G H := by
  intro candidate hrealizes
  let cut : SmallCyclicEdgeCut H :=
    (candidate.toCyclicEdgeCutRealization hrealizes).toSmallCyclicEdgeCut
      candidate.hcard_le_four
  rcases hlift cut with ⟨ambientCut, hcard⟩
  exact ⟨ambientCut, by simpa [cut] using hcard⟩

/--
Bundled-cut lifting and realized-candidate lifting are equivalent graph-facing
foundation targets.
-/
theorem peeledCollarRealizedCandidateLiftsToAmbientSmallCut_iff_smallCutLift
    {G : SimpleGraph V} {H : SimpleGraph W} :
    PeeledCollarRealizedCandidateLiftsToAmbientSmallCut G H ↔
      PeeledCollarSmallCyclicCutLiftsToAmbient G H :=
  ⟨peeledCollarSmallCyclicCutLiftsToAmbient_of_realizedCandidateLift,
    peeledCollarRealizedCandidateLiftsToAmbientSmallCut_of_smallCutLift⟩

/--
If the ambient graph has no small cyclic edge cut and every small collar cut
lifts to the ambient graph without increasing size, then the peeled collar has
no cyclic edge cut of size at most four.
-/
theorem noCyclicEdgeCutOfSizeAtMostFour_of_ambient_noSmallCuts_of_peeledCollarSmallCutLift
    {G : SimpleGraph V} {H : SimpleGraph W}
    (hambient : NoCyclicEdgeCutOfSizeAtMostFour G)
    (hlift : PeeledCollarSmallCyclicCutLiftsToAmbient G H) :
    NoCyclicEdgeCutOfSizeAtMostFour H := by
  intro hcut
  rcases hcut with ⟨cut, hcard⟩
  rcases hlift cut with ⟨ambientCut, hle⟩
  exact hambient ⟨ambientCut, le_trans hle hcard⟩

/--
Load-bearing bridge in graph form: ambient no-small-cyclic-cuts plus the
peeled-collar cut-lift target proves that the peeled collar is cyclically
five-edge-connected.
-/
theorem cyclicallyFiveEdgeConnected_of_ambient_noSmallCuts_of_peeledCollarSmallCutLift
    {G : SimpleGraph V} {H : SimpleGraph W}
    (hambient : NoCyclicEdgeCutOfSizeAtMostFour G)
    (hlift : PeeledCollarSmallCyclicCutLiftsToAmbient G H) :
    CyclicallyFiveEdgeConnected H :=
  (noCyclicEdgeCutOfSizeAtMostFour_of_ambient_noSmallCuts_of_peeledCollarSmallCutLift
    hambient hlift).cyclicallyFiveEdgeConnected

/--
Regime-facing bridge: the ambient minimal-counterexample/CAP5-free normal form
supplies the ambient no-small-cut obstruction; the named cut-lift foundation
target supplies the inheritance step for the selected peeled collar.
-/
theorem peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_smallCutLift
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (hlift : PeeledCollarSmallCyclicCutLiftsToAmbient G H) :
    CyclicallyFiveEdgeConnected H :=
  cyclicallyFiveEdgeConnected_of_ambient_noSmallCuts_of_peeledCollarSmallCutLift
    regime.ambient.noSmallCyclicEdgeCuts hlift

/--
Same bridge using the checker-facing realized-candidate lift form, which is
usually what a rotation-system/Jordan argument produces first.
-/
theorem peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_realizedCandidateLift
    [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (hlift : PeeledCollarRealizedCandidateLiftsToAmbientSmallCut G H) :
    CyclicallyFiveEdgeConnected H :=
  peeledCollar_cyclicallyFiveEdgeConnected_of_minimalCounterexampleRegime_of_smallCutLift
    regime
    (peeledCollarSmallCyclicCutLiftsToAmbient_of_realizedCandidateLift hlift)

end Mettapedia.GraphTheory.FourColor
