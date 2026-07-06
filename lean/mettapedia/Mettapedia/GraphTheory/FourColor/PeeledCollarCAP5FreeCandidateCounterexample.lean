import Mettapedia.GraphTheory.FourColor.PeeledCollarCAP5FreeSmallCutLiftFoundation

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

/-!
Checker-facing counterexamples for CAP5-free peeled-collar separator
candidates.

Once a realized-candidate lift theorem is available, the ambient
minimal-counterexample normal form rules out every realized small separator
candidate in the peeled collar.  Equivalently, every such candidate must emit
the standard finite-checker counterexample: an unlisted side-crossing edge and
the one-edge walk across it.
-/

variable {V W : Type} [DecidableEq V] [DecidableEq W]

namespace CyclicSeparatorCandidate

/--
Ambient no-small-cyclic-cuts plus realized-candidate lift forbids exact
realization of any collar-side separator candidate.
-/
theorem not_realizes_of_minimalCounterexampleRegime_of_realizedCandidateLift
    {G : SimpleGraph V} {H : SimpleGraph W}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (hlift : PeeledCollarRealizedCandidateLiftsToAmbientSmallCut G H)
    (candidate : CyclicSeparatorCandidate H) :
    ¬ candidate.Realizes := by
  intro hrealizes
  rcases hlift candidate hrealizes with ⟨ambientCut, hcard⟩
  exact regime.ambient.noSmallCyclicEdgeCuts
    ⟨ambientCut, le_trans hcard candidate.hcard_le_four⟩

/--
Under the same inputs, every collar-side separator candidate has the
finite-checker counterexample witness.
-/
theorem counterexample_of_minimalCounterexampleRegime_of_realizedCandidateLift
    {G : SimpleGraph V} {H : SimpleGraph W}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (hlift : PeeledCollarRealizedCandidateLiftsToAmbientSmallCut G H)
    (candidate : CyclicSeparatorCandidate H) :
    candidate.Counterexample :=
  candidate.counterexample_of_crossing_outside
    ((candidate.not_realizes_iff_exists_crossing_outside).1
      (candidate.not_realizes_of_minimalCounterexampleRegime_of_realizedCandidateLift
        regime hlift))

/--
Equivalently, every collar-side separator candidate has an unlisted
side-crossing edge.
-/
theorem exists_crossing_outside_of_minimalCounterexampleRegime_of_realizedCandidateLift
    {G : SimpleGraph V} {H : SimpleGraph W}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (hlift : PeeledCollarRealizedCandidateLiftsToAmbientSmallCut G H)
    (candidate : CyclicSeparatorCandidate H) :
    ∃ e : H.edgeSet, e ∉ candidate.edgeCut ∧
      EdgeCrossesVertexSide H candidate.side e :=
  (candidate.not_realizes_iff_exists_crossing_outside).1
    (candidate.not_realizes_of_minimalCounterexampleRegime_of_realizedCandidateLift
      regime hlift)

/--
One-edge finite-checker output for every collar-side separator candidate under
the CAP5-free regime plus realized-candidate lift.
-/
theorem exists_oneEdge_counterexample_of_minimalCounterexampleRegime_of_realizedCandidateLift
    {G : SimpleGraph V} {H : SimpleGraph W}
    (regime : MinimalCounterexamplePeeledCollarRegime G W H)
    (hlift : PeeledCollarRealizedCandidateLiftsToAmbientSmallCut G H)
    (candidate : CyclicSeparatorCandidate H) :
    ∃ u v : W, ∃ e : H.edgeSet, ∃ p : H.Walk u v,
      e ∉ candidate.edgeCut ∧
        candidate.side u ∧ ¬ candidate.side v ∧
          p.edges = [(e : Sym2 W)] ∧
            ∀ f : H.edgeSet,
              f ∈ candidate.edgeCut → (f : Sym2 W) ∉ p.edges :=
  candidate.exists_oneEdge_counterexample_of_crossing_outside
    (candidate.exists_crossing_outside_of_minimalCounterexampleRegime_of_realizedCandidateLift
      regime hlift)

end CyclicSeparatorCandidate

/--
Checker-facing route index for the realized-candidate lift foundation: every
small separator candidate in the selected peeled collar is forced into the
counterexample bin.
-/
def Section92Step4CAP5FreeRealizedCandidateCounterexampleFoundationRouteIndexTarget :
    Prop :=
  ∀ {V W : Type} [DecidableEq V] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W},
      MinimalCounterexamplePeeledCollarRegime G W H →
        ∀ candidate : CyclicSeparatorCandidate H,
          (¬ candidate.Realizes) ∧
            candidate.Counterexample ∧
            (∃ e : H.edgeSet, e ∉ candidate.edgeCut ∧
              EdgeCrossesVertexSide H candidate.side e) ∧
            ∃ u v : W, ∃ e : H.edgeSet, ∃ p : H.Walk u v,
              e ∉ candidate.edgeCut ∧
                candidate.side u ∧ ¬ candidate.side v ∧
                  p.edges = [(e : Sym2 W)] ∧
                    ∀ f : H.edgeSet,
                      f ∈ candidate.edgeCut → (f : Sym2 W) ∉ p.edges

/--
Route-index theorem for the realized-candidate counterexample foundation
target.
-/
theorem section92Step4CAP5FreeRealizedCandidateCounterexampleFoundationRouteIndexTarget
    (hfoundation :
      CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget) :
    Section92Step4CAP5FreeRealizedCandidateCounterexampleFoundationRouteIndexTarget := by
  intro V W _ _ G H regime candidate
  exact
    ⟨candidate.not_realizes_of_minimalCounterexampleRegime_of_realizedCandidateLift
        regime (hfoundation regime),
      candidate.counterexample_of_minimalCounterexampleRegime_of_realizedCandidateLift
        regime (hfoundation regime),
      candidate.exists_crossing_outside_of_minimalCounterexampleRegime_of_realizedCandidateLift
        regime (hfoundation regime),
      candidate.exists_oneEdge_counterexample_of_minimalCounterexampleRegime_of_realizedCandidateLift
        regime (hfoundation regime)⟩

/--
The realized-candidate lift foundation supplies both the existing route index
and the checker-facing counterexample route index.
-/
theorem cap5FreeRealizedCandidateLiftFoundationTarget_routeIndexTargets
    (hfoundation :
      CAP5FreePeeledCollarRealizedCandidateLiftFoundationTarget) :
    Section92Step4CAP5FreeRealizedCandidateLiftFoundationRouteIndexTarget ∧
      Section92Step4CAP5FreeRealizedCandidateCounterexampleFoundationRouteIndexTarget :=
  ⟨section92Step4CAP5FreeRealizedCandidateLiftFoundationRouteIndexTarget
      hfoundation,
    section92Step4CAP5FreeRealizedCandidateCounterexampleFoundationRouteIndexTarget
      hfoundation⟩

end Mettapedia.GraphTheory.FourColor
