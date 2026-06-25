import Mettapedia.GraphTheory.FourColor.CAP5WitnessGenerator
import Mettapedia.GraphTheory.FourColor.Curriculum.PathXor

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*} [DecidableEq V]
variable {G : SimpleGraph V}
variable {boundaryEdge : Fin 5 → G.edgeSet} {side : V → Prop}

/-- First-coordinate `𝔽₂` weight on `Sym2 V` induced by a color-chain on graph edges.  It is
zero away from actual graph edges. -/
noncomputable def edgeColorFirstCoordinateWeight
    (z : G.edgeSet → Color) : Sym2 V → F2 := by
  classical
  exact fun s =>
    if h : ∃ e : G.edgeSet, (e : Sym2 V) = s then
      (z (Classical.choose h)).1
    else
      0

/-- Second-coordinate `𝔽₂` weight on `Sym2 V` induced by a color-chain on graph edges.  It is
zero away from actual graph edges. -/
noncomputable def edgeColorSecondCoordinateWeight
    (z : G.edgeSet → Color) : Sym2 V → F2 := by
  classical
  exact fun s =>
    if h : ∃ e : G.edgeSet, (e : Sym2 V) = s then
      (z (Classical.choose h)).2
    else
      0

omit [DecidableEq V] in
@[simp] theorem edgeColorFirstCoordinateWeight_coe
    (z : G.edgeSet → Color) (e : G.edgeSet) :
    edgeColorFirstCoordinateWeight z (e : Sym2 V) = (z e).1 := by
  classical
  let h : ∃ e' : G.edgeSet, (e' : Sym2 V) = (e : Sym2 V) := ⟨e, rfl⟩
  have hchoose : Classical.choose h = e :=
    Subtype.ext (Classical.choose_spec h)
  unfold edgeColorFirstCoordinateWeight
  rw [dif_pos h, hchoose]

omit [DecidableEq V] in
@[simp] theorem edgeColorSecondCoordinateWeight_coe
    (z : G.edgeSet → Color) (e : G.edgeSet) :
    edgeColorSecondCoordinateWeight z (e : Sym2 V) = (z e).2 := by
  classical
  let h : ∃ e' : G.edgeSet, (e' : Sym2 V) = (e : Sym2 V) := ⟨e, rfl⟩
  have hchoose : Classical.choose h = e :=
    Subtype.ext (Classical.choose_spec h)
  unfold edgeColorSecondCoordinateWeight
  rw [dif_pos h, hchoose]

omit [DecidableEq V] in
/-- A one-edge walk carrying a nonzero color-chain value has a nonzero first- or
second-coordinate path-xor detector signal. -/
theorem edgeColorCoordinatePathXor_ne_zero_of_walk_edges_singleton_of_color_ne_zero
    (z : G.edgeSet → Color) {u v : V} {e : G.edgeSet} {p : G.Walk u v}
    (hpEdges : p.edges = [(e : Sym2 V)]) (hz : z e ≠ 0) :
    Curriculum.pathXor (edgeColorFirstCoordinateWeight z) p.edges ≠ 0 ∨
      Curriculum.pathXor (edgeColorSecondCoordinateWeight z) p.edges ≠ 0 := by
  rcases (color_ne_zero_iff_fst_or_snd_ne_zero (z e)).1 hz with hfst | hsnd
  · left
    have hsingle :
        Curriculum.pathXor (edgeColorFirstCoordinateWeight z) [(e : Sym2 V)] ≠ 0 := by
      rw [Curriculum.pathXor_singleton]
      simpa using hfst
    simpa [hpEdges] using hsingle
  · right
    have hsingle :
        Curriculum.pathXor (edgeColorSecondCoordinateWeight z) [(e : Sym2 V)] ≠ 0 := by
      rw [Curriculum.pathXor_singleton]
      simpa using hsnd
    simpa [hpEdges] using hsingle

/-- Finite `𝔽₂` detector marking one emitted graph edge and no other `Sym2` edge. -/
def edgeIndicatorWeight (e : G.edgeSet) : Sym2 V → F2 :=
  fun s => if s = (e : Sym2 V) then 1 else 0

@[simp]
theorem edgeIndicatorWeight_self (e : G.edgeSet) :
    edgeIndicatorWeight e (e : Sym2 V) = 1 := by
  simp [edgeIndicatorWeight]

theorem pathXor_edgeIndicatorWeight_singleton (e : G.edgeSet) :
    Curriculum.pathXor (edgeIndicatorWeight e) [(e : Sym2 V)] = 1 := by
  simp [Curriculum.pathXor, edgeIndicatorWeight]

namespace CAP5ExceptionalAnnulusGeneratorNode

/--
A forced edge emitted by a CAP5 node carries its own canonical finite `𝔽₂` detector payload:
the edge-indicator detector fires on the one-edge forced walk and the same edge is outside the
generated support while crossing the proposed side.
-/
theorem forcedCounterexampleEdge_indicatorDetector_payload
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    {e : G.edgeSet} (h : node.ForcedCounterexampleEdge e) :
    ∃ u v : V, ∃ p : G.Walk u v,
      e ∉ node.candidate.edgeSupport ∧
        node.side u ∧ ¬ node.side v ∧
          p.edges = [(e : Sym2 V)] ∧
            (∀ i : Fin 5, i ∈ node.candidate.portalCandidate.portalSet →
              ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
              EdgeCrossesVertexSide G node.side e ∧
                Curriculum.pathXor (edgeIndicatorWeight e) p.edges = 1 := by
  have hcross : EdgeCrossesVertexSide G node.side e :=
    node.forcedCounterexampleEdge_crosses h
  rcases h with ⟨u, v, p, heOutside, hu, hv, hpEdges, havoid⟩
  refine ⟨u, v, p, heOutside, hu, hv, hpEdges, havoid, hcross, ?_⟩
  simp [hpEdges, pathXor_edgeIndicatorWeight_singleton (G := G) e]

end CAP5ExceptionalAnnulusGeneratorNode

namespace CAP5ExceptionalAnnulusGeneratorReport

/--
A forced-counterexample report-bin entry emits a one-edge walk.  Any nonzero finite path-xor
detector signal on that emitted walk therefore exposes a concrete marked edge: the same edge is
outside the generated support, crosses the report side, lies on the emitted walk, and carries
nonzero detector weight.
-/
theorem exists_oneEdge_forcedCounterexampleWalk_detector_payload_of_mem_forcedCounterexampleLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.forcedCounterexampleLatents)
    (weight : Sym2 V → F2) :
    ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
      e ∉ (report.node latent).candidate.edgeSupport ∧
        side u ∧ ¬ side v ∧
          p.edges = [(e : Sym2 V)] ∧
            (∀ i : Fin 5, i ∈ (report.node latent).candidate.portalCandidate.portalSet →
              ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
              EdgeCrossesVertexSide G side e ∧
                (Curriculum.pathXor weight p.edges ≠ 0 →
                  ∃ e' : G.edgeSet,
                    e' ∉ (report.node latent).candidate.edgeSupport ∧
                      EdgeCrossesVertexSide G side e' ∧
                        (e' : Sym2 V) ∈ p.edges ∧
                          weight (e' : Sym2 V) ≠ 0) := by
  rcases report.exists_oneEdge_forcedCounterexampleWalk_of_mem_forcedCounterexampleLatents
      hmem with
    ⟨u, v, e, p, heOutside, hu, hv, hpEdges, havoid, hcross⟩
  refine ⟨u, v, e, p, heOutside, hu, hv, hpEdges, havoid, hcross, ?_⟩
  intro hxor
  have hweight : weight (e : Sym2 V) ≠ 0 := by
    have hsingleton : Curriculum.pathXor weight [(e : Sym2 V)] ≠ 0 := by
      simpa [hpEdges] using hxor
    exact (Curriculum.pathXor_singleton_ne_zero_iff weight
      (e := (e : Sym2 V))).1 hsingleton
  exact ⟨e, heOutside, hcross, by simp [hpEdges], hweight⟩

/--
Canonical detector payload for a forced report row.  Unlike an arbitrary path-xor weight, the
edge-indicator detector is generated from the emitted forced edge itself, so every forced row
has a concrete finite `𝔽₂` signal available for the algebraic follow-up lane.
-/
theorem exists_oneEdge_forcedCounterexampleWalk_indicatorDetector_payload_of_mem_forcedCounterexampleLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.forcedCounterexampleLatents) :
    ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
      e ∉ (report.node latent).candidate.edgeSupport ∧
        side u ∧ ¬ side v ∧
          p.edges = [(e : Sym2 V)] ∧
            (∀ i : Fin 5,
              i ∈ (report.node latent).candidate.portalCandidate.portalSet →
                ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
              EdgeCrossesVertexSide G side e ∧
                Curriculum.pathXor (edgeIndicatorWeight e) p.edges = 1 := by
  rcases report.forcedCounterexample_of_mem_forcedCounterexampleLatents hmem with
    ⟨e, hedge⟩
  rcases (report.node latent).forcedCounterexampleEdge_indicatorDetector_payload hedge with
    ⟨u, v, p, heOutside, hu, hv, hpEdges, havoid, hcross, hxor⟩
  exact ⟨u, v, e, p, heOutside, by
      simpa [node, latentNode] using hu,
    by simpa [node, latentNode] using hv,
    hpEdges, havoid, by simpa [node, latentNode] using hcross, hxor⟩

/--
Per-latent complete-frontier detector payload.  In a cyclically five-edge-connected graph, a
single complete checker latent already has the same one-edge forced-walk detector payload as a
forced-bin latent.  This lets finite search mine complete rows one at a time instead of requiring
the whole 16-latent report to be complete first.
-/
theorem exists_oneEdge_forcedCounterexampleWalk_detector_payload_of_mem_completeCheckerLatents_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.completeCheckerLatents)
    (weight : Sym2 V → F2) :
    ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
      e ∉ (report.node latent).candidate.edgeSupport ∧
        side u ∧ ¬ side v ∧
          p.edges = [(e : Sym2 V)] ∧
            (∀ i : Fin 5, i ∈ (report.node latent).candidate.portalCandidate.portalSet →
              ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
              EdgeCrossesVertexSide G side e ∧
                (Curriculum.pathXor weight p.edges ≠ 0 →
                  ∃ e' : G.edgeSet,
                    e' ∉ (report.node latent).candidate.edgeSupport ∧
                      EdgeCrossesVertexSide G side e' ∧
                        (e' : Sym2 V) ∈ p.edges ∧
                          weight (e' : Sym2 V) ≠ 0) :=
  report.exists_oneEdge_forcedCounterexampleWalk_detector_payload_of_mem_forcedCounterexampleLatents
    ((report.mem_forcedCounterexampleLatents_iff_mem_completeCheckerLatents_of_cyclicallyFiveEdgeConnected
      hcyclic).2 hmem)
    weight

/--
Executable report-completeness form.  If the primitive missing-evidence frontier is empty, every
finite CAP5 latent has the two checker facts needed by the report-level detector bridges.  This is
the handoff from a finite forward checker to the proof-facing CAP5 route: no separate global
portal/cycle hypotheses need to be supplied once the checker frontier is empty.
-/
theorem all_checker_evidence_of_missingCheckerEvidenceLatents_eq_nil
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hmissingEmpty : report.missingCheckerEvidenceLatents = []) :
    (∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      (report.node latent).PortalCrosses) ∧
      (∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles) := by
  have hcompleteAll :
      report.completeCheckerLatents =
          CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge :=
    (report.completeCheckerLatents_eq_all_iff_missingCheckerEvidenceLatents_eq_nil).2
      hmissingEmpty
  constructor
  · intro latent
    have hmemAll :
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge :=
      CAP5ExceptionalAnnulusGeneratorLatent.mem_all latent
    have hcompleteMem : latent ∈ report.completeCheckerLatents := by
      simpa [hcompleteAll] using hmemAll
    have hnotMissing : ¬ (report.node latent).MissingCheckerEvidence :=
      (report.mem_completeCheckerLatents_iff).1 hcompleteMem |>.2
    exact (((report.node latent).not_missingCheckerEvidence_iff_complete).1
      hnotMissing).1
  · intro latent
    have hmemAll :
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge :=
      CAP5ExceptionalAnnulusGeneratorLatent.mem_all latent
    have hcompleteMem : latent ∈ report.completeCheckerLatents := by
      simpa [hcompleteAll] using hmemAll
    have hnotMissing : ¬ (report.node latent).MissingCheckerEvidence :=
      (report.mem_completeCheckerLatents_iff).1 hcompleteMem |>.2
    exact (((report.node latent).not_missingCheckerEvidence_iff_complete).1
      hnotMissing).2

end CAP5ExceptionalAnnulusGeneratorReport

namespace CAP5TransportedEdgeComponentCoverCore

variable {n : Nat}

/--
Named color-coordinate path-xor detector payload emitted by a finite CAP5 checker report.  The
payload packages one enumerated exceptional latent, the forced outside-crossing edge, the one-edge
walk witnessing the side crossing, and the bidirectional coordinate detector: a nonzero color value
on the emitted edge fires a first- or second-coordinate path-xor signal, and any fired coordinate
signal returns a nonzero outside-crossing edge on the walk.
-/
def ColorCoordinatePathXorDetectorPayload
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (p0Inside p4Inside : Bool) (z : G.edgeSet → Color) : Prop :=
  ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
    latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
      latent.p0Inside = p0Inside ∧
        latent.p4Inside = p4Inside ∧
          data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
            latent ∈ report.forcedCounterexampleLatents ∧
              ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
                data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e ∧
                  e ∉ (report.node latent).candidate.edgeSupport ∧
                    side u ∧ ¬ side v ∧
                      p.edges = [(e : Sym2 V)] ∧
                        (∀ i : Fin 5,
                          i ∈ (report.node latent).candidate.portalCandidate.portalSet →
                            ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
                          EdgeCrossesVertexSide G side e ∧
                            (z e ≠ 0 →
                              Curriculum.pathXor (edgeColorFirstCoordinateWeight z)
                                  p.edges ≠ 0 ∨
                                Curriculum.pathXor (edgeColorSecondCoordinateWeight z)
                                  p.edges ≠ 0) ∧
                              ((Curriculum.pathXor (edgeColorFirstCoordinateWeight z)
                                    p.edges ≠ 0 ∨
                                  Curriculum.pathXor (edgeColorSecondCoordinateWeight z)
                                    p.edges ≠ 0) →
                                ∃ e' : G.edgeSet,
                                  data.ExceptionalAnnulusCrossingOutsideEdge
                                    p0Inside p4Inside side e' ∧
                                    e' ∉ (report.node latent).candidate.edgeSupport ∧
                                      EdgeCrossesVertexSide G side e' ∧
                                        (e' : Sym2 V) ∈ p.edges ∧
                                          z e' ≠ 0)

/-- A named path-xor payload carries, in particular, a concrete outside-crossing edge. -/
theorem exists_exceptionalAnnulusCrossingOutsideEdge_of_colorCoordinatePathXorDetectorPayload
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side}
    {p0Inside p4Inside : Bool} {z : G.edgeSet → Color}
    (hpayload : data.ColorCoordinatePathXorDetectorPayload report p0Inside p4Inside z) :
    ∃ e : G.edgeSet,
      data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e := by
  rcases hpayload with
    ⟨_latent, _hlatentMem, _hp0, _hp4, _horientation, _hforced, _u, _v, e, _p,
      hedge, _heOutside, _hu, _hv, _hpEdges, _havoid, _hcross, _hcolorToXor,
      _hxorToEdge⟩
  exact ⟨e, hedge⟩

/-- Named payload for one finite CAP5 extension signal.  If the current emitted-edge classifier
does not yet control the selected boundary-zero chains, a later finite control set exposes either a
side-crossing one-edge path-xor signal or a noncrossing color-coordinate signal. -/
def ExtensionCoordinateSignal
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) : Prop :=
  (∃ z : G.edgeSet → Color,
    z ∈ planarBoundaryZeroSubmodule emb ∧
      z ≠ 0 ∧
        (∀ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
            z e = 0) ∧
          ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
            e ∈ classifier.crossingExtensionFinset controlEdges ∧
              ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                z e ≠ 0 ∧
                  EdgeCrossesVertexSide G side e ∧
                    side u ∧ ¬ side v ∧
                      p.edges = [(e : Sym2 V)] ∧
                        (∀ f : G.edgeSet, f ∈ classifier.emittedFinset →
                          (f : Sym2 V) ∉ p.edges) ∧
                          (Curriculum.pathXor (edgeColorFirstCoordinateWeight z)
                              p.edges ≠ 0 ∨
                            Curriculum.pathXor (edgeColorSecondCoordinateWeight z)
                              p.edges ≠ 0)) ∨
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          (∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0) ∧
            ∃ e : G.edgeSet,
              e ∈ classifier.noncrossingExtensionFinset controlEdges ∧
                ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                  z e ≠ 0 ∧ ¬ EdgeCrossesVertexSide G side e ∧
                    ((z e).1 ≠ 0 ∨ (z e).2 ≠ 0)

/-- Named payload for a CAP5 extension signal that also carries the finite worklist decrease. -/
def ExtensionCoordinateSignalWithProgress
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) : Prop :=
  (∃ z : G.edgeSet → Color,
    z ∈ planarBoundaryZeroSubmodule emb ∧
      z ≠ 0 ∧
        (∀ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
            z e = 0) ∧
          ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
            e ∈ classifier.crossingExtensionFinset controlEdges ∧
              ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                z e ≠ 0 ∧
                  EdgeCrossesVertexSide G side e ∧
                    side u ∧ ¬ side v ∧
                      p.edges = [(e : Sym2 V)] ∧
                        (∀ f : G.edgeSet, f ∈ classifier.emittedFinset →
                          (f : Sym2 V) ∉ p.edges) ∧
                          (Curriculum.pathXor (edgeColorFirstCoordinateWeight z)
                              p.edges ≠ 0 ∨
                            Curriculum.pathXor (edgeColorSecondCoordinateWeight z)
                              p.edges ≠ 0) ∧
                            ((classifier.remainingControlEdges controlEdges).erase e).card <
                              (classifier.remainingControlEdges controlEdges).card) ∨
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          (∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0) ∧
            ∃ e : G.edgeSet,
              e ∈ classifier.noncrossingExtensionFinset controlEdges ∧
                ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                  z e ≠ 0 ∧ ¬ EdgeCrossesVertexSide G side e ∧
                    ((z e).1 ≠ 0 ∨ (z e).2 ≠ 0) ∧
                      ((classifier.remainingControlEdges controlEdges).erase e).card <
                        (classifier.remainingControlEdges controlEdges).card

/-- Forget the finite worklist decrease from a CAP5 extension signal. -/
theorem extensionCoordinateSignal_of_extensionCoordinateSignalWithProgress
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    {classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side}
    {controlEdges : Finset G.edgeSet}
    (hsignal :
      data.ExtensionCoordinateSignalWithProgress emb p0Inside p4Inside side classifier
        controlEdges) :
    data.ExtensionCoordinateSignal emb p0Inside p4Inside side classifier controlEdges := by
  rcases hsignal with hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, hePredicateOutside,
        hze, hcross, hsideu, hsidev, hpEdges, havoid, hcoordinate, _hprogress⟩
    exact Or.inl
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, hePredicateOutside,
        hze, hcross, hsideu, hsidev, hpEdges, havoid, hcoordinate⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze,
        hnotCross, hcoordinate, _hprogress⟩
    exact Or.inr
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze,
        hnotCross, hcoordinate⟩

/--
A named CAP5 extension signal is already an algebraic detector handoff.  If the generator
family contains red and blue single-coordinate probes for every candidate extension edge, the
obstructing boundary-zero chain exposed by the signal has a nonzero family pairing.
-/
theorem exists_boundaryZeroChain_familyPairing_ne_zero_of_extensionCoordinateSignal
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    {p0Inside p4Inside : Bool} {side : V → Prop}
    {classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side}
    {controlEdges : Finset G.edgeSet}
    (hsignal :
      data.ExtensionCoordinateSignal emb p0Inside p4Inside side classifier controlEdges)
    (hwitnessRed :
      ∀ e : G.edgeSet,
        e ∈ classifier.crossingExtensionFinset controlEdges ∨
            e ∈ classifier.noncrossingExtensionFinset controlEdges →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        e ∈ classifier.crossingExtensionFinset controlEdges ∨
            e ∈ classifier.noncrossingExtensionFinset controlEdges →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue) :
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          (∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0) ∧
            ∃ i : κ,
              chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  rcases hsignal with hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, _u, _v, e, _p, heBin, _hePredicateOutside,
        hze, _hcross, _hsideu, _hsidev, _hpEdges, _havoid, _hcoordinate⟩
    rcases exists_familyPairing_ne_zero_of_redBlueSingleCoordinateWitness
        family e hze (hwitnessRed e (Or.inl heBin)) (hwitnessBlue e (Or.inl heBin)) with
      ⟨i, hpair⟩
    exact ⟨z, hzBoundary, hzNonzero, hvanish, i, hpair⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, _hePredicateOutside, hze,
        _hnotCross, _hcoordinate⟩
    rcases exists_familyPairing_ne_zero_of_redBlueSingleCoordinateWitness
        family e hze (hwitnessRed e (Or.inr heBin)) (hwitnessBlue e (Or.inr heBin)) with
      ⟨i, hpair⟩
    exact ⟨z, hzBoundary, hzNonzero, hvanish, i, hpair⟩

/-- Worklist-progress version of the CAP5 extension-signal algebraic handoff. -/
theorem exists_boundaryZeroChain_familyPairing_ne_zero_of_extensionCoordinateSignalWithProgress
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    {p0Inside p4Inside : Bool} {side : V → Prop}
    {classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side}
    {controlEdges : Finset G.edgeSet}
    (hsignal :
      data.ExtensionCoordinateSignalWithProgress emb p0Inside p4Inside side classifier
        controlEdges)
    (hwitnessRed :
      ∀ e : G.edgeSet,
        e ∈ classifier.crossingExtensionFinset controlEdges ∨
            e ∈ classifier.noncrossingExtensionFinset controlEdges →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        e ∈ classifier.crossingExtensionFinset controlEdges ∨
            e ∈ classifier.noncrossingExtensionFinset controlEdges →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue) :
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          (∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0) ∧
            ∃ i : κ,
              chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 :=
  data.exists_boundaryZeroChain_familyPairing_ne_zero_of_extensionCoordinateSignal
    family (data.extensionCoordinateSignal_of_extensionCoordinateSignalWithProgress hsignal)
    hwitnessRed hwitnessBlue

/--
Per-latent complete-frontier bridge into the algebraic forced-edge predicate.  A single complete
CAP5 checker row in a cyclically five-edge-connected graph emits an enumerated forced edge and a
one-edge detector payload for that exact latent.  This is the local handoff from finite
checker-frontier mining to the F₂/path-xor lane.
-/
theorem exists_enumeratedExceptionalAnnulusForcedEdge_oneEdgeWalk_detector_payload_of_mem_completeCheckerLatents_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.completeCheckerLatents)
    (horientation : data.RealizesExceptionalBoundarySupportOrientation latent.orientation)
    (weight : Sym2 V → F2) :
    ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
      data.EnumeratedExceptionalAnnulusForcedEdge
          latent.p0Inside latent.p4Inside side e ∧
        e ∉ (report.node latent).candidate.edgeSupport ∧
          side u ∧ ¬ side v ∧
            p.edges = [(e : Sym2 V)] ∧
              (∀ i : Fin 5,
                i ∈ (report.node latent).candidate.portalCandidate.portalSet →
                  ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
                EdgeCrossesVertexSide G side e ∧
                  (Curriculum.pathXor weight p.edges ≠ 0 →
                    ∃ e' : G.edgeSet,
                      data.EnumeratedExceptionalAnnulusForcedEdge
                        latent.p0Inside latent.p4Inside side e' ∧
                        e' ∉ (report.node latent).candidate.edgeSupport ∧
                          EdgeCrossesVertexSide G side e' ∧
                            (e' : Sym2 V) ∈ p.edges ∧
                              weight (e' : Sym2 V) ≠ 0) := by
  rcases report.exists_oneEdge_forcedCounterexampleWalk_detector_payload_of_mem_completeCheckerLatents_of_cyclicallyFiveEdgeConnected
      hcyclic hmem weight with
    ⟨u, v, e, p, heOutside, hu, hv, hpEdges, havoid, hcross, hdetector⟩
  have hlatentMem :
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge :=
    (report.mem_completeCheckerLatents_iff).1 hmem |>.1
  have hforcedNode : (report.node latent).ForcedCounterexampleEdge e := by
    refine ⟨u, v, p, heOutside, ?_, ?_, hpEdges, havoid⟩
    · simpa [CAP5ExceptionalAnnulusGeneratorReport.node,
        CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hu
    · simpa [CAP5ExceptionalAnnulusGeneratorReport.node,
        CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hv
  have hedge :
      data.EnumeratedExceptionalAnnulusForcedEdge
        latent.p0Inside latent.p4Inside side e :=
    ⟨latent, hlatentMem, rfl, rfl, horientation, by
      simpa [CAP5ExceptionalAnnulusGeneratorReport.node,
        CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hforcedNode⟩
  refine ⟨u, v, e, p, hedge, heOutside, hu, hv, hpEdges, havoid, hcross, ?_⟩
  intro hxor
  rcases hdetector hxor with ⟨e', heOutside', hcross', heMem', hweight'⟩
  have heqSym : (e' : Sym2 V) = (e : Sym2 V) := by
    simpa [hpEdges] using heMem'
  have heq : e' = e := Subtype.ext heqSym
  subst e'
  exact ⟨e, hedge, heOutside', hcross', by simp [hpEdges], hweight'⟩

/--
Complete cyclic-five exceptional CAP5 reports emit a one-edge forced walk.  A nonzero finite
path-xor detector signal on that emitted walk exposes a marked enumerated forced edge, keeping
the detector output attached to the same finite generator payload consumed by the algebraic
lane.
-/
theorem exists_enumeratedExceptionalAnnulusForcedEdge_oneEdgeWalk_detector_payload_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles)
    (weight : Sym2 V → F2) :
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        latent.p0Inside = p0Inside ∧
          latent.p4Inside = p4Inside ∧
            data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
              latent ∈ report.forcedCounterexampleLatents ∧
                ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
                  data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                    e ∉ (report.node latent).candidate.edgeSupport ∧
                      side u ∧ ¬ side v ∧
                        p.edges = [(e : Sym2 V)] ∧
                          (∀ i : Fin 5,
                            i ∈ (report.node latent).candidate.portalCandidate.portalSet →
                              ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
                            EdgeCrossesVertexSide G side e ∧
                              (Curriculum.pathXor weight p.edges ≠ 0 →
                                ∃ e' : G.edgeSet,
                                  data.EnumeratedExceptionalAnnulusForcedEdge
                                    p0Inside p4Inside side e' ∧
                                    e' ∉ (report.node latent).candidate.edgeSupport ∧
                                      EdgeCrossesVertexSide G side e' ∧
                                        (e' : Sym2 V) ∈ p.edges ∧
                                          weight (e' : Sym2 V) ≠ 0) := by
  rcases data.exists_enumeratedExceptionalAnnulusForcedEdge_and_oneEdge_forcedCounterexampleWalk_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      report p0Inside p4Inside h hcyclic hportal hcycles with
    ⟨latent, hlatentMem, hp0, hp4, horientation, hforced, u, v, e, p, hedge,
      heOutside, hu, hv, hpEdges, havoid, hcross⟩
  refine
    ⟨latent, hlatentMem, hp0, hp4, horientation, hforced, u, v, e, p, hedge,
      heOutside, hu, hv, hpEdges, havoid, hcross, ?_⟩
  intro hxor
  have hweight : weight (e : Sym2 V) ≠ 0 := by
    have hsingleton : Curriculum.pathXor weight [(e : Sym2 V)] ≠ 0 := by
      simpa [hpEdges] using hxor
    exact (Curriculum.pathXor_singleton_ne_zero_iff weight
      (e := (e : Sym2 V))).1 hsingleton
  exact ⟨e, hedge, heOutside, hcross, by simp [hpEdges], hweight⟩

/--
Empty-frontier form of the one-edge detector payload.  A finite CAP5 checker run with no missing
primitive checker evidence can be consumed directly by the detector/algebraic lane: cyclic
five-edge-connectivity turns the complete checker frontier into a forced-counterexample frontier,
and the emitted edge remains attached to the enumerated exceptional annulus predicate.
-/
theorem exists_enumeratedExceptionalAnnulusForcedEdge_oneEdgeWalk_detector_payload_of_missingCheckerEvidenceLatents_eq_nil_of_isExceptional_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hmissingEmpty : report.missingCheckerEvidenceLatents = [])
    (weight : Sym2 V → F2) :
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        latent.p0Inside = p0Inside ∧
          latent.p4Inside = p4Inside ∧
            data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
              latent ∈ report.forcedCounterexampleLatents ∧
                ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
                  data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                    e ∉ (report.node latent).candidate.edgeSupport ∧
                      side u ∧ ¬ side v ∧
                        p.edges = [(e : Sym2 V)] ∧
                          (∀ i : Fin 5,
                            i ∈ (report.node latent).candidate.portalCandidate.portalSet →
                              ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
                            EdgeCrossesVertexSide G side e ∧
                              (Curriculum.pathXor weight p.edges ≠ 0 →
                                ∃ e' : G.edgeSet,
                                  data.EnumeratedExceptionalAnnulusForcedEdge
                                    p0Inside p4Inside side e' ∧
                                    e' ∉ (report.node latent).candidate.edgeSupport ∧
                                      EdgeCrossesVertexSide G side e' ∧
                                        (e' : Sym2 V) ∈ p.edges ∧
                                          weight (e' : Sym2 V) ≠ 0) := by
  rcases report.all_checker_evidence_of_missingCheckerEvidenceLatents_eq_nil
      hmissingEmpty with
    ⟨hportal, hcycles⟩
  exact
    data.exists_enumeratedExceptionalAnnulusForcedEdge_oneEdgeWalk_detector_payload_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      report p0Inside p4Inside h hcyclic hportal hcycles weight

/--
Complete cyclic-five exceptional CAP5 reports feed the algebraic normal form directly.  The
one-edge path-xor detector either stays silent, or a nonzero signal exposes an edge in the
`ExceptionalAnnulusCrossingOutsideEdge` predicate: an edge outside the realized support crossing
the selected side.
-/
theorem exists_exceptionalAnnulusCrossingOutsideEdge_oneEdgeWalk_detector_payload_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles)
    (weight : Sym2 V → F2) :
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        latent.p0Inside = p0Inside ∧
          latent.p4Inside = p4Inside ∧
            data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
              latent ∈ report.forcedCounterexampleLatents ∧
                ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
                  data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e ∧
                    e ∉ (report.node latent).candidate.edgeSupport ∧
                      side u ∧ ¬ side v ∧
                        p.edges = [(e : Sym2 V)] ∧
                          (∀ i : Fin 5,
                            i ∈ (report.node latent).candidate.portalCandidate.portalSet →
                              ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
                            EdgeCrossesVertexSide G side e ∧
                              (Curriculum.pathXor weight p.edges ≠ 0 →
                                ∃ e' : G.edgeSet,
                                  data.ExceptionalAnnulusCrossingOutsideEdge
                                    p0Inside p4Inside side e' ∧
                                    e' ∉ (report.node latent).candidate.edgeSupport ∧
                                      EdgeCrossesVertexSide G side e' ∧
                                        (e' : Sym2 V) ∈ p.edges ∧
                                          weight (e' : Sym2 V) ≠ 0) := by
  rcases data.exists_enumeratedExceptionalAnnulusForcedEdge_oneEdgeWalk_detector_payload_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      report p0Inside p4Inside h hcyclic hportal hcycles weight with
    ⟨latent, hlatentMem, hp0, hp4, horientation, hforced, u, v, e, p, _hedge,
      heOutside, hu, hv, hpEdges, havoid, hcross, hdetector⟩
  let edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge :=
    (report.node latent).candidate
  have horientationCandidate :
      data.RealizesExceptionalBoundarySupportOrientation
        edgeCandidate.portalCandidate.orientation := by
    simpa [edgeCandidate, CAP5ExceptionalAnnulusGeneratorReport.node,
      CAP5ExceptionalAnnulusGeneratorReport.latentNode] using horientation
  have hsideCase :
      edgeCandidate.portalCandidate.sideCase =
        CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside := by
    simp [edgeCandidate, CAP5ExceptionalAnnulusGeneratorReport.node,
      CAP5ExceptionalAnnulusGeneratorReport.latentNode,
      CAP5ExceptionalAnnulusGeneratorLatent.sideCase, hp0, hp4]
  have hedgeNormal :
      data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e :=
    ⟨edgeCandidate, horientationCandidate, hsideCase, by
      simpa [edgeCandidate] using heOutside, hcross⟩
  refine
    ⟨latent, hlatentMem, hp0, hp4, horientation, hforced, u, v, e, p,
      hedgeNormal, heOutside, hu, hv, hpEdges, havoid, hcross, ?_⟩
  intro hxor
  rcases hdetector hxor with
    ⟨e', _hedge', heOutside', hcross', heMem, hweight⟩
  have hedgeNormal' :
      data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e' :=
    ⟨edgeCandidate, horientationCandidate, hsideCase, by
      simpa [edgeCandidate] using heOutside', hcross'⟩
  exact ⟨e', hedgeNormal', heOutside', hcross', heMem, hweight⟩

/--
Empty-frontier crossing-outside detector form.  This is the same executable checker handoff as the
enumerated-edge theorem, normalized to the broader predicate consumed by the algebraic extension
machinery.
-/
theorem exists_exceptionalAnnulusCrossingOutsideEdge_oneEdgeWalk_detector_payload_of_missingCheckerEvidenceLatents_eq_nil_of_isExceptional_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hmissingEmpty : report.missingCheckerEvidenceLatents = [])
    (weight : Sym2 V → F2) :
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        latent.p0Inside = p0Inside ∧
          latent.p4Inside = p4Inside ∧
            data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
              latent ∈ report.forcedCounterexampleLatents ∧
                ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
                  data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e ∧
                    e ∉ (report.node latent).candidate.edgeSupport ∧
                      side u ∧ ¬ side v ∧
                        p.edges = [(e : Sym2 V)] ∧
                          (∀ i : Fin 5,
                            i ∈ (report.node latent).candidate.portalCandidate.portalSet →
                              ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
                            EdgeCrossesVertexSide G side e ∧
                              (Curriculum.pathXor weight p.edges ≠ 0 →
                                ∃ e' : G.edgeSet,
                                  data.ExceptionalAnnulusCrossingOutsideEdge
                                    p0Inside p4Inside side e' ∧
                                    e' ∉ (report.node latent).candidate.edgeSupport ∧
                                      EdgeCrossesVertexSide G side e' ∧
                                        (e' : Sym2 V) ∈ p.edges ∧
                                          weight (e' : Sym2 V) ≠ 0) := by
  rcases report.all_checker_evidence_of_missingCheckerEvidenceLatents_eq_nil
      hmissingEmpty with
    ⟨hportal, hcycles⟩
  exact
    data.exists_exceptionalAnnulusCrossingOutsideEdge_oneEdgeWalk_detector_payload_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      report p0Inside p4Inside h hcyclic hportal hcycles weight

/--
Complete cyclic-five exceptional CAP5 reports turn the emitted one-edge walk into a coordinate
path-xor detector for any color-chain on graph edges.  If the emitted outside-crossing edge is
nonzero in the chain, one of its two `𝔽₂` coordinate detectors fires; conversely, any fired
coordinate detector on that one-edge walk returns a crossing-outside edge where the chain is
nonzero.
-/
theorem exists_exceptionalAnnulusCrossingOutsideEdge_colorCoordinatePathXor_detector_payload_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles)
    (z : G.edgeSet → Color) :
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        latent.p0Inside = p0Inside ∧
          latent.p4Inside = p4Inside ∧
            data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
              latent ∈ report.forcedCounterexampleLatents ∧
                ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
                  data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e ∧
                    e ∉ (report.node latent).candidate.edgeSupport ∧
                      side u ∧ ¬ side v ∧
                        p.edges = [(e : Sym2 V)] ∧
                          (∀ i : Fin 5,
                            i ∈ (report.node latent).candidate.portalCandidate.portalSet →
                              ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
                            EdgeCrossesVertexSide G side e ∧
                              (z e ≠ 0 →
                                Curriculum.pathXor (edgeColorFirstCoordinateWeight z)
                                    p.edges ≠ 0 ∨
                                  Curriculum.pathXor (edgeColorSecondCoordinateWeight z)
                                    p.edges ≠ 0) ∧
                                ((Curriculum.pathXor (edgeColorFirstCoordinateWeight z)
                                      p.edges ≠ 0 ∨
                                    Curriculum.pathXor (edgeColorSecondCoordinateWeight z)
                                      p.edges ≠ 0) →
                                  ∃ e' : G.edgeSet,
                                    data.ExceptionalAnnulusCrossingOutsideEdge
                                      p0Inside p4Inside side e' ∧
                                      e' ∉ (report.node latent).candidate.edgeSupport ∧
                                        EdgeCrossesVertexSide G side e' ∧
                                          (e' : Sym2 V) ∈ p.edges ∧
                                            z e' ≠ 0) := by
  rcases data.exists_exceptionalAnnulusCrossingOutsideEdge_oneEdgeWalk_detector_payload_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      report p0Inside p4Inside h hcyclic hportal hcycles
      (edgeColorFirstCoordinateWeight z) with
    ⟨latent, hlatentMem, hp0, hp4, horientation, hforced, u, v, e, p, hedge,
      heOutside, hu, hv, hpEdges, havoid, hcross, _hdetector⟩
  refine
    ⟨latent, hlatentMem, hp0, hp4, horientation, hforced, u, v, e, p,
      hedge, heOutside, hu, hv, hpEdges, havoid, hcross, ?_, ?_⟩
  · intro hz
    exact edgeColorCoordinatePathXor_ne_zero_of_walk_edges_singleton_of_color_ne_zero
      z hpEdges hz
  · intro hsignal
    have heMem : (e : Sym2 V) ∈ p.edges := by
      simp [hpEdges]
    have hz : z e ≠ 0 := by
      rcases hsignal with hfst | hsnd
      · have hweight :
            edgeColorFirstCoordinateWeight z (e : Sym2 V) ≠ 0 := by
          have hsingle :
              Curriculum.pathXor (edgeColorFirstCoordinateWeight z)
                  [(e : Sym2 V)] ≠ 0 := by
            simpa [hpEdges] using hfst
          exact (Curriculum.pathXor_singleton_ne_zero_iff
            (edgeColorFirstCoordinateWeight z) (e := (e : Sym2 V))).1 hsingle
        exact (color_ne_zero_iff_fst_or_snd_ne_zero (z e)).2
          (Or.inl (by simpa using hweight))
      · have hweight :
            edgeColorSecondCoordinateWeight z (e : Sym2 V) ≠ 0 := by
          have hsingle :
              Curriculum.pathXor (edgeColorSecondCoordinateWeight z)
                  [(e : Sym2 V)] ≠ 0 := by
            simpa [hpEdges] using hsnd
          exact (Curriculum.pathXor_singleton_ne_zero_iff
            (edgeColorSecondCoordinateWeight z) (e := (e : Sym2 V))).1 hsingle
        exact (color_ne_zero_iff_fst_or_snd_ne_zero (z e)).2
          (Or.inr (by simpa using hweight))
    exact ⟨e, hedge, heOutside, hcross, heMem, hz⟩

/--
Empty-frontier coordinate detector form.  A finished finite checker report supplies the
color-coordinate path-xor witness used by the algebraic lane without separately restating the
portal-crossing and side-cycle checker facts.
-/
theorem exists_exceptionalAnnulusCrossingOutsideEdge_colorCoordinatePathXor_detector_payload_of_missingCheckerEvidenceLatents_eq_nil_of_isExceptional_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hmissingEmpty : report.missingCheckerEvidenceLatents = [])
    (z : G.edgeSet → Color) :
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        latent.p0Inside = p0Inside ∧
          latent.p4Inside = p4Inside ∧
            data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
              latent ∈ report.forcedCounterexampleLatents ∧
                ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
                  data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e ∧
                    e ∉ (report.node latent).candidate.edgeSupport ∧
                      side u ∧ ¬ side v ∧
                        p.edges = [(e : Sym2 V)] ∧
                          (∀ i : Fin 5,
                            i ∈ (report.node latent).candidate.portalCandidate.portalSet →
                              ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
                            EdgeCrossesVertexSide G side e ∧
                              (z e ≠ 0 →
                                Curriculum.pathXor (edgeColorFirstCoordinateWeight z)
                                    p.edges ≠ 0 ∨
                                  Curriculum.pathXor (edgeColorSecondCoordinateWeight z)
                                    p.edges ≠ 0) ∧
                                ((Curriculum.pathXor (edgeColorFirstCoordinateWeight z)
                                      p.edges ≠ 0 ∨
                                    Curriculum.pathXor (edgeColorSecondCoordinateWeight z)
                                      p.edges ≠ 0) →
                                  ∃ e' : G.edgeSet,
                                    data.ExceptionalAnnulusCrossingOutsideEdge
                                      p0Inside p4Inside side e' ∧
                                      e' ∉ (report.node latent).candidate.edgeSupport ∧
                                        EdgeCrossesVertexSide G side e' ∧
                                          (e' : Sym2 V) ∈ p.edges ∧
                                            z e' ≠ 0) := by
  rcases report.all_checker_evidence_of_missingCheckerEvidenceLatents_eq_nil
      hmissingEmpty with
    ⟨hportal, hcycles⟩
  exact
    data.exists_exceptionalAnnulusCrossingOutsideEdge_colorCoordinatePathXor_detector_payload_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      report p0Inside p4Inside h hcyclic hportal hcycles z

/-- Named-payload form of the empty-frontier coordinate detector handoff. -/
theorem colorCoordinatePathXorDetectorPayload_of_missingCheckerEvidenceLatents_eq_nil_of_isExceptional_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hmissingEmpty : report.missingCheckerEvidenceLatents = [])
    (z : G.edgeSet → Color) :
    data.ColorCoordinatePathXorDetectorPayload report p0Inside p4Inside z :=
  data.exists_exceptionalAnnulusCrossingOutsideEdge_colorCoordinatePathXor_detector_payload_of_missingCheckerEvidenceLatents_eq_nil_of_isExceptional_of_cyclicallyFiveEdgeConnected
    report p0Inside p4Inside h hcyclic hmissingEmpty z

/--
Canonical finite-checker dichotomy for the CAP5 generator.  Running the executable checker either
returns a concrete latent with missing primitive checker evidence, or an empty missing frontier
feeds the color-coordinate path-xor detector payload.  This is the generator-facing boundary:
partial rows become the next hypothesis-discovery target, while a finished frontier goes directly
to the algebraic/cocycle lane.
-/
theorem ofDecidableChecks_missingCheckerEvidence_or_colorCoordinatePathXor_detector_payload_of_isExceptional_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).RealizedSeparator)]
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (z : G.edgeSet → Color) :
    (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).MissingCheckerEvidence) ∨
      ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
          latent.p0Inside = p0Inside ∧
            latent.p4Inside = p4Inside ∧
              data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
                latent ∈ (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
                  boundaryEdge side).forcedCounterexampleLatents ∧
                  ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
                    data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e ∧
                      e ∉ ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
                        boundaryEdge side).node latent).candidate.edgeSupport ∧
                        side u ∧ ¬ side v ∧
                          p.edges = [(e : Sym2 V)] ∧
                            (∀ i : Fin 5,
                              i ∈ ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
                                boundaryEdge side).node latent).candidate.portalCandidate.portalSet →
                                ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
                              EdgeCrossesVertexSide G side e ∧
                                (z e ≠ 0 →
                                  Curriculum.pathXor (edgeColorFirstCoordinateWeight z)
                                      p.edges ≠ 0 ∨
                                    Curriculum.pathXor (edgeColorSecondCoordinateWeight z)
                                      p.edges ≠ 0) ∧
                                  ((Curriculum.pathXor (edgeColorFirstCoordinateWeight z)
                                        p.edges ≠ 0 ∨
                                      Curriculum.pathXor (edgeColorSecondCoordinateWeight z)
                                        p.edges ≠ 0) →
                                    ∃ e' : G.edgeSet,
                                      data.ExceptionalAnnulusCrossingOutsideEdge
                                        p0Inside p4Inside side e' ∧
                                        e' ∉ ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
                                          boundaryEdge side).node latent).candidate.edgeSupport ∧
                                          EdgeCrossesVertexSide G side e' ∧
                                            (e' : Sym2 V) ∈ p.edges ∧
                                              z e' ≠ 0) := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks boundaryEdge side
  by_cases hmissingEmpty : report.missingCheckerEvidenceLatents = []
  · right
    simpa [report] using
      data.exists_exceptionalAnnulusCrossingOutsideEdge_colorCoordinatePathXor_detector_payload_of_missingCheckerEvidenceLatents_eq_nil_of_isExceptional_of_cyclicallyFiveEdgeConnected
        report p0Inside p4Inside h hcyclic hmissingEmpty z
  · left
    rcases (report.missingCheckerEvidenceLatents_ne_nil_iff_exists_missingCheckerEvidence).1
        hmissingEmpty with
      ⟨latent, hmem, hmissing⟩
    exact ⟨latent, hmem, by
      simpa [report, CAP5ExceptionalAnnulusGeneratorReport.node,
        CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hmissing⟩

/--
Named-payload, three-bin version of the canonical finite-checker dichotomy.  A checker run either
identifies the exact primitive evidence still missing from some enumerated latent, or it emits the
coordinate path-xor detector payload consumed by the algebraic/cocycle lane.
-/
theorem ofDecidableChecks_missing_checker_ingredient_or_colorCoordinatePathXorDetectorPayload_of_isExceptional_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).RealizedSeparator)]
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (z : G.edgeSet → Color) :
    ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).MissingPortalCrossingEvidence) ∨
      (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
          (CAP5ExceptionalAnnulusGeneratorReport.latentNode
            boundaryEdge side latent).MissingSelectedSideCycleEvidence) ∨
        (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
          latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
            (CAP5ExceptionalAnnulusGeneratorReport.latentNode
              boundaryEdge side latent).MissingComplementarySideCycleEvidence)) ∨
      data.ColorCoordinatePathXorDetectorPayload
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks boundaryEdge side)
        p0Inside p4Inside z := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks boundaryEdge side
  by_cases hmissingEmpty : report.missingCheckerEvidenceLatents = []
  · right
    simpa [report] using
      data.colorCoordinatePathXorDetectorPayload_of_missingCheckerEvidenceLatents_eq_nil_of_isExceptional_of_cyclicallyFiveEdgeConnected
        report p0Inside p4Inside h hcyclic hmissingEmpty z
  · left
    have hingredient :=
      (report.missingCheckerEvidenceLatents_ne_nil_iff_exists_missing_checker_ingredient).1
        hmissingEmpty
    simpa [report, CAP5ExceptionalAnnulusGeneratorReport.node,
      CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hingredient

/--
Edge-obstruction form of the canonical finite-checker dichotomy.  Once the primitive
missing-checker frontier is empty, cyclic five-edge-connectivity already gives a concrete
exceptional-annulus crossing-outside edge; otherwise the generator reports exactly which primitive
checker ingredient is missing.
-/
theorem ofDecidableChecks_missing_checker_ingredient_or_exceptionalAnnulusCrossingOutsideEdge_of_isExceptional_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
        boundaryEdge side latent).RealizedSeparator)]
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).MissingPortalCrossingEvidence) ∨
      (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
          (CAP5ExceptionalAnnulusGeneratorReport.latentNode
            boundaryEdge side latent).MissingSelectedSideCycleEvidence) ∨
        (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
          latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
            (CAP5ExceptionalAnnulusGeneratorReport.latentNode
              boundaryEdge side latent).MissingComplementarySideCycleEvidence)) ∨
      ∃ e : G.edgeSet,
        data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e := by
  rcases data.ofDecidableChecks_missing_checker_ingredient_or_colorCoordinatePathXorDetectorPayload_of_isExceptional_of_cyclicallyFiveEdgeConnected
      side p0Inside p4Inside h hcyclic (fun _ => 0) with hingredient | hpayload
  · exact Or.inl hingredient
  · exact Or.inr
      (data.exists_exceptionalAnnulusCrossingOutsideEdge_of_colorCoordinatePathXorDetectorPayload
        hpayload)

/--
Coordinate-signal form of the failed finite-control extension.  When the current CAP5 emitted
edge classifier does not control all selected boundary-zero chains but a later finite control set
does, the generator's next witness is not just a nonzero color value: the crossing branch carries
a first- or second-coordinate path-xor signal on its one-edge walk, while the noncrossing branch
carries an explicit nonzero color coordinate for the algebraic detector.
-/
theorem exists_boundaryZeroChain_and_extensionFinsetWitness_coordinateSignal_crossing_or_noncrossing_of_not_classifierControl_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hnotControl :
      ¬ ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0) :
    (∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          (∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0) ∧
            ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
              e ∈ classifier.crossingExtensionFinset controlEdges ∧
                ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                  z e ≠ 0 ∧
                    EdgeCrossesVertexSide G side e ∧
                      side u ∧ ¬ side v ∧
                        p.edges = [(e : Sym2 V)] ∧
                          (∀ f : G.edgeSet, f ∈ classifier.emittedFinset →
                            (f : Sym2 V) ∉ p.edges) ∧
                            (Curriculum.pathXor (edgeColorFirstCoordinateWeight z)
                                p.edges ≠ 0 ∨
                              Curriculum.pathXor (edgeColorSecondCoordinateWeight z)
                                p.edges ≠ 0)) ∨
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ e : G.edgeSet,
                e ∈ classifier.noncrossingExtensionFinset controlEdges ∧
                  ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                    z e ≠ 0 ∧ ¬ EdgeCrossesVertexSide G side e ∧
                      ((z e).1 ≠ 0 ∨ (z e).2 ≠ 0) := by
  rcases data.exists_boundaryZeroChain_and_extensionFinsetWitness_crossing_or_noncrossing_of_not_classifierControl_of_finsetControl
      emb p0Inside p4Inside side classifier controlEdges hnotControl hcontrol with
    hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, hePredicateOutside,
        hze, hcross, hsideu, hsidev, hpEdges, havoid⟩
    have hsignal :
        Curriculum.pathXor (edgeColorFirstCoordinateWeight z) p.edges ≠ 0 ∨
          Curriculum.pathXor (edgeColorSecondCoordinateWeight z) p.edges ≠ 0 :=
      edgeColorCoordinatePathXor_ne_zero_of_walk_edges_singleton_of_color_ne_zero
        z hpEdges hze
    exact Or.inl
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, hePredicateOutside,
        hze, hcross, hsideu, hsidev, hpEdges, havoid, hsignal⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze,
        hnotCross⟩
    have hcoord : (z e).1 ≠ 0 ∨ (z e).2 ≠ 0 :=
      (color_ne_zero_iff_fst_or_snd_ne_zero (z e)).1 hze
    exact Or.inr
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze,
        hnotCross, hcoord⟩

/-- Compact named-payload form of the failed finite-control coordinate signal. -/
theorem extensionCoordinateSignal_of_not_classifierControl_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hnotControl :
      ¬ ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0) :
    data.ExtensionCoordinateSignal emb p0Inside p4Inside side classifier controlEdges :=
  data.exists_boundaryZeroChain_and_extensionFinsetWitness_coordinateSignal_crossing_or_noncrossing_of_not_classifierControl_of_finsetControl
    emb p0Inside p4Inside side classifier controlEdges hnotControl hcontrol

/--
Failed-synthesis generator step with coordinate-level output.  In the cyclic-five exceptional
CAP5 setting, if the current emitted-edge classifier does not synthesize Theorem 4.9 but a later
finite control set controls the selected boundary-zero chains, then the run has both an emitted
forced CAP5 edge and a next extension witness whose nonzero obstruction is visible as either a
crossing path-xor signal or a noncrossing color-coordinate signal.
-/
theorem forcedEdge_and_extensionFinsetWitness_coordinateSignal_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v))
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitnessRed :
      ∀ e : G.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    (∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) ∧
      ((∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
                e ∈ classifier.crossingExtensionFinset controlEdges ∧
                  ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                    z e ≠ 0 ∧
                      EdgeCrossesVertexSide G side e ∧
                        side u ∧ ¬ side v ∧
                          p.edges = [(e : Sym2 V)] ∧
                            (∀ f : G.edgeSet, f ∈ classifier.emittedFinset →
                              (f : Sym2 V) ∉ p.edges) ∧
                              (Curriculum.pathXor (edgeColorFirstCoordinateWeight z)
                                  p.edges ≠ 0 ∨
                                Curriculum.pathXor (edgeColorSecondCoordinateWeight z)
                                  p.edges ≠ 0)) ∨
        ∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              (∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) ∧
                ∃ e : G.edgeSet,
                  e ∈ classifier.noncrossingExtensionFinset controlEdges ∧
                    ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                      z e ≠ 0 ∧ ¬ EdgeCrossesVertexSide G side e ∧
                        ((z e).1 ≠ 0 ∨ (z e).2 ≠ 0)) := by
  refine ⟨?_, ?_⟩
  · exact
      data.exists_enumeratedExceptionalAnnulusForcedEdge_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
        p0Inside p4Inside h side hcyclic hportal_crosses hcycles
  · have hnotControl :
        ¬ ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule emb →
          (∀ e ∈ classifier.emittedFinset, z e = 0) →
            z = 0 := by
      intro hclassifierControl
      exact hnotSynthesis
        (data.theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierControl
          emb C₀ colorings hsubset family p0Inside p4Inside side classifier
          hclassifierControl hwitnessRed hwitnessBlue)
    exact
      data.exists_boundaryZeroChain_and_extensionFinsetWitness_coordinateSignal_crossing_or_noncrossing_of_not_classifierControl_of_finsetControl
        emb p0Inside p4Inside side classifier controlEdges hnotControl hcontrol

/--
Loop-facing coordinate-signal form of a failed CAP5 generator step.  This combines the
coordinate detector output with the finite worklist measure: the next crossing or noncrossing
extension witness is not merely diagnostic, because erasing its edge strictly decreases
`remainingControlEdges`.
-/
theorem forcedEdge_and_extensionFinsetWitness_coordinateSignal_with_worklistProgress_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v))
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitnessRed :
      ∀ e : G.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    (∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) ∧
      ((∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
                e ∈ classifier.crossingExtensionFinset controlEdges ∧
                  ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                    z e ≠ 0 ∧
                      EdgeCrossesVertexSide G side e ∧
                        side u ∧ ¬ side v ∧
                          p.edges = [(e : Sym2 V)] ∧
                            (∀ f : G.edgeSet, f ∈ classifier.emittedFinset →
                              (f : Sym2 V) ∉ p.edges) ∧
                              (Curriculum.pathXor (edgeColorFirstCoordinateWeight z)
                                  p.edges ≠ 0 ∨
                                Curriculum.pathXor (edgeColorSecondCoordinateWeight z)
                                  p.edges ≠ 0) ∧
                                ((classifier.remainingControlEdges controlEdges).erase e).card <
                                  (classifier.remainingControlEdges controlEdges).card) ∨
        ∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              (∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) ∧
                ∃ e : G.edgeSet,
                  e ∈ classifier.noncrossingExtensionFinset controlEdges ∧
                    ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                      z e ≠ 0 ∧ ¬ EdgeCrossesVertexSide G side e ∧
                        ((z e).1 ≠ 0 ∨ (z e).2 ≠ 0) ∧
                          ((classifier.remainingControlEdges controlEdges).erase e).card <
                            (classifier.remainingControlEdges controlEdges).card) := by
  rcases data.forcedEdge_and_extensionFinsetWitness_coordinateSignal_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
      emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue hnotSynthesis with
    ⟨hforced, hbranch⟩
  refine ⟨hforced, ?_⟩
  rcases hbranch with hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, hePredicateOutside,
        hze, hcross, hsideu, hsidev, hpEdges, havoid, hsignal⟩
    exact Or.inl
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, hePredicateOutside,
        hze, hcross, hsideu, hsidev, hpEdges, havoid, hsignal,
        classifier.card_erase_remainingControlEdges_lt_of_mem_crossingExtensionFinset
          controlEdges heBin⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze,
        hnotCross, hcoord⟩
    exact Or.inr
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze,
        hnotCross, hcoord,
        classifier.card_erase_remainingControlEdges_lt_of_mem_noncrossingExtensionFinset
          controlEdges heBin⟩

/-- Compact named-payload form of a failed CAP5 synthesis step with finite worklist progress. -/
theorem forcedEdge_and_extensionCoordinateSignalWithProgress_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v))
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitnessRed :
      ∀ e : G.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    (∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) ∧
      data.ExtensionCoordinateSignalWithProgress emb p0Inside p4Inside side classifier
        controlEdges :=
  data.forcedEdge_and_extensionFinsetWitness_coordinateSignal_with_worklistProgress_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
    emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
    hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue hnotSynthesis

/--
One-step finite generator runner with coordinate-level output.  Either the current CAP5
classifier already synthesizes Theorem 4.9, or the failure branch returns the emitted forced edge
and a next crossing/noncrossing coordinate-signal witness whose erasure strictly decreases the
remaining finite worklist.
-/
theorem theorem49BoundaryRootSynthesis_or_forcedEdge_and_extensionFinsetWitness_coordinateSignal_with_worklistProgress_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v))
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitnessRed :
      ∀ e : G.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue) :
    Theorem49BoundaryRootSynthesis emb C₀ ∨
      (∃ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) ∧
        ((∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              (∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) ∧
                ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
                  e ∈ classifier.crossingExtensionFinset controlEdges ∧
                    ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                      z e ≠ 0 ∧
                        EdgeCrossesVertexSide G side e ∧
                          side u ∧ ¬ side v ∧
                            p.edges = [(e : Sym2 V)] ∧
                              (∀ f : G.edgeSet, f ∈ classifier.emittedFinset →
                                (f : Sym2 V) ∉ p.edges) ∧
                                (Curriculum.pathXor (edgeColorFirstCoordinateWeight z)
                                    p.edges ≠ 0 ∨
                                  Curriculum.pathXor (edgeColorSecondCoordinateWeight z)
                                    p.edges ≠ 0) ∧
                                  ((classifier.remainingControlEdges controlEdges).erase e).card <
                                    (classifier.remainingControlEdges controlEdges).card) ∨
          ∃ z : G.edgeSet → Color,
            z ∈ planarBoundaryZeroSubmodule emb ∧
              z ≠ 0 ∧
                (∀ e : G.edgeSet,
                  data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                    z e = 0) ∧
                  ∃ e : G.edgeSet,
                    e ∈ classifier.noncrossingExtensionFinset controlEdges ∧
                      ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                        z e ≠ 0 ∧ ¬ EdgeCrossesVertexSide G side e ∧
                          ((z e).1 ≠ 0 ∨ (z e).2 ≠ 0) ∧
                            ((classifier.remainingControlEdges controlEdges).erase e).card <
                              (classifier.remainingControlEdges controlEdges).card) := by
    by_cases hclosed : Theorem49BoundaryRootSynthesis emb C₀
    · exact Or.inl hclosed
    · exact Or.inr
        (data.forcedEdge_and_extensionFinsetWitness_coordinateSignal_with_worklistProgress_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
          emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
          hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue hclosed)

/-- Compact named-payload form of the one-step CAP5 coordinate-signal runner. -/
theorem theorem49BoundaryRootSynthesis_or_forcedEdge_and_extensionCoordinateSignalWithProgress_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v))
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitnessRed :
      ∀ e : G.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue) :
    Theorem49BoundaryRootSynthesis emb C₀ ∨
      (∃ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) ∧
        data.ExtensionCoordinateSignalWithProgress emb p0Inside p4Inside side classifier
          controlEdges := by
  by_cases hclosed : Theorem49BoundaryRootSynthesis emb C₀
  · exact Or.inl hclosed
  · exact Or.inr
      (data.forcedEdge_and_extensionCoordinateSignalWithProgress_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
        emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue hclosed)

/--
Runner-level algebraic handoff for one finite CAP5 step.  If the current step does not close
Theorem 4.9, then under red/blue probes for the next extension edges it exposes a nonzero
selected-boundary-zero chain with a nonzero family pairing.
-/
theorem theorem49BoundaryRootSynthesis_or_forcedEdge_and_boundaryZeroChain_familyPairing_ne_zero_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v))
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hwitnessRed :
      ∀ e : G.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        e ∈ classifier.emittedFinset →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue)
    (hwitnessExtensionRed :
      ∀ e : G.edgeSet,
        e ∈ classifier.crossingExtensionFinset controlEdges ∨
            e ∈ classifier.noncrossingExtensionFinset controlEdges →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessExtensionBlue :
      ∀ e : G.edgeSet,
        e ∈ classifier.crossingExtensionFinset controlEdges ∨
            e ∈ classifier.noncrossingExtensionFinset controlEdges →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue) :
    Theorem49BoundaryRootSynthesis emb C₀ ∨
      (∃ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) ∧
        ∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              (∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) ∧
                ∃ i : κ,
                  chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  rcases data.theorem49BoundaryRootSynthesis_or_forcedEdge_and_extensionCoordinateSignalWithProgress_of_finsetControl
      emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue with
    hclosed | hnext
  · exact Or.inl hclosed
  · rcases hnext with ⟨hforced, hsignal⟩
    rcases data.exists_boundaryZeroChain_familyPairing_ne_zero_of_extensionCoordinateSignalWithProgress
        family hsignal hwitnessExtensionRed hwitnessExtensionBlue with
      ⟨z, hzBoundary, hzNonzero, hvanish, i, hpair⟩
    exact Or.inr ⟨hforced, z, hzBoundary, hzNonzero, hvanish, i, hpair⟩

end CAP5TransportedEdgeComponentCoverCore

end Mettapedia.GraphTheory.FourColor
