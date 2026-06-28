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
Mixed report boundary for finite CAP5 calibration runs.  A realized-separator row already
refutes cyclic five-edge-connectivity, while a forced-counterexample row emits a canonical
one-edge `𝔽₂` detector.  This packages the hold/fail boundary mined by finite generator runs
without assuming the unresolved planar separator step.
-/
theorem mixed_boundary_indicatorDetector_payload_of_mem_realizedSeparatorLatents_of_mem_forcedCounterexampleLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {realizedLatent forcedLatent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hrealized : realizedLatent ∈ report.realizedSeparatorLatents)
    (hforced : forcedLatent ∈ report.forcedCounterexampleLatents) :
    ¬ CyclicallyFiveEdgeConnected G ∧
      ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
        e ∉ (report.node forcedLatent).candidate.edgeSupport ∧
          side u ∧ ¬ side v ∧
            p.edges = [(e : Sym2 V)] ∧
              (∀ i : Fin 5,
                i ∈ (report.node forcedLatent).candidate.portalCandidate.portalSet →
                  ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
                EdgeCrossesVertexSide G side e ∧
                  Curriculum.pathXor (edgeIndicatorWeight e) p.edges = 1 := by
  exact
    ⟨report.not_cyclicallyFiveEdgeConnected_of_mem_realizedSeparatorLatents
        hrealized,
      report.exists_oneEdge_forcedCounterexampleWalk_indicatorDetector_payload_of_mem_forcedCounterexampleLatents
        hforced⟩

/--
Existential mixed-boundary form for finite generator sweeps.  If a report has at least one
realized-separator row and at least one forced-counterexample row, then the sample is already a
cyclic-five-connectivity refutation and it exposes a forced row with a canonical one-edge `𝔽₂`
detector payload.
-/
theorem mixed_boundary_indicatorDetector_payload_of_exists_bins
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hrealized : ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ report.realizedSeparatorLatents)
    (hforced : ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ report.forcedCounterexampleLatents) :
    ¬ CyclicallyFiveEdgeConnected G ∧
      ∃ forcedLatent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        forcedLatent ∈ report.forcedCounterexampleLatents ∧
          ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
            e ∉ (report.node forcedLatent).candidate.edgeSupport ∧
              side u ∧ ¬ side v ∧
                p.edges = [(e : Sym2 V)] ∧
                  (∀ i : Fin 5,
                    i ∈ (report.node forcedLatent).candidate.portalCandidate.portalSet →
                      ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
                    EdgeCrossesVertexSide G side e ∧
                      Curriculum.pathXor (edgeIndicatorWeight e) p.edges = 1 := by
  rcases hrealized with ⟨realizedLatent, hrealizedMem⟩
  rcases hforced with ⟨forcedLatent, hforcedMem⟩
  rcases report.mixed_boundary_indicatorDetector_payload_of_mem_realizedSeparatorLatents_of_mem_forcedCounterexampleLatents
      hrealizedMem hforcedMem with
    ⟨hnotCyclic, hpayload⟩
  exact ⟨hnotCyclic, forcedLatent, hforcedMem, hpayload⟩

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

/--
Named one-edge indicator payload emitted by the finite CAP5 forced-edge generator.  This is the
generator-facing forced bin: it records the latent, realized orientation, emitted forced edge,
outside-support fact, side-crossing one-edge walk, portal avoidance, and the canonical `𝔽₂`
edge-indicator detector firing with value `1`.
-/
def ForcedEdgeIndicatorPathXorDetectorPayload
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool) (side : V → Prop) : Prop :=
  ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
    latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
      latent.p0Inside = p0Inside ∧
        latent.p4Inside = p4Inside ∧
          data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
            ∃ e : G.edgeSet, ∃ u v : V, ∃ p : G.Walk u v,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                e ∉ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
                  boundaryEdge side latent).candidate.edgeSupport ∧
                  side u ∧ ¬ side v ∧
                    p.edges = [(e : Sym2 V)] ∧
                      (∀ i : Fin 5,
                        i ∈ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
                          boundaryEdge side latent).candidate.portalCandidate.portalSet →
                          ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
                        EdgeCrossesVertexSide G side e ∧
                          Curriculum.pathXor (edgeIndicatorWeight e) p.edges = 1

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

/--
Data-level forced-generator payload.  Every edge emitted by
`EnumeratedExceptionalAnnulusForcedEdge` carries the same one-edge indicator detector as the
node-level forced bin: the edge is outside the generated support, crosses the selected side, and
the finite `𝔽₂` edge-indicator path-xor fires on the emitted one-edge walk.
-/
theorem enumeratedExceptionalAnnulusForcedEdge_indicatorDetector_payload
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : V → Prop} {e : G.edgeSet}
    (h : data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) :
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        latent.p0Inside = p0Inside ∧
          latent.p4Inside = p4Inside ∧
            data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
              ∃ u v : V, ∃ p : G.Walk u v,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                  e ∉ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
                    boundaryEdge side latent).candidate.edgeSupport ∧
                    side u ∧ ¬ side v ∧
                      p.edges = [(e : Sym2 V)] ∧
                        (∀ i : Fin 5,
                          i ∈ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
                            boundaryEdge side latent).candidate.portalCandidate.portalSet →
                            ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
                          EdgeCrossesVertexSide G side e ∧
                            Curriculum.pathXor (edgeIndicatorWeight e) p.edges = 1 := by
  rcases h with ⟨latent, hmem, hp0, hp4, horientation, hforced⟩
  let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
    CAP5ExceptionalAnnulusGeneratorReport.latentNode boundaryEdge side latent
  have hforcedNode : node.ForcedCounterexampleEdge e := by
    simpa [node, CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hforced
  rcases node.forcedCounterexampleEdge_indicatorDetector_payload hforcedNode with
    ⟨u, v, p, heOutside, hu, hv, hpEdges, havoid, hcross, hxor⟩
  have hedge :
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e :=
    ⟨latent, hmem, hp0, hp4, horientation, by
      simpa [node, CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hforcedNode⟩
  refine
    ⟨latent, hmem, hp0, hp4, horientation, u, v, p, hedge, ?_, ?_, ?_,
      hpEdges, ?_, ?_, hxor⟩
  · simpa [node] using heOutside
  · simpa [node, CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hu
  · simpa [node, CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hv
  · simpa [node] using havoid
  · simpa [node, CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hcross

/-- Package a data-level enumerated forced edge as the named one-edge indicator payload. -/
theorem forcedEdgeIndicatorPathXorDetectorPayload_of_enumeratedExceptionalAnnulusForcedEdge
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : V → Prop} {e : G.edgeSet}
    (h : data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) :
    data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side := by
  rcases data.enumeratedExceptionalAnnulusForcedEdge_indicatorDetector_payload h with
    ⟨latent, hmem, hp0, hp4, horientation, u, v, p, hedge, heOutside, hu, hv,
      hpEdges, havoid, hcross, hxor⟩
  exact
    ⟨latent, hmem, hp0, hp4, horientation, e, u, v, p, hedge, heOutside, hu, hv,
      hpEdges, havoid, hcross, hxor⟩

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

/--
Named payload for a CAP5 extension signal whose witness edge is also available in an explicit
residual worklist state.  This is the scheduler-facing version of
`ExtensionCoordinateSignalWithProgress`: it records that processing the same crossing or
noncrossing extension edge strictly decreases the residual measure.
-/
def ExtensionCoordinateSignalWithResidualProgress
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges processed : Finset G.edgeSet) : Prop :=
  (∃ z : G.edgeSet → Color,
    z ∈ planarBoundaryZeroSubmodule emb ∧
      z ≠ 0 ∧
        (∀ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
            z e = 0) ∧
          ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
            e ∈ classifier.crossingExtensionFinset controlEdges ∧
              e ∈ classifier.remainingControlEdges controlEdges ∧
                e ∈ classifier.residualRemainingControlEdges controlEdges processed ∧
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
                                (classifier.residualRemainingControlEdges controlEdges
                                    (insert e processed)).card <
                                  (classifier.residualRemainingControlEdges controlEdges
                                    processed).card ∧
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
                e ∈ classifier.remainingControlEdges controlEdges ∧
                  e ∈ classifier.residualRemainingControlEdges controlEdges processed ∧
                    ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                      z e ≠ 0 ∧ ¬ EdgeCrossesVertexSide G side e ∧
                        ((z e).1 ≠ 0 ∨ (z e).2 ≠ 0) ∧
                          (classifier.residualRemainingControlEdges controlEdges
                              (insert e processed)).card <
                            (classifier.residualRemainingControlEdges controlEdges
                              processed).card ∧
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

/-- Forget the residual-state data from a scheduler-facing CAP5 extension signal. -/
theorem extensionCoordinateSignalWithProgress_of_extensionCoordinateSignalWithResidualProgress
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    {classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side}
    {controlEdges processed : Finset G.edgeSet}
    (hsignal :
      data.ExtensionCoordinateSignalWithResidualProgress emb p0Inside p4Inside side
        classifier controlEdges processed) :
    data.ExtensionCoordinateSignalWithProgress emb p0Inside p4Inside side classifier
      controlEdges := by
  rcases hsignal with hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, _heRemaining,
        _heResidual, hePredicateOutside, hze, hcross, hsideu, hsidev, hpEdges,
        havoid, hcoordinate, _hresidualProgress, hprogress⟩
    exact Or.inl
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, hePredicateOutside,
        hze, hcross, hsideu, hsidev, hpEdges, havoid, hcoordinate, hprogress⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, _heRemaining, _heResidual,
        hePredicateOutside, hze, hnotCross, hcoordinate, _hresidualProgress,
        hprogress⟩
    exact Or.inr
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze,
        hnotCross, hcoordinate, hprogress⟩

/--
Promote an ordinary worklist-progress extension signal to a residual-state signal whenever every
remaining control edge is still unprocessed.
-/
theorem extensionCoordinateSignalWithResidualProgress_of_extensionCoordinateSignalWithProgress
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    {classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side}
    {controlEdges processed : Finset G.edgeSet}
    (hsignal :
      data.ExtensionCoordinateSignalWithProgress emb p0Inside p4Inside side classifier
        controlEdges)
    (hnotProcessed :
      ∀ e ∈ classifier.remainingControlEdges controlEdges, e ∉ processed) :
    data.ExtensionCoordinateSignalWithResidualProgress emb p0Inside p4Inside side
      classifier controlEdges processed := by
  rcases hsignal with hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, hePredicateOutside,
        hze, hcross, hsideu, hsidev, hpEdges, havoid, hcoordinate, hprogress⟩
    have heRemaining : e ∈ classifier.remainingControlEdges controlEdges := by
      rw [← classifier.crossingExtensionFinset_union_noncrossingExtensionFinset_eq_remainingControlEdges
        controlEdges]
      exact Finset.mem_union.2 (Or.inl heBin)
    have heResidual :
        e ∈ classifier.residualRemainingControlEdges controlEdges processed :=
      classifier.mem_residualRemainingControlEdges_of_mem_remainingControlEdges_of_not_mem_processed
        controlEdges processed heRemaining (hnotProcessed e heRemaining)
    have hresidualProgress :
        (classifier.residualRemainingControlEdges controlEdges (insert e processed)).card <
          (classifier.residualRemainingControlEdges controlEdges processed).card :=
      classifier.card_residualRemainingControlEdges_insert_lt_of_mem_remainingControlEdges_of_not_mem_processed
        controlEdges processed heRemaining (hnotProcessed e heRemaining)
    exact Or.inl
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, heRemaining,
        heResidual, hePredicateOutside, hze, hcross, hsideu, hsidev, hpEdges,
        havoid, hcoordinate, hresidualProgress, hprogress⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze,
        hnotCross, hcoordinate, hprogress⟩
    have heRemaining : e ∈ classifier.remainingControlEdges controlEdges := by
      rw [← classifier.crossingExtensionFinset_union_noncrossingExtensionFinset_eq_remainingControlEdges
        controlEdges]
      exact Finset.mem_union.2 (Or.inr heBin)
    have heResidual :
        e ∈ classifier.residualRemainingControlEdges controlEdges processed :=
      classifier.mem_residualRemainingControlEdges_of_mem_remainingControlEdges_of_not_mem_processed
        controlEdges processed heRemaining (hnotProcessed e heRemaining)
    have hresidualProgress :
        (classifier.residualRemainingControlEdges controlEdges (insert e processed)).card <
          (classifier.residualRemainingControlEdges controlEdges processed).card :=
      classifier.card_residualRemainingControlEdges_insert_lt_of_mem_remainingControlEdges_of_not_mem_processed
        controlEdges processed heRemaining (hnotProcessed e heRemaining)
    exact Or.inr
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, heRemaining, heResidual,
        hePredicateOutside, hze, hnotCross, hcoordinate, hresidualProgress,
        hprogress⟩

/--
Positive processed-edge zero invariant for an immutable Boolean classifier.  If every processed
edge has already been emitted by the classifier, then emitted-edge vanishing immediately forces
all processed edges to vanish.
-/
theorem processedControl_of_subset_emittedFinset
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    {processed : Finset G.edgeSet}
    (hprocessedSubset : processed ⊆ classifier.emittedFinset) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        ∀ e ∈ processed, z e = 0 := by
  intro z _hzBoundary hvanishEmitted e heProcessed
  exact hvanishEmitted e (hprocessedSubset heProcessed)

/--
Finite scheduler subset update.  If every currently processed edge is already emitted by the
immutable classifier, then after selecting a residual edge `e`, the updated processed set is a
subset of the one-edge emitted/control update.
-/
theorem processedSubset_insert_emittedFinset
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    {processed : Finset G.edgeSet} {e : G.edgeSet}
    (hprocessedSubset : processed ⊆ classifier.emittedFinset) :
    insert e processed ⊆ insert e classifier.emittedFinset := by
  intro f hf
  rcases Finset.mem_insert.1 hf with hfe | hfProcessed
  · exact Finset.mem_insert.2 (Or.inl hfe)
  · exact Finset.mem_insert_of_mem (hprocessedSubset hfProcessed)

/--
Processed-control insertion decomposes into the old processed-control invariant plus a genuine
edge-control proof for the inserted edge.  This is the scheduler invariant that must be supplied
by a real classifier/control update before recording a residual edge as processed.
-/
theorem processedControl_insert_iff_processedControl_and_edgeControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (processed : Finset G.edgeSet) (e : G.edgeSet) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ f ∈ classifier.emittedFinset, z f = 0) →
        ∀ f ∈ insert e processed, z f = 0) ↔
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ f ∈ classifier.emittedFinset, z f = 0) →
          ∀ f ∈ processed, z f = 0) ∧
        (∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule emb →
          (∀ f ∈ classifier.emittedFinset, z f = 0) →
            z e = 0) := by
  constructor
  · intro hinsert
    constructor
    · intro z hzBoundary hvanishEmitted f hfProcessed
      exact hinsert hzBoundary hvanishEmitted f (Finset.mem_insert_of_mem hfProcessed)
    · intro z hzBoundary hvanishEmitted
      exact hinsert hzBoundary hvanishEmitted e (Finset.mem_insert_self e processed)
  · rintro ⟨hprocessed, hedge⟩ z hzBoundary hvanishEmitted f hfInsert
    rcases Finset.mem_insert.1 hfInsert with hfe | hfProcessed
    · subst hfe
      exact hedge hzBoundary hvanishEmitted
    · exact hprocessed hzBoundary hvanishEmitted f hfProcessed

/--
Forward form of `processedControl_insert_iff_processedControl_and_edgeControl`: once the current
processed set is controlled and a new edge is genuinely controlled by emitted-edge vanishing, the
inserted processed set is controlled.
-/
theorem processedControl_insert_of_processedControl_of_edgeControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    {processed : Finset G.edgeSet} {e : G.edgeSet}
    (hprocessed :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ f ∈ classifier.emittedFinset, z f = 0) →
          ∀ f ∈ processed, z f = 0)
    (hedge :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ f ∈ classifier.emittedFinset, z f = 0) →
          z e = 0) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ f ∈ classifier.emittedFinset, z f = 0) →
        ∀ f ∈ insert e processed, z f = 0 :=
  (data.processedControl_insert_iff_processedControl_and_edgeControl
    classifier processed e).2 ⟨hprocessed, hedge⟩

/--
Processed-control monotonicity in the emitted/control premise.  If a later emitted/control set
contains every edge emitted by the immutable classifier, then any processed set controlled from
the classifier output is still controlled from the later set.
-/
theorem processedControl_mono_emittedFinset
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    {processed emitted : Finset G.edgeSet}
    (hsubset : classifier.emittedFinset ⊆ emitted)
    (hprocessed :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ f ∈ classifier.emittedFinset, z f = 0) →
          ∀ f ∈ processed, z f = 0) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ f ∈ emitted, z f = 0) →
        ∀ f ∈ processed, z f = 0 := by
  intro z hzBoundary hvanishEmitted f hfProcessed
  exact hprocessed hzBoundary
    (by
      intro g hg
      exact hvanishEmitted g (hsubset hg))
    f hfProcessed

/--
Positive scheduler update: if the later emitted/control premise contains the immutable classifier
output and also contains the edge to be recorded as processed, then insertion of that edge is a
valid processed-control update.
-/
theorem processedControl_insert_of_processedControl_of_emittedSuperset_mem
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    {processed emitted : Finset G.edgeSet} {e : G.edgeSet}
    (hsubset : classifier.emittedFinset ⊆ emitted)
    (heEmitted : e ∈ emitted)
    (hprocessed :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ f ∈ classifier.emittedFinset, z f = 0) →
          ∀ f ∈ processed, z f = 0) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ f ∈ emitted, z f = 0) →
        ∀ f ∈ insert e processed, z f = 0 := by
  intro z hzBoundary hvanishEmitted f hfInsert
  rcases Finset.mem_insert.1 hfInsert with hfe | hfProcessed
  · simpa [hfe] using hvanishEmitted e heEmitted
  · exact hprocessed hzBoundary
      (by
        intro g hg
        exact hvanishEmitted g (hsubset hg))
      f hfProcessed

/--
Concrete one-edge update form.  Adding the selected edge to the emitted/control premise supplies
the missing edge-control proof needed to insert that edge into the processed set.
-/
theorem processedControl_insert_of_processedControl_of_insert_emittedFinset
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    {processed : Finset G.edgeSet} {e : G.edgeSet}
    (hprocessed :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ f ∈ classifier.emittedFinset, z f = 0) →
          ∀ f ∈ processed, z f = 0) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ f ∈ insert e classifier.emittedFinset, z f = 0) →
        ∀ f ∈ insert e processed, z f = 0 :=
  data.processedControl_insert_of_processedControl_of_emittedSuperset_mem
    classifier (Finset.subset_insert e classifier.emittedFinset)
    (Finset.mem_insert_self e classifier.emittedFinset) hprocessed

/--
A residual signal exposes an edge that is not controlled by vanishing on the immutable classifier
output.  This is the exact missing premise in
`processedControl_insert_of_processedControl_of_edgeControl`.
-/
theorem exists_residualEdge_not_edgeControl_of_extensionCoordinateSignalWithResidualProgress
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    {classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side}
    {controlEdges processed : Finset G.edgeSet}
    (hsignal :
      data.ExtensionCoordinateSignalWithResidualProgress emb p0Inside p4Inside side
        classifier controlEdges processed) :
    ∃ e : G.edgeSet,
      e ∈ classifier.residualRemainingControlEdges controlEdges processed ∧
        ¬ (∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule emb →
          (∀ f ∈ classifier.emittedFinset, z f = 0) →
            z e = 0) := by
  rcases hsignal with hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, _hzNonzero, hvanishForced, _u, _v, e, _p, _heBin,
        _heRemaining, heResidual, _hePredicateOutside, hze, _hcross, _hsideu,
        _hsidev, _hpEdges, _havoid, _hcoordinate, _hresidualProgress,
        _hprogress⟩
    refine ⟨e, heResidual, ?_⟩
    intro hedgeControl
    have hvanishEmitted : ∀ f ∈ classifier.emittedFinset, z f = 0 := by
      intro f hf
      exact hvanishForced f ((classifier.emittedFinset_spec f).1 hf)
    exact hze (hedgeControl hzBoundary hvanishEmitted)
  · rcases hnoncrossing with
      ⟨z, hzBoundary, _hzNonzero, hvanishForced, e, _heBin, _heRemaining,
        heResidual, _hePredicateOutside, hze, _hnotCross, _hcoordinate,
        _hresidualProgress, _hprogress⟩
    refine ⟨e, heResidual, ?_⟩
    intro hedgeControl
    have hvanishEmitted : ∀ f ∈ classifier.emittedFinset, z f = 0 := by
      intro f hf
      exact hvanishForced f ((classifier.emittedFinset_spec f).1 hf)
    exact hze (hedgeControl hzBoundary hvanishEmitted)

/--
Positive/negative scheduler transition for a residual signal.  The residual edge is not controlled
by the immutable classifier output, but if the next emitted/control premise explicitly contains
that edge, then recording it as processed is a valid processed-control update.
-/
theorem exists_residualEdge_not_edgeControl_and_processedControl_insert_of_insert_emittedFinset_of_extensionCoordinateSignalWithResidualProgress
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    {classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side}
    {controlEdges processed : Finset G.edgeSet}
    (hsignal :
      data.ExtensionCoordinateSignalWithResidualProgress emb p0Inside p4Inside side
        classifier controlEdges processed)
    (hprocessedControl :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ f ∈ classifier.emittedFinset, z f = 0) →
          ∀ f ∈ processed, z f = 0) :
    ∃ e : G.edgeSet,
      e ∈ classifier.residualRemainingControlEdges controlEdges processed ∧
        ¬ (∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule emb →
          (∀ f ∈ classifier.emittedFinset, z f = 0) →
            z e = 0) ∧
          ∀ ⦃z : G.edgeSet → Color⦄,
            z ∈ planarBoundaryZeroSubmodule emb →
            (∀ f ∈ insert e classifier.emittedFinset, z f = 0) →
              ∀ f ∈ insert e processed, z f = 0 := by
  rcases data.exists_residualEdge_not_edgeControl_of_extensionCoordinateSignalWithResidualProgress
      hsignal with
    ⟨e, heResidual, hnotEdgeControl⟩
  exact
    ⟨e, heResidual, hnotEdgeControl,
      data.processedControl_insert_of_processedControl_of_insert_emittedFinset
        classifier hprocessedControl⟩

/--
Scheduler transition for a residual signal.  The same selected residual edge witnesses immutable
classifier edge-control failure, supports the one-edge emitted/control update needed to mark it
processed, and strictly decreases the explicit residual worklist after insertion.
-/
theorem exists_residualEdge_not_edgeControl_and_processedControl_insert_of_insert_emittedFinset_and_residualProgress_of_extensionCoordinateSignalWithResidualProgress
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    {classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side}
    {controlEdges processed : Finset G.edgeSet}
    (hsignal :
      data.ExtensionCoordinateSignalWithResidualProgress emb p0Inside p4Inside side
        classifier controlEdges processed)
    (hprocessedControl :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ f ∈ classifier.emittedFinset, z f = 0) →
          ∀ f ∈ processed, z f = 0) :
    ∃ e : G.edgeSet,
      e ∈ classifier.residualRemainingControlEdges controlEdges processed ∧
        ¬ (∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule emb →
          (∀ f ∈ classifier.emittedFinset, z f = 0) →
            z e = 0) ∧
          (∀ ⦃z : G.edgeSet → Color⦄,
            z ∈ planarBoundaryZeroSubmodule emb →
            (∀ f ∈ insert e classifier.emittedFinset, z f = 0) →
              ∀ f ∈ insert e processed, z f = 0) ∧
            (classifier.residualRemainingControlEdges controlEdges (insert e processed)).card <
              (classifier.residualRemainingControlEdges controlEdges processed).card := by
  rcases hsignal with hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, _hzNonzero, hvanishForced, _u, _v, e, _p, _heBin,
        _heRemaining, heResidual, _hePredicateOutside, hze, _hcross, _hsideu,
        _hsidev, _hpEdges, _havoid, _hcoordinate, hresidualProgress,
        _hprogress⟩
    have hnotEdgeControl :
        ¬ (∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule emb →
          (∀ f ∈ classifier.emittedFinset, z f = 0) →
            z e = 0) := by
      intro hedgeControl
      have hvanishEmitted : ∀ f ∈ classifier.emittedFinset, z f = 0 := by
        intro f hf
        exact hvanishForced f ((classifier.emittedFinset_spec f).1 hf)
      exact hze (hedgeControl hzBoundary hvanishEmitted)
    exact
      ⟨e, heResidual, hnotEdgeControl,
        data.processedControl_insert_of_processedControl_of_insert_emittedFinset
          classifier hprocessedControl,
        hresidualProgress⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, _hzNonzero, hvanishForced, e, _heBin, _heRemaining,
        heResidual, _hePredicateOutside, hze, _hnotCross, _hcoordinate,
        hresidualProgress, _hprogress⟩
    have hnotEdgeControl :
        ¬ (∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule emb →
          (∀ f ∈ classifier.emittedFinset, z f = 0) →
            z e = 0) := by
      intro hedgeControl
      have hvanishEmitted : ∀ f ∈ classifier.emittedFinset, z f = 0 := by
        intro f hf
        exact hvanishForced f ((classifier.emittedFinset_spec f).1 hf)
      exact hze (hedgeControl hzBoundary hvanishEmitted)
    exact
      ⟨e, heResidual, hnotEdgeControl,
        data.processedControl_insert_of_processedControl_of_insert_emittedFinset
          classifier hprocessedControl,
        hresidualProgress⟩

/--
Concrete finite-state scheduler transition for a residual signal.  From the finite invariant
`processed ⊆ classifier.emittedFinset`, the selected residual edge both preserves the subset
invariant after the one-edge emitted/control update and supplies the processed-control update
needed for the next residual state.
-/
theorem exists_residualEdge_not_edgeControl_and_processedSubset_insert_and_processedControl_insert_of_insert_emittedFinset_and_residualProgress_of_extensionCoordinateSignalWithResidualProgress
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    {classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side}
    {controlEdges processed : Finset G.edgeSet}
    (hsignal :
      data.ExtensionCoordinateSignalWithResidualProgress emb p0Inside p4Inside side
        classifier controlEdges processed)
    (hprocessedSubset : processed ⊆ classifier.emittedFinset) :
    ∃ e : G.edgeSet,
      e ∈ classifier.residualRemainingControlEdges controlEdges processed ∧
        ¬ (∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule emb →
          (∀ f ∈ classifier.emittedFinset, z f = 0) →
            z e = 0) ∧
          insert e processed ⊆ insert e classifier.emittedFinset ∧
            (∀ ⦃z : G.edgeSet → Color⦄,
              z ∈ planarBoundaryZeroSubmodule emb →
              (∀ f ∈ insert e classifier.emittedFinset, z f = 0) →
                ∀ f ∈ insert e processed, z f = 0) ∧
              (classifier.residualRemainingControlEdges controlEdges (insert e processed)).card <
                (classifier.residualRemainingControlEdges controlEdges processed).card := by
  have hprocessedControl :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ f ∈ classifier.emittedFinset, z f = 0) →
          ∀ f ∈ processed, z f = 0 :=
    data.processedControl_of_subset_emittedFinset (emb := emb) classifier hprocessedSubset
  rcases
      data.exists_residualEdge_not_edgeControl_and_processedControl_insert_of_insert_emittedFinset_and_residualProgress_of_extensionCoordinateSignalWithResidualProgress
        hsignal hprocessedControl with
    ⟨e, heResidual, hnotEdgeControl, hprocessedInsert, hresidualProgress⟩
  exact
    ⟨e, heResidual, hnotEdgeControl,
      data.processedSubset_insert_emittedFinset classifier hprocessedSubset,
      hprocessedInsert, hresidualProgress⟩

/--
Negative processed-edge zero invariant for residual iteration.  A residual signal exposes a
boundary-zero chain that vanishes on the immutable classifier output but is nonzero on the chosen
residual edge.  Therefore the same classifier cannot justify marking that edge as processed
without adding new emitted/control information.
-/
theorem exists_residualEdge_not_processedControl_insert_of_extensionCoordinateSignalWithResidualProgress
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    {classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side}
    {controlEdges processed : Finset G.edgeSet}
    (hsignal :
      data.ExtensionCoordinateSignalWithResidualProgress emb p0Inside p4Inside side
        classifier controlEdges processed) :
    ∃ e : G.edgeSet,
      e ∈ classifier.residualRemainingControlEdges controlEdges processed ∧
        ¬ (∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule emb →
          (∀ f ∈ classifier.emittedFinset, z f = 0) →
            ∀ f ∈ insert e processed, z f = 0) := by
  rcases hsignal with hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, _hzNonzero, hvanishForced, _u, _v, e, _p, _heBin,
        _heRemaining, heResidual, _hePredicateOutside, hze, _hcross, _hsideu,
        _hsidev, _hpEdges, _havoid, _hcoordinate, _hresidualProgress,
        _hprogress⟩
    refine ⟨e, heResidual, ?_⟩
    intro hprocessedControl
    have hvanishEmitted : ∀ f ∈ classifier.emittedFinset, z f = 0 := by
      intro f hf
      exact hvanishForced f ((classifier.emittedFinset_spec f).1 hf)
    exact hze
      (hprocessedControl hzBoundary hvanishEmitted e
        (Finset.mem_insert_self e processed))
  · rcases hnoncrossing with
      ⟨z, hzBoundary, _hzNonzero, hvanishForced, e, _heBin, _heRemaining,
        heResidual, _hePredicateOutside, hze, _hnotCross, _hcoordinate,
        _hresidualProgress, _hprogress⟩
    refine ⟨e, heResidual, ?_⟩
    intro hprocessedControl
    have hvanishEmitted : ∀ f ∈ classifier.emittedFinset, z f = 0 := by
      intro f hf
      exact hvanishForced f ((classifier.emittedFinset_spec f).1 hf)
    exact hze
      (hprocessedControl hzBoundary hvanishEmitted e
        (Finset.mem_insert_self e processed))

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
Worklist-progress algebraic handoff retaining the next extension edge.  This is the edge-level
payload consumed by a detector iteration: the returned boundary-zero chain is nonzero on a
crossing or noncrossing extension edge, the edge is not already enumerated by the CAP5 forced
classifier, and erasing it strictly decreases the finite remaining-control worklist.
-/
theorem exists_boundaryZeroChain_extensionControlEdge_familyPairing_ne_zero_of_extensionCoordinateSignalWithProgress
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
            ∃ e : G.edgeSet,
              (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                  z e ≠ 0 ∧
                    ((classifier.remainingControlEdges controlEdges).erase e).card <
                      (classifier.remainingControlEdges controlEdges).card ∧
                      ∃ i : κ,
                        chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  rcases hsignal with hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, _u, _v, e, _p, heBin,
        hePredicateOutside, hze, _hcross, _hsideu, _hsidev, _hpEdges, _havoid,
        _hcoordinate, hprogress⟩
    rcases exists_familyPairing_ne_zero_of_redBlueSingleCoordinateWitness
        family e hze (hwitnessRed e (Or.inl heBin)) (hwitnessBlue e (Or.inl heBin)) with
      ⟨i, hpair⟩
    exact
      ⟨z, hzBoundary, hzNonzero, hvanish, e, Or.inl heBin, hePredicateOutside, hze,
        hprogress, i, hpair⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze,
        _hnotCross, _hcoordinate, hprogress⟩
    rcases exists_familyPairing_ne_zero_of_redBlueSingleCoordinateWitness
        family e hze (hwitnessRed e (Or.inr heBin)) (hwitnessBlue e (Or.inr heBin)) with
      ⟨i, hpair⟩
    exact
      ⟨z, hzBoundary, hzNonzero, hvanish, e, Or.inr heBin, hePredicateOutside, hze,
        hprogress, i, hpair⟩

/--
Canonical-family version of the CAP5 extension-signal handoff.  The red/blue family is built
from membership certificates on the finite remaining-control worklist, and the returned edge is
kept both in its crossing/noncrossing extension bin and in the named remaining-control worklist.
-/
theorem exists_boundaryZeroChain_extensionControlEdge_canonicalFamilyPairing_ne_zero_of_extensionCoordinateSignalWithProgress
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    {classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side}
    {controlEdges : Finset G.edgeSet}
    (hsignal :
      data.ExtensionCoordinateSignalWithProgress emb p0Inside p4Inside side classifier
        controlEdges)
    (hred :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          (∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0) ∧
            ∃ e : G.edgeSet,
              (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                e ∈ classifier.remainingControlEdges controlEdges ∧
                  ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                    z e ≠ 0 ∧
                      ((classifier.remainingControlEdges controlEdges).erase e).card <
                        (classifier.remainingControlEdges controlEdges).card ∧
                        ∃ i :
                          ({e : G.edgeSet //
                            e ∈ classifier.remainingControlEdges controlEdges} × Bool),
                          chainDotBilinForm G.edgeSet
                              (redBlueSingleCoordinateFamily
                                (classifier.remainingControlEdges controlEdges) hred hblue i :
                                G.edgeSet → Color) z ≠ 0 := by
  have hwitnessRed :
      ∀ e : G.edgeSet,
        e ∈ classifier.crossingExtensionFinset controlEdges ∨
            e ∈ classifier.noncrossingExtensionFinset controlEdges →
          ∃ i :
            ({e : G.edgeSet // e ∈ classifier.remainingControlEdges controlEdges} × Bool),
            ((redBlueSingleCoordinateFamily
                (classifier.remainingControlEdges controlEdges) hred hblue i :
                projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red := by
    intro e heExtension
    have heRemaining : e ∈ classifier.remainingControlEdges controlEdges := by
      rw [← classifier.crossingExtensionFinset_union_noncrossingExtensionFinset_eq_remainingControlEdges
        controlEdges]
      exact Finset.mem_union.2 heExtension
    exact
      (redBlueSingleCoordinateFamily_witnessRed
        (classifier.remainingControlEdges controlEdges) hred hblue) e heRemaining
  have hwitnessBlue :
      ∀ e : G.edgeSet,
        e ∈ classifier.crossingExtensionFinset controlEdges ∨
            e ∈ classifier.noncrossingExtensionFinset controlEdges →
          ∃ i :
            ({e : G.edgeSet // e ∈ classifier.remainingControlEdges controlEdges} × Bool),
            ((redBlueSingleCoordinateFamily
                (classifier.remainingControlEdges controlEdges) hred hblue i :
                projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue := by
    intro e heExtension
    have heRemaining : e ∈ classifier.remainingControlEdges controlEdges := by
      rw [← classifier.crossingExtensionFinset_union_noncrossingExtensionFinset_eq_remainingControlEdges
        controlEdges]
      exact Finset.mem_union.2 heExtension
    exact
      (redBlueSingleCoordinateFamily_witnessBlue
        (classifier.remainingControlEdges controlEdges) hred hblue) e heRemaining
  rcases data.exists_boundaryZeroChain_extensionControlEdge_familyPairing_ne_zero_of_extensionCoordinateSignalWithProgress
      (redBlueSingleCoordinateFamily
        (classifier.remainingControlEdges controlEdges) hred hblue)
      hsignal hwitnessRed hwitnessBlue with
    ⟨z, hzBoundary, hzNonzero, hvanish, e, heExtension, hePredicateOutside, hze,
      hprogress, i, hpair⟩
  have heRemaining : e ∈ classifier.remainingControlEdges controlEdges := by
    rw [← classifier.crossingExtensionFinset_union_noncrossingExtensionFinset_eq_remainingControlEdges
      controlEdges]
    exact Finset.mem_union.2 heExtension
  exact
    ⟨z, hzBoundary, hzNonzero, hvanish, e, heExtension, heRemaining,
      hePredicateOutside, hze, hprogress, i, hpair⟩

/--
Residual-state version of the canonical CAP5 extension-signal handoff.  When the detector's
extension edge has not already been recorded in an explicit processed set, the same edge gives a
strict decrease of the explicit residual worklist.
-/
theorem exists_boundaryZeroChain_extensionControlEdge_canonicalFamilyPairing_ne_zero_and_residualProgress_of_extensionCoordinateSignalWithProgress
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    {classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side}
    {controlEdges processed : Finset G.edgeSet}
    (hsignal :
      data.ExtensionCoordinateSignalWithProgress emb p0Inside p4Inside side classifier
        controlEdges)
    (hred :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnotProcessed :
      ∀ e ∈ classifier.remainingControlEdges controlEdges, e ∉ processed) :
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          (∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0) ∧
            ∃ e : G.edgeSet,
              (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                e ∈ classifier.remainingControlEdges controlEdges ∧
                  e ∈ classifier.residualRemainingControlEdges controlEdges processed ∧
                    ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                      z e ≠ 0 ∧
                        (classifier.residualRemainingControlEdges controlEdges
                            (insert e processed)).card <
                          (classifier.residualRemainingControlEdges controlEdges processed).card ∧
                        ((classifier.remainingControlEdges controlEdges).erase e).card <
                          (classifier.remainingControlEdges controlEdges).card ∧
                          ∃ i :
                            ({e : G.edgeSet //
                              e ∈ classifier.remainingControlEdges controlEdges} × Bool),
                            chainDotBilinForm G.edgeSet
                                (redBlueSingleCoordinateFamily
                                  (classifier.remainingControlEdges controlEdges) hred hblue i :
                                  G.edgeSet → Color) z ≠ 0 := by
  rcases data.exists_boundaryZeroChain_extensionControlEdge_canonicalFamilyPairing_ne_zero_of_extensionCoordinateSignalWithProgress
      hsignal hred hblue with
    ⟨z, hzBoundary, hzNonzero, hvanish, e, heExtension, heRemaining,
      hePredicateOutside, hze, hprogress, i, hpair⟩
  have heResidual :
      e ∈ classifier.residualRemainingControlEdges controlEdges processed :=
    classifier.mem_residualRemainingControlEdges_of_mem_remainingControlEdges_of_not_mem_processed
      controlEdges processed heRemaining (hnotProcessed e heRemaining)
  have hresidualProgress :
      (classifier.residualRemainingControlEdges controlEdges (insert e processed)).card <
        (classifier.residualRemainingControlEdges controlEdges processed).card :=
    classifier.card_residualRemainingControlEdges_insert_lt_of_mem_remainingControlEdges_of_not_mem_processed
      controlEdges processed heRemaining (hnotProcessed e heRemaining)
  exact
    ⟨z, hzBoundary, hzNonzero, hvanish, e, heExtension, heRemaining, heResidual,
      hePredicateOutside, hze, hresidualProgress, hprogress, i, hpair⟩

/--
Trace-indexed residual-state version of the canonical CAP5 extension-signal handoff.  A
residual-aware signal already names an edge in the explicit residual worklist; this theorem also
records that the same edge occurs in the canonical remaining-control trace, so scheduler code can
connect the algebraic detector witness to the finite trace certificate.
-/
theorem exists_boundaryZeroChain_extensionControlTraceEdge_canonicalFamilyPairing_ne_zero_and_residualProgress_of_extensionCoordinateSignalWithResidualProgress
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    {classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side}
    {controlEdges processed : Finset G.edgeSet}
    (hsignal :
      data.ExtensionCoordinateSignalWithResidualProgress emb p0Inside p4Inside side
        classifier controlEdges processed)
    (hred :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          (∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0) ∧
            ∃ e : G.edgeSet,
              (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                e ∈ classifier.remainingControlEdges controlEdges ∧
                  e ∈ classifier.remainingControlEdgeTrace controlEdges ∧
                    e ∈ classifier.residualRemainingControlEdges controlEdges processed ∧
                      ¬ data.EnumeratedExceptionalAnnulusForcedEdge
                        p0Inside p4Inside side e ∧
                        z e ≠ 0 ∧
                          (classifier.residualRemainingControlEdges controlEdges
                              (insert e processed)).card <
                            (classifier.residualRemainingControlEdges controlEdges
                              processed).card ∧
                          ((classifier.remainingControlEdges controlEdges).erase e).card <
                            (classifier.remainingControlEdges controlEdges).card ∧
                            ∃ i :
                              ({e : G.edgeSet //
                                e ∈ classifier.remainingControlEdges controlEdges} × Bool),
                              chainDotBilinForm G.edgeSet
                                  (redBlueSingleCoordinateFamily
                                    (classifier.remainingControlEdges controlEdges) hred hblue i :
                                    G.edgeSet → Color) z ≠ 0 := by
  rcases hsignal with hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, _u, _v, e, _p, heBin, heRemaining,
        heResidual, hePredicateOutside, hze, _hcross, _hsideu, _hsidev, _hpEdges,
        _havoid, _hcoordinate, hresidualProgress, hprogress⟩
    have heTrace : e ∈ classifier.remainingControlEdgeTrace controlEdges :=
      (classifier.mem_remainingControlEdgeTrace_iff controlEdges e).2 heRemaining
    rcases exists_familyPairing_ne_zero_of_redBlueSingleCoordinateWitness
        (redBlueSingleCoordinateFamily
          (classifier.remainingControlEdges controlEdges) hred hblue)
        e hze
        ((redBlueSingleCoordinateFamily_witnessRed
          (classifier.remainingControlEdges controlEdges) hred hblue) e heRemaining)
        ((redBlueSingleCoordinateFamily_witnessBlue
          (classifier.remainingControlEdges controlEdges) hred hblue) e heRemaining) with
      ⟨i, hpair⟩
    exact
      ⟨z, hzBoundary, hzNonzero, hvanish, e, Or.inl heBin, heRemaining, heTrace,
        heResidual, hePredicateOutside, hze, hresidualProgress, hprogress, i, hpair⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, heRemaining, heResidual,
        hePredicateOutside, hze, _hnotCross, _hcoordinate, hresidualProgress,
        hprogress⟩
    have heTrace : e ∈ classifier.remainingControlEdgeTrace controlEdges :=
      (classifier.mem_remainingControlEdgeTrace_iff controlEdges e).2 heRemaining
    rcases exists_familyPairing_ne_zero_of_redBlueSingleCoordinateWitness
        (redBlueSingleCoordinateFamily
          (classifier.remainingControlEdges controlEdges) hred hblue)
        e hze
        ((redBlueSingleCoordinateFamily_witnessRed
          (classifier.remainingControlEdges controlEdges) hred hblue) e heRemaining)
        ((redBlueSingleCoordinateFamily_witnessBlue
          (classifier.remainingControlEdges controlEdges) hred hblue) e heRemaining) with
      ⟨i, hpair⟩
    exact
      ⟨z, hzBoundary, hzNonzero, hvanish, e, Or.inr heBin, heRemaining, heTrace,
        heResidual, hePredicateOutside, hze, hresidualProgress, hprogress, i, hpair⟩

/--
Trace-indexed residual-state handoff for an arbitrary finite generator family.  If the family
supplies red and blue single-coordinate probes for every edge in the classifier's canonical
remaining-control trace, a residual extension signal exposes a traced edge with a nonzero family
pairing and strict residual-worklist progress.
-/
theorem exists_boundaryZeroChain_extensionControlTraceEdge_familyPairing_ne_zero_and_residualProgress_of_extensionCoordinateSignalWithResidualProgress
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    {p0Inside p4Inside : Bool} {side : V → Prop}
    {classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side}
    {controlEdges processed : Finset G.edgeSet}
    (hsignal :
      data.ExtensionCoordinateSignalWithResidualProgress emb p0Inside p4Inside side
        classifier controlEdges processed)
    (hwitnessRed :
      ∀ e : G.edgeSet,
        e ∈ classifier.remainingControlEdgeTrace controlEdges →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        e ∈ classifier.remainingControlEdgeTrace controlEdges →
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
            ∃ e : G.edgeSet,
              (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                e ∈ classifier.remainingControlEdges controlEdges ∧
                  e ∈ classifier.remainingControlEdgeTrace controlEdges ∧
                    e ∈ classifier.residualRemainingControlEdges controlEdges processed ∧
                      ¬ data.EnumeratedExceptionalAnnulusForcedEdge
                        p0Inside p4Inside side e ∧
                        z e ≠ 0 ∧
                          (classifier.residualRemainingControlEdges controlEdges
                              (insert e processed)).card <
                            (classifier.residualRemainingControlEdges controlEdges
                              processed).card ∧
                          ((classifier.remainingControlEdges controlEdges).erase e).card <
                            (classifier.remainingControlEdges controlEdges).card ∧
                            ∃ i : κ,
                              chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  rcases hsignal with hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, _u, _v, e, _p, heBin, heRemaining,
        heResidual, hePredicateOutside, hze, _hcross, _hsideu, _hsidev, _hpEdges,
        _havoid, _hcoordinate, hresidualProgress, hprogress⟩
    have heTrace : e ∈ classifier.remainingControlEdgeTrace controlEdges :=
      (classifier.mem_remainingControlEdgeTrace_iff controlEdges e).2 heRemaining
    rcases exists_familyPairing_ne_zero_of_redBlueSingleCoordinateWitness family e hze
        (hwitnessRed e heTrace) (hwitnessBlue e heTrace) with
      ⟨i, hpair⟩
    exact
      ⟨z, hzBoundary, hzNonzero, hvanish, e, Or.inl heBin, heRemaining, heTrace,
        heResidual, hePredicateOutside, hze, hresidualProgress, hprogress, i, hpair⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, heRemaining, heResidual,
        hePredicateOutside, hze, _hnotCross, _hcoordinate, hresidualProgress,
        hprogress⟩
    have heTrace : e ∈ classifier.remainingControlEdgeTrace controlEdges :=
      (classifier.mem_remainingControlEdgeTrace_iff controlEdges e).2 heRemaining
    rcases exists_familyPairing_ne_zero_of_redBlueSingleCoordinateWitness family e hze
        (hwitnessRed e heTrace) (hwitnessBlue e heTrace) with
      ⟨i, hpair⟩
    exact
      ⟨z, hzBoundary, hzNonzero, hvanish, e, Or.inr heBin, heRemaining, heTrace,
        heResidual, hePredicateOutside, hze, hresidualProgress, hprogress, i, hpair⟩

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
Executable forced-bin checker boundary.  Running the finite CAP5 checker either identifies the
primitive evidence still missing from some latent, or it returns a named forced-edge indicator
payload.  This is the direct hold/partial/forced-counterexample interface for finite
hypothesis-discovery runs: a completed primitive frontier does not merely produce an edge, it
also emits the canonical one-edge `𝔽₂` detector for the algebraic/cocycle lane.
-/
theorem ofDecidableChecks_missing_checker_ingredient_or_forcedEdgeIndicatorPathXorDetectorPayload_of_isExceptional_of_cyclicallyFiveEdgeConnected
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
      data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks boundaryEdge side
  by_cases hmissingEmpty : report.missingCheckerEvidenceLatents = []
  · right
    rcases report.all_checker_evidence_of_missingCheckerEvidenceLatents_eq_nil
        hmissingEmpty with
      ⟨hportal, hcycles⟩
    rcases data.exists_enumeratedExceptionalAnnulusForcedEdge_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
        report p0Inside p4Inside h hcyclic hportal hcycles with
      ⟨e, hedge⟩
    exact
      data.forcedEdgeIndicatorPathXorDetectorPayload_of_enumeratedExceptionalAnnulusForcedEdge
        hedge
  · left
    have hingredient :=
      (report.missingCheckerEvidenceLatents_ne_nil_iff_exists_missing_checker_ingredient).1
        hmissingEmpty
    simpa [report, CAP5ExceptionalAnnulusGeneratorReport.node,
      CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hingredient

/--
Histogram-plus-detector form of the canonical finite-checker boundary.  Under cyclic
five-edge-connectivity, the executable CAP5 checker either returns an enumerated latent with
missing primitive checker evidence, or the run has the complete `(0, 0, 16)` histogram profile
and emits the named one-edge `𝔽₂` detector for the algebraic/cocycle lane.
-/
theorem ofDecidableChecks_missingCheckerEvidence_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_of_isExceptional_of_cyclicallyFiveEdgeConnected
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
    (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).MissingCheckerEvidence) ∨
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).partialLatents.length = 0 ∧
          (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
            boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
        data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks boundaryEdge side
  by_cases hmissingEmpty : report.missingCheckerEvidenceLatents = []
  · right
    rcases report.all_checker_evidence_of_missingCheckerEvidenceLatents_eq_nil
        hmissingEmpty with
      ⟨hportal, hcycles⟩
    have hhist :
        report.realizedSeparatorLatents.length = 0 ∧
          report.partialLatents.length = 0 ∧
            report.forcedCounterexampleLatents.length = 16 :=
      report.histogram_lengths_eq_of_complete_of_cyclicallyFiveEdgeConnected
        hcyclic hportal hcycles
    rcases data.exists_enumeratedExceptionalAnnulusForcedEdge_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
        report p0Inside p4Inside h hcyclic hportal hcycles with
      ⟨e, hedge⟩
    exact
      ⟨by simpa [report] using hhist,
        data.forcedEdgeIndicatorPathXorDetectorPayload_of_enumeratedExceptionalAnnulusForcedEdge
          hedge⟩
  · left
    rcases (report.missingCheckerEvidenceLatents_ne_nil_iff_exists_missingCheckerEvidence).1
        hmissingEmpty with
      ⟨latent, hmem, hmissing⟩
    exact ⟨latent, hmem, by
      simpa [report, CAP5ExceptionalAnnulusGeneratorReport.node,
        CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hmissing⟩

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
Cardinality obstruction for the current CAP5 classifier controls.  If the emitted edge set plus
the selected boundary-zero coordinates has smaller dimension than the ambient edge-chain space,
then the classifier cannot force all selected boundary-zero chains to vanish.
-/
theorem not_classifierControl_of_emittedFinset_card_add_boundary_card_lt
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet) :
    ¬ ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0 :=
  not_forall_eq_zero_on_control_of_planarBoundaryZeroSubmodule_of_control_card_add_boundary_card_lt
    emb classifier.emittedFinset hcard

/--
Lower-bound form of the classifier-control obstruction.  Any CAP5 classifier whose emitted
edges already control all selected boundary-zero chains must emit enough coordinates to cover the
ambient edge-chain dimension after the selected boundary-zero coordinates are added.
-/
theorem edge_card_le_emittedFinset_card_add_boundary_card_of_classifierControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0) :
    Fintype.card G.edgeSet ≤
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} := by
  by_contra hnotLowerBound
  exact
    (data.not_classifierControl_of_emittedFinset_card_add_boundary_card_lt
      emb p0Inside p4Inside side classifier (Nat.lt_of_not_ge hnotLowerBound))
      hcontrol

/--
Kirchhoff-target cardinality obstruction for the current CAP5 classifier controls.  If the
emitted edge set plus selected-boundary coordinates plus selected Kirchhoff vertex equations is
still below the ambient edge-chain dimension, then the classifier cannot control the
boundary-zero Kirchhoff target.
-/
theorem not_classifierKirchhoffControl_of_emittedFinset_card_add_boundary_card_add_vertex_card_lt
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard :
      classifier.emittedFinset.card +
          Fintype.card {e : G.edgeSet //
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} +
        Fintype.card {v : V // v ∈ vertices} <
        Fintype.card G.edgeSet) :
    ¬ ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0 :=
  not_forall_eq_zero_on_control_of_theorem49BoundaryZeroKirchhoffSubspace_of_card_sum_lt
    emb vertices classifier.emittedFinset hcard

/--
Lower-bound form of the Kirchhoff-target classifier obstruction.  Any CAP5 classifier whose
emitted edges already control the boundary-zero Kirchhoff target must meet the ambient
dimension bound after adding boundary coordinates and the chosen Kirchhoff vertex equations.
-/
theorem edge_card_le_emittedFinset_card_add_boundary_card_add_vertex_card_of_classifierKirchhoffControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0) :
    Fintype.card G.edgeSet ≤
      classifier.emittedFinset.card +
          Fintype.card {e : G.edgeSet //
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} +
        Fintype.card {v : V // v ∈ vertices} := by
  by_contra hnotLowerBound
  exact
    (data.not_classifierKirchhoffControl_of_emittedFinset_card_add_boundary_card_add_vertex_card_lt
      emb vertices p0Inside p4Inside side classifier (Nat.lt_of_not_ge hnotLowerBound))
      hcontrol

/-- Finite-coordinate version of predicate control for the boundary-zero Kirchhoff target.  A
finite edge set controls the target exactly when every nonzero target chain is nonzero on at
least one edge of that set. -/
theorem theorem49BoundaryZeroKirchhoffSubspace_finsetControls_iff_forall_nonzero_exists_mem_nonzero
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (controlEdges : Finset G.edgeSet) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
      (∀ e ∈ controlEdges, z e = 0) →
        z = 0) ↔
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
      z ≠ 0 →
        ∃ e : G.edgeSet, e ∈ controlEdges ∧ z e ≠ 0) := by
  constructor
  · intro hcontrol z hz hzNonzero
    by_contra hno
    apply hzNonzero
    apply hcontrol hz
    intro e he
    by_contra hze
    exact hno ⟨e, he, hze⟩
  · intro hwitness z hz hvanish
    by_contra hzNonzero
    rcases hwitness hz hzNonzero with ⟨e, he, hze⟩
    exact hze (hvanish e he)

/-- Failure certificate for a finite Kirchhoff-target control check.  If vanishing on the finite
control set does not force a boundary-zero Kirchhoff chain to vanish, then there is a concrete
nonzero target chain invisible on all controlling coordinates. -/
theorem not_theorem49BoundaryZeroKirchhoffSubspace_finsetControls_iff_exists_nonzero_vanishes_on_finset
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (controlEdges : Finset G.edgeSet) :
    (¬ ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
      (∀ e ∈ controlEdges, z e = 0) →
        z = 0) ↔
    ∃ z : G.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices ∧
        z ≠ 0 ∧
          ∀ e ∈ controlEdges, z e = 0 := by
  constructor
  · intro hnot
    by_contra hno
    apply hnot
    intro z hz hvanish
    by_contra hzNonzero
    exact hno ⟨z, hz, hzNonzero, hvanish⟩
  · rintro ⟨z, hz, hzNonzero, hvanish⟩ hcontrol
    exact hzNonzero (hcontrol hz hvanish)

/--
Forced-edge coverage controls the boundary-zero Kirchhoff target.  This is the target-subspace
version of the ordinary boundary-zero coverage handoff: every forced edge reported by CAP5 is
also present in the classifier's emitted finite set.
-/
theorem enumeratedExceptionalAnnulusForcedEdgeClassifierKirchhoffControl_of_forcedEdgeKirchhoffCoverage
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0 := by
  intro z hz hvanish
  by_contra hzNonzero
  rcases hcoverage hz hzNonzero with ⟨e, heForced, hze⟩
  exact hze (hvanish e ((classifier.emittedFinset_spec e).2 heForced))

/-- Exact generic CAP5 detector contract for the Kirchhoff target.  Coverage by the enumerated
forced-edge predicate is equivalent to finite control of the boundary-zero Kirchhoff target by
the classifier's emitted edge set. -/
theorem forcedEdgeKirchhoffCoverage_iff_enumeratedExceptionalAnnulusForcedEdgeClassifierKirchhoffControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
      z ≠ 0 →
        ∃ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) ↔
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0) := by
  constructor
  · exact
      data.enumeratedExceptionalAnnulusForcedEdgeClassifierKirchhoffControl_of_forcedEdgeKirchhoffCoverage
        emb vertices classifier
  · intro hcontrol z hz hzNonzero
    have hwitness :=
      (theorem49BoundaryZeroKirchhoffSubspace_finsetControls_iff_forall_nonzero_exists_mem_nonzero
        emb vertices classifier.emittedFinset).1 hcontrol
    rcases hwitness hz hzNonzero with ⟨e, heEmitted, hze⟩
    exact ⟨e, (classifier.emittedFinset_spec e).1 heEmitted, hze⟩

/-- Exact no-evader form of CAP5 forced-edge coverage for the boundary-zero Kirchhoff target.
The classifier controls the target iff there is no nonzero target chain vanishing on every
enumerated CAP5 forced edge. -/
theorem forcedEdgeKirchhoffCoverage_iff_no_kirchhoffEvader
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (p0Inside p4Inside : Bool) (side : V → Prop) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
      z ≠ 0 →
        ∃ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) ↔
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0 := by
  constructor
  · intro hcoverage hevader
    rcases hevader with ⟨z, hz, hzNonzero, hvanish⟩
    rcases hcoverage hz hzNonzero with ⟨e, hedge, hze⟩
    exact hze (hvanish e hedge)
  · intro hnoEvader z hz hzNonzero
    by_contra hnoWitness
    exact hnoEvader ⟨z, hz, hzNonzero, by
      intro e hedge
      by_contra hze
      exact hnoWitness ⟨e, hedge, hze⟩⟩

/-- Route-facing specialization of the target no-evader contract to the theorem-4.9 carrier
`W0(H)`.  This is the exact F2 oracle statement for the current boundary-root target. -/
theorem forcedEdgeBoundaryTargetCoverage_iff_no_targetEvader
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ Theorem49BoundaryTarget emb →
      z ≠ 0 →
        ∃ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) ↔
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ Theorem49BoundaryTarget emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0 := by
  change
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (Theorem49BoundaryVertices emb) →
      z ≠ 0 →
        ∃ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) ↔
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (Theorem49BoundaryVertices emb) ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0
  exact data.forcedEdgeKirchhoffCoverage_iff_no_kirchhoffEvader
    emb (Theorem49BoundaryVertices emb) p0Inside p4Inside side

/--
Exact classifier-control no-evader contract for the boundary-zero Kirchhoff target.  The CAP5
classifier controls the target subspace precisely when no nonzero target chain can vanish on
every enumerated forced edge.
-/
theorem enumeratedExceptionalAnnulusForcedEdgeClassifierKirchhoffControl_iff_no_kirchhoffEvader
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0) ↔
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0 := by
  constructor
  · intro hcontrol
    exact
      (data.forcedEdgeKirchhoffCoverage_iff_no_kirchhoffEvader
        emb vertices p0Inside p4Inside side).1
        ((data.forcedEdgeKirchhoffCoverage_iff_enumeratedExceptionalAnnulusForcedEdgeClassifierKirchhoffControl
          emb vertices classifier).2 hcontrol)
  · intro hnoEvader
    exact
      (data.forcedEdgeKirchhoffCoverage_iff_enumeratedExceptionalAnnulusForcedEdgeClassifierKirchhoffControl
        emb vertices classifier).1
        ((data.forcedEdgeKirchhoffCoverage_iff_no_kirchhoffEvader
          emb vertices p0Inside p4Inside side).2 hnoEvader)

/--
Route-facing no-evader contract for the theorem-4.9 carrier `W0(H)`.  The emitted CAP5
classifier coordinates control the boundary-root target exactly when no nonzero target chain
evades every enumerated forced edge.
-/
theorem theorem49BoundaryTargetClassifierControl_iff_no_targetEvader
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ Theorem49BoundaryTarget emb →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0) ↔
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ Theorem49BoundaryTarget emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0 := by
  change
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (Theorem49BoundaryVertices emb) →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0) ↔
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb (Theorem49BoundaryVertices emb) ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0
  exact
    data.enumeratedExceptionalAnnulusForcedEdgeClassifierKirchhoffControl_iff_no_kirchhoffEvader
      emb (Theorem49BoundaryVertices emb) p0Inside p4Inside side classifier

/--
Route-facing no-evader contract for the full selected-boundary-zero carrier.  The emitted CAP5
classifier coordinates control every selected-boundary-zero chain exactly when no nonzero
selected-boundary-zero chain evades all enumerated forced edges.
-/
theorem enumeratedExceptionalAnnulusForcedEdgeClassifierBoundaryZeroControl_iff_no_boundaryZeroEvader
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0) ↔
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0 := by
  simpa using
    (data.enumeratedExceptionalAnnulusForcedEdgeClassifierControl_iff_no_boundaryZeroChainObstruction
      (emb := emb) classifier)

/--
Target-level dimension fork.  If the emitted CAP5 classifier is too small to meet the
boundary-zero plus theorem-4.9 Kirchhoff target dimension bound, the algebraic failure is a
genuine nonzero `W0(H)` evader for the enumerated forced edges.
-/
theorem exists_theorem49BoundaryTargetEvader_of_emittedFinset_card_add_boundary_card_add_theorem49BoundaryVertices_card_lt
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard :
      classifier.emittedFinset.card +
          Fintype.card {e : G.edgeSet //
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} +
        Fintype.card {v : V // v ∈ Theorem49BoundaryVertices emb} <
        Fintype.card G.edgeSet) :
    ∃ z : G.edgeSet → Color,
      z ∈ Theorem49BoundaryTarget emb ∧
        z ≠ 0 ∧
          ∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0 := by
  by_contra hnoEvader
  have hcontrolTarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0 :=
    (data.theorem49BoundaryTargetClassifierControl_iff_no_targetEvader
      emb p0Inside p4Inside side classifier).2 hnoEvader
  exact
    (data.not_classifierKirchhoffControl_of_emittedFinset_card_add_boundary_card_add_vertex_card_lt
      emb (Theorem49BoundaryVertices emb) p0Inside p4Inside side classifier hcard)
      (by
        intro z hz hvanish
        exact hcontrolTarget
          (by simpa [Theorem49BoundaryTarget, Theorem49BoundaryVertices] using hz)
          hvanish)

/--
No-evader dimension lower bound for the theorem-4.9 target.  Any CAP5 classifier with no
nonzero `W0(H)` evader must emit enough coordinates to meet the boundary-zero plus target
Kirchhoff dimension bound.
-/
theorem edge_card_le_emittedFinset_card_add_boundary_card_add_theorem49BoundaryVertices_card_of_no_targetEvader
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hnoEvader :
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ Theorem49BoundaryTarget emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) :
    Fintype.card G.edgeSet ≤
      classifier.emittedFinset.card +
          Fintype.card {e : G.edgeSet //
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} +
        Fintype.card {v : V // v ∈ Theorem49BoundaryVertices emb} := by
  have hcontrolTarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0 :=
    (data.theorem49BoundaryTargetClassifierControl_iff_no_targetEvader
      emb p0Inside p4Inside side classifier).2 hnoEvader
  exact
    data.edge_card_le_emittedFinset_card_add_boundary_card_add_vertex_card_of_classifierKirchhoffControl
      emb (Theorem49BoundaryVertices emb) p0Inside p4Inside side classifier
      (by
        intro z hz hvanish
        exact hcontrolTarget
          (by simpa [Theorem49BoundaryTarget, Theorem49BoundaryVertices] using hz)
          hvanish)

/--
Coverage lower bound for the Kirchhoff target.  If the enumerated CAP5 forced-edge predicate
meets every nonzero boundary-zero Kirchhoff chain, then the emitted classifier must satisfy the
target-space dimension inequality.
-/
theorem edge_card_le_emittedFinset_card_add_boundary_card_add_vertex_card_of_forcedEdgeKirchhoffCoverage
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    Fintype.card G.edgeSet ≤
      classifier.emittedFinset.card +
          Fintype.card {e : G.edgeSet //
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} +
        Fintype.card {v : V // v ∈ vertices} :=
  data.edge_card_le_emittedFinset_card_add_boundary_card_add_vertex_card_of_classifierKirchhoffControl
    emb vertices p0Inside p4Inside side classifier
    (data.enumeratedExceptionalAnnulusForcedEdgeClassifierKirchhoffControl_of_forcedEdgeKirchhoffCoverage
      emb vertices classifier hcoverage)

/--
Fixed-point lower bound for a Kirchhoff-target worklist.  If a finite control set controls the
boundary-zero Kirchhoff target and all of its edges have already been emitted, then the emitted
classifier satisfies the same target-space dimension inequality.
-/
theorem edge_card_le_emittedFinset_card_add_boundary_card_add_vertex_card_of_finsetKirchhoffControl_of_controlEdges_subset_emittedFinset
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hsubsetEdges : controlEdges ⊆ classifier.emittedFinset) :
    Fintype.card G.edgeSet ≤
      classifier.emittedFinset.card +
          Fintype.card {e : G.edgeSet //
            e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} +
        Fintype.card {v : V // v ∈ vertices} :=
  data.edge_card_le_emittedFinset_card_add_boundary_card_add_vertex_card_of_classifierKirchhoffControl
    emb vertices p0Inside p4Inside side classifier
    (by
      intro z hz hvanishEmitted
      exact hcontrol hz (by
        intro e heControl
        exact hvanishEmitted e (hsubsetEdges heControl)))

/-- Kirchhoff-target falsification payload for the emitted CAP5 forced-edge predicate.  If the
classifier output does not control the chosen boundary-zero Kirchhoff target, then there is a
concrete nonzero target chain invisible to every enumerated forced edge. -/
theorem exists_boundaryZeroKirchhoffChain_vanishingOnEnumeratedExceptionalAnnulusForcedEdges_of_not_classifierKirchhoffControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G) (vertices : Finset V)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hnotControl :
      ¬ ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0) :
    ∃ z : G.edgeSet → Color,
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb vertices ∧
        z ≠ 0 ∧
          ∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0 := by
  rcases
      (not_theorem49BoundaryZeroKirchhoffSubspace_finsetControls_iff_exists_nonzero_vanishes_on_finset
        emb vertices classifier.emittedFinset).1 hnotControl with
    ⟨z, hz, hzNonzero, hvanish⟩
  exact ⟨z, hz, hzNonzero, by
    intro e hedge
    exact hvanish e ((classifier.emittedFinset_spec e).2 hedge)⟩

/--
Fixed-point lower bound for an implementation worklist.  If a finite control set controls all
selected boundary-zero chains and the classifier has already emitted every edge in that worklist,
then the emitted classifier must meet the same dimension lower bound.
-/
theorem edge_card_le_emittedFinset_card_add_boundary_card_of_finsetControl_of_controlEdges_subset_emittedFinset
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hsubsetEdges : controlEdges ⊆ classifier.emittedFinset) :
    Fintype.card G.edgeSet ≤
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} :=
  data.edge_card_le_emittedFinset_card_add_boundary_card_of_classifierControl
    emb p0Inside p4Inside side classifier
    (data.enumeratedExceptionalAnnulusForcedEdgeClassifierControl_of_finsetControl_of_controlEdges_subset_emittedFinset
      emb p0Inside p4Inside side classifier controlEdges hcontrol hsubsetEdges)

/--
Empty-worklist cardinality invariant.  If every edge in a later finite control set has already
been emitted by the classifier, then filtering the emitted set back to that control set contains
at least all control coordinates.  This is the finite bookkeeping fact behind shell-level
interior-control lower bounds for saturated CAP5 worklists.
-/
theorem controlEdges_card_le_emittedFinset_filter_controlEdges_card_of_remainingControlEdges_eq_empty
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hremainingEmpty : classifier.remainingControlEdges controlEdges = ∅) :
    controlEdges.card ≤
      (classifier.emittedFinset.filter fun e => e ∈ controlEdges).card := by
  classical
  have hsubsetEdges : controlEdges ⊆ classifier.emittedFinset := by
    intro e heControl
    by_contra heNotEmitted
    have hmemRemaining : e ∈ classifier.remainingControlEdges controlEdges :=
      (classifier.mem_remainingControlEdges_iff controlEdges e).2
        ⟨heControl, heNotEmitted⟩
    rw [hremainingEmpty] at hmemRemaining
    simp at hmemRemaining
  exact Finset.card_le_card (by
    intro e heControl
    exact Finset.mem_filter.2 ⟨hsubsetEdges heControl, heControl⟩)

/--
Interior-support specialization of the empty-worklist invariant.  A saturated CAP5 runner over
the canonical interior support has emitted at least all interior-support coordinates when viewed
through the emitted-set interior filter.
-/
theorem interiorEdgeSupport_card_le_emittedFinset_filter_interiorEdgeSupport_card_of_remainingInteriorEdgeSupportEdges_eq_empty
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hremainingEmpty :
      classifier.remainingControlEdges (interiorEdgeSupport emb.faceBoundary emb.faces) = ∅) :
    (interiorEdgeSupport emb.faceBoundary emb.faces).card ≤
      (classifier.emittedFinset.filter fun e =>
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces).card :=
  controlEdges_card_le_emittedFinset_filter_controlEdges_card_of_remainingControlEdges_eq_empty
    classifier (interiorEdgeSupport emb.faceBoundary emb.faces) hremainingEmpty

/--
No fixed point below the boundary-zero dimension threshold.  If a later finite worklist controls
all selected boundary-zero chains while the emitted classifier is still too small, then that
worklist contains an edge outside the emitted set.
-/
theorem not_controlEdges_subset_emittedFinset_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0) :
    ¬ controlEdges ⊆ classifier.emittedFinset := by
  intro hsubsetEdges
  exact
    (data.not_classifierControl_of_emittedFinset_card_add_boundary_card_lt
      emb p0Inside p4Inside side classifier hcard)
      (data.enumeratedExceptionalAnnulusForcedEdgeClassifierControl_of_finsetControl_of_controlEdges_subset_emittedFinset
        emb p0Inside p4Inside side classifier controlEdges hcontrol hsubsetEdges)

/--
Named remaining-worklist form of the same fixed-point obstruction.  If a controlling finite
worklist exists while the emitted classifier is still below the boundary-zero dimension threshold,
then at least one control edge remains outside the emitted set.
-/
theorem remainingControlEdges_nonempty_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0) :
    (classifier.remainingControlEdges controlEdges).Nonempty := by
  classical
  have hnotSubset :
      ¬ controlEdges ⊆ classifier.emittedFinset :=
    data.not_controlEdges_subset_emittedFinset_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb p0Inside p4Inside side classifier controlEdges hcard hcontrol
  by_contra hremainingEmpty
  have hsubsetEdges : controlEdges ⊆ classifier.emittedFinset := by
    intro e heControl
    by_contra heNotEmitted
    exact hremainingEmpty
      ⟨e, (classifier.mem_remainingControlEdges_iff controlEdges e).2
        ⟨heControl, heNotEmitted⟩⟩
  exact hnotSubset hsubsetEdges

/--
Cardinality form of the remaining-worklist obstruction.  A too-small emitted classifier with a
successful controlling finite worklist has a strictly positive remaining-control measure, so a
finite generator can choose a genuine next edge.
-/
theorem remainingControlEdges_card_pos_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0) :
    0 < (classifier.remainingControlEdges controlEdges).card :=
  Finset.card_pos.2
    (data.remainingControlEdges_nonempty_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb p0Inside p4Inside side classifier controlEdges hcard hcontrol)

/--
Loop-facing remaining-edge form of the cardinality obstruction.  A too-small emitted classifier
with a later controlling finite worklist yields a concrete unprocessed control edge whose erasure
strictly decreases the named `remainingControlEdges` measure.
-/
theorem exists_remainingControlEdge_with_card_erase_lt_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0) :
    ∃ e : G.edgeSet,
      e ∈ classifier.remainingControlEdges controlEdges ∧
        ((classifier.remainingControlEdges controlEdges).erase e).card <
          (classifier.remainingControlEdges controlEdges).card := by
  rcases data.remainingControlEdges_nonempty_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb p0Inside p4Inside side classifier controlEdges hcard hcontrol with
    ⟨e, he⟩
  exact ⟨e, he, classifier.card_erase_remainingControlEdges_lt_of_mem controlEdges he⟩

/--
Cardinality-driven finite-worklist progress.  A controlling finite worklist cannot have both
extension bins empty while the emitted classifier remains below the boundary-zero dimension
threshold.
-/
theorem crossingExtensionFinset_nonempty_or_noncrossingExtensionFinset_nonempty_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0) :
    (classifier.crossingExtensionFinset controlEdges).Nonempty ∨
      (classifier.noncrossingExtensionFinset controlEdges).Nonempty :=
  data.crossingExtensionFinset_nonempty_or_noncrossingExtensionFinset_nonempty_of_not_classifierControl_of_finsetControl
    emb p0Inside p4Inside side classifier controlEdges
    (data.not_classifierControl_of_emittedFinset_card_add_boundary_card_lt
      emb p0Inside p4Inside side classifier hcard)
    hcontrol

/--
Loop-facing extension-bin form of the cardinality obstruction.  The same dimension gap exposes a
next crossing or noncrossing extension edge, already packaged with the strict decrease of the
finite `remainingControlEdges` measure.
-/
theorem crossingExtensionEdge_or_noncrossingExtensionEdge_with_card_erase_lt_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0) :
    (∃ e : G.edgeSet,
      e ∈ classifier.crossingExtensionFinset controlEdges ∧
        ((classifier.remainingControlEdges controlEdges).erase e).card <
          (classifier.remainingControlEdges controlEdges).card) ∨
      ∃ e : G.edgeSet,
        e ∈ classifier.noncrossingExtensionFinset controlEdges ∧
          ((classifier.remainingControlEdges controlEdges).erase e).card <
            (classifier.remainingControlEdges controlEdges).card := by
  rcases data.crossingExtensionFinset_nonempty_or_noncrossingExtensionFinset_nonempty_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb p0Inside p4Inside side classifier controlEdges hcard hcontrol with
    hcrossing | hnoncrossing
  · rcases hcrossing with ⟨e, he⟩
    exact Or.inl
      ⟨e, he,
        classifier.card_erase_remainingControlEdges_lt_of_mem_crossingExtensionFinset
          controlEdges he⟩
  · rcases hnoncrossing with ⟨e, he⟩
    exact Or.inr
      ⟨e, he,
        classifier.card_erase_remainingControlEdges_lt_of_mem_noncrossingExtensionFinset
          controlEdges he⟩

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
Worklist-progress form of the failed finite-control coordinate signal.  A failed classifier
control check against a later finite control set returns a crossing or noncrossing extension
coordinate, and membership in either extension bin already proves strict decrease after erasing
that edge from `remainingControlEdges`.
-/
theorem extensionCoordinateSignalWithProgress_of_not_classifierControl_of_finsetControl
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
    data.ExtensionCoordinateSignalWithProgress emb p0Inside p4Inside side classifier
      controlEdges := by
  rcases data.extensionCoordinateSignal_of_not_classifierControl_of_finsetControl
      emb p0Inside p4Inside side classifier controlEdges hnotControl hcontrol with
    hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, hePredicateOutside,
        hze, hcross, hsideu, hsidev, hpEdges, havoid, hcoordinate⟩
    exact Or.inl
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, hePredicateOutside,
        hze, hcross, hsideu, hsidev, hpEdges, havoid, hcoordinate,
        classifier.card_erase_remainingControlEdges_lt_of_mem_crossingExtensionFinset
          controlEdges heBin⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze,
        hnotCross, hcoordinate⟩
    exact Or.inr
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze,
        hnotCross, hcoordinate,
        classifier.card_erase_remainingControlEdges_lt_of_mem_noncrossingExtensionFinset
          controlEdges heBin⟩

/--
Residual finite-control coordinate signal.  If the current explicit residual worklist controls the
selected boundary-zero chains while the emitted classifier does not, then the next coordinate
signal can be emitted directly over that residual worklist; the needed freshness hypothesis is
supplied by the residual-worklist algebra.
-/
theorem extensionCoordinateSignalWithResidualProgress_of_not_classifierControl_of_residualFinsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges processed : Finset G.edgeSet)
    (hnotControl :
      ¬ ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)
    (hresidualControl :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.residualRemainingControlEdges controlEdges processed, z e = 0) →
          z = 0) :
    data.ExtensionCoordinateSignalWithResidualProgress emb p0Inside p4Inside side classifier
      (classifier.residualRemainingControlEdges controlEdges processed) processed := by
  have hsignal :
      data.ExtensionCoordinateSignalWithProgress emb p0Inside p4Inside side classifier
        (classifier.residualRemainingControlEdges controlEdges processed) :=
    data.extensionCoordinateSignalWithProgress_of_not_classifierControl_of_finsetControl
      emb p0Inside p4Inside side classifier
      (classifier.residualRemainingControlEdges controlEdges processed) hnotControl
      hresidualControl
  exact
    data.extensionCoordinateSignalWithResidualProgress_of_extensionCoordinateSignalWithProgress
      hsignal
      (fun e he =>
        classifier.not_mem_processed_of_mem_remainingControlEdges_residualRemainingControlEdges
          controlEdges processed he)

/--
Residual coordinate signal from an original finite-control proof plus a processed-edge zero
invariant.  This is the iteration-facing form: the later control set may still be the original
finite worklist, but the obstruction edge is forced into the explicit residual worklist because
processed edges are already controlled whenever the emitted classifier edges are zero.
-/
theorem extensionCoordinateSignalWithResidualProgress_of_not_classifierControl_of_finsetControl_of_processedControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges processed : Finset G.edgeSet)
    (hnotControl :
      ¬ ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hprocessedControl :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          ∀ e ∈ processed, z e = 0) :
    data.ExtensionCoordinateSignalWithResidualProgress emb p0Inside p4Inside side classifier
      controlEdges processed := by
  rcases data.exists_boundaryZeroChain_and_residualExtensionFinsetWitness_crossing_or_noncrossing_of_not_classifierControl_of_finsetControl_of_processedControl
      emb p0Inside p4Inside side classifier controlEdges processed hnotControl hcontrol
      hprocessedControl with
    hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, heResidual,
        hePredicateOutside, hze, hcross, hsideu, hsidev, hpEdges, havoid⟩
    have heRemaining : e ∈ classifier.remainingControlEdges controlEdges :=
      (classifier.mem_residualRemainingControlEdges_iff controlEdges processed e).1
        heResidual |>.1
    have hcoordinate :
        Curriculum.pathXor (edgeColorFirstCoordinateWeight z) p.edges ≠ 0 ∨
          Curriculum.pathXor (edgeColorSecondCoordinateWeight z) p.edges ≠ 0 :=
      edgeColorCoordinatePathXor_ne_zero_of_walk_edges_singleton_of_color_ne_zero
        z hpEdges hze
    exact Or.inl
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, heRemaining,
        heResidual, hePredicateOutside, hze, hcross, hsideu, hsidev, hpEdges,
        havoid, hcoordinate,
        classifier.card_residualRemainingControlEdges_insert_lt_of_mem controlEdges
          processed heResidual,
        classifier.card_erase_remainingControlEdges_lt_of_mem controlEdges heRemaining⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, heResidual,
        hePredicateOutside, hze, hnotCross⟩
    have heRemaining : e ∈ classifier.remainingControlEdges controlEdges :=
      (classifier.mem_residualRemainingControlEdges_iff controlEdges processed e).1
        heResidual |>.1
    have hcoordinate : (z e).1 ≠ 0 ∨ (z e).2 ≠ 0 :=
      (color_ne_zero_iff_fst_or_snd_ne_zero (z e)).1 hze
    exact Or.inr
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, heRemaining, heResidual,
        hePredicateOutside, hze, hnotCross, hcoordinate,
        classifier.card_residualRemainingControlEdges_insert_lt_of_mem controlEdges
          processed heResidual,
        classifier.card_erase_remainingControlEdges_lt_of_mem controlEdges heRemaining⟩

/--
Failed-classifier form of the missing edge-control premise.  If the immutable classifier fails
while a later finite control proof and current processed-control invariant hold, the selected
residual edge is not controlled by vanishing on the immutable classifier output.
-/
theorem exists_residualEdge_not_edgeControl_of_not_classifierControl_of_finsetControl_of_processedControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges processed : Finset G.edgeSet)
    (hnotControl :
      ¬ ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hprocessedControl :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          ∀ e ∈ processed, z e = 0) :
    ∃ e : G.edgeSet,
      e ∈ classifier.residualRemainingControlEdges controlEdges processed ∧
        ¬ (∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule emb →
          (∀ f ∈ classifier.emittedFinset, z f = 0) →
            z e = 0) :=
  data.exists_residualEdge_not_edgeControl_of_extensionCoordinateSignalWithResidualProgress
    (data.extensionCoordinateSignalWithResidualProgress_of_not_classifierControl_of_finsetControl_of_processedControl
      emb p0Inside p4Inside side classifier controlEdges processed hnotControl hcontrol
      hprocessedControl)

/--
Failed-classifier form of the immutable-processed obstruction.  The residual signal produced from
`hnotControl`, a later finite control proof, and the current processed-edge zero invariant names
an edge whose insertion into the same classifier's processed set would make that zero invariant
false.  A scheduler must therefore pair the insertion with new emitted/control information.
-/
theorem exists_residualEdge_not_processedControl_insert_of_not_classifierControl_of_finsetControl_of_processedControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges processed : Finset G.edgeSet)
    (hnotControl :
      ¬ ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hprocessedControl :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          ∀ e ∈ processed, z e = 0) :
    ∃ e : G.edgeSet,
      e ∈ classifier.residualRemainingControlEdges controlEdges processed ∧
        ¬ (∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule emb →
          (∀ f ∈ classifier.emittedFinset, z f = 0) →
            ∀ f ∈ insert e processed, z f = 0) :=
  data.exists_residualEdge_not_processedControl_insert_of_extensionCoordinateSignalWithResidualProgress
    (data.extensionCoordinateSignalWithResidualProgress_of_not_classifierControl_of_finsetControl_of_processedControl
      emb p0Inside p4Inside side classifier controlEdges processed hnotControl hcontrol
      hprocessedControl)

/--
Cardinality-driven named-payload form of the CAP5 extension coordinate signal.  The emitted
classifier controls do not need a separate non-control hypothesis when their coordinate count plus
the selected boundary-zero coordinate count is strictly smaller than the edge-chain space.
-/
theorem extensionCoordinateSignal_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0) :
    data.ExtensionCoordinateSignal emb p0Inside p4Inside side classifier controlEdges :=
  data.extensionCoordinateSignal_of_not_classifierControl_of_finsetControl
    emb p0Inside p4Inside side classifier controlEdges
    (data.not_classifierControl_of_emittedFinset_card_add_boundary_card_lt
      emb p0Inside p4Inside side classifier hcard)
    hcontrol

/--
Cardinality-driven CAP5 extension signal with finite worklist progress.  This is the direct
finite-control runner surface: the strict dimension gap supplies the failed classifier control,
and every returned crossing/noncrossing extension edge erases a remaining control edge.
-/
theorem extensionCoordinateSignalWithProgress_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0) :
    data.ExtensionCoordinateSignalWithProgress emb p0Inside p4Inside side classifier
      controlEdges := by
  rcases data.extensionCoordinateSignal_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb p0Inside p4Inside side classifier controlEdges hcard hcontrol with
    hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, hePredicateOutside,
        hze, hcross, hsideu, hsidev, hpEdges, havoid, hcoordinate⟩
    exact Or.inl
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, hePredicateOutside,
        hze, hcross, hsideu, hsidev, hpEdges, havoid, hcoordinate,
        classifier.card_erase_remainingControlEdges_lt_of_mem_crossingExtensionFinset
          controlEdges heBin⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze,
        hnotCross, hcoordinate⟩
    exact Or.inr
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze,
        hnotCross, hcoordinate,
        classifier.card_erase_remainingControlEdges_lt_of_mem_noncrossingExtensionFinset
          controlEdges heBin⟩

/--
CAP5 finite-control step driven only by the cardinality obstruction.  Under the usual cyclic
exceptional CAP5 hypotheses, a too-small emitted classifier set yields both an emitted forced
edge and a next extension coordinate signal with finite worklist progress.
-/
theorem forcedEdge_and_extensionCoordinateSignalWithProgress_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
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
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0) :
    (∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) ∧
      data.ExtensionCoordinateSignalWithProgress emb p0Inside p4Inside side classifier
        controlEdges := by
  refine ⟨?_, ?_⟩
  · exact
      data.exists_enumeratedExceptionalAnnulusForcedEdge_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
        p0Inside p4Inside h side hcyclic hportal_crosses hcycles
  · exact
      data.extensionCoordinateSignalWithProgress_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
        emb p0Inside p4Inside side classifier controlEdges hcard hcontrol

/--
Interior-support control form of the cardinality-driven CAP5 extension signal.  Vanishing on all
interior-support edges controls every planar-boundary-zero chain, so this discharges the generic
finite-control hypothesis of the runner.
-/
theorem extensionCoordinateSignalWithProgress_of_emittedFinset_card_add_boundary_card_lt_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet) :
    data.ExtensionCoordinateSignalWithProgress emb p0Inside p4Inside side classifier
      (interiorEdgeSupport emb.faceBoundary emb.faces) := by
  refine
    data.extensionCoordinateSignalWithProgress_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb p0Inside p4Inside side classifier
      (interiorEdgeSupport emb.faceBoundary emb.faces) hcard ?_
  intro z hzBoundary hcontrol
  exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    z hzBoundary hcontrol

/--
Interior-support control form of the cardinality-driven CAP5 finite step.  Under the usual cyclic
exceptional hypotheses, a too-small emitted classifier set yields both an emitted forced edge and
the next extension coordinate signal with progress, using all interior-support edges as the later
control set.
-/
theorem forcedEdge_and_extensionCoordinateSignalWithProgress_of_emittedFinset_card_add_boundary_card_lt_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
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
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet) :
    (∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) ∧
      data.ExtensionCoordinateSignalWithProgress emb p0Inside p4Inside side classifier
        (interiorEdgeSupport emb.faceBoundary emb.faces) := by
  refine ⟨?_, ?_⟩
  · exact
      data.exists_enumeratedExceptionalAnnulusForcedEdge_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
        p0Inside p4Inside h side hcyclic hportal_crosses hcycles
  · exact
      data.extensionCoordinateSignalWithProgress_of_emittedFinset_card_add_boundary_card_lt_of_interiorEdgeSupportControl
        emb p0Inside p4Inside side classifier hcard

/--
Interior-support fixed-point close for the CAP5 classifier runner.  If the classifier has no
remaining interior-support control edge, then the existing emitted-edge coordinates already
control every selected-boundary-zero chain, so the boundary-root synthesis follows.
-/
theorem theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierRemainingInteriorEdgeSupportEdgesEmpty
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hremainingEmpty :
      classifier.remainingControlEdges (interiorEdgeSupport emb.faceBoundary emb.faces) = ∅)
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
    Theorem49BoundaryRootSynthesis emb C₀ := by
  refine
    data.theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierRemainingControlEdgesEmpty
      emb C₀ colorings hsubset family p0Inside p4Inside side classifier
      (interiorEdgeSupport emb.faceBoundary emb.faces) ?_ hremainingEmpty hwitnessRed
      hwitnessBlue
  intro z hzBoundary hcontrol
  exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    z hzBoundary hcontrol

/--
Failed-synthesis falsification for an exhausted interior-support worklist.  A CAP5 run using the
interior face-incidence support as its control set cannot stop with no remaining support edge and
still fail Theorem 4.9 synthesis.
-/
theorem false_of_not_theorem49BoundaryRootSynthesis_of_remainingInteriorEdgeSupportEdges_eq_empty
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hremainingEmpty :
      classifier.remainingControlEdges (interiorEdgeSupport emb.faceBoundary emb.faces) = ∅)
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
    False :=
  hnotSynthesis
    (data.theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierRemainingInteriorEdgeSupportEdgesEmpty
      emb C₀ colorings hsubset family p0Inside p4Inside side classifier hremainingEmpty
      hwitnessRed hwitnessBlue)

/--
Interior-support one-step CAP5 runner.  The all-interior support set is a canonical finite
control set for selected-boundary-zero chains, so the runner either closes Theorem 4.9 synthesis
or returns a concrete remaining interior-support edge whose erasure strictly decreases the
worklist.
-/
theorem theorem49BoundaryRootSynthesis_or_exists_remainingInteriorEdgeSupportEdge_with_card_erase_lt
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
      ∃ e : G.edgeSet,
        e ∈ classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
          ((classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
            (classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
  refine
    data.theorem49BoundaryRootSynthesis_or_exists_remainingControlEdge_with_card_erase_lt_of_finsetControl
      emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier (interiorEdgeSupport emb.faceBoundary emb.faces) ?_
      hwitnessRed hwitnessBlue
  intro z hzBoundary hcontrol
  exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    z hzBoundary hcontrol

/--
Strong interior-support one-step CAP5 runner.  The failure branch retains both the CAP5 forced
edge emitted by the exceptional separator generator and a fresh remaining interior-support edge
whose erasure strictly decreases the finite worklist.
-/
theorem theorem49BoundaryRootSynthesis_or_forcedEdge_and_exists_remainingInteriorEdgeSupportEdge_with_card_erase_lt
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
        ∃ e : G.edgeSet,
          e ∈ classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
            ((classifier.remainingControlEdges
                (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
              (classifier.remainingControlEdges
                (interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
  refine
    data.theorem49BoundaryRootSynthesis_or_forcedEdge_and_exists_remainingControlEdge_with_card_erase_lt_of_finsetControl
      emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier (interiorEdgeSupport emb.faceBoundary emb.faces) ?_
      hwitnessRed hwitnessBlue
  intro z hzBoundary hcontrol
  exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    z hzBoundary hcontrol

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
Generator-state form of the one-step CAP5 runner.  If the finite step does not already close
Theorem 4.9, it returns the forced-bin one-edge detector together with the next extension
coordinate signal whose selected edge strictly decreases the finite worklist.  This keeps the
forced histogram/falsification output attached to the actual next generator move, before taking
the further algebraic-family-pairing consequence.
-/
theorem theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionCoordinateSignalWithProgress_of_finsetControl
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
      data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
        data.ExtensionCoordinateSignalWithProgress emb p0Inside p4Inside side classifier
          controlEdges := by
  rcases data.theorem49BoundaryRootSynthesis_or_forcedEdge_and_extensionCoordinateSignalWithProgress_of_finsetControl
      emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue with
    hclosed | hnext
  · exact Or.inl hclosed
  · rcases hnext with ⟨hforced, hsignal⟩
    rcases hforced with ⟨e, hedge⟩
    exact Or.inr
      ⟨data.forcedEdgeIndicatorPathXorDetectorPayload_of_enumeratedExceptionalAnnulusForcedEdge
          hedge,
        hsignal⟩

/--
Executable histogram-to-runner state for the CAP5 generator.  A decidable finite CAP5 sweep
either identifies a latent whose primitive checker evidence is still missing, or else its
complete cyclic-five histogram is `(0, 0, 16)` and the same run reaches the one-step algebraic
runner: Theorem 4.9 synthesis closes, or the forced-bin detector is paired with a next extension
coordinate signal that strictly decreases the finite worklist.
-/
theorem ofDecidableChecks_missingCheckerEvidence_or_histogram_and_theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionCoordinateSignalWithProgress_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).MissingCheckerEvidence) ∨
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).partialLatents.length = 0 ∧
          (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
            boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
        (Theorem49BoundaryRootSynthesis emb C₀ ∨
          data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
            data.ExtensionCoordinateSignalWithProgress emb p0Inside p4Inside side classifier
              controlEdges) := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks boundaryEdge side
  by_cases hmissingEmpty : report.missingCheckerEvidenceLatents = []
  · right
    rcases report.all_checker_evidence_of_missingCheckerEvidenceLatents_eq_nil
        hmissingEmpty with
      ⟨hportal, hsideCycles⟩
    have hhist :
        report.realizedSeparatorLatents.length = 0 ∧
          report.partialLatents.length = 0 ∧
            report.forcedCounterexampleLatents.length = 16 :=
      report.histogram_lengths_eq_of_complete_of_cyclicallyFiveEdgeConnected
        hcyclic hportal hsideCycles
    exact
      ⟨by simpa [report] using hhist,
        data.theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionCoordinateSignalWithProgress_of_finsetControl
          emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic
          hportal_crosses hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue⟩
  · left
    rcases (report.missingCheckerEvidenceLatents_ne_nil_iff_exists_missingCheckerEvidence).1
        hmissingEmpty with
      ⟨latent, hmem, hmissing⟩
    exact ⟨latent, hmem, by
      simpa [report, CAP5ExceptionalAnnulusGeneratorReport.node,
        CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hmissing⟩

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

/--
Runner-level algebraic handoff with the forced-bin detector kept attached.  If the finite CAP5
step does not already close Theorem 4.9, then the run exposes both the named one-edge forced
detector payload and a nonzero selected-boundary-zero chain pairing.  This is the compact
interface between the finite forced-counterexample bin and the surviving algebraic/cocycle lane.
-/
theorem theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_finsetControl
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
      data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
        ∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              (∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) ∧
                ∃ i : κ,
                  chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  rcases data.theorem49BoundaryRootSynthesis_or_forcedEdge_and_boundaryZeroChain_familyPairing_ne_zero_of_finsetControl
      emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue
      hwitnessExtensionRed hwitnessExtensionBlue with
    hclosed | hfallback
  · exact Or.inl hclosed
  · rcases hfallback with
      ⟨hforced, z, hzBoundary, hzNonzero, hvanish, i, hpair⟩
    rcases hforced with ⟨e, hedge⟩
    exact Or.inr
      ⟨data.forcedEdgeIndicatorPathXorDetectorPayload_of_enumeratedExceptionalAnnulusForcedEdge
          hedge,
        z, hzBoundary, hzNonzero, hvanish, i, hpair⟩

/--
Interior-support control version of the runner-level algebraic handoff.  The later finite
control set is the canonical face-incidence interior support, so the failure branch carries the
forced-bin one-edge detector together with a nonzero selected-boundary-zero chain pairing without
requiring a separate finite-control proof.
-/
theorem theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_interiorEdgeSupportControl
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
        e ∈ classifier.crossingExtensionFinset
              (interiorEdgeSupport emb.faceBoundary emb.faces) ∨
            e ∈ classifier.noncrossingExtensionFinset
              (interiorEdgeSupport emb.faceBoundary emb.faces) →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessExtensionBlue :
      ∀ e : G.edgeSet,
        e ∈ classifier.crossingExtensionFinset
              (interiorEdgeSupport emb.faceBoundary emb.faces) ∨
            e ∈ classifier.noncrossingExtensionFinset
              (interiorEdgeSupport emb.faceBoundary emb.faces) →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue) :
    Theorem49BoundaryRootSynthesis emb C₀ ∨
      data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
        ∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              (∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) ∧
                ∃ i : κ,
                  chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  refine
    data.theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_finsetControl
      emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier (interiorEdgeSupport emb.faceBoundary emb.faces) ?_
      hwitnessRed hwitnessBlue hwitnessExtensionRed hwitnessExtensionBlue
  intro z hzBoundary hcontrol
  exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    z hzBoundary hcontrol

/--
Runner-level canonical-family handoff for one CAP5 finite-control step.  The family used to
test already emitted coordinates is built from emitted-edge red/blue membership certificates,
while the failure branch returns the canonical red/blue family over the next remaining-control
worklist together with the concrete extension edge and strict worklist decrease.
-/
theorem theorem49BoundaryRootSynthesis_or_forcedEdge_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    Theorem49BoundaryRootSynthesis emb C₀ ∨
      (∃ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) ∧
        ∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              (∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) ∧
                ∃ e : G.edgeSet,
                  (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                    e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                    e ∈ classifier.remainingControlEdges controlEdges ∧
                      ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                        z e ≠ 0 ∧
                          ((classifier.remainingControlEdges controlEdges).erase e).card <
                            (classifier.remainingControlEdges controlEdges).card ∧
                            ∃ i :
                              ({e : G.edgeSet //
                                e ∈ classifier.remainingControlEdges controlEdges} × Bool),
                              chainDotBilinForm G.edgeSet
                                  (redBlueSingleCoordinateFamily
                                    (classifier.remainingControlEdges controlEdges)
                                    hredRemaining hblueRemaining i :
                                    G.edgeSet → Color) z ≠ 0 := by
  rcases data.theorem49BoundaryRootSynthesis_or_forcedEdge_and_extensionCoordinateSignalWithProgress_of_finsetControl
      emb C₀ colorings hsubset
      (redBlueSingleCoordinateFamily classifier.emittedFinset hredEmitted hblueEmitted)
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles classifier
      controlEdges hcontrol
      (redBlueSingleCoordinateFamily_witnessRed classifier.emittedFinset hredEmitted
        hblueEmitted)
      (redBlueSingleCoordinateFamily_witnessBlue classifier.emittedFinset hredEmitted
        hblueEmitted) with
    hclosed | hnext
  · exact Or.inl hclosed
  · rcases hnext with ⟨hforced, hsignal⟩
    rcases data.exists_boundaryZeroChain_extensionControlEdge_canonicalFamilyPairing_ne_zero_of_extensionCoordinateSignalWithProgress
        hsignal hredRemaining hblueRemaining with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heExtension, heRemaining,
        hePredicateOutside, hze, hprogress, i, hpair⟩
    exact Or.inr
      ⟨hforced, z, hzBoundary, hzNonzero, hvanish, e, heExtension, heRemaining,
        hePredicateOutside, hze, hprogress, i, hpair⟩

/--
Forced-bin detector form of the runner-level canonical-family handoff.  If the CAP5 step does
not close Theorem 4.9, the failure branch is expressed only in terms of canonical red/blue
single-coordinate families over emitted and remaining worklists.
-/
theorem theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    Theorem49BoundaryRootSynthesis emb C₀ ∨
      data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
        ∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              (∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) ∧
                ∃ e : G.edgeSet,
                  (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                    e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                    e ∈ classifier.remainingControlEdges controlEdges ∧
                      ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                        z e ≠ 0 ∧
                          ((classifier.remainingControlEdges controlEdges).erase e).card <
                            (classifier.remainingControlEdges controlEdges).card ∧
                            ∃ i :
                              ({e : G.edgeSet //
                                e ∈ classifier.remainingControlEdges controlEdges} × Bool),
                              chainDotBilinForm G.edgeSet
                                  (redBlueSingleCoordinateFamily
                                    (classifier.remainingControlEdges controlEdges)
                                    hredRemaining hblueRemaining i :
                                    G.edgeSet → Color) z ≠ 0 := by
  rcases data.theorem49BoundaryRootSynthesis_or_forcedEdge_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining
      hblueRemaining with
    hclosed | hfallback
  · exact Or.inl hclosed
  · rcases hfallback with
      ⟨hforced, z, hzBoundary, hzNonzero, hvanish, e, heExtension, heRemaining,
        hePredicateOutside, hze, hprogress, i, hpair⟩
    rcases hforced with ⟨_forcedEdge, hedge⟩
    exact Or.inr
      ⟨data.forcedEdgeIndicatorPathXorDetectorPayload_of_enumeratedExceptionalAnnulusForcedEdge
          hedge,
        z, hzBoundary, hzNonzero, hvanish, e, heExtension, heRemaining,
        hePredicateOutside, hze, hprogress, i, hpair⟩

/--
Residual-state version of the runner-level canonical-family handoff.  The failure branch keeps
the forced-bin detector payload, the canonical F2 pairing witness, the concrete extension edge,
and the strict residual-worklist decrease obtained by recording that edge as processed.
-/
theorem theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_and_residualProgress_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
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
    (controlEdges processed : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnotProcessed :
      ∀ e ∈ classifier.remainingControlEdges controlEdges, e ∉ processed) :
    Theorem49BoundaryRootSynthesis emb C₀ ∨
      data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
        ∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              (∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) ∧
                ∃ e : G.edgeSet,
                  (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                    e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                    e ∈ classifier.remainingControlEdges controlEdges ∧
                      e ∈ classifier.residualRemainingControlEdges controlEdges processed ∧
                        ¬ data.EnumeratedExceptionalAnnulusForcedEdge
                          p0Inside p4Inside side e ∧
                          z e ≠ 0 ∧
                            (classifier.residualRemainingControlEdges controlEdges
                                (insert e processed)).card <
                              (classifier.residualRemainingControlEdges controlEdges
                                processed).card ∧
                              ((classifier.remainingControlEdges controlEdges).erase e).card <
                                (classifier.remainingControlEdges controlEdges).card ∧
                                ∃ i :
                                  ({e : G.edgeSet //
                                    e ∈ classifier.remainingControlEdges controlEdges} × Bool),
                                  chainDotBilinForm G.edgeSet
                                      (redBlueSingleCoordinateFamily
                                        (classifier.remainingControlEdges controlEdges)
                                        hredRemaining hblueRemaining i :
                                        G.edgeSet → Color) z ≠ 0 := by
  rcases data.theorem49BoundaryRootSynthesis_or_forcedEdge_and_extensionCoordinateSignalWithProgress_of_finsetControl
      emb C₀ colorings hsubset
      (redBlueSingleCoordinateFamily classifier.emittedFinset hredEmitted hblueEmitted)
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles classifier
      controlEdges hcontrol
      (redBlueSingleCoordinateFamily_witnessRed classifier.emittedFinset hredEmitted
        hblueEmitted)
      (redBlueSingleCoordinateFamily_witnessBlue classifier.emittedFinset hredEmitted
        hblueEmitted) with
    hclosed | hnext
  · exact Or.inl hclosed
  · rcases hnext with ⟨hforced, hsignal⟩
    rcases hforced with ⟨_forcedEdge, hedge⟩
    rcases data.exists_boundaryZeroChain_extensionControlEdge_canonicalFamilyPairing_ne_zero_and_residualProgress_of_extensionCoordinateSignalWithProgress
        hsignal hredRemaining hblueRemaining hnotProcessed with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heExtension, heRemaining, heResidual,
        hePredicateOutside, hze, hresidualProgress, hprogress, i, hpair⟩
    exact Or.inr
      ⟨data.forcedEdgeIndicatorPathXorDetectorPayload_of_enumeratedExceptionalAnnulusForcedEdge
          hedge,
        z, hzBoundary, hzNonzero, hvanish, e, heExtension, heRemaining, heResidual,
        hePredicateOutside, hze, hresidualProgress, hprogress, i, hpair⟩

/--
Trace-indexed residual-state version of the runner-level canonical-family handoff.  The failure
branch keeps the forced-bin detector payload, the canonical F2 pairing witness, the concrete
extension edge, proof that this edge occurs in the canonical remaining-control trace, and the
strict residual-worklist decrease obtained by recording that edge as processed.
-/
theorem theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlTraceEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_and_residualProgress_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
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
    (controlEdges processed : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnotProcessed :
      ∀ e ∈ classifier.remainingControlEdges controlEdges, e ∉ processed) :
    Theorem49BoundaryRootSynthesis emb C₀ ∨
      data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
        ∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              (∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) ∧
                ∃ e : G.edgeSet,
                  (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                    e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                    e ∈ classifier.remainingControlEdges controlEdges ∧
                      e ∈ classifier.remainingControlEdgeTrace controlEdges ∧
                        e ∈ classifier.residualRemainingControlEdges controlEdges processed ∧
                          ¬ data.EnumeratedExceptionalAnnulusForcedEdge
                            p0Inside p4Inside side e ∧
                            z e ≠ 0 ∧
                              (classifier.residualRemainingControlEdges controlEdges
                                  (insert e processed)).card <
                                (classifier.residualRemainingControlEdges controlEdges
                                  processed).card ∧
                              ((classifier.remainingControlEdges controlEdges).erase e).card <
                                (classifier.remainingControlEdges controlEdges).card ∧
                                ∃ i :
                                  ({e : G.edgeSet //
                                    e ∈ classifier.remainingControlEdges controlEdges} × Bool),
                                  chainDotBilinForm G.edgeSet
                                      (redBlueSingleCoordinateFamily
                                        (classifier.remainingControlEdges controlEdges)
                                        hredRemaining hblueRemaining i :
                                        G.edgeSet → Color) z ≠ 0 := by
  rcases data.theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionCoordinateSignalWithProgress_of_finsetControl
      emb C₀ colorings hsubset
      (redBlueSingleCoordinateFamily classifier.emittedFinset hredEmitted hblueEmitted)
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles classifier
      controlEdges hcontrol
      (redBlueSingleCoordinateFamily_witnessRed classifier.emittedFinset hredEmitted
        hblueEmitted)
      (redBlueSingleCoordinateFamily_witnessBlue classifier.emittedFinset hredEmitted
        hblueEmitted) with
    hclosed | hnext
  · exact Or.inl hclosed
  · rcases hnext with ⟨hforced, hsignal⟩
    have hresidualSignal :
        data.ExtensionCoordinateSignalWithResidualProgress emb p0Inside p4Inside side
          classifier controlEdges processed :=
      data.extensionCoordinateSignalWithResidualProgress_of_extensionCoordinateSignalWithProgress
        hsignal hnotProcessed
    rcases data.exists_boundaryZeroChain_extensionControlTraceEdge_canonicalFamilyPairing_ne_zero_and_residualProgress_of_extensionCoordinateSignalWithResidualProgress
        hresidualSignal hredRemaining hblueRemaining with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heExtension, heRemaining, heTrace,
        heResidual, hePredicateOutside, hze, hresidualProgress, hprogress, i, hpair⟩
    exact Or.inr
      ⟨hforced, z, hzBoundary, hzNonzero, hvanish, e, heExtension, heRemaining,
        heTrace, heResidual, hePredicateOutside, hze, hresidualProgress, hprogress, i,
        hpair⟩

/--
Trace-indexed residual-state runner handoff from a processed-edge zero invariant.  This is the
iteration-facing form of the canonical-family handoff: the current finite control set may still
be the original worklist, but any already processed edge is known zero under emitted-edge
vanishing, so the next obstruction edge is forced into the explicit residual worklist.
-/
theorem theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlTraceEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_and_residualProgress_of_finsetControl_of_processedControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
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
    (controlEdges processed : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hprocessedControl :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          ∀ e ∈ processed, z e = 0) :
    Theorem49BoundaryRootSynthesis emb C₀ ∨
      data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
        ∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              (∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) ∧
                ∃ e : G.edgeSet,
                  (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                    e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                    e ∈ classifier.remainingControlEdges controlEdges ∧
                      e ∈ classifier.remainingControlEdgeTrace controlEdges ∧
                        e ∈ classifier.residualRemainingControlEdges controlEdges processed ∧
                          ¬ data.EnumeratedExceptionalAnnulusForcedEdge
                            p0Inside p4Inside side e ∧
                            z e ≠ 0 ∧
                              (classifier.residualRemainingControlEdges controlEdges
                                  (insert e processed)).card <
                                (classifier.residualRemainingControlEdges controlEdges
                                  processed).card ∧
                              ((classifier.remainingControlEdges controlEdges).erase e).card <
                                (classifier.remainingControlEdges controlEdges).card ∧
                                ∃ i :
                                  ({e : G.edgeSet //
                                    e ∈ classifier.remainingControlEdges controlEdges} × Bool),
                                  chainDotBilinForm G.edgeSet
                                      (redBlueSingleCoordinateFamily
                                        (classifier.remainingControlEdges controlEdges)
                                        hredRemaining hblueRemaining i :
                                        G.edgeSet → Color) z ≠ 0 := by
  by_cases hclosed : Theorem49BoundaryRootSynthesis emb C₀
  · exact Or.inl hclosed
  · have hnotControl :
        ¬ ∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ planarBoundaryZeroSubmodule emb →
          (∀ e ∈ classifier.emittedFinset, z e = 0) →
            z = 0 := by
      intro hclassifierControl
      exact hclosed
        (data.theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierControl
          emb C₀ colorings hsubset
          (redBlueSingleCoordinateFamily classifier.emittedFinset hredEmitted hblueEmitted)
          p0Inside p4Inside side classifier hclassifierControl
          (redBlueSingleCoordinateFamily_witnessRed classifier.emittedFinset hredEmitted
            hblueEmitted)
          (redBlueSingleCoordinateFamily_witnessBlue classifier.emittedFinset hredEmitted
            hblueEmitted))
    have hpayload :
        data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side := by
      rcases data.exists_enumeratedExceptionalAnnulusForcedEdge_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
          p0Inside p4Inside h side hcyclic hportal_crosses hcycles with
        ⟨_forcedEdge, hedge⟩
      exact
        data.forcedEdgeIndicatorPathXorDetectorPayload_of_enumeratedExceptionalAnnulusForcedEdge
          hedge
    have hresidualSignal :
        data.ExtensionCoordinateSignalWithResidualProgress emb p0Inside p4Inside side
          classifier controlEdges processed :=
      data.extensionCoordinateSignalWithResidualProgress_of_not_classifierControl_of_finsetControl_of_processedControl
        emb p0Inside p4Inside side classifier controlEdges processed hnotControl hcontrol
        hprocessedControl
    rcases data.exists_boundaryZeroChain_extensionControlTraceEdge_canonicalFamilyPairing_ne_zero_and_residualProgress_of_extensionCoordinateSignalWithResidualProgress
        hresidualSignal hredRemaining hblueRemaining with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heExtension, heRemaining, heTrace,
        heResidual, hePredicateOutside, hze, hresidualProgress, hprogress, i, hpair⟩
    exact Or.inr
      ⟨hpayload, z, hzBoundary, hzNonzero, hvanish, e, heExtension, heRemaining,
        heTrace, heResidual, hePredicateOutside, hze, hresidualProgress, hprogress, i,
        hpair⟩

/--
Interior-support version of the runner-level canonical-family handoff.  The control set is the
canonical face-incidence interior support, and both the emitted-edge and remaining-edge probes
are the canonical red/blue single-coordinate families.
-/
theorem theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    Theorem49BoundaryRootSynthesis emb C₀ ∨
      data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
        ∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              (∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) ∧
                ∃ e : G.edgeSet,
                  (e ∈ classifier.crossingExtensionFinset
                      (interiorEdgeSupport emb.faceBoundary emb.faces) ∨
                    e ∈ classifier.noncrossingExtensionFinset
                      (interiorEdgeSupport emb.faceBoundary emb.faces)) ∧
                    e ∈ classifier.remainingControlEdges
                      (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
                      ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                        z e ≠ 0 ∧
                          ((classifier.remainingControlEdges
                              (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
                            (classifier.remainingControlEdges
                              (interiorEdgeSupport emb.faceBoundary emb.faces)).card ∧
                            ∃ i :
                              ({e : G.edgeSet //
                                e ∈ classifier.remainingControlEdges
                                  (interiorEdgeSupport emb.faceBoundary emb.faces)} × Bool),
                              chainDotBilinForm G.edgeSet
                                  (redBlueSingleCoordinateFamily
                                    (classifier.remainingControlEdges
                                      (interiorEdgeSupport emb.faceBoundary emb.faces))
                                    hredRemaining hblueRemaining i :
                                    G.edgeSet → Color) z ≠ 0 := by
  refine
    data.theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
      classifier (interiorEdgeSupport emb.faceBoundary emb.faces) ?_
      hredEmitted hblueEmitted hredRemaining hblueRemaining
  intro z hzBoundary hcontrol
  exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    z hzBoundary hcontrol

/--
Cardinality-driven algebraic handoff for one CAP5 finite-control step.  The emitted classifier
edges need no separate synthesis/failure witness here: once their coordinate count is too small
and a later finite control set controls the planar-boundary-zero chains, the extension signal
already exposes a nonzero boundary-zero chain with nonzero family pairing.
-/
theorem forcedEdge_and_boundaryZeroChain_familyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (colorings : Set (G.EdgeColoring Color))
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
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
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
  rcases data.forcedEdge_and_extensionCoordinateSignalWithProgress_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb p0Inside p4Inside h side hcyclic hportal_crosses hcycles classifier
      controlEdges hcard hcontrol with
    ⟨hforced, hsignal⟩
  rcases data.exists_boundaryZeroChain_familyPairing_ne_zero_of_extensionCoordinateSignalWithProgress
      family hsignal hwitnessExtensionRed hwitnessExtensionBlue with
    ⟨z, hzBoundary, hzNonzero, hvanish, i, hpair⟩
  exact ⟨hforced, z, hzBoundary, hzNonzero, hvanish, i, hpair⟩

/--
Forced-bin payload version of the cardinality-driven algebraic handoff.  This keeps the
finite forced-edge detector attached to the boundary-zero chain pairing that the cardinality
obstruction exposes.
-/
theorem forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (colorings : Set (G.EdgeColoring Color))
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
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
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
    data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ i : κ,
                chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  rcases data.forcedEdge_and_boundaryZeroChain_familyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb colorings family p0Inside p4Inside h side hcyclic hportal_crosses hcycles
      classifier controlEdges hcard hcontrol hwitnessExtensionRed hwitnessExtensionBlue with
    ⟨hforced, z, hzBoundary, hzNonzero, hvanish, i, hpair⟩
  rcases hforced with ⟨e, hedge⟩
  exact
    ⟨data.forcedEdgeIndicatorPathXorDetectorPayload_of_enumeratedExceptionalAnnulusForcedEdge
        hedge,
      z, hzBoundary, hzNonzero, hvanish, i, hpair⟩

/--
Interior-support control version of the cardinality-driven algebraic handoff.  This removes the
explicit finite-control proof from the family-pairing surface by using all interior-support edges
as the later control set.
-/
theorem forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (colorings : Set (G.EdgeColoring Color))
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
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hwitnessExtensionRed :
      ∀ e : G.edgeSet,
        e ∈ classifier.crossingExtensionFinset
              (interiorEdgeSupport emb.faceBoundary emb.faces) ∨
            e ∈ classifier.noncrossingExtensionFinset
              (interiorEdgeSupport emb.faceBoundary emb.faces) →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessExtensionBlue :
      ∀ e : G.edgeSet,
        e ∈ classifier.crossingExtensionFinset
              (interiorEdgeSupport emb.faceBoundary emb.faces) ∨
            e ∈ classifier.noncrossingExtensionFinset
              (interiorEdgeSupport emb.faceBoundary emb.faces) →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue) :
    data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ i : κ,
                chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  refine
    data.forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb colorings family p0Inside p4Inside h side hcyclic hportal_crosses hcycles
      classifier (interiorEdgeSupport emb.faceBoundary emb.faces) hcard ?_
      hwitnessExtensionRed hwitnessExtensionBlue
  intro z hzBoundary hcontrol
  exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    z hzBoundary hcontrol

/--
Cardinality-driven algebraic handoff retaining the next extension edge.  In the failure branch
the finite runner now exposes the concrete extension edge on which the boundary-zero chain is
nonzero, together with the strict remaining-worklist decrease and a nonzero family pairing.
-/
theorem forcedEdge_and_extensionControlEdge_boundaryZeroChain_familyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (colorings : Set (G.EdgeColoring Color))
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
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
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
    (∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) ∧
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ e : G.edgeSet,
                (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                  e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                  ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                    z e ≠ 0 ∧
                      ((classifier.remainingControlEdges controlEdges).erase e).card <
                        (classifier.remainingControlEdges controlEdges).card ∧
                        ∃ i : κ,
                          chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  rcases data.forcedEdge_and_extensionCoordinateSignalWithProgress_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb p0Inside p4Inside h side hcyclic hportal_crosses hcycles classifier
      controlEdges hcard hcontrol with
    ⟨hforced, hsignal⟩
  rcases data.exists_boundaryZeroChain_extensionControlEdge_familyPairing_ne_zero_of_extensionCoordinateSignalWithProgress
      family hsignal hwitnessExtensionRed hwitnessExtensionBlue with
    ⟨z, hzBoundary, hzNonzero, hvanish, e, heExtension, hePredicateOutside, hze,
      hprogress, i, hpair⟩
  exact
    ⟨hforced, z, hzBoundary, hzNonzero, hvanish, e, heExtension, hePredicateOutside,
      hze, hprogress, i, hpair⟩

/--
Forced-bin detector form of the edge-level cardinality handoff.  The returned obstruction now
keeps both finite detector sides: the one-edge forced payload and the nonzero extension edge that
strictly decreases the remaining-control worklist.
-/
theorem forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_familyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (colorings : Set (G.EdgeColoring Color))
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
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
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
    data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ e : G.edgeSet,
                (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                  e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                  ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                    z e ≠ 0 ∧
                      ((classifier.remainingControlEdges controlEdges).erase e).card <
                        (classifier.remainingControlEdges controlEdges).card ∧
                        ∃ i : κ,
                          chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  rcases data.forcedEdge_and_extensionControlEdge_boundaryZeroChain_familyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb colorings family p0Inside p4Inside h side hcyclic hportal_crosses hcycles
      classifier controlEdges hcard hcontrol hwitnessExtensionRed hwitnessExtensionBlue with
    ⟨hforced, z, hzBoundary, hzNonzero, hvanish, e, heExtension, hePredicateOutside,
      hze, hprogress, i, hpair⟩
  rcases hforced with ⟨_forcedEdge, hedge⟩
  exact
    ⟨data.forcedEdgeIndicatorPathXorDetectorPayload_of_enumeratedExceptionalAnnulusForcedEdge
        hedge,
      z, hzBoundary, hzNonzero, hvanish, e, heExtension, hePredicateOutside, hze,
      hprogress, i, hpair⟩

/--
Interior-support version of the edge-level cardinality handoff.  This is the canonical
no-extra-control form: the next extension edge, nonzero boundary-zero chain, worklist decrease,
family pairing, and one-edge forced-bin detector are all returned over the face-incidence
interior support.
-/
theorem forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_familyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (colorings : Set (G.EdgeColoring Color))
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
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hwitnessExtensionRed :
      ∀ e : G.edgeSet,
        e ∈ classifier.crossingExtensionFinset
              (interiorEdgeSupport emb.faceBoundary emb.faces) ∨
            e ∈ classifier.noncrossingExtensionFinset
              (interiorEdgeSupport emb.faceBoundary emb.faces) →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessExtensionBlue :
      ∀ e : G.edgeSet,
        e ∈ classifier.crossingExtensionFinset
              (interiorEdgeSupport emb.faceBoundary emb.faces) ∨
            e ∈ classifier.noncrossingExtensionFinset
              (interiorEdgeSupport emb.faceBoundary emb.faces) →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue) :
    data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ e : G.edgeSet,
                (e ∈ classifier.crossingExtensionFinset
                    (interiorEdgeSupport emb.faceBoundary emb.faces) ∨
                  e ∈ classifier.noncrossingExtensionFinset
                    (interiorEdgeSupport emb.faceBoundary emb.faces)) ∧
                  ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                    z e ≠ 0 ∧
                      ((classifier.remainingControlEdges
                          (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
                        (classifier.remainingControlEdges
                          (interiorEdgeSupport emb.faceBoundary emb.faces)).card ∧
                        ∃ i : κ,
                          chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  refine
    data.forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_familyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb colorings family p0Inside p4Inside h side hcyclic hportal_crosses hcycles
      classifier (interiorEdgeSupport emb.faceBoundary emb.faces) hcard ?_
      hwitnessExtensionRed hwitnessExtensionBlue
  intro z hzBoundary hcontrol
  exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    z hzBoundary hcontrol

/--
Canonical-family cardinality handoff for one CAP5 finite-control step.  Instead of taking an
external generator family and red/blue witness predicates, this theorem builds the family from
red/blue single-coordinate membership certificates on the remaining-control worklist.
-/
theorem forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (colorings : Set (G.EdgeColoring Color))
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
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hred :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ e : G.edgeSet,
                (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                  e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                  e ∈ classifier.remainingControlEdges controlEdges ∧
                    ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                      z e ≠ 0 ∧
                        ((classifier.remainingControlEdges controlEdges).erase e).card <
                          (classifier.remainingControlEdges controlEdges).card ∧
                          ∃ i :
                            ({e : G.edgeSet //
                              e ∈ classifier.remainingControlEdges controlEdges} × Bool),
                            chainDotBilinForm G.edgeSet
                                (redBlueSingleCoordinateFamily
                                  (classifier.remainingControlEdges controlEdges) hred hblue i :
                                  G.edgeSet → Color) z ≠ 0 := by
  rcases data.forcedEdge_and_extensionCoordinateSignalWithProgress_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb p0Inside p4Inside h side hcyclic hportal_crosses hcycles classifier
      controlEdges hcard hcontrol with
    ⟨hforced, hsignal⟩
  rcases hforced with ⟨_forcedEdge, hedge⟩
  rcases data.exists_boundaryZeroChain_extensionControlEdge_canonicalFamilyPairing_ne_zero_of_extensionCoordinateSignalWithProgress
      hsignal hred hblue with
    ⟨z, hzBoundary, hzNonzero, hvanish, e, heExtension, heRemaining,
      hePredicateOutside, hze, hprogress, i, hpair⟩
  exact
    ⟨data.forcedEdgeIndicatorPathXorDetectorPayload_of_enumeratedExceptionalAnnulusForcedEdge
        hedge,
      z, hzBoundary, hzNonzero, hvanish, e, heExtension, heRemaining,
      hePredicateOutside, hze, hprogress, i, hpair⟩

/--
Unique-certificate form of the canonical-family cardinality handoff.  A finite checker can now
feed unique projected-bicolored face certificates directly on the remaining-control worklist;
the theorem extracts the red/blue single-coordinate memberships and then runs the path-xor
handoff with the canonical red/blue family.
-/
theorem forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_uniqueProjectedBicoloredCertificates_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (colorings : Set (G.EdgeColoring Color))
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
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hred :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        ∃ C ∈ colorings, ∃ f : emb.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            a + b = red ∧
              e ∈ emb.faceBoundary f ∧
                e ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∧
                  (C e = a ∨ C e = b) ∧
                    ∀ e' : G.edgeSet,
                      e' ≠ e →
                      e' ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces →
                      e' ∈ emb.faceBoundary f →
                        ¬ (C e' = a ∨ C e' = b))
    (hblue :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        ∃ C ∈ colorings, ∃ f : emb.Face, ∃ a b : Color,
          ValidColorPair a b ∧
            a + b = blue ∧
              e ∈ emb.faceBoundary f ∧
                e ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces ∧
                  (C e = a ∨ C e = b) ∧
                    ∀ e' : G.edgeSet,
                      e' ≠ e →
                      e' ∉ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces →
                      e' ∈ emb.faceBoundary f →
                        ¬ (C e' = a ∨ C e' = b)) :
    let hmembers :=
      redBlueSingleCoordinateMemberships_of_uniqueProjectedBicoloredCertificates
        (emb := emb) (colorings := colorings)
        (classifier.remainingControlEdges controlEdges) hred hblue
    data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ e : G.edgeSet,
                (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                  e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                  e ∈ classifier.remainingControlEdges controlEdges ∧
                    ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                      z e ≠ 0 ∧
                        ((classifier.remainingControlEdges controlEdges).erase e).card <
                          (classifier.remainingControlEdges controlEdges).card ∧
                          ∃ i :
                            ({e : G.edgeSet //
                              e ∈ classifier.remainingControlEdges controlEdges} × Bool),
                            chainDotBilinForm G.edgeSet
                                (redBlueSingleCoordinateFamily
                                  (classifier.remainingControlEdges controlEdges)
                                  hmembers.1 hmembers.2 i :
                                  G.edgeSet → Color) z ≠ 0 := by
  let hmembers :=
    redBlueSingleCoordinateMemberships_of_uniqueProjectedBicoloredCertificates
      (emb := emb) (colorings := colorings)
      (classifier.remainingControlEdges controlEdges) hred hblue
  exact
    data.forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb colorings p0Inside p4Inside h side hcyclic hportal_crosses hcycles
      classifier controlEdges hcard hcontrol hmembers.1 hmembers.2

/--
Interior-support canonical-family cardinality handoff.  The finite control set is the canonical
face-incidence interior support, while the generator family is built from membership certificates
on the remaining interior-support worklist.
-/
theorem forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (colorings : Set (G.EdgeColoring Color))
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
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hred :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ e : G.edgeSet,
                (e ∈ classifier.crossingExtensionFinset
                    (interiorEdgeSupport emb.faceBoundary emb.faces) ∨
                  e ∈ classifier.noncrossingExtensionFinset
                    (interiorEdgeSupport emb.faceBoundary emb.faces)) ∧
                  e ∈ classifier.remainingControlEdges
                    (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
                    ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                      z e ≠ 0 ∧
                        ((classifier.remainingControlEdges
                            (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
                          (classifier.remainingControlEdges
                            (interiorEdgeSupport emb.faceBoundary emb.faces)).card ∧
                          ∃ i :
                            ({e : G.edgeSet //
                              e ∈ classifier.remainingControlEdges
                                (interiorEdgeSupport emb.faceBoundary emb.faces)} × Bool),
                            chainDotBilinForm G.edgeSet
                                (redBlueSingleCoordinateFamily
                                  (classifier.remainingControlEdges
                                    (interiorEdgeSupport emb.faceBoundary emb.faces))
                                  hred hblue i : G.edgeSet → Color) z ≠ 0 := by
  refine
    data.forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb colorings p0Inside p4Inside h side hcyclic hportal_crosses hcycles
      classifier (interiorEdgeSupport emb.faceBoundary emb.faces) hcard ?_ hred hblue
  intro z hzBoundary hcontrol
  exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    z hzBoundary hcontrol

/--
Executable checker-to-algebraic handoff driven by the emitted-finset cardinality gap.  A finite
CAP5 sweep either reports missing primitive checker evidence, or its completed cyclic-five
histogram reaches the forced-bin detector together with the nonzero boundary-zero family pairing
exposed by the cardinality obstruction.
-/
theorem ofDecidableChecks_missingCheckerEvidence_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (colorings : Set (G.EdgeColoring Color))
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
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
    (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).MissingCheckerEvidence) ∨
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).partialLatents.length = 0 ∧
          (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
            boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
        data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
          ∃ z : G.edgeSet → Color,
            z ∈ planarBoundaryZeroSubmodule emb ∧
              z ≠ 0 ∧
                (∀ e : G.edgeSet,
                  data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                    z e = 0) ∧
                  ∃ i : κ,
                    chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks boundaryEdge side
  by_cases hmissingEmpty : report.missingCheckerEvidenceLatents = []
  · right
    rcases report.all_checker_evidence_of_missingCheckerEvidenceLatents_eq_nil
        hmissingEmpty with
      ⟨hportal, hsideCycles⟩
    have hhist :
        report.realizedSeparatorLatents.length = 0 ∧
          report.partialLatents.length = 0 ∧
            report.forcedCounterexampleLatents.length = 16 :=
      report.histogram_lengths_eq_of_complete_of_cyclicallyFiveEdgeConnected
        hcyclic hportal hsideCycles
    exact
      ⟨by simpa [report] using hhist,
        data.forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
          emb colorings family p0Inside p4Inside h side hcyclic hportal_crosses
          hcycles classifier controlEdges hcard hcontrol hwitnessExtensionRed
          hwitnessExtensionBlue⟩
  · left
    rcases (report.missingCheckerEvidenceLatents_ne_nil_iff_exists_missingCheckerEvidence).1
        hmissingEmpty with
      ⟨latent, hmem, hmissing⟩
    exact ⟨latent, hmem, by
      simpa [report, CAP5ExceptionalAnnulusGeneratorReport.node,
        CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hmissing⟩

/--
Histogram-to-canonical-family form of the cardinality handoff.  A decidable CAP5 sweep either
reports the primitive missing checker evidence, or the complete forced-bin histogram is paired
with the canonical remaining-worklist red/blue detector and a nonzero boundary-zero chain.
-/
theorem ofDecidableChecks_missingCheckerEvidence_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (colorings : Set (G.EdgeColoring Color))
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hred :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).MissingCheckerEvidence) ∨
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).partialLatents.length = 0 ∧
          (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
            boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
        data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
          ∃ z : G.edgeSet → Color,
            z ∈ planarBoundaryZeroSubmodule emb ∧
              z ≠ 0 ∧
                (∀ e : G.edgeSet,
                  data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                    z e = 0) ∧
                  ∃ e : G.edgeSet,
                    (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                      e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                      e ∈ classifier.remainingControlEdges controlEdges ∧
                        ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                          z e ≠ 0 ∧
                            ((classifier.remainingControlEdges controlEdges).erase e).card <
                              (classifier.remainingControlEdges controlEdges).card ∧
                              ∃ i :
                                ({e : G.edgeSet //
                                  e ∈ classifier.remainingControlEdges controlEdges} × Bool),
                                chainDotBilinForm G.edgeSet
                                    (redBlueSingleCoordinateFamily
                                      (classifier.remainingControlEdges controlEdges)
                                      hred hblue i :
                                      G.edgeSet → Color) z ≠ 0 := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks boundaryEdge side
  by_cases hmissingEmpty : report.missingCheckerEvidenceLatents = []
  · right
    rcases report.all_checker_evidence_of_missingCheckerEvidenceLatents_eq_nil
        hmissingEmpty with
      ⟨hportal, hsideCycles⟩
    have hhist :
        report.realizedSeparatorLatents.length = 0 ∧
          report.partialLatents.length = 0 ∧
            report.forcedCounterexampleLatents.length = 16 :=
      report.histogram_lengths_eq_of_complete_of_cyclicallyFiveEdgeConnected
        hcyclic hportal hsideCycles
    exact
      ⟨by simpa [report] using hhist,
        data.forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
          emb colorings p0Inside p4Inside h side hcyclic hportal_crosses hcycles classifier
          controlEdges hcard hcontrol hred hblue⟩
  · left
    rcases (report.missingCheckerEvidenceLatents_ne_nil_iff_exists_missingCheckerEvidence).1
        hmissingEmpty with
      ⟨latent, hmem, hmissing⟩
    exact ⟨latent, hmem, by
      simpa [report, CAP5ExceptionalAnnulusGeneratorReport.node,
        CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hmissing⟩

/--
Exact forced-edge coverage refutes an evading boundary-zero chain.  This is the algebraic core
behind the CAP5 path-xor obstruction: a nonzero selected-boundary-zero chain cannot both vanish
on every enumerated forced edge and be hit by an enumerated forced edge.
-/
theorem forcedEdgeCoverage_refutes_boundaryZeroChain_vanishing_on_forcedEdges
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    ¬ ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          ∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0 := by
  rintro ⟨z, hzBoundary, hzNonzero, hzForcedZero⟩
  rcases hcoverage hzBoundary hzNonzero with ⟨e, heForced, hze⟩
  exact hze (hzForcedZero e heForced)

/-- Exact forced-edge coverage follows as soon as the enumerated CAP5 forced edges contain every
ambient interior-support edge.  This is the detector-facing form of the finite all-interior-edge
control survivor. -/
theorem forcedEdgeCoverage_of_interiorEdgeSupport_subset_enumeratedForcedEdges
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hInteriorForced :
      ∀ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      z ≠ 0 →
        ∃ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0 :=
  planarBoundaryZeroSubmodule_nonzeroCoverage_of_interiorEdgeSupport_subset
    emb hInteriorForced

/-- The all-interior enumerated forced-edge premise also supplies the broader normal-form
outside-crossing predicate used by the algebraic CAP5 lane. -/
theorem interiorEdgeSupport_subset_exceptionalAnnulusCrossingOutsideEdge_of_interiorEdgeSupport_subset_enumeratedForcedEdges
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hInteriorForced :
      ∀ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) :
    ∀ e : G.edgeSet,
      e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
        data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e := by
  intro e heInterior
  exact data.enumeratedExceptionalAnnulusForcedEdge_to_exceptionalAnnulusCrossingOutsideEdge
    (hInteriorForced e heInterior)

/-- The broader outside-crossing CAP5 predicate controls all selected-boundary-zero chains as
soon as it contains the ambient interior support. -/
theorem exceptionalAnnulusCrossingOutsideEdgeCoverage_of_interiorEdgeSupport_subset_exceptionalAnnulusCrossingOutsideEdge
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hInteriorCrossingOutside :
      ∀ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
          data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      z ≠ 0 →
        ∃ e : G.edgeSet,
          data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e ∧
            z e ≠ 0 :=
  planarBoundaryZeroSubmodule_nonzeroCoverage_of_interiorEdgeSupport_subset
    emb hInteriorCrossingOutside

/-- Consequently, all-interior enumerated forced-edge coverage is strong enough to discharge the
nonzero-witness obligation for the broader outside-crossing CAP5 algebraic predicate. -/
theorem exceptionalAnnulusCrossingOutsideEdgeCoverage_of_interiorEdgeSupport_subset_enumeratedForcedEdges
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hInteriorForced :
      ∀ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      z ≠ 0 →
        ∃ e : G.edgeSet,
          data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e ∧
            z e ≠ 0 :=
  data.exceptionalAnnulusCrossingOutsideEdgeCoverage_of_interiorEdgeSupport_subset_exceptionalAnnulusCrossingOutsideEdge
    emb p0Inside p4Inside side
    (data.interiorEdgeSupport_subset_exceptionalAnnulusCrossingOutsideEdge_of_interiorEdgeSupport_subset_enumeratedForcedEdges
      emb p0Inside p4Inside side hInteriorForced)

/-- All-interior enumerated forced-edge coverage can hold only on sides crossing every ambient
interior-support edge.  This isolates the geometric side condition hidden in the finite
forced-edge worklist. -/
theorem interiorEdgeSupport_subset_sideCrossing_of_interiorEdgeSupport_subset_enumeratedForcedEdges
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hInteriorForced :
      ∀ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) :
    ∀ e : G.edgeSet,
      e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
        EdgeCrossesVertexSide G side e := by
  intro e heInterior
  exact data.enumeratedExceptionalAnnulusForcedEdge_crosses
    (hInteriorForced e heInterior)

/-- Odd closed-walk obstruction for the enumerated CAP5 forced-edge predicate.  A fixed side
cannot force every edge traversed by an odd closed walk, because enumerated forced edges all
cross that same side. -/
theorem not_forall_enumeratedExceptionalAnnulusForcedEdge_of_closed_walk_odd_length
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : V → Prop) {u : V}
    (p : G.Walk u u) (hodd : Odd p.length) :
    ¬ (∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) := by
  intro hforced
  exact not_forall_edgeCrossesVertexSide_of_closed_walk_odd_length p hodd
    (fun e he => data.enumeratedExceptionalAnnulusForcedEdge_crosses (hforced e he))

/-- Witness form of the odd closed-walk obstruction: at least one traversed edge of an odd
closed walk is absent from the enumerated CAP5 forced-edge predicate. -/
theorem exists_walkEdge_not_enumeratedExceptionalAnnulusForcedEdge_of_closed_walk_odd_length
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : V → Prop) {u : V}
    (p : G.Walk u u) (hodd : Odd p.length) :
    ∃ e : G.edgeSet,
      (e : Sym2 V) ∈ p.edges ∧
        ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
  classical
  by_contra hnoGap
  exact data.not_forall_enumeratedExceptionalAnnulusForcedEdge_of_closed_walk_odd_length
    p0Inside p4Inside side p hodd
    (by
      intro e he
      by_contra hnotForced
      exact hnoGap ⟨e, he, hnotForced⟩)

/-- Worklist-facing odd closed-walk obstruction.  If all traversed edges of an odd closed walk
lie in the ambient interior support, the CAP5 forced-edge enumeration must miss some
interior-support edge. -/
theorem exists_interiorEdgeSupportEdge_not_enumeratedForcedEdge_of_closed_walk_odd_length
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop) {u : V}
    (p : G.Walk u u) (hodd : Odd p.length)
    (hInterior :
      ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ∃ e : G.edgeSet,
      e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
        ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
  rcases data.exists_walkEdge_not_enumeratedExceptionalAnnulusForcedEdge_of_closed_walk_odd_length
      p0Inside p4Inside side p hodd with
    ⟨e, heWalk, hnotForced⟩
  exact ⟨e, hInterior e heWalk, hnotForced⟩

/--
Canonical-worklist form of the odd closed-walk obstruction.  If an odd closed walk is entirely
supported inside the ambient interior support, the Boolean CAP5 forced-edge classifier cannot
have exhausted the canonical interior-support worklist: one traversed interior edge remains
unemitted, and erasing it strictly decreases the finite worklist measure.
-/
theorem exists_remainingInteriorSupportEdge_with_card_erase_lt_of_closed_walk_odd_length_in_interiorSupport
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    {u : V} (p : G.Walk u u) (hodd : Odd p.length)
    (hInterior :
      ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ∃ e : G.edgeSet,
      e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
        ((classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
          (classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
  rcases data.exists_interiorEdgeSupportEdge_not_enumeratedForcedEdge_of_closed_walk_odd_length
      emb p0Inside p4Inside side p hodd hInterior with
    ⟨e, heInterior, hnotForced⟩
  have heRemaining :
      e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces) := by
    refine
      (classifier.mem_remainingControlEdges_iff
        (interiorEdgeSupport emb.faceBoundary emb.faces) e).2 ⟨heInterior, ?_⟩
    intro heEmitted
    exact hnotForced ((classifier.emittedFinset_spec e).1 heEmitted)
  exact ⟨e, heRemaining,
    classifier.card_erase_remainingControlEdges_lt_of_mem
      (interiorEdgeSupport emb.faceBoundary emb.faces) heRemaining⟩

/--
Consequently, an odd closed walk in the ambient interior support refutes the executable
empty-worklist side of the exact F2 fork for that classifier.
-/
theorem not_remainingInteriorSupportEmpty_of_closed_walk_odd_length_in_interiorSupport
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    {u : V} (p : G.Walk u u) (hodd : Odd p.length)
    (hInterior :
      ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    classifier.remainingControlEdges (interiorEdgeSupport emb.faceBoundary emb.faces) ≠ ∅ := by
  intro hEmpty
  rcases
      data.exists_remainingInteriorSupportEdge_with_card_erase_lt_of_closed_walk_odd_length_in_interiorSupport
        emb p0Inside p4Inside side classifier p hodd hInterior with
    ⟨e, heRemaining, _hdecrease⟩
  rw [hEmpty] at heRemaining
  simp at heRemaining

/--
The all-interior forced-edge success side excludes the odd-interior obstruction.  If every
ambient interior-support edge is enumerated as a CAP5 forced edge for one side, then the ambient
interior support cannot contain an odd closed walk.
-/
theorem not_exists_closed_odd_walk_in_interiorSupport_of_interiorEdgeSupport_subset_enumeratedForcedEdges
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hInteriorForced :
      ∀ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) :
    ¬ ∃ u : V, ∃ p : G.Walk u u,
      Odd p.length ∧
        ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
          e ∈ interiorEdgeSupport emb.faceBoundary emb.faces := by
  rintro ⟨u, p, hodd, hInterior⟩
  exact data.not_forall_enumeratedExceptionalAnnulusForcedEdge_of_closed_walk_odd_length
    p0Inside p4Inside side p hodd
    (fun e he => hInteriorForced e (hInterior e he))

/-- A triangle inside the ambient interior support obstructs the all-interior side-crossing
premise.  This is the Lean form of the validation-lab odd-cycle obstruction: one fixed side
cannot cross all three edges of an interior triangle. -/
theorem not_interiorEdgeSupport_subset_sideCrossing_of_interiorEdgeSupport_triangle
    (emb : PlaneEmbeddingWithBoundary G) (side : V → Prop)
    {a b c : V} {eab ebc eac : G.edgeSet}
    (heab_pair : (eab : Sym2 V) = s(a, b))
    (hebc_pair : (ebc : Sym2 V) = s(b, c))
    (heac_pair : (eac : Sym2 V) = s(a, c))
    (heabInterior : eab ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (hebcInterior : ebc ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (heacInterior : eac ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ¬ (∀ e : G.edgeSet,
      e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
        EdgeCrossesVertexSide G side e) := by
  intro hcrossAll
  exact not_three_edgeCrossesVertexSide_triangle heab_pair hebc_pair heac_pair
    ⟨hcrossAll eab heabInterior, hcrossAll ebc hebcInterior,
      hcrossAll eac heacInterior⟩

/-- A triangle inside the ambient interior support obstructs all-interior coverage by the
normal-form CAP5 outside-crossing predicate. -/
theorem not_interiorEdgeSupport_subset_exceptionalAnnulusCrossingOutsideEdge_of_interiorEdgeSupport_triangle
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    {a b c : V} {eab ebc eac : G.edgeSet}
    (heab_pair : (eab : Sym2 V) = s(a, b))
    (hebc_pair : (ebc : Sym2 V) = s(b, c))
    (heac_pair : (eac : Sym2 V) = s(a, c))
    (heabInterior : eab ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (hebcInterior : ebc ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (heacInterior : eac ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ¬ (∀ e : G.edgeSet,
      e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
        data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e) := by
  intro hcrossingOutsideAll
  exact data.not_three_exceptionalAnnulusCrossingOutsideEdge_triangle
    heab_pair hebc_pair heac_pair
    ⟨hcrossingOutsideAll eab heabInterior, hcrossingOutsideAll ebc hebcInterior,
      hcrossingOutsideAll eac heacInterior⟩

/-- A triangle inside the ambient interior support obstructs the all-interior enumerated
forced-edge premise: if every interior-support edge were enumerated, all three triangle edges
would have to cross the same side. -/
theorem not_interiorEdgeSupport_subset_enumeratedForcedEdges_of_interiorEdgeSupport_triangle
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    {a b c : V} {eab ebc eac : G.edgeSet}
    (heab_pair : (eab : Sym2 V) = s(a, b))
    (hebc_pair : (ebc : Sym2 V) = s(b, c))
    (heac_pair : (eac : Sym2 V) = s(a, c))
    (heabInterior : eab ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (hebcInterior : ebc ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (heacInterior : eac ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ¬ (∀ e : G.edgeSet,
      e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) := by
  intro hInteriorForced
  exact not_interiorEdgeSupport_subset_sideCrossing_of_interiorEdgeSupport_triangle
    emb side heab_pair hebc_pair heac_pair heabInterior hebcInterior heacInterior
    (data.interiorEdgeSupport_subset_sideCrossing_of_interiorEdgeSupport_subset_enumeratedForcedEdges
      emb p0Inside p4Inside side hInteriorForced)

/-- A non-crossing ambient interior-support edge is a concrete obstruction to all-interior
enumerated forced-edge coverage. -/
theorem exists_interiorEdgeSupportEdge_not_enumeratedForcedEdge_of_exists_interiorEdgeSupportEdge_not_sideCrossing
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hNoncrossing :
      ∃ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
          ¬ EdgeCrossesVertexSide G side e) :
    ∃ e : G.edgeSet,
      e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
        ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
  rcases hNoncrossing with ⟨e, heInterior, hnotCross⟩
  refine ⟨e, heInterior, ?_⟩
  intro heForced
  exact hnotCross (data.enumeratedExceptionalAnnulusForcedEdge_crosses heForced)

/-- If an ambient interior-support edge is not even in the broader outside-crossing CAP5
predicate, it cannot be enumerated by the finite forced-edge generator. -/
theorem exists_interiorEdgeSupportEdge_not_enumeratedForcedEdge_of_exists_interiorEdgeSupportEdge_not_exceptionalAnnulusCrossingOutsideEdge
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hNotCrossingOutside :
      ∃ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
          ¬ data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e) :
    ∃ e : G.edgeSet,
      e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
        ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
  rcases hNotCrossingOutside with ⟨e, heInterior, hnotCrossingOutside⟩
  refine ⟨e, heInterior, ?_⟩
  intro heForced
  exact hnotCrossingOutside
    (data.enumeratedExceptionalAnnulusForcedEdge_to_exceptionalAnnulusCrossingOutsideEdge
      heForced)

/-- Worklist-facing triangle obstruction.  If the ambient interior support contains a triangle,
the CAP5 forced-edge enumeration must miss at least one of the ambient interior-support edges. -/
theorem exists_interiorEdgeSupportEdge_not_enumeratedForcedEdge_of_interiorEdgeSupport_triangle
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    {a b c : V} {eab ebc eac : G.edgeSet}
    (heab_pair : (eab : Sym2 V) = s(a, b))
    (hebc_pair : (ebc : Sym2 V) = s(b, c))
    (heac_pair : (eac : Sym2 V) = s(a, c))
    (heabInterior : eab ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (hebcInterior : ebc ∈ interiorEdgeSupport emb.faceBoundary emb.faces)
    (heacInterior : eac ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ∃ e : G.edgeSet,
      e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
        ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
  by_contra hnoGap
  exact
    not_interiorEdgeSupport_subset_enumeratedForcedEdges_of_interiorEdgeSupport_triangle
      emb p0Inside p4Inside side heab_pair hebc_pair heac_pair
      heabInterior hebcInterior heacInterior
      (by
        intro e heInterior
        by_contra hnotForced
        exact hnoGap ⟨e, heInterior, hnotForced⟩)

/-- Consequently, no nonzero selected-boundary-zero chain can vanish on all enumerated CAP5 forced
edges when those forced edges include the ambient interior support. -/
theorem refutes_boundaryZeroChain_vanishing_on_forcedEdges_of_interiorEdgeSupport_subset_enumeratedForcedEdges
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hInteriorForced :
      ∀ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) :
    ¬ ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          ∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0 := by
  exact
    data.forcedEdgeCoverage_refutes_boundaryZeroChain_vanishing_on_forcedEdges
      emb p0Inside p4Inside side
      (data.forcedEdgeCoverage_of_interiorEdgeSupport_subset_enumeratedForcedEdges
        emb p0Inside p4Inside side hInteriorForced)

/--
Failure of exact forced-edge coverage produces the evading chain explicitly: a nonzero
selected-boundary-zero chain that vanishes on every enumerated CAP5 forced edge.  This is the
proof-facing form of the finite F2 lab verdict.
-/
theorem exists_boundaryZeroChain_vanishing_on_forcedEdges_of_not_forcedEdgeCoverage
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hnotCoverage :
      ¬ (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)) :
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          ∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0 := by
  by_contra hnoObstruction
  exact hnotCoverage (by
    intro z hzBoundary hzNonzero
    by_contra hnoHit
    exact hnoObstruction ⟨z, hzBoundary, hzNonzero, by
      intro e heForced
      by_contra hze
      exact hnoHit ⟨e, heForced, hze⟩⟩)

/--
Exact forced-edge coverage is equivalent to the absence of a nonzero selected-boundary-zero
chain that vanishes on every enumerated forced edge.
-/
theorem forcedEdgeCoverage_iff_no_boundaryZeroChain_vanishing_on_forcedEdges
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      z ≠ 0 →
        ∃ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) ↔
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0 := by
  constructor
  · intro hcoverage
    exact
      data.forcedEdgeCoverage_refutes_boundaryZeroChain_vanishing_on_forcedEdges
        emb p0Inside p4Inside side hcoverage
  · intro hnoEvader z hzBoundary hzNonzero
    by_contra hnoHit
    exact hnoEvader ⟨z, hzBoundary, hzNonzero, by
      intro e heForced
      by_contra hze
      exact hnoHit ⟨e, heForced, hze⟩⟩

/-- Negating exact forced-edge coverage is equivalent to the existence of an evading nonzero
selected-boundary-zero chain. -/
theorem not_forcedEdgeCoverage_iff_exists_boundaryZeroChain_vanishing_on_forcedEdges
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop) :
    (¬ ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      z ≠ 0 →
        ∃ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) ↔
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0 := by
  constructor
  · exact data.exists_boundaryZeroChain_vanishing_on_forcedEdges_of_not_forcedEdgeCoverage
      emb p0Inside p4Inside side
  · intro hevader hcoverage
    exact
      (data.forcedEdgeCoverage_refutes_boundaryZeroChain_vanishing_on_forcedEdges
        emb p0Inside p4Inside side hcoverage) hevader

/--
Failure of exact forced-edge coverage also has a geometric finite-worklist face: at least one
ambient interior-support edge is not enumerated by the CAP5 forced-edge predicate.  Otherwise the
all-interior-support survivor would supply exact coverage.
-/
theorem exists_interiorEdgeSupportEdge_not_enumeratedForcedEdge_of_not_forcedEdgeCoverage
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hnotCoverage :
      ¬ (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)) :
    ∃ e : G.edgeSet,
      e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
        ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
  by_contra hnoGap
  have hInteriorForced :
      ∀ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
    intro e heInterior
    by_contra hnotForced
    exact hnoGap ⟨e, heInterior, hnotForced⟩
  exact hnotCoverage
    (data.forcedEdgeCoverage_of_interiorEdgeSupport_subset_enumeratedForcedEdges
      emb p0Inside p4Inside side hInteriorForced)

/--
Classifier worklist form of coverage failure.  If exact forced-edge coverage fails, then the
canonical interior-support worklist still has a concrete unprocessed edge, and erasing it strictly
decreases the remaining-worklist measure.
-/
theorem exists_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_not_forcedEdgeCoverage
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hnotCoverage :
      ¬ (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)) :
    ∃ e : G.edgeSet,
      e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
        ((classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
          (classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
  rcases
      data.exists_interiorEdgeSupportEdge_not_enumeratedForcedEdge_of_not_forcedEdgeCoverage
        emb p0Inside p4Inside side hnotCoverage with
    ⟨e, heInterior, hnotForced⟩
  have heRemaining :
      e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces) := by
    refine
      (classifier.mem_remainingControlEdges_iff
        (interiorEdgeSupport emb.faceBoundary emb.faces) e).2 ⟨heInterior, ?_⟩
    intro heEmitted
    exact hnotForced ((classifier.emittedFinset_spec e).1 heEmitted)
  exact ⟨e, heRemaining,
    classifier.card_erase_remainingControlEdges_lt_of_mem
      (interiorEdgeSupport emb.faceBoundary emb.faces) heRemaining⟩

/--
No-missing-evidence consequence of the cardinality handoff.  If the finite CAP5 sweep has no
latent with missing checker evidence, then the cardinality-gap branch supplies a nonzero
selected-boundary-zero chain vanishing on every enumerated forced edge; equivalently, those
enumerated forced edges cannot meet every nonzero selected-boundary-zero chain.
-/
theorem noMissingCheckerEvidence_refutes_forcedEdgeCoverage_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (colorings : Set (G.EdgeColoring Color))
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hred :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnoMissing :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge →
          ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
            boundaryEdge side latent).MissingCheckerEvidence) :
    ¬ (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      z ≠ 0 →
        ∃ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0) := by
  intro hcoverage
  have hreport :=
    data.ofDecidableChecks_missingCheckerEvidence_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb colorings p0Inside p4Inside h side hcyclic hportal_crosses hcycles
      classifier controlEdges hcard hcontrol hred hblue
  rcases hreport with hmissing | hcomplete
  · rcases hmissing with ⟨latent, hmem, hmissing⟩
    exact hnoMissing latent hmem hmissing
  · rcases hcomplete with ⟨_, hpayloadAndWitness⟩
    rcases hpayloadAndWitness with ⟨_, hwitness⟩
    rcases hwitness with ⟨z, hzBoundary, hzNonzero, hzForcedZero, _⟩
    exact
      (data.forcedEdgeCoverage_refutes_boundaryZeroChain_vanishing_on_forcedEdges
        emb p0Inside p4Inside side hcoverage)
        ⟨z, hzBoundary, hzNonzero, hzForcedZero⟩

/--
Detector-payload form of exact forced-edge coverage for an arbitrary chain family.  A concrete
nonzero chain hit by the CAP5 coverage predicate yields the named one-edge indicator path-xor
payload from the enumerated forced edge that hits it.
-/
theorem forcedEdgeCoverage_forces_indicatorPayload_of_chain
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (chain : (G.edgeSet → Color) → Prop)
    (z : G.edgeSet → Color)
    (hzChain : chain z)
    (hzNonzero : z ≠ 0)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        chain z →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side := by
  rcases hcoverage hzChain hzNonzero with ⟨e, heForced, _⟩
  exact data.forcedEdgeIndicatorPathXorDetectorPayload_of_enumeratedExceptionalAnnulusForcedEdge
    heForced

/--
Detector-payload form of exact forced-edge coverage.  A concrete nonzero selected-boundary-zero
chain hit by the CAP5 coverage predicate yields the named one-edge indicator path-xor payload
from the enumerated forced edge that hits it.
-/
theorem forcedEdgeCoverage_forces_indicatorPayload_of_boundaryZeroChain
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (z : G.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule emb)
    (hzNonzero : z ≠ 0)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side := by
  exact data.forcedEdgeCoverage_forces_indicatorPayload_of_chain
    p0Inside p4Inside side (fun z => z ∈ planarBoundaryZeroSubmodule emb)
    z hzBoundary hzNonzero hcoverage

/--
Negative detector form for an arbitrary chain family.  Once the chain family has a nonzero
member, exact forced-edge coverage would emit an indicator payload; absence of that payload
therefore refutes the coverage predicate.
-/
theorem noIndicatorPayload_refutes_forcedEdgeCoverage_of_nonzero_chain
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (chain : (G.edgeSet → Color) → Prop)
    (hexists : ∃ z : G.edgeSet → Color, chain z ∧ z ≠ 0)
    (hnoPayload :
      ¬ data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side) :
    ¬ (∀ ⦃z : G.edgeSet → Color⦄,
        chain z →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) := by
  intro hcoverage
  rcases hexists with ⟨z, hzChain, hzNonzero⟩
  exact hnoPayload
    (data.forcedEdgeCoverage_forces_indicatorPayload_of_chain
      p0Inside p4Inside side chain z hzChain hzNonzero hcoverage)

/--
Boundary-zero specialization of the negative detector.  A nonzero selected-boundary-zero chain
plus absence of the one-edge indicator payload refutes exact CAP5 coverage of all nonzero
selected-boundary-zero chains.
-/
theorem noIndicatorPayload_refutes_forcedEdgeCoverage_of_nonzero_boundaryZeroChain
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hexists :
      ∃ z : G.edgeSet → Color, z ∈ planarBoundaryZeroSubmodule emb ∧ z ≠ 0)
    (hnoPayload :
      ¬ data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side) :
    ¬ (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) := by
  exact data.noIndicatorPayload_refutes_forcedEdgeCoverage_of_nonzero_chain
    p0Inside p4Inside side (fun z => z ∈ planarBoundaryZeroSubmodule emb)
    hexists hnoPayload

/--
Singleton-support form of forced-edge coverage.  If a nonzero selected-boundary-zero chain can
only be nonzero at one target edge, then any CAP5 coverage predicate for all nonzero
selected-boundary-zero chains must enumerate that target edge as forced.
-/
theorem forcedEdgeCoverage_forces_edge_of_boundaryZero_singletonSupport
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (target : G.edgeSet) (z : G.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule emb)
    (hzTarget : z target ≠ 0)
    (hzOnly : ∀ ⦃e : G.edgeSet⦄, z e ≠ 0 → e = target)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side target := by
  have hzNonzero : z ≠ 0 := by
    intro hzero
    exact hzTarget (congrFun hzero target)
  rcases hcoverage hzBoundary hzNonzero with ⟨e, heForced, hze⟩
  have heq : e = target := hzOnly hze
  simpa [heq] using heForced

/--
Singleton-support detector-payload form of forced-edge coverage.  This packages the common
finite-lab pattern where a singleton-support boundary-zero witness forces its target edge and
therefore emits the one-edge indicator path-xor detector payload.
-/
theorem forcedEdgeCoverage_forces_indicatorPayload_of_boundaryZero_singletonSupport
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (target : G.edgeSet) (z : G.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule emb)
    (hzTarget : z target ≠ 0)
    (hzOnly : ∀ ⦃e : G.edgeSet⦄, z e ≠ 0 → e = target)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side := by
  exact data.forcedEdgeIndicatorPathXorDetectorPayload_of_enumeratedExceptionalAnnulusForcedEdge
    (data.forcedEdgeCoverage_forces_edge_of_boundaryZero_singletonSupport
      emb p0Inside p4Inside side target z hzBoundary hzTarget hzOnly hcoverage)

/--
Classifier-facing singleton-support form of forced-edge coverage.  The Boolean classifier
emitted set is certified to be exactly the CAP5 enumerated forced-edge predicate, so the same
singleton boundary-zero witness forces the target edge into `classifier.emittedFinset`.
-/
theorem forcedEdgeCoverage_forces_emittedFinset_mem_of_boundaryZero_singletonSupport
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (target : G.edgeSet) (z : G.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule emb)
    (hzTarget : z target ≠ 0)
    (hzOnly : ∀ ⦃e : G.edgeSet⦄, z e ≠ 0 → e = target)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    target ∈ classifier.emittedFinset := by
  exact (classifier.emittedFinset_spec target).2
    (data.forcedEdgeCoverage_forces_edge_of_boundaryZero_singletonSupport
      emb p0Inside p4Inside side target z hzBoundary hzTarget hzOnly hcoverage)

/--
Lower-bound form of the no-missing-evidence cardinality handoff.  If the enumerated CAP5 forced
edges meet every nonzero selected-boundary-zero chain, then the emitted forced-edge count plus
the selected-boundary edge count must reach the whole edge count.
-/
theorem forcedEdgeCoverage_emittedFinset_card_add_boundary_card_ge_of_noMissingCheckerEvidence_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (colorings : Set (G.EdgeColoring Color))
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hred :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblue :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnoMissing :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge →
          ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
            boundaryEdge side latent).MissingCheckerEvidence)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    Fintype.card G.edgeSet ≤
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} := by
  by_contra hnot
  have hcard :
      classifier.emittedFinset.card +
        Fintype.card {e : G.edgeSet //
          e ∈ selectedBoundarySupport emb.faceBoundary emb.faces emb.faces} <
        Fintype.card G.edgeSet :=
    Nat.lt_of_not_ge hnot
  exact
    (data.noMissingCheckerEvidence_refutes_forcedEdgeCoverage_of_emittedFinset_card_add_boundary_card_lt_of_finsetControl
      emb colorings p0Inside p4Inside h side hcyclic hportal_crosses hcycles
      classifier controlEdges hcard hcontrol hred hblue hnoMissing) hcoverage

/--
Executable histogram-to-algebraic-handoff state for the CAP5 generator.  A decidable finite
CAP5 sweep either identifies a latent whose primitive checker evidence is still missing, or else
the complete cyclic-five histogram is `(0, 0, 16)` and the same run reaches the compact
boundary-zero algebraic lane: Theorem 4.9 synthesis closes, or the forced-bin detector is paired
with a nonzero selected-boundary-zero chain that has nonzero family pairing.
-/
theorem ofDecidableChecks_missingCheckerEvidence_or_histogram_and_theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).MissingCheckerEvidence) ∨
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).partialLatents.length = 0 ∧
          (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
            boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
        (Theorem49BoundaryRootSynthesis emb C₀ ∨
          data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
            ∃ z : G.edgeSet → Color,
              z ∈ planarBoundaryZeroSubmodule emb ∧
                z ≠ 0 ∧
                  (∀ e : G.edgeSet,
                    data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                      z e = 0) ∧
                    ∃ i : κ,
                      chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0) := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks boundaryEdge side
  by_cases hmissingEmpty : report.missingCheckerEvidenceLatents = []
  · right
    rcases report.all_checker_evidence_of_missingCheckerEvidenceLatents_eq_nil
        hmissingEmpty with
      ⟨hportal, hsideCycles⟩
    have hhist :
        report.realizedSeparatorLatents.length = 0 ∧
          report.partialLatents.length = 0 ∧
            report.forcedCounterexampleLatents.length = 16 :=
      report.histogram_lengths_eq_of_complete_of_cyclicallyFiveEdgeConnected
        hcyclic hportal hsideCycles
    exact
      ⟨by simpa [report] using hhist,
        data.theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_finsetControl
          emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic
          hportal_crosses hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue
          hwitnessExtensionRed hwitnessExtensionBlue⟩
  · left
    rcases (report.missingCheckerEvidenceLatents_ne_nil_iff_exists_missingCheckerEvidence).1
        hmissingEmpty with
      ⟨latent, hmem, hmissing⟩
    exact ⟨latent, hmem, by
      simpa [report, CAP5ExceptionalAnnulusGeneratorReport.node,
        CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hmissing⟩

/--
Executable histogram-to-canonical-family state for the CAP5 generator.  A decidable finite CAP5
sweep either identifies a latent whose primitive checker evidence is still missing, or else its
complete cyclic-five histogram is `(0, 0, 16)` and the same run reaches the canonical red/blue
single-coordinate detector branch over the next remaining-control worklist.
-/
theorem ofDecidableChecks_missingCheckerEvidence_or_histogram_and_theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).MissingCheckerEvidence) ∨
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).partialLatents.length = 0 ∧
          (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
            boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
        (Theorem49BoundaryRootSynthesis emb C₀ ∨
          data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
            ∃ z : G.edgeSet → Color,
              z ∈ planarBoundaryZeroSubmodule emb ∧
                z ≠ 0 ∧
                  (∀ e : G.edgeSet,
                    data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                      z e = 0) ∧
                    ∃ e : G.edgeSet,
                      (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                        e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                        e ∈ classifier.remainingControlEdges controlEdges ∧
                          ¬ data.EnumeratedExceptionalAnnulusForcedEdge
                            p0Inside p4Inside side e ∧
                            z e ≠ 0 ∧
                              ((classifier.remainingControlEdges controlEdges).erase e).card <
                                (classifier.remainingControlEdges controlEdges).card ∧
                                ∃ i :
                                  ({e : G.edgeSet //
                                    e ∈ classifier.remainingControlEdges controlEdges} × Bool),
                                  chainDotBilinForm G.edgeSet
                                      (redBlueSingleCoordinateFamily
                                        (classifier.remainingControlEdges controlEdges)
                                        hredRemaining hblueRemaining i :
                                        G.edgeSet → Color) z ≠ 0) := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks boundaryEdge side
  by_cases hmissingEmpty : report.missingCheckerEvidenceLatents = []
  · right
    rcases report.all_checker_evidence_of_missingCheckerEvidenceLatents_eq_nil
        hmissingEmpty with
      ⟨hportal, hsideCycles⟩
    have hhist :
        report.realizedSeparatorLatents.length = 0 ∧
          report.partialLatents.length = 0 ∧
            report.forcedCounterexampleLatents.length = 16 :=
      report.histogram_lengths_eq_of_complete_of_cyclicallyFiveEdgeConnected
        hcyclic hportal hsideCycles
    exact
      ⟨by simpa [report] using hhist,
        data.theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_finsetControl
          emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
          hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted
          hredRemaining hblueRemaining⟩
  · left
    rcases (report.missingCheckerEvidenceLatents_ne_nil_iff_exists_missingCheckerEvidence).1
        hmissingEmpty with
      ⟨latent, hmem, hmissing⟩
    exact ⟨latent, hmem, by
      simpa [report, CAP5ExceptionalAnnulusGeneratorReport.node,
        CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hmissing⟩

/--
Executable histogram-to-canonical-family state with explicit residual progress.  Once the finite
checker is complete, the failure branch carries the concrete extension edge into the residual
worklist state and proves that recording it as processed strictly decreases that residual
measure.
-/
theorem ofDecidableChecks_missingCheckerEvidence_or_histogram_and_theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_and_residualProgress_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (controlEdges processed : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnotProcessed :
      ∀ e ∈ classifier.remainingControlEdges controlEdges, e ∉ processed) :
    (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).MissingCheckerEvidence) ∨
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).partialLatents.length = 0 ∧
          (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
            boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
        (Theorem49BoundaryRootSynthesis emb C₀ ∨
          data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
            ∃ z : G.edgeSet → Color,
              z ∈ planarBoundaryZeroSubmodule emb ∧
                z ≠ 0 ∧
                  (∀ e : G.edgeSet,
                    data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                      z e = 0) ∧
                    ∃ e : G.edgeSet,
                      (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                        e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                        e ∈ classifier.remainingControlEdges controlEdges ∧
                          e ∈ classifier.residualRemainingControlEdges controlEdges
                            processed ∧
                            ¬ data.EnumeratedExceptionalAnnulusForcedEdge
                              p0Inside p4Inside side e ∧
                              z e ≠ 0 ∧
                                (classifier.residualRemainingControlEdges controlEdges
                                    (insert e processed)).card <
                                  (classifier.residualRemainingControlEdges controlEdges
                                    processed).card ∧
                                  ((classifier.remainingControlEdges controlEdges).erase e).card <
                                    (classifier.remainingControlEdges controlEdges).card ∧
                                    ∃ i :
                                      ({e : G.edgeSet //
                                        e ∈ classifier.remainingControlEdges controlEdges} × Bool),
                                      chainDotBilinForm G.edgeSet
                                          (redBlueSingleCoordinateFamily
                                            (classifier.remainingControlEdges controlEdges)
                                            hredRemaining hblueRemaining i :
                                            G.edgeSet → Color) z ≠ 0) := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks boundaryEdge side
  by_cases hmissingEmpty : report.missingCheckerEvidenceLatents = []
  · right
    rcases report.all_checker_evidence_of_missingCheckerEvidenceLatents_eq_nil
        hmissingEmpty with
      ⟨hportal, hsideCycles⟩
    have hhist :
        report.realizedSeparatorLatents.length = 0 ∧
          report.partialLatents.length = 0 ∧
            report.forcedCounterexampleLatents.length = 16 :=
      report.histogram_lengths_eq_of_complete_of_cyclicallyFiveEdgeConnected
        hcyclic hportal hsideCycles
    exact
      ⟨by simpa [report] using hhist,
        data.theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_and_residualProgress_of_finsetControl
          emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
          hcycles classifier controlEdges processed hcontrol hredEmitted hblueEmitted
          hredRemaining hblueRemaining hnotProcessed⟩
  · left
    rcases (report.missingCheckerEvidenceLatents_ne_nil_iff_exists_missingCheckerEvidence).1
        hmissingEmpty with
      ⟨latent, hmem, hmissing⟩
    exact ⟨latent, hmem, by
      simpa [report, CAP5ExceptionalAnnulusGeneratorReport.node,
        CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hmissing⟩

/--
Failure-branch form of the executable CAP5 generator.  If the current CAP5 runner does not
already close Theorem 4.9, then a decidable finite sweep either reports exactly which primitive
checker evidence is still missing, or else its complete cyclic-five histogram is `(0, 0, 16)`
and it exposes the forced-bin detector together with a nonzero selected-boundary-zero chain
having nonzero family pairing.  This is the concrete obstruction output to inspect before
returning to any planar/Jordan realization route.
-/
theorem ofDecidableChecks_missingCheckerEvidence_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
              Pi.single e blue)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).MissingCheckerEvidence) ∨
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).partialLatents.length = 0 ∧
          (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
            boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
        data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
          ∃ z : G.edgeSet → Color,
            z ∈ planarBoundaryZeroSubmodule emb ∧
              z ≠ 0 ∧
                (∀ e : G.edgeSet,
                  data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                    z e = 0) ∧
                  ∃ i : κ,
                    chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  rcases data.ofDecidableChecks_missingCheckerEvidence_or_histogram_and_theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_finsetControl
      emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue
      hwitnessExtensionRed hwitnessExtensionBlue with
    hmissing | hcomplete
  · exact Or.inl hmissing
  · rcases hcomplete with ⟨hhist, hclosed_or_fallback⟩
    rcases hclosed_or_fallback with hclosed | hfallback
    · exact False.elim (hnotSynthesis hclosed)
    · exact Or.inr ⟨hhist, hfallback⟩

/--
Failure-branch executable CAP5 generator with canonical red/blue single-coordinate families.
If Theorem 4.9 does not close, the completed checker branch exposes the forced-bin detector,
the concrete nonzero extension edge, and the canonical remaining-worklist pairing witness.
-/
theorem ofDecidableChecks_missingCheckerEvidence_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).MissingCheckerEvidence) ∨
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).partialLatents.length = 0 ∧
          (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
            boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
        data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
          ∃ z : G.edgeSet → Color,
            z ∈ planarBoundaryZeroSubmodule emb ∧
              z ≠ 0 ∧
                (∀ e : G.edgeSet,
                  data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                    z e = 0) ∧
                  ∃ e : G.edgeSet,
                    (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                      e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                      e ∈ classifier.remainingControlEdges controlEdges ∧
                        ¬ data.EnumeratedExceptionalAnnulusForcedEdge
                          p0Inside p4Inside side e ∧
                          z e ≠ 0 ∧
                            ((classifier.remainingControlEdges controlEdges).erase e).card <
                              (classifier.remainingControlEdges controlEdges).card ∧
                              ∃ i :
                                ({e : G.edgeSet //
                                  e ∈ classifier.remainingControlEdges controlEdges} × Bool),
                                chainDotBilinForm G.edgeSet
                                    (redBlueSingleCoordinateFamily
                                      (classifier.remainingControlEdges controlEdges)
                                      hredRemaining hblueRemaining i :
                                      G.edgeSet → Color) z ≠ 0 := by
  rcases data.ofDecidableChecks_missingCheckerEvidence_or_histogram_and_theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining
      hblueRemaining with
    hmissing | hcomplete
  · exact Or.inl hmissing
  · rcases hcomplete with ⟨hhist, hclosed_or_fallback⟩
    rcases hclosed_or_fallback with hclosed | hfallback
    · exact False.elim (hnotSynthesis hclosed)
    · exact Or.inr ⟨hhist, hfallback⟩

/--
Exact-coverage runner closure for the canonical-family CAP5 handoff.  If the finite checker has
no missing primitive evidence and the enumerated forced edges meet every nonzero
selected-boundary-zero chain, then the completed runner cannot return the path-xor evader
branch; the only remaining completed branch is Theorem 4.9 boundary-root synthesis.
-/
theorem theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_noMissingCheckerEvidence_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnoMissing :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge →
          ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
            boundaryEdge side latent).MissingCheckerEvidence)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases data.ofDecidableChecks_missingCheckerEvidence_or_histogram_and_theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining
      hblueRemaining with
    hmissing | hcomplete
  · rcases hmissing with ⟨latent, hmem, hmissing⟩
    exact False.elim (hnoMissing latent hmem hmissing)
  · rcases hcomplete with ⟨_hhist, hclosed_or_fallback⟩
    rcases hclosed_or_fallback with hclosed | hfallback
    · exact hclosed
    · rcases hfallback with ⟨_payload, z, hzBoundary, hzNonzero, hzForcedZero, _⟩
      exact False.elim
        ((data.forcedEdgeCoverage_refutes_boundaryZeroChain_vanishing_on_forcedEdges
          emb p0Inside p4Inside side hcoverage)
          ⟨z, hzBoundary, hzNonzero, hzForcedZero⟩)

/--
No-evader runner closure for the canonical-family CAP5 handoff.  This is the finite `F₂`
verdict in its most direct form: if no nonzero selected-boundary-zero chain can vanish on every
enumerated forced edge, then the exact-coverage runner closure applies.
-/
theorem theorem49BoundaryRootSynthesis_of_no_boundaryZeroChain_vanishing_on_forcedEdges_of_noMissingCheckerEvidence_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnoMissing :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge →
          ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
            boundaryEdge side latent).MissingCheckerEvidence)
    (hnoEvader :
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  data.theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_noMissingCheckerEvidence_of_finsetControl
    emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
    hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining
    hblueRemaining hnoMissing
    ((data.forcedEdgeCoverage_iff_no_boundaryZeroChain_vanishing_on_forcedEdges
      emb p0Inside p4Inside side).2 hnoEvader)

/--
No-indicator-payload runner closure for the canonical-family CAP5 handoff.  If the finite
checker has no missing primitive evidence and the forced-bin one-edge indicator payload is
absent, then the completed runner cannot return its path-xor fallback; the only remaining
completed branch is Theorem 4.9 boundary-root synthesis.
-/
theorem theorem49BoundaryRootSynthesis_of_noIndicatorPayload_of_noMissingCheckerEvidence_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnoMissing :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge →
          ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
            boundaryEdge side latent).MissingCheckerEvidence)
    (hnoPayload :
      ¬ data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  rcases data.ofDecidableChecks_missingCheckerEvidence_or_histogram_and_theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining
      hblueRemaining with
    hmissing | hcomplete
  · rcases hmissing with ⟨latent, hmem, hmissing⟩
    exact False.elim (hnoMissing latent hmem hmissing)
  · rcases hcomplete with ⟨_hhist, hclosed_or_fallback⟩
    rcases hclosed_or_fallback with hclosed | hfallback
    · exact hclosed
    · exact False.elim (hnoPayload hfallback.1)

/--
Primitive-frontier form of the CAP5 failure detector.  If Theorem 4.9 does not already close,
the finite CAP5 sweep either names a concrete missing checker ingredient--portal crossings,
the selected-side cycle, or the complementary-side cycle--or else the full cyclic-five
histogram is `(0, 0, 16)` and the run reaches the algebraic boundary-zero obstruction.
-/
theorem ofDecidableChecks_missing_checker_ingredient_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
              Pi.single e blue)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
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
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).partialLatents.length = 0 ∧
          (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
            boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
        data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
          ∃ z : G.edgeSet → Color,
            z ∈ planarBoundaryZeroSubmodule emb ∧
              z ≠ 0 ∧
                (∀ e : G.edgeSet,
                  data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                    z e = 0) ∧
                  ∃ i : κ,
                    chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  rcases data.ofDecidableChecks_missingCheckerEvidence_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
      emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue
      hwitnessExtensionRed hwitnessExtensionBlue hnotSynthesis with
    hmissing | hcomplete
  · left
    rcases hmissing with ⟨latent, hmem, hmissing⟩
    rcases ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).missingCheckerEvidence_iff_missing_ingredient).1
        hmissing with hportal | hcycle
    · exact Or.inl ⟨latent, hmem, hportal⟩
    · rcases hcycle with hselected | hcomplement
      · exact Or.inr <| Or.inl ⟨latent, hmem, hselected⟩
      · exact Or.inr <| Or.inr ⟨latent, hmem, hcomplement⟩
  · exact Or.inr hcomplete

/--
Primitive-frontier executable CAP5 failure detector with canonical red/blue families.  The
completed branch carries the histogram, forced-bin detector, concrete extension edge, worklist
decrease, and canonical pairing witness.
-/
theorem ofDecidableChecks_missing_checker_ingredient_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
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
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).partialLatents.length = 0 ∧
          (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
            boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
        data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
          ∃ z : G.edgeSet → Color,
            z ∈ planarBoundaryZeroSubmodule emb ∧
              z ≠ 0 ∧
                (∀ e : G.edgeSet,
                  data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                    z e = 0) ∧
                  ∃ e : G.edgeSet,
                    (e ∈ classifier.crossingExtensionFinset controlEdges ∨
                      e ∈ classifier.noncrossingExtensionFinset controlEdges) ∧
                      e ∈ classifier.remainingControlEdges controlEdges ∧
                        ¬ data.EnumeratedExceptionalAnnulusForcedEdge
                          p0Inside p4Inside side e ∧
                          z e ≠ 0 ∧
                            ((classifier.remainingControlEdges controlEdges).erase e).card <
                              (classifier.remainingControlEdges controlEdges).card ∧
                              ∃ i :
                                ({e : G.edgeSet //
                                  e ∈ classifier.remainingControlEdges controlEdges} × Bool),
                                chainDotBilinForm G.edgeSet
                                    (redBlueSingleCoordinateFamily
                                      (classifier.remainingControlEdges controlEdges)
                                      hredRemaining hblueRemaining i :
                                      G.edgeSet → Color) z ≠ 0 := by
  rcases data.ofDecidableChecks_missingCheckerEvidence_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining
      hblueRemaining hnotSynthesis with
    hmissing | hcomplete
  · left
    rcases hmissing with ⟨latent, hmem, hmissing⟩
    rcases ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).missingCheckerEvidence_iff_missing_ingredient).1
        hmissing with hportal | hcycle
    · exact Or.inl ⟨latent, hmem, hportal⟩
    · rcases hcycle with hselected | hcomplement
      · exact Or.inr <| Or.inl ⟨latent, hmem, hselected⟩
      · exact Or.inr <| Or.inr ⟨latent, hmem, hcomplement⟩
  · exact Or.inr hcomplete

/--
Exact-coverage primitive frontier for the canonical-family CAP5 detector.  If Theorem 4.9
synthesis still fails after the forced-edge detector meets every nonzero selected-boundary-zero
chain, the algebraic path-xor fallback is impossible; the finite checker must name the missing
primitive ingredient.
-/
theorem missing_checker_ingredient_of_not_theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
              boundaryEdge side latent).MissingComplementarySideCycleEvidence) := by
  rcases data.ofDecidableChecks_missing_checker_ingredient_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining
      hblueRemaining hnotSynthesis with
    hmissing | hcomplete
  · exact hmissing
  · rcases hcomplete with ⟨_hhist, _payload, z, hzBoundary, hzNonzero, hzForcedZero, _⟩
    exact False.elim
      ((data.forcedEdgeCoverage_refutes_boundaryZeroChain_vanishing_on_forcedEdges
        emb p0Inside p4Inside side hcoverage)
        ⟨z, hzBoundary, hzNonzero, hzForcedZero⟩)

/--
Total failed-synthesis frontier for the canonical-family CAP5 detector.  If Theorem 4.9
synthesis does not close, the finite checker must either name a missing primitive ingredient,
or the enumerated forced edges fail exact coverage of the nonzero selected-boundary-zero chains.
-/
theorem missing_checker_ingredient_or_not_forcedEdgeCoverage_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
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
      ¬ (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) := by
  by_cases hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0
  · exact Or.inl
      (data.missing_checker_ingredient_of_not_theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_finsetControl
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted
        hredRemaining hblueRemaining hcoverage hnotSynthesis)
  · exact Or.inr hcoverage

/--
No-indicator-payload primitive frontier for the canonical-family CAP5 detector.  If Theorem 4.9
synthesis still fails and the forced-bin indicator payload is absent, the completed algebraic
fallback branch is impossible; the finite checker must name the missing primitive ingredient.
-/
theorem missing_checker_ingredient_of_not_theorem49BoundaryRootSynthesis_of_noIndicatorPayload_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnoPayload :
      ¬ data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
              boundaryEdge side latent).MissingComplementarySideCycleEvidence) := by
  rcases data.ofDecidableChecks_missing_checker_ingredient_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining
      hblueRemaining hnotSynthesis with
    hmissing | hcomplete
  · exact hmissing
  · rcases hcomplete with ⟨_hhist, hpayload, _⟩
    exact False.elim (hnoPayload hpayload)

/--
Exact-coverage active-branch frontier for the canonical-family CAP5 detector.  Under the
active portal-side crossing hypotheses and the two side-cycle hypotheses, exact forced-edge
coverage rules out every synthesis-failure branch except a portal-crossing checker gap for a
latent that is not the active exceptional orientation with the active portal-side bits.
-/
theorem offBranch_missingPortalCrossingEvidence_of_not_theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).MissingPortalCrossingEvidence ∧
          ¬ (data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
            latent.p0Inside = p0Inside ∧ latent.p4Inside = p4Inside) := by
  rcases data.missing_checker_ingredient_of_not_theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
      classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining hblueRemaining
      hcoverage hnotSynthesis with
    hportal | hcycle
  · rcases hportal with ⟨latent, hmem, hmissingPortal⟩
    refine ⟨latent, hmem, hmissingPortal, ?_⟩
    rintro ⟨horientation, hp0, hp4⟩
    let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
      { latent := latent, side := side }
    have hnodePortal : node.PortalCrosses := by
      intro i hi
      have horientation' :
          data.RealizesExceptionalBoundarySupportOrientation
            node.candidate.portalCandidate.orientation := by
        simpa [node] using horientation
      have hsideCase :
          node.candidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside := by
        change CAP5ExceptionalAnnulusSideCase.ofPortalSides
            node.latent.p0Inside node.latent.p4Inside =
          CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside
        rw [hp0, hp4]
      exact hportal_crosses node.candidate horientation' hsideCase i hi
    exact hmissingPortal (by
      simpa [CAP5ExceptionalAnnulusGeneratorReport.latentNode, node] using hnodePortal)
  · rcases hcycle with hselected | hcomplement
    · rcases hselected with ⟨latent, _hmem, hmissingSelected⟩
      exact False.elim (hmissingSelected (by
        simpa [CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hcycles.1))
    · rcases hcomplement with ⟨latent, _hmem, hmissingComplement⟩
      exact False.elim (hmissingComplement (by
        simpa [CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hcycles.2))

/--
Exact-coverage closed-frontier theorem for the canonical-family CAP5 detector.  If the finite
checker has no missing primitive ingredient and the forced-edge detector meets every nonzero
selected-boundary-zero chain, a failed synthesis run has no remaining branch.
-/
theorem theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_no_missing_checker_ingredient_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  by_contra hnotSynthesis
  exact hnoMissing
    (data.missing_checker_ingredient_of_not_theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
      classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining hblueRemaining
      hcoverage hnotSynthesis)

/--
No-evader closed-frontier theorem for the canonical-family CAP5 detector.  Once the primitive
checker frontier is closed, the finite `F₂` no-evader verdict is enough to close synthesis.
-/
theorem theorem49BoundaryRootSynthesis_of_no_boundaryZeroChain_vanishing_on_forcedEdges_of_no_missing_checker_ingredient_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnoEvader :
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  data.theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_no_missing_checker_ingredient_of_finsetControl
    emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
    classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining hblueRemaining
    ((data.forcedEdgeCoverage_iff_no_boundaryZeroChain_vanishing_on_forcedEdges
      emb p0Inside p4Inside side).2 hnoEvader)
    hnoMissing

/--
Full boundary-zero classifier-control handoff for the Move-2 oracle.  A completed CAP5 checker
with no nonzero selected-boundary-zero evader does not only close synthesis: the same F2 verdict
proves that the emitted classifier coordinates control the whole selected-boundary-zero
subspace.
-/
theorem theorem49BoundaryRootSynthesis_and_boundaryZeroClassifierControl_of_no_boundaryZeroEvader_of_no_missing_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnoEvader :
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0) := by
  exact
    ⟨data.theorem49BoundaryRootSynthesis_of_no_boundaryZeroChain_vanishing_on_forcedEdges_of_no_missing_checker_ingredient_of_finsetControl
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining
        hblueRemaining hnoEvader hnoMissing,
      (data.enumeratedExceptionalAnnulusForcedEdgeClassifierBoundaryZeroControl_iff_no_boundaryZeroEvader
        emb p0Inside p4Inside side classifier).2 hnoEvader⟩

/--
Move-2 handoff for the full F2 no-evader verdict.  A completed CAP5 finite checker with no
selected-boundary-zero evader both closes theorem-4.9 synthesis and proves that the classifier
controls the actual boundary-root target `W0(H)`.
-/
theorem theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_no_evader_of_no_missing_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnoEvader :
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) := by
  have hsynthesis :
      Theorem49BoundaryRootSynthesis emb C₀ :=
    data.theorem49BoundaryRootSynthesis_of_no_boundaryZeroChain_vanishing_on_forcedEdges_of_no_missing_checker_ingredient_of_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining
      hblueRemaining hnoEvader hnoMissing
  have hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0 :=
    (data.forcedEdgeCoverage_iff_no_boundaryZeroChain_vanishing_on_forcedEdges
      emb p0Inside p4Inside side).2 hnoEvader
  have htarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0 := by
    intro z hzTarget hzNonzero
    exact hcoverage
      ((theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
        emb (Theorem49BoundaryVertices emb)) (by
          simpa [Theorem49BoundaryTarget, Theorem49BoundaryVertices] using hzTarget))
      hzNonzero
  exact ⟨hsynthesis, htarget⟩

/--
Target-control closure theorem for the current Move-2 fork.  Controlling the theorem-4.9 target
`W0(H)` is enough to close the canonical CAP5 runner exactly when every remaining
selected-boundary-zero evader would already lie in that target.  Thus the only extra algebraic
burden beyond target classifier control is the absence of an off-target boundary-zero evader.
-/
theorem theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_no_offTargetBoundaryZeroEvader_of_no_missing_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcontrolTarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)
    (hnoOffTargetEvader :
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ∉ Theorem49BoundaryTarget emb ∧
            z ≠ 0 ∧
              ∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) := by
  have hnoEvader :
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0 := by
    rintro ⟨z, hzBoundary, hzNonzero, hzForcedZero⟩
    by_cases hzTarget : z ∈ Theorem49BoundaryTarget emb
    · have hzEmittedZero :
          ∀ e ∈ classifier.emittedFinset, z e = 0 := by
        intro e heEmitted
        exact hzForcedZero e ((classifier.emittedFinset_spec e).1 heEmitted)
      exact hzNonzero (hcontrolTarget hzTarget hzEmittedZero)
    · exact hnoOffTargetEvader ⟨z, hzBoundary, hzTarget, hzNonzero, hzForcedZero⟩
  exact
    data.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_no_evader_of_no_missing_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining
      hblueRemaining hnoEvader hnoMissing

/--
Concrete form of the off-target branch.  A selected-boundary-zero chain outside the theorem-4.9
target is not an abstract complement element: it fails the Kirchhoff equation at some named
theorem-4.9 boundary vertex.
-/
theorem exists_theorem49BoundaryVertex_vertexKirchhoffSum_ne_zero_of_boundaryZero_of_not_theorem49BoundaryTarget
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    {z : G.edgeSet → Color}
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule emb)
    (hzOffTarget : z ∉ Theorem49BoundaryTarget emb) :
    ∃ v : V,
      v ∈ Theorem49BoundaryVertices emb ∧
        vertexKirchhoffSum G z v ≠ 0 := by
  by_contra hnoVertex
  exact hzOffTarget (by
    change z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
      (Theorem49BoundaryVertices emb)
    refine ⟨?_, hzBoundary⟩
    intro v hv
    by_contra hkirchhoff
    exact hnoVertex ⟨v, hv, hkirchhoff⟩)

/--
Row-span/subset form of the concrete vertex-failure oracle.  If every selected-boundary-zero
chain that vanishes on the enumerated forced edges already lies in the theorem-4.9 target, then
there is no remaining forced-edge-vanishing chain with a nonzero theorem-4.9 boundary-vertex
Kirchhoff sum.
-/
theorem no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hsubsetTarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
            z e = 0) →
          z ∈ Theorem49BoundaryTarget emb) :
    ¬ ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          (∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0) ∧
            ∃ v : V,
              v ∈ Theorem49BoundaryVertices emb ∧
                vertexKirchhoffSum G z v ≠ 0 := by
  rintro ⟨z, hzBoundary, _hzNonzero, hzForcedZero, v, hv, hvNonzero⟩
  have hzTarget : z ∈ Theorem49BoundaryTarget emb :=
    hsubsetTarget hzBoundary hzForcedZero
  have hzKirchhoff :
      z ∈ theorem49BoundaryZeroKirchhoffSubspace emb
        (Theorem49BoundaryVertices emb) := by
    simpa [Theorem49BoundaryTarget, Theorem49BoundaryVertices] using hzTarget
  exact hvNonzero (hzKirchhoff.1 v hv)

/--
Converse row-span/subset frontier.  Failure of the subset certificate is already a genuine
forced-edge-vanishing selected-boundary-zero evader with a concrete nonzero theorem-4.9
boundary-vertex Kirchhoff sum.
-/
theorem boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_not_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hnotSubset :
      ¬ ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
            z e = 0) →
          z ∈ Theorem49BoundaryTarget emb) :
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          (∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0) ∧
            ∃ v : V,
              v ∈ Theorem49BoundaryVertices emb ∧
                vertexKirchhoffSum G z v ≠ 0 := by
  classical
  push Not at hnotSubset
  rcases hnotSubset with ⟨z, hzBoundary, hzForcedZero, hzOffTarget⟩
  have hzNonzero : z ≠ 0 := by
    intro hzero
    apply hzOffTarget
    rw [hzero]
    change (0 : G.edgeSet → Color) ∈ theorem49BoundaryZeroKirchhoffSubspace emb
      (Theorem49BoundaryVertices emb)
    exact Submodule.zero_mem _
  exact
    ⟨z, hzBoundary, hzNonzero, hzForcedZero,
      exists_theorem49BoundaryVertex_vertexKirchhoffSum_ne_zero_of_boundaryZero_of_not_theorem49BoundaryTarget
        emb hzBoundary hzOffTarget⟩

/--
Exact fork statement for the row-span/subset certificate.  The finite F2 subset test succeeds
precisely when there is no forced-edge-vanishing selected-boundary-zero chain with a nonzero
theorem-4.9 boundary-vertex Kirchhoff sum.  Thus a failed subset certificate is not just an
unknown complement case: it is the concrete evader demanded by the current oracle.
-/
theorem forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_iff_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
          z e = 0) →
        z ∈ Theorem49BoundaryTarget emb) ↔
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ v : V,
                v ∈ Theorem49BoundaryVertices emb ∧
                  vertexKirchhoffSum G z v ≠ 0 := by
  constructor
  · exact
      data.no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget
        emb p0Inside p4Inside side
  · intro hnoFailure z hzBoundary hzForcedZero
    by_contra hzOffTarget
    have hzNonzero : z ≠ 0 := by
      intro hzero
      apply hzOffTarget
      rw [hzero]
      change (0 : G.edgeSet → Color) ∈ theorem49BoundaryZeroKirchhoffSubspace emb
        (Theorem49BoundaryVertices emb)
      exact Submodule.zero_mem _
    exact hnoFailure
      ⟨z, hzBoundary, hzNonzero, hzForcedZero,
        exists_theorem49BoundaryVertex_vertexKirchhoffSum_ne_zero_of_boundaryZero_of_not_theorem49BoundaryTarget
          emb hzBoundary hzOffTarget⟩

/--
Empty-worklist extraction for the exact F2 fork.  Once the canonical interior-support
worklist is empty, every ambient interior-support edge is already enumerated as a CAP5
forced edge.
-/
theorem interiorEdgeSupport_subset_enumeratedForcedEdges_of_remainingInteriorSupportEmpty
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hremainingEmpty :
      classifier.remainingControlEdges (interiorEdgeSupport emb.faceBoundary emb.faces) = ∅) :
    ∀ e : G.edgeSet,
      e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
  intro e heInterior
  by_contra hnotForced
  have heRemaining :
      e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces) := by
    refine
      (classifier.mem_remainingControlEdges_iff
        (interiorEdgeSupport emb.faceBoundary emb.faces) e).2 ⟨heInterior, ?_⟩
    intro heEmitted
    exact hnotForced ((classifier.emittedFinset_spec e).1 heEmitted)
  rw [hremainingEmpty] at heRemaining
  simp at heRemaining

/--
Forced-edge coverage supplies the exact row-span/subset certificate for the current Move-2
fork: any selected-boundary-zero chain vanishing on all enumerated forced edges is forced to be
zero, hence lies in the theorem-4.9 boundary target.
-/
theorem forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_forcedEdgeCoverage
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
          z e = 0) →
        z ∈ Theorem49BoundaryTarget emb := by
  intro z hzBoundary hzForcedZero
  by_cases hzZero : z = 0
  · rw [hzZero]
    change (0 : G.edgeSet → Color) ∈ theorem49BoundaryZeroKirchhoffSubspace emb
      (Theorem49BoundaryVertices emb)
    exact Submodule.zero_mem _
  · rcases hcoverage hzBoundary hzZero with ⟨e, heForced, hze⟩
    exact False.elim (hze (hzForcedZero e heForced))

/--
All-interior forced-edge coverage proves the exact row-span/subset certificate, not merely the
older no-evader handoff.  This is the Lean form of the finite F2 all-interior survivor for the
current subset-certificate fork.
-/
theorem forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_interiorEdgeSupport_subset_enumeratedForcedEdges
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hInteriorForced :
      ∀ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
          z e = 0) →
        z ∈ Theorem49BoundaryTarget emb :=
  data.forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_forcedEdgeCoverage
    emb p0Inside p4Inside side
    (data.forcedEdgeCoverage_of_interiorEdgeSupport_subset_enumeratedForcedEdges
      emb p0Inside p4Inside side hInteriorForced)

/--
Executable empty-worklist certificate for the exact subset fork.  If the canonical
interior-support worklist is empty, the subset certificate needed by the binary F2 theorem is
already proved.
-/
theorem forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_remainingInteriorSupportEmpty
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hremainingEmpty :
      classifier.remainingControlEdges (interiorEdgeSupport emb.faceBoundary emb.faces) = ∅) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
          z e = 0) →
        z ∈ Theorem49BoundaryTarget emb :=
  data.forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_interiorEdgeSupport_subset_enumeratedForcedEdges
    emb p0Inside p4Inside side
    (data.interiorEdgeSupport_subset_enumeratedForcedEdges_of_remainingInteriorSupportEmpty
      emb p0Inside p4Inside side classifier hremainingEmpty)

/--
Empty canonical worklist rules out the concrete vertex-Kirchhoff evader branch of the current
exact F2 fork.
-/
theorem no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_remainingInteriorSupportEmpty
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hremainingEmpty :
      classifier.remainingControlEdges (interiorEdgeSupport emb.faceBoundary emb.faces) = ∅) :
    ¬ ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          (∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0) ∧
            ∃ v : V,
              v ∈ Theorem49BoundaryVertices emb ∧
                vertexKirchhoffSum G z v ≠ 0 :=
  data.no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget
    emb p0Inside p4Inside side
    (data.forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_remainingInteriorSupportEmpty
      emb p0Inside p4Inside side classifier hremainingEmpty)

/--
Kirchhoff-failure closure theorem for the current Move-2 fork.  Target classifier control leaves
only one possible selected-boundary-zero failure mode: a chain vanishing on all enumerated forced
edges whose Kirchhoff sum is nonzero at a theorem-4.9 boundary vertex.  Excluding that concrete
failure mode closes the completed CAP5 checker.
-/
theorem theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_no_missing_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcontrolTarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)
    (hnoKirchhoffFailureEvader :
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ v : V,
                v ∈ Theorem49BoundaryVertices emb ∧
                  vertexKirchhoffSum G z v ≠ 0)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) := by
  refine
    data.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_no_offTargetBoundaryZeroEvader_of_no_missing_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining
      hblueRemaining hcontrolTarget ?_ hnoMissing
  rintro ⟨z, hzBoundary, hzOffTarget, hzNonzero, hzForcedZero⟩
  exact hnoKirchhoffFailureEvader
    ⟨z, hzBoundary, hzNonzero, hzForcedZero,
      exists_theorem49BoundaryVertex_vertexKirchhoffSum_ne_zero_of_boundaryZero_of_not_theorem49BoundaryTarget
        emb hzBoundary hzOffTarget⟩

/--
Subset-certificate closure theorem for the current Move-2 oracle.  This is the Lean landing
point for the finite F2 row-span test: once target classifier control is known, it is enough to
prove that every boundary-zero chain vanishing on the enumerated forced edges is already in the
theorem-4.9 boundary target.
-/
theorem theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_no_missing_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcontrolTarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)
    (hsubsetTarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
            z e = 0) →
          z ∈ Theorem49BoundaryTarget emb)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :=
  data.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_no_missing_finsetControl
    emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
    hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining
    hblueRemaining hcontrolTarget
    (data.no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget
      emb p0Inside p4Inside side hsubsetTarget)
    hnoMissing

/--
Empty-worklist specialization of the exact subset-certificate closure.  Under target classifier
control and a closed checker, an empty canonical interior-support worklist collapses the binary
F2 fork to synthesis plus target coverage: the vertex-Kirchhoff evader branch has already been
ruled out by the subset certificate above.
-/
theorem theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_remainingInteriorSupportEmpty_of_no_missing_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcontrolTarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)
    (hremainingEmpty :
      classifier.remainingControlEdges (interiorEdgeSupport emb.faceBoundary emb.faces) = ∅)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :=
  data.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_no_missing_finsetControl
    emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
    hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining
    hblueRemaining hcontrolTarget
    (data.forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_remainingInteriorSupportEmpty
      emb p0Inside p4Inside side classifier hremainingEmpty)
    hnoMissing

/--
Binary route theorem for the current algebraic fork.  Under target classifier control and a
closed finite checker, either the subset certificate closes theorem-4.9 synthesis and target
coverage, or Lean returns the genuine forced-edge-vanishing vertex-Kirchhoff evader.  This is the
machine-checked form of the remaining F2 oracle decision.
-/
theorem theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_or_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_theorem49BoundaryTargetClassifierControl_of_no_missing_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcontrolTarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    (Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)) ∨
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ v : V,
                v ∈ Theorem49BoundaryVertices emb ∧
                  vertexKirchhoffSum G z v ≠ 0 := by
  classical
  by_cases hsubsetTarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
            z e = 0) →
          z ∈ Theorem49BoundaryTarget emb
  · left
    exact
      data.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget_of_no_missing_finsetControl
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted
        hredRemaining hblueRemaining hcontrolTarget hsubsetTarget hnoMissing
  · right
    exact
      data.boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_not_forced_vanishing_boundaryZero_subset_theorem49BoundaryTarget
        emb p0Inside p4Inside side hsubsetTarget

/--
Concrete-checker closed-frontier theorem for the canonical-family CAP5 detector.  Exact
forced-edge coverage closes synthesis once the finite checker has portal-crossing evidence for
every enumerated latent and the ambient side has cycles on both sides.
-/
theorem theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_allPortalCrosses_of_sideCycles_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v))
    (hallPortalCrosses :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).PortalCrosses)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact data.theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_no_missing_checker_ingredient_of_finsetControl
    emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
    classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining hblueRemaining
    hcoverage
    (CAP5ExceptionalAnnulusGeneratorReport.no_missing_checker_ingredient_of_allPortalCrosses_of_sideCycles
      boundaryEdge side hallPortalCrosses hcycles)

/--
Concrete-checker no-evader closed-frontier theorem for the canonical-family CAP5 detector.
Portal-crossing evidence plus side cycles close the primitive frontier; the finite `F₂`
no-evader verdict supplies the exact coverage input.
-/
theorem theorem49BoundaryRootSynthesis_of_no_boundaryZeroChain_vanishing_on_forcedEdges_of_allPortalCrosses_of_sideCycles_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v))
    (hallPortalCrosses :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).PortalCrosses)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnoEvader :
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  data.theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_allPortalCrosses_of_sideCycles_of_finsetControl
    emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
    hallPortalCrosses classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining
    hblueRemaining
    ((data.forcedEdgeCoverage_iff_no_boundaryZeroChain_vanishing_on_forcedEdges
      emb p0Inside p4Inside side).2 hnoEvader)

/--
Interior-support failure detector for the executable CAP5 generator.  If Theorem 4.9 synthesis
does not close, the finite checker either names the missing primitive evidence or, once complete,
returns the forced-bin detector together with a nonzero selected-boundary-zero chain pairing over
the canonical interior-support control set.
-/
theorem ofDecidableChecks_missing_checker_ingredient_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
        e ∈ classifier.crossingExtensionFinset
              (interiorEdgeSupport emb.faceBoundary emb.faces) ∨
            e ∈ classifier.noncrossingExtensionFinset
              (interiorEdgeSupport emb.faceBoundary emb.faces) →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessExtensionBlue :
      ∀ e : G.edgeSet,
        e ∈ classifier.crossingExtensionFinset
              (interiorEdgeSupport emb.faceBoundary emb.faces) ∨
            e ∈ classifier.noncrossingExtensionFinset
              (interiorEdgeSupport emb.faceBoundary emb.faces) →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
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
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).partialLatents.length = 0 ∧
          (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
            boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
        data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
          ∃ z : G.edgeSet → Color,
            z ∈ planarBoundaryZeroSubmodule emb ∧
              z ≠ 0 ∧
                (∀ e : G.edgeSet,
                  data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                    z e = 0) ∧
                  ∃ i : κ,
                    chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  refine
    data.ofDecidableChecks_missing_checker_ingredient_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
      emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier (interiorEdgeSupport emb.faceBoundary emb.faces) ?_
      hwitnessRed hwitnessBlue hwitnessExtensionRed hwitnessExtensionBlue hnotSynthesis
  intro z hzBoundary hcontrol
  exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    z hzBoundary hcontrol

/--
Interior-support executable CAP5 failure detector with canonical red/blue single-coordinate
families.  This is the no-extra-control frontier form for the canonical F2 detector lane.
-/
theorem ofDecidableChecks_missing_checker_ingredient_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
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
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).partialLatents.length = 0 ∧
          (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
            boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
        data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
          ∃ z : G.edgeSet → Color,
            z ∈ planarBoundaryZeroSubmodule emb ∧
              z ≠ 0 ∧
                (∀ e : G.edgeSet,
                  data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                    z e = 0) ∧
                  ∃ e : G.edgeSet,
                    (e ∈ classifier.crossingExtensionFinset
                        (interiorEdgeSupport emb.faceBoundary emb.faces) ∨
                      e ∈ classifier.noncrossingExtensionFinset
                        (interiorEdgeSupport emb.faceBoundary emb.faces)) ∧
                      e ∈ classifier.remainingControlEdges
                        (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
                        ¬ data.EnumeratedExceptionalAnnulusForcedEdge
                          p0Inside p4Inside side e ∧
                          z e ≠ 0 ∧
                            ((classifier.remainingControlEdges
                                (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
                              (classifier.remainingControlEdges
                                (interiorEdgeSupport emb.faceBoundary emb.faces)).card ∧
                              ∃ i :
                                ({e : G.edgeSet //
                                  e ∈ classifier.remainingControlEdges
                                    (interiorEdgeSupport emb.faceBoundary emb.faces)} × Bool),
                                chainDotBilinForm G.edgeSet
                                    (redBlueSingleCoordinateFamily
                                      (classifier.remainingControlEdges
                                        (interiorEdgeSupport emb.faceBoundary emb.faces))
                                      hredRemaining hblueRemaining i :
                                      G.edgeSet → Color) z ≠ 0 := by
  refine
    data.ofDecidableChecks_missing_checker_ingredient_or_histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_extensionControlEdge_boundaryZeroChain_canonicalFamilyPairing_ne_zero_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier (interiorEdgeSupport emb.faceBoundary emb.faces) ?_
      hredEmitted hblueEmitted hredRemaining hblueRemaining hnotSynthesis
  intro z hzBoundary hcontrol
  exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    z hzBoundary hcontrol

/--
Interior-support exact-coverage primitive frontier for the canonical-family CAP5 detector.
With the canonical interior-support control set, exact forced-edge coverage eliminates the
path-xor fallback from a failed synthesis run; only a concrete missing primitive checker
ingredient remains.
-/
theorem missing_checker_ingredient_of_not_theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
              boundaryEdge side latent).MissingComplementarySideCycleEvidence) := by
  refine
    data.missing_checker_ingredient_of_not_theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
      classifier (interiorEdgeSupport emb.faceBoundary emb.faces) ?_ hredEmitted hblueEmitted
      hredRemaining hblueRemaining hcoverage hnotSynthesis
  intro z hzBoundary hcontrol
  exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    z hzBoundary hcontrol

/--
Interior-support total failed-synthesis frontier for the canonical-family CAP5 detector.  With
the canonical interior-support control set, every failed synthesis run leaves either a concrete
missing primitive checker ingredient or a failure of exact forced-edge coverage.
-/
theorem missing_checker_ingredient_or_not_forcedEdgeCoverage_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
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
      ¬ (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) := by
  refine
    data.missing_checker_ingredient_or_not_forcedEdgeCoverage_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier (interiorEdgeSupport emb.faceBoundary emb.faces) ?_
      hredEmitted hblueEmitted hredRemaining hblueRemaining hnotSynthesis
  intro z hzBoundary hcontrol
  exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    z hzBoundary hcontrol

/--
Concrete interior-support failed-synthesis frontier.  For the canonical interior-support control
set, failed CAP5 synthesis leaves either a named primitive checker gap or a concrete remaining
interior-support edge whose removal strictly decreases the finite worklist.  This replaces the
abstract `¬ forcedEdgeCoverage` branch by the next edge that the checker must enumerate.
-/
theorem missing_checker_ingredient_or_exists_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
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
        e ∈ classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
          ((classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
            (classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
  rcases
      data.missing_checker_ingredient_or_not_forcedEdgeCoverage_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
        hnotSynthesis with
    hmissing | hnotCoverage
  · exact Or.inl hmissing
  · exact Or.inr
      (data.exists_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_not_forcedEdgeCoverage
        emb p0Inside p4Inside side classifier hnotCoverage)

/--
Success-or-concrete-frontier form.  A canonical interior-support CAP5 run either closes Theorem
4.9 synthesis, reports a primitive checker gap, or exposes the next remaining interior-support
edge with a decreasing worklist measure.
-/
theorem theorem49BoundaryRootSynthesis_or_missing_checker_ingredient_or_exists_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings) :
    Theorem49BoundaryRootSynthesis emb C₀ ∨
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
          e ∈ classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
            ((classifier.remainingControlEdges
                (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
              (classifier.remainingControlEdges
                (interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
  by_cases hclosed : Theorem49BoundaryRootSynthesis emb C₀
  · exact Or.inl hclosed
  · exact Or.inr
      (data.missing_checker_ingredient_or_exists_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier hredEmitted hblueEmitted hredRemaining hblueRemaining hclosed)

/--
Interior-support closed-frontier theorem for the canonical-family CAP5 detector.  With the
canonical interior-support control set, exact forced-edge coverage plus absence of every
primitive missing-checker bin closes Theorem 4.9 synthesis.
-/
theorem theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_no_missing_checker_ingredient_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  by_contra hnotSynthesis
  exact hnoMissing
    (data.missing_checker_ingredient_of_not_theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_interiorEdgeSupportControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
      classifier hredEmitted hblueEmitted hredRemaining hblueRemaining hcoverage hnotSynthesis)

/--
Interior-support no-evader closed-frontier theorem for the canonical-family CAP5 detector.  With
the canonical interior-support control set, the finite `F₂` no-evader verdict supplies the exact
coverage input once the primitive checker frontier is closed.
-/
theorem theorem49BoundaryRootSynthesis_of_no_boundaryZeroChain_vanishing_on_forcedEdges_of_no_missing_checker_ingredient_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnoEvader :
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  data.theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_no_missing_checker_ingredient_of_interiorEdgeSupportControl
    emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
    classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
    ((data.forcedEdgeCoverage_iff_no_boundaryZeroChain_vanishing_on_forcedEdges
      emb p0Inside p4Inside side).2 hnoEvader)
    hnoMissing

/--
Executable full-boundary-zero no-evader handoff.  For the canonical interior-support runner, an
empty primitive checker report plus the finite F2 no-evader verdict yields both theorem-4.9
synthesis and full selected-boundary-zero classifier control by the emitted CAP5 coordinates.
-/
theorem theorem49BoundaryRootSynthesis_and_boundaryZeroClassifierControl_of_no_boundaryZeroEvader_of_missingCheckerEvidenceLatents_eq_nil_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnoEvader :
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0)
    (hmissingEmpty :
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).missingCheckerEvidenceLatents = []) :
    Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0) := by
  refine
    data.theorem49BoundaryRootSynthesis_and_boundaryZeroClassifierControl_of_no_boundaryZeroEvader_of_no_missing_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier (interiorEdgeSupport emb.faceBoundary emb.faces) ?_
      hredEmitted hblueEmitted hredRemaining hblueRemaining hnoEvader
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks_missingCheckerEvidenceLatents_eq_nil_iff_no_missing_checker_ingredient
        boundaryEdge side).1 hmissingEmpty)
  intro z hzBoundary hcontrol
  exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    z hzBoundary hcontrol

/--
Interior-support all-forced closed-frontier theorem.  This is the direct finite-lab survivor:
once the enumerated CAP5 forced edges contain the ambient interior support, no nonzero
selected-boundary-zero chain can evade them; with the primitive checker frontier closed, this
closes synthesis.
-/
theorem theorem49BoundaryRootSynthesis_of_interiorEdgeSupport_subset_enumeratedForcedEdges_of_no_missing_checker_ingredient_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hInteriorForced :
      ∀ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  data.theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_no_missing_checker_ingredient_of_interiorEdgeSupportControl
    emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
    classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
    (data.forcedEdgeCoverage_of_interiorEdgeSupport_subset_enumeratedForcedEdges
      emb p0Inside p4Inside side hInteriorForced)
    hnoMissing

/--
All-interior-support no-evader handoff.  When the completed CAP5 run enumerates every ambient
interior-support edge as forced, the finite all-interior F2 survivor closes synthesis and also
proves forced-edge coverage of the actual theorem-4.9 target `W0(H)`.
-/
theorem interiorSupportForced_synthesis_and_boundaryTargetCoverage
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hInteriorForced :
      ∀ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) := by
  have hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0 :=
    data.forcedEdgeCoverage_of_interiorEdgeSupport_subset_enumeratedForcedEdges
      emb p0Inside p4Inside side hInteriorForced
  have hsynthesis :
      Theorem49BoundaryRootSynthesis emb C₀ :=
    data.theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_no_missing_checker_ingredient_of_interiorEdgeSupportControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier hredEmitted hblueEmitted hredRemaining hblueRemaining hcoverage
      hnoMissing
  have htarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0 := by
    intro z hzTarget hzNonzero
    exact hcoverage
      ((theorem49BoundaryZeroKirchhoffSubspace_le_planarBoundaryZeroSubmodule
        emb (Theorem49BoundaryVertices emb)) (by
          simpa [Theorem49BoundaryTarget, Theorem49BoundaryVertices] using hzTarget))
      hzNonzero
  exact ⟨hsynthesis, htarget⟩

/--
All-interior forced-edge success with the odd-interior obstruction excluded.  The same
all-interior coverage that closes synthesis and target coverage also proves that ambient
interior support contains no odd closed walk, because all forced edges cross one fixed side.
-/
theorem interiorSupportForced_synthesis_and_boundaryTargetCoverage_and_no_closed_odd_walk
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hInteriorForced :
      ∀ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    (Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)) ∧
      ¬ ∃ u : V, ∃ p : G.Walk u u,
        Odd p.length ∧
          ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
            e ∈ interiorEdgeSupport emb.faceBoundary emb.faces := by
  exact
    ⟨data.interiorSupportForced_synthesis_and_boundaryTargetCoverage
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
        hInteriorForced hnoMissing,
      data.not_exists_closed_odd_walk_in_interiorSupport_of_interiorEdgeSupport_subset_enumeratedForcedEdges
        emb p0Inside p4Inside side hInteriorForced⟩

/--
Decisive all-interior worklist frontier.  A closed primitive checker either has already
enumerated enough forced edges to close synthesis and target coverage, or it exposes a concrete
remaining interior-support edge whose erasure decreases the canonical finite worklist.
-/
theorem interiorSupportForced_or_remainingEdge
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    (Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)) ∨
      ∃ e : G.edgeSet,
        e ∈ classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
          ((classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
            (classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
  by_cases hInteriorForced :
      ∀ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e
  · exact Or.inl
      (data.interiorSupportForced_synthesis_and_boundaryTargetCoverage
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
        classifier hredEmitted hblueEmitted hredRemaining hblueRemaining hInteriorForced
        hnoMissing)
  · have hgap :
        ∃ e : G.edgeSet,
          e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
            ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
      by_contra hnoGap
      exact hInteriorForced (by
        intro e heInterior
        by_contra hnotForced
        exact hnoGap ⟨e, heInterior, hnotForced⟩)
    rcases hgap with ⟨e, heInterior, hnotForced⟩
    have heRemaining :
        e ∈ classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces) := by
      refine
        (classifier.mem_remainingControlEdges_iff
          (interiorEdgeSupport emb.faceBoundary emb.faces) e).2 ⟨heInterior, ?_⟩
      intro heEmitted
      exact hnotForced ((classifier.emittedFinset_spec e).1 heEmitted)
    exact Or.inr ⟨e, heRemaining,
      classifier.card_erase_remainingControlEdges_lt_of_mem
        (interiorEdgeSupport emb.faceBoundary emb.faces) heRemaining⟩

/--
Closed-worklist certificate for the all-interior F2 frontier.  If the primitive checker frontier
is closed and the canonical interior-support worklist is empty, the CAP5 runner has reached the
all-interior no-evader branch, so synthesis and target coverage both follow.
-/
theorem remainingInteriorSupportEmpty_synthesis_and_targetCoverage
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hremainingEmpty :
      classifier.remainingControlEdges (interiorEdgeSupport emb.faceBoundary emb.faces) = ∅)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) := by
  rcases data.interiorSupportForced_or_remainingEdge
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
      hnoMissing with hdone | hremaining
  · exact hdone
  · rcases hremaining with ⟨e, heRemaining, _⟩
    rw [hremainingEmpty] at heRemaining
    simp at heRemaining

/--
Executable empty-worklist success with the odd-interior obstruction excluded.  An empty
canonical interior-support worklist reaches the all-interior no-evader/subset side; the same
certificate also proves that ambient interior support has no odd closed walk.
-/
theorem remainingInteriorSupportEmpty_synthesis_and_targetCoverage_and_no_closed_odd_walk
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hremainingEmpty :
      classifier.remainingControlEdges (interiorEdgeSupport emb.faceBoundary emb.faces) = ∅)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence))) :
    (Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)) ∧
      ¬ ∃ u : V, ∃ p : G.Walk u u,
        Odd p.length ∧
          ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
            e ∈ interiorEdgeSupport emb.faceBoundary emb.faces := by
  have hInteriorForced :
      ∀ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e :=
    data.interiorEdgeSupport_subset_enumeratedForcedEdges_of_remainingInteriorSupportEmpty
      emb p0Inside p4Inside side classifier hremainingEmpty
  exact
    ⟨data.remainingInteriorSupportEmpty_synthesis_and_targetCoverage
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
        hremainingEmpty hnoMissing,
      data.not_exists_closed_odd_walk_in_interiorSupport_of_interiorEdgeSupport_subset_enumeratedForcedEdges
        emb p0Inside p4Inside side hInteriorForced⟩

/--
Executable closed-worklist certificate.  The decidable CAP5 report having no missing evidence,
together with an empty canonical interior-support worklist, is enough to close synthesis and
target coverage.
-/
theorem remainingInteriorSupportEmpty_report_synthesis_and_targetCoverage
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hremainingEmpty :
      classifier.remainingControlEdges (interiorEdgeSupport emb.faceBoundary emb.faces) = ∅)
    (hmissingEmpty :
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).missingCheckerEvidenceLatents = []) :
    Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :=
  data.remainingInteriorSupportEmpty_synthesis_and_targetCoverage
    emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
    classifier hredEmitted hblueEmitted hredRemaining hblueRemaining hremainingEmpty
    ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks_missingCheckerEvidenceLatents_eq_nil_iff_no_missing_checker_ingredient
      boundaryEdge side).1 hmissingEmpty)

/--
Interior-support concrete-checker closed-frontier theorem.  With the canonical interior-support
control set, exact forced-edge coverage closes synthesis once every enumerated latent has
portal-crossing evidence and the ambient side has cycles on both sides.
-/
theorem theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_allPortalCrosses_of_sideCycles_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v))
    (hallPortalCrosses :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).PortalCrosses)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    Theorem49BoundaryRootSynthesis emb C₀ := by
  exact data.theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_no_missing_checker_ingredient_of_interiorEdgeSupportControl
    emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
    classifier hredEmitted hblueEmitted hredRemaining hblueRemaining hcoverage
    (CAP5ExceptionalAnnulusGeneratorReport.no_missing_checker_ingredient_of_allPortalCrosses_of_sideCycles
      boundaryEdge side hallPortalCrosses hcycles)

/--
Interior-support concrete all-forced closed-frontier theorem.  Portal-crossing evidence plus
side cycles close the primitive checker frontier; if CAP5 enumerates every ambient
interior-support edge as forced, the finite `F₂` all-interior-support survivor supplies exact
coverage.
-/
theorem theorem49BoundaryRootSynthesis_of_interiorEdgeSupport_subset_enumeratedForcedEdges_of_allPortalCrosses_of_sideCycles_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v))
    (hallPortalCrosses :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).PortalCrosses)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hInteriorForced :
      ∀ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  data.theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_allPortalCrosses_of_sideCycles_of_interiorEdgeSupportControl
    emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
    hallPortalCrosses classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
    (data.forcedEdgeCoverage_of_interiorEdgeSupport_subset_enumeratedForcedEdges
      emb p0Inside p4Inside side hInteriorForced)

/--
Interior-support concrete-checker no-evader closed-frontier theorem.  With portal-crossing
evidence and side cycles closing the primitive frontier, the finite `F₂` no-evader verdict closes
the canonical interior-support CAP5 route.
-/
theorem theorem49BoundaryRootSynthesis_of_no_boundaryZeroChain_vanishing_on_forcedEdges_of_allPortalCrosses_of_sideCycles_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v))
    (hallPortalCrosses :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          boundaryEdge side latent).PortalCrosses)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnoEvader :
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  data.theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_allPortalCrosses_of_sideCycles_of_interiorEdgeSupportControl
    emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
    hallPortalCrosses classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
    ((data.forcedEdgeCoverage_iff_no_boundaryZeroChain_vanishing_on_forcedEdges
      emb p0Inside p4Inside side).2 hnoEvader)

/--
No-missing interior-support frontier.  If Theorem 4.9 synthesis still fails after the primitive
checker frontier is closed, the CAP5 enumerated forced-edge predicate cannot contain the whole
ambient interior support: a concrete interior-support edge is missing from the enumeration.
-/
theorem exists_interiorEdgeSupportEdge_not_enumeratedForcedEdge_of_no_missing_checker_ingredient_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence)))
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    ∃ e : G.edgeSet,
      e ∈ interiorEdgeSupport emb.faceBoundary emb.faces ∧
        ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
  by_contra hnoGap
  have hInteriorForced :
      ∀ e : G.edgeSet,
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces →
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
    intro e heInterior
    by_contra hnotForced
    exact hnoGap ⟨e, heInterior, hnotForced⟩
  have hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0 :=
    data.forcedEdgeCoverage_of_interiorEdgeSupport_subset_enumeratedForcedEdges
      emb p0Inside p4Inside side hInteriorForced
  exact hnotSynthesis
    (data.theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage_of_no_missing_checker_ingredient_of_interiorEdgeSupportControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
      classifier hredEmitted hblueEmitted hredRemaining hblueRemaining hcoverage hnoMissing)

/--
Worklist-facing form of the no-missing interior-support frontier.  Failed synthesis with no
primitive checker gap exposes a remaining interior-support edge, with the standard finite
measure decrease available after erasing that edge.
-/
theorem exists_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_no_missing_checker_ingredient_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence)))
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    ∃ e : G.edgeSet,
      e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
        ((classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
          (classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
  rcases
      data.exists_interiorEdgeSupportEdge_not_enumeratedForcedEdge_of_no_missing_checker_ingredient_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
        classifier hredEmitted hblueEmitted hredRemaining hblueRemaining hnoMissing
        hnotSynthesis with
    ⟨e, heInterior, hnotForced⟩
  have heRemaining :
      e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces) := by
    refine
      (classifier.mem_remainingControlEdges_iff
        (interiorEdgeSupport emb.faceBoundary emb.faces) e).2 ⟨heInterior, ?_⟩
    intro heEmitted
    exact hnotForced ((classifier.emittedFinset_spec e).1 heEmitted)
  exact ⟨e, heRemaining,
    classifier.card_erase_remainingControlEdges_lt_of_mem
      (interiorEdgeSupport emb.faceBoundary emb.faces) heRemaining⟩

/--
Executable-report variant of the no-missing interior-support frontier.  If the decidable CAP5
report has no missing checker evidence and synthesis still fails, the classifier has a concrete
remaining interior-support edge.
-/
theorem exists_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hmissingEmpty :
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).missingCheckerEvidenceLatents = [])
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    ∃ e : G.edgeSet,
      e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
        ((classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
          (classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
  exact
    data.exists_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_no_missing_checker_ingredient_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses hcycles
      classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
      ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks_missingCheckerEvidenceLatents_eq_nil_iff_no_missing_checker_ingredient
        boundaryEdge side).1 hmissingEmpty)
      hnotSynthesis

/--
Executable-report closed frontier for finite-control CAP5 runs.  If the decidable missing-
evidence report is empty but Theorem 4.9 synthesis still fails, exact forced-edge coverage is
false in the strongest useful sense: there is a nonzero selected-boundary-zero chain invisible
to every enumerated CAP5 forced edge.
-/
theorem exists_boundaryZeroChain_vanishing_on_forcedEdges_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges controlEdges,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hmissingEmpty :
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).missingCheckerEvidenceLatents = [])
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          ∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0 := by
  have hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence)) :=
    (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks_missingCheckerEvidenceLatents_eq_nil_iff_no_missing_checker_ingredient
      boundaryEdge side).1 hmissingEmpty
  rcases data.missing_checker_ingredient_or_not_forcedEdgeCoverage_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hredEmitted hblueEmitted hredRemaining
      hblueRemaining hnotSynthesis with
    hmissing | hnotCoverage
  · exact False.elim (hnoMissing hmissing)
  · exact data.exists_boundaryZeroChain_vanishing_on_forcedEdges_of_not_forcedEdgeCoverage
      emb p0Inside p4Inside side hnotCoverage

/--
Interior-support executable-report closed frontier.  With the canonical interior-support control
set, an empty decidable missing-evidence report turns failed synthesis directly into a concrete
F2 boundary-zero evader for the enumerated CAP5 forced edges.
-/
theorem exists_boundaryZeroChain_vanishing_on_forcedEdges_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hmissingEmpty :
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).missingCheckerEvidenceLatents = [])
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          ∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0 := by
  refine
    data.exists_boundaryZeroChain_vanishing_on_forcedEdges_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
      emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier (interiorEdgeSupport emb.faceBoundary emb.faces) ?_
      hredEmitted hblueEmitted hredRemaining hblueRemaining hmissingEmpty hnotSynthesis
  intro z hzBoundary hcontrol
  exact eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
    z hzBoundary hcontrol

/--
Executable-report failure frontier for the canonical interior-support runner.  Once the
primitive checker report is empty, a failed synthesis run carries both sides of the remaining
algebraic obstruction: a genuine selected-boundary-zero evader for the enumerated CAP5 forced
edges and a concrete remaining interior-support worklist edge with the standard erasure
decrease.
-/
theorem boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hmissingEmpty :
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).missingCheckerEvidenceLatents = [])
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    (∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          ∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0) ∧
      ∃ e : G.edgeSet,
        e ∈ classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
          ((classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
            (classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
  exact
    ⟨data.exists_boundaryZeroChain_vanishing_on_forcedEdges_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
        hmissingEmpty hnotSynthesis,
      data.exists_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
        hmissingEmpty hnotSynthesis⟩

/--
Target-controlled failure frontier.  If the closed primitive checker has no missing evidence and
the CAP5 classifier controls the theorem-4.9 target `W0(H)`, then a failed synthesis run cannot
hide its algebraic obstruction inside `W0(H)`: the exposed boundary-zero evader is necessarily
off-target, and the same branch still carries a concrete decreasing interior-support worklist
edge.
-/
theorem offTargetBoundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcontrolTarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)
    (hmissingEmpty :
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).missingCheckerEvidenceLatents = [])
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    (∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ∉ Theorem49BoundaryTarget emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
      ∃ e : G.edgeSet,
        e ∈ classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
          ((classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
            (classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
  rcases
      data.boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
        hmissingEmpty hnotSynthesis with
    ⟨zEvader, hremaining⟩
  rcases zEvader with ⟨z, hzBoundary, hzNonzero, hzForcedZero⟩
  have hzOffTarget : z ∉ Theorem49BoundaryTarget emb := by
    intro hzTarget
    have hzEmittedZero :
        ∀ e ∈ classifier.emittedFinset, z e = 0 := by
      intro e heEmitted
      exact hzForcedZero e ((classifier.emittedFinset_spec e).1 heEmitted)
    exact hzNonzero (hcontrolTarget hzTarget hzEmittedZero)
  exact ⟨⟨z, hzBoundary, hzOffTarget, hzNonzero, hzForcedZero⟩, hremaining⟩

/--
Vertex-Kirchhoff failure frontier.  Under target classifier control, the closed-checker failure
branch exposes a selected-boundary-zero evader that vanishes on every enumerated forced edge and
fails Kirchhoff at a concrete theorem-4.9 boundary vertex, along with the same decreasing
interior-support worklist edge.
-/
theorem boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcontrolTarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)
    (hmissingEmpty :
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).missingCheckerEvidenceLatents = [])
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    (∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          (∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0) ∧
            ∃ v : V,
              v ∈ Theorem49BoundaryVertices emb ∧
                vertexKirchhoffSum G z v ≠ 0) ∧
      ∃ e : G.edgeSet,
        e ∈ classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
          ((classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
            (classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
  rcases
      data.offTargetBoundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
        hcontrolTarget hmissingEmpty hnotSynthesis with
    ⟨zEvader, hremaining⟩
  rcases zEvader with ⟨z, hzBoundary, hzOffTarget, hzNonzero, hzForcedZero⟩
  exact
    ⟨⟨z, hzBoundary, hzNonzero, hzForcedZero,
        exists_theorem49BoundaryVertex_vertexKirchhoffSum_ne_zero_of_boundaryZero_of_not_theorem49BoundaryTarget
          emb hzBoundary hzOffTarget⟩,
      hremaining⟩

/--
Target-controlled executable fork.  Once the primitive checker report is closed and the CAP5
classifier controls the theorem-4.9 target, the remaining F2 route has only two outcomes:
synthesis with target coverage, or a genuine boundary-zero evader failing Kirchhoff at a
theorem-4.9 boundary vertex together with the decreasing interior-support worklist edge.
-/
theorem theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_or_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcontrolTarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)
    (hmissingEmpty :
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).missingCheckerEvidenceLatents = []) :
    (Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)) ∨
      (∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ v : V,
                v ∈ Theorem49BoundaryVertices emb ∧
                  vertexKirchhoffSum G z v ≠ 0) ∧
        ∃ e : G.edgeSet,
          e ∈ classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
            ((classifier.remainingControlEdges
                (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
              (classifier.remainingControlEdges
                (interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
  have htargetCoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0 := by
    exact
      (data.forcedEdgeBoundaryTargetCoverage_iff_no_targetEvader
        emb p0Inside p4Inside side).2
        ((data.theorem49BoundaryTargetClassifierControl_iff_no_targetEvader
          emb p0Inside p4Inside side classifier).1 hcontrolTarget)
  by_cases hclosed : Theorem49BoundaryRootSynthesis emb C₀
  · exact Or.inl ⟨hclosed, htargetCoverage⟩
  · exact Or.inr
      (data.boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
        hcontrolTarget hmissingEmpty hclosed)

/--
Odd-interior specialization of the target-controlled fork.  If an odd closed walk lies entirely
inside the ambient interior support, the empty-worklist proof path is impossible for the same
classifier; nevertheless the closed target-controlled checker still reduces the F2 route to
synthesis with target coverage versus the concrete theorem-4.9 vertex-Kirchhoff evader branch.
-/
theorem theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_or_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_oddInteriorWorklistEdge_of_closed_walk_odd_length_in_interiorSupport
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcontrolTarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)
    (hmissingEmpty :
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).missingCheckerEvidenceLatents = [])
    {u : V} (p : G.Walk u u) (hodd : Odd p.length)
    (hInterior :
      ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    ((Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)) ∨
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ v : V,
                v ∈ Theorem49BoundaryVertices emb ∧
                  vertexKirchhoffSum G z v ≠ 0) ∧
      ∃ e : G.edgeSet,
        e ∈ classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
          ((classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
            (classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
  have hremaining :
      ∃ e : G.edgeSet,
        e ∈ classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
          ((classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
            (classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).card :=
    data.exists_remainingInteriorSupportEdge_with_card_erase_lt_of_closed_walk_odd_length_in_interiorSupport
      emb p0Inside p4Inside side classifier p hodd hInterior
  rcases
      data.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_or_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_theorem49BoundaryTargetClassifierControl_of_interiorEdgeSupportControl
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
        hcontrolTarget hmissingEmpty with
    hdone | hfailure
  · exact ⟨Or.inl hdone, hremaining⟩
  · exact ⟨Or.inr hfailure.1, hfailure.2⟩

/--
Odd-interior no-evader closure.  An odd closed walk can force a nonempty canonical
interior-support worklist, but it does not by itself obstruct the no-evader side of the
target-controlled F2 fork: if the concrete theorem-4.9 boundary-vertex Kirchhoff evader is
absent, the closed checker still yields synthesis and target coverage while the odd walk
supplies the decreasing worklist witness.
-/
theorem theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_and_remainingInteriorSupportEdge_with_card_erase_lt_of_closed_walk_odd_length_in_interiorSupport_of_theorem49BoundaryTargetClassifierControl_of_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hcontrolTarget :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)
    (hnoKirchhoffFailureEvader :
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ v : V,
                v ∈ Theorem49BoundaryVertices emb ∧
                  vertexKirchhoffSum G z v ≠ 0)
    (hmissingEmpty :
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).missingCheckerEvidenceLatents = [])
    {u : V} (p : G.Walk u u) (hodd : Odd p.length)
    (hInterior :
      ∀ e : G.edgeSet, (e : Sym2 V) ∈ p.edges →
        e ∈ interiorEdgeSupport emb.faceBoundary emb.faces) :
    (Theorem49BoundaryRootSynthesis emb C₀ ∧
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ Theorem49BoundaryTarget emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)) ∧
      ∃ e : G.edgeSet,
        e ∈ classifier.remainingControlEdges
            (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
          ((classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
            (classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
  have hdone :
      Theorem49BoundaryRootSynthesis emb C₀ ∧
        (∀ ⦃z : G.edgeSet → Color⦄,
          z ∈ Theorem49BoundaryTarget emb →
          z ≠ 0 →
            ∃ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                z e ≠ 0) := by
    refine
      data.theorem49BoundaryRootSynthesis_and_boundaryTargetCoverage_of_theorem49BoundaryTargetClassifierControl_of_no_boundaryZeroEvader_with_theorem49BoundaryVertexKirchhoffFailure_of_no_missing_finsetControl
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier (interiorEdgeSupport emb.faceBoundary emb.faces) ?_
        hredEmitted hblueEmitted hredRemaining hblueRemaining hcontrolTarget
        hnoKirchhoffFailureEvader
        ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks_missingCheckerEvidenceLatents_eq_nil_iff_no_missing_checker_ingredient
          boundaryEdge side).1 hmissingEmpty)
    intro z hzBoundary hcontrol
    exact
      eq_zero_of_mem_planarBoundaryZeroSubmodule_of_interiorEdgeSupport
        z hzBoundary hcontrol
  exact
    ⟨hdone,
      data.exists_remainingInteriorSupportEdge_with_card_erase_lt_of_closed_walk_odd_length_in_interiorSupport
        emb p0Inside p4Inside side classifier p hodd hInterior⟩

/--
Executable closed-report synthesis-or-evader frontier.  For the canonical interior-support
runner, an empty primitive checker report leaves exactly the algebraic F2 fork: either
Theorem 4.9 synthesis closes, or there is a genuine selected-boundary-zero evader together with
a concrete remaining interior-support worklist edge.
-/
theorem theorem49BoundaryRootSynthesis_or_boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_interiorEdgeSupportControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
    (hredEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueEmitted :
      ∀ e ∈ classifier.emittedFinset,
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hredRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e red ∈ projectedColoringGeneratorSubspace emb colorings)
    (hblueRemaining :
      ∀ e ∈ classifier.remainingControlEdges
          (interiorEdgeSupport emb.faceBoundary emb.faces),
        Pi.single e blue ∈ projectedColoringGeneratorSubspace emb colorings)
    (hmissingEmpty :
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).missingCheckerEvidenceLatents = []) :
    Theorem49BoundaryRootSynthesis emb C₀ ∨
      (∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
        ∃ e : G.edgeSet,
          e ∈ classifier.remainingControlEdges
              (interiorEdgeSupport emb.faceBoundary emb.faces) ∧
            ((classifier.remainingControlEdges
                (interiorEdgeSupport emb.faceBoundary emb.faces)).erase e).card <
              (classifier.remainingControlEdges
                (interiorEdgeSupport emb.faceBoundary emb.faces)).card := by
  by_cases hclosed : Theorem49BoundaryRootSynthesis emb C₀
  · exact Or.inl hclosed
  · exact Or.inr
      (data.boundaryZeroEvader_and_remainingInteriorEdgeSupportEdge_with_card_erase_lt_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_interiorEdgeSupportControl
        emb C₀ colorings hsubset p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier hredEmitted hblueEmitted hredRemaining hblueRemaining
        hmissingEmpty hclosed)

/--
Closed-frontier branch of the CAP5 generator.  Once the finite checker has no missing primitive
evidence left to report, a failed Theorem 4.9 synthesis cannot remain in the geometric partial
case: the report has the complete cyclic-five histogram `(0, 0, 16)` and exposes the same
boundary-zero algebraic obstruction as the forced-bin detector.
-/
theorem histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
              Pi.single e blue)
    (hmissingEmpty :
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).missingCheckerEvidenceLatents = [])
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).partialLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
      data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
        ∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              (∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) ∧
                ∃ i : κ,
                  chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks boundaryEdge side
  have hmissingEmptyReport : report.missingCheckerEvidenceLatents = [] := by
    simpa [report] using hmissingEmpty
  rcases report.all_checker_evidence_of_missingCheckerEvidenceLatents_eq_nil
      hmissingEmptyReport with
    ⟨hportal, hsideCycles⟩
  have hhist :
      report.realizedSeparatorLatents.length = 0 ∧
        report.partialLatents.length = 0 ∧
          report.forcedCounterexampleLatents.length = 16 :=
    report.histogram_lengths_eq_of_complete_of_cyclicallyFiveEdgeConnected
      hcyclic hportal hsideCycles
  rcases data.theorem49BoundaryRootSynthesis_or_forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_finsetControl
      emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue
      hwitnessExtensionRed hwitnessExtensionBlue with
    hclosed | hfallback
  · exact False.elim (hnotSynthesis hclosed)
  · exact ⟨by simpa [report] using hhist, hfallback⟩

/--
Primitive-bin closed-frontier branch of the CAP5 generator.  If no enumerated latent is missing
portal-crossing evidence, a selected-side cycle, or a complementary-side cycle, then failed
Theorem 4.9 synthesis forces the completed `(0, 0, 16)` histogram into the same algebraic
boundary-zero obstruction branch.
-/
theorem histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_no_missing_checker_ingredient_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
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
    (hcyclic : CyclicallyFiveEdgeConnected G)
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
              Pi.single e blue)
    (hnoMissing :
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
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
                boundaryEdge side latent).MissingComplementarySideCycleEvidence)))
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    ((CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).partialLatents.length = 0 ∧
        (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
          boundaryEdge side).forcedCounterexampleLatents.length = 16) ∧
      data.ForcedEdgeIndicatorPathXorDetectorPayload p0Inside p4Inside side ∧
        ∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              (∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) ∧
                ∃ i : κ,
                  chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 := by
  have hmissingEmpty :
      (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
        boundaryEdge side).missingCheckerEvidenceLatents = [] :=
    (CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks_missingCheckerEvidenceLatents_eq_nil_iff_no_missing_checker_ingredient
      boundaryEdge side).2 hnoMissing
  exact
    data.histogram_and_forcedEdgeIndicatorPathXorDetectorPayload_and_boundaryZeroChain_familyPairing_ne_zero_of_missingCheckerEvidenceLatents_eq_nil_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
      emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue
      hwitnessExtensionRed hwitnessExtensionBlue hmissingEmpty hnotSynthesis

end CAP5TransportedEdgeComponentCoverCore

end Mettapedia.GraphTheory.FourColor
