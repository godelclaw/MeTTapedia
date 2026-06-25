import Mettapedia.GraphTheory.FourColor.CAP5WitnessGenerator
import Mettapedia.GraphTheory.FourColor.Curriculum.PathXor

namespace Mettapedia.GraphTheory.FourColor

open SimpleGraph

variable {V : Type*} [DecidableEq V]
variable {G : SimpleGraph V}
variable {boundaryEdge : Fin 5 → G.edgeSet} {side : V → Prop}

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

end CAP5ExceptionalAnnulusGeneratorReport

namespace CAP5TransportedEdgeComponentCoverCore

variable {n : Nat}

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

end CAP5TransportedEdgeComponentCoverCore

end Mettapedia.GraphTheory.FourColor
