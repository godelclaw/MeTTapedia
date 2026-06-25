import Mettapedia.GraphTheory.FourColor.CAP5AlgebraBridge

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]

/-- Public-facing status names for a finite CAP5 separator-generator run.
The `partial` status records missing checker evidence, not a third mathematical
case: once portal crossings and two side cycles are certified, the generic graph
checker resolves the node as either realized or forced-counterexample. -/
inductive CAP5SeparatorGeneratorStatus where
  | realizedSeparator
  | forcedCounterexample
  | partialCase
deriving DecidableEq, Repr

/-- Finite latent choices for one exceptional CAP5 annulus separator sample: the transported
exceptional orientation and the two portal-side bits.  Translating this latent through the five
CAP5 boundary edges gives the canonical candidate edge support to forward-check. -/
structure CAP5ExceptionalAnnulusGeneratorLatent
    {E : Type*} [DecidableEq E] (boundaryEdge : Fin 5 → E) where
  orientation : CAP5ExceptionalBoundarySupportOrientation
  p0Inside : Bool
  p4Inside : Bool

namespace CAP5ExceptionalAnnulusGeneratorLatent

variable {E : Type*} [DecidableEq E] {boundaryEdge : Fin 5 → E}

/-- The four exceptional component-pairing orientations. -/
def allExceptionalBoundarySupportOrientations :
    List CAP5ExceptionalBoundarySupportOrientation :=
  [.redBlue03_redPurple04, .redBlue03_redPurple13,
    .redBlue12_redPurple04, .redBlue12_redPurple13]

@[simp] theorem length_allExceptionalBoundarySupportOrientations :
    allExceptionalBoundarySupportOrientations.length = 4 :=
  rfl

/-- The four Boolean portal-side choices for the exceptional annulus case. -/
def allPortalSideChoices : List (Bool × Bool) :=
  [(true, true), (true, false), (false, true), (false, false)]

@[simp] theorem length_allPortalSideChoices :
    allPortalSideChoices.length = 4 :=
  rfl

/-- The finite latent space for one CAP5 boundary-edge interpretation: four orientations times
four portal-side choices. -/
def all (boundaryEdge : Fin 5 → E) :
    List (CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :=
  allExceptionalBoundarySupportOrientations.flatMap fun orientation =>
    allPortalSideChoices.map fun sideChoice =>
      { orientation := orientation
        p0Inside := sideChoice.1
        p4Inside := sideChoice.2 }

/-- The CAP5 exceptional-annulus finite generator has exactly sixteen latent choices: four
component-pairing orientations times four portal-side choices. -/
@[simp] theorem length_all (boundaryEdge : Fin 5 → E) :
    (all boundaryEdge).length = 16 := by
  simp [all, allExceptionalBoundarySupportOrientations, allPortalSideChoices]

/-- Every exceptional orientation occurs in the finite latent enumeration. -/
theorem mem_allExceptionalBoundarySupportOrientations
    (orientation : CAP5ExceptionalBoundarySupportOrientation) :
    orientation ∈ allExceptionalBoundarySupportOrientations := by
  cases orientation <;> simp [allExceptionalBoundarySupportOrientations]

/-- Every Boolean portal-side choice occurs in the finite latent enumeration. -/
theorem mem_allPortalSideChoices (p0Inside p4Inside : Bool) :
    (p0Inside, p4Inside) ∈ allPortalSideChoices := by
  cases p0Inside <;> cases p4Inside <;> simp [allPortalSideChoices]

/-- Constructor-level membership in the finite CAP5 latent enumeration. -/
theorem mem_all_of_fields
    (boundaryEdge : Fin 5 → E)
    (orientation : CAP5ExceptionalBoundarySupportOrientation)
    (p0Inside p4Inside : Bool) :
    ({ orientation := orientation
       p0Inside := p0Inside
       p4Inside := p4Inside } :
      CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) ∈ all boundaryEdge := by
  unfold all
  exact List.mem_flatMap.2
    ⟨orientation, mem_allExceptionalBoundarySupportOrientations orientation,
      List.mem_map.2
        ⟨(p0Inside, p4Inside), mem_allPortalSideChoices p0Inside p4Inside, rfl⟩⟩

/-- Every generated latent is present in the finite CAP5 latent enumeration. -/
theorem mem_all (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :
    latent ∈ all boundaryEdge := by
  rcases latent with ⟨orientation, p0Inside, p4Inside⟩
  exact mem_all_of_fields boundaryEdge orientation p0Inside p4Inside

/-- Exceptional component-cover data selects an orientation occurring in the finite latent
enumeration, for any fixed portal-side choice. -/
theorem exists_mem_all_of_isExceptional_of_portalSides
    {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional) :
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ all boundaryEdge ∧
        latent.p0Inside = p0Inside ∧
          latent.p4Inside = p4Inside ∧
            data.RealizesExceptionalBoundarySupportOrientation latent.orientation := by
  rcases CAP5TransportedEdgeComponentCoverCore.exists_exceptionalBoundarySupportOrientation_of_isExceptional
      h with
    ⟨orientation, horientation⟩
  exact
    ⟨{ orientation := orientation
       p0Inside := p0Inside
       p4Inside := p4Inside },
      mem_all_of_fields boundaryEdge orientation p0Inside p4Inside, rfl, rfl,
      horientation⟩

/-- Side-case selected by the two portal-side bits. -/
def sideCase (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :
    CAP5ExceptionalAnnulusSideCase :=
  CAP5ExceptionalAnnulusSideCase.ofPortalSides latent.p0Inside latent.p4Inside

/-- Canonical boundary-edge support candidate generated by the latent choices. -/
def candidate (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :
    CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge :=
  CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndSideCase
    boundaryEdge latent.orientation latent.sideCase

@[simp]
theorem candidate_orientation
    (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :
    latent.candidate.portalCandidate.orientation = latent.orientation :=
  rfl

@[simp]
theorem candidate_sideCase
    (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :
    latent.candidate.portalCandidate.sideCase = latent.sideCase :=
  rfl

theorem candidate_sideCase_eq_ofPortalSides
    (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :
    latent.candidate.portalCandidate.sideCase =
      CAP5ExceptionalAnnulusSideCase.ofPortalSides latent.p0Inside latent.p4Inside :=
  rfl

end CAP5ExceptionalAnnulusGeneratorLatent

/-- A graph-side CAP5 generator node: finite annulus latent choices plus the vertex-side
predicate proposed by the current separator interpretation. -/
structure CAP5ExceptionalAnnulusGeneratorNode
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (boundaryEdge : Fin 5 → G.edgeSet) where
  latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge
  side : V → Prop

namespace CAP5ExceptionalAnnulusGeneratorNode

variable {G : SimpleGraph V}
variable {boundaryEdge : Fin 5 → G.edgeSet}

/-- The canonical candidate edge support generated by this node. -/
def candidate (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) :
    CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge :=
  node.latent.candidate

@[simp]
theorem candidate_orientation
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) :
    node.candidate.portalCandidate.orientation = node.latent.orientation := by
  exact node.latent.candidate_orientation

@[simp]
theorem candidate_sideCase
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) :
    node.candidate.portalCandidate.sideCase = node.latent.sideCase := by
  exact node.latent.candidate_sideCase

/-- Checker prerequisite: every named portal in the generated support crosses the proposed
vertex side. -/
def PortalCrosses (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) : Prop :=
  ∀ i : Fin 5, i ∈ node.candidate.portalCandidate.portalSet →
    EdgeCrossesVertexSide G node.side (boundaryEdge i)

/-- Checker prerequisite: both sides of the proposed separator carry cycles. -/
def SideCycles (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) : Prop :=
  HasCycleOnSide G node.side ∧ HasCycleOnSide G (fun v => ¬ node.side v)

/-- Realized bin: the generated candidate is exact cyclic-cut realization data. -/
def RealizedSeparator (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) : Prop :=
  Nonempty (node.candidate.CyclicEdgeCutRealizationData (G := G))

/-- A generator node cannot be in the realized-separator bin if one of its candidate edges has
a support-avoiding bypass walk between that edge's endpoints. -/
theorem not_realizedSeparator_of_candidate_edge_bypass
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    {u v : V} {e : G.edgeSet}
    (he_pair : (e : Sym2 V) = s(u, v))
    (hecut : e ∈ node.candidate.edgeSupport)
    (p : G.Walk u v)
    (havoid : ∀ e' : G.edgeSet, e' ∈ node.candidate.edgeSupport →
      (e' : Sym2 V) ∉ p.edges) :
    ¬ node.RealizedSeparator := by
  exact node.candidate.not_cyclicEdgeCutRealizationData_of_edge_bypass
    he_pair hecut p havoid

/-- Forced-counterexample edge emitted by the finite forward checker.  The edge is outside the
generated support, crosses the proposed side by a one-edge walk, and avoids every generated
portal boundary edge. -/
def ForcedCounterexampleEdge
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) (e : G.edgeSet) : Prop :=
  ∃ u v : V, ∃ p : G.Walk u v,
    e ∉ node.candidate.edgeSupport ∧
      node.side u ∧ ¬ node.side v ∧
        p.edges = [(e : Sym2 V)] ∧
          ∀ i : Fin 5, i ∈ node.candidate.portalCandidate.portalSet →
            ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges

/-- Forced-counterexample bin: the checker emits at least one concrete outside crossing edge. -/
def ForcedCounterexample (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) : Prop :=
  ∃ e : G.edgeSet, node.ForcedCounterexampleEdge e

/-- A forced generator edge is a raw side-crossing edge.  This is the reusable bridge from the
finite CAP5 report output back to the graph-theoretic cyclic-cut checker. -/
theorem forcedCounterexampleEdge_crosses
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    {e : G.edgeSet} (h : node.ForcedCounterexampleEdge e) :
    EdgeCrossesVertexSide G node.side e := by
  rcases h with ⟨u, v, p, _heOutside, hu, hv, hpEdges, _havoid⟩
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides node.side p hu hv with
    ⟨e', heEdges, hcross⟩
  have hsym : (e' : Sym2 V) = (e : Sym2 V) := by
    simpa [hpEdges] using heEdges
  have heq : e' = e := Subtype.ext hsym
  simpa [heq] using hcross

/-- Partial bin: the forward checker has not yet certified the graph-side prerequisites needed
for the generic holds-vs-counterexample theorem. -/
def Partial (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) : Prop :=
  ¬ node.PortalCrosses ∨ ¬ node.SideCycles

/-- Predicate associating status labels with their proof obligations. -/
def InBin (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) :
    CAP5SeparatorGeneratorStatus → Prop
  | .realizedSeparator =>
      node.PortalCrosses ∧ node.SideCycles ∧ node.RealizedSeparator
  | .forcedCounterexample =>
      node.PortalCrosses ∧ node.SideCycles ∧ node.ForcedCounterexample
  | .partialCase =>
      node.Partial

/-- Complete CAP5 forward-checker boundary for one generated node.  Once portal crossings and
two-sided cycles are available, the generic graph checker resolves the node: either the candidate
is a realized separator, or it emits a concrete one-edge counterexample. -/
theorem realizedSeparator_or_forcedCounterexample_of_complete
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    (hportal : node.PortalCrosses) (hcycles : node.SideCycles) :
    node.RealizedSeparator ∨ node.ForcedCounterexample := by
  rcases hcycles with ⟨hinside_cycle, houtside_cycle⟩
  rcases node.candidate
      |>.cyclicEdgeCutRealizationData_or_oneEdge_walk_avoiding_portalBoundaryEdges_of_portal_crosses
        node.side hportal hinside_cycle houtside_cycle with
    hrealized | hforced
  · exact Or.inl hrealized
  · rcases hforced with ⟨u, v, e, p, heOutside, hu, hv, hpEdges, havoid⟩
    exact Or.inr ⟨e, u, v, p, heOutside, hu, hv, hpEdges, havoid⟩

/-- Status-form version of the complete forward-checker boundary. -/
theorem inBin_realizedSeparator_or_forcedCounterexample_of_complete
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    (hportal : node.PortalCrosses) (hcycles : node.SideCycles) :
    node.InBin CAP5SeparatorGeneratorStatus.realizedSeparator ∨
      node.InBin CAP5SeparatorGeneratorStatus.forcedCounterexample := by
  rcases node.realizedSeparator_or_forcedCounterexample_of_complete hportal hcycles with
    hrealized | hforced
  · exact Or.inl ⟨hportal, hcycles, hrealized⟩
  · exact Or.inr ⟨hportal, hcycles, hforced⟩

/-- Data-level generator theorem.  Exceptional CAP5 component-cover data chooses an enumerated
latent.  If the graph-side interpretation certifies portal crossings and two side cycles for the
selected portal-side bits, that enumerated node resolves into either the realized-separator bin
or the forced-counterexample bin. -/
theorem exists_enumeratedNode_inBin_realizedSeparator_or_forcedCounterexample_of_isExceptional_of_portalSides
    {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v)) :
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        latent.p0Inside = p0Inside ∧
          latent.p4Inside = p4Inside ∧
            data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
              (let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
                { latent := latent, side := side };
                node.InBin CAP5SeparatorGeneratorStatus.realizedSeparator ∨
                  node.InBin CAP5SeparatorGeneratorStatus.forcedCounterexample) := by
  rcases CAP5ExceptionalAnnulusGeneratorLatent.exists_mem_all_of_isExceptional_of_portalSides
      (boundaryEdge := boundaryEdge) p0Inside p4Inside h with
    ⟨latent, hmem, hp0, hp4, horientation⟩
  let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
    { latent := latent, side := side }
  have hnodePortal : node.PortalCrosses := by
    intro i hi
    have horientation' :
        data.RealizesExceptionalBoundarySupportOrientation
          node.candidate.portalCandidate.orientation := by
      simpa using horientation
    have hsideCase :
        node.candidate.portalCandidate.sideCase =
          CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside := by
      change CAP5ExceptionalAnnulusSideCase.ofPortalSides
          node.latent.p0Inside node.latent.p4Inside =
        CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside
      rw [hp0, hp4]
    exact hportal_crosses node.candidate horientation' hsideCase i hi
  have hresolved :=
    node.inBin_realizedSeparator_or_forcedCounterexample_of_complete hnodePortal hcycles
  exact ⟨latent, hmem, hp0, hp4, horientation, by simpa [node] using hresolved⟩

/-- In a cyclically five-edge-connected graph, any complete size-at-most-four CAP5 generated
node is forced into the counterexample bin.  This is the finite falsification form of the
separator route. -/
theorem forcedCounterexample_of_cyclicallyFiveEdgeConnected
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal : node.PortalCrosses) (hcycles : node.SideCycles) :
    node.ForcedCounterexample := by
  rcases hcycles with ⟨hinside_cycle, houtside_cycle⟩
  rcases node.candidate
      |>.exists_oneEdge_walk_avoiding_portalBoundaryEdges_of_cyclicallyFiveEdgeConnected_of_portal_crosses
        node.side hcyclic hportal hinside_cycle houtside_cycle with
    ⟨u, v, e, p, heOutside, hu, hv, hpEdges, havoid⟩
  exact ⟨e, u, v, p, heOutside, hu, hv, hpEdges, havoid⟩

/-- Data-level cyclic-connectivity specialization of the finite CAP5 generator.  Exceptional
component-cover data selects an enumerated latent, and cyclic five-edge-connectivity forces the
complete generated node into the counterexample bin rather than the small-separator bin. -/
theorem exists_enumeratedNode_inBin_forcedCounterexample_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
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
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v)) :
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        latent.p0Inside = p0Inside ∧
          latent.p4Inside = p4Inside ∧
            data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
              (let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
                { latent := latent, side := side };
                node.InBin CAP5SeparatorGeneratorStatus.forcedCounterexample) := by
  rcases CAP5ExceptionalAnnulusGeneratorLatent.exists_mem_all_of_isExceptional_of_portalSides
      (boundaryEdge := boundaryEdge) p0Inside p4Inside h with
    ⟨latent, hmem, hp0, hp4, horientation⟩
  let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
    { latent := latent, side := side }
  have hnodePortal : node.PortalCrosses := by
    intro i hi
    have horientation' :
        data.RealizesExceptionalBoundarySupportOrientation
          node.candidate.portalCandidate.orientation := by
      simpa using horientation
    have hsideCase :
        node.candidate.portalCandidate.sideCase =
          CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside := by
      change CAP5ExceptionalAnnulusSideCase.ofPortalSides
          node.latent.p0Inside node.latent.p4Inside =
        CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside
      rw [hp0, hp4]
    exact hportal_crosses node.candidate horientation' hsideCase i hi
  have hforced := node.forcedCounterexample_of_cyclicallyFiveEdgeConnected
    hcyclic hnodePortal hcycles
  exact ⟨latent, hmem, hp0, hp4, horientation, by
    simpa [node] using (show node.InBin CAP5SeparatorGeneratorStatus.forcedCounterexample from
      ⟨hnodePortal, hcycles, hforced⟩)⟩

/-- Cyclic five-edge-connectivity rules out the realized-separator bin for any complete CAP5
generated node. -/
theorem not_realizedSeparator_of_cyclicallyFiveEdgeConnected
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    ¬ node.RealizedSeparator := by
  rintro ⟨realization⟩
  rcases node.candidate.exists_smallCyclicEdgeCut_of_realizationData realization with
    ⟨cut, hcut, hcard⟩
  exact hcyclic.not_smallCyclicEdgeCut_card_le_four cut (by
    simpa [hcut] using hcard)

/-- Certified output for one generated CAP5 separator node.  The status is computationally
useful only together with the certificate that it really belongs to the advertised bin. -/
structure Report (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) where
  status : CAP5SeparatorGeneratorStatus
  cert : node.InBin status

namespace Report

/-- A complete generator node cannot honestly be reported as partial. -/
theorem status_ne_partialCase_of_complete
    {node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge}
    (report : node.Report) (hportal : node.PortalCrosses) (hcycles : node.SideCycles) :
    report.status ≠ CAP5SeparatorGeneratorStatus.partialCase := by
  intro hstatus
  have hcert := report.cert
  rw [hstatus] at hcert
  change node.Partial at hcert
  rcases hcert with hnotPortal | hnotCycles
  · exact hnotPortal hportal
  · exact hnotCycles hcycles

/-- In a cyclically five-edge-connected graph, a certified report cannot put a generated
complete CAP5 node in the realized-separator bin. -/
theorem status_ne_realizedSeparator_of_cyclicallyFiveEdgeConnected
    {node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge}
    (report : node.Report) (hcyclic : CyclicallyFiveEdgeConnected G) :
    report.status ≠ CAP5SeparatorGeneratorStatus.realizedSeparator := by
  intro hstatus
  have hcert := report.cert
  rw [hstatus] at hcert
  rcases hcert with ⟨_hportal, _hcycles, hrealized⟩
  exact node.not_realizedSeparator_of_cyclicallyFiveEdgeConnected hcyclic hrealized

/-- A certified report cannot put a node in the realized-separator bin when a candidate edge has
a support-avoiding bypass walk between its endpoints. -/
theorem status_ne_realizedSeparator_of_candidate_edge_bypass
    {node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge}
    (report : node.Report)
    {u v : V} {e : G.edgeSet}
    (he_pair : (e : Sym2 V) = s(u, v))
    (hecut : e ∈ node.candidate.edgeSupport)
    (p : G.Walk u v)
    (havoid : ∀ e' : G.edgeSet, e' ∈ node.candidate.edgeSupport →
      (e' : Sym2 V) ∉ p.edges) :
    report.status ≠ CAP5SeparatorGeneratorStatus.realizedSeparator := by
  intro hstatus
  have hcert := report.cert
  rw [hstatus] at hcert
  rcases hcert with ⟨_hportal, _hcycles, hrealized⟩
  exact node.not_realizedSeparator_of_candidate_edge_bypass
    he_pair hecut p havoid hrealized

/-- Under cyclic five-edge-connectivity and complete checker evidence, the certified status of a
generated CAP5 node is forced-counterexample.  This is the report-level falsification form of the
small-separator route. -/
theorem status_eq_forcedCounterexample_of_complete_of_cyclicallyFiveEdgeConnected
    {node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge}
    (report : node.Report) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal : node.PortalCrosses) (hcycles : node.SideCycles) :
    report.status = CAP5SeparatorGeneratorStatus.forcedCounterexample := by
  cases hstatus : report.status with
  | realizedSeparator =>
      exact False.elim
        (report.status_ne_realizedSeparator_of_cyclicallyFiveEdgeConnected hcyclic hstatus)
  | forcedCounterexample =>
      rfl
  | partialCase =>
      exact False.elim
        (report.status_ne_partialCase_of_complete hportal hcycles hstatus)

/-- Under complete checker evidence, a candidate-edge bypass witness forces the certified report
status to `forcedCounterexample`.  This is the report-level finite-witness form: a concrete
support-avoiding bypass refutes the realized-separator bin, and completeness rules out `partial`. -/
theorem status_eq_forcedCounterexample_of_complete_of_candidate_edge_bypass
    {node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge}
    (report : node.Report)
    (hportal : node.PortalCrosses) (hcycles : node.SideCycles)
    {u v : V} {e : G.edgeSet}
    (he_pair : (e : Sym2 V) = s(u, v))
    (hecut : e ∈ node.candidate.edgeSupport)
    (p : G.Walk u v)
    (havoid : ∀ e' : G.edgeSet, e' ∈ node.candidate.edgeSupport →
      (e' : Sym2 V) ∉ p.edges) :
    report.status = CAP5SeparatorGeneratorStatus.forcedCounterexample := by
  cases hstatus : report.status with
  | realizedSeparator =>
      exact False.elim
        (report.status_ne_realizedSeparator_of_candidate_edge_bypass
          he_pair hecut p havoid hstatus)
  | forcedCounterexample =>
      rfl
  | partialCase =>
      exact False.elim
        (report.status_ne_partialCase_of_complete hportal hcycles hstatus)

/-- Canonical certified report from three concrete checker decisions: whether the node has
portal crossings, whether it has cycles on both sides, and whether the proposed separator is
actually realized.  If the complete checker data is present but realization fails, the generic
holds-vs-counterexample theorem supplies the forced-counterexample certificate. -/
def ofDecidableChecks
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    [Decidable node.PortalCrosses] [Decidable node.SideCycles]
    [Decidable node.RealizedSeparator] :
    node.Report := by
  by_cases hportal : node.PortalCrosses
  · by_cases hcycles : node.SideCycles
    · by_cases hrealized : node.RealizedSeparator
      · exact
          { status := CAP5SeparatorGeneratorStatus.realizedSeparator
            cert := ⟨hportal, hcycles, hrealized⟩ }
      · have hforced : node.ForcedCounterexample := by
          rcases node.realizedSeparator_or_forcedCounterexample_of_complete hportal hcycles with
            hrealized' | hforced
          · exact False.elim (hrealized hrealized')
          · exact hforced
        exact
          { status := CAP5SeparatorGeneratorStatus.forcedCounterexample
            cert := ⟨hportal, hcycles, hforced⟩ }
    · exact
        { status := CAP5SeparatorGeneratorStatus.partialCase
          cert := Or.inr hcycles }
  · exact
      { status := CAP5SeparatorGeneratorStatus.partialCase
        cert := Or.inl hportal }

end Report

/-- A forced generator edge is exactly the emitted-edge predicate consumed by the existing
exceptional CAP5 algebraic lane, once the finite component-cover data realizes the node's
orientation. -/
theorem forcedCounterexampleEdge_to_exceptionalAnnulusOneEdgeCounterexampleEdge
    {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    (horientation :
      data.RealizesExceptionalBoundarySupportOrientation node.latent.orientation)
    {e : G.edgeSet} (hforced : node.ForcedCounterexampleEdge e) :
    data.ExceptionalAnnulusOneEdgeCounterexampleEdge
      node.latent.p0Inside node.latent.p4Inside node.side e := by
  rcases hforced with ⟨u, v, p, heOutside, hu, hv, hpEdges, havoid⟩
  exact ⟨node.candidate, by
    simpa [CAP5ExceptionalAnnulusGeneratorNode.candidate] using horientation,
    node.latent.candidate_sideCase_eq_ofPortalSides, u, v, p, heOutside, hu, hv,
    hpEdges, havoid⟩

/-- Existential bridge from the forced generator bin into the emitted-edge predicate used by the
non-geometric algebraic detector. -/
theorem exists_exceptionalAnnulusOneEdgeCounterexampleEdge_of_forcedCounterexample
    {n : Nat}
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    (horientation :
      data.RealizesExceptionalBoundarySupportOrientation node.latent.orientation)
    (hforced : node.ForcedCounterexample) :
    ∃ e : G.edgeSet,
      data.ExceptionalAnnulusOneEdgeCounterexampleEdge
        node.latent.p0Inside node.latent.p4Inside node.side e := by
  rcases hforced with ⟨e, hedge⟩
  exact ⟨e, node.forcedCounterexampleEdge_to_exceptionalAnnulusOneEdgeCounterexampleEdge
    horientation hedge⟩

end CAP5ExceptionalAnnulusGeneratorNode

/-- Certified finite CAP5 separator-generator report over the full latent list.  The report
classifies every orientation/portal-side latent, and each classification carries its Lean proof
obligation. -/
structure CAP5ExceptionalAnnulusGeneratorReport
    {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop) where
  classify : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge → CAP5SeparatorGeneratorStatus
  cert :
    ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      (let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
        { latent := latent, side := side };
        node.InBin (classify latent))

namespace CAP5ExceptionalAnnulusGeneratorReport

variable {G : SimpleGraph V}
variable {boundaryEdge : Fin 5 → G.edgeSet} {side : V → Prop}

/-- The node represented by a latent and a proposed side predicate, independent of any report. -/
def latentNode (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :
    CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
  { latent := latent, side := side }

/-- The node represented by one latent inside a full generator report. -/
def node (_report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :
    CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
  latentNode boundaryEdge side latent

/-- Extract the one-node certified report from a full generator report. -/
def nodeReport (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :
    (report.node latent).Report where
  status := report.classify latent
  cert := by
    simpa [node, latentNode] using report.cert latent

/-- Construct the full finite generator report from per-latent checker decisions.  This is the
operational report producer: a finite implementation can decide the portal, side-cycle, and
realization checks for each of the 16 latents, and this constructor turns those decisions into a
certified three-bin report. -/
def ofDecidableChecks
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)] :
    CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side where
  classify latent :=
    (CAP5ExceptionalAnnulusGeneratorNode.Report.ofDecidableChecks
      (latentNode boundaryEdge side latent)).status
  cert latent := by
    exact
      (CAP5ExceptionalAnnulusGeneratorNode.Report.ofDecidableChecks
        (latentNode boundaryEdge side latent)).cert

/-- Executable report theorem for one latent: the canonical finite report producer classifies a
complete cyclic-five CAP5 sample as forced-counterexample.  This is the direct bridge from a
checked sample to the bin predicted by the abstract report theorem. -/
theorem ofDecidableChecks_classify_eq_forcedCounterexample_of_complete_of_cyclicallyFiveEdgeConnected
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)]
    (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal : (latentNode boundaryEdge side latent).PortalCrosses)
    (hcycles : (latentNode boundaryEdge side latent).SideCycles) :
    (ofDecidableChecks boundaryEdge side).classify latent =
      CAP5SeparatorGeneratorStatus.forcedCounterexample := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  have hstatus :
      (report.nodeReport latent).status =
        CAP5SeparatorGeneratorStatus.forcedCounterexample :=
    (report.nodeReport latent).status_eq_forcedCounterexample_of_complete_of_cyclicallyFiveEdgeConnected
      hcyclic
      (by simpa [report, node, latentNode] using hportal)
      (by simpa [report, node, latentNode] using hcycles)
  simpa [report, nodeReport] using hstatus

/-- Executable report theorem for a concrete finite bypass witness.  If the portal and two-cycle
checks are complete, and one candidate edge has a support-avoiding bypass walk, the canonical
finite report producer classifies that latent as `forcedCounterexample`. -/
theorem ofDecidableChecks_classify_eq_forcedCounterexample_of_complete_of_candidate_edge_bypass
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)]
    (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge)
    (hportal : (latentNode boundaryEdge side latent).PortalCrosses)
    (hcycles : (latentNode boundaryEdge side latent).SideCycles)
    {u v : V} {e : G.edgeSet}
    (he_pair : (e : Sym2 V) = s(u, v))
    (hecut : e ∈ (latentNode boundaryEdge side latent).candidate.edgeSupport)
    (p : G.Walk u v)
    (havoid :
      ∀ e' : G.edgeSet, e' ∈ (latentNode boundaryEdge side latent).candidate.edgeSupport →
        (e' : Sym2 V) ∉ p.edges) :
    (ofDecidableChecks boundaryEdge side).classify latent =
      CAP5SeparatorGeneratorStatus.forcedCounterexample := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  have hstatus :
      (report.nodeReport latent).status =
        CAP5SeparatorGeneratorStatus.forcedCounterexample :=
    (report.nodeReport latent).status_eq_forcedCounterexample_of_complete_of_candidate_edge_bypass
      (by simpa [report, node, latentNode] using hportal)
      (by simpa [report, node, latentNode] using hcycles)
      he_pair
      (by simpa [report, node, latentNode] using hecut)
      p
      (by simpa [report, node, latentNode] using havoid)
  simpa [report, nodeReport] using hstatus

/-- Diagnostic contrapositive for one executable CAP5 sample.  If the canonical finite report
producer does not classify a latent as forced-counterexample, then cyclic five-edge-connectivity,
portal crossings, or two-sided cycles are missing.  This turns a non-forced sample output into a
precise prerequisite failure rather than another ambiguous route node. -/
theorem ofDecidableChecks_classify_ne_forcedCounterexample_implies_missing_prerequisite
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)]
    (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge)
    (hstatus :
      (ofDecidableChecks boundaryEdge side).classify latent ≠
        CAP5SeparatorGeneratorStatus.forcedCounterexample) :
    ¬ CyclicallyFiveEdgeConnected G ∨
      ¬ (latentNode boundaryEdge side latent).PortalCrosses ∨
        ¬ (latentNode boundaryEdge side latent).SideCycles := by
  by_cases hcyclic : CyclicallyFiveEdgeConnected G
  · by_cases hportal : (latentNode boundaryEdge side latent).PortalCrosses
    · by_cases hcycles : (latentNode boundaryEdge side latent).SideCycles
      · have hforced :=
          ofDecidableChecks_classify_eq_forcedCounterexample_of_complete_of_cyclicallyFiveEdgeConnected
            boundaryEdge side latent hcyclic hportal hcycles
        exact False.elim (hstatus hforced)
      · exact Or.inr <| Or.inr hcycles
    · exact Or.inr <| Or.inl hportal
  · exact Or.inl hcyclic

/-- Executable report diagnostic for a realized-separator output.  If the canonical finite
report producer classifies a latent as realized-separator, then the ambient graph cannot be
cyclically five-edge-connected.  Thus a concrete realized-bin sample is a cyclic-five refutation,
not evidence for the CAP5 route under the minimal-counterexample hypothesis. -/
theorem ofDecidableChecks_classify_eq_realizedSeparator_implies_not_cyclicallyFiveEdgeConnected
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)]
    (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge)
    (hstatus :
      (ofDecidableChecks boundaryEdge side).classify latent =
        CAP5SeparatorGeneratorStatus.realizedSeparator) :
    ¬ CyclicallyFiveEdgeConnected G := by
  intro hcyclic
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  have hstatus' :
      (report.nodeReport latent).status =
        CAP5SeparatorGeneratorStatus.realizedSeparator := by
    simpa [report, nodeReport] using hstatus
  exact (report.nodeReport latent).status_ne_realizedSeparator_of_cyclicallyFiveEdgeConnected
    hcyclic hstatus'

/-- Executable report diagnostic for a partial output.  A partial classification from the
canonical finite report producer means the sample is missing portal-crossing evidence or
two-sided cycle evidence for that latent. -/
theorem ofDecidableChecks_classify_eq_partialCase_implies_missing_checker_evidence
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)]
    (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge)
    (hstatus :
      (ofDecidableChecks boundaryEdge side).classify latent =
        CAP5SeparatorGeneratorStatus.partialCase) :
    ¬ (latentNode boundaryEdge side latent).PortalCrosses ∨
      ¬ (latentNode boundaryEdge side latent).SideCycles := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  have hcert : (report.node latent).InBin CAP5SeparatorGeneratorStatus.partialCase := by
    have hstatus' :
        report.classify latent = CAP5SeparatorGeneratorStatus.partialCase := by
      simpa [report] using hstatus
    have hcert' : (report.node latent).InBin (report.classify latent) := by
      simpa [nodeReport] using (report.nodeReport latent).cert
    simpa [hstatus'] using hcert'
  change (report.node latent).Partial at hcert
  simpa [CAP5ExceptionalAnnulusGeneratorNode.Partial, report, node, latentNode] using hcert

/-- Latents reported in the realized-separator bin. -/
def realizedSeparatorLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side) :
    List (CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :=
  (CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge).filter fun latent =>
    decide (report.classify latent = CAP5SeparatorGeneratorStatus.realizedSeparator)

/-- Latents reported in the forced-counterexample bin. -/
def forcedCounterexampleLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side) :
    List (CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :=
  (CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge).filter fun latent =>
    decide (report.classify latent = CAP5SeparatorGeneratorStatus.forcedCounterexample)

/-- Latents reported as partial checker runs. -/
def partialLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side) :
    List (CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :=
  (CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge).filter fun latent =>
    decide (report.classify latent = CAP5SeparatorGeneratorStatus.partialCase)

theorem mem_realizedSeparatorLatents_iff
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge} :
    latent ∈ report.realizedSeparatorLatents ↔
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        report.classify latent = CAP5SeparatorGeneratorStatus.realizedSeparator := by
  simp [realizedSeparatorLatents]

theorem mem_forcedCounterexampleLatents_iff
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge} :
    latent ∈ report.forcedCounterexampleLatents ↔
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        report.classify latent = CAP5SeparatorGeneratorStatus.forcedCounterexample := by
  simp [forcedCounterexampleLatents]

theorem mem_partialLatents_iff
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge} :
    latent ∈ report.partialLatents ↔
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        report.classify latent = CAP5SeparatorGeneratorStatus.partialCase := by
  simp [partialLatents]

/-- Every enumerated latent lands in exactly one of the three report bins. -/
theorem mem_one_status_bin_of_mem_all
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge) :
    latent ∈ report.realizedSeparatorLatents ∨
      latent ∈ report.forcedCounterexampleLatents ∨
        latent ∈ report.partialLatents := by
  cases hstatus : report.classify latent with
  | realizedSeparator =>
      exact Or.inl ((report.mem_realizedSeparatorLatents_iff).2 ⟨hmem, hstatus⟩)
  | forcedCounterexample =>
      exact Or.inr <| Or.inl ((report.mem_forcedCounterexampleLatents_iff).2 ⟨hmem, hstatus⟩)
  | partialCase =>
      exact Or.inr <| Or.inr ((report.mem_partialLatents_iff).2 ⟨hmem, hstatus⟩)

/-- The realized-separator and forced-counterexample report bins are disjoint. -/
theorem not_mem_forcedCounterexampleLatents_of_mem_realizedSeparatorLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.realizedSeparatorLatents) :
    latent ∉ report.forcedCounterexampleLatents := by
  intro hforced
  have hreal :
      report.classify latent = CAP5SeparatorGeneratorStatus.realizedSeparator :=
    (report.mem_realizedSeparatorLatents_iff).1 hmem |>.2
  have hforcedStatus :
      report.classify latent = CAP5SeparatorGeneratorStatus.forcedCounterexample :=
    (report.mem_forcedCounterexampleLatents_iff).1 hforced |>.2
  rw [hreal] at hforcedStatus
  cases hforcedStatus

/-- The realized-separator and partial report bins are disjoint. -/
theorem not_mem_partialLatents_of_mem_realizedSeparatorLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.realizedSeparatorLatents) :
    latent ∉ report.partialLatents := by
  intro hpartial
  have hreal :
      report.classify latent = CAP5SeparatorGeneratorStatus.realizedSeparator :=
    (report.mem_realizedSeparatorLatents_iff).1 hmem |>.2
  have hpartialStatus :
      report.classify latent = CAP5SeparatorGeneratorStatus.partialCase :=
    (report.mem_partialLatents_iff).1 hpartial |>.2
  rw [hreal] at hpartialStatus
  cases hpartialStatus

/-- The forced-counterexample and partial report bins are disjoint. -/
theorem not_mem_partialLatents_of_mem_forcedCounterexampleLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.forcedCounterexampleLatents) :
    latent ∉ report.partialLatents := by
  intro hpartial
  have hforced :
      report.classify latent = CAP5SeparatorGeneratorStatus.forcedCounterexample :=
    (report.mem_forcedCounterexampleLatents_iff).1 hmem |>.2
  have hpartialStatus :
      report.classify latent = CAP5SeparatorGeneratorStatus.partialCase :=
    (report.mem_partialLatents_iff).1 hpartial |>.2
  rw [hforced] at hpartialStatus
  cases hpartialStatus

/-- Membership in the realized-separator bin carries the certified realized-separator payload.
This is the consumer-facing soundness theorem for finite report outputs. -/
theorem inBin_realizedSeparator_of_mem_realizedSeparatorLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.realizedSeparatorLatents) :
    (report.node latent).InBin CAP5SeparatorGeneratorStatus.realizedSeparator := by
  have hstatus :
      report.classify latent = CAP5SeparatorGeneratorStatus.realizedSeparator :=
    (report.mem_realizedSeparatorLatents_iff).1 hmem |>.2
  have hcert : (report.node latent).InBin (report.classify latent) := by
    simpa [nodeReport] using (report.nodeReport latent).cert
  simpa [hstatus] using hcert

/-- Membership in the forced-counterexample bin carries the certified counterexample payload.
Finite checker runs can use this theorem to turn a list membership proof into the actual
outside-crossing edge witness. -/
theorem inBin_forcedCounterexample_of_mem_forcedCounterexampleLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.forcedCounterexampleLatents) :
    (report.node latent).InBin CAP5SeparatorGeneratorStatus.forcedCounterexample := by
  have hstatus :
      report.classify latent = CAP5SeparatorGeneratorStatus.forcedCounterexample :=
    (report.mem_forcedCounterexampleLatents_iff).1 hmem |>.2
  have hcert : (report.node latent).InBin (report.classify latent) := by
    simpa [nodeReport] using (report.nodeReport latent).cert
  simpa [hstatus] using hcert

/-- Membership in the partial bin carries the certified reason why the checker could not yet
resolve the node. -/
theorem inBin_partialCase_of_mem_partialLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.partialLatents) :
    (report.node latent).InBin CAP5SeparatorGeneratorStatus.partialCase := by
  have hstatus :
      report.classify latent = CAP5SeparatorGeneratorStatus.partialCase :=
    (report.mem_partialLatents_iff).1 hmem |>.2
  have hcert : (report.node latent).InBin (report.classify latent) := by
    simpa [nodeReport] using (report.nodeReport latent).cert
  simpa [hstatus] using hcert

/-- Projection of the realized-separator payload from a finite report bin. -/
theorem realizedSeparator_of_mem_realizedSeparatorLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.realizedSeparatorLatents) :
    (report.node latent).RealizedSeparator :=
  (report.inBin_realizedSeparator_of_mem_realizedSeparatorLatents hmem).2.2

/-- Projection of the forced-counterexample payload from a finite report bin. -/
theorem forcedCounterexample_of_mem_forcedCounterexampleLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.forcedCounterexampleLatents) :
    (report.node latent).ForcedCounterexample :=
  (report.inBin_forcedCounterexample_of_mem_forcedCounterexampleLatents hmem).2.2

/-- Projection of the partial-checker reason from a finite report bin. -/
theorem partial_of_mem_partialLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.partialLatents) :
    (report.node latent).Partial :=
  report.inBin_partialCase_of_mem_partialLatents hmem

/-- In a cyclically five-edge-connected graph, no certified report latent can remain in the
realized-separator bin: such a latent would expose a forbidden cyclic edge cut of size at most
four. -/
theorem not_mem_realizedSeparatorLatents_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge} :
    latent ∉ report.realizedSeparatorLatents := by
  intro hmem
  exact (report.node latent).not_realizedSeparator_of_cyclicallyFiveEdgeConnected hcyclic
    (report.realizedSeparator_of_mem_realizedSeparatorLatents hmem)

/-- A realized-separator bin entry is already a cyclic-five-connectivity refutation.
This is the consumer-facing finite-generator form: once the report emits a realized small
separator, the ambient graph is not a valid minimal-counterexample candidate. -/
theorem not_cyclicallyFiveEdgeConnected_of_mem_realizedSeparatorLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.realizedSeparatorLatents) :
    ¬ CyclicallyFiveEdgeConnected G := by
  intro hcyclic
  exact report.not_mem_realizedSeparatorLatents_of_cyclicallyFiveEdgeConnected hcyclic hmem

/-- Nonempty realized-separator report bins refute cyclic five-edge-connectivity. -/
theorem not_cyclicallyFiveEdgeConnected_of_exists_mem_realizedSeparatorLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (h : ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ report.realizedSeparatorLatents) :
    ¬ CyclicallyFiveEdgeConnected G := by
  rcases h with ⟨latent, hmem⟩
  exact report.not_cyclicallyFiveEdgeConnected_of_mem_realizedSeparatorLatents hmem

/-- A complete checker run has no partial latent: portal crossings and side cycles rule out both
ways that the report can honestly classify a latent as partial. -/
theorem not_mem_partialLatents_of_complete
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge} :
    latent ∉ report.partialLatents := by
  intro hmem
  rcases report.partial_of_mem_partialLatents hmem with hnotPortal | hnotCycles
  · exact hnotPortal (hportal latent)
  · exact hnotCycles (hcycles latent)

/-- If every generated latent has complete checker evidence in a cyclically five-edge-connected
graph, the full finite report has no realized or partial cases: every enumerated latent is forced
into the counterexample bin. -/
theorem mem_forcedCounterexampleLatents_of_mem_all_of_complete_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge) :
    latent ∈ report.forcedCounterexampleLatents := by
  have hstatus :
      report.classify latent = CAP5SeparatorGeneratorStatus.forcedCounterexample :=
    (report.nodeReport latent).status_eq_forcedCounterexample_of_complete_of_cyclicallyFiveEdgeConnected
      hcyclic (hportal latent) (hcycles latent)
  exact (report.mem_forcedCounterexampleLatents_iff).2 ⟨hmem, hstatus⟩

/-- Full-report form of the CAP5 generator boundary under cyclic five-edge-connectivity. -/
theorem all_latents_forcedCounterexample_of_complete_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles) :
    ∀ latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge,
      latent ∈ report.forcedCounterexampleLatents := by
  intro latent hmem
  exact report.mem_forcedCounterexampleLatents_of_mem_all_of_complete_of_cyclicallyFiveEdgeConnected
    hcyclic hportal hcycles hmem

/-- Exact bin-membership form of the complete cyclic-five report: the forced-counterexample bin
is precisely the finite latent enumeration. -/
theorem mem_forcedCounterexampleLatents_iff_mem_all_of_complete_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge} :
    latent ∈ report.forcedCounterexampleLatents ↔
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge := by
  constructor
  · intro hmem
    exact (report.mem_forcedCounterexampleLatents_iff).1 hmem |>.1
  · intro hmem
    exact report.mem_forcedCounterexampleLatents_of_mem_all_of_complete_of_cyclicallyFiveEdgeConnected
      hcyclic hportal hcycles hmem

/-- A cyclically five-edge-connected graph makes the realized-separator report bin empty. -/
theorem realizedSeparatorLatents_eq_nil_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    report.realizedSeparatorLatents = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro latent hmem
  exact report.not_mem_realizedSeparatorLatents_of_cyclicallyFiveEdgeConnected hcyclic hmem

/-- A complete checker run makes the partial report bin empty. -/
theorem partialLatents_eq_nil_of_complete
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles) :
    report.partialLatents = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro latent hmem
  exact report.not_mem_partialLatents_of_complete hportal hcycles hmem

/-- In a complete cyclic-five run, the forced-counterexample report bin is the whole finite
latent list.  This is the histogram form of the CAP5 generator falsification boundary. -/
theorem forcedCounterexampleLatents_eq_all_of_complete_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles) :
    report.forcedCounterexampleLatents =
      CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge := by
  unfold forcedCounterexampleLatents
  apply List.filter_eq_self.2
  intro latent hmem
  have hstatus :
      report.classify latent = CAP5SeparatorGeneratorStatus.forcedCounterexample :=
    (report.nodeReport latent).status_eq_forcedCounterexample_of_complete_of_cyclicallyFiveEdgeConnected
      hcyclic (hportal latent) (hcycles latent)
  simp [hstatus]

/-- Executable full-report theorem: when the canonical report producer is run with complete
checker evidence in a cyclically five-edge-connected graph, its forced-counterexample bin is
exactly the full sixteen-latent CAP5 enumeration. -/
theorem ofDecidableChecks_forcedCounterexampleLatents_eq_all_of_complete_of_cyclicallyFiveEdgeConnected
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)]
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (latentNode boundaryEdge side latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (latentNode boundaryEdge side latent).SideCycles) :
    (ofDecidableChecks boundaryEdge side).forcedCounterexampleLatents =
      CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  exact report.forcedCounterexampleLatents_eq_all_of_complete_of_cyclicallyFiveEdgeConnected
    hcyclic
    (by
      intro latent
      simpa [report, node, latentNode] using hportal latent)
    (by
      intro latent
      simpa [report, node, latentNode] using hcycles latent)

/-- Executable histogram theorem for complete cyclic-five CAP5 sample runs: the canonical report
producer emits exactly sixteen forced-counterexample latents. -/
theorem ofDecidableChecks_forcedCounterexampleLatents_length_eq_sixteen_of_complete_of_cyclicallyFiveEdgeConnected
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)]
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (latentNode boundaryEdge side latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (latentNode boundaryEdge side latent).SideCycles) :
    (ofDecidableChecks boundaryEdge side).forcedCounterexampleLatents.length = 16 := by
  rw [ofDecidableChecks_forcedCounterexampleLatents_eq_all_of_complete_of_cyclicallyFiveEdgeConnected
    boundaryEdge side hcyclic hportal hcycles]
  exact CAP5ExceptionalAnnulusGeneratorLatent.length_all boundaryEdge

/-- Cardinality form of the realized-bin emptiness theorem. -/
theorem realizedSeparatorLatents_length_eq_zero_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    report.realizedSeparatorLatents.length = 0 := by
  rw [report.realizedSeparatorLatents_eq_nil_of_cyclicallyFiveEdgeConnected hcyclic]
  rfl

/-- Cardinality form of the partial-bin emptiness theorem. -/
theorem partialLatents_length_eq_zero_of_complete
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles) :
    report.partialLatents.length = 0 := by
  rw [report.partialLatents_eq_nil_of_complete hportal hcycles]
  rfl

/-- Quantitative histogram form of the complete cyclic-five report: all sixteen generated latents
land in the forced-counterexample bin. -/
theorem forcedCounterexampleLatents_length_eq_sixteen_of_complete_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles) :
    report.forcedCounterexampleLatents.length = 16 := by
  rw [report.forcedCounterexampleLatents_eq_all_of_complete_of_cyclicallyFiveEdgeConnected
    hcyclic hportal hcycles]
  exact CAP5ExceptionalAnnulusGeneratorLatent.length_all boundaryEdge

/-- A complete CAP5 report in a cyclically five-edge-connected graph has a concrete
forced-counterexample latent.  This is the nonempty-output form consumed by finite checker runs:
the generated report cannot be vacuous once every latent has the graph-side evidence needed by the
checker. -/
theorem exists_mem_forcedCounterexampleLatents_of_complete_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles) :
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ report.forcedCounterexampleLatents := by
  let latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge :=
    { orientation := CAP5ExceptionalBoundarySupportOrientation.redBlue03_redPurple04
      p0Inside := true
      p4Inside := true }
  exact ⟨latent,
    report.mem_forcedCounterexampleLatents_of_mem_all_of_complete_of_cyclicallyFiveEdgeConnected
      hcyclic hportal hcycles (CAP5ExceptionalAnnulusGeneratorLatent.mem_all latent)⟩

end CAP5ExceptionalAnnulusGeneratorReport

namespace CAP5TransportedEdgeComponentCoverCore

variable {G : SimpleGraph V}
variable {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}

/-- Edge predicate emitted by the enumerated exceptional CAP5 witness generator.  The predicate
is intentionally tied to the finite latent list: an emitted edge comes from one of the sixteen
orientation/portal-side samples, with transported component-cover data realizing that sample's
orientation, and the generated node forced into the one-edge counterexample bin. -/
def EnumeratedExceptionalAnnulusForcedEdge
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool) (side : V → Prop) (e : G.edgeSet) : Prop :=
  ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
    latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
      latent.p0Inside = p0Inside ∧
        latent.p4Inside = p4Inside ∧
          data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
            (let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
              { latent := latent, side := side };
              node.ForcedCounterexampleEdge e)

/-- Every edge emitted by the enumerated exceptional CAP5 generator is a raw side-crossing edge.
This is the witness-generator output consumed by finite cyclic-cut and cocycle checks. -/
theorem enumeratedExceptionalAnnulusForcedEdge_crosses
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : V → Prop} {e : G.edgeSet}
    (h : data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) :
    EdgeCrossesVertexSide G side e := by
  rcases h with ⟨latent, _hmem, _hp0, _hp4, _horientation, hforced⟩
  let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
    { latent := latent, side := side }
  exact node.forcedCounterexampleEdge_crosses (by simpa [node] using hforced)

/-- Every edge emitted by the enumerated generator is an edge emitted by the broader exceptional
CAP5 one-edge counterexample predicate used by the algebraic lane. -/
theorem enumeratedExceptionalAnnulusForcedEdge_to_exceptionalAnnulusOneEdgeCounterexampleEdge
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : V → Prop} {e : G.edgeSet}
    (h :
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) :
    data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e := by
  rcases h with ⟨latent, _hmem, hp0, hp4, horientation, hforced⟩
  let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
    { latent := latent, side := side }
  have hedge :
      data.ExceptionalAnnulusOneEdgeCounterexampleEdge
        node.latent.p0Inside node.latent.p4Inside node.side e :=
    node.forcedCounterexampleEdge_to_exceptionalAnnulusOneEdgeCounterexampleEdge
      horientation (by simpa [node] using hforced)
  simpa [node, hp0, hp4] using hedge

/-- A forced latent emitted by a certified finite report gives an enumerated forced edge once the
component-cover data realizes that latent's orientation.  This is the report-output bridge into
the algebraic checker predicate. -/
theorem exists_enumeratedExceptionalAnnulusForcedEdge_of_mem_forcedCounterexampleLatents
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.forcedCounterexampleLatents)
    (horientation : data.RealizesExceptionalBoundarySupportOrientation latent.orientation) :
    ∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge
        latent.p0Inside latent.p4Inside side e := by
  have hlatentMem :
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge :=
    (report.mem_forcedCounterexampleLatents_iff).1 hmem |>.1
  rcases report.forcedCounterexample_of_mem_forcedCounterexampleLatents hmem with
    ⟨e, hedge⟩
  exact ⟨e, latent, hlatentMem, rfl, rfl, horientation, by
    simpa [CAP5ExceptionalAnnulusGeneratorReport.node,
      CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hedge⟩

/-- A forced latent emitted by a certified finite report gives the broader exceptional-annulus
one-edge counterexample consumed by the algebraic lane. -/
theorem exists_exceptionalAnnulusOneEdgeCounterexampleEdge_of_mem_forcedCounterexampleLatents
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.forcedCounterexampleLatents)
    (horientation : data.RealizesExceptionalBoundarySupportOrientation latent.orientation) :
    ∃ e : G.edgeSet,
      data.ExceptionalAnnulusOneEdgeCounterexampleEdge
        latent.p0Inside latent.p4Inside side e := by
  rcases data.exists_enumeratedExceptionalAnnulusForcedEdge_of_mem_forcedCounterexampleLatents
      report hmem horientation with
    ⟨e, hedge⟩
  exact ⟨e,
    data.enumeratedExceptionalAnnulusForcedEdge_to_exceptionalAnnulusOneEdgeCounterexampleEdge
      hedge⟩

/-- Report-level exceptional CAP5 emission theorem.  If a complete certified report is run in a
cyclically five-edge-connected graph, then any exceptional component-cover branch emits an
enumerated forced edge for the selected portal-side bits. -/
theorem exists_enumeratedExceptionalAnnulusForcedEdge_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles) :
    ∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
  rcases CAP5ExceptionalAnnulusGeneratorLatent.exists_mem_all_of_isExceptional_of_portalSides
      (boundaryEdge := boundaryEdge) p0Inside p4Inside h with
    ⟨latent, hlatentMem, hp0, hp4, horientation⟩
  have hforced :
      latent ∈ report.forcedCounterexampleLatents :=
    report.mem_forcedCounterexampleLatents_of_mem_all_of_complete_of_cyclicallyFiveEdgeConnected
      hcyclic hportal hcycles hlatentMem
  rcases data.exists_enumeratedExceptionalAnnulusForcedEdge_of_mem_forcedCounterexampleLatents
      report hforced horientation with
    ⟨e, hedge⟩
  exact ⟨e, by simpa [hp0, hp4] using hedge⟩

/-- Report-level bridge from a complete exceptional CAP5 report to the broader one-edge
counterexample predicate consumed by the algebraic lane. -/
theorem exists_exceptionalAnnulusOneEdgeCounterexampleEdge_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles) :
    ∃ e : G.edgeSet,
      data.ExceptionalAnnulusOneEdgeCounterexampleEdge p0Inside p4Inside side e := by
  rcases data.exists_enumeratedExceptionalAnnulusForcedEdge_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      report p0Inside p4Inside h hcyclic hportal hcycles with
    ⟨e, hedge⟩
  exact ⟨e,
    data.enumeratedExceptionalAnnulusForcedEdge_to_exceptionalAnnulusOneEdgeCounterexampleEdge
      hedge⟩

/-- Cyclic five-edge-connectivity makes the enumerated exceptional CAP5 generator emit at least
one forced edge for the selected portal-side bits, provided the graph-side portal crossings and
side cycles are certified. -/
theorem exists_enumeratedExceptionalAnnulusForcedEdge_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
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
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v)) :
    ∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
  rcases CAP5ExceptionalAnnulusGeneratorLatent.exists_mem_all_of_isExceptional_of_portalSides
      (boundaryEdge := boundaryEdge) p0Inside p4Inside h with
    ⟨latent, hmem, hp0, hp4, horientation⟩
  let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
    { latent := latent, side := side }
  have hnodePortal : node.PortalCrosses := by
    intro i hi
    have horientation' :
        data.RealizesExceptionalBoundarySupportOrientation
          node.candidate.portalCandidate.orientation := by
      simpa using horientation
    have hsideCase :
        node.candidate.portalCandidate.sideCase =
          CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside := by
      change CAP5ExceptionalAnnulusSideCase.ofPortalSides
          node.latent.p0Inside node.latent.p4Inside =
        CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside
      rw [hp0, hp4]
    exact hportal_crosses node.candidate horientation' hsideCase i hi
  rcases node.forcedCounterexample_of_cyclicallyFiveEdgeConnected
      hcyclic hnodePortal hcycles with
    ⟨e, hforced⟩
  exact ⟨e, latent, hmem, hp0, hp4, horientation, by simpa [node] using hforced⟩

/-- Raw-checker output form of the enumerated CAP5 generator: the emitted forced edge is also a
side-crossing edge, so finite samples can feed it directly to separator or cocycle checks. -/
theorem exists_crossing_enumeratedExceptionalAnnulusForcedEdge_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
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
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v)) :
    ∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
        EdgeCrossesVertexSide G side e := by
  rcases data.exists_enumeratedExceptionalAnnulusForcedEdge_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles with
    ⟨e, hedge⟩
  exact ⟨e, hedge, data.enumeratedExceptionalAnnulusForcedEdge_crosses hedge⟩

/-- Theorem 4.9 synthesis route from the finite enumerated CAP5 generator predicate.  The checker
target is local: every nonzero selected-boundary-zero chain exposes a nonzero coordinate on an
edge emitted by one of the enumerated forced CAP5 samples. -/
theorem theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeNonzeroWitnesses
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)
    (hwitnessRed :
      ∀ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_edgePredicateNonzeroWitnesses
    emb C₀ colorings hsubset family
    (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)
    hnonzero hwitnessRed hwitnessBlue

/-- Finite checker certificate for the edges emitted by the exceptional CAP5 generator.  A
checker can provide a concrete `Finset` of emitted edges; this proposition states that the finite
list is extensionally equal to the Lean predicate generated by the 16 CAP5 latents. -/
def EnumeratedExceptionalAnnulusForcedEdgeFinset
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool) (side : V → Prop) (emitted : Finset G.edgeSet) : Prop :=
  ∀ e : G.edgeSet,
    e ∈ emitted ↔ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e

/-- Canonical finite emitted-edge set when the enumerated generator predicate is decidable.  This
is the concrete artifact a finite checker can compute: filter all graph edges by the generated
CAP5 forced-edge predicate. -/
def enumeratedExceptionalAnnulusForcedEdgeFinset
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    [Fintype G.edgeSet]
    (p0Inside p4Inside : Bool) (side : V → Prop)
    [DecidablePred (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)] :
    Finset G.edgeSet :=
  Finset.univ.filter (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)

/-- The canonical filtered finite set is a correct emitted-edge certificate. -/
theorem enumeratedExceptionalAnnulusForcedEdgeFinset_spec
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (p0Inside p4Inside : Bool) (side : V → Prop)
    [DecidablePred (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)] :
    data.EnumeratedExceptionalAnnulusForcedEdgeFinset p0Inside p4Inside side
      (data.enumeratedExceptionalAnnulusForcedEdgeFinset p0Inside p4Inside side) := by
  intro e
  simp [enumeratedExceptionalAnnulusForcedEdgeFinset]

/-- Boolean checker certificate for the finite exceptional CAP5 generator.  The checker returns
`true` exactly on the edges emitted by the enumerated forced-edge predicate, so its filtered edge
list is an auditable finite artifact rather than an implicit decidability instance. -/
structure EnumeratedExceptionalAnnulusForcedEdgeClassifier
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool) (side : V → Prop) where
  accept : G.edgeSet → Bool
  accept_spec :
    ∀ e : G.edgeSet,
      accept e = true ↔ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e

namespace EnumeratedExceptionalAnnulusForcedEdgeClassifier

/-- The concrete finite edge set emitted by a Boolean exceptional CAP5 checker. -/
def emittedFinset
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    [Fintype G.edgeSet] :
    Finset G.edgeSet :=
  Finset.univ.filter (fun e => classifier.accept e = true)

/-- The filtered output of a correct Boolean checker is exactly the enumerated CAP5 forced-edge
predicate. -/
theorem emittedFinset_spec
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    data.EnumeratedExceptionalAnnulusForcedEdgeFinset p0Inside p4Inside side
      classifier.emittedFinset := by
  intro e
  simp [emittedFinset, classifier.accept_spec e]

end EnumeratedExceptionalAnnulusForcedEdgeClassifier

/-- Boolean classifier induced by a decidable enumerated CAP5 forced-edge predicate.  This is the
default bridge from Lean's decidable predicate form to an explicit Boolean checker artifact. -/
def enumeratedExceptionalAnnulusForcedEdgeClassifier
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    [DecidablePred (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)] :
    data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side where
  accept e := decide (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e)
  accept_spec e := by
    simp

/-- The decidable-predicate Boolean classifier emits the same finite edge set as the canonical
filtered predicate. -/
theorem enumeratedExceptionalAnnulusForcedEdgeClassifier_emittedFinset_eq
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (p0Inside p4Inside : Bool) (side : V → Prop)
    [DecidablePred (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)] :
    (data.enumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side).emittedFinset =
      data.enumeratedExceptionalAnnulusForcedEdgeFinset p0Inside p4Inside side := by
  ext e
  simp [EnumeratedExceptionalAnnulusForcedEdgeClassifier.emittedFinset,
    enumeratedExceptionalAnnulusForcedEdgeClassifier,
    enumeratedExceptionalAnnulusForcedEdgeFinset]

/-- The finite emitted-edge list is nonempty whenever the CAP5 generator emits a forced edge.
This is the first sanity check a finite forward run should pass under cyclic five-edge-connectivity:
the generated forced-counterexample bin must expose at least one concrete edge. -/
theorem enumeratedExceptionalAnnulusForcedEdgeFinset_nonempty_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emitted : Finset G.edgeSet)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hcert :
      data.EnumeratedExceptionalAnnulusForcedEdgeFinset p0Inside p4Inside side emitted)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v)) :
    emitted.Nonempty := by
  rcases data.exists_enumeratedExceptionalAnnulusForcedEdge_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles with
    ⟨e, hedge⟩
  exact ⟨e, (hcert e).2 hedge⟩

/-- Every edge in a certified finite emitted-edge set is a genuine side-crossing edge.  This is
the concrete finite-checker form consumed by later separator and cocycle audits. -/
theorem enumeratedExceptionalAnnulusForcedEdgeFinset_edges_cross
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {emitted : Finset G.edgeSet}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (hcert :
      data.EnumeratedExceptionalAnnulusForcedEdgeFinset p0Inside p4Inside side emitted)
    {e : G.edgeSet} (hemitted : e ∈ emitted) :
    EdgeCrossesVertexSide G side e :=
  data.enumeratedExceptionalAnnulusForcedEdge_crosses ((hcert e).1 hemitted)

/-- Strong finite-output sanity check for a complete cyclic-five exceptional CAP5 run: the
certified emitted-edge set contains an edge, and that edge is a raw side-crossing witness. -/
theorem exists_mem_enumeratedExceptionalAnnulusForcedEdgeFinset_crossing_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (emitted : Finset G.edgeSet)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop) (hcyclic : CyclicallyFiveEdgeConnected G)
    (hcert :
      data.EnumeratedExceptionalAnnulusForcedEdgeFinset p0Inside p4Inside side emitted)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v)) :
    ∃ e : G.edgeSet, e ∈ emitted ∧ EdgeCrossesVertexSide G side e := by
  rcases data.exists_crossing_enumeratedExceptionalAnnulusForcedEdge_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles with
    ⟨e, hedge, hcross⟩
  exact ⟨e, (hcert e).2 hedge, hcross⟩

/-- Every edge emitted by a Boolean exceptional CAP5 checker is a raw side-crossing edge. -/
theorem EnumeratedExceptionalAnnulusForcedEdgeClassifier.emittedFinset_edges_cross
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    {e : G.edgeSet} (hemitted : e ∈ classifier.emittedFinset) :
    EdgeCrossesVertexSide G side e :=
  data.enumeratedExceptionalAnnulusForcedEdgeFinset_edges_cross
    classifier.emittedFinset_spec hemitted

/-- Strong Boolean-checker output form for complete cyclic-five exceptional CAP5 runs: the
checker-emitted finite set contains an edge, and that edge is a raw side-crossing witness. -/
theorem EnumeratedExceptionalAnnulusForcedEdgeClassifier.exists_mem_emittedFinset_crossing_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop) (hcyclic : CyclicallyFiveEdgeConnected G)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v)) :
    ∃ e : G.edgeSet, e ∈ classifier.emittedFinset ∧ EdgeCrossesVertexSide G side e :=
  data.exists_mem_enumeratedExceptionalAnnulusForcedEdgeFinset_crossing_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    classifier.emittedFinset p0Inside p4Inside h side hcyclic
    classifier.emittedFinset_spec hportal_crosses hcycles

/-- False-negative guard for complete cyclic-five exceptional CAP5 Boolean runs: the checker
cannot emit the empty finite edge set.  An empty output falsifies one of the supplied hypotheses
rather than silently advancing the route. -/
theorem EnumeratedExceptionalAnnulusForcedEdgeClassifier.emittedFinset_nonempty_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop) (hcyclic : CyclicallyFiveEdgeConnected G)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v)) :
    classifier.emittedFinset.Nonempty := by
  rcases classifier.exists_mem_emittedFinset_crossing_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles with
    ⟨e, hemitted, _hcross⟩
  exact ⟨e, hemitted⟩

/-- Boolean form of the CAP5 false-negative guard: under the complete cyclic-five exceptional
hypotheses, some graph edge must be accepted by the checker and it is a genuine side-crossing
edge. -/
theorem EnumeratedExceptionalAnnulusForcedEdgeClassifier.exists_accept_true_crossing_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop) (hcyclic : CyclicallyFiveEdgeConnected G)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v)) :
    ∃ e : G.edgeSet,
      classifier.accept e = true ∧ EdgeCrossesVertexSide G side e := by
  rcases classifier.exists_mem_emittedFinset_crossing_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles with
    ⟨e, hemitted, hcross⟩
  exact ⟨e,
    by
      simpa [EnumeratedExceptionalAnnulusForcedEdgeClassifier.emittedFinset] using hemitted,
    hcross⟩

/-- A complete cyclic-five exceptional CAP5 Boolean checker cannot reject every edge.  This is
the executable all-false diagnostic form for finite witness-generator experiments. -/
theorem EnumeratedExceptionalAnnulusForcedEdgeClassifier.not_forall_accept_eq_false_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop) (hcyclic : CyclicallyFiveEdgeConnected G)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hportal_crosses :
      ∀ edgeCandidate : CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate boundaryEdge,
        data.RealizesExceptionalBoundarySupportOrientation
            edgeCandidate.portalCandidate.orientation →
        edgeCandidate.portalCandidate.sideCase =
            CAP5ExceptionalAnnulusSideCase.ofPortalSides p0Inside p4Inside →
        ∀ i : Fin 5, i ∈ edgeCandidate.portalCandidate.portalSet →
          EdgeCrossesVertexSide G side (boundaryEdge i))
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v)) :
    ¬ ∀ e : G.edgeSet, classifier.accept e = false := by
  intro hallFalse
  rcases classifier.exists_accept_true_crossing_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles with
    ⟨e, htrue, _hcross⟩
  rw [hallFalse e] at htrue
  contradiction

/-- Theorem 4.9 synthesis route from a concrete finite checker's control certificate.  The finite
rank-style obligation is: if a selected-boundary-zero chain vanishes on all emitted edges, then it
vanishes everywhere.  The edge-set certificate translates that concrete finite obligation back to
the enumerated CAP5 generator predicate. -/
theorem theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeFinsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (side : V → Prop) (emitted : Finset G.edgeSet)
    (hcert :
      data.EnumeratedExceptionalAnnulusForcedEdgeFinset p0Inside p4Inside side emitted)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ emitted, z e = 0) →
          z = 0)
    (hwitnessRed :
      ∀ e : G.edgeSet,
        e ∈ emitted →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        e ∈ emitted →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_edgePredicateFamilyPairingSeparation
    emb C₀ colorings hsubset family
    (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)
    (by
      intro z hz hvanish
      apply hcontrol hz
      intro e hemitted
      exact hvanish e ((hcert e).1 hemitted))
    (by
      intro e hedge
      exact hwitnessRed e ((hcert e).2 hedge))
    (by
      intro e hedge
      exact hwitnessBlue e ((hcert e).2 hedge))

/-- Theorem 4.9 synthesis route from the canonical filtered emitted-edge set.  Compared with the
abstract certificate form, the finite artifact is fixed to `Finset.univ.filter` on the generated
predicate, so a decidable checker can target this statement directly. -/
theorem theorem49BoundaryRootSynthesis_of_decidableEnumeratedExceptionalAnnulusForcedEdgeFinsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    [DecidablePred (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)]
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ data.enumeratedExceptionalAnnulusForcedEdgeFinset p0Inside p4Inside side,
          z e = 0) →
          z = 0)
    (hwitnessRed :
      ∀ e : G.edgeSet,
        e ∈ data.enumeratedExceptionalAnnulusForcedEdgeFinset p0Inside p4Inside side →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        e ∈ data.enumeratedExceptionalAnnulusForcedEdgeFinset p0Inside p4Inside side →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeFinsetControl
    emb C₀ colorings hsubset family p0Inside p4Inside side
    (data.enumeratedExceptionalAnnulusForcedEdgeFinset p0Inside p4Inside side)
    (data.enumeratedExceptionalAnnulusForcedEdgeFinset_spec p0Inside p4Inside side)
    hcontrol hwitnessRed hwitnessBlue

/-- Theorem 4.9 synthesis route from a Boolean exceptional CAP5 checker.  The classifier is the
operational finite artifact: after its correctness spec identifies the emitted edge set, the same
finite control/rank obligation discharges the boundary-root synthesis route. -/
theorem theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierControl
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
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
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
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeFinsetControl
    emb C₀ colorings hsubset family p0Inside p4Inside side classifier.emittedFinset
    classifier.emittedFinset_spec hcontrol hwitnessRed hwitnessBlue

/-- Witness form of the Boolean-classifier finite control obligation.  A classifier output
controls the selected-boundary-zero chains exactly when every nonzero such chain has a nonzero
coordinate on some emitted edge. -/
theorem enumeratedExceptionalAnnulusForcedEdgeClassifierControl_iff_forall_nonzero_exists_mem_nonzero
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side) :
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0) ↔
    (∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      z ≠ 0 →
        ∃ e : G.edgeSet, e ∈ classifier.emittedFinset ∧ z e ≠ 0) :=
  finsetControls_iff_forall_nonzero_exists_mem_nonzero classifier.emittedFinset

/-- Theorem 4.9 synthesis route from a Boolean classifier in nonzero-coordinate witness form.
This is the checker-facing shape: for each nonzero selected-boundary-zero chain, the finite
classifier output supplies an emitted coordinate where the chain is nonzero. -/
theorem theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierNonzeroWitnesses
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
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet, e ∈ classifier.emittedFinset ∧ z e ≠ 0)
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
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeNonzeroWitnesses
    emb C₀ colorings hsubset family p0Inside p4Inside side
    (by
      intro z hz hzNonzero
      rcases hnonzero hz hzNonzero with ⟨e, hemitted, hze⟩
      exact ⟨e, (classifier.emittedFinset_spec e).1 hemitted, hze⟩)
    (by
      intro e hedge
      exact hwitnessRed e ((classifier.emittedFinset_spec e).2 hedge))
    (by
      intro e hedge
      exact hwitnessBlue e ((classifier.emittedFinset_spec e).2 hedge))

/-- Failure certificate for the finite CAP5 emitted-edge control route.  If the concrete finite
checker output does not control the selected-boundary-zero chains, the failed check produces a
nonzero selected-boundary-zero chain that vanishes on every edge emitted by the enumerated CAP5
generator.  This is the falsification payload for the algebraic branch. -/
theorem exists_boundaryZeroChain_vanishingOnEnumeratedExceptionalAnnulusForcedEdges_of_not_finsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop) (emitted : Finset G.edgeSet)
    (hcert :
      data.EnumeratedExceptionalAnnulusForcedEdgeFinset p0Inside p4Inside side emitted)
    (hnotControl :
      ¬ ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ emitted, z e = 0) →
          z = 0) :
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          ∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0 := by
  rcases (not_finsetControls_iff_exists_nonzero_vanishes_on_finset
      (G := G) (emb := emb) emitted).1 hnotControl with
    ⟨z, hzBoundary, hzNonzero, hvanish⟩
  exact ⟨z, hzBoundary, hzNonzero, by
    intro e hedge
    exact hvanish e ((hcert e).2 hedge)⟩

/-- Falsification payload for the canonical filtered emitted-edge set.  If the finite checker's
kernel/control test fails on the generated `Finset.univ.filter` edge set, the result is a concrete
nonzero selected-boundary-zero chain invisible to every enumerated CAP5 emitted edge. -/
theorem exists_boundaryZeroChain_vanishingOnEnumeratedExceptionalAnnulusForcedEdges_of_not_decidableFinsetControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    [DecidablePred (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)]
    (hnotControl :
      ¬ ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ data.enumeratedExceptionalAnnulusForcedEdgeFinset p0Inside p4Inside side,
          z e = 0) →
          z = 0) :
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          ∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0 :=
  exists_boundaryZeroChain_vanishingOnEnumeratedExceptionalAnnulusForcedEdges_of_not_finsetControl
    emb p0Inside p4Inside side
    (data.enumeratedExceptionalAnnulusForcedEdgeFinset p0Inside p4Inside side)
    (data.enumeratedExceptionalAnnulusForcedEdgeFinset_spec p0Inside p4Inside side)
    hnotControl

/-- Falsification payload for a Boolean exceptional CAP5 checker.  If the classifier's finite
edge output does not control the selected-boundary-zero chains, the failed check returns a nonzero
boundary-zero chain invisible to every edge the generated CAP5 predicate can emit. -/
theorem exists_boundaryZeroChain_vanishingOnEnumeratedExceptionalAnnulusForcedEdges_of_not_classifierControl
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hnotControl :
      ¬ ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0) :
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          ∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0 :=
  exists_boundaryZeroChain_vanishingOnEnumeratedExceptionalAnnulusForcedEdges_of_not_finsetControl
    emb p0Inside p4Inside side classifier.emittedFinset classifier.emittedFinset_spec
    hnotControl

/-- Decidable finite-checker dichotomy for a Boolean exceptional CAP5 classifier.  Once the
checker supplies red/blue single-edge witnesses for every emitted edge, deciding the finite
control/rank obligation has exactly two outputs: either Theorem 4.9 boundary-root synthesis, or a
nonzero boundary-zero obstruction invisible to every generated CAP5 emitted edge. -/
theorem theorem49BoundaryRootSynthesis_or_boundaryZeroChainObstruction_of_classifierControl
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
    [Decidable
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)]
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
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0 := by
  by_cases hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0
  · exact Or.inl
      (theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierControl
        emb C₀ colorings hsubset family p0Inside p4Inside side classifier hcontrol
        hwitnessRed hwitnessBlue)
  · exact Or.inr
      (exists_boundaryZeroChain_vanishingOnEnumeratedExceptionalAnnulusForcedEdges_of_not_classifierControl
        emb p0Inside p4Inside side classifier hcontrol)

/-- Theorem 4.9 synthesis route from a concrete finite checker output.  The checker need only
certify that its finite edge set is exactly the enumerated CAP5 emitted-edge predicate, and then
prove the local nonzero/witness obligations by finite membership in that set. -/
theorem theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeFinsetNonzeroWitnesses
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (side : V → Prop) (emitted : Finset G.edgeSet)
    (hcert :
      data.EnumeratedExceptionalAnnulusForcedEdgeFinset p0Inside p4Inside side emitted)
    (hnonzero :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            e ∈ emitted ∧ z e ≠ 0)
    (hwitnessRed :
      ∀ e : G.edgeSet,
        e ∈ emitted →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red)
    (hwitnessBlue :
      ∀ e : G.edgeSet,
        e ∈ emitted →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue) :
    Theorem49BoundaryRootSynthesis emb C₀ :=
  theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeNonzeroWitnesses
    emb C₀ colorings hsubset family p0Inside p4Inside side
    (by
      intro z hz hzNonzero
      rcases hnonzero hz hzNonzero with ⟨e, hemitted, hze⟩
      exact ⟨e, (hcert e).1 hemitted, hze⟩)
    (by
      intro e hedge
      exact hwitnessRed e ((hcert e).2 hedge))
    (by
      intro e hedge
      exact hwitnessBlue e ((hcert e).2 hedge))

end CAP5TransportedEdgeComponentCoverCore

end Mettapedia.GraphTheory.FourColor
