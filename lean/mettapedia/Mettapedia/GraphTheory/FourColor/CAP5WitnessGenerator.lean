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

/-- Same-side realized bin: the generated candidate is exact cyclic-cut realization data for
the node's proposed side predicate.  The broader `RealizedSeparator` predicate intentionally
allows any realizing side; this sharper form is the one directly refuted by an outside crossing
edge emitted by the finite checker. -/
def RealizedSeparatorOnSide (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) : Prop :=
  ∃ realization : node.candidate.CyclicEdgeCutRealizationData (G := G),
    realization.side = node.side

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

/--
The forced-edge predicate is exactly the local edge-level falsifier for the generated support:
an emitted edge is forced precisely when it lies outside the candidate and crosses the proposed
side.  The stored one-edge walk witness is canonical data, not an additional assumption.
-/
theorem forcedCounterexampleEdge_iff_crossing_outside
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    {e : G.edgeSet} :
    node.ForcedCounterexampleEdge e ↔
      e ∉ node.candidate.edgeSupport ∧ EdgeCrossesVertexSide G node.side e := by
  constructor
  · intro h
    have hcross := node.forcedCounterexampleEdge_crosses h
    rcases h with ⟨_u, _v, _p, heOutside, _hu, _hv, _hpEdges, _havoid⟩
    exact ⟨heOutside, hcross⟩
  · rintro ⟨heOutside, hcross⟩
    rcases hcross with ⟨u, v, hu, hv, hsu, hsv⟩
    rcases exists_walk_edges_eq_singleton_of_edge_endpoint_sides
        (G := G) (side := node.side) (e := e) hu hv hsu hsv with
      ⟨p, hpEdges⟩
    refine ⟨u, v, p, heOutside, hsu, hsv, hpEdges, ?_⟩
    intro i hi hiEdges
    have hboundary_eq : boundaryEdge i = e := by
      apply Subtype.ext
      simpa [hpEdges] using hiEdges
    exact heOutside ((node.candidate.mem_edgeSupport_iff_exists_portal e).2
      ⟨i, hi, hboundary_eq⟩)

/--
The forced-counterexample bin is equivalently the existence of a non-candidate edge crossing the
proposed side.  This is the CAP5 generator's finite falsifier in its graph-local normal form.
-/
theorem forcedCounterexample_iff_exists_crossing_outside
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) :
    node.ForcedCounterexample ↔
      ∃ e : G.edgeSet, e ∉ node.candidate.edgeSupport ∧
        EdgeCrossesVertexSide G node.side e := by
  constructor
  · rintro ⟨e, hedge⟩
    exact ⟨e, (node.forcedCounterexampleEdge_iff_crossing_outside).1 hedge⟩
  · rintro ⟨e, hedge⟩
    exact ⟨e, (node.forcedCounterexampleEdge_iff_crossing_outside).2 hedge⟩

/-- A forced generator edge refutes realization of the candidate on the same proposed side.  The
emitted edge is outside the candidate support yet crosses the proposed side, so the proposed side
cannot make the support exactly equal to its crossing-edge cut. -/
theorem not_realizedSeparatorOnSide_of_forcedCounterexampleEdge
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    {e : G.edgeSet} (h : node.ForcedCounterexampleEdge e) :
    ¬ node.RealizedSeparatorOnSide := by
  have hcross : EdgeCrossesVertexSide G node.side e :=
    node.forcedCounterexampleEdge_crosses h
  rcases h with ⟨_u, _v, _p, heOutside, _hu, _hv, _hpEdges, _havoid⟩
  exact node.candidate.not_cyclicEdgeCutRealizationData_on_side_of_crossing_outside
    node.side heOutside hcross

/-- A forced-counterexample generator node refutes same-side realization of its candidate. -/
theorem not_realizedSeparatorOnSide_of_forcedCounterexample
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    (h : node.ForcedCounterexample) :
    ¬ node.RealizedSeparatorOnSide := by
  rcases h with ⟨e, hedge⟩
  exact node.not_realizedSeparatorOnSide_of_forcedCounterexampleEdge hedge

/-- Partial bin: the forward checker has not yet certified the graph-side prerequisites needed
for the generic holds-vs-counterexample theorem. -/
def Partial (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) : Prop :=
  ¬ node.PortalCrosses ∨ ¬ node.SideCycles

/-- Split form of the partial-bin obstruction.  A partial CAP5 node is missing either portal
crossing evidence, a cycle on the selected side, or a cycle on the complementary side. -/
def MissingCheckerEvidence (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) : Prop :=
  ¬ node.PortalCrosses ∨
    ¬ HasCycleOnSide G node.side ∨
      ¬ HasCycleOnSide G (fun v => ¬ node.side v)

/-- The portal-crossing checker has not yet certified every generated portal. -/
def MissingPortalCrossingEvidence
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) : Prop :=
  ¬ node.PortalCrosses

/-- The checker has not yet certified a cycle on the selected side. -/
def MissingSelectedSideCycleEvidence
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) : Prop :=
  ¬ HasCycleOnSide G node.side

/-- The checker has not yet certified a cycle on the complementary side. -/
def MissingComplementarySideCycleEvidence
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) : Prop :=
  ¬ HasCycleOnSide G (fun v => ¬ node.side v)

/-- The split missing-evidence predicate is the disjunction of its three primitive bins. -/
theorem missingCheckerEvidence_iff_missing_ingredient
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) :
    node.MissingCheckerEvidence ↔
      node.MissingPortalCrossingEvidence ∨
        node.MissingSelectedSideCycleEvidence ∨
          node.MissingComplementarySideCycleEvidence := by
  rfl

/-- The split missing-evidence predicate is exactly the older partial-bin predicate. -/
theorem partial_iff_missingCheckerEvidence
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) :
    node.Partial ↔ node.MissingCheckerEvidence := by
  classical
  constructor
  · rintro (hnotPortal | hnotCycles)
    · exact Or.inl hnotPortal
    · by_cases hinside : HasCycleOnSide G node.side
      · by_cases houtside : HasCycleOnSide G (fun v => ¬ node.side v)
        · exact False.elim (hnotCycles ⟨hinside, houtside⟩)
        · exact Or.inr (Or.inr houtside)
      · exact Or.inr (Or.inl hinside)
  · rintro (hnotPortal | hmissingCycle)
    · exact Or.inl hnotPortal
    · exact Or.inr <| by
        intro hcycles
        rcases hmissingCycle with hnotInside | hnotOutside
        · exact hnotInside hcycles.1
        · exact hnotOutside hcycles.2

/-- A generated node has no missing primitive checker evidence exactly when it is complete:
portal crossings and cycles on both sides are present. -/
theorem not_missingCheckerEvidence_iff_complete
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) :
    ¬ node.MissingCheckerEvidence ↔ node.PortalCrosses ∧ node.SideCycles := by
  classical
  constructor
  · intro hnotMissing
    by_cases hportal : node.PortalCrosses
    · by_cases hcycles : node.SideCycles
      · exact ⟨hportal, hcycles⟩
      · exact False.elim <| hnotMissing <|
          (node.partial_iff_missingCheckerEvidence).1 (Or.inr hcycles)
    · exact False.elim <| hnotMissing <|
        (node.partial_iff_missingCheckerEvidence).1 (Or.inl hportal)
  · rintro ⟨hportal, hcycles⟩ hmissing
    have hpartial : node.Partial :=
      (node.partial_iff_missingCheckerEvidence).2 hmissing
    rcases hpartial with hnotPortal | hnotCycles
    · exact hnotPortal hportal
    · exact hnotCycles hcycles

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

/-- Side-preserving version of the complete forward-checker boundary.  This is the form the
planar/Jordan layer needs: the realized branch remembers that the candidate support realizes the
node's proposed side, while the forced branch emits the same one-edge counterexample as before. -/
theorem realizedSeparatorOnSide_or_forcedCounterexample_of_complete
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    (hportal : node.PortalCrosses) (hcycles : node.SideCycles) :
    node.RealizedSeparatorOnSide ∨ node.ForcedCounterexample := by
  rcases hcycles with ⟨hinside_cycle, houtside_cycle⟩
  rcases node.candidate
      |>.cyclicEdgeCutRealizationDataOnSide_or_oneEdge_walk_avoiding_portalBoundaryEdges_of_portal_crosses
        node.side hportal hinside_cycle houtside_cycle with
    hrealized | hforced
  · exact Or.inl hrealized
  · rcases hforced with ⟨u, v, e, p, heOutside, hu, hv, hpEdges, havoid⟩
    exact Or.inr ⟨e, u, v, p, heOutside, hu, hv, hpEdges, havoid⟩

/-- For a complete generated node, same-side realization is exactly the absence of a forced
counterexample.  This is the finite checker's exact holds-vs-falsifier boundary for the selected
side. -/
theorem realizedSeparatorOnSide_iff_not_forcedCounterexample_of_complete
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    (hportal : node.PortalCrosses) (hcycles : node.SideCycles) :
    node.RealizedSeparatorOnSide ↔ ¬ node.ForcedCounterexample := by
  constructor
  · intro hreal hforced
    exact node.not_realizedSeparatorOnSide_of_forcedCounterexample hforced hreal
  · intro hnotForced
    rcases node.realizedSeparatorOnSide_or_forcedCounterexample_of_complete hportal hcycles with
      hreal | hforced
    · exact hreal
    · exact False.elim (hnotForced hforced)

/-- For a complete generated node, the forced-counterexample bin is exactly failure of same-side
realization. -/
theorem forcedCounterexample_iff_not_realizedSeparatorOnSide_of_complete
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    (hportal : node.PortalCrosses) (hcycles : node.SideCycles) :
    node.ForcedCounterexample ↔ ¬ node.RealizedSeparatorOnSide := by
  constructor
  · exact node.not_realizedSeparatorOnSide_of_forcedCounterexample
  · intro hnotReal
    rcases node.realizedSeparatorOnSide_or_forcedCounterexample_of_complete hportal hcycles with
      hreal | hforced
    · exact False.elim (hnotReal hreal)
    · exact hforced

/-- Complete generated nodes realize the selected side exactly when no non-candidate edge crosses
that side.  This is the graph-local normal form of the CAP5 generator boundary. -/
theorem realizedSeparatorOnSide_iff_no_crossing_outside_of_complete
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    (hportal : node.PortalCrosses) (hcycles : node.SideCycles) :
    node.RealizedSeparatorOnSide ↔
      ¬ ∃ e : G.edgeSet, e ∉ node.candidate.edgeSupport ∧
        EdgeCrossesVertexSide G node.side e := by
  rw [node.realizedSeparatorOnSide_iff_not_forcedCounterexample_of_complete hportal hcycles,
    node.forcedCounterexample_iff_exists_crossing_outside]

/-- Complete generated nodes fail to realize the selected side exactly when there is a concrete
non-candidate edge crossing that side.  This is the CAP5 node-level falsification boundary for
the planar/Jordan separator route. -/
theorem not_realizedSeparatorOnSide_iff_exists_crossing_outside_of_complete
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    (hportal : node.PortalCrosses) (hcycles : node.SideCycles) :
    ¬ node.RealizedSeparatorOnSide ↔
      ∃ e : G.edgeSet, e ∉ node.candidate.edgeSupport ∧
        EdgeCrossesVertexSide G node.side e :=
  (node.forcedCounterexample_iff_not_realizedSeparatorOnSide_of_complete
    hportal hcycles).symm.trans node.forcedCounterexample_iff_exists_crossing_outside

/--
Node-level proof-as-generator boundary.  A generated CAP5 node is either missing primitive
checker evidence, realizes the proposed side exactly, or emits a forced counterexample.  This is
the local holds / partial / forced-counterexample split independent of any report histogram.
-/
theorem missingCheckerEvidence_or_realizedSeparatorOnSide_or_forcedCounterexample
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge) :
    node.MissingCheckerEvidence ∨ node.RealizedSeparatorOnSide ∨ node.ForcedCounterexample := by
  classical
  by_cases hmissing : node.MissingCheckerEvidence
  · exact Or.inl hmissing
  · rcases (node.not_missingCheckerEvidence_iff_complete).1 hmissing with
      ⟨hportal, hcycles⟩
    exact Or.inr (node.realizedSeparatorOnSide_or_forcedCounterexample_of_complete
      hportal hcycles)

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

/-- Side-preserving data-level generator theorem.  This keeps the selected enumerated latent
visible while resolving it into the exact-side realized branch or the forced-counterexample
branch.  It is the sample-level boundary used by the proof-as-generator pass. -/
theorem exists_enumeratedNode_realizedSeparatorOnSide_or_forcedCounterexample_of_isExceptional_of_portalSides
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
                node.RealizedSeparatorOnSide ∨ node.ForcedCounterexample) := by
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
    node.realizedSeparatorOnSide_or_forcedCounterexample_of_complete hnodePortal hcycles
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

/--
Cyclic-five specialization of the node-level generator boundary.  In a cyclically five-edge
connected graph, a generated CAP5 node is either still missing primitive checker evidence, or it
has a forced counterexample.
-/
theorem missingCheckerEvidence_or_forcedCounterexample_of_cyclicallyFiveEdgeConnected
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    node.MissingCheckerEvidence ∨ node.ForcedCounterexample := by
  classical
  by_cases hmissing : node.MissingCheckerEvidence
  · exact Or.inl hmissing
  · rcases (node.not_missingCheckerEvidence_iff_complete).1 hmissing with
      ⟨hportal, hcycles⟩
    exact Or.inr (node.forcedCounterexample_of_cyclicallyFiveEdgeConnected
      hcyclic hportal hcycles)

/--
Concrete-edge form of the cyclic-five generator boundary.  Once cyclic five-edge-connectivity is
assumed, every generated CAP5 node either exposes the primitive checker evidence still missing or
emits an actual non-candidate edge crossing the proposed side.
-/
theorem missingCheckerEvidence_or_exists_crossing_outside_of_cyclicallyFiveEdgeConnected
    (node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    node.MissingCheckerEvidence ∨
      ∃ e : G.edgeSet, e ∉ node.candidate.edgeSupport ∧
        EdgeCrossesVertexSide G node.side e := by
  rcases node.missingCheckerEvidence_or_forcedCounterexample_of_cyclicallyFiveEdgeConnected
      hcyclic with hmissing | hforced
  · exact Or.inl hmissing
  · exact Or.inr ((node.forcedCounterexample_iff_exists_crossing_outside).1 hforced)

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

/-- A certified partial status is exactly missing checker evidence: portal-crossing evidence or
two-sided cycle evidence failed for this generated node. -/
theorem status_eq_partialCase_iff_missing_checker_evidence
    {node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge}
    (report : node.Report) :
    report.status = CAP5SeparatorGeneratorStatus.partialCase ↔
      ¬ node.PortalCrosses ∨ ¬ node.SideCycles := by
  constructor
  · intro hstatus
    have hcert := report.cert
    rw [hstatus] at hcert
    change node.Partial at hcert
    exact hcert
  · intro hpartial
    cases hstatus : report.status with
    | realizedSeparator =>
        have hcert := report.cert
        rw [hstatus] at hcert
        rcases hcert with ⟨hportal, hcycles, _hrealized⟩
        exact False.elim <| by
          rcases hpartial with hnotPortal | hnotCycles
          · exact hnotPortal hportal
          · exact hnotCycles hcycles
    | forcedCounterexample =>
        have hcert := report.cert
        rw [hstatus] at hcert
        rcases hcert with ⟨hportal, hcycles, _hforced⟩
        exact False.elim <| by
          rcases hpartial with hnotPortal | hnotCycles
          · exact hnotPortal hportal
          · exact hnotCycles hcycles
    | partialCase =>
        rfl

/-- Split form of `status_eq_partialCase_iff_missing_checker_evidence`: a certified partial
status is exactly one of the three primitive missing checker obligations. -/
theorem status_eq_partialCase_iff_missingCheckerEvidence
    {node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge}
    (report : node.Report) :
    report.status = CAP5SeparatorGeneratorStatus.partialCase ↔
      node.MissingCheckerEvidence := by
  have hpartial :
      report.status = CAP5SeparatorGeneratorStatus.partialCase ↔ node.Partial := by
    simpa [CAP5ExceptionalAnnulusGeneratorNode.Partial] using
      report.status_eq_partialCase_iff_missing_checker_evidence
  exact hpartial.trans node.partial_iff_missingCheckerEvidence

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

/-- A full generator report classifies one latent as partial exactly when that latent is missing
portal-crossing evidence or two-sided cycle evidence. -/
theorem classify_eq_partialCase_iff_missing_checker_evidence
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :
    report.classify latent = CAP5SeparatorGeneratorStatus.partialCase ↔
      ¬ (report.node latent).PortalCrosses ∨ ¬ (report.node latent).SideCycles := by
  simpa [nodeReport] using
    (report.nodeReport latent).status_eq_partialCase_iff_missing_checker_evidence

/-- Split form of the partial-status theorem for full reports. -/
theorem classify_eq_partialCase_iff_missingCheckerEvidence
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :
    report.classify latent = CAP5SeparatorGeneratorStatus.partialCase ↔
      (report.node latent).MissingCheckerEvidence := by
  simpa [nodeReport] using
    (report.nodeReport latent).status_eq_partialCase_iff_missingCheckerEvidence

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

/-- Executable exactness theorem for a partial output.  The canonical finite report producer
classifies a latent as partial exactly when portal-crossing evidence or two-sided cycle evidence
is missing for that latent. -/
theorem ofDecidableChecks_classify_eq_partialCase_iff_missing_checker_evidence
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)]
    (latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) :
    (ofDecidableChecks boundaryEdge side).classify latent =
        CAP5SeparatorGeneratorStatus.partialCase ↔
      ¬ (latentNode boundaryEdge side latent).PortalCrosses ∨
        ¬ (latentNode boundaryEdge side latent).SideCycles := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  have hstatus := report.classify_eq_partialCase_iff_missing_checker_evidence latent
  simpa [report, node, latentNode] using hstatus

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

/-- Latents whose graph-side checker evidence is incomplete: a portal crossing is missing,
or one of the two side-cycle witnesses is missing.  This is the diagnostic frontier the
finite generator should mine before treating a non-all-forced report as mathematical evidence. -/
noncomputable def missingCheckerEvidenceLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side) :
    List (CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) := by
  classical
  exact (CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge).filter fun latent =>
    decide ((report.node latent).MissingCheckerEvidence)

/-- Latents with all primitive checker evidence present: portal crossings and two side
cycles.  Under cyclic five-edge-connectivity these are exactly the forced-counterexample
latents, so this list is the computable complement of the missing-evidence frontier. -/
noncomputable def completeCheckerLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side) :
    List (CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge) := by
  classical
  exact (CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge).filter fun latent =>
    decide (¬ (report.node latent).MissingCheckerEvidence)

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

/-- Membership in the primitive missing-evidence frontier. -/
theorem mem_missingCheckerEvidenceLatents_iff
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge} :
    latent ∈ report.missingCheckerEvidenceLatents ↔
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (report.node latent).MissingCheckerEvidence := by
  classical
  simp [missingCheckerEvidenceLatents]

/-- Membership in the primitive complete-checker frontier. -/
theorem mem_completeCheckerLatents_iff
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge} :
    latent ∈ report.completeCheckerLatents ↔
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        ¬ (report.node latent).MissingCheckerEvidence := by
  classical
  simp [completeCheckerLatents]

/-- The primitive finite checker frontier is exhaustive: every enumerated latent is either
missing primitive checker evidence or belongs to the complete-checker frontier. -/
theorem mem_missingCheckerEvidenceLatents_or_mem_completeCheckerLatents_of_mem_all
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge) :
    latent ∈ report.missingCheckerEvidenceLatents ∨
      latent ∈ report.completeCheckerLatents := by
  classical
  by_cases hmissing : (report.node latent).MissingCheckerEvidence
  · exact Or.inl ((report.mem_missingCheckerEvidenceLatents_iff).2 ⟨hmem, hmissing⟩)
  · exact Or.inr ((report.mem_completeCheckerLatents_iff).2 ⟨hmem, hmissing⟩)

/-- Membership in the finite CAP5 latent enumeration is exactly membership in one of the two
primitive checker frontiers: missing evidence or complete evidence.  This is the list-level
contract consumed by finite enumeration passes. -/
theorem mem_all_iff_mem_missingCheckerEvidenceLatents_or_mem_completeCheckerLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge} :
    latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ↔
      latent ∈ report.missingCheckerEvidenceLatents ∨
        latent ∈ report.completeCheckerLatents := by
  constructor
  · exact report.mem_missingCheckerEvidenceLatents_or_mem_completeCheckerLatents_of_mem_all
  · intro hfrontier
    rcases hfrontier with hmissing | hcomplete
    · exact (report.mem_missingCheckerEvidenceLatents_iff).1 hmissing |>.1
    · exact (report.mem_completeCheckerLatents_iff).1 hcomplete |>.1

/-- The two primitive checker frontiers are disjoint. -/
theorem not_mem_completeCheckerLatents_of_mem_missingCheckerEvidenceLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmissingMem : latent ∈ report.missingCheckerEvidenceLatents) :
    latent ∉ report.completeCheckerLatents := by
  intro hcompleteMem
  exact ((report.mem_completeCheckerLatents_iff).1 hcompleteMem |>.2)
    ((report.mem_missingCheckerEvidenceLatents_iff).1 hmissingMem |>.2)

/-- Symmetric disjointness form for the primitive checker frontiers. -/
theorem not_mem_missingCheckerEvidenceLatents_of_mem_completeCheckerLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hcompleteMem : latent ∈ report.completeCheckerLatents) :
    latent ∉ report.missingCheckerEvidenceLatents := by
  intro hmissingMem
  exact report.not_mem_completeCheckerLatents_of_mem_missingCheckerEvidenceLatents
    hmissingMem hcompleteMem

/-- The complete-checker frontier covers all sixteen finite latents exactly when the
missing-evidence frontier is empty. -/
theorem completeCheckerLatents_eq_all_iff_missingCheckerEvidenceLatents_eq_nil
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side) :
    report.completeCheckerLatents =
        CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ↔
      report.missingCheckerEvidenceLatents = [] := by
  constructor
  · intro hcompleteAll
    apply List.eq_nil_iff_forall_not_mem.2
    intro latent hmissingMem
    have hmemAll :
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge :=
      (report.mem_missingCheckerEvidenceLatents_iff).1 hmissingMem |>.1
    have hcompleteMem : latent ∈ report.completeCheckerLatents := by
      simpa [hcompleteAll] using hmemAll
    exact report.not_mem_completeCheckerLatents_of_mem_missingCheckerEvidenceLatents
      hmissingMem hcompleteMem
  · intro hmissingEmpty
    unfold completeCheckerLatents
    apply List.filter_eq_self.2
    intro latent hmemAll
    have hnotMissing : ¬ (report.node latent).MissingCheckerEvidence := by
      intro hmissing
      have hmissingMem : latent ∈ report.missingCheckerEvidenceLatents :=
        (report.mem_missingCheckerEvidenceLatents_iff).2 ⟨hmemAll, hmissing⟩
      have hnil : latent ∈ ([] :
          List (CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge)) := by
        rw [hmissingEmpty] at hmissingMem
        exact hmissingMem
      cases hnil
    simp [hnotMissing]

/-- The certified partial bin is exactly the primitive missing-checker-evidence frontier. -/
theorem partialLatents_eq_missingCheckerEvidenceLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side) :
    report.partialLatents = report.missingCheckerEvidenceLatents := by
  classical
  unfold partialLatents missingCheckerEvidenceLatents
  apply List.filter_congr
  intro latent _hmem
  by_cases hstatus :
      report.classify latent = CAP5SeparatorGeneratorStatus.partialCase
  · have hmissing :
        (report.node latent).MissingCheckerEvidence :=
      (report.classify_eq_partialCase_iff_missingCheckerEvidence latent).1 hstatus
    simp [hstatus, hmissing]
  · have hmissing :
        ¬ (report.node latent).MissingCheckerEvidence := by
      intro h
      exact hstatus
        ((report.classify_eq_partialCase_iff_missingCheckerEvidence latent).2 h)
    simp [hstatus, hmissing]

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

/-- A forced-counterexample report-bin entry refutes realization of the generated candidate on
the report's proposed side.  It does not claim to refute arbitrary realization data with an
unrelated side predicate. -/
theorem not_realizedSeparatorOnSide_of_mem_forcedCounterexampleLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.forcedCounterexampleLatents) :
    ¬ (report.node latent).RealizedSeparatorOnSide :=
  (report.node latent).not_realizedSeparatorOnSide_of_forcedCounterexample
    (report.forcedCounterexample_of_mem_forcedCounterexampleLatents hmem)

/-- A forced-counterexample report-bin entry carries a concrete emitted edge that crosses the
reported side.  This is the raw graph-theoretic output consumed by finite cocycle/algebraic
checks. -/
theorem exists_forcedCounterexampleEdge_crossing_of_mem_forcedCounterexampleLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.forcedCounterexampleLatents) :
    ∃ e : G.edgeSet,
      (report.node latent).ForcedCounterexampleEdge e ∧
        EdgeCrossesVertexSide G side e := by
  rcases report.forcedCounterexample_of_mem_forcedCounterexampleLatents hmem with
    ⟨e, hedge⟩
  exact ⟨e, hedge, by
    simpa [node, latentNode] using (report.node latent).forcedCounterexampleEdge_crosses hedge⟩

/-- Normal-form payload of a forced-counterexample report-bin entry: it gives a concrete edge
outside the generated candidate support that crosses the reported side.  This is the finite
failed-separator sample consumed by the separator and algebraic follow-up checks. -/
theorem exists_crossing_outside_of_mem_forcedCounterexampleLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.forcedCounterexampleLatents) :
    ∃ e : G.edgeSet,
      e ∉ (report.node latent).candidate.edgeSupport ∧
        EdgeCrossesVertexSide G side e := by
  rcases report.forcedCounterexample_of_mem_forcedCounterexampleLatents hmem with
    ⟨e, hedge⟩
  have hnormal :
      e ∉ (report.node latent).candidate.edgeSupport ∧
        EdgeCrossesVertexSide G (report.node latent).side e :=
    ((report.node latent).forcedCounterexampleEdge_iff_crossing_outside (e := e)).1 hedge
  exact ⟨e, hnormal.1, by simpa [node, latentNode] using hnormal.2⟩

/-- A forced-counterexample report-bin entry carries the full one-edge avoiding-walk witness
emitted by the checker.  This is the finite data a cocycle or algebraic-cancellation pass can
consume directly: endpoints on opposite sides, the emitted outside edge, the one-edge walk, and
avoidance of the generated portal boundary edges. -/
theorem exists_oneEdge_forcedCounterexampleWalk_of_mem_forcedCounterexampleLatents
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.forcedCounterexampleLatents) :
    ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
      e ∉ (report.node latent).candidate.edgeSupport ∧
        side u ∧ ¬ side v ∧
          p.edges = [(e : Sym2 V)] ∧
            (∀ i : Fin 5, i ∈ (report.node latent).candidate.portalCandidate.portalSet →
              ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
              EdgeCrossesVertexSide G side e := by
  rcases report.exists_forcedCounterexampleEdge_crossing_of_mem_forcedCounterexampleLatents
      hmem with
    ⟨e, hedge, hcross⟩
  rcases hedge with ⟨u, v, p, heOutside, hu, hv, hpEdges, havoid⟩
  exact ⟨u, v, e, p, heOutside,
    by simpa [node, latentNode] using hu,
    by simpa [node, latentNode] using hv,
    hpEdges, havoid, hcross⟩

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

/-- Exact partial-bin boundary: the partial report bin is empty exactly when every enumerated
latent has the two checker ingredients that rule out partiality, namely portal crossings and
side cycles.  This theorem does not need cyclic five-edge-connectivity; it isolates the finite
checker frontier before any global minimal-counterexample hypothesis is used. -/
theorem partialLatents_eq_nil_iff_all_checker_evidence
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side) :
    report.partialLatents = [] ↔
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge →
          (report.node latent).PortalCrosses ∧
            (report.node latent).SideCycles := by
  constructor
  · intro hpartialEmpty latent hmem
    have hnotMissing :
        ¬ (¬ (report.node latent).PortalCrosses ∨
          ¬ (report.node latent).SideCycles) := by
      intro hmissing
      have hstatus :
          report.classify latent = CAP5SeparatorGeneratorStatus.partialCase :=
        (report.classify_eq_partialCase_iff_missing_checker_evidence latent).2 hmissing
      have hpartial : latent ∈ report.partialLatents :=
        (report.mem_partialLatents_iff).2 ⟨hmem, hstatus⟩
      have hnil : latent ∈ ([] :
          List (CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge)) := by
        rw [hpartialEmpty] at hpartial
        exact hpartial
      cases hnil
    constructor
    · by_contra hnotPortal
      exact hnotMissing (Or.inl hnotPortal)
    · by_contra hnotCycles
      exact hnotMissing (Or.inr hnotCycles)
  · intro hcomplete
    apply List.eq_nil_iff_forall_not_mem.2
    intro latent hpartial
    have hpartialData := (report.mem_partialLatents_iff).1 hpartial
    have hcompleteLatent := hcomplete latent hpartialData.1
    have hmissing :
        ¬ (report.node latent).PortalCrosses ∨
          ¬ (report.node latent).SideCycles :=
      (report.classify_eq_partialCase_iff_missing_checker_evidence latent).1
        hpartialData.2
    rcases hmissing with hnotPortal | hnotCycles
    · exact hnotPortal hcompleteLatent.1
    · exact hnotCycles hcompleteLatent.2

/-- Nonempty partial-bin form of the same boundary: a finite report has a partial latent exactly
when some enumerated latent is missing portal-crossing evidence or side-cycle evidence. -/
theorem partialLatents_ne_nil_iff_exists_missing_checker_evidence
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side) :
    report.partialLatents ≠ [] ↔
      ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
          (¬ (report.node latent).PortalCrosses ∨
            ¬ (report.node latent).SideCycles) := by
  constructor
  · intro hpartialNonempty
    by_contra hnone
    have hpartialEmpty : report.partialLatents = [] := by
      apply (report.partialLatents_eq_nil_iff_all_checker_evidence).2
      intro latent hmem
      have hnotMissing :
          ¬ (¬ (report.node latent).PortalCrosses ∨
            ¬ (report.node latent).SideCycles) := by
        intro hmissing
        exact hnone ⟨latent, hmem, hmissing⟩
      constructor
      · by_contra hnotPortal
        exact hnotMissing (Or.inl hnotPortal)
      · by_contra hnotCycles
        exact hnotMissing (Or.inr hnotCycles)
    exact hpartialNonempty hpartialEmpty
  · rintro ⟨latent, hmem, hmissing⟩ hpartialEmpty
    have hstatus :
        report.classify latent = CAP5SeparatorGeneratorStatus.partialCase :=
      (report.classify_eq_partialCase_iff_missing_checker_evidence latent).2 hmissing
    have hpartial : latent ∈ report.partialLatents :=
      (report.mem_partialLatents_iff).2 ⟨hmem, hstatus⟩
    have hnil : latent ∈ ([] :
        List (CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge)) := by
      rw [hpartialEmpty] at hpartial
      exact hpartial
    cases hnil

/-- Split obstruction form of the nonempty partial-bin boundary.  A nonempty partial list is
equivalent to a concrete enumerated latent missing one primitive checker ingredient: portal
crossings, a selected-side cycle, or a complementary-side cycle. -/
theorem partialLatents_ne_nil_iff_exists_missingCheckerEvidence
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side) :
    report.partialLatents ≠ [] ↔
      ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
          (report.node latent).MissingCheckerEvidence := by
  constructor
  · intro hpartialNonempty
    rcases (report.partialLatents_ne_nil_iff_exists_missing_checker_evidence).1
        hpartialNonempty with
      ⟨latent, hmem, hmissing⟩
    have hpartial : (report.node latent).Partial := hmissing
    exact ⟨latent, hmem,
      ((report.node latent).partial_iff_missingCheckerEvidence).1 hpartial⟩
  · rintro ⟨latent, hmem, hmissing⟩
    apply (report.partialLatents_ne_nil_iff_exists_missing_checker_evidence).2
    have hpartial : (report.node latent).Partial :=
      ((report.node latent).partial_iff_missingCheckerEvidence).2 hmissing
    exact ⟨latent, hmem, hpartial⟩

/-- Nonempty primitive missing-frontier boundary.  The executable missing-evidence list is
nonempty exactly when the finite report has an enumerated latent missing one primitive checker
ingredient. -/
theorem missingCheckerEvidenceLatents_ne_nil_iff_exists_missingCheckerEvidence
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side) :
    report.missingCheckerEvidenceLatents ≠ [] ↔
      ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
          (report.node latent).MissingCheckerEvidence := by
  rw [← report.partialLatents_eq_missingCheckerEvidenceLatents]
  exact report.partialLatents_ne_nil_iff_exists_missingCheckerEvidence

/-- Three-bin diagnostic form of the missing-frontier boundary.  A nonempty missing-evidence
frontier means the generator has an enumerated latent in one of the primitive missing-checker
bins: portal crossings, selected-side cycle, or complementary-side cycle. -/
theorem missingCheckerEvidenceLatents_ne_nil_iff_exists_missing_checker_ingredient
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side) :
    report.missingCheckerEvidenceLatents ≠ [] ↔
      (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
          (report.node latent).MissingPortalCrossingEvidence) ∨
        (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
          latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
            (report.node latent).MissingSelectedSideCycleEvidence) ∨
          (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
            latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
              (report.node latent).MissingComplementarySideCycleEvidence) := by
  constructor
  · intro hfrontier
    rcases (report.missingCheckerEvidenceLatents_ne_nil_iff_exists_missingCheckerEvidence).1
        hfrontier with
      ⟨latent, hmem, hmissing⟩
    rcases ((report.node latent).missingCheckerEvidence_iff_missing_ingredient).1
        hmissing with hportal | hcycle
    · exact Or.inl ⟨latent, hmem, hportal⟩
    · rcases hcycle with hselected | hcomplement
      · exact Or.inr <| Or.inl ⟨latent, hmem, hselected⟩
      · exact Or.inr <| Or.inr ⟨latent, hmem, hcomplement⟩
  · intro hingredient
    apply (report.missingCheckerEvidenceLatents_ne_nil_iff_exists_missingCheckerEvidence).2
    rcases hingredient with hportal | hcycle
    · rcases hportal with ⟨latent, hmem, hportal⟩
      exact ⟨latent, hmem,
        ((report.node latent).missingCheckerEvidence_iff_missing_ingredient).2
          (Or.inl hportal)⟩
    · rcases hcycle with hselected | hcomplement
      · rcases hselected with ⟨latent, hmem, hselected⟩
        exact ⟨latent, hmem,
          ((report.node latent).missingCheckerEvidence_iff_missing_ingredient).2
            (Or.inr (Or.inl hselected))⟩
      · rcases hcomplement with ⟨latent, hmem, hcomplement⟩
        exact ⟨latent, hmem,
          ((report.node latent).missingCheckerEvidence_iff_missing_ingredient).2
            (Or.inr (Or.inr hcomplement))⟩

/--
Closed-frontier form of the three-bin diagnostic boundary.  The checker has no missing-evidence
latents exactly when none of the enumerated latents is missing portal-crossing evidence, a
selected-side cycle, or a complementary-side cycle.
-/
theorem missingCheckerEvidenceLatents_eq_nil_iff_no_missing_checker_ingredient
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side) :
    report.missingCheckerEvidenceLatents = [] ↔
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
          (report.node latent).MissingPortalCrossingEvidence) ∨
        (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
          latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
            (report.node latent).MissingSelectedSideCycleEvidence) ∨
          (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
            latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
              (report.node latent).MissingComplementarySideCycleEvidence)) := by
  constructor
  · intro hnil hingredient
    have hfrontier :
        report.missingCheckerEvidenceLatents ≠ [] :=
      (report.missingCheckerEvidenceLatents_ne_nil_iff_exists_missing_checker_ingredient).2
        hingredient
    exact hfrontier hnil
  · intro hnoIngredient
    by_cases hnil : report.missingCheckerEvidenceLatents = []
    · exact hnil
    · exact False.elim
        (hnoIngredient
          ((report.missingCheckerEvidenceLatents_ne_nil_iff_exists_missing_checker_ingredient).1
            hnil))

/--
Concrete primitive-frontier closure for a finite CAP5 checker run.  If every enumerated latent
has portal-crossing evidence, and the ambient selected side has cycles on both sides, then none
of the primitive missing-checker bins can be inhabited.
-/
theorem no_missing_checker_ingredient_of_allPortalCrosses_of_sideCycles
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (latentNode boundaryEdge side latent).PortalCrosses)
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v)) :
    ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (latentNode boundaryEdge side latent).MissingPortalCrossingEvidence) ∨
      (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
          (latentNode boundaryEdge side latent).MissingSelectedSideCycleEvidence) ∨
        (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
          latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
            (latentNode boundaryEdge side latent).MissingComplementarySideCycleEvidence)) := by
  rintro (hmissingPortal | hmissingCycle)
  · rcases hmissingPortal with ⟨latent, _hmem, hmissing⟩
    exact hmissing (hportal latent)
  · rcases hmissingCycle with hmissingSelected | hmissingComplement
    · rcases hmissingSelected with ⟨latent, _hmem, hmissing⟩
      exact hmissing (by
        simpa [latentNode] using hcycles.1)
    · rcases hmissingComplement with ⟨latent, _hmem, hmissing⟩
      exact hmissing (by
        simpa [latentNode] using hcycles.2)

/--
In a cyclically five-edge-connected graph, the report's only obstruction to putting every
enumerated latent in the forced-counterexample bin is genuinely partial checker evidence.  Thus a
finite CAP5 run has a sharp diagnostic boundary: all sixteen latents are forced exactly when no
latent remains partial.
-/
theorem forcedCounterexampleLatents_eq_all_iff_partialLatents_eq_nil_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    report.forcedCounterexampleLatents =
        CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ↔
      report.partialLatents = [] := by
  constructor
  · intro hforcedAll
    apply List.eq_nil_iff_forall_not_mem.2
    intro latent hpartial
    have hlatentMem :
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge :=
      (report.mem_partialLatents_iff).1 hpartial |>.1
    have hforced : latent ∈ report.forcedCounterexampleLatents := by
      simpa [hforcedAll] using hlatentMem
    exact report.not_mem_partialLatents_of_mem_forcedCounterexampleLatents hforced hpartial
  · intro hpartialEmpty
    unfold forcedCounterexampleLatents
    apply List.filter_eq_self.2
    intro latent hlatentMem
    rcases report.mem_one_status_bin_of_mem_all hlatentMem with
      hrealized | hforcedOrPartial
    · exact False.elim
        (report.not_mem_realizedSeparatorLatents_of_cyclicallyFiveEdgeConnected
          hcyclic hrealized)
    · rcases hforcedOrPartial with hforced | hpartial
      · have hstatus :
            report.classify latent =
              CAP5SeparatorGeneratorStatus.forcedCounterexample :=
          (report.mem_forcedCounterexampleLatents_iff).1 hforced |>.2
        simp [hstatus]
      · have hmemEmpty : latent ∈ ([] :
            List (CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge)) := by
          rw [← hpartialEmpty]
          exact hpartial
        cases hmemEmpty

/--
Operational generator boundary: in a cyclically five-edge-connected graph, any failure of the
finite CAP5 report to force all enumerated latents exposes a concrete partial latent.  This is the
next checker target: such a latent is missing portal-crossing or side-cycle evidence rather than
opening a fourth report case.
-/
theorem exists_partialLatent_of_forcedCounterexampleLatents_ne_all_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hnotAll :
      report.forcedCounterexampleLatents ≠
        CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge) :
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        report.classify latent = CAP5SeparatorGeneratorStatus.partialCase := by
  by_contra hnone
  have hpartialEmpty : report.partialLatents = [] := by
    apply List.eq_nil_iff_forall_not_mem.2
    intro latent hpartial
    have hpartialData := (report.mem_partialLatents_iff).1 hpartial
    exact hnone ⟨latent, hpartialData.1, hpartialData.2⟩
  exact hnotAll
    ((report.forcedCounterexampleLatents_eq_all_iff_partialLatents_eq_nil_of_cyclicallyFiveEdgeConnected
      hcyclic).2 hpartialEmpty)

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

/--
Exact CAP5 generator boundary under cyclic five-edge-connectivity: the finite report forces all
enumerated latents exactly when every latent has the two checker ingredients still missing from
partial runs, namely portal crossings and side cycles.  This is the report-level form of the
hypothesis-discovery boundary: a non-all-forced report is not a new case, but missing checker
evidence for at least one latent.
-/
theorem forcedCounterexampleLatents_eq_all_iff_all_checker_evidence_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    report.forcedCounterexampleLatents =
        CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ↔
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses ∧ (report.node latent).SideCycles := by
  constructor
  · intro hforcedAll latent
    have hmemAll :
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge :=
      CAP5ExceptionalAnnulusGeneratorLatent.mem_all latent
    have hforced : latent ∈ report.forcedCounterexampleLatents := by
      simpa [hforcedAll] using hmemAll
    have hbin := report.inBin_forcedCounterexample_of_mem_forcedCounterexampleLatents hforced
    exact ⟨hbin.1, hbin.2.1⟩
  · intro hcomplete
    exact report.forcedCounterexampleLatents_eq_all_of_complete_of_cyclicallyFiveEdgeConnected
      hcyclic (fun latent => (hcomplete latent).1) (fun latent => (hcomplete latent).2)

/--
Computable complement form of the cyclic-five CAP5 frontier: under cyclic five-edge-connectivity,
the forced-counterexample list is exactly the list of latents with complete primitive checker
evidence.  The remaining latents are therefore precisely diagnostic failures of portal or
side-cycle evidence, not hidden realized-separator cases.
-/
theorem forcedCounterexampleLatents_eq_completeCheckerLatents_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    report.forcedCounterexampleLatents = report.completeCheckerLatents := by
  classical
  unfold forcedCounterexampleLatents completeCheckerLatents
  apply List.filter_congr
  intro latent _hmem
  have hcert : (report.node latent).InBin (report.classify latent) := by
    simpa [nodeReport] using (report.nodeReport latent).cert
  cases hstatus : report.classify latent with
  | realizedSeparator =>
      have hrealizedBin :
          (report.node latent).InBin CAP5SeparatorGeneratorStatus.realizedSeparator := by
        simpa [hstatus] using hcert
      exact False.elim
        ((report.node latent).not_realizedSeparator_of_cyclicallyFiveEdgeConnected
          hcyclic hrealizedBin.2.2)
  | forcedCounterexample =>
      have hforcedBin :
          (report.node latent).InBin CAP5SeparatorGeneratorStatus.forcedCounterexample := by
        simpa [hstatus] using hcert
      have hnotMissing :
          ¬ (report.node latent).MissingCheckerEvidence :=
        ((report.node latent).not_missingCheckerEvidence_iff_complete).2
          ⟨hforcedBin.1, hforcedBin.2.1⟩
      simp [hnotMissing]
  | partialCase =>
      have hmissing :
          (report.node latent).MissingCheckerEvidence :=
        (report.classify_eq_partialCase_iff_missingCheckerEvidence latent).1 hstatus
      simp [hmissing]

/-- Membership form of the computable cyclic-five CAP5 frontier: under cyclic
five-edge-connectivity, a latent is forced exactly when it is a complete checker run. -/
theorem mem_forcedCounterexampleLatents_iff_mem_completeCheckerLatents_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge} :
    latent ∈ report.forcedCounterexampleLatents ↔
      latent ∈ report.completeCheckerLatents := by
  rw [report.forcedCounterexampleLatents_eq_completeCheckerLatents_of_cyclicallyFiveEdgeConnected
    hcyclic]

/-- Cyclic-five finite frontier in its executable stopping form: the report forces all sixteen
latents exactly when the primitive missing-evidence frontier is empty. -/
theorem forcedCounterexampleLatents_eq_all_iff_missingCheckerEvidenceLatents_eq_nil_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    report.forcedCounterexampleLatents =
        CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ↔
      report.missingCheckerEvidenceLatents = [] := by
  rw [report.forcedCounterexampleLatents_eq_completeCheckerLatents_of_cyclicallyFiveEdgeConnected
    hcyclic]
  exact report.completeCheckerLatents_eq_all_iff_missingCheckerEvidenceLatents_eq_nil

/-- A single complete checker latent in a cyclically five-edge-connected report carries a
forced-counterexample payload.  This is the per-latent form needed by finite generators: they do
not need every latent to be complete before mining a forced witness from one complete row. -/
theorem forcedCounterexample_of_mem_completeCheckerLatents_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.completeCheckerLatents) :
    (report.node latent).ForcedCounterexample := by
  exact report.forcedCounterexample_of_mem_forcedCounterexampleLatents
    ((report.mem_forcedCounterexampleLatents_iff_mem_completeCheckerLatents_of_cyclicallyFiveEdgeConnected
      hcyclic).2 hmem)

/-- A single complete checker latent in a cyclically five-edge-connected report emits the full
one-edge forced-counterexample walk.  This is the finite payload for hypothesis discovery: an
outside edge, endpoints on opposite sides, a one-edge crossing walk, and avoidance of the
generated portal boundary edges. -/
theorem exists_oneEdge_forcedCounterexampleWalk_of_mem_completeCheckerLatents_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.completeCheckerLatents) :
    ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
      e ∉ (report.node latent).candidate.edgeSupport ∧
        side u ∧ ¬ side v ∧
          p.edges = [(e : Sym2 V)] ∧
            (∀ i : Fin 5, i ∈ (report.node latent).candidate.portalCandidate.portalSet →
              ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
              EdgeCrossesVertexSide G side e := by
  exact report.exists_oneEdge_forcedCounterexampleWalk_of_mem_forcedCounterexampleLatents
    ((report.mem_forcedCounterexampleLatents_iff_mem_completeCheckerLatents_of_cyclicallyFiveEdgeConnected
      hcyclic).2 hmem)

/--
Dual form of the exact CAP5 generator boundary: under cyclic five-edge-connectivity, a report
fails to force all enumerated latents exactly when some generated latent is missing portal-
crossing evidence or side-cycle evidence.  This is the concrete obstruction frontier consumed by
the next generator-refinement pass.
-/
theorem forcedCounterexampleLatents_ne_all_iff_exists_missing_checker_evidence_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    report.forcedCounterexampleLatents ≠
        CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ↔
      ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        ¬ (report.node latent).PortalCrosses ∨ ¬ (report.node latent).SideCycles := by
  constructor
  · intro hnotAll
    rcases report.exists_partialLatent_of_forcedCounterexampleLatents_ne_all_of_cyclicallyFiveEdgeConnected
        hcyclic hnotAll with
      ⟨latent, hmem, hstatus⟩
    have hpartial : latent ∈ report.partialLatents :=
      (report.mem_partialLatents_iff).2 ⟨hmem, hstatus⟩
    exact ⟨latent, report.partial_of_mem_partialLatents hpartial⟩
  · rintro ⟨latent, hmissing⟩ hforcedAll
    have hcomplete :=
      (report.forcedCounterexampleLatents_eq_all_iff_all_checker_evidence_of_cyclicallyFiveEdgeConnected
        hcyclic).1 hforcedAll latent
    rcases hmissing with hnotPortal | hnotCycles
    · exact hnotPortal hcomplete.1
    · exact hnotCycles hcomplete.2

/--
Split dual form of the exact CAP5 generator boundary: under cyclic five-edge-connectivity, a
report fails to force all enumerated latents exactly when some generated latent is missing one
primitive checker ingredient: portal crossings, a selected-side cycle, or a complementary-side
cycle.
-/
theorem forcedCounterexampleLatents_ne_all_iff_exists_missingCheckerEvidence_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    report.forcedCounterexampleLatents ≠
        CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ↔
      ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).MissingCheckerEvidence := by
  have hboundary :=
    report.forcedCounterexampleLatents_ne_all_iff_exists_missing_checker_evidence_of_cyclicallyFiveEdgeConnected
      hcyclic
  constructor
  · intro hnotAll
    rcases hboundary.1 hnotAll with ⟨latent, hmissing⟩
    have hpartial : (report.node latent).Partial := hmissing
    exact ⟨latent, ((report.node latent).partial_iff_missingCheckerEvidence).1 hpartial⟩
  · rintro ⟨latent, hmissing⟩
    apply hboundary.2
    have hpartial : (report.node latent).Partial :=
      ((report.node latent).partial_iff_missingCheckerEvidence).2 hmissing
    exact ⟨latent, hpartial⟩

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

/--
Executable generator boundary: if the canonical finite checker does not force all sixteen CAP5
latents in a cyclically five-edge-connected graph, it returns an explicit latent whose status is
`partialCase`.
-/
theorem ofDecidableChecks_exists_partialLatent_of_forcedCounterexampleLatents_ne_all_of_cyclicallyFiveEdgeConnected
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)]
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hnotAll :
      (ofDecidableChecks boundaryEdge side).forcedCounterexampleLatents ≠
        CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge) :
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        (ofDecidableChecks boundaryEdge side).classify latent =
          CAP5SeparatorGeneratorStatus.partialCase := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  exact
    report.exists_partialLatent_of_forcedCounterexampleLatents_ne_all_of_cyclicallyFiveEdgeConnected
      hcyclic hnotAll

/--
Executable exact partial-bin boundary for the canonical finite CAP5 checker.  Its partial list is
empty exactly when every enumerated latent has portal-crossing evidence and side-cycle evidence.
This is the local finite-checker frontier, independent of cyclic five-edge-connectivity.
-/
theorem ofDecidableChecks_partialLatents_eq_nil_iff_all_checker_evidence
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)] :
    (ofDecidableChecks boundaryEdge side).partialLatents = [] ↔
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge →
          (latentNode boundaryEdge side latent).PortalCrosses ∧
            (latentNode boundaryEdge side latent).SideCycles := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  have hboundary := report.partialLatents_eq_nil_iff_all_checker_evidence
  constructor
  · intro hpartialEmpty latent hmem
    have hdata := hboundary.1 hpartialEmpty latent hmem
    simpa [report, node, latentNode] using hdata
  · intro hcomplete
    apply hboundary.2
    intro latent hmem
    have hdata := hcomplete latent hmem
    simpa [report, node, latentNode] using hdata

/--
Executable nonempty partial-bin boundary for the canonical finite CAP5 checker.  A nonempty
partial list is equivalent to an enumerated latent with missing portal-crossing or side-cycle
evidence.
-/
theorem ofDecidableChecks_partialLatents_ne_nil_iff_exists_missing_checker_evidence
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)] :
    (ofDecidableChecks boundaryEdge side).partialLatents ≠ [] ↔
      ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
          (¬ (latentNode boundaryEdge side latent).PortalCrosses ∨
            ¬ (latentNode boundaryEdge side latent).SideCycles) := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  have hboundary := report.partialLatents_ne_nil_iff_exists_missing_checker_evidence
  constructor
  · intro hpartialNonempty
    rcases hboundary.1 hpartialNonempty with ⟨latent, hmem, hmissing⟩
    exact ⟨latent, hmem, by simpa [report, node, latentNode] using hmissing⟩
  · rintro ⟨latent, hmem, hmissing⟩
    apply hboundary.2
    exact ⟨latent, hmem, by simpa [report, node, latentNode] using hmissing⟩

/--
Executable split obstruction frontier for the canonical finite CAP5 checker.  A nonempty partial
list is equivalent to an enumerated latent missing one primitive checker ingredient: portal
crossings, a selected-side cycle, or a complementary-side cycle.
-/
theorem ofDecidableChecks_partialLatents_ne_nil_iff_exists_missingCheckerEvidence
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)] :
    (ofDecidableChecks boundaryEdge side).partialLatents ≠ [] ↔
      ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
          (latentNode boundaryEdge side latent).MissingCheckerEvidence := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  have hboundary := report.partialLatents_ne_nil_iff_exists_missingCheckerEvidence
  constructor
  · intro hpartialNonempty
    rcases hboundary.1 hpartialNonempty with ⟨latent, hmem, hmissing⟩
    exact ⟨latent, hmem, by simpa [report, node, latentNode] using hmissing⟩
  · rintro ⟨latent, hmem, hmissing⟩
    apply hboundary.2
    exact ⟨latent, hmem, by simpa [report, node, latentNode] using hmissing⟩

/--
Executable three-bin diagnostic frontier for the canonical finite CAP5 checker.  A nonempty
missing-evidence list is equivalent to an enumerated latent missing portal crossings, a
selected-side cycle, or a complementary-side cycle.
-/
theorem ofDecidableChecks_missingCheckerEvidenceLatents_ne_nil_iff_exists_missing_checker_ingredient
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)] :
    (ofDecidableChecks boundaryEdge side).missingCheckerEvidenceLatents ≠ [] ↔
      (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
          (latentNode boundaryEdge side latent).MissingPortalCrossingEvidence) ∨
        (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
          latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
            (latentNode boundaryEdge side latent).MissingSelectedSideCycleEvidence) ∨
          (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
            latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
              (latentNode boundaryEdge side latent).MissingComplementarySideCycleEvidence) := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  have hboundary :=
    report.missingCheckerEvidenceLatents_ne_nil_iff_exists_missing_checker_ingredient
  constructor
  · intro hfrontier
    have hingredient := hboundary.1 hfrontier
    simpa [report, node, latentNode] using hingredient
  · intro hingredient
    apply hboundary.2
    simpa [report, node, latentNode] using hingredient

/--
Closed-frontier version for the canonical finite CAP5 checker.  Its missing-evidence list is
empty exactly when the enumerated frontier has no latent in any primitive missing-checker bin.
-/
theorem ofDecidableChecks_missingCheckerEvidenceLatents_eq_nil_iff_no_missing_checker_ingredient
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)] :
    (ofDecidableChecks boundaryEdge side).missingCheckerEvidenceLatents = [] ↔
      ¬ ((∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
          (latentNode boundaryEdge side latent).MissingPortalCrossingEvidence) ∨
        (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
          latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
            (latentNode boundaryEdge side latent).MissingSelectedSideCycleEvidence) ∨
          (∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
            latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
              (latentNode boundaryEdge side latent).MissingComplementarySideCycleEvidence)) := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  have hboundary :=
    report.missingCheckerEvidenceLatents_eq_nil_iff_no_missing_checker_ingredient
  constructor
  · intro hnil hingredient
    exact hboundary.1 hnil (by
      simpa [report, node, latentNode] using hingredient)
  · intro hnoIngredient
    apply hboundary.2
    intro hingredient
    exact hnoIngredient (by
      simpa [report, node, latentNode] using hingredient)

/--
Executable exact boundary for the canonical finite CAP5 checker: under cyclic five-edge-
connectivity, it emits an all-forced report exactly when every latent has portal-crossing and
side-cycle evidence.
-/
theorem ofDecidableChecks_forcedCounterexampleLatents_eq_all_iff_all_checker_evidence_of_cyclicallyFiveEdgeConnected
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)]
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    (ofDecidableChecks boundaryEdge side).forcedCounterexampleLatents =
        CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ↔
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (latentNode boundaryEdge side latent).PortalCrosses ∧
          (latentNode boundaryEdge side latent).SideCycles := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  have hboundary :=
    report.forcedCounterexampleLatents_eq_all_iff_all_checker_evidence_of_cyclicallyFiveEdgeConnected
      hcyclic
  constructor
  · intro hforcedAll latent
    have hdata := hboundary.1 hforcedAll latent
    simpa [report, node, latentNode] using hdata
  · intro hcomplete
    apply hboundary.2
    intro latent
    have hdata := hcomplete latent
    simpa [report, node, latentNode] using hdata

/--
Executable stopping criterion for the canonical finite CAP5 checker: under cyclic
five-edge-connectivity, all sixteen latents are forced exactly when the primitive
missing-evidence frontier is empty.
-/
theorem ofDecidableChecks_forcedCounterexampleLatents_eq_all_iff_missingCheckerEvidenceLatents_eq_nil_of_cyclicallyFiveEdgeConnected
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)]
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    (ofDecidableChecks boundaryEdge side).forcedCounterexampleLatents =
        CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ↔
      (ofDecidableChecks boundaryEdge side).missingCheckerEvidenceLatents = [] := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  exact
    report.forcedCounterexampleLatents_eq_all_iff_missingCheckerEvidenceLatents_eq_nil_of_cyclicallyFiveEdgeConnected
      hcyclic

/--
Executable obstruction frontier for the canonical finite CAP5 checker: under cyclic five-edge-
connectivity, a non-all-forced report is equivalent to an explicit latent missing portal-crossing
or side-cycle evidence.
-/
theorem ofDecidableChecks_forcedCounterexampleLatents_ne_all_iff_exists_missing_checker_evidence_of_cyclicallyFiveEdgeConnected
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)]
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    (ofDecidableChecks boundaryEdge side).forcedCounterexampleLatents ≠
        CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ↔
      ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        ¬ (latentNode boundaryEdge side latent).PortalCrosses ∨
          ¬ (latentNode boundaryEdge side latent).SideCycles := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  have hboundary :=
    report.forcedCounterexampleLatents_ne_all_iff_exists_missing_checker_evidence_of_cyclicallyFiveEdgeConnected
      hcyclic
  constructor
  · intro hnotAll
    rcases hboundary.1 hnotAll with ⟨latent, hmissing⟩
    exact ⟨latent, by simpa [report, node, latentNode] using hmissing⟩
  · rintro ⟨latent, hmissing⟩
    apply hboundary.2
    exact ⟨latent, by simpa [report, node, latentNode] using hmissing⟩

/--
Executable split obstruction frontier for the canonical finite CAP5 checker: under cyclic
five-edge-connectivity, a non-all-forced report is equivalent to an explicit latent missing one
primitive checker ingredient.
-/
theorem ofDecidableChecks_forcedCounterexampleLatents_ne_all_iff_exists_missingCheckerEvidence_of_cyclicallyFiveEdgeConnected
    (boundaryEdge : Fin 5 → G.edgeSet) (side : V → Prop)
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).PortalCrosses)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).SideCycles)]
    [∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      Decidable ((latentNode boundaryEdge side latent).RealizedSeparator)]
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    (ofDecidableChecks boundaryEdge side).forcedCounterexampleLatents ≠
        CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ↔
      ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (latentNode boundaryEdge side latent).MissingCheckerEvidence := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  have hboundary :=
    report.forcedCounterexampleLatents_ne_all_iff_exists_missingCheckerEvidence_of_cyclicallyFiveEdgeConnected
      hcyclic
  constructor
  · intro hnotAll
    rcases hboundary.1 hnotAll with ⟨latent, hmissing⟩
    exact ⟨latent, by simpa [report, node, latentNode] using hmissing⟩
  · rintro ⟨latent, hmissing⟩
    apply hboundary.2
    exact ⟨latent, by simpa [report, node, latentNode] using hmissing⟩

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

/--
Complete cyclic-five histogram profile for a finite CAP5 generator sweep.  Once every latent has
the primitive portal-crossing and side-cycle checker evidence, cyclic five-edge-connectivity rules
out all realized-separator rows, leaves no partial rows, and sends all sixteen latents to the
forced-counterexample bin.
-/
theorem histogram_lengths_eq_of_complete_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles) :
    report.realizedSeparatorLatents.length = 0 ∧
      report.partialLatents.length = 0 ∧
        report.forcedCounterexampleLatents.length = 16 := by
  exact
    ⟨report.realizedSeparatorLatents_length_eq_zero_of_cyclicallyFiveEdgeConnected hcyclic,
      report.partialLatents_length_eq_zero_of_complete hportal hcycles,
      report.forcedCounterexampleLatents_length_eq_sixteen_of_complete_of_cyclicallyFiveEdgeConnected
        hcyclic hportal hcycles⟩

/--
Executable histogram profile for the canonical decidable CAP5 report.  This is the generator-facing
contract: a complete cyclic-five sample run has no hold/partial bins and exactly sixteen forced
rows to feed into the algebraic detector lane.
-/
theorem ofDecidableChecks_histogram_lengths_eq_of_complete_of_cyclicallyFiveEdgeConnected
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
    (ofDecidableChecks boundaryEdge side).realizedSeparatorLatents.length = 0 ∧
      (ofDecidableChecks boundaryEdge side).partialLatents.length = 0 ∧
        (ofDecidableChecks boundaryEdge side).forcedCounterexampleLatents.length = 16 := by
  let report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side :=
    ofDecidableChecks boundaryEdge side
  exact report.histogram_lengths_eq_of_complete_of_cyclicallyFiveEdgeConnected hcyclic
    (by
      intro latent
      simpa [report, node, latentNode] using hportal latent)
    (by
      intro latent
      simpa [report, node, latentNode] using hcycles latent)

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

/-- A complete cyclic-five CAP5 report emits a concrete one-edge forced-counterexample walk.  This is
the finite generator payload: an enumerated latent, an outside edge, endpoint sides, a one-edge walk
crossing the proposed side, and avoidance of the generated portal boundary edges. -/
theorem exists_oneEdge_forcedCounterexampleWalk_of_complete_of_cyclicallyFiveEdgeConnected
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles) :
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        latent ∈ report.forcedCounterexampleLatents ∧
          ∃ u v : V, ∃ e : G.edgeSet, ∃ p : G.Walk u v,
            e ∉ (report.node latent).candidate.edgeSupport ∧
              side u ∧ ¬ side v ∧
                p.edges = [(e : Sym2 V)] ∧
                  (∀ i : Fin 5, i ∈ (report.node latent).candidate.portalCandidate.portalSet →
                    ((boundaryEdge i : G.edgeSet) : Sym2 V) ∉ p.edges) ∧
                    EdgeCrossesVertexSide G side e := by
  rcases report.exists_mem_forcedCounterexampleLatents_of_complete_of_cyclicallyFiveEdgeConnected
      hcyclic hportal hcycles with
    ⟨latent, hforcedMem⟩
  have hlatentMem :
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge :=
    (report.mem_forcedCounterexampleLatents_iff).1 hforcedMem |>.1
  rcases report.exists_oneEdge_forcedCounterexampleWalk_of_mem_forcedCounterexampleLatents
      hforcedMem with
    ⟨u, v, e, p, heOutside, hu, hv, hpEdges, havoid, hcross⟩
  exact
    ⟨latent, hlatentMem, hforcedMem, u, v, e, p, heOutside, hu, hv,
      hpEdges, havoid, hcross⟩

end CAP5ExceptionalAnnulusGeneratorReport

namespace CAP5TransportedEdgeComponentCoverCore

variable {G : SimpleGraph V}
variable {boundaryEdge : Fin 5 → G.edgeSet} {n : Nat}

/-- Side-calibrated realized predicate emitted by the enumerated exceptional CAP5 generator.
Unlike the report's broad `realizedSeparator` status, this predicate records that the candidate
support realizes the exact side predicate being tested.  This is the hold-bin counterpart to the
forced-edge predicate below. -/
def EnumeratedExceptionalAnnulusSameSideRealization
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool) (side : V → Prop) : Prop :=
  ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
    latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
      latent.p0Inside = p0Inside ∧
        latent.p4Inside = p4Inside ∧
          data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
            (let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
              { latent := latent, side := side };
              node.RealizedSeparatorOnSide)

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

/-- Missing-checker predicate emitted by the enumerated exceptional CAP5 witness generator.  This
is the partial-bin counterpart to the side-realized and forced-edge predicates: the selected
latent is genuine exceptional CAP5 data, but the finite checker is still missing primitive
portal/cycle evidence for that generated node. -/
def EnumeratedExceptionalAnnulusMissingCheckerEvidence
    (data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n)
    (p0Inside p4Inside : Bool) (side : V → Prop) : Prop :=
  ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
    latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
      latent.p0Inside = p0Inside ∧
        latent.p4Inside = p4Inside ∧
          data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
            (let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
              { latent := latent, side := side };
              node.MissingCheckerEvidence)

/-- Cyclic five-edge-connectivity rules out the side-calibrated realized bin of the enumerated
exceptional CAP5 generator.  Any such realization would be a cyclic edge cut of size at most four. -/
theorem not_enumeratedExceptionalAnnulusSameSideRealization_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (hcyclic : CyclicallyFiveEdgeConnected G) :
    ¬ data.EnumeratedExceptionalAnnulusSameSideRealization p0Inside p4Inside side := by
  rintro ⟨latent, _hmem, _hp0, _hp4, _horientation, hrealizedOnSide⟩
  let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
    { latent := latent, side := side }
  have hrealized : node.RealizedSeparator := by
    rcases (show node.RealizedSeparatorOnSide from by
      simpa [node] using hrealizedOnSide) with
      ⟨realization, _hside⟩
    exact ⟨realization⟩
  exact node.not_realizedSeparator_of_cyclicallyFiveEdgeConnected hcyclic hrealized

/-- Side-calibrated generator boundary for exceptional CAP5 data.  Under complete portal and
two-cycle evidence, the selected latent either realizes the exact proposed side or emits a
concrete forced edge.  This is the finite hold/fail boundary to mine before pushing the route
through a separate planar-topology layer. -/
theorem enumeratedExceptionalAnnulusSameSideRealization_or_exists_enumeratedExceptionalAnnulusForcedEdge_of_isExceptional_of_portalSides
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
    data.EnumeratedExceptionalAnnulusSameSideRealization p0Inside p4Inside side ∨
      ∃ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
  rcases
      CAP5ExceptionalAnnulusGeneratorNode.exists_enumeratedNode_realizedSeparatorOnSide_or_forcedCounterexample_of_isExceptional_of_portalSides
        (boundaryEdge := boundaryEdge) p0Inside p4Inside h side hportal_crosses hcycles with
    ⟨latent, hmem, hp0, hp4, horientation, hresolved⟩
  let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
    { latent := latent, side := side }
  rcases hresolved with
    hrealized | hforced
  · exact Or.inl ⟨latent, hmem, hp0, hp4, horientation, by
      simpa [node] using hrealized⟩
  · rcases hforced with ⟨e, hedge⟩
    exact Or.inr ⟨e, latent, hmem, hp0, hp4, horientation, by
      simpa [node] using hedge⟩

/--
Unconditional side-calibrated generator boundary for exceptional CAP5 data.  For the selected
portal-side bits, the realized exceptional orientation gives an enumerated latent that is either
missing primitive checker evidence, realizes the proposed side exactly, or emits a forced edge.
-/
theorem enumeratedExceptionalAnnulusMissingCheckerEvidence_or_sameSideRealization_or_exists_forcedEdge_of_isExceptional_of_portalSides
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop) :
    data.EnumeratedExceptionalAnnulusMissingCheckerEvidence p0Inside p4Inside side ∨
      data.EnumeratedExceptionalAnnulusSameSideRealization p0Inside p4Inside side ∨
        ∃ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
  rcases CAP5ExceptionalAnnulusGeneratorLatent.exists_mem_all_of_isExceptional_of_portalSides
      (boundaryEdge := boundaryEdge) p0Inside p4Inside h with
    ⟨latent, hmem, hp0, hp4, horientation⟩
  let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
    { latent := latent, side := side }
  rcases node.missingCheckerEvidence_or_realizedSeparatorOnSide_or_forcedCounterexample with
    hmissing | hresolved
  · exact Or.inl ⟨latent, hmem, hp0, hp4, horientation, by
      simpa [node] using hmissing⟩
  · rcases hresolved with hrealized | hforced
    · exact Or.inr <| Or.inl ⟨latent, hmem, hp0, hp4, horientation, by
        simpa [node] using hrealized⟩
    · rcases hforced with ⟨e, hedge⟩
      exact Or.inr <| Or.inr ⟨e, latent, hmem, hp0, hp4, horientation, by
        simpa [node] using hedge⟩

/--
Cyclic-five sample boundary for exceptional CAP5 data.  Under cyclic five-edge-connectivity,
the same selected latent is either missing primitive checker evidence or emits an actual
exceptional-annulus outside-crossing edge.
-/
theorem enumeratedExceptionalAnnulusMissingCheckerEvidence_or_exists_exceptionalAnnulusCrossingOutsideEdge_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (side : V → Prop) (hcyclic : CyclicallyFiveEdgeConnected G) :
    data.EnumeratedExceptionalAnnulusMissingCheckerEvidence p0Inside p4Inside side ∨
      ∃ e : G.edgeSet,
        data.ExceptionalAnnulusCrossingOutsideEdge p0Inside p4Inside side e := by
  rcases CAP5ExceptionalAnnulusGeneratorLatent.exists_mem_all_of_isExceptional_of_portalSides
      (boundaryEdge := boundaryEdge) p0Inside p4Inside h with
    ⟨latent, hmem, hp0, hp4, horientation⟩
  let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
    { latent := latent, side := side }
  rcases node.missingCheckerEvidence_or_exists_crossing_outside_of_cyclicallyFiveEdgeConnected
      hcyclic with hmissing | hcrossing
  · exact Or.inl ⟨latent, hmem, hp0, hp4, horientation, by
      simpa [node] using hmissing⟩
  · rcases hcrossing with ⟨e, heOutside, hcross⟩
    refine Or.inr ⟨e, node.candidate, ?_, ?_, ?_, ?_⟩
    · simpa [node, CAP5ExceptionalAnnulusGeneratorNode.candidate] using horientation
    · simpa [node, CAP5ExceptionalAnnulusGeneratorNode.candidate, hp0, hp4] using
        node.latent.candidate_sideCase_eq_ofPortalSides
    · simpa [node] using heOutside
    · simpa [node] using hcross

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

/-- Exact normal form for the data-level enumerated forced-edge predicate: an emitted edge is
precisely a non-candidate edge crossing the selected side for one realized exceptional latent.
This is the transparent finite witness-generator boundary used by separator and cocycle checks. -/
theorem enumeratedExceptionalAnnulusForcedEdge_iff_exists_latent_crossing_outside
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    {p0Inside p4Inside : Bool} {side : V → Prop} {e : G.edgeSet} :
    data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ↔
      ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
          latent.p0Inside = p0Inside ∧
            latent.p4Inside = p4Inside ∧
              data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
                (let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
                  { latent := latent, side := side };
                  e ∉ node.candidate.edgeSupport ∧ EdgeCrossesVertexSide G side e) := by
  constructor
  · rintro ⟨latent, hmem, hp0, hp4, horientation, hforced⟩
    let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
      { latent := latent, side := side }
    have hforcedNode : node.ForcedCounterexampleEdge e := by
      simpa [node] using hforced
    have hnormal :
        e ∉ node.candidate.edgeSupport ∧ EdgeCrossesVertexSide G node.side e :=
      (node.forcedCounterexampleEdge_iff_crossing_outside (e := e)).1 hforcedNode
    exact ⟨latent, hmem, hp0, hp4, horientation, by simpa [node] using hnormal⟩
  · rintro ⟨latent, hmem, hp0, hp4, horientation, hnormal⟩
    let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
      { latent := latent, side := side }
    have hnormalNode :
        e ∉ node.candidate.edgeSupport ∧ EdgeCrossesVertexSide G node.side e := by
      simpa [node] using hnormal
    have hforcedNode : node.ForcedCounterexampleEdge e :=
      (node.forcedCounterexampleEdge_iff_crossing_outside (e := e)).2 hnormalNode
    exact ⟨latent, hmem, hp0, hp4, horientation, by simpa [node] using hforcedNode⟩

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

/-- A forced latent emitted by a certified finite report supplies an enumerated forced edge in
the same crossing-outside normal form as the separator checker. -/
theorem exists_enumeratedExceptionalAnnulusForcedEdge_crossing_outside_of_mem_forcedCounterexampleLatents
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.forcedCounterexampleLatents)
    (horientation : data.RealizesExceptionalBoundarySupportOrientation latent.orientation) :
    ∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge
          latent.p0Inside latent.p4Inside side e ∧
        e ∉ (report.node latent).candidate.edgeSupport ∧
          EdgeCrossesVertexSide G side e := by
  have hlatentMem :
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge :=
    (report.mem_forcedCounterexampleLatents_iff).1 hmem |>.1
  rcases report.exists_crossing_outside_of_mem_forcedCounterexampleLatents hmem with
    ⟨e, heOutside, hcross⟩
  have hnormal :
      e ∉ (report.node latent).candidate.edgeSupport ∧
        EdgeCrossesVertexSide G (report.node latent).side e := by
    exact ⟨heOutside, by simpa [CAP5ExceptionalAnnulusGeneratorReport.node,
      CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hcross⟩
  have hforced : (report.node latent).ForcedCounterexampleEdge e :=
    ((report.node latent).forcedCounterexampleEdge_iff_crossing_outside (e := e)).2 hnormal
  exact ⟨e,
    ⟨latent, hlatentMem, rfl, rfl, horientation, by
      simpa [CAP5ExceptionalAnnulusGeneratorReport.node,
        CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hforced⟩,
    heOutside, hcross⟩

/-- A complete checker latent in a cyclically five-edge-connected report gives an enumerated
forced edge for the latent's own portal-side bits, once the component-cover data realizes its
orientation.  This is the per-latent bridge from the computable checker frontier into the
algebraic forced-edge predicate. -/
theorem exists_enumeratedExceptionalAnnulusForcedEdge_of_mem_completeCheckerLatents_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.completeCheckerLatents)
    (horientation : data.RealizesExceptionalBoundarySupportOrientation latent.orientation) :
    ∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge
        latent.p0Inside latent.p4Inside side e := by
  exact data.exists_enumeratedExceptionalAnnulusForcedEdge_of_mem_forcedCounterexampleLatents
    report
    ((report.mem_forcedCounterexampleLatents_iff_mem_completeCheckerLatents_of_cyclicallyFiveEdgeConnected
      hcyclic).2 hmem)
    horientation

/-- A complete checker latent in a cyclically five-edge-connected report gives an enumerated
forced edge in crossing-outside normal form. -/
theorem exists_enumeratedExceptionalAnnulusForcedEdge_crossing_outside_of_mem_completeCheckerLatents_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    {latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge}
    (hmem : latent ∈ report.completeCheckerLatents)
    (horientation : data.RealizesExceptionalBoundarySupportOrientation latent.orientation) :
    ∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge
          latent.p0Inside latent.p4Inside side e ∧
        e ∉ (report.node latent).candidate.edgeSupport ∧
          EdgeCrossesVertexSide G side e := by
  exact data.exists_enumeratedExceptionalAnnulusForcedEdge_crossing_outside_of_mem_forcedCounterexampleLatents
    report
    ((report.mem_forcedCounterexampleLatents_iff_mem_completeCheckerLatents_of_cyclicallyFiveEdgeConnected
      hcyclic).2 hmem)
    horientation

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

/-- Report-level exceptional CAP5 emission with the concrete one-edge walk payload kept attached to
the selected exceptional latent.  This is the data-level bridge from the finite report histogram to
the algebraic/cocycle lane: the emitted edge is simultaneously an enumerated forced edge for the
requested portal-side bits and the edge of an outside one-edge walk avoiding the selected portals. -/
theorem exists_enumeratedExceptionalAnnulusForcedEdge_and_oneEdge_forcedCounterexampleWalk_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
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
                            EdgeCrossesVertexSide G side e := by
  rcases CAP5ExceptionalAnnulusGeneratorLatent.exists_mem_all_of_isExceptional_of_portalSides
      (boundaryEdge := boundaryEdge) p0Inside p4Inside h with
    ⟨latent, hlatentMem, hp0, hp4, horientation⟩
  have hforced :
      latent ∈ report.forcedCounterexampleLatents :=
    report.mem_forcedCounterexampleLatents_of_mem_all_of_complete_of_cyclicallyFiveEdgeConnected
      hcyclic hportal hcycles hlatentMem
  rcases report.exists_oneEdge_forcedCounterexampleWalk_of_mem_forcedCounterexampleLatents
      hforced with
    ⟨u, v, e, p, heOutside, hu, hv, hpEdges, havoid, hcross⟩
  have hforcedEdge : (report.node latent).ForcedCounterexampleEdge e :=
    ⟨u, v, p, heOutside, hu, hv, hpEdges, havoid⟩
  have hedge :
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
    have hedgeRaw :
        data.EnumeratedExceptionalAnnulusForcedEdge
          latent.p0Inside latent.p4Inside side e :=
      ⟨latent, hlatentMem, rfl, rfl, horientation, by
        simpa [CAP5ExceptionalAnnulusGeneratorReport.node,
          CAP5ExceptionalAnnulusGeneratorReport.latentNode] using hforcedEdge⟩
    simpa [hp0, hp4] using hedgeRaw
  exact
    ⟨latent, hlatentMem, hp0, hp4, horientation, hforced, u, v, e, p,
      hedge, heOutside, hu, hv, hpEdges, havoid, hcross⟩

/-- Report-level algebraic emission theorem.  If a complete cyclic-five exceptional CAP5 report
emits a one-edge forced-walk payload and the selected chain is nonzero on every enumerated emitted
edge, then the same selected latent also supplies a nonzero red/blue family-pairing witness.  This
keeps the finite report histogram connected to the non-geometric algebraic detector lane. -/
theorem exists_enumeratedExceptionalAnnulusForcedEdge_oneEdgeWalk_and_familyPairing_ne_zero_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles)
    {z : G.edgeSet → Color}
    (hzNonzero :
      ∀ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
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
                              ∃ i : κ,
                                chainDotBilinForm G.edgeSet
                                  (family i : G.edgeSet → Color) z ≠ 0 := by
  rcases data.exists_enumeratedExceptionalAnnulusForcedEdge_and_oneEdge_forcedCounterexampleWalk_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      report p0Inside p4Inside h hcyclic hportal hcycles with
    ⟨latent, hlatentMem, hp0, hp4, horientation, hforced, u, v, e, p, hedge,
      heOutside, hu, hv, hpEdges, havoid, hcross⟩
  rcases exists_familyPairing_ne_zero_of_edgePredicateWitness family
      (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)
      ⟨e, hedge, hzNonzero e hedge⟩ hwitnessRed hwitnessBlue with
    ⟨i, hpair⟩
  exact
    ⟨latent, hlatentMem, hp0, hp4, horientation, hforced, u, v, e, p,
      hedge, heOutside, hu, hv, hpEdges, havoid, hcross, i, hpair⟩

/-- CAP5 specialization of the all-zero red/blue pairing diagnostic.  If every generated family
pairing with `z` is zero, then `z` vanishes on every edge emitted by the enumerated exceptional
CAP5 forced-edge predicate. -/
theorem enumeratedExceptionalAnnulusForcedEdge_vanishes_of_forall_familyPairing_eq_zero
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    {z : G.edgeSet → Color}
    (hpairZero :
      ∀ i : κ,
        chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z = 0)
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
    ∀ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
        z e = 0 :=
  edgePredicate_vanishes_of_forall_familyPairing_eq_zero family
    (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)
    hpairZero hwitnessRed hwitnessBlue

/-- All-zero red/blue pairings for a nonzero selected-boundary-zero chain produce the CAP5
emitted-edge obstruction object.  This is the algebraic failure payload for a finite CAP5 run:
the current report-generated coordinate family did not detect `z`, and `z` is invisible to every
enumerated exceptional CAP5 forced edge. -/
theorem exists_boundaryZeroChain_vanishingOnEnumeratedExceptionalAnnulusForcedEdges_of_forall_familyPairing_eq_zero
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    {z : G.edgeSet → Color}
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule emb)
    (hzNonzero : z ≠ 0)
    (hpairZero :
      ∀ i : κ,
        chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z = 0)
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
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          ∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0 :=
  exists_boundaryZeroChainObstruction_of_forall_familyPairing_eq_zero family
    (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)
    hzBoundary hzNonzero hpairZero hwitnessRed hwitnessBlue

/-- Report-level algebraic falsification diagnostic.  If every generated family pairing vanishes,
then a complete cyclic-five exceptional CAP5 report exposes a concrete forced-walk emitted edge on
which the selected chain is zero.  This is the finite coordinate returned when the algebraic lane
cannot detect the selected chain through the red/blue probes attached to the report output. -/
theorem exists_enumeratedExceptionalAnnulusForcedEdge_oneEdgeWalk_eq_zero_of_forall_familyPairing_eq_zero_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (report : CAP5ExceptionalAnnulusGeneratorReport boundaryEdge side)
    (p0Inside p4Inside : Bool) (h : data.IsExceptional)
    (hcyclic : CyclicallyFiveEdgeConnected G)
    (hportal :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).PortalCrosses)
    (hcycles :
      ∀ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
        (report.node latent).SideCycles)
    {z : G.edgeSet → Color}
    (hpairZero :
      ∀ i : κ,
        chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z = 0)
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
                              z e = 0 := by
  rcases data.exists_enumeratedExceptionalAnnulusForcedEdge_and_oneEdge_forcedCounterexampleWalk_of_report_complete_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      report p0Inside p4Inside h hcyclic hportal hcycles with
    ⟨latent, hlatentMem, hp0, hp4, horientation, hforced, u, v, e, p, hedge,
      heOutside, hu, hv, hpEdges, havoid, hcross⟩
  have hzeZero : z e = 0 :=
    data.enumeratedExceptionalAnnulusForcedEdge_vanishes_of_forall_familyPairing_eq_zero
      family p0Inside p4Inside side hpairZero hwitnessRed hwitnessBlue e hedge
  exact
    ⟨latent, hlatentMem, hp0, hp4, horientation, hforced, u, v, e, p,
      hedge, heOutside, hu, hv, hpEdges, havoid, hcross, hzeZero⟩

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

/-- Contrapositive diagnostic for the direct CAP5 forced-edge route.  If the enumerated forced
edges cover every nonzero selected-boundary-zero chain but Theorem 4.9 synthesis still fails,
then the missing ingredient is explicit: some enumerated forced edge lacks a red or blue
single-coordinate projected-generator witness. -/
theorem exists_forcedEdge_missing_red_or_blue_singleCoordinateWitness_of_forcedEdgeCoverage_of_not_theorem49BoundaryRootSynthesis
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    (∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
        ¬ ∃ i : κ,
          ((family i : projectedColoringGeneratorSubspace emb colorings) :
              G.edgeSet → Color) =
            Pi.single e red) ∨
      ∃ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
          ¬ ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue := by
  classical
  by_contra hnoGap
  have hred :
      ∀ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red := by
    intro e hedge
    by_contra hmissing
    exact hnoGap (Or.inl ⟨e, hedge, hmissing⟩)
  have hblue :
      ∀ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
          ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e blue := by
    intro e hedge
    by_contra hmissing
    exact hnoGap (Or.inr ⟨e, hedge, hmissing⟩)
  exact hnotSynthesis
    (data.theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeNonzeroWitnesses
      emb C₀ colorings hsubset family p0Inside p4Inside side hcoverage hred hblue)

/-- Exact CAP5 coverage dichotomy for the direct forced-edge route.  Once the enumerated forced
edges cover all nonzero selected-boundary-zero chains, either Theorem 4.9 synthesis follows or the
remaining obstruction is a named forced edge missing a red or blue projected single-coordinate
witness. -/
theorem theorem49BoundaryRootSynthesis_or_forcedEdge_missing_red_or_blue_singleCoordinateWitness_of_forcedEdgeCoverage
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    (p0Inside p4Inside : Bool) (side : V → Prop)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    Theorem49BoundaryRootSynthesis emb C₀ ∨
      (∃ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
          ¬ ∃ i : κ,
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) =
              Pi.single e red) ∨
        ∃ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            ¬ ∃ i : κ,
              ((family i : projectedColoringGeneratorSubspace emb colorings) :
                  G.edgeSet → Color) =
                Pi.single e blue := by
  classical
  by_cases hclosed : Theorem49BoundaryRootSynthesis emb C₀
  · exact Or.inl hclosed
  · exact Or.inr
      (data.exists_forcedEdge_missing_red_or_blue_singleCoordinateWitness_of_forcedEdgeCoverage_of_not_theorem49BoundaryRootSynthesis
        emb C₀ colorings hsubset family p0Inside p4Inside side hcoverage hclosed)

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

/-- Finite worklist of later control edges that are not yet emitted by the checker.  This is the
measure used by the CAP5 witness generator: every productive extension step must remove an edge
from this set rather than merely add more report structure around the same obstruction. -/
def remainingControlEdges
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    Finset G.edgeSet :=
  controlEdges.filter fun e => e ∉ classifier.emittedFinset

/-- Membership in the finite remaining-control-edge worklist. -/
theorem mem_remainingControlEdges_iff
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) (e : G.edgeSet) :
    e ∈ classifier.remainingControlEdges controlEdges ↔
      e ∈ controlEdges ∧ e ∉ classifier.emittedFinset := by
  simp [remainingControlEdges]

/-- Erasing any chosen remaining control edge strictly decreases the finite generator worklist. -/
theorem card_erase_remainingControlEdges_lt_of_mem
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) {e : G.edgeSet}
    (he : e ∈ classifier.remainingControlEdges controlEdges) :
    ((classifier.remainingControlEdges controlEdges).erase e).card <
      (classifier.remainingControlEdges controlEdges).card :=
  (classifier.remainingControlEdges controlEdges).card_erase_lt_of_mem he

/--
Explicit residual state for finite CAP5 worklist runs.  The Boolean classifier itself is
immutable--its emitted set is fixed by `accept_spec`--so iteration is represented by a separate
finite set of already processed remaining-control edges.
-/
def residualRemainingControlEdges
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges processed : Finset G.edgeSet) :
    Finset G.edgeSet :=
  classifier.remainingControlEdges controlEdges \ processed

/-- Membership in the explicit residual CAP5 worklist. -/
theorem mem_residualRemainingControlEdges_iff
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges processed : Finset G.edgeSet) (e : G.edgeSet) :
    e ∈ classifier.residualRemainingControlEdges controlEdges processed ↔
      e ∈ classifier.remainingControlEdges controlEdges ∧ e ∉ processed := by
  simp [residualRemainingControlEdges]

/--
Processing a residual edge is implemented by inserting it into the processed set; this is exactly
the same residual worklist as erasing that edge from the current residual state.
-/
theorem residualRemainingControlEdges_insert_eq_erase
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges processed : Finset G.edgeSet) (e : G.edgeSet) :
    classifier.residualRemainingControlEdges controlEdges (insert e processed) =
      (classifier.residualRemainingControlEdges controlEdges processed).erase e := by
  ext f
  by_cases hfe : f = e
  · subst hfe
    simp [residualRemainingControlEdges]
  · simp [residualRemainingControlEdges, hfe]

/-- Processing any residual edge strictly decreases the explicit residual worklist measure. -/
theorem card_residualRemainingControlEdges_insert_lt_of_mem
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges processed : Finset G.edgeSet) {e : G.edgeSet}
    (he : e ∈ classifier.residualRemainingControlEdges controlEdges processed) :
    (classifier.residualRemainingControlEdges controlEdges (insert e processed)).card <
      (classifier.residualRemainingControlEdges controlEdges processed).card := by
  rw [classifier.residualRemainingControlEdges_insert_eq_erase controlEdges processed e]
  exact Finset.card_erase_lt_of_mem he

/-- A remaining-control edge not yet recorded as processed lies in the explicit residual state. -/
theorem mem_residualRemainingControlEdges_of_mem_remainingControlEdges_of_not_mem_processed
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges processed : Finset G.edgeSet) {e : G.edgeSet}
    (heRemaining : e ∈ classifier.remainingControlEdges controlEdges)
    (heNotProcessed : e ∉ processed) :
    e ∈ classifier.residualRemainingControlEdges controlEdges processed :=
  (classifier.mem_residualRemainingControlEdges_iff controlEdges processed e).2
    ⟨heRemaining, heNotProcessed⟩

/--
A remaining-control edge not yet processed gives a strict residual-state decrease when inserted
into the processed set.
-/
theorem card_residualRemainingControlEdges_insert_lt_of_mem_remainingControlEdges_of_not_mem_processed
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges processed : Finset G.edgeSet) {e : G.edgeSet}
    (heRemaining : e ∈ classifier.remainingControlEdges controlEdges)
    (heNotProcessed : e ∉ processed) :
    (classifier.residualRemainingControlEdges controlEdges (insert e processed)).card <
      (classifier.residualRemainingControlEdges controlEdges processed).card :=
  classifier.card_residualRemainingControlEdges_insert_lt_of_mem controlEdges processed
    (classifier.mem_residualRemainingControlEdges_of_mem_remainingControlEdges_of_not_mem_processed
      controlEdges processed heRemaining heNotProcessed)

/--
The residual worklist is exhausted exactly when every original remaining-control edge has been
recorded as processed.
-/
theorem residualRemainingControlEdges_eq_empty_iff_remainingControlEdges_subset_processed
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges processed : Finset G.edgeSet) :
    classifier.residualRemainingControlEdges controlEdges processed = ∅ ↔
      classifier.remainingControlEdges controlEdges ⊆ processed := by
  constructor
  · intro h e heRemaining
    by_contra heNotProcessed
    have hmem : e ∈ classifier.residualRemainingControlEdges controlEdges processed := by
      simp [residualRemainingControlEdges, heRemaining, heNotProcessed]
    rw [h] at hmem
    simp at hmem
  · intro hsubset
    ext e
    constructor
    · intro he
      have he' :
          e ∈ classifier.remainingControlEdges controlEdges ∧ e ∉ processed := by
        simpa [residualRemainingControlEdges] using he
      exact False.elim (he'.2 (hsubset he'.1))
    · intro he
      simp at he

/-- Canonical finite trace listing the remaining-control worklist. -/
noncomputable def remainingControlEdgeTrace
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    List G.edgeSet :=
  (classifier.remainingControlEdges controlEdges).toList

/-- Membership in the canonical remaining-control trace is exactly worklist membership. -/
theorem mem_remainingControlEdgeTrace_iff
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) (e : G.edgeSet) :
    e ∈ classifier.remainingControlEdgeTrace controlEdges ↔
      e ∈ classifier.remainingControlEdges controlEdges := by
  simp [remainingControlEdgeTrace]

/-- The canonical remaining-control trace contains no duplicate edges. -/
theorem remainingControlEdgeTrace_nodup
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    (classifier.remainingControlEdgeTrace controlEdges).Nodup :=
  Finset.nodup_toList (classifier.remainingControlEdges controlEdges)

/-- The trace length is the named remaining-control measure. -/
theorem length_remainingControlEdgeTrace_eq_card_remainingControlEdges
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    (classifier.remainingControlEdgeTrace controlEdges).length =
      (classifier.remainingControlEdges controlEdges).card :=
  Finset.length_toList (classifier.remainingControlEdges controlEdges)

/-- The canonical trace's finite set is exactly the remaining-control worklist. -/
theorem remainingControlEdgeTrace_toFinset_eq_remainingControlEdges
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    (classifier.remainingControlEdgeTrace controlEdges).toFinset =
      classifier.remainingControlEdges controlEdges := by
  ext e
  simp [remainingControlEdgeTrace]

/-- Processing every edge in the canonical trace exhausts the explicit residual worklist. -/
theorem residualRemainingControlEdges_remainingControlEdgeTrace_toFinset_eq_empty
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    classifier.residualRemainingControlEdges controlEdges
        (classifier.remainingControlEdgeTrace controlEdges).toFinset = ∅ := by
  rw [classifier.remainingControlEdgeTrace_toFinset_eq_remainingControlEdges controlEdges]
  ext e
  simp [residualRemainingControlEdges]

/--
Packaged finite iteration certificate for the CAP5 remaining-control worklist: the trace has no
duplicates, lists exactly the remaining edges, has length equal to the worklist measure, and
exhausts the explicit residual state when all trace entries are processed.
-/
theorem exists_remainingControlEdgeTrace_certificate
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    ∃ trace : List G.edgeSet,
      trace.Nodup ∧
        (∀ e : G.edgeSet, e ∈ trace ↔ e ∈ classifier.remainingControlEdges controlEdges) ∧
          trace.length = (classifier.remainingControlEdges controlEdges).card ∧
            classifier.residualRemainingControlEdges controlEdges trace.toFinset = ∅ := by
  refine ⟨classifier.remainingControlEdgeTrace controlEdges, ?_, ?_, ?_, ?_⟩
  · exact classifier.remainingControlEdgeTrace_nodup controlEdges
  · exact classifier.mem_remainingControlEdgeTrace_iff controlEdges
  · exact classifier.length_remainingControlEdgeTrace_eq_card_remainingControlEdges controlEdges
  · exact
      classifier.residualRemainingControlEdges_remainingControlEdgeTrace_toFinset_eq_empty
        controlEdges

/-- New control edges outside a Boolean checker output that cross the proposed side.  This is the
finite geometric bin for a generator extension run. -/
noncomputable def crossingExtensionFinset
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    Finset G.edgeSet := by
  classical
  exact controlEdges.filter
    (fun e => e ∉ classifier.emittedFinset ∧ EdgeCrossesVertexSide G side e)

/-- New control edges outside a Boolean checker output that do not cross the proposed side.  This
is the finite algebraic-detector bin for a generator extension run. -/
noncomputable def noncrossingExtensionFinset
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    Finset G.edgeSet := by
  classical
  exact controlEdges.filter
    (fun e => e ∉ classifier.emittedFinset ∧ ¬ EdgeCrossesVertexSide G side e)

/-- Membership in the finite geometric extension bin. -/
theorem mem_crossingExtensionFinset_iff
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) (e : G.edgeSet) :
    e ∈ classifier.crossingExtensionFinset controlEdges ↔
      e ∈ controlEdges ∧ e ∉ classifier.emittedFinset ∧
        EdgeCrossesVertexSide G side e := by
  classical
  simp [crossingExtensionFinset]

/-- Membership in the finite algebraic-detector extension bin. -/
theorem mem_noncrossingExtensionFinset_iff
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) (e : G.edgeSet) :
    e ∈ classifier.noncrossingExtensionFinset controlEdges ↔
      e ∈ controlEdges ∧ e ∉ classifier.emittedFinset ∧
        ¬ EdgeCrossesVertexSide G side e := by
  classical
  simp [noncrossingExtensionFinset]

/-- The two extension bins together are exactly the later finite control edges that the
classifier has not emitted yet.  This is the finite witness-generator partition: every new
control edge is routed either to the side-crossing bin or the noncrossing/algebraic bin. -/
theorem crossingExtensionFinset_union_noncrossingExtensionFinset_eq_filter_not_emitted
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    classifier.crossingExtensionFinset controlEdges ∪
        classifier.noncrossingExtensionFinset controlEdges =
      controlEdges.filter fun e => e ∉ classifier.emittedFinset := by
  classical
  ext e
  constructor
  · intro he
    rcases Finset.mem_union.1 he with hcrossing | hnoncrossing
    · have he' :=
        (classifier.mem_crossingExtensionFinset_iff controlEdges e).1 hcrossing
      exact Finset.mem_filter.2 ⟨he'.1, he'.2.1⟩
    · have he' :=
        (classifier.mem_noncrossingExtensionFinset_iff controlEdges e).1 hnoncrossing
      exact Finset.mem_filter.2 ⟨he'.1, he'.2.1⟩
  · intro he
    rcases Finset.mem_filter.1 he with ⟨heControl, heNotEmitted⟩
    by_cases hcross : EdgeCrossesVertexSide G side e
    · exact Finset.mem_union.2 <| Or.inl <|
        (classifier.mem_crossingExtensionFinset_iff controlEdges e).2
          ⟨heControl, heNotEmitted, hcross⟩
    · exact Finset.mem_union.2 <| Or.inr <|
        (classifier.mem_noncrossingExtensionFinset_iff controlEdges e).2
          ⟨heControl, heNotEmitted, hcross⟩

/-- The crossing and noncrossing extension bins are exactly the finite remaining-control-edge
worklist, packaged under its named generator measure. -/
theorem crossingExtensionFinset_union_noncrossingExtensionFinset_eq_remainingControlEdges
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    classifier.crossingExtensionFinset controlEdges ∪
        classifier.noncrossingExtensionFinset controlEdges =
      classifier.remainingControlEdges controlEdges := by
  simpa [remainingControlEdges] using
    classifier.crossingExtensionFinset_union_noncrossingExtensionFinset_eq_filter_not_emitted
      controlEdges

/-- The side-crossing and noncrossing extension bins are disjoint. -/
theorem disjoint_crossingExtensionFinset_noncrossingExtensionFinset
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    Disjoint (classifier.crossingExtensionFinset controlEdges)
      (classifier.noncrossingExtensionFinset controlEdges) := by
  classical
  rw [Finset.disjoint_left]
  intro e hcrossing hnoncrossing
  have hcross :=
    (classifier.mem_crossingExtensionFinset_iff controlEdges e).1 hcrossing |>.2.2
  have hnotCross :=
    (classifier.mem_noncrossingExtensionFinset_iff controlEdges e).1 hnoncrossing |>.2.2
  exact hnotCross hcross

/-- A geometric-bin witness can be processed by erasing it from the finite remaining worklist. -/
theorem card_erase_remainingControlEdges_lt_of_mem_crossingExtensionFinset
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) {e : G.edgeSet}
    (he : e ∈ classifier.crossingExtensionFinset controlEdges) :
    ((classifier.remainingControlEdges controlEdges).erase e).card <
      (classifier.remainingControlEdges controlEdges).card := by
  have he' :=
    (classifier.mem_crossingExtensionFinset_iff controlEdges e).1 he
  exact classifier.card_erase_remainingControlEdges_lt_of_mem controlEdges
    ((classifier.mem_remainingControlEdges_iff controlEdges e).2 ⟨he'.1, he'.2.1⟩)

/-- A noncrossing/algebraic-bin witness can be processed by erasing it from the finite remaining
worklist. -/
theorem card_erase_remainingControlEdges_lt_of_mem_noncrossingExtensionFinset
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) {e : G.edgeSet}
    (he : e ∈ classifier.noncrossingExtensionFinset controlEdges) :
    ((classifier.remainingControlEdges controlEdges).erase e).card <
      (classifier.remainingControlEdges controlEdges).card := by
  have he' :=
    (classifier.mem_noncrossingExtensionFinset_iff controlEdges e).1 he
  exact classifier.card_erase_remainingControlEdges_lt_of_mem controlEdges
    ((classifier.mem_remainingControlEdges_iff controlEdges e).2 ⟨he'.1, he'.2.1⟩)

/-- Constructive nonempty form of the extension-bin partition.  The finite checker has a next
extension-bin witness exactly when the later finite control set contains an edge that the
classifier has not emitted yet. -/
theorem crossingExtensionFinset_nonempty_or_noncrossingExtensionFinset_nonempty_iff_exists_controlEdge_not_emitted
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    (classifier.crossingExtensionFinset controlEdges).Nonempty ∨
        (classifier.noncrossingExtensionFinset controlEdges).Nonempty ↔
      ∃ e : G.edgeSet, e ∈ controlEdges ∧ e ∉ classifier.emittedFinset := by
  classical
  constructor
  · rintro (hcrossing | hnoncrossing)
    · rcases hcrossing with ⟨e, he⟩
      have he' :=
        (classifier.mem_crossingExtensionFinset_iff controlEdges e).1 he
      exact ⟨e, he'.1, he'.2.1⟩
    · rcases hnoncrossing with ⟨e, he⟩
      have he' :=
        (classifier.mem_noncrossingExtensionFinset_iff controlEdges e).1 he
      exact ⟨e, he'.1, he'.2.1⟩
  · rintro ⟨e, heControl, heNotEmitted⟩
    by_cases hcross : EdgeCrossesVertexSide G side e
    · exact Or.inl ⟨e,
        (classifier.mem_crossingExtensionFinset_iff controlEdges e).2
          ⟨heControl, heNotEmitted, hcross⟩⟩
    · exact Or.inr ⟨e,
        (classifier.mem_noncrossingExtensionFinset_iff controlEdges e).2
          ⟨heControl, heNotEmitted, hcross⟩⟩

/-- Quantitative progress measure for the extension-bin checker: the number of un-emitted
finite control edges is exactly the number of crossing-bin edges plus the number of
noncrossing-bin edges. -/
theorem card_crossingExtensionFinset_add_card_noncrossingExtensionFinset_eq_card_filter_not_emitted
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    (classifier.crossingExtensionFinset controlEdges).card +
        (classifier.noncrossingExtensionFinset controlEdges).card =
      (controlEdges.filter fun e => e ∉ classifier.emittedFinset).card := by
  classical
  rw [← Finset.card_union_of_disjoint
    (classifier.disjoint_crossingExtensionFinset_noncrossingExtensionFinset controlEdges)]
  rw [classifier.crossingExtensionFinset_union_noncrossingExtensionFinset_eq_filter_not_emitted
    controlEdges]

/-- The extension-bin sizes add up to the named finite worklist size. -/
theorem card_crossingExtensionFinset_add_card_noncrossingExtensionFinset_eq_card_remainingControlEdges
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    (classifier.crossingExtensionFinset controlEdges).card +
        (classifier.noncrossingExtensionFinset controlEdges).card =
      (classifier.remainingControlEdges controlEdges).card := by
  simpa [remainingControlEdges] using
    classifier.card_crossingExtensionFinset_add_card_noncrossingExtensionFinset_eq_card_filter_not_emitted
      controlEdges

/-- Empty named worklist is equivalent to empty crossing and noncrossing extension bins. -/
theorem remainingControlEdges_eq_empty_iff_extensionFinsets_eq_empty
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    classifier.remainingControlEdges controlEdges = ∅ ↔
      classifier.crossingExtensionFinset controlEdges = ∅ ∧
        classifier.noncrossingExtensionFinset controlEdges = ∅ := by
  constructor
  · intro hremainingEmpty
    have hunionEmpty :
        classifier.crossingExtensionFinset controlEdges ∪
            classifier.noncrossingExtensionFinset controlEdges = ∅ := by
      rw [classifier.crossingExtensionFinset_union_noncrossingExtensionFinset_eq_remainingControlEdges
        controlEdges, hremainingEmpty]
    constructor
    · ext e
      constructor
      · intro he
        have heUnion :
            e ∈ classifier.crossingExtensionFinset controlEdges ∪
              classifier.noncrossingExtensionFinset controlEdges :=
          Finset.mem_union.2 (Or.inl he)
        rw [hunionEmpty] at heUnion
        exact heUnion
      · intro he
        simp at he
    · ext e
      constructor
      · intro he
        have heUnion :
            e ∈ classifier.crossingExtensionFinset controlEdges ∪
              classifier.noncrossingExtensionFinset controlEdges :=
          Finset.mem_union.2 (Or.inr he)
        rw [hunionEmpty] at heUnion
        exact heUnion
      · intro he
        simp at he
  · rintro ⟨hcrossingEmpty, hnoncrossingEmpty⟩
    rw [← classifier.crossingExtensionFinset_union_noncrossingExtensionFinset_eq_remainingControlEdges
      controlEdges, hcrossingEmpty, hnoncrossingEmpty]
    simp

/-- The two extension bins are empty exactly when the later finite control set introduces no edge
outside the classifier output.  This is the finite partition fact behind the checker fixed point:
every new control edge is either crossing or noncrossing with respect to the proposed side. -/
theorem controlEdges_subset_emittedFinset_iff_extensionFinsets_eq_empty
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet) :
    controlEdges ⊆ classifier.emittedFinset ↔
      classifier.crossingExtensionFinset controlEdges = ∅ ∧
        classifier.noncrossingExtensionFinset controlEdges = ∅ := by
  classical
  constructor
  · intro hsubset
    constructor
    · ext e
      constructor
      · intro he
        have he' :=
          (classifier.mem_crossingExtensionFinset_iff controlEdges e).1 he
        exact False.elim (he'.2.1 (hsubset he'.1))
      · intro he
        simp at he
    · ext e
      constructor
      · intro he
        have he' :=
          (classifier.mem_noncrossingExtensionFinset_iff controlEdges e).1 he
        exact False.elim (he'.2.1 (hsubset he'.1))
      · intro he
        simp at he
  · rintro ⟨hcrossingEmpty, hnoncrossingEmpty⟩ e heControl
    by_cases hcross : EdgeCrossesVertexSide G side e
    · by_contra heNotEmitted
      have heCrossing : e ∈ classifier.crossingExtensionFinset controlEdges :=
        (classifier.mem_crossingExtensionFinset_iff controlEdges e).2
          ⟨heControl, heNotEmitted, hcross⟩
      rw [hcrossingEmpty] at heCrossing
      simp at heCrossing
    · by_contra heNotEmitted
      have heNoncrossing : e ∈ classifier.noncrossingExtensionFinset controlEdges :=
        (classifier.mem_noncrossingExtensionFinset_iff controlEdges e).2
          ⟨heControl, heNotEmitted, hcross⟩
      rw [hnoncrossingEmpty] at heNoncrossing
      simp at heNoncrossing

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

/-- Strong finite-output form for complete cyclic-five exceptional CAP5 runs: the certified
emitted-edge set contains an edge that crosses the proposed side and is outside the generated
candidate support for one matching exceptional latent.  This is the finite witness-generator
obstruction boundary needed by separator and cocycle checks. -/
theorem exists_mem_enumeratedExceptionalAnnulusForcedEdgeFinset_crossing_outside_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
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
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        latent.p0Inside = p0Inside ∧
          latent.p4Inside = p4Inside ∧
            data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
              (let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
                { latent := latent, side := side };
                ∃ e : G.edgeSet, e ∈ emitted ∧ e ∉ node.candidate.edgeSupport ∧
                  EdgeCrossesVertexSide G side e) := by
  rcases data.exists_enumeratedExceptionalAnnulusForcedEdge_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      p0Inside p4Inside h side hcyclic hportal_crosses hcycles with
    ⟨e, hedge⟩
  have hnormal :=
    (data.enumeratedExceptionalAnnulusForcedEdge_iff_exists_latent_crossing_outside
      (p0Inside := p0Inside) (p4Inside := p4Inside) (side := side) (e := e)).1 hedge
  rcases hnormal with ⟨latent, hmem, hp0, hp4, horientation, houtside⟩
  let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
    { latent := latent, side := side }
  exact ⟨latent, hmem, hp0, hp4, horientation, by
    exact ⟨e, (hcert e).2 hedge, by simpa [node] using houtside⟩⟩

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

/-- Strong Boolean-checker output form for complete cyclic-five exceptional CAP5 runs: the
checker-emitted finite set contains a side-crossing edge outside one matching generated support. -/
theorem EnumeratedExceptionalAnnulusForcedEdgeClassifier.exists_mem_emittedFinset_crossing_outside_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
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
    ∃ latent : CAP5ExceptionalAnnulusGeneratorLatent boundaryEdge,
      latent ∈ CAP5ExceptionalAnnulusGeneratorLatent.all boundaryEdge ∧
        latent.p0Inside = p0Inside ∧
          latent.p4Inside = p4Inside ∧
            data.RealizesExceptionalBoundarySupportOrientation latent.orientation ∧
              (let node : CAP5ExceptionalAnnulusGeneratorNode boundaryEdge :=
                { latent := latent, side := side };
                ∃ e : G.edgeSet, e ∈ classifier.emittedFinset ∧
                  e ∉ node.candidate.edgeSupport ∧ EdgeCrossesVertexSide G side e) :=
  data.exists_mem_enumeratedExceptionalAnnulusForcedEdgeFinset_crossing_outside_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
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

/-- Subset fixed-point criterion for a Boolean CAP5 classifier.  If a finite checker has already
proved control for a control set, and every edge in that control set is already emitted by the
classifier, then the classifier itself controls the selected boundary-zero chains.  This is the
implementation-facing fixed point: no new control edges means no extension work remains. -/
theorem enumeratedExceptionalAnnulusForcedEdgeClassifierControl_of_finsetControl_of_controlEdges_subset_emittedFinset
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
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0 := by
  intro z hzBoundary hvanishEmitted
  exact hcontrol hzBoundary (by
    intro e heControl
    exact hvanishEmitted e (hsubsetEdges heControl))

/-- Synthesis from the subset fixed point.  A finite implementation can close the CAP5
classifier route by proving a finite control set controls selected boundary-zero chains and then
checking that this control set introduces no edge outside the classifier output. -/
theorem theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierControlEdgesSubset
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
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hsubsetEdges : controlEdges ⊆ classifier.emittedFinset)
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
  theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierControl
    emb C₀ colorings hsubset family p0Inside p4Inside side classifier
    (data.enumeratedExceptionalAnnulusForcedEdgeClassifierControl_of_finsetControl_of_controlEdges_subset_emittedFinset
      emb p0Inside p4Inside side classifier controlEdges hcontrol hsubsetEdges)
    hwitnessRed hwitnessBlue

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

/-- Exact obstruction boundary for a Boolean exceptional CAP5 checker.  The classifier controls the
selected-boundary-zero chains iff there is no nonzero selected-boundary-zero chain invisible to
every edge emitted by the generated CAP5 predicate.  This is the algebraic meaning of a successful
finite CAP5 run. -/
theorem enumeratedExceptionalAnnulusForcedEdgeClassifierControl_iff_no_boundaryZeroChainObstruction
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
    ¬ ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          ∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0 := by
  rw [← edgePredicateControls_iff_no_boundaryZeroChainObstruction
    (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)]
  constructor
  · intro hcontrol z hzBoundary hvanish
    exact hcontrol hzBoundary (by
      intro e hemitted
      exact hvanish e ((classifier.emittedFinset_spec e).1 hemitted))
  · intro hcontrol z hzBoundary hvanish
    exact hcontrol hzBoundary (by
      intro e hedge
      exact hvanish e ((classifier.emittedFinset_spec e).2 hedge))

/-- Coverage by the enumerated CAP5 forced-edge predicate is exactly the positive finite-control
condition for the Boolean classifier output.  This is the generic handoff from an F2 lab
coverage certificate to the Lean classifier-control API. -/
theorem enumeratedExceptionalAnnulusForcedEdgeClassifierControl_of_forcedEdgeCoverage
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0 := by
  exact
    (data.enumeratedExceptionalAnnulusForcedEdgeClassifierControl_iff_forall_nonzero_exists_mem_nonzero
      classifier).2
      (by
        intro z hzBoundary hzNonzero
        rcases hcoverage hzBoundary hzNonzero with ⟨e, hedge, hze⟩
        exact ⟨e, (classifier.emittedFinset_spec e).2 hedge, hze⟩)

/--
Finite-lab handoff for exact CAP5 coverage.  If a concrete control set meets every nonzero
selected-boundary-zero chain and every control edge is emitted by the CAP5 classifier, then the
enumerated CAP5 forced-edge predicate has the exact coverage property used by the synthesis
theorems.
-/
theorem forcedEdgeCoverage_of_controlEdges_subset_emittedFinset
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcontrolCoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet, e ∈ controlEdges ∧ z e ≠ 0)
    (hsubset : controlEdges ⊆ classifier.emittedFinset) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      z ≠ 0 →
        ∃ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            z e ≠ 0 := by
  intro z hzBoundary hzNonzero
  rcases hcontrolCoverage hzBoundary hzNonzero with ⟨e, heControl, hze⟩
  exact ⟨e, (classifier.emittedFinset_spec e).1 (hsubset heControl), hze⟩

/--
Classifier-control handoff for finite F₂ lab coverage.  A concrete control set that meets every
nonzero selected-boundary-zero chain controls the classifier output as soon as all of its edges
are emitted by the classifier.
-/
theorem enumeratedExceptionalAnnulusForcedEdgeClassifierControl_of_controlEdges_nonzeroCoverage_subset_emittedFinset
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    (emb : PlaneEmbeddingWithBoundary G)
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    (controlEdges : Finset G.edgeSet)
    (hcontrolCoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet, e ∈ controlEdges ∧ z e ≠ 0)
    (hsubset : controlEdges ⊆ classifier.emittedFinset) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0 :=
  data.enumeratedExceptionalAnnulusForcedEdgeClassifierControl_of_forcedEdgeCoverage
    emb classifier
    (data.forcedEdgeCoverage_of_controlEdges_subset_emittedFinset
      emb classifier controlEdges hcontrolCoverage hsubset)

/-- Synthesis endpoint for exact CAP5 forced-edge coverage.  If the enumerated forced-edge set
covers every nonzero selected-boundary-zero chain, and the chosen projected generator family has
red and blue single-coordinate witnesses on every emitted classifier edge, then the boundary-root
synthesis follows. -/
theorem theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage
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
    (hcoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
              z e ≠ 0)
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
  data.theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierControl
    emb C₀ colorings hsubset family p0Inside p4Inside side classifier
    (data.enumeratedExceptionalAnnulusForcedEdgeClassifierControl_of_forcedEdgeCoverage
      emb classifier hcoverage)
    hwitnessRed hwitnessBlue

/--
Synthesis endpoint from finite F₂ lab coverage and classifier emission.  This removes the
abstract exact-coverage hypothesis from the Boolean-classifier route: a lab-certified control set
that catches every nonzero selected-boundary-zero chain, and is wholly emitted by the classifier,
is enough to feed the existing CAP5 synthesis theorem.
-/
theorem theorem49BoundaryRootSynthesis_of_controlEdges_nonzeroCoverage_subset_emittedFinset
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
    (controlEdges : Finset G.edgeSet)
    (hcontrolCoverage :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        z ≠ 0 →
          ∃ e : G.edgeSet, e ∈ controlEdges ∧ z e ≠ 0)
    (hsubsetEdges : controlEdges ⊆ classifier.emittedFinset)
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
  data.theorem49BoundaryRootSynthesis_of_forcedEdgeCoverage
    emb C₀ colorings hsubset family p0Inside p4Inside side classifier
    (data.forcedEdgeCoverage_of_controlEdges_subset_emittedFinset
      emb classifier controlEdges hcontrolCoverage hsubsetEdges)
    hwitnessRed hwitnessBlue

/-- A CAP5 emitted-edge obstruction is an explicit nonzero kernel witness for any red/blue
single-coordinate family that only probes edges emitted by the CAP5 classifier.  Thus a failed
finite control run returns the exact algebraic payload needed to diagnose why the coordinate
generator cannot justify the synthesis route without adding a stronger detector. -/
theorem exists_nonzero_mem_ker_planarBoundaryZeroFamilyPairingMap_of_enumeratedExceptionalAnnulusBoundaryZeroChainObstruction
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (hfamily :
      ∀ i : κ,
        ∃ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            (((family i : projectedColoringGeneratorSubspace emb colorings) :
                  G.edgeSet → Color) = Pi.single e red ∨
              ((family i : projectedColoringGeneratorSubspace emb colorings) :
                  G.edgeSet → Color) = Pi.single e blue))
    (hobs :
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) :
    ∃ w : planarBoundaryZeroSubmodule emb,
      w ∈ LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) ∧
        w ≠ 0 := by
  rcases hobs with ⟨z, hzBoundary, hzNonzero, hvanish⟩
  exact
    exists_nonzero_mem_ker_planarBoundaryZeroFamilyPairingMap_of_boundaryZeroChainObstruction
      family (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)
      hfamily z hzBoundary hzNonzero hvanish

/-- A CAP5 emitted-edge obstruction rules out a trivial family-pairing kernel for any red/blue
single-coordinate family that only probes classifier-emitted edges.  This is the negative
certificate shape for the generator: once this obstruction is returned, the current emitted-edge
coordinate detector is provably incomplete. -/
theorem not_ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_enumeratedExceptionalAnnulusBoundaryZeroChainObstruction
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (hfamily :
      ∀ i : κ,
        ∃ e : G.edgeSet,
          data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
            (((family i : projectedColoringGeneratorSubspace emb colorings) :
                  G.edgeSet → Color) = Pi.single e red ∨
              ((family i : projectedColoringGeneratorSubspace emb colorings) :
                  G.edgeSet → Color) = Pi.single e blue))
    (hobs :
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) :
    LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) ≠ ⊥ :=
  not_ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_boundaryZeroChainObstruction
    family (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)
    hfamily hobs

/-- Detector-enrichment boundary for the CAP5 finite generator.  If an emitted-edge CAP5
obstruction exists but a red/blue single-coordinate family has trivial family-pairing kernel, then
that family must include at least one probe outside the CAP5 classifier's emitted-edge predicate.
This is the next-pass instruction produced by the obstruction. -/
theorem exists_family_singleCoordinate_not_enumeratedExceptionalAnnulusForcedEdge_of_boundaryZeroChainObstruction_of_ker_eq_bot
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (hsingle :
      ∀ i : κ,
        ∃ e : G.edgeSet,
          (((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e red ∨
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e blue))
    (hobs :
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0)
    (hker : LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥) :
    ∃ i : κ, ∃ e : G.edgeSet,
      ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
        (((family i : projectedColoringGeneratorSubspace emb colorings) :
              G.edgeSet → Color) = Pi.single e red ∨
          ((family i : projectedColoringGeneratorSubspace emb colorings) :
              G.edgeSet → Color) = Pi.single e blue) :=
  exists_family_singleCoordinate_outside_predicate_of_boundaryZeroChainObstruction_of_ker_eq_bot
    family (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)
    hsingle hobs hker

/-- Concrete CAP5 enrichment witness from a returned obstruction chain.  If the family has
trivial pairing kernel, some single-coordinate probe outside the enumerated CAP5 forced-edge
predicate pairs nontrivially with the obstruction.  This is the edge-level payload for the next
generator iteration. -/
theorem exists_family_singleCoordinate_not_enumeratedExceptionalAnnulusForcedEdge_pairing_ne_zero_of_boundaryZeroChainObstruction_of_ker_eq_bot
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    {colorings : Set (G.EdgeColoring Color)}
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
    {p0Inside p4Inside : Bool} {side : V → Prop}
    (hsingle :
      ∀ i : κ,
        ∃ e : G.edgeSet,
          (((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e red ∨
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e blue))
    (z : G.edgeSet → Color)
    (hzBoundary : z ∈ planarBoundaryZeroSubmodule emb)
    (hzNonzero : z ≠ 0)
    (hvanish :
      ∀ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
          z e = 0)
    (hker : LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) = ⊥) :
    ∃ i : κ, ∃ e : G.edgeSet,
      ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
        (((family i : projectedColoringGeneratorSubspace emb colorings) :
              G.edgeSet → Color) = Pi.single e red ∨
          ((family i : projectedColoringGeneratorSubspace emb colorings) :
              G.edgeSet → Color) = Pi.single e blue) ∧
        chainDotBilinForm G.edgeSet (family i : G.edgeSet → Color) z ≠ 0 ∧
        z e ≠ 0 :=
  exists_family_singleCoordinate_outside_predicate_pairing_ne_zero_of_boundaryZeroChainObstruction_of_ker_eq_bot
    family (data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side)
    hsingle z hzBoundary hzNonzero hvanish hker

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

/-- Closed-walk kernel-shell packaging of the Boolean classifier nonzero-witness certificate.
This keeps the finite `F₂` checker output as a reusable pairing-kernel shell instead of using it
only once to prove synthesis. -/
def closedWalkNeighborhoodPairingKernelShell_of_enumeratedExceptionalAnnulusForcedEdgeClassifierNonzeroWitnesses
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (shell : ClosedWalkExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
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
    ClosedWalkNeighborhoodPairingKernelShell emb :=
  ClosedWalkNeighborhoodPairingKernelShell.of_controlEdgeNonzeroWitnesses
    shell colorings hsubset family classifier.emittedFinset
    hnonzero hwitnessRed hwitnessBlue

/-- Successor-cycle kernel-shell packaging of the same Boolean classifier nonzero-witness
certificate. -/
def successorCycleNeighborhoodPairingKernelShell_of_enumeratedExceptionalAnnulusForcedEdgeClassifierNonzeroWitnesses
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (shell : SuccessorCycleExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
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
    SuccessorCycleNeighborhoodPairingKernelShell emb :=
  SuccessorCycleNeighborhoodPairingKernelShell.of_controlEdgeNonzeroWitnesses
    shell colorings hsubset family classifier.emittedFinset
    hnonzero hwitnessRed hwitnessBlue

/-- Theorem 4.9 synthesis from the exact no-obstruction boundary.  Once the checker output has
red/blue single-edge witnesses for every emitted edge, excluding the boundary-zero obstruction is
precisely enough to enter the boundary-root synthesis route. -/
theorem theorem49BoundaryRootSynthesis_of_no_boundaryZeroChainObstruction_of_classifierWitnesses
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
    (hnoObstruction :
      ¬ ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0)
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
  theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierControl
    emb C₀ colorings hsubset family p0Inside p4Inside side classifier
    ((data.enumeratedExceptionalAnnulusForcedEdgeClassifierControl_iff_no_boundaryZeroChainObstruction
      classifier).2 hnoObstruction)
    hwitnessRed hwitnessBlue

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

/-- Finite-control extension witness for a failed Boolean CAP5 classifier.  If the classifier's
emitted edge set does not control selected-boundary-zero chains, but a later finite control set
does, then a returned obstruction identifies a genuinely new control edge outside the classifier
output where the obstruction is nonzero. -/
theorem exists_boundaryZeroChain_and_newControlEdge_nonzero_of_not_classifierControl_of_finsetControl
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
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          (∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0) ∧
            ∃ e : G.edgeSet,
              e ∈ controlEdges ∧ e ∉ classifier.emittedFinset ∧ z e ≠ 0 := by
  rcases exists_obstruction_and_newControlEdge_nonzero_of_not_finsetControls_of_finsetControls
      classifier.emittedFinset controlEdges hnotControl hcontrol with
    ⟨z, hzBoundary, hzNonzero, hvanishEmitted, hnew⟩
  exact ⟨z, hzBoundary, hzNonzero, by
    intro e hedge
    exact hvanishEmitted e ((classifier.emittedFinset_spec e).2 hedge),
    hnew⟩

/-- Geometric/algebraic binning for a failed Boolean CAP5 classifier after a successful later
finite-control extension.  The new nonzero control edge returned by the algebraic obstruction is
either a side-crossing one-edge probe outside the classifier output, or a noncrossing coordinate
that must be handled by the algebraic detector. -/
theorem exists_boundaryZeroChain_and_newControlEdge_crossing_or_noncrossing_of_not_classifierControl_of_finsetControl
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
              e ∈ controlEdges ∧
                e ∉ classifier.emittedFinset ∧
                  ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                    z e ≠ 0 ∧
                      EdgeCrossesVertexSide G side e ∧
                        side u ∧ ¬ side v ∧
                          p.edges = [(e : Sym2 V)] ∧
                            ∀ f : G.edgeSet, f ∈ classifier.emittedFinset →
                              (f : Sym2 V) ∉ p.edges) ∨
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ e : G.edgeSet,
                e ∈ controlEdges ∧
                  e ∉ classifier.emittedFinset ∧
                    ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                      z e ≠ 0 ∧ ¬ EdgeCrossesVertexSide G side e := by
  classical
  rcases data.exists_boundaryZeroChain_and_newControlEdge_nonzero_of_not_classifierControl_of_finsetControl
      emb p0Inside p4Inside side classifier controlEdges hnotControl hcontrol with
    ⟨z, hzBoundary, hzNonzero, hvanish, e, heControl, heOutside, hze⟩
  have hePredicateOutside :
      ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e := by
    intro hedge
    exact heOutside ((classifier.emittedFinset_spec e).2 hedge)
  by_cases hcross : EdgeCrossesVertexSide G side e
  · rcases hcross with ⟨u, v, hu, hv, hsu, hsv⟩
    rcases exists_walk_edges_eq_singleton_of_edge_endpoint_sides
        (G := G) (side := side) hu hv hsu hsv with
      ⟨p, hpEdges⟩
    refine Or.inl ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p,
      heControl, heOutside, hePredicateOutside, hze, ?_, hsu, hsv, hpEdges, ?_⟩
    · exact ⟨u, v, hu, hv, hsu, hsv⟩
    intro f hf hmem
    have hsym : (f : Sym2 V) = (e : Sym2 V) := by
      simpa [hpEdges] using hmem
    have hfe : f = e := Subtype.ext hsym
    exact heOutside (by simpa [hfe] using hf)
  · exact Or.inr ⟨z, hzBoundary, hzNonzero, hvanish, e,
      heControl, heOutside, hePredicateOutside, hze, hcross⟩

/-- Finite-bin witness form of the failed Boolean CAP5 classifier extension.  This is the
consumer-facing version of the crossing/noncrossing split: the returned nonzero obstruction
coordinate is packaged as membership in the finite extension bin that a checker can enumerate. -/
theorem exists_boundaryZeroChain_and_extensionFinsetWitness_crossing_or_noncrossing_of_not_classifierControl_of_finsetControl
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
                          ∀ f : G.edgeSet, f ∈ classifier.emittedFinset →
                            (f : Sym2 V) ∉ p.edges) ∨
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ e : G.edgeSet,
                e ∈ classifier.noncrossingExtensionFinset controlEdges ∧
                  ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                    z e ≠ 0 ∧ ¬ EdgeCrossesVertexSide G side e := by
  rcases data.exists_boundaryZeroChain_and_newControlEdge_crossing_or_noncrossing_of_not_classifierControl_of_finsetControl
      emb p0Inside p4Inside side classifier controlEdges hnotControl hcontrol with
    hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p,
        heControl, heOutside, hePredicateOutside, hze, hcross, hsu, hsv,
        hpEdges, havoid⟩
    exact Or.inl ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p,
      (classifier.mem_crossingExtensionFinset_iff controlEdges e).2
        ⟨heControl, heOutside, hcross⟩,
      hePredicateOutside, hze, hcross, hsu, hsv, hpEdges, havoid⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, e,
        heControl, heOutside, hePredicateOutside, hze, hnotCross⟩
    exact Or.inr ⟨z, hzBoundary, hzNonzero, hvanish, e,
      (classifier.mem_noncrossingExtensionFinset_iff controlEdges e).2
        ⟨heControl, heOutside, hnotCross⟩,
      hePredicateOutside, hze, hnotCross⟩

/-- If the finite geometric extension bin is empty, a successful finite-control extension of a
failed Boolean CAP5 classifier must return a noncrossing algebraic-detector coordinate. -/
theorem exists_boundaryZeroChain_and_noncrossingExtensionFinsetWitness_of_not_classifierControl_of_finsetControl_of_crossingExtensionFinset_eq_empty
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
          z = 0)
    (hcrossingEmpty : classifier.crossingExtensionFinset controlEdges = ∅) :
    ∃ z : G.edgeSet → Color,
      z ∈ planarBoundaryZeroSubmodule emb ∧
        z ≠ 0 ∧
          (∀ e : G.edgeSet,
            data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
              z e = 0) ∧
            ∃ e : G.edgeSet,
              e ∈ classifier.noncrossingExtensionFinset controlEdges ∧
                ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                  z e ≠ 0 ∧ ¬ EdgeCrossesVertexSide G side e := by
  rcases data.exists_boundaryZeroChain_and_extensionFinsetWitness_crossing_or_noncrossing_of_not_classifierControl_of_finsetControl
      emb p0Inside p4Inside side classifier controlEdges hnotControl hcontrol with
    hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨_z, _hzBoundary, _hzNonzero, _hvanish, _u, _v, e, _p,
        heCrossingBin, _hePredicateOutside, _hze, _hcross, _hsu, _hsv,
        _hpEdges, _havoid⟩
    rw [hcrossingEmpty] at heCrossingBin
    simp at heCrossingBin
  · exact hnoncrossing

/-- If the finite algebraic-detector extension bin is empty, a successful finite-control
extension of a failed Boolean CAP5 classifier must return a crossing one-edge witness. -/
theorem exists_boundaryZeroChain_and_crossingExtensionFinsetWitness_of_not_classifierControl_of_finsetControl_of_noncrossingExtensionFinset_eq_empty
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
          z = 0)
    (hnoncrossingEmpty : classifier.noncrossingExtensionFinset controlEdges = ∅) :
    ∃ z : G.edgeSet → Color,
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
                          ∀ f : G.edgeSet, f ∈ classifier.emittedFinset →
                            (f : Sym2 V) ∉ p.edges := by
  rcases data.exists_boundaryZeroChain_and_extensionFinsetWitness_crossing_or_noncrossing_of_not_classifierControl_of_finsetControl
      emb p0Inside p4Inside side classifier controlEdges hnotControl hcontrol with
    hcrossing | hnoncrossing
  · exact hcrossing
  · rcases hnoncrossing with
      ⟨_z, _hzBoundary, _hzNonzero, _hvanish, e,
        heNoncrossingBin, _hePredicateOutside, _hze, _hnotCross⟩
    rw [hnoncrossingEmpty] at heNoncrossingBin
    simp at heNoncrossingBin

/-- Fixed-point criterion for a finite CAP5 classifier.  If a later finite control set controls
all selected boundary-zero chains, and both extension bins are empty, then the current classifier
already controls the selected boundary-zero chains.  This is the success case dual to the witness
generator: nonempty bins produce the next witness; empty bins close the finite classifier. -/
theorem enumeratedExceptionalAnnulusForcedEdgeClassifierControl_of_finsetControl_of_extensionFinsets_eq_empty
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
    (hcrossingEmpty : classifier.crossingExtensionFinset controlEdges = ∅)
    (hnoncrossingEmpty : classifier.noncrossingExtensionFinset controlEdges = ∅) :
    ∀ ⦃z : G.edgeSet → Color⦄,
      z ∈ planarBoundaryZeroSubmodule emb →
      (∀ e ∈ classifier.emittedFinset, z e = 0) →
        z = 0 := by
  have hsubsetEdges : controlEdges ⊆ classifier.emittedFinset :=
    (classifier.controlEdges_subset_emittedFinset_iff_extensionFinsets_eq_empty
      controlEdges).2 ⟨hcrossingEmpty, hnoncrossingEmpty⟩
  exact
    data.enumeratedExceptionalAnnulusForcedEdgeClassifierControl_of_finsetControl_of_controlEdges_subset_emittedFinset
      emb p0Inside p4Inside side classifier controlEdges hcontrol hsubsetEdges

/-- A successful finite-control extension of a failed Boolean CAP5 classifier makes at least one
of the two finite extension bins nonempty: either a new side-crossing edge appears, or a new
noncrossing algebraic detector coordinate appears. -/
theorem crossingExtensionFinset_nonempty_or_noncrossingExtensionFinset_nonempty_of_not_classifierControl_of_finsetControl
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
    (classifier.crossingExtensionFinset controlEdges).Nonempty ∨
      (classifier.noncrossingExtensionFinset controlEdges).Nonempty := by
  rcases data.exists_boundaryZeroChain_and_newControlEdge_crossing_or_noncrossing_of_not_classifierControl_of_finsetControl
      emb p0Inside p4Inside side classifier controlEdges hnotControl hcontrol with
    hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨_z, _hzBoundary, _hzNonzero, _hvanish, _u, _v, e, _p,
        heControl, heOutside, _hePredicateOutside, _hze, hcross, _hsu, _hsv,
        _hpEdges, _havoid⟩
    exact Or.inl ⟨e,
      (classifier.mem_crossingExtensionFinset_iff controlEdges e).2
        ⟨heControl, heOutside, hcross⟩⟩
  · rcases hnoncrossing with
      ⟨_z, _hzBoundary, _hzNonzero, _hvanish, e,
        heControl, heOutside, _hePredicateOutside, _hze, hnotCross⟩
    exact Or.inr ⟨e,
      (classifier.mem_noncrossingExtensionFinset_iff controlEdges e).2
        ⟨heControl, heOutside, hnotCross⟩⟩

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

/-- Kernel-aware finite-checker dichotomy for a Boolean exceptional CAP5 classifier.  If the
checker's emitted edges are covered by red/blue probes, and the explicit family contains only
red/blue probes on emitted edges, then the finite control decision returns either Theorem 4.9
boundary-root synthesis or a nontrivial kernel for the family-pairing map.

This is the algebraic failure form of the checker: an obstruction is no longer just a vanishing
boundary-zero chain, but a proof that the current emitted-edge probe family cannot have trivial
kernel. -/
theorem theorem49BoundaryRootSynthesis_or_ker_planarBoundaryZeroFamilyPairingMap_ne_bot_of_classifierControl
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
    (hfamilyOnlyEmitted :
      ∀ i : κ,
        ∃ e : G.edgeSet, e ∈ classifier.emittedFinset ∧
          (((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e red ∨
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e blue))
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
      LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) ≠ ⊥ := by
  rcases data.theorem49BoundaryRootSynthesis_or_boundaryZeroChainObstruction_of_classifierControl
      emb C₀ colorings hsubset family p0Inside p4Inside side classifier
      hwitnessRed hwitnessBlue with
    hsynthesis | hobs
  · exact Or.inl hsynthesis
  · refine Or.inr ?_
    apply
      not_ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_enumeratedExceptionalAnnulusBoundaryZeroChainObstruction
        family
    · intro i
      rcases hfamilyOnlyEmitted i with ⟨e, hemitted, hprobe⟩
      exact ⟨e, (classifier.emittedFinset_spec e).1 hemitted, hprobe⟩
    · exact hobs

/-- Generator-first CAP5 branch theorem.  A complete exceptional CAP5 sample either realizes the
exact proposed side, or it emits a forced edge and the finite algebraic checker produces the
next non-geometric outcome: Theorem 4.9 boundary-root synthesis, or a concrete boundary-zero
obstruction invisible to every generated forced edge. -/
theorem enumeratedExceptionalAnnulusSameSideRealization_or_forcedEdge_and_theorem49BoundaryRootSynthesis_or_boundaryZeroChainObstruction
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
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
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v))
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
    data.EnumeratedExceptionalAnnulusSameSideRealization p0Inside p4Inside side ∨
      (∃ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) ∧
        (Theorem49BoundaryRootSynthesis emb C₀ ∨
          ∃ z : G.edgeSet → Color,
            z ∈ planarBoundaryZeroSubmodule emb ∧
              z ≠ 0 ∧
                ∀ e : G.edgeSet,
                  data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                    z e = 0) := by
  rcases data.enumeratedExceptionalAnnulusSameSideRealization_or_exists_enumeratedExceptionalAnnulusForcedEdge_of_isExceptional_of_portalSides
      p0Inside p4Inside h side hportal_crosses hcycles with
    hsameSide | hforced
  · exact Or.inl hsameSide
  · have halgebraic :=
      data.theorem49BoundaryRootSynthesis_or_boundaryZeroChainObstruction_of_classifierControl
        emb C₀ colorings hsubset family p0Inside p4Inside side classifier hwitnessRed
        hwitnessBlue
    exact Or.inr ⟨hforced, halgebraic⟩

/-- Kernel-aware generator-first CAP5 branch theorem.  A complete exceptional CAP5 sample either
realizes the exact proposed side, or it emits a forced edge and the finite algebraic checker
returns the next non-geometric outcome in kernel form: Theorem 4.9 boundary-root synthesis, or a
proof that the current emitted-edge probe family has nontrivial family-pairing kernel. -/
theorem enumeratedExceptionalAnnulusSameSideRealization_or_forcedEdge_and_theorem49BoundaryRootSynthesis_or_ker_planarBoundaryZeroFamilyPairingMap_ne_bot
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet] [FiniteDimensional F2 (G.edgeSet → Color)]
    (emb : PlaneEmbeddingWithBoundary G) (C₀ : G.EdgeColoring Color)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure C₀)
    {κ : Type*}
    (family : κ → projectedColoringGeneratorSubspace emb colorings)
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
    (hcycles : HasCycleOnSide G side ∧ HasCycleOnSide G (fun v => ¬ side v))
    (classifier :
      data.EnumeratedExceptionalAnnulusForcedEdgeClassifier p0Inside p4Inside side)
    [Decidable
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)]
    (hfamilyOnlyEmitted :
      ∀ i : κ,
        ∃ e : G.edgeSet, e ∈ classifier.emittedFinset ∧
          (((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e red ∨
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e blue))
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
    data.EnumeratedExceptionalAnnulusSameSideRealization p0Inside p4Inside side ∨
      (∃ e : G.edgeSet,
        data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) ∧
        (Theorem49BoundaryRootSynthesis emb C₀ ∨
          LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) ≠ ⊥) := by
  rcases data.enumeratedExceptionalAnnulusSameSideRealization_or_exists_enumeratedExceptionalAnnulusForcedEdge_of_isExceptional_of_portalSides
      p0Inside p4Inside h side hportal_crosses hcycles with
    hsameSide | hforced
  · exact Or.inl hsameSide
  · have halgebraic :=
      data.theorem49BoundaryRootSynthesis_or_ker_planarBoundaryZeroFamilyPairingMap_ne_bot_of_classifierControl
        emb C₀ colorings hsubset family p0Inside p4Inside side classifier
        hfamilyOnlyEmitted hwitnessRed hwitnessBlue
    exact Or.inr ⟨hforced, halgebraic⟩

/-- Cyclic-connectivity specialization of the generator-first CAP5 branch theorem.  In the
target cyclic-five setting the exact same-side realization branch is impossible, so the finite
sample must emit a forced edge and immediately enter the algebraic fallback: either Theorem 4.9
boundary-root synthesis, or a concrete boundary-zero obstruction invisible to all generated
forced edges. -/
theorem forcedEdge_and_theorem49BoundaryRootSynthesis_or_boundaryZeroChainObstruction_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
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
    (∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) ∧
      (Theorem49BoundaryRootSynthesis emb C₀ ∨
        ∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              ∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) := by
  rcases data.enumeratedExceptionalAnnulusSameSideRealization_or_forcedEdge_and_theorem49BoundaryRootSynthesis_or_boundaryZeroChainObstruction
      emb C₀ colorings hsubset family p0Inside p4Inside h side hportal_crosses hcycles
      classifier hwitnessRed hwitnessBlue with
    hsameSide | hfallback
  · exact False.elim
      (data.not_enumeratedExceptionalAnnulusSameSideRealization_of_cyclicallyFiveEdgeConnected
        (p0Inside := p0Inside) (p4Inside := p4Inside) (side := side) hcyclic hsameSide)
  · exact hfallback

/-- Kernel-aware cyclic-connectivity specialization of the generator-first CAP5 branch theorem.
In the cyclic-five setting, the exact same-side realization branch is impossible, so the finite
sample emits a forced edge and the algebraic checker returns either Theorem 4.9 boundary-root
synthesis or a nontrivial kernel for the current emitted-edge family-pairing map. -/
theorem forcedEdge_and_theorem49BoundaryRootSynthesis_or_ker_planarBoundaryZeroFamilyPairingMap_ne_bot_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
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
    [Decidable
      (∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ classifier.emittedFinset, z e = 0) →
          z = 0)]
    (hfamilyOnlyEmitted :
      ∀ i : κ,
        ∃ e : G.edgeSet, e ∈ classifier.emittedFinset ∧
          (((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e red ∨
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e blue))
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
    (∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) ∧
      (Theorem49BoundaryRootSynthesis emb C₀ ∨
        LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) ≠ ⊥) := by
  rcases data.enumeratedExceptionalAnnulusSameSideRealization_or_forcedEdge_and_theorem49BoundaryRootSynthesis_or_ker_planarBoundaryZeroFamilyPairingMap_ne_bot
      emb C₀ colorings hsubset family p0Inside p4Inside h side hportal_crosses hcycles
      classifier hfamilyOnlyEmitted hwitnessRed hwitnessBlue with
    hsameSide | hfallback
  · exact False.elim
      (data.not_enumeratedExceptionalAnnulusSameSideRealization_of_cyclicallyFiveEdgeConnected
        (p0Inside := p0Inside) (p4Inside := p4Inside) (side := side) hcyclic hsameSide)
  · exact hfallback

/-- Contrapositive CAP5 target boundary.  In the cyclic-five setting, if the boundary-root
synthesis route fails after the finite classifier has supplied red/blue witnesses, the failure is
not ambiguous: the generator has emitted a forced edge and there is a concrete nonzero
boundary-zero chain invisible to every generated forced edge. -/
theorem forcedEdge_and_boundaryZeroChainObstruction_of_not_theorem49BoundaryRootSynthesis_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
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
    (hnotSynthesis : ¬ Theorem49BoundaryRootSynthesis emb C₀) :
    (∃ e : G.edgeSet,
      data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e) ∧
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0 := by
  constructor
  · exact
      data.exists_enumeratedExceptionalAnnulusForcedEdge_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
        p0Inside p4Inside h side hcyclic hportal_crosses hcycles
  · by_contra hnoObstruction
    exact hnotSynthesis
      (data.theorem49BoundaryRootSynthesis_of_no_boundaryZeroChainObstruction_of_classifierWitnesses
        emb C₀ colorings hsubset family p0Inside p4Inside side classifier hnoObstruction
        hwitnessRed hwitnessBlue)

/-- Kernel-aware contrapositive CAP5 target boundary.  In the cyclic-five setting, if the
boundary-root synthesis route fails and the explicit family only probes emitted red/blue
coordinates, the finite generator has emitted a forced edge and the current family-pairing map has
nontrivial kernel.  This is the algebraic failure certificate extracted from the failed CAP5
branch. -/
theorem forcedEdge_and_ker_planarBoundaryZeroFamilyPairingMap_ne_bot_of_not_theorem49BoundaryRootSynthesis_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
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
    (hfamilyOnlyEmitted :
      ∀ i : κ,
        ∃ e : G.edgeSet, e ∈ classifier.emittedFinset ∧
          (((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e red ∨
            ((family i : projectedColoringGeneratorSubspace emb colorings) :
                G.edgeSet → Color) = Pi.single e blue))
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
      LinearMap.ker (planarBoundaryZeroFamilyPairingMap family) ≠ ⊥ := by
  constructor
  · exact
      data.exists_enumeratedExceptionalAnnulusForcedEdge_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
        p0Inside p4Inside h side hcyclic hportal_crosses hcycles
  · rcases data.forcedEdge_and_boundaryZeroChainObstruction_of_not_theorem49BoundaryRootSynthesis_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
      emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier hwitnessRed hwitnessBlue hnotSynthesis with
    ⟨_, hobs⟩
    apply
      not_ker_planarBoundaryZeroFamilyPairingMap_eq_bot_of_enumeratedExceptionalAnnulusBoundaryZeroChainObstruction
        family
    · intro i
      rcases hfamilyOnlyEmitted i with ⟨e, hemitted, hprobe⟩
      exact ⟨e, (classifier.emittedFinset_spec e).1 hemitted, hprobe⟩
    · exact hobs

/-- Generator handoff after failed CAP5 synthesis.  In the cyclic-five exceptional setting, if the
current classifier witnesses do not synthesize the boundary root but a later finite control set
does control the selected boundary-zero chains, then the generator has both the obstruction and a
nonempty next extension bin.  The bin is the concrete next finite artifact to inspect: crossing
edges feed the separator route, while noncrossing edges feed the algebraic detector route. -/
theorem forcedEdge_and_boundaryZeroChainObstruction_and_extensionBin_nonempty_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
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
      (∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            ∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
        ((classifier.crossingExtensionFinset controlEdges).Nonempty ∨
          (classifier.noncrossingExtensionFinset controlEdges).Nonempty) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      data.exists_enumeratedExceptionalAnnulusForcedEdge_of_isExceptional_of_portalSides_of_cyclicallyFiveEdgeConnected
        p0Inside p4Inside h side hcyclic hportal_crosses hcycles
  · by_contra hnoObstruction
    exact hnotSynthesis
      (data.theorem49BoundaryRootSynthesis_of_no_boundaryZeroChainObstruction_of_classifierWitnesses
        emb C₀ colorings hsubset family p0Inside p4Inside side classifier hnoObstruction
        hwitnessRed hwitnessBlue)
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
      data.crossingExtensionFinset_nonempty_or_noncrossingExtensionFinset_nonempty_of_not_classifierControl_of_finsetControl
        emb p0Inside p4Inside side classifier controlEdges hnotControl hcontrol

/-- Generator witness after failed CAP5 synthesis.  This strengthens the finite-bin handoff by
returning the actual next obstruction coordinate: either a one-edge side-crossing walk outside the
classifier output, or a noncrossing algebraic detector coordinate outside the classifier output. -/
theorem forcedEdge_and_extensionWitness_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
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
                e ∈ controlEdges ∧
                  e ∉ classifier.emittedFinset ∧
                    ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                      z e ≠ 0 ∧
                        EdgeCrossesVertexSide G side e ∧
                          side u ∧ ¬ side v ∧
                            p.edges = [(e : Sym2 V)] ∧
                              ∀ f : G.edgeSet, f ∈ classifier.emittedFinset →
                                (f : Sym2 V) ∉ p.edges) ∨
        ∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              (∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) ∧
                ∃ e : G.edgeSet,
                  e ∈ controlEdges ∧
                    e ∉ classifier.emittedFinset ∧
                      ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                        z e ≠ 0 ∧ ¬ EdgeCrossesVertexSide G side e) := by
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
      data.exists_boundaryZeroChain_and_newControlEdge_crossing_or_noncrossing_of_not_classifierControl_of_finsetControl
        emb p0Inside p4Inside side classifier controlEdges hnotControl hcontrol

/-- Finite-bin version of the failed CAP5 synthesis witness.  A failed boundary-root synthesis
attempt, together with a later successful finite control set, returns a forced edge and then an
actual nonzero obstruction coordinate in one of the enumerated extension bins. -/
theorem forcedEdge_and_extensionFinsetWitness_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
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
                            ∀ f : G.edgeSet, f ∈ classifier.emittedFinset →
                              (f : Sym2 V) ∉ p.edges) ∨
        ∃ z : G.edgeSet → Color,
          z ∈ planarBoundaryZeroSubmodule emb ∧
            z ≠ 0 ∧
              (∀ e : G.edgeSet,
                data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                  z e = 0) ∧
                ∃ e : G.edgeSet,
                  e ∈ classifier.noncrossingExtensionFinset controlEdges ∧
                    ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                      z e ≠ 0 ∧ ¬ EdgeCrossesVertexSide G side e) := by
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
      data.exists_boundaryZeroChain_and_extensionFinsetWitness_crossing_or_noncrossing_of_not_classifierControl_of_finsetControl
        emb p0Inside p4Inside side classifier controlEdges hnotControl hcontrol

/-- Failed CAP5 synthesis as a generator step with a decreasing finite worklist.  The returned
crossing or noncrossing bin coordinate is not just diagnostic data: erasing that coordinate from
`remainingControlEdges` strictly decreases the finite search measure. -/
theorem forcedEdge_and_extensionFinsetWitness_with_worklistProgress_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
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
                        ((classifier.remainingControlEdges controlEdges).erase e).card <
                          (classifier.remainingControlEdges controlEdges).card) := by
  rcases data.forcedEdge_and_extensionFinsetWitness_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
      emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue hnotSynthesis with
    ⟨hforced, hbranch⟩
  refine ⟨hforced, ?_⟩
  rcases hbranch with hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, hePredicateOutside,
        hze, hcross, hsideu, hsidev, hpEdges, havoid⟩
    exact Or.inl
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, hePredicateOutside,
        hze, hcross, hsideu, hsidev, hpEdges, havoid,
        classifier.card_erase_remainingControlEdges_lt_of_mem_crossingExtensionFinset
          controlEdges heBin⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze,
        hnotCross⟩
    exact Or.inr
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze, hnotCross,
        classifier.card_erase_remainingControlEdges_lt_of_mem_noncrossingExtensionFinset
          controlEdges heBin⟩

/-- Loop-facing form of the failed CAP5 generator step.  A failed boundary-root synthesis and a
later finite control set expose a concrete unprocessed control edge whose erasure strictly
decreases the finite `remainingControlEdges` measure. -/
theorem exists_remainingControlEdge_with_card_erase_lt_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
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
    ∃ e : G.edgeSet,
      e ∈ classifier.remainingControlEdges controlEdges ∧
        ((classifier.remainingControlEdges controlEdges).erase e).card <
          (classifier.remainingControlEdges controlEdges).card := by
  rcases data.forcedEdge_and_extensionFinsetWitness_with_worklistProgress_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
      emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue hnotSynthesis with
    ⟨_, hbranch⟩
  rcases hbranch with hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, hePredicateOutside,
        hze, hcross, hsideu, hsidev, hpEdges, havoid, hlt⟩
    have he' := (classifier.mem_crossingExtensionFinset_iff controlEdges e).1 heBin
    exact ⟨e,
      (classifier.mem_remainingControlEdges_iff controlEdges e).2 ⟨he'.1, he'.2.1⟩,
      hlt⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze,
        hnotCross, hlt⟩
    have he' := (classifier.mem_noncrossingExtensionFinset_iff controlEdges e).1 heBin
    exact ⟨e,
      (classifier.mem_remainingControlEdges_iff controlEdges e).2 ⟨he'.1, he'.2.1⟩,
      hlt⟩

/-- Strong loop-facing form of the failed CAP5 generator step.  A failed boundary-root synthesis
does not merely expose a fresh remaining control edge: it also preserves the CAP5 forced edge
already emitted by the separator generator.  This is the handoff needed by generator runs that
track both the concrete CAP5 falsifier and the decreasing finite worklist. -/
theorem forcedEdge_and_exists_remainingControlEdge_with_card_erase_lt_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
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
      ∃ e : G.edgeSet,
        e ∈ classifier.remainingControlEdges controlEdges ∧
          ((classifier.remainingControlEdges controlEdges).erase e).card <
            (classifier.remainingControlEdges controlEdges).card := by
  rcases data.forcedEdge_and_extensionFinsetWitness_with_worklistProgress_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
      emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
      hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue hnotSynthesis with
    ⟨hforced, hbranch⟩
  refine ⟨hforced, ?_⟩
  rcases hbranch with hcrossing | hnoncrossing
  · rcases hcrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, u, v, e, p, heBin, hePredicateOutside,
        hze, hcross, hsideu, hsidev, hpEdges, havoid, hlt⟩
    have he' := (classifier.mem_crossingExtensionFinset_iff controlEdges e).1 heBin
    exact ⟨e,
      (classifier.mem_remainingControlEdges_iff controlEdges e).2 ⟨he'.1, he'.2.1⟩,
      hlt⟩
  · rcases hnoncrossing with
      ⟨z, hzBoundary, hzNonzero, hvanish, e, heBin, hePredicateOutside, hze,
        hnotCross, hlt⟩
    have he' := (classifier.mem_noncrossingExtensionFinset_iff controlEdges e).1 heBin
    exact ⟨e,
      (classifier.mem_remainingControlEdges_iff controlEdges e).2 ⟨he'.1, he'.2.1⟩,
      hlt⟩

/-- One-step finite generator runner for failed/successful CAP5 synthesis.  Given the current
Boolean classifier and a later finite control set, either the classifier already closes Theorem 4.9
boundary-root synthesis, or failed synthesis exposes a remaining control edge whose erasure strictly
decreases the named worklist measure. -/
theorem theorem49BoundaryRootSynthesis_or_exists_remainingControlEdge_with_card_erase_lt_of_finsetControl
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
      ∃ e : G.edgeSet,
        e ∈ classifier.remainingControlEdges controlEdges ∧
          ((classifier.remainingControlEdges controlEdges).erase e).card <
            (classifier.remainingControlEdges controlEdges).card := by
  by_cases hclosed : Theorem49BoundaryRootSynthesis emb C₀
  · exact Or.inl hclosed
  · exact Or.inr
      (data.exists_remainingControlEdge_with_card_erase_lt_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
        emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue hclosed)

/-- Strong one-step finite generator runner.  Either the current classifier closes Theorem 4.9
boundary-root synthesis, or the failure branch retains both the CAP5 forced edge emitted by the
separator generator and a fresh remaining control edge whose erasure strictly decreases the named
worklist measure. -/
theorem theorem49BoundaryRootSynthesis_or_forcedEdge_and_exists_remainingControlEdge_with_card_erase_lt_of_finsetControl
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
        ∃ e : G.edgeSet,
          e ∈ classifier.remainingControlEdges controlEdges ∧
            ((classifier.remainingControlEdges controlEdges).erase e).card <
              (classifier.remainingControlEdges controlEdges).card := by
  by_cases hclosed : Theorem49BoundaryRootSynthesis emb C₀
  · exact Or.inl hclosed
  · exact Or.inr
      (data.forcedEdge_and_exists_remainingControlEdge_with_card_erase_lt_of_not_theorem49BoundaryRootSynthesis_of_finsetControl
        emb C₀ colorings hsubset family p0Inside p4Inside h side hcyclic hportal_crosses
        hcycles classifier controlEdges hcontrol hwitnessRed hwitnessBlue hclosed)

/-- Empty geometric-bin specialization of failed CAP5 synthesis.  If a finite checker has proved
that no new crossing control edge exists, then failed synthesis must return a noncrossing
algebraic-detector coordinate. -/
theorem forcedEdge_and_noncrossingExtensionFinsetWitness_of_not_theorem49BoundaryRootSynthesis_of_finsetControl_of_crossingExtensionFinset_eq_empty
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
    (hcrossingEmpty : classifier.crossingExtensionFinset controlEdges = ∅)
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
      ∃ z : G.edgeSet → Color,
        z ∈ planarBoundaryZeroSubmodule emb ∧
          z ≠ 0 ∧
            (∀ e : G.edgeSet,
              data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e →
                z e = 0) ∧
              ∃ e : G.edgeSet,
                e ∈ classifier.noncrossingExtensionFinset controlEdges ∧
                  ¬ data.EnumeratedExceptionalAnnulusForcedEdge p0Inside p4Inside side e ∧
                    z e ≠ 0 ∧ ¬ EdgeCrossesVertexSide G side e := by
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
      data.exists_boundaryZeroChain_and_noncrossingExtensionFinsetWitness_of_not_classifierControl_of_finsetControl_of_crossingExtensionFinset_eq_empty
        emb p0Inside p4Inside side classifier controlEdges hnotControl hcontrol hcrossingEmpty

/-- Empty algebraic-bin specialization of failed CAP5 synthesis.  If a finite checker has proved
that no new noncrossing control coordinate exists, then failed synthesis must return a crossing
one-edge witness for the separator route. -/
theorem forcedEdge_and_crossingExtensionFinsetWitness_of_not_theorem49BoundaryRootSynthesis_of_finsetControl_of_noncrossingExtensionFinset_eq_empty
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
    (hnoncrossingEmpty : classifier.noncrossingExtensionFinset controlEdges = ∅)
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
      ∃ z : G.edgeSet → Color,
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
                            ∀ f : G.edgeSet, f ∈ classifier.emittedFinset →
                              (f : Sym2 V) ∉ p.edges := by
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
      data.exists_boundaryZeroChain_and_crossingExtensionFinsetWitness_of_not_classifierControl_of_finsetControl_of_noncrossingExtensionFinset_eq_empty
        emb p0Inside p4Inside side classifier controlEdges hnotControl hcontrol hnoncrossingEmpty

/-- Finite fixed-point synthesis criterion for a Boolean CAP5 classifier.  If a later finite
control set controls selected boundary-zero chains and both extension bins are empty, then the
current emitted-edge classifier is already sufficient for the Theorem 4.9 boundary-root synthesis
route.  This is the finite checker success endpoint dual to the failed-synthesis witness
generator. -/
theorem theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierExtensionFinsetsEmpty
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
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hcrossingEmpty : classifier.crossingExtensionFinset controlEdges = ∅)
    (hnoncrossingEmpty : classifier.noncrossingExtensionFinset controlEdges = ∅)
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
  theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierControl
    emb C₀ colorings hsubset family p0Inside p4Inside side classifier
    (data.enumeratedExceptionalAnnulusForcedEdgeClassifierControl_of_finsetControl_of_extensionFinsets_eq_empty
      emb p0Inside p4Inside side classifier controlEdges hcontrol hcrossingEmpty hnoncrossingEmpty)
    hwitnessRed hwitnessBlue

/-- Finite fixed-point synthesis criterion stated in the generator's named worklist vocabulary.
If the later finite control set controls selected boundary-zero chains and no unprocessed control
edge remains, the current emitted-edge classifier is already enough for Theorem 4.9 synthesis. -/
theorem theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierRemainingControlEdgesEmpty
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
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hremainingEmpty : classifier.remainingControlEdges controlEdges = ∅)
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
  have hemptyBins :=
    (classifier.remainingControlEdges_eq_empty_iff_extensionFinsets_eq_empty
      controlEdges).1 hremainingEmpty
  exact
    data.theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierExtensionFinsetsEmpty
      emb C₀ colorings hsubset family p0Inside p4Inside side classifier controlEdges
      hcontrol hemptyBins.1 hemptyBins.2 hwitnessRed hwitnessBlue

/-- Failed-synthesis falsification of the finite fixed point.  A CAP5 run cannot simultaneously
have a successful finite-control superset, empty crossing and noncrossing extension bins, and a
failed Theorem 4.9 boundary-root synthesis.  Thus an attempted refutation must expose a nonempty
extension bin rather than stop at an exhausted finite classifier. -/
theorem false_of_not_theorem49BoundaryRootSynthesis_of_finsetControl_of_extensionFinsets_eq_empty
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
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hcrossingEmpty : classifier.crossingExtensionFinset controlEdges = ∅)
    (hnoncrossingEmpty : classifier.noncrossingExtensionFinset controlEdges = ∅)
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
    (data.theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierExtensionFinsetsEmpty
      emb C₀ colorings hsubset family p0Inside p4Inside side classifier controlEdges
      hcontrol hcrossingEmpty hnoncrossingEmpty hwitnessRed hwitnessBlue)

/-- Failed-synthesis falsification of an exhausted named worklist.  A CAP5 generator run cannot
have a successful finite-control superset, no remaining control edges, and a failed Theorem 4.9
boundary-root synthesis.  Thus a failed run must expose a next remaining edge. -/
theorem false_of_not_theorem49BoundaryRootSynthesis_of_finsetControl_of_remainingControlEdges_eq_empty
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
    (controlEdges : Finset G.edgeSet)
    (hcontrol :
      ∀ ⦃z : G.edgeSet → Color⦄,
        z ∈ planarBoundaryZeroSubmodule emb →
        (∀ e ∈ controlEdges, z e = 0) →
          z = 0)
    (hremainingEmpty : classifier.remainingControlEdges controlEdges = ∅)
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
    (data.theorem49BoundaryRootSynthesis_of_enumeratedExceptionalAnnulusForcedEdgeClassifierRemainingControlEdgesEmpty
      emb C₀ colorings hsubset family p0Inside p4Inside side classifier controlEdges
      hcontrol hremainingEmpty hwitnessRed hwitnessBlue)

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

/-- Closed-walk kernel-shell packaging of a concrete finite emitted-edge certificate.  The
certificate identifies the finite list with the enumerated CAP5 forced-edge predicate, while the
rank-style nonzero witness and red/blue probes build the reusable pairing-kernel shell. -/
def closedWalkNeighborhoodPairingKernelShell_of_enumeratedExceptionalAnnulusForcedEdgeFinsetNonzeroWitnesses
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (shell : ClosedWalkExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
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
    ClosedWalkNeighborhoodPairingKernelShell emb :=
  ClosedWalkNeighborhoodPairingKernelShell.of_controlEdgeNonzeroWitnesses
    shell colorings hsubset family emitted
    (by
      intro z hz hzNonzero
      rcases hnonzero hz hzNonzero with ⟨e, hedge, hze⟩
      exact ⟨e, (hcert e).2 hedge, hze⟩)
    (by
      intro e hemitted
      exact hwitnessRed e ((hcert e).1 hemitted))
    (by
      intro e hemitted
      exact hwitnessBlue e ((hcert e).1 hemitted))

/-- Successor-cycle kernel-shell packaging of a concrete finite emitted-edge certificate. -/
def successorCycleNeighborhoodPairingKernelShell_of_enumeratedExceptionalAnnulusForcedEdgeFinsetNonzeroWitnesses
    {data : CAP5TransportedEdgeComponentCoverCore boundaryEdge n}
    [Fintype G.edgeSet]
    {emb : PlaneEmbeddingWithBoundary G}
    (shell : SuccessorCycleExactShell emb)
    (colorings : Set (G.EdgeColoring Color))
    (hsubset : colorings ⊆ G.EdgeKempeClosure shell.tait.coloring)
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
    SuccessorCycleNeighborhoodPairingKernelShell emb :=
  SuccessorCycleNeighborhoodPairingKernelShell.of_controlEdgeNonzeroWitnesses
    shell colorings hsubset family emitted
    (by
      intro z hz hzNonzero
      rcases hnonzero hz hzNonzero with ⟨e, hedge, hze⟩
      exact ⟨e, (hcert e).2 hedge, hze⟩)
    (by
      intro e hemitted
      exact hwitnessRed e ((hcert e).1 hemitted))
    (by
      intro e hemitted
      exact hwitnessBlue e ((hcert e).1 hemitted))

end CAP5TransportedEdgeComponentCoverCore

end Mettapedia.GraphTheory.FourColor
