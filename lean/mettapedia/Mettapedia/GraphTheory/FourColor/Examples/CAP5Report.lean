import Mettapedia.GraphTheory.FourColor.CAP5WitnessGenerator
import Mathlib.Tactic.FinCases

/-!
A small executable-style CAP5 report over a one-edge graph.

The point of this module is not to model an exceptional annulus.  It gives the
finite report generator a concrete graph, boundary-edge interpretation, and side
predicate whose output is forced into the `partialCase` bin for a mathematically
visible reason: one side has no vertices, hence no cycle.
-/

namespace Mettapedia.GraphTheory.FourColor.Examples.CAP5Report

open SimpleGraph

/-- A minimal concrete graph with one edge. -/
def toyGraph : SimpleGraph (Fin 2) :=
  SimpleGraph.fromEdgeSet ({s(0, 1)} : Set (Sym2 (Fin 2)))

/-- The unique edge of `toyGraph`, used as a repeated toy CAP5 boundary edge. -/
def toyEdge01 : toyGraph.edgeSet :=
  ⟨s(0, 1), by simp [toyGraph]⟩

/-- A toy five-slot CAP5 boundary interpretation over the one-edge graph. -/
def toyCAP5BoundaryEdge (_ : Fin 5) : toyGraph.edgeSet :=
  toyEdge01

/-- The trivial side marks every vertex as inside, leaving the outside empty. -/
def toyTrivialSide (_ : Fin 2) : Prop :=
  True

instance toyTrivialSideDecidable (v : Fin 2) :
    Decidable (toyTrivialSide v) := by
  unfold toyTrivialSide
  infer_instance

/-- The empty outside of `toyTrivialSide` cannot support a cycle. -/
theorem toyTrivialSide_no_outside_cycle :
    ¬ HasCycleOnSide toyGraph (fun v => ¬ toyTrivialSide v) := by
  rintro ⟨u, hu, _cycle⟩
  exact hu trivial

/-- Every CAP5 latent for the toy side is missing two-sided cycles. -/
theorem toyCAP5Latent_not_sideCycles
    (latent : CAP5ExceptionalAnnulusGeneratorLatent toyCAP5BoundaryEdge) :
    ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
        toyCAP5BoundaryEdge toyTrivialSide latent).SideCycles := by
  rintro ⟨_insideCycle, outsideCycle⟩
  exact toyTrivialSide_no_outside_cycle outsideCycle

/-- The decidable CAP5 report on the one-edge benchmark. -/
noncomputable def toyCAP5Report :
    CAP5ExceptionalAnnulusGeneratorReport toyCAP5BoundaryEdge toyTrivialSide := by
  classical
  exact CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
    toyCAP5BoundaryEdge toyTrivialSide

/--
The one-edge benchmark lands in the partial bin for every latent, because
the outside side has no cycle.
-/
theorem toyCAP5Report_classify_eq_partialCase
    (latent : CAP5ExceptionalAnnulusGeneratorLatent toyCAP5BoundaryEdge) :
    toyCAP5Report.classify latent = CAP5SeparatorGeneratorStatus.partialCase := by
  classical
  have hnotCycles :
      ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          toyCAP5BoundaryEdge toyTrivialSide latent).SideCycles :=
    toyCAP5Latent_not_sideCycles latent
  by_cases hportal :
      (CAP5ExceptionalAnnulusGeneratorReport.latentNode
        toyCAP5BoundaryEdge toyTrivialSide latent).PortalCrosses
  · by_cases hcycles :
        (CAP5ExceptionalAnnulusGeneratorReport.latentNode
          toyCAP5BoundaryEdge toyTrivialSide latent).SideCycles
    · exact False.elim (hnotCycles hcycles)
    · simp [toyCAP5Report,
        CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks,
        CAP5ExceptionalAnnulusGeneratorNode.Report.ofDecidableChecks,
        hportal, hcycles]
  · simp [toyCAP5Report,
      CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks,
      CAP5ExceptionalAnnulusGeneratorNode.Report.ofDecidableChecks,
      hportal]

/--
The classifier's diagnostic theorem recovers the expected reason for the toy
partial output: a checker prerequisite is absent, here the two-sided cycle data.
-/
theorem toyCAP5Report_missing_checker_evidence
    (latent : CAP5ExceptionalAnnulusGeneratorLatent toyCAP5BoundaryEdge) :
    ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
        toyCAP5BoundaryEdge toyTrivialSide latent).PortalCrosses ∨
    ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
        toyCAP5BoundaryEdge toyTrivialSide latent).SideCycles := by
  exact Or.inr (toyCAP5Latent_not_sideCycles latent)

/-- A six-vertex benchmark: two triangles joined by four candidate CAP5 separator edges. -/
abbrev RealizedV := Fin 6

/-- Two 3-cycles joined by four bridge edges. -/
def realizedGraph : SimpleGraph RealizedV :=
  SimpleGraph.fromEdgeSet
    ({s(0, 1), s(1, 2), s(2, 0), s(3, 4), s(4, 5), s(5, 3),
      s(0, 3), s(0, 4), s(1, 3), s(2, 5)} : Set (Sym2 RealizedV))

/-- The proposed separator side is the first triangle. -/
def realizedSide (v : RealizedV) : Prop :=
  v = 0 ∨ v = 1 ∨ v = 2

instance realizedSideDecidable (v : RealizedV) : Decidable (realizedSide v) := by
  unfold realizedSide
  infer_instance

def r01 : realizedGraph.edgeSet := ⟨s(0, 1), by simp [realizedGraph]⟩
def r12 : realizedGraph.edgeSet := ⟨s(1, 2), by simp [realizedGraph]⟩
def r20 : realizedGraph.edgeSet := ⟨s(2, 0), by simp [realizedGraph]⟩
def r34 : realizedGraph.edgeSet := ⟨s(3, 4), by simp [realizedGraph]⟩
def r45 : realizedGraph.edgeSet := ⟨s(4, 5), by simp [realizedGraph]⟩
def r53 : realizedGraph.edgeSet := ⟨s(5, 3), by simp [realizedGraph]⟩
def r03 : realizedGraph.edgeSet := ⟨s(0, 3), by simp [realizedGraph]⟩
def r04 : realizedGraph.edgeSet := ⟨s(0, 4), by simp [realizedGraph]⟩
def r13 : realizedGraph.edgeSet := ⟨s(1, 3), by simp [realizedGraph]⟩
def r25 : realizedGraph.edgeSet := ⟨s(2, 5), by simp [realizedGraph]⟩

/-- A CAP5 boundary interpretation whose first four slots are exactly the bridge edges. -/
def realizedCAP5BoundaryEdge : Fin 5 → realizedGraph.edgeSet
  | 0 => r03
  | 1 => r04
  | 2 => r13
  | 3 => r25
  | 4 => r01

/-- The latent selecting slots 0, 1, 2, 3 as the separator portal set. -/
def realizedLatent : CAP5ExceptionalAnnulusGeneratorLatent realizedCAP5BoundaryEdge where
  orientation := CAP5ExceptionalBoundarySupportOrientation.redBlue03_redPurple04
  p0Inside := true
  p4Inside := false

def realizedCandidate :
    CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate realizedCAP5BoundaryEdge :=
  realizedLatent.candidate

/-- The latent selecting a three-edge portal set; `r13` will be the outside crossing edge. -/
def forcedLatent : CAP5ExceptionalAnnulusGeneratorLatent realizedCAP5BoundaryEdge where
  orientation := CAP5ExceptionalBoundarySupportOrientation.redBlue03_redPurple04
  p0Inside := true
  p4Inside := true

def forcedCandidate :
    CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate realizedCAP5BoundaryEdge :=
  forcedLatent.candidate

def realizedInsideCycleWalk : realizedGraph.Walk (0 : RealizedV) 0 :=
  Walk.cons' 0 1 0 (by simp [realizedGraph])
    (Walk.cons' 1 2 0 (by simp [realizedGraph])
      (Walk.cons' 2 0 0 (by simp [realizedGraph]) Walk.nil))

theorem realizedInsideCycleWalk_isCycle : realizedInsideCycleWalk.IsCycle := by
  simp [realizedInsideCycleWalk, Walk.cons_isCycle_iff, Walk.cons_isPath_iff]

theorem realizedInsideCycleWalk_support_side :
    ∀ v, v ∈ realizedInsideCycleWalk.support → realizedSide v := by
  intro v hv
  fin_cases v <;> simp [realizedInsideCycleWalk, realizedSide] at hv ⊢

theorem realized_inside_cycle : HasCycleOnSide realizedGraph realizedSide := by
  exact ⟨0, by simp [realizedSide], realizedInsideCycleWalk,
    realizedInsideCycleWalk_isCycle, realizedInsideCycleWalk_support_side⟩

def realizedOutsideCycleWalk : realizedGraph.Walk (3 : RealizedV) 3 :=
  Walk.cons' 3 4 3 (by simp [realizedGraph])
    (Walk.cons' 4 5 3 (by simp [realizedGraph])
      (Walk.cons' 5 3 3 (by simp [realizedGraph]) Walk.nil))

theorem realizedOutsideCycleWalk_isCycle : realizedOutsideCycleWalk.IsCycle := by
  simp [realizedOutsideCycleWalk, Walk.cons_isCycle_iff, Walk.cons_isPath_iff]

theorem realizedOutsideCycleWalk_support_not_side :
    ∀ v, v ∈ realizedOutsideCycleWalk.support → ¬ realizedSide v := by
  intro v hv
  fin_cases v <;> simp [realizedOutsideCycleWalk, realizedSide] at hv ⊢

theorem realized_outside_cycle :
    HasCycleOnSide realizedGraph (fun v => ¬ realizedSide v) := by
  exact ⟨3, by simp [realizedSide], realizedOutsideCycleWalk,
    realizedOutsideCycleWalk_isCycle, realizedOutsideCycleWalk_support_not_side⟩

theorem realized_edge_eq_cases (e : realizedGraph.edgeSet) :
    e = r01 ∨ e = r12 ∨ e = r20 ∨ e = r34 ∨ e = r45 ∨ e = r53 ∨
      e = r03 ∨ e = r04 ∨ e = r13 ∨ e = r25 := by
  have h :
      (e.1 = s(0, 1) ∨ e.1 = s(1, 2) ∨ e.1 = s(2, 0) ∨
        e.1 = s(3, 4) ∨ e.1 = s(4, 5) ∨ e.1 = s(5, 3) ∨
        e.1 = s(0, 3) ∨ e.1 = s(0, 4) ∨ e.1 = s(1, 3) ∨
        e.1 = s(2, 5)) ∧ ¬ e.1.IsDiag := by
    simpa [realizedGraph] using e.2
  rcases h.1 with h01 | h12 | h20 | h34 | h45 | h53 | h03 | h04 | h13 | h25
  · exact Or.inl (Subtype.ext h01)
  · exact Or.inr <| Or.inl (Subtype.ext h12)
  · exact Or.inr <| Or.inr <| Or.inl (Subtype.ext h20)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h34)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h45)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl (Subtype.ext h53)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
      (Subtype.ext h03)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inl (Subtype.ext h04)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inr <| Or.inl (Subtype.ext h13)
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
      Or.inr <| Or.inr <| Or.inr (Subtype.ext h25)

theorem realized_support_simp (e : realizedGraph.edgeSet) :
    e ∈ realizedCandidate.edgeSupport ↔ e = r03 ∨ e = r04 ∨ e = r13 ∨ e = r25 := by
  rcases realized_edge_eq_cases e with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp [realizedCandidate, realizedLatent,
      CAP5ExceptionalAnnulusGeneratorLatent.candidate,
      CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndSideCase,
      CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofPortalCandidate,
      CAP5ExceptionalAnnulusSeparatorPortalCandidate.ofOrientationAndSideCase,
      CAP5ExceptionalAnnulusGeneratorLatent.sideCase, realizedCAP5BoundaryEdge,
      CAP5ExceptionalAnnulusSideCase.ofPortalSides,
      CAP5ExceptionalAnnulusSideCase.separatorPortalSet, r01, r12, r20, r34, r45, r53,
      r03, r04, r13, r25]

theorem forced_support_simp (e : realizedGraph.edgeSet) :
    e ∈ forcedCandidate.edgeSupport ↔ e = r03 ∨ e = r04 ∨ e = r25 := by
  rcases realized_edge_eq_cases e with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl <;>
    simp [forcedCandidate, forcedLatent,
      CAP5ExceptionalAnnulusGeneratorLatent.candidate,
      CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndSideCase,
      CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofPortalCandidate,
      CAP5ExceptionalAnnulusSeparatorPortalCandidate.ofOrientationAndSideCase,
      CAP5ExceptionalAnnulusGeneratorLatent.sideCase, realizedCAP5BoundaryEdge,
      CAP5ExceptionalAnnulusSideCase.ofPortalSides,
      CAP5ExceptionalAnnulusSideCase.separatorPortalSet, r01, r12, r20, r34, r45, r53,
      r03, r04, r13, r25]

theorem realized_r03_crosses : EdgeCrossesVertexSide realizedGraph realizedSide r03 := by
  exact ⟨0, 3, by simp [r03], by simp [r03], by simp [realizedSide], by simp [realizedSide]⟩

theorem realized_r04_crosses : EdgeCrossesVertexSide realizedGraph realizedSide r04 := by
  exact ⟨0, 4, by simp [r04], by simp [r04], by simp [realizedSide], by simp [realizedSide]⟩

theorem realized_r13_crosses : EdgeCrossesVertexSide realizedGraph realizedSide r13 := by
  exact ⟨1, 3, by simp [r13], by simp [r13], by simp [realizedSide], by simp [realizedSide]⟩

theorem realized_r25_crosses : EdgeCrossesVertexSide realizedGraph realizedSide r25 := by
  exact ⟨2, 5, by simp [r25], by simp [r25], by simp [realizedSide], by simp [realizedSide]⟩

theorem realized_nonCandidate_not_crosses (e : realizedGraph.edgeSet)
    (hnot : e ∉ realizedCandidate.edgeSupport) :
    ¬ EdgeCrossesVertexSide realizedGraph realizedSide e := by
  rcases realized_edge_eq_cases e with rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · rintro ⟨u, v, hu, hv, hsu, hsv⟩
    fin_cases u <;> fin_cases v <;> simp [r01, realizedSide] at hu hv hsu hsv
  · rintro ⟨u, v, hu, hv, hsu, hsv⟩
    fin_cases u <;> fin_cases v <;> simp [r12, realizedSide] at hu hv hsu hsv
  · rintro ⟨u, v, hu, hv, hsu, hsv⟩
    fin_cases u <;> fin_cases v <;> simp [r20, realizedSide] at hu hv hsu hsv
  · rintro ⟨u, v, hu, hv, hsu, hsv⟩
    fin_cases u <;> fin_cases v <;> simp [r34, realizedSide] at hu hv hsu hsv
  · rintro ⟨u, v, hu, hv, hsu, hsv⟩
    fin_cases u <;> fin_cases v <;> simp [r45, realizedSide] at hu hv hsu hsv
  · rintro ⟨u, v, hu, hv, hsu, hsv⟩
    fin_cases u <;> fin_cases v <;> simp [r53, realizedSide] at hu hv hsu hsv
  · exact False.elim (hnot ((realized_support_simp r03).2 (Or.inl rfl)))
  · exact False.elim (hnot ((realized_support_simp r04).2 (Or.inr <| Or.inl rfl)))
  · exact False.elim (hnot ((realized_support_simp r13).2 (Or.inr <| Or.inr <| Or.inl rfl)))
  · exact False.elim (hnot ((realized_support_simp r25).2 (Or.inr <| Or.inr <| Or.inr rfl)))

theorem realized_portalCrosses :
    (CAP5ExceptionalAnnulusGeneratorReport.latentNode
      realizedCAP5BoundaryEdge realizedSide realizedLatent).PortalCrosses := by
  intro i hi
  fin_cases i <;>
    simp [CAP5ExceptionalAnnulusGeneratorReport.latentNode,
      CAP5ExceptionalAnnulusGeneratorNode.candidate, realizedLatent,
      CAP5ExceptionalAnnulusGeneratorLatent.candidate,
      CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndSideCase,
      CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofPortalCandidate,
      CAP5ExceptionalAnnulusSeparatorPortalCandidate.ofOrientationAndSideCase,
      CAP5ExceptionalAnnulusGeneratorLatent.sideCase, realizedCAP5BoundaryEdge,
      CAP5ExceptionalAnnulusSideCase.ofPortalSides,
      CAP5ExceptionalAnnulusSideCase.separatorPortalSet] at hi ⊢ <;>
    first
    | exact realized_r03_crosses
    | exact realized_r04_crosses
    | exact realized_r13_crosses
    | exact realized_r25_crosses

theorem realized_sideCycles :
    (CAP5ExceptionalAnnulusGeneratorReport.latentNode
      realizedCAP5BoundaryEdge realizedSide realizedLatent).SideCycles := by
  exact ⟨realized_inside_cycle, realized_outside_cycle⟩

def realizedCutData :
    realizedCandidate.CyclicEdgeCutRealizationData (G := realizedGraph) :=
  realizedCandidate.cyclicEdgeCutRealizationData_of_edge_crossing_classification
    realizedSide
    (by
      intro e he
      rcases (realized_support_simp e).1 he with rfl | rfl | rfl | rfl
      · exact realized_r03_crosses
      · exact realized_r04_crosses
      · exact realized_r13_crosses
      · exact realized_r25_crosses)
    realized_nonCandidate_not_crosses
    realized_inside_cycle
    realized_outside_cycle

theorem realized_realizedSeparator :
    (CAP5ExceptionalAnnulusGeneratorReport.latentNode
      realizedCAP5BoundaryEdge realizedSide realizedLatent).RealizedSeparator := by
  exact ⟨realizedCutData⟩

theorem forced_portalCrosses :
    (CAP5ExceptionalAnnulusGeneratorReport.latentNode
      realizedCAP5BoundaryEdge realizedSide forcedLatent).PortalCrosses := by
  intro i hi
  fin_cases i <;>
    simp [CAP5ExceptionalAnnulusGeneratorReport.latentNode,
      CAP5ExceptionalAnnulusGeneratorNode.candidate, forcedLatent,
      CAP5ExceptionalAnnulusGeneratorLatent.candidate,
      CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndSideCase,
      CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofPortalCandidate,
      CAP5ExceptionalAnnulusSeparatorPortalCandidate.ofOrientationAndSideCase,
      CAP5ExceptionalAnnulusGeneratorLatent.sideCase, realizedCAP5BoundaryEdge,
      CAP5ExceptionalAnnulusSideCase.ofPortalSides,
      CAP5ExceptionalAnnulusSideCase.separatorPortalSet] at hi ⊢ <;>
    first
    | exact realized_r03_crosses
    | exact realized_r04_crosses
    | exact realized_r25_crosses

theorem forced_sideCycles :
    (CAP5ExceptionalAnnulusGeneratorReport.latentNode
      realizedCAP5BoundaryEdge realizedSide forcedLatent).SideCycles := by
  exact ⟨realized_inside_cycle, realized_outside_cycle⟩

def forcedCounterexampleWalk : realizedGraph.Walk (1 : RealizedV) 3 :=
  Walk.cons' 1 3 3 (by simp [realizedGraph]) Walk.nil

theorem forcedCandidate_r13_not_mem : r13 ∉ forcedCandidate.edgeSupport := by
  rw [forced_support_simp]
  simp [r13, r03, r04, r25]

theorem forcedCandidate_r01_not_mem : r01 ∉ forcedCandidate.edgeSupport := by
  rw [forced_support_simp]
  simp [r01, r03, r04, r25]

theorem forcedCandidate_r03_mem : r03 ∈ forcedCandidate.edgeSupport := by
  exact (forced_support_simp r03).2 (Or.inl rfl)

theorem forced_node_forcedCounterexampleEdge_r13 :
    (CAP5ExceptionalAnnulusGeneratorReport.latentNode
      realizedCAP5BoundaryEdge realizedSide forcedLatent).ForcedCounterexampleEdge r13 := by
  refine ⟨1, 3, forcedCounterexampleWalk, forcedCandidate_r13_not_mem,
    ?_, ?_, ?_, ?_⟩
  · unfold realizedSide
    exact Or.inr (Or.inl rfl)
  · unfold realizedSide
    rintro (h | h | h) <;> cases h
  · simp [forcedCounterexampleWalk, r13]
  · intro i hi hiEdges
    fin_cases i <;>
      simp [CAP5ExceptionalAnnulusGeneratorReport.latentNode,
        CAP5ExceptionalAnnulusGeneratorNode.candidate, forcedLatent,
        CAP5ExceptionalAnnulusGeneratorLatent.candidate,
        CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndSideCase,
        CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofPortalCandidate,
        CAP5ExceptionalAnnulusSeparatorPortalCandidate.ofOrientationAndSideCase,
        CAP5ExceptionalAnnulusGeneratorLatent.sideCase, realizedCAP5BoundaryEdge,
        CAP5ExceptionalAnnulusSideCase.ofPortalSides,
        CAP5ExceptionalAnnulusSideCase.separatorPortalSet,
        forcedCounterexampleWalk, r03, r04, r25] at hi hiEdges

theorem forced_realizedSeparator_false :
    ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
      realizedCAP5BoundaryEdge realizedSide forcedLatent).RealizedSeparator := by
  rintro ⟨realization⟩
  have hnot01Cross :
      ¬ EdgeCrossesVertexSide realizedGraph realization.side r01 := by
    intro hcross
    exact forcedCandidate_r01_not_mem ((realization.hcut_eq r01).2 hcross)
  have hnot13Cross :
      ¬ EdgeCrossesVertexSide realizedGraph realization.side r13 := by
    intro hcross
    exact forcedCandidate_r13_not_mem ((realization.hcut_eq r13).2 hcross)
  have h01 :
      realization.side (0 : RealizedV) ↔ realization.side 1 :=
    (not_edgeCrossesVertexSide_iff_forall_side_iff realizedGraph realization.side r01).1
      hnot01Cross 0 1 (by simp [r01]) (by simp [r01])
  have h13 :
      realization.side (1 : RealizedV) ↔ realization.side 3 :=
    (not_edgeCrossesVertexSide_iff_forall_side_iff realizedGraph realization.side r13).1
      hnot13Cross 1 3 (by simp [r13]) (by simp [r13])
  have h03Same : realization.side (0 : RealizedV) ↔ realization.side 3 := h01.trans h13
  have hnot03Cross :
      ¬ EdgeCrossesVertexSide realizedGraph realization.side r03 := by
    rw [not_edgeCrossesVertexSide_iff_forall_side_iff]
    intro u v hu hv
    fin_cases u <;> fin_cases v <;> simp [r03] at hu hv ⊢
    · exact h03Same
    · exact h03Same.symm
  exact hnot03Cross ((realization.hcut_eq r03).1 forcedCandidate_r03_mem)

/-- The three-edge latent has a concrete outside crossing edge and hence a forced witness. -/
theorem forced_node_forcedCounterexample :
    (CAP5ExceptionalAnnulusGeneratorReport.latentNode
      realizedCAP5BoundaryEdge realizedSide forcedLatent).ForcedCounterexample := by
  exact ⟨r13, forced_node_forcedCounterexampleEdge_r13⟩

/-- The decidable CAP5 report on the two-triangle realized-separator benchmark. -/
noncomputable def realizedCAP5Report :
    CAP5ExceptionalAnnulusGeneratorReport realizedCAP5BoundaryEdge realizedSide := by
  classical
  exact CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks
    realizedCAP5BoundaryEdge realizedSide

/--
The two-triangle benchmark lands in the realized-separator bin: the chosen four bridge
edges are exactly the cyclic edge cut between the two cycles.
-/
theorem realizedCAP5Report_classify_eq_realizedSeparator :
    realizedCAP5Report.classify realizedLatent =
      CAP5SeparatorGeneratorStatus.realizedSeparator := by
  classical
  simp [realizedCAP5Report,
    CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks,
    CAP5ExceptionalAnnulusGeneratorNode.Report.ofDecidableChecks,
    realized_portalCrosses, realized_sideCycles, realized_realizedSeparator]

/--
The same graph also contains a forced-counterexample latent: the three-edge candidate cannot be
a cyclic cut, because the cycle `0-3-1-0` meets it in exactly one edge, while `r13` is the
concrete outside crossing edge.
-/
theorem realizedCAP5Report_classify_forcedLatent_eq_forcedCounterexample :
    realizedCAP5Report.classify forcedLatent =
      CAP5SeparatorGeneratorStatus.forcedCounterexample := by
  classical
  have hnotRealized :
      ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
        realizedCAP5BoundaryEdge realizedSide forcedLatent).RealizedSeparator :=
    forced_realizedSeparator_false
  simp [realizedCAP5Report,
    CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks,
    CAP5ExceptionalAnnulusGeneratorNode.Report.ofDecidableChecks,
    forced_portalCrosses, forced_sideCycles, hnotRealized]

/--
The realized-separator bin is a genuine cyclic-five-connectivity refutation for this finite
sample, so it is a calibration case for the CAP5 witness generator rather than evidence for a
minimal-counterexample route.
-/
theorem realizedCAP5Report_not_cyclicallyFiveEdgeConnected :
    ¬ CyclicallyFiveEdgeConnected realizedGraph := by
  classical
  exact
    CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks_classify_eq_realizedSeparator_implies_not_cyclicallyFiveEdgeConnected
      realizedCAP5BoundaryEdge realizedSide realizedLatent
      realizedCAP5Report_classify_eq_realizedSeparator

end Mettapedia.GraphTheory.FourColor.Examples.CAP5Report
