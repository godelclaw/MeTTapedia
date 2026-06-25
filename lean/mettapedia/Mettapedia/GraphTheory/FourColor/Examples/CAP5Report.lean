import Mettapedia.GraphTheory.FourColor.CAP5WitnessGenerator
import Mettapedia.GraphTheory.FourColor.Curriculum.PathXor
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

/-- Split diagnostic for the toy sample: the primitive missing ingredient is the outside cycle. -/
theorem toyCAP5Report_missingCheckerEvidence
    (latent : CAP5ExceptionalAnnulusGeneratorLatent toyCAP5BoundaryEdge) :
    (toyCAP5Report.node latent).MissingCheckerEvidence := by
  exact Or.inr (Or.inr toyTrivialSide_no_outside_cycle)

/-- Every latent of the one-edge toy sample is reported partial. -/
theorem toyCAP5Report_partialLatents_eq_all :
    toyCAP5Report.partialLatents =
      CAP5ExceptionalAnnulusGeneratorLatent.all toyCAP5BoundaryEdge := by
  unfold CAP5ExceptionalAnnulusGeneratorReport.partialLatents
  apply List.filter_eq_self.2
  intro latent _hmem
  simp [toyCAP5Report_classify_eq_partialCase latent]

/-- The one-edge toy sample puts all latents in the primitive missing-evidence frontier. -/
theorem toyCAP5Report_missingCheckerEvidenceLatents_eq_all :
    toyCAP5Report.missingCheckerEvidenceLatents =
      CAP5ExceptionalAnnulusGeneratorLatent.all toyCAP5BoundaryEdge := by
  rw [← toyCAP5Report_partialLatents_eq_all]
  exact toyCAP5Report.partialLatents_eq_missingCheckerEvidenceLatents.symm

@[simp]
theorem toyCAP5Report_partialLatents_length :
    toyCAP5Report.partialLatents.length = 16 := by
  rw [toyCAP5Report_partialLatents_eq_all]
  simp

@[simp]
theorem toyCAP5Report_missingCheckerEvidenceLatents_length :
    toyCAP5Report.missingCheckerEvidenceLatents.length = 16 := by
  rw [toyCAP5Report_missingCheckerEvidenceLatents_eq_all]
  simp

/-- The one-edge toy sample has no complete checker latents. -/
theorem toyCAP5Report_completeCheckerLatents_eq_nil :
    toyCAP5Report.completeCheckerLatents = [] := by
  apply List.eq_nil_iff_forall_not_mem.2
  intro latent hmem
  have hcomplete := (toyCAP5Report.mem_completeCheckerLatents_iff).1 hmem
  exact hcomplete.2 (toyCAP5Report_missingCheckerEvidence latent)

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

/-- Red/blue component support using boundary slots `{0, 3}` in the realized benchmark. -/
def realizedRedBlueEdge₁ : Finset realizedGraph.edgeSet := {r03, r25}

/-- Red/blue component support using boundary slots `{1, 2}` in the realized benchmark. -/
def realizedRedBlueEdge₂ : Finset realizedGraph.edgeSet := {r04, r13}

/-- Red/purple component support using boundary slots `{0, 4}` in the realized benchmark. -/
def realizedRedPurpleEdge₁ : Finset realizedGraph.edgeSet := {r03, r01}

/-- Red/purple component support using boundary slots `{1, 3}` in the realized benchmark. -/
def realizedRedPurpleEdge₂ : Finset realizedGraph.edgeSet := {r04, r25}

theorem realizedRedBlueEdge₁_boundarySupport :
    cap5BoundarySupportOfEdges realizedCAP5BoundaryEdge realizedRedBlueEdge₁ =
      ({0, 3} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5BoundarySupportOfEdges, realizedRedBlueEdge₁,
      realizedCAP5BoundaryEdge, r01, r03, r04, r13, r25]

theorem realizedRedBlueEdge₂_boundarySupport :
    cap5BoundarySupportOfEdges realizedCAP5BoundaryEdge realizedRedBlueEdge₂ =
      ({1, 2} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5BoundarySupportOfEdges, realizedRedBlueEdge₂,
      realizedCAP5BoundaryEdge, r01, r03, r04, r13, r25]

theorem realizedRedPurpleEdge₁_boundarySupport :
    cap5BoundarySupportOfEdges realizedCAP5BoundaryEdge realizedRedPurpleEdge₁ =
      ({0, 4} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5BoundarySupportOfEdges, realizedRedPurpleEdge₁,
      realizedCAP5BoundaryEdge, r01, r03, r04, r13, r25]

theorem realizedRedPurpleEdge₂_boundarySupport :
    cap5BoundarySupportOfEdges realizedCAP5BoundaryEdge realizedRedPurpleEdge₂ =
      ({1, 3} : Finset (Fin 5)) := by
  ext i
  fin_cases i <;>
    simp [cap5BoundarySupportOfEdges, realizedRedPurpleEdge₂,
      realizedCAP5BoundaryEdge, r01, r03, r04, r13, r25]

/--
Transported exceptional component-cover data for the two-triangle benchmark.  This packages the
finite CAP5 support pairing that the witness generator samples against the concrete graph.
-/
def realizedCAP5Core :
    CAP5TransportedEdgeComponentCoverCore realizedCAP5BoundaryEdge 0 where
  redBlueEdge₁ := realizedRedBlueEdge₁
  redBlueEdge₂ := realizedRedBlueEdge₂
  redPurpleEdge₁ := realizedRedPurpleEdge₁
  redPurpleEdge₂ := realizedRedPurpleEdge₂
  redBlue₁ := {0, 3}
  redBlue₂ := {1, 2}
  redPurple₁ := {0, 4}
  redPurple₂ := {1, 3}
  hredBlue₁ := by
    simpa [cap5RotateBoundarySupportN] using realizedRedBlueEdge₁_boundarySupport
  hredBlue₂ := by
    simpa [cap5RotateBoundarySupportN] using realizedRedBlueEdge₂_boundarySupport
  hredPurple₁ := by
    simpa [cap5RotateBoundarySupportN] using realizedRedPurpleEdge₁_boundarySupport
  hredPurple₂ := by
    simpa [cap5RotateBoundarySupportN] using realizedRedPurpleEdge₂_boundarySupport
  hredBlue := by
    rw [CAP5BadRedBlueComponentCover]
    refine ⟨by simp, by simp, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro i hi₁ hi₂
      fin_cases i <;> simp at hi₁ hi₂
    · ext i
      fin_cases i <;> simp
  hredPurple := by
    rw [CAP5BadRedPurpleComponentCover]
    refine ⟨by simp, by simp, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro i hi₁ hi₂
      fin_cases i <;> simp at hi₁ hi₂
    · ext i
      fin_cases i <;> simp

theorem realizedCAP5Core_isExceptional :
    realizedCAP5Core.IsExceptional := by
  change CAP5BadExceptionalPairingPattern
    ({0, 3} : Finset (Fin 5)) ({1, 2} : Finset (Fin 5))
      ({0, 4} : Finset (Fin 5)) ({1, 3} : Finset (Fin 5))
  rw [CAP5BadExceptionalPairingPattern, CAP5BadRedBlueExceptionalPairing,
    CAP5BadRedPurpleExceptionalPairing]
  exact ⟨Or.inl ⟨rfl, rfl⟩, Or.inl ⟨rfl, rfl⟩⟩

theorem realizedCAP5Core_realizes_redBlue03_redPurple04 :
    realizedCAP5Core.RealizesExceptionalBoundarySupportOrientation
      CAP5ExceptionalBoundarySupportOrientation.redBlue03_redPurple04 := by
  simp [CAP5TransportedEdgeComponentCoverCore.RealizesExceptionalBoundarySupportOrientation,
    realizedCAP5Core, cap5RotateBoundarySupportN,
    realizedRedBlueEdge₁_boundarySupport, realizedRedBlueEdge₂_boundarySupport,
    realizedRedPurpleEdge₁_boundarySupport, realizedRedPurpleEdge₂_boundarySupport]

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

/-- The realized benchmark latent is complete: it is not in the missing-checker frontier. -/
theorem realized_latent_not_missingCheckerEvidence :
    ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
      realizedCAP5BoundaryEdge realizedSide realizedLatent).MissingCheckerEvidence := by
  exact
    ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
      realizedCAP5BoundaryEdge realizedSide realizedLatent)
      |>.not_missingCheckerEvidence_iff_complete).2
      ⟨realized_portalCrosses, realized_sideCycles⟩

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

/-- The four-edge latent realizes the separator on the concrete side used by the benchmark. -/
theorem realized_realizedSeparatorOnSide :
    (CAP5ExceptionalAnnulusGeneratorReport.latentNode
      realizedCAP5BoundaryEdge realizedSide realizedLatent).RealizedSeparatorOnSide := by
  exact ⟨realizedCutData, rfl⟩

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

/-- The forced benchmark latent is also complete; its negative result is a real forced edge,
not missing checker evidence. -/
theorem forced_latent_not_missingCheckerEvidence :
    ¬ (CAP5ExceptionalAnnulusGeneratorReport.latentNode
      realizedCAP5BoundaryEdge realizedSide forcedLatent).MissingCheckerEvidence := by
  exact
    ((CAP5ExceptionalAnnulusGeneratorReport.latentNode
      realizedCAP5BoundaryEdge realizedSide forcedLatent)
      |>.not_missingCheckerEvidence_iff_complete).2
      ⟨forced_portalCrosses, forced_sideCycles⟩

def forcedCounterexampleWalk : realizedGraph.Walk (1 : RealizedV) 3 :=
  Walk.cons' 1 3 3 (by simp [realizedGraph]) Walk.nil

/-- The return walk witnessing that the candidate edge `r03` is not a true cut edge:
`0` reaches `3` through the non-candidate edges `r01` and `r13`. -/
def forcedCandidateBypassWalk : realizedGraph.Walk (0 : RealizedV) 3 :=
  Walk.cons' 0 1 3 (by simp [realizedGraph])
    (Walk.cons' 1 3 3 (by simp [realizedGraph]) Walk.nil)

theorem forcedCandidate_r13_not_mem : r13 ∉ forcedCandidate.edgeSupport := by
  rw [forced_support_simp]
  simp [r13, r03, r04, r25]

theorem forcedCandidate_r01_not_mem : r01 ∉ forcedCandidate.edgeSupport := by
  rw [forced_support_simp]
  simp [r01, r03, r04, r25]

theorem forcedCandidate_r03_mem : r03 ∈ forcedCandidate.edgeSupport := by
  exact (forced_support_simp r03).2 (Or.inl rfl)

/-- The bypass walk avoids the whole forced candidate support. -/
theorem forcedCandidateBypassWalk_avoids_forcedCandidate :
    ∀ e : realizedGraph.edgeSet, e ∈ forcedCandidate.edgeSupport →
      (e : Sym2 RealizedV) ∉ forcedCandidateBypassWalk.edges := by
  intro e he heEdges
  rcases (forced_support_simp e).1 he with rfl | rfl | rfl
  · simp [forcedCandidateBypassWalk, r03] at heEdges
  · simp [forcedCandidateBypassWalk, r04] at heEdges
  · simp [forcedCandidateBypassWalk, r25] at heEdges

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
  exact
    (CAP5ExceptionalAnnulusGeneratorReport.latentNode
      realizedCAP5BoundaryEdge realizedSide forcedLatent)
      |>.not_realizedSeparator_of_candidate_edge_bypass
    (u := (0 : RealizedV)) (v := 3) (e := r03)
    (by simp [r03]) forcedCandidate_r03_mem forcedCandidateBypassWalk
    forcedCandidateBypassWalk_avoids_forcedCandidate

/-- The three-edge latent has a concrete outside crossing edge and hence a forced witness. -/
theorem forced_node_forcedCounterexample :
    (CAP5ExceptionalAnnulusGeneratorReport.latentNode
      realizedCAP5BoundaryEdge realizedSide forcedLatent).ForcedCounterexample := by
  exact ⟨r13, forced_node_forcedCounterexampleEdge_r13⟩

/--
The transported component-cover view of the benchmark puts the four-edge portal choice in the
same-side realized bin.  This is the finite hold-sample for the CAP5 witness generator.
-/
theorem realizedCAP5Core_sameSideRealization :
    realizedCAP5Core.EnumeratedExceptionalAnnulusSameSideRealization
      true false realizedSide := by
  refine ⟨realizedLatent, CAP5ExceptionalAnnulusGeneratorLatent.mem_all realizedLatent,
    rfl, rfl, realizedCAP5Core_realizes_redBlue03_redPurple04, ?_⟩
  simpa [CAP5ExceptionalAnnulusGeneratorReport.latentNode] using
    realized_realizedSeparatorOnSide

/--
The same transported component-cover sample puts the three-edge portal choice in the forced-edge
bin, emitting the concrete outside crossing edge `r13`.
-/
theorem realizedCAP5Core_forcedEdge_r13 :
    realizedCAP5Core.EnumeratedExceptionalAnnulusForcedEdge
      true true realizedSide r13 := by
  refine ⟨forcedLatent, CAP5ExceptionalAnnulusGeneratorLatent.mem_all forcedLatent,
    rfl, rfl, realizedCAP5Core_realizes_redBlue03_redPurple04, ?_⟩
  simpa [CAP5ExceptionalAnnulusGeneratorReport.latentNode] using
    forced_node_forcedCounterexampleEdge_r13

/--
Data-level calibration for the CAP5 proof-as-generator pass: one transported exceptional
component-cover sample has both a same-side realization and a concrete emitted forced edge,
depending on the finite portal-side latent.
-/
theorem realizedCAP5Core_generator_boundary_mixed :
    realizedCAP5Core.EnumeratedExceptionalAnnulusSameSideRealization true false realizedSide ∧
      realizedCAP5Core.EnumeratedExceptionalAnnulusForcedEdge true true realizedSide r13 ∧
        EdgeCrossesVertexSide realizedGraph realizedSide r13 :=
  ⟨realizedCAP5Core_sameSideRealization,
    realizedCAP5Core_forcedEdge_r13, realized_r13_crosses⟩

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
  exact
    CAP5ExceptionalAnnulusGeneratorReport.ofDecidableChecks_classify_eq_forcedCounterexample_of_complete_of_candidate_edge_bypass
        realizedCAP5BoundaryEdge realizedSide forcedLatent
        forced_portalCrosses forced_sideCycles
        (u := (0 : RealizedV)) (v := 3) (e := r03)
        (by simp [r03]) forcedCandidate_r03_mem forcedCandidateBypassWalk
        forcedCandidateBypassWalk_avoids_forcedCandidate

/--
The concrete finite report exposes the four-edge latent in the realized-separator bin.
This is the positive side of the two-triangle calibration sample.
-/
theorem realizedCAP5Report_realizedLatent_mem_realizedSeparatorLatents :
    realizedLatent ∈ realizedCAP5Report.realizedSeparatorLatents := by
  exact (realizedCAP5Report.mem_realizedSeparatorLatents_iff).2
    ⟨CAP5ExceptionalAnnulusGeneratorLatent.mem_all realizedLatent,
      realizedCAP5Report_classify_eq_realizedSeparator⟩

/--
The same finite report exposes the three-edge latent in the forced-counterexample bin.
This is the negative side of the sample: one graph carries both report outcomes.
-/
theorem realizedCAP5Report_forcedLatent_mem_forcedCounterexampleLatents :
    forcedLatent ∈ realizedCAP5Report.forcedCounterexampleLatents := by
  exact (realizedCAP5Report.mem_forcedCounterexampleLatents_iff).2
    ⟨CAP5ExceptionalAnnulusGeneratorLatent.mem_all forcedLatent,
      realizedCAP5Report_classify_forcedLatent_eq_forcedCounterexample⟩

/-- The named realized benchmark latent is not a partial run. -/
theorem realizedCAP5Report_realizedLatent_not_mem_partialLatents :
    realizedLatent ∉ realizedCAP5Report.partialLatents :=
  realizedCAP5Report.not_mem_partialLatents_of_mem_realizedSeparatorLatents
    realizedCAP5Report_realizedLatent_mem_realizedSeparatorLatents

/-- The named forced benchmark latent is not a partial run. -/
theorem realizedCAP5Report_forcedLatent_not_mem_partialLatents :
    forcedLatent ∉ realizedCAP5Report.partialLatents :=
  realizedCAP5Report.not_mem_partialLatents_of_mem_forcedCounterexampleLatents
    realizedCAP5Report_forcedLatent_mem_forcedCounterexampleLatents

/-- The mixed two-triangle sample's two named latents are complete checker runs. -/
theorem realizedCAP5Report_named_latents_not_missingCheckerEvidence :
    ¬ (realizedCAP5Report.node realizedLatent).MissingCheckerEvidence ∧
      ¬ (realizedCAP5Report.node forcedLatent).MissingCheckerEvidence := by
  constructor
  · simpa [CAP5ExceptionalAnnulusGeneratorReport.node,
      CAP5ExceptionalAnnulusGeneratorReport.latentNode] using
      realized_latent_not_missingCheckerEvidence
  · simpa [CAP5ExceptionalAnnulusGeneratorReport.node,
      CAP5ExceptionalAnnulusGeneratorReport.latentNode] using
      forced_latent_not_missingCheckerEvidence

/-- The realized benchmark latent is a complete checker run in the report frontier. -/
theorem realizedCAP5Report_realizedLatent_mem_completeCheckerLatents :
    realizedLatent ∈ realizedCAP5Report.completeCheckerLatents := by
  exact (realizedCAP5Report.mem_completeCheckerLatents_iff).2
    ⟨CAP5ExceptionalAnnulusGeneratorLatent.mem_all realizedLatent,
      realizedCAP5Report_named_latents_not_missingCheckerEvidence.1⟩

/-- The forced benchmark latent is also a complete checker run, not a missing-evidence case. -/
theorem realizedCAP5Report_forcedLatent_mem_completeCheckerLatents :
    forcedLatent ∈ realizedCAP5Report.completeCheckerLatents := by
  exact (realizedCAP5Report.mem_completeCheckerLatents_iff).2
    ⟨CAP5ExceptionalAnnulusGeneratorLatent.mem_all forcedLatent,
      realizedCAP5Report_named_latents_not_missingCheckerEvidence.2⟩

/-- The two named two-triangle latents calibrate the complete-checker frontier. -/
theorem realizedCAP5Report_named_latents_mem_completeCheckerLatents :
    realizedLatent ∈ realizedCAP5Report.completeCheckerLatents ∧
      forcedLatent ∈ realizedCAP5Report.completeCheckerLatents :=
  ⟨realizedCAP5Report_realizedLatent_mem_completeCheckerLatents,
    realizedCAP5Report_forcedLatent_mem_completeCheckerLatents⟩

/-- The realized-bin membership projects back to the certified cyclic-cut payload. -/
theorem realizedCAP5Report_realizedLatent_payload :
    (realizedCAP5Report.node realizedLatent).RealizedSeparator :=
  realizedCAP5Report.realizedSeparator_of_mem_realizedSeparatorLatents
    realizedCAP5Report_realizedLatent_mem_realizedSeparatorLatents

/-- The realized-bin latent also carries same-side realization data for the report side. -/
theorem realizedCAP5Report_realizedLatent_payload_onSide :
    (realizedCAP5Report.node realizedLatent).RealizedSeparatorOnSide := by
  simpa [CAP5ExceptionalAnnulusGeneratorReport.node,
    CAP5ExceptionalAnnulusGeneratorReport.latentNode] using realized_realizedSeparatorOnSide

/-- The forced-bin membership projects back to the certified outside-crossing payload. -/
theorem realizedCAP5Report_forcedLatent_payload :
    (realizedCAP5Report.node forcedLatent).ForcedCounterexample :=
  realizedCAP5Report.forcedCounterexample_of_mem_forcedCounterexampleLatents
    realizedCAP5Report_forcedLatent_mem_forcedCounterexampleLatents

/--
The forced latent refutes realization of its generated support on the concrete report side.
This is the exact same-side obstruction exposed by the finite checker.
-/
theorem realizedCAP5Report_forcedLatent_not_realizedSeparatorOnSide :
    ¬ (realizedCAP5Report.node forcedLatent).RealizedSeparatorOnSide :=
  realizedCAP5Report.not_realizedSeparatorOnSide_of_mem_forcedCounterexampleLatents
    realizedCAP5Report_forcedLatent_mem_forcedCounterexampleLatents

/--
Same-side calibration boundary for the two-triangle report: the four-edge latent realizes the
report side, while the three-edge latent is forced out of same-side realization.
-/
theorem realizedCAP5Report_sameSide_boundary :
    (realizedCAP5Report.node realizedLatent).RealizedSeparatorOnSide ∧
      ¬ (realizedCAP5Report.node forcedLatent).RealizedSeparatorOnSide :=
  ⟨realizedCAP5Report_realizedLatent_payload_onSide,
    realizedCAP5Report_forcedLatent_not_realizedSeparatorOnSide⟩

/--
The forced bin in the concrete report exposes an actual side-crossing emitted edge, not just a
status label.
-/
theorem realizedCAP5Report_forcedLatent_exists_crossing_edge :
    ∃ e : realizedGraph.edgeSet,
      (realizedCAP5Report.node forcedLatent).ForcedCounterexampleEdge e ∧
        EdgeCrossesVertexSide realizedGraph realizedSide e :=
  realizedCAP5Report.exists_forcedCounterexampleEdge_crossing_of_mem_forcedCounterexampleLatents
    realizedCAP5Report_forcedLatent_mem_forcedCounterexampleLatents

/--
The forced bin in this calibration sample emits the exact bridge `r13`, not merely an
unidentified crossing edge.
-/
theorem realizedCAP5Report_forcedLatent_exact_crossing_edge :
    (realizedCAP5Report.node forcedLatent).ForcedCounterexampleEdge r13 ∧
      EdgeCrossesVertexSide realizedGraph realizedSide r13 := by
  constructor
  · simpa [CAP5ExceptionalAnnulusGeneratorReport.node,
      CAP5ExceptionalAnnulusGeneratorReport.latentNode] using
      forced_node_forcedCounterexampleEdge_r13
  · exact realized_r13_crosses

/--
The forced bin also exposes the one-edge avoiding-walk witness emitted by the checker.
-/
theorem realizedCAP5Report_forcedLatent_exists_oneEdge_crossing_walk :
    ∃ u v : RealizedV, ∃ e : realizedGraph.edgeSet, ∃ p : realizedGraph.Walk u v,
      e ∉ (realizedCAP5Report.node forcedLatent).candidate.edgeSupport ∧
        realizedSide u ∧ ¬ realizedSide v ∧
          p.edges = [(e : Sym2 RealizedV)] ∧
            (∀ i : Fin 5,
              i ∈ (realizedCAP5Report.node forcedLatent).candidate.portalCandidate.portalSet →
                ((realizedCAP5BoundaryEdge i : realizedGraph.edgeSet) : Sym2 RealizedV) ∉
                  p.edges) ∧
              EdgeCrossesVertexSide realizedGraph realizedSide e :=
  realizedCAP5Report.exists_oneEdge_forcedCounterexampleWalk_of_mem_forcedCounterexampleLatents
    realizedCAP5Report_forcedLatent_mem_forcedCounterexampleLatents

/--
The report-level forced branch is witnessed by the specific one-edge walk over `r13`.  This is
the concrete finite-generator payload behind the existential one-edge-walk theorem above.
-/
theorem realizedCAP5Report_forcedLatent_exact_oneEdge_crossing_walk :
    r13 ∉ (realizedCAP5Report.node forcedLatent).candidate.edgeSupport ∧
      realizedSide (1 : RealizedV) ∧ ¬ realizedSide (3 : RealizedV) ∧
        forcedCounterexampleWalk.edges = [(r13 : Sym2 RealizedV)] ∧
          (∀ i : Fin 5,
            i ∈ (realizedCAP5Report.node forcedLatent).candidate.portalCandidate.portalSet →
              ((realizedCAP5BoundaryEdge i : realizedGraph.edgeSet) : Sym2 RealizedV) ∉
                forcedCounterexampleWalk.edges) ∧
            EdgeCrossesVertexSide realizedGraph realizedSide r13 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, realized_r13_crosses⟩
  · change r13 ∉ forcedCandidate.edgeSupport
    exact forcedCandidate_r13_not_mem
  · simp [realizedSide]
  · simp [realizedSide]
  · simp [forcedCounterexampleWalk, r13]
  · intro i hi hiEdges
    fin_cases i <;>
      simp [CAP5ExceptionalAnnulusGeneratorReport.node,
        CAP5ExceptionalAnnulusGeneratorReport.latentNode,
        CAP5ExceptionalAnnulusGeneratorNode.candidate, forcedLatent,
        CAP5ExceptionalAnnulusGeneratorLatent.candidate,
        CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofOrientationAndSideCase,
        CAP5ExceptionalAnnulusBoundaryEdgeSupportCandidate.ofPortalCandidate,
        CAP5ExceptionalAnnulusSeparatorPortalCandidate.ofOrientationAndSideCase,
        CAP5ExceptionalAnnulusGeneratorLatent.sideCase, realizedCAP5BoundaryEdge,
        CAP5ExceptionalAnnulusSideCase.ofPortalSides,
        CAP5ExceptionalAnnulusSideCase.separatorPortalSet,
        forcedCounterexampleWalk, r03, r04, r25] at hi hiEdges

/--
The exact one-edge forced walk contributes exactly the `𝔽₂` weight of the emitted edge.  This
is the algebraic readout of the concrete generator witness.
-/
theorem realizedCAP5Report_forcedLatent_exact_oneEdge_pathXor
    (weight : Sym2 RealizedV → F2) :
    Curriculum.pathXor weight forcedCounterexampleWalk.edges =
      weight (r13 : Sym2 RealizedV) := by
  simp [Curriculum.pathXor, forcedCounterexampleWalk, r13]

/--
If a finite algebraic detector marks the emitted crossing edge, the concrete forced walk has a
nonzero `𝔽₂` path-xor signal.
-/
theorem realizedCAP5Report_forcedLatent_exact_oneEdge_pathXor_ne_zero
    (weight : Sym2 RealizedV → F2)
    (hweight : weight (r13 : Sym2 RealizedV) = 1) :
    Curriculum.pathXor weight forcedCounterexampleWalk.edges ≠ 0 := by
  simpa [forcedCounterexampleWalk, r13] using
    Curriculum.pathXor_singleton_ne_zero weight (e := (r13 : Sym2 RealizedV)) hweight

/--
For the exact one-edge forced walk, a finite detector has nonzero path-xor precisely when it
marks the emitted crossing edge `r13`.
-/
theorem realizedCAP5Report_forcedLatent_exact_oneEdge_pathXor_ne_zero_iff
    (weight : Sym2 RealizedV → F2) :
    Curriculum.pathXor weight forcedCounterexampleWalk.edges ≠ 0 ↔
      weight (r13 : Sym2 RealizedV) ≠ 0 := by
  simp [forcedCounterexampleWalk, r13, Curriculum.pathXor]

/--
A nonzero finite detector signal on the forced walk exposes an actual marked edge in that walk.
This is the extraction direction needed by cocycle-style falsification passes.
-/
theorem realizedCAP5Report_forcedLatent_exists_edge_weight_ne_zero_of_pathXor_ne_zero
    (weight : Sym2 RealizedV → F2)
    (hxor : Curriculum.pathXor weight forcedCounterexampleWalk.edges ≠ 0) :
    ∃ e, e ∈ forcedCounterexampleWalk.edges ∧ weight e ≠ 0 :=
  Curriculum.exists_mem_weight_ne_zero_of_pathXor_ne_zero weight hxor

/--
For the exact one-edge forced walk, exposing a marked path edge is equivalent to marking the
emitted crossing edge `r13` itself.
-/
theorem realizedCAP5Report_forcedLatent_exists_edge_weight_ne_zero_iff
    (weight : Sym2 RealizedV → F2) :
    (∃ e, e ∈ forcedCounterexampleWalk.edges ∧ weight e ≠ 0) ↔
      weight (r13 : Sym2 RealizedV) ≠ 0 := by
  simp [forcedCounterexampleWalk, r13]

/--
For the exact forced branch, a nonzero finite detector signal exposes the graph obstruction it
detected: the emitted edge is outside the forced candidate support, crosses the side predicate,
lies on the forced walk, and carries nonzero detector weight.
-/
theorem realizedCAP5Report_forcedLatent_pathXor_ne_zero_exposes_outside_crossing_edge
    (weight : Sym2 RealizedV → F2)
    (hxor : Curriculum.pathXor weight forcedCounterexampleWalk.edges ≠ 0) :
    ∃ e : realizedGraph.edgeSet,
      e ∉ (realizedCAP5Report.node forcedLatent).candidate.edgeSupport ∧
        EdgeCrossesVertexSide realizedGraph realizedSide e ∧
          (e : Sym2 RealizedV) ∈ forcedCounterexampleWalk.edges ∧
            weight (e : Sym2 RealizedV) ≠ 0 := by
  refine ⟨r13, ?_, realized_r13_crosses, ?_, ?_⟩
  · change r13 ∉ forcedCandidate.edgeSupport
    exact forcedCandidate_r13_not_mem
  · simp [forcedCounterexampleWalk, r13]
  · exact (realizedCAP5Report_forcedLatent_exact_oneEdge_pathXor_ne_zero_iff weight).1 hxor

/--
For the forced branch, a nonzero finite detector signal is not merely an algebraic marker:
it packages the concrete bypass refutation of the generated separator together with the
outside crossing edge detected on the forced walk.
-/
theorem realizedCAP5Report_forcedLatent_detector_refutes_separator
    (weight : Sym2 RealizedV → F2)
    (hxor : Curriculum.pathXor weight forcedCounterexampleWalk.edges ≠ 0) :
    ¬ (realizedCAP5Report.node forcedLatent).RealizedSeparator ∧
      ∃ e : realizedGraph.edgeSet,
        e ∉ (realizedCAP5Report.node forcedLatent).candidate.edgeSupport ∧
          EdgeCrossesVertexSide realizedGraph realizedSide e ∧
            (e : Sym2 RealizedV) ∈ forcedCounterexampleWalk.edges ∧
              weight (e : Sym2 RealizedV) ≠ 0 := by
  have hnot :
      ¬ (realizedCAP5Report.node forcedLatent).RealizedSeparator := by
    simpa [CAP5ExceptionalAnnulusGeneratorReport.node,
      CAP5ExceptionalAnnulusGeneratorReport.latentNode] using
      forced_realizedSeparator_false
  exact ⟨hnot,
    realizedCAP5Report_forcedLatent_pathXor_ne_zero_exposes_outside_crossing_edge
      weight hxor⟩

/-- Concrete finite `𝔽₂` detector marking exactly the emitted forced crossing edge `r13`. -/
def realizedForcedEdgeDetector (e : Sym2 RealizedV) : F2 :=
  if e = (r13 : Sym2 RealizedV) then 1 else 0

@[simp]
theorem realizedForcedEdgeDetector_r13 :
    realizedForcedEdgeDetector (r13 : Sym2 RealizedV) = 1 := by
  simp [realizedForcedEdgeDetector]

/--
The concrete detector sees the exact one-edge forced walk as a nonzero `𝔽₂` signal.
This is the finite algebraic readout of the emitted CAP5 crossing edge.
-/
theorem realizedCAP5Report_forcedLatent_concrete_detector_pathXor :
    Curriculum.pathXor realizedForcedEdgeDetector forcedCounterexampleWalk.edges = 1 := by
  simpa [realizedForcedEdgeDetector] using
    realizedCAP5Report_forcedLatent_exact_oneEdge_pathXor realizedForcedEdgeDetector

theorem realizedCAP5Report_forcedLatent_concrete_detector_pathXor_ne_zero :
    Curriculum.pathXor realizedForcedEdgeDetector forcedCounterexampleWalk.edges ≠ 0 := by
  rw [realizedCAP5Report_forcedLatent_concrete_detector_pathXor]
  decide

/--
Concrete algebraic calibration of the forced branch: the benchmark's emitted edge is outside the
generated support, crosses the proposed side, lies on the one-edge forced walk, and is marked by
the finite `𝔽₂` detector.
-/
theorem realizedCAP5Report_forcedLatent_concrete_detector_refutes_separator :
    ¬ (realizedCAP5Report.node forcedLatent).RealizedSeparator ∧
      r13 ∉ (realizedCAP5Report.node forcedLatent).candidate.edgeSupport ∧
        EdgeCrossesVertexSide realizedGraph realizedSide r13 ∧
          (r13 : Sym2 RealizedV) ∈ forcedCounterexampleWalk.edges ∧
            realizedForcedEdgeDetector (r13 : Sym2 RealizedV) = 1 := by
  have hnot :
      ¬ (realizedCAP5Report.node forcedLatent).RealizedSeparator := by
    simpa [CAP5ExceptionalAnnulusGeneratorReport.node,
      CAP5ExceptionalAnnulusGeneratorReport.latentNode] using
      forced_realizedSeparator_false
  exact ⟨hnot, by
      change r13 ∉ forcedCandidate.edgeSupport
      exact forcedCandidate_r13_not_mem,
    realized_r13_crosses, by simp [forcedCounterexampleWalk, r13],
    realizedForcedEdgeDetector_r13⟩

/--
The two-triangle benchmark has a genuinely mixed finite-generator output: one latent certifies
a small cyclic separator and another certifies a forced counterexample.
-/
theorem realizedCAP5Report_has_mixed_bins :
    (∃ latent, latent ∈ realizedCAP5Report.realizedSeparatorLatents) ∧
      (∃ latent, latent ∈ realizedCAP5Report.forcedCounterexampleLatents) :=
  ⟨⟨realizedLatent,
      realizedCAP5Report_realizedLatent_mem_realizedSeparatorLatents⟩,
    ⟨forcedLatent,
      realizedCAP5Report_forcedLatent_mem_forcedCounterexampleLatents⟩⟩

/--
The realized-separator bin is a genuine cyclic-five-connectivity refutation for this finite
sample, so it is a calibration case for the CAP5 witness generator rather than evidence for a
minimal-counterexample route.
-/
theorem realizedCAP5Report_not_cyclicallyFiveEdgeConnected :
    ¬ CyclicallyFiveEdgeConnected realizedGraph := by
  exact realizedCAP5Report.not_cyclicallyFiveEdgeConnected_of_mem_realizedSeparatorLatents
    realizedCAP5Report_realizedLatent_mem_realizedSeparatorLatents

/--
Combined calibration payload for the finite generator: the same two-triangle sample has a
realized separator refuting cyclic five-edge-connectivity, and its forced branch emits the
concrete outside crossing edge `r13`.
-/
theorem realizedCAP5Report_generator_boundary_payload :
    (realizedCAP5Report.node realizedLatent).RealizedSeparatorOnSide ∧
      ¬ CyclicallyFiveEdgeConnected realizedGraph ∧
        (realizedCAP5Report.node forcedLatent).ForcedCounterexampleEdge r13 ∧
          EdgeCrossesVertexSide realizedGraph realizedSide r13 := by
  exact ⟨realizedCAP5Report_realizedLatent_payload_onSide,
    realizedCAP5Report_not_cyclicallyFiveEdgeConnected,
    realizedCAP5Report_forcedLatent_exact_crossing_edge.1,
    realizedCAP5Report_forcedLatent_exact_crossing_edge.2⟩

end Mettapedia.GraphTheory.FourColor.Examples.CAP5Report
