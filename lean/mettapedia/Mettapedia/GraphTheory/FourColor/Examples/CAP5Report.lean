import Mettapedia.GraphTheory.FourColor.CAP5WitnessGenerator

/-!
A small executable-style CAP5 report over a one-edge graph.

The point of this module is not to model an exceptional annulus.  It gives the
finite report generator a concrete graph, boundary-edge interpretation, and side
predicate whose output is forced into the `partialCase` bin for a mathematically
visible reason: one side has no vertices, hence no cycle.
-/

namespace Mettapedia.GraphTheory.FourColor.Examples.CAP5Report

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

end Mettapedia.GraphTheory.FourColor.Examples.CAP5Report
