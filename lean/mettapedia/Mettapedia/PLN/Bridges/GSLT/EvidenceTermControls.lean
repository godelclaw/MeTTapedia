import Mettapedia.PLN.Core.CompletePLN
import Mettapedia.PLN.Bridges.GSLT.EvidenceTermComposition
import Mettapedia.PLN.Bridges.GSLT.LedgerTermControls

/-!
# Concrete recursive evidence settings

The likelihood fixture has two genuinely informative reports that are
independent conditional on either hypothesis value. Reusing a noisy report
fails that contract. A finite population fixture separately checks deduction
with a compound source query and explicit marginal/conditional requests.
-/

namespace Mettapedia.PLN.Bridges.GSLT.EvidenceTermControls

open Mettapedia.GSLT.LanguageDef.FirstOrderCalculus
open scoped BigOperators
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.GSLT.LanguageDef.SemanticSettings
open Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusModule
open Mettapedia.PLN.Bridges.GSLT.EvidenceTermComposition
open Mettapedia.PLN.Bridges.GSLT.EvidenceTermSettings
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceContracts

namespace ReportFixture

def hypothesis : Pattern := app "hypothesis" []
def first : Pattern := app "first-report" []
def second : Pattern := app "second-report" []

private theorem sum_eight [fin : Fintype (Fin 8)] (f : Fin 8 → ℝ) :
    (∑ x, f x) = f 0 + (f 1 + (f 2 + (f 3 + (f 4 + (f 5 + (f 6 + f 7)))))) := by
  have canonical : fin = Fin.fintype 8 := Subsingleton.elim _ _
  cases canonical
  change (∑ x : Fin 8, f x) = _
  simp [Fin.sum_univ_succ]

noncomputable def weights : Mettapedia.InformationTheory.Prob (Fin 8) :=
  ⟨![9/32, 1/32, 3/32, 3/32, 3/32, 3/32, 1/32, 9/32], by
    constructor
    · intro i; fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_succ]⟩

noncomputable def model : Reports.Model where
  Ω := Fin 8
  weight := weights
  atomQuery _ world := worldToAssignment 3 world 0
  atomReport name world := if name = first then worldToAssignment 3 world 1
    else worldToAssignment 3 world 2
  atomSummary _ := ⟨3/4, 1/4⟩

def context : List Pattern :=
  [reportLikelihoods hypothesis first, reportLikelihoods hypothesis second,
    reportHolds (app "reports" [hypothesis, first, second])]

def proof : RawOpenProof :=
  .node ⟨⟨"fuse"⟩, [hypothesis, first, second]⟩ [.premise 0, .premise 1, .premise 2]

theorem proof_checks : checkOpenRaw evidenceCalculusValidated context
    (reportLikelihoods hypothesis (app "fuse" [first, second])) proof = true := by decide +kernel

theorem context_holds : ∀ premise ∈ context, model.holds premise := by
  dsimp only [model]
  norm_num [context, Reports.Model.holds, reportLikelihoods, reportHolds, app,
    Reports.Model.query, Reports.Model.report, Reports.Model.summary,
    Reports.Model.supported, Reports.Model.likelihoods, Reports.Model.likelihood,
    Mettapedia.ProbabilityTheory.FiniteConditionalStability.conditional,
    Mettapedia.ProbabilityTheory.FiniteEventMass.mass, weights, hypothesis, first, second,
    worldToAssignment, Fin.sum_univ_succ, Evidence.ext_iff]
  simp only [String.reduceEq, ↓reduceIte]
  simp only [sum_eight, Matrix.cons_val]
  norm_num

theorem fused_likelihoods : model.summary (app "fuse" [first, second]) = ⟨9/16, 1/16⟩ := by
  dsimp only [model, first, second, app]
  simp only [Reports.Model.summary]
  norm_num [first, second, fuse, Evidence.ext_iff]

theorem duplicate_noisy_report_not_independent :
    ¬ model.holds (reportHolds (app "reports" [hypothesis, first, first])) := by
  dsimp only [model]
  norm_num [Reports.Model.holds, reportHolds, app, Reports.Model.query, Reports.Model.report,
    Reports.Model.likelihood, Mettapedia.ProbabilityTheory.FiniteConditionalStability.conditional,
    Mettapedia.ProbabilityTheory.FiniteEventMass.mass, weights, hypothesis, first,
    worldToAssignment, Fin.sum_univ_succ]
  simp only [sum_eight, Matrix.cons_val]
  norm_num

end ReportFixture

namespace PopulationFixture

def a : Pattern := app "a" []
def b : Pattern := app "b" []
def c : Pattern := app "c" []
def source : Pattern := app "not" [app "not" [a]]
def s1 : Pattern := app "source-middle" []
def s2 : Pattern := app "middle-target" []
def s3 : Pattern := app "middle-marginal" []
def s4 : Pattern := app "target-marginal" []

noncomputable def model : Population.Model where
  W := Bool × Bool
  population := {(false, false), (false, true), (true, false), (true, true)}
  atomQuery name world := if name = a then world.1 else world.2
  atomValue name := if name = s2 then 1 else 1/2

def context : List Pattern :=
  [populationReadout (app "conditional" [source, b]) s1,
    populationReadout (app "conditional" [b, c]) s2,
    populationReadout (app "probability" [b]) s3,
    populationReadout (app "probability" [c]) s4,
    populationHolds (app "screens" [source, b, c])]

def proof : RawOpenProof :=
  .node ⟨⟨"deduce"⟩, [source, b, c, s1, s2, s3, s4]⟩
    [.premise 0, .premise 1, .premise 2, .premise 3, .premise 4]

def conclusion : Pattern := populationReadout (app "conditional" [source, c])
  (app "deduction" [s1, s2, s3, s4])

theorem proof_checks : checkOpenRaw evidenceCalculusValidated context conclusion proof = true := by
  decide +kernel

theorem context_holds : ∀ premise ∈ context, model.holds premise := by
  dsimp only [model]
  norm_num [context, Population.Model.holds, populationReadout, populationHolds,
    Population.Model.value, Population.Model.query, Population.Model.freq,
    app, source, a, b, c, s1, s2, s3, s4, count, Multiset.countP_cons,
    Bool.and_eq_true, Evidence.ext_iff ]
  simp only [String.reduceEq, ↓reduceIte]
  simp only [← Multiset.cons_zero, Multiset.countP_cons, Multiset.countP_zero]
  norm_num

def ambiguousContext : List Pattern := context.set 2 (populationReadout b s3)

theorem bare_query_cannot_feed_marginal_slot :
    checkOpenRaw evidenceCalculusValidated ambiguousContext conclusion proof = false := by
  decide +kernel

end PopulationFixture

namespace SampleFixture

def a : Pattern := app "left-query" []
def b : Pattern := app "right-query" []
def first : Pattern := app "first-sample" []
def second : Pattern := app "second-sample" []

def model : Samples.Model where
  W := Bool × Bool
  atomQuery name world := if name = a then world.1 else world.2
  atomBag _ := {(true, true), (false, false)}
  atomSummary _ := ⟨1, 1⟩
  combine first second := (first.1, second.2)

def context : List Pattern :=
  [sampleCounts a first, sampleCounts b second, sampleHolds (app "independent" [a, b])]

def proof : RawOpenProof :=
  .node ⟨⟨"conjoin-independent"⟩, [a, b, first, second]⟩ [.premise 0, .premise 1, .premise 2]

theorem proof_checks : checkOpenRaw evidenceCalculusValidated context
    (sampleCounts (app "and" [a, b]) (app "pair" [first, second])) proof = true := by decide +kernel

theorem context_holds : ∀ premise ∈ context, model.holds premise := by
  dsimp only [model]
  norm_num [context, Samples.Model.holds, sampleCounts, sampleHolds,
    Samples.Model.query, Samples.Model.summary, Samples.Model.bag, app, a, b,
    first, second, ofSamples, sampleEvidence, Evidence.positive, Evidence.negative,
    Evidence.ext_iff]
  simp [String.reduceEq]

end SampleFixture

noncomputable def models : Models
  | .ledger => LedgerTermControls.model
  | .samples => SampleFixture.model
  | .reports => ReportFixture.model
  | .population => PopulationFixture.model

/-- The full nine-rule checker establishes the report conclusion in a
concrete family of independently interpreted models. -/
theorem report_derivation_semantic :
    meaning models (reportLikelihoods ReportFixture.hypothesis
      (app "fuse" [ReportFixture.first, ReportFixture.second])) := by
  apply checked_proof_sound models ReportFixture.context _ ReportFixture.proof ReportFixture.proof_checks
  intro premise member
  have truePremises := ReportFixture.context_holds
  simp only [ReportFixture.context, List.mem_cons, List.not_mem_nil, or_false] at member
  simp only [ReportFixture.context, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at truePremises
  rcases member with rfl | rfl | rfl
  all_goals
    dsimp only [meaning, combinedHolds, settingOf, reading, models,
      reportLikelihoods, reportHolds, app]
    first | exact truePremises.1 | exact truePremises.2.1 | exact truePremises.2.2

theorem sample_derivation_semantic : meaning models (sampleCounts (app "and" [SampleFixture.a, SampleFixture.b])
      (app "pair" [SampleFixture.first, SampleFixture.second])) := by
  apply checked_proof_sound models SampleFixture.context _ SampleFixture.proof SampleFixture.proof_checks
  intro premise member
  have truePremises := SampleFixture.context_holds
  simp only [SampleFixture.context, List.mem_cons, List.not_mem_nil, or_false] at member
  simp only [SampleFixture.context, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at truePremises
  rcases member with rfl | rfl | rfl
  all_goals
    dsimp only [meaning, combinedHolds, settingOf, reading, models, sampleCounts, sampleHolds, app]
    first | exact truePremises.1 | exact truePremises.2.1 | exact truePremises.2.2

theorem population_derivation_semantic : meaning models (PopulationFixture.conclusion) := by
  apply checked_proof_sound models PopulationFixture.context _ PopulationFixture.proof PopulationFixture.proof_checks
  intro premise member
  have truePremises := PopulationFixture.context_holds
  simp only [PopulationFixture.context, List.mem_cons, List.not_mem_nil, or_false] at member
  simp only [PopulationFixture.context, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at truePremises
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals
    dsimp only [meaning, combinedHolds, settingOf, reading, models, populationReadout, populationHolds, app]
    first | exact truePremises.1 | exact truePremises.2.1 | exact truePremises.2.2.1 | exact truePremises.2.2.2.1 | exact truePremises.2.2.2.2

end Mettapedia.PLN.Bridges.GSLT.EvidenceTermControls
