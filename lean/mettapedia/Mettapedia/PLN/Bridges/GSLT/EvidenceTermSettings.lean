import Mettapedia.PLN.Bridges.GSLT.LedgerTermSemantics
import Mettapedia.ProbabilityTheory.FiniteConditionalStability

/-!
# Recursive sample, likelihood and population settings

Each setting has its own world carrier, atomic interpretations and summary
operations. Compound arguments are interpreted recursively. In particular,
observation-count multiplication, likelihood fusion and population readouts
do not become the same operation because their values have similar shapes.

A likelihood judgment additionally requires that both the hypothesis and its
negation have positive mass. Population requests distinguish `probability q`
from `conditional a b`, independently of the syntax of the queries themselves.
-/

namespace Mettapedia.PLN.Bridges.GSLT.EvidenceTermSettings

open Mettapedia.GSLT.LanguageDef.FirstOrderCalculus
open scoped BigOperators
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusModule
open Mettapedia.PLN.WorldModel.EvidenceContracts
open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceSpaces.Evidence
open Mettapedia.ProbabilityTheory.FiniteEventMass

namespace Samples

structure Model where
  W : Type
  atomQuery : Pattern → W → Bool
  atomBag : Pattern → Multiset W
  atomSummary : Pattern → Evidence ℕ
  combine : W → W → W

namespace Model

def query (model : Model) : Pattern → model.W → Bool :=
  BooleanTermSemantics.eval model.atomQuery

def bag (model : Model) : Pattern → Multiset model.W
  | .apply "pair" [a, b] => (model.bag a ×ˢ model.bag b).map fun p => model.combine p.1 p.2
  | other => model.atomBag other
termination_by pattern => sizeOf pattern

def summary (model : Model) : Pattern → Evidence ℕ
  | .apply "pair" [a, b] => model.summary a * model.summary b
  | other => model.atomSummary other
termination_by pattern => sizeOf pattern

@[simp] theorem bag_atom (model : Model) (name : String) :
    model.bag (.apply name []) = model.atomBag (.apply name []) := by
  rw [bag]; simp

@[simp] theorem summary_atom (model : Model) (name : String) :
    model.summary (.apply name []) = model.atomSummary (.apply name []) := by
  rw [summary]; simp

def holds (model : Model) : Pattern → Prop
  | .apply "SampleCounts" [q, e] => model.summary e = ofSamples (model.query q) (model.bag e)
  | .apply "SampleHolds" [.apply "independent" [a, b]] =>
      ∀ w v, model.query a (model.combine w v) = model.query a w ∧
        model.query b (model.combine w v) = model.query b v
  | _ => False

theorem conjoin (model : Model) (a b first second : Pattern)
    (firstExact : model.holds (sampleCounts a first))
    (secondExact : model.holds (sampleCounts b second))
    (separable : model.holds (sampleHolds (app "independent" [a, b]))) :
    model.holds (sampleCounts (app "and" [a, b]) (app "pair" [first, second])) := by
  simp only [holds, sampleCounts, sampleHolds, app, query, bag, summary,
    BooleanTermSemantics.eval_and] at *
  rw [firstExact, secondExact, ← ofSamples_product]
  simp only [ofSamples, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro pair _
  simp only [Function.comp_apply, sampleEvidence, (separable pair.1 pair.2).1,
    (separable pair.1 pair.2).2]

end Model
end Samples

namespace Reports

structure Model where
  Ω : Type
  [fin : Fintype Ω]
  weight : Mettapedia.InformationTheory.Prob Ω
  atomQuery : Pattern → Ω → Bool
  atomReport : Pattern → Ω → Bool
  atomSummary : Pattern → Evidence ℝ

attribute [instance] Model.fin

namespace Model

def query (model : Model) : Pattern → model.Ω → Bool :=
  BooleanTermSemantics.eval model.atomQuery

def report (model : Model) : Pattern → model.Ω → Bool
  | .apply "fuse" [a, b] => fun world => model.report a world && model.report b world
  | other => model.atomReport other
termination_by pattern => sizeOf pattern

noncomputable def summary (model : Model) : Pattern → Evidence ℝ
  | .apply "fuse" [a, b] => Mettapedia.PLN.WorldModel.EvidenceContracts.fuse (model.summary a) (model.summary b)
  | other => model.atomSummary other
termination_by pattern => sizeOf pattern

@[simp] theorem report_atom (model : Model) (name : String) :
    model.report (.apply name []) = model.atomReport (.apply name []) := by
  rw [report]; simp

@[simp] theorem summary_atom (model : Model) (name : String) :
    model.summary (.apply name []) = model.atomSummary (.apply name []) := by
  rw [summary]; simp

noncomputable def likelihood (model : Model) (hypothesis evidence : model.Ω → Bool) : ℝ :=
  Mettapedia.ProbabilityTheory.FiniteConditionalStability.conditional model.weight.1 evidence hypothesis

noncomputable def likelihoods (model : Model) (hypothesis evidence : model.Ω → Bool) : Evidence ℝ :=
  ⟨model.likelihood hypothesis evidence, model.likelihood (fun world => !hypothesis world) evidence⟩

def supported (model : Model) (hypothesis : model.Ω → Bool) : Prop :=
  0 < mass model.weight.1 hypothesis ∧ 0 < mass model.weight.1 (fun world => !hypothesis world)

noncomputable def holds (model : Model) : Pattern → Prop
  | .apply "ReportLikelihoods" [q, e] =>
      model.supported (model.query q) ∧ model.summary e = model.likelihoods (model.query q) (model.report e)
  | .apply "ReportHolds" [.apply "reports" [q, a, b]] =>
      model.likelihood (model.query q) (fun world => model.report a world && model.report b world) =
          model.likelihood (model.query q) (model.report a) *
            model.likelihood (model.query q) (model.report b) ∧
        model.likelihood (fun world => !model.query q world)
            (fun world => model.report a world && model.report b world) =
          model.likelihood (fun world => !model.query q world) (model.report a) *
            model.likelihood (fun world => !model.query q world) (model.report b)
  | _ => False

theorem fuse (model : Model) (q first second : Pattern)
    (firstExact : model.holds (reportLikelihoods q first))
    (secondExact : model.holds (reportLikelihoods q second))
    (independent : model.holds (reportHolds (app "reports" [q, first, second]))) :
    model.holds (reportLikelihoods q (app "fuse" [first, second])) := by
  simp only [holds, reportLikelihoods, reportHolds, app, report, summary] at *
  refine ⟨firstExact.1, ?_⟩
  rw [firstExact.2, secondExact.2]
  apply Evidence.ext
  · exact independent.1.symm
  · exact independent.2.symm

end Model
end Reports

namespace Population

structure Model where
  W : Type
  population : Multiset W
  atomQuery : Pattern → W → Bool
  atomValue : Pattern → ℝ

namespace Model

def query (model : Model) : Pattern → model.W → Bool :=
  BooleanTermSemantics.eval model.atomQuery

abbrev freq (model : Model) (predicate : model.W → Bool) : ℕ := count model.population predicate

noncomputable def value (model : Model) : Pattern → ℝ
  | .apply "deduction" [s1, s2, s3, s4] =>
      model.value s1 * model.value s2 + (1 - model.value s1) *
        Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.complementConditionalFromMarginal
          (model.value s3) (model.value s4) (model.value s2)
  | other => model.atomValue other
termination_by pattern => sizeOf pattern

@[simp] theorem value_atom (model : Model) (name : String) :
    model.value (.apply name []) = model.atomValue (.apply name []) := by
  rw [value]; simp

noncomputable def holds (model : Model) : Pattern → Prop
  | .apply "PopulationReadout" [.apply "conditional" [a, b], v] =>
      model.value v = (model.freq (fun w => model.query a w && model.query b w) : ℝ) /
        model.freq (model.query a)
  | .apply "PopulationReadout" [.apply "probability" [q], v] =>
      model.value v = (model.freq (model.query q) : ℝ) / Multiset.card model.population
  | .apply "PopulationHolds" [.apply "screens" [a, b, c]] =>
      model.freq (fun w => model.query a w && model.query b w && model.query c w) *
          model.freq (model.query b) =
        model.freq (fun w => model.query a w && model.query b w) *
          model.freq (fun w => model.query b w && model.query c w) ∧
      model.freq (fun w => model.query a w && !model.query b w && model.query c w) *
          model.freq (fun w => !model.query b w) =
        model.freq (fun w => model.query a w && !model.query b w) *
          model.freq (fun w => !model.query b w && model.query c w) ∧
      model.freq (model.query a) ≠ 0 ∧ model.freq (model.query b) ≠ 0 ∧
        model.freq (fun w => !model.query b w) ≠ 0
  | _ => False

theorem deduce (model : Model) (a b c s1 s2 s3 s4 : Pattern)
    (sourceMiddle : model.holds (populationReadout (app "conditional" [a, b]) s1))
    (middleTarget : model.holds (populationReadout (app "conditional" [b, c]) s2))
    (middle : model.holds (populationReadout (app "probability" [b]) s3))
    (target : model.holds (populationReadout (app "probability" [c]) s4))
    (screening : model.holds (populationHolds (app "screens" [a, b, c]))) :
    model.holds (populationReadout (app "conditional" [a, c])
      (app "deduction" [s1, s2, s3, s4])) := by
  simp only [holds, populationReadout, populationHolds, app, value] at *
  rw [sourceMiddle, middleTarget, middle, target]
  exact (deduction_exact_of_screening model.population (model.query a) (model.query b)
    (model.query c) screening.1 screening.2.1 screening.2.2.1 screening.2.2.2.1
      screening.2.2.2.2).symm

end Model
end Population

end Mettapedia.PLN.Bridges.GSLT.EvidenceTermSettings
