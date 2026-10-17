import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDerivation
import Mettapedia.PLN.WorldModel.WorldModelCalculus
import Mettapedia.PLN.WorldModel.WorldModelITV
import Mettapedia.PLN.WorldModel.WorldModelITVHypercube
import Mettapedia.PLN.Bridges.Languages.PLNWMOSLFBridge
import Mettapedia.PLN.Bridges.Languages.PLNWMOSLFBridgeITV
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNXiRuleRegistry
import Mettapedia.PLN.Bridges.ProbabilityTheory.PLNXiCarrierScreening
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNXiDerivedBNRules
import Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel
import Mettapedia.KR.ConceptGeometry.Bridges.UniversalAI.IntensionalInheritanceSolomonoffBridge
import Mettapedia.KR.ConceptGeometry.Examples.IntensionalInheritanceAllCanary
import Mettapedia.KR.ConceptGeometry.Bridges.ProbabilityTheory.EmpiricalIntensionalFactorGraphBridge
import Mettapedia.KR.ConceptOntology.Formation
import Mettapedia.KR.ConceptOntology.CredalFormation
import Mettapedia.KR.ConceptOntology.MizarBenchmark
import Mettapedia.KR.ConceptOntology.MizarBenchmarkEndpoint
import Mettapedia.KR.ConceptOntology.ConstructionBaseInheritance
import Mettapedia.KR.ConceptOntology.ConstructionBaseInference
import Mettapedia.KR.ConceptOntology.ConstructionBasePredictive
import Mettapedia.KR.ConceptOntology.ConstructionBasePredictiveITV
import Mettapedia.PLN.Bridges.KR.ConceptClosure.FormedConceptFixpointClosureBridge
import Mettapedia.Logic.FormedConceptOntologyGrowthBridge
import Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFixpointClosureBridge
import Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge
import Mettapedia.Logic.CredalConceptOntologyGrowthBridge
import Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlCore
import Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlAlgorithms
import Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlChainer
import Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlExamples
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNGuardedHigherOrderSemantics
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNMixedModeChainComposition
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNProbHOLPlannerBridge
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNRegimeMixtureBenchmarkBridge
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNRegimeMixtureRegression
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNHigherOrderChainingTheorems
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNHigherOrderChainingRegression
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNHigherOrderCertifiedEstimates
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNUntrustedOracleAdapters
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNUntrustedOracleAdapterRegression
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNHigherOrderChainBounds
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNHigherOrderDecisionTheorems
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNGWASHigherOrderBridge
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNHigherOrderCertifiedChainingRegression
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNTopologyCPTNoGo
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNVarianceChainNoGo
import Mettapedia.PLN.RuleFamilies.HigherOrder.PLNHigherOrderNoGoBridge
import Mettapedia.Logic.MarkovLogicAbstract
import Mettapedia.Logic.MarkovLogicCountable
import Mettapedia.Logic.MarkovLogicFiniteRestriction
import Mettapedia.Logic.MarkovLogicFactorGraph
import Mettapedia.Logic.MarkovLogicWorldModel
import Mettapedia.Logic.MarkovLogicRegression
import Mettapedia.Logic.MarkovLogicClauseSemantics
import Mettapedia.Logic.MarkovLogicClauseFactorGraph
import Mettapedia.Logic.MarkovLogicClauseWorldModel
import Mettapedia.Logic.MarkovLogicClauseRegression
import Mettapedia.Logic.MarkovLogicInfiniteCollapse
import Mettapedia.Logic.MarkovLogicInfiniteSymmetricGridExample
import Mettapedia.ProbabilityTheory.BayesianNetworks.MessagePassingTreeExactness
import Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus
import Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNColliderSingletonBridge
import Mettapedia.PLN.Bridges.Languages.PLNErrorMagnificationGrounding
import Mettapedia.PLN.Bridges.ProbabilityTheory.PLNKyburgReduction
import Mettapedia.NARS.Bridges.PLN.RuleCorrespondence
import Mettapedia.PLN.Evidence.BinaryEvidence
import Mettapedia.PLN.Evidence.EvidenceSTVBridge
import Mettapedia.ProbabilityTheory.Exchangeability.DeFinetti
import Mettapedia.ProbabilityTheory.Exchangeability.DeFinettiProjectiveCredalBridge
import Mettapedia.PLN.Bridges.ProbabilityTheory.DeFinettiPLNTruthBridge
import Mettapedia.PLN.WorldModel.SufficientStatisticEncoder
import Mettapedia.PLN.WorldModel.GenericWorldModelForgetting
import Mettapedia.PLN.WorldModel.WorldModelOverlap
import Mettapedia.PLN.WorldModel.PLNWorldModelSupportForgetting
import Mettapedia.PLN.WorldModel.WorldModelConservationPack
import Mettapedia.PLN.WorldModel.OrderCost.PLNWorldModelOrderCostBounds
import Mettapedia.PLN.WorldModel.OrderCost.PLNWorldModelOrderCostAuditCertificate
import Mettapedia.PLN.WorldModel.OrderCost.PLNWorldModelOrderCostProvenanceDemo
import Mettapedia.PLN.WorldModel.OrderCost.PLNWorldModelOrderCostWeightedDemo
import Mettapedia.PLN.WorldModel.OrderCost.PLNWorldModelOrderCostGasPolicyDemo
import Mettapedia.PLN.WorldModel.Audit.PLNWorldModelAudit
import Mettapedia.PLN.WorldModel.Semitopology.PLNSemitopology
import Mettapedia.PLN.WorldModel.Provenance.PLNProvenanceWMSupportBridge
import Mettapedia.PLN.WorldModel.Semitopology.PLNSemitopologyProvenanceBridge
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.InfiniteSoundness
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.InfiniteCanary
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.FuzzyQuantifierSoundnessInf
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.ChoquetQuantifierSemantics
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.GradedQuantifierSpecialization
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.FuzzyDomainQuantifiers
import Mettapedia.PLN.RuleFamilies.FirstOrder.Quantifiers.FuzzyQuantifierSemanticsFin
import Mettapedia.Logic.HOL
import Mettapedia.Logic.HOL.Probabilistic
import Mettapedia.Logic.HOL.LogicalInduction
import Mettapedia.PLN.Bridges.HOL.LogicalInduction
import Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCore
import Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLCompleteness
import Mettapedia.PLN.Bridges.HOL.PLNWorldModelHOLSetBridge
import Mettapedia.PLN.Bridges.HOL.PLNHigherOrderHOL
import Mettapedia.PLN.Bridges.HOL.Probabilistic
import Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCode
import Mettapedia.PLN.Bridges.HOL.PLNWorldModelPredCodeInfinitary
import Mettapedia.PLN.WorldModel.WorldModelPreorder
import Mettapedia.PLN.Bridges.ProbabilityTheory.PLNGaussianEMExtension
import Mettapedia.PLN.TruthValues.PLNConfidenceWeightRevision
import Mettapedia.PLN.TruthValues.PLNInformationGeometry
import Mettapedia.PLN.TruthValues.PLNAmplitudePhase
import Mettapedia.PLN.TruthValues.PLNTruthTheoryIndex

open Mettapedia.PLN.Bridges.Languages

/-!
# PLN end-to-end interval-semantics theorems

This module proves composite statements that run through several PLN layers at
once:

- interval semantics for world-model queries (Bayes normal and exact
  intervals, Walley IDM) and their width/credibility identities;
- selector, WM rewrite, query equivalence and OSLF threshold transport,
  packaged as end-to-end bundles for an arbitrary interval semantics;
- mixed extensional/intensional (ASSOC/PAT) threshold atoms under
  Solomonoff-linked intensional score models;
- event-calculus threshold endpoints;
- an index of the derived Bayesian-network rules and their exactness matrix.

It is not an interface layer: every declaration here has content, and
statements from other modules are referenced by their own names.  The evidence
carriers, observation contracts, readouts, rules and world models these
theorems compose are owned by `Mettapedia.PLN.Evidence`,
`Mettapedia.PLN.TruthValues`, `Mettapedia.PLN.RuleFamilies` and
`Mettapedia.PLN.WorldModel`.

The logical-induction belief/process and planner-shadow statements are
experimental overlays; no intuitionistic or stronger-than-Henkin HOL
completeness claim is made here.
-/

namespace Mettapedia.PLN.Core.PLNCanonical

open Mettapedia.PLN.Evidence
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.RuleFamilies.FirstOrder
open Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNCompilation
open Mettapedia.PLN.Bridges.ProbabilityTheory.BayesNet.PLNBNCompilation.BNWorldModel
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNXiDerivedBNRules
open Mettapedia.PLN.RuleFamilies.FirstOrder.PLNXiDerivedBNRules.Typed
open Mettapedia.PLN.ConceptGeometry.AssocPat
open Mettapedia.ProbabilityTheory.BayesianNetworks
open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples

/-! ## WM-calculus canonical type aliases -/

/-! ## WM-Core View Aliases (Strength/Confidence/Interpretation) -/

/-  Naming convention:
`wmQuery*` aliases expose ENNReal-valued core views (not the Chapter-8 `Real` wrappers).
Use `wmQueryEq*_to_*` aliases for transport/equivalence lemmas on those core views. -/

/-! ## Error-Magnification Grounding Aliases -/

/-! ## Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV semantics canonical aliases -/

noncomputable def queryITVSigmaBayes95 {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (ctx : EvidenceClass.BinaryContext) (W : State) (q : Sigma Query) : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV :=
  PLNWorldModel.WorldModelSigma.queryITV (State := State) (Srt := Srt) (Query := Query) (Ctx := EvidenceClass.BinaryContext)
    PLNWorldModel.ITVSemantics.bayesCredible95 ctx W q

noncomputable def queryITVSigmaBayes90 {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (ctx : EvidenceClass.BinaryContext) (W : State) (q : Sigma Query) : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV :=
  PLNWorldModel.WorldModelSigma.queryITV (State := State) (Srt := Srt) (Query := Query) (Ctx := EvidenceClass.BinaryContext)
    PLNWorldModel.ITVSemantics.bayesCredible90 ctx W q

noncomputable def queryITVSigmaBayesExact95 {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (ctx : EvidenceClass.BinaryContext) (W : State) (q : Sigma Query) : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV :=
  PLNWorldModel.WorldModelSigma.queryITV (State := State) (Srt := Srt) (Query := Query) (Ctx := EvidenceClass.BinaryContext)
    PLNWorldModel.ITVSemantics.bayesCredibleExact95 ctx W q

noncomputable def queryITVSigmaBayesExact90 {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (ctx : EvidenceClass.BinaryContext) (W : State) (q : Sigma Query) : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV :=
  PLNWorldModel.WorldModelSigma.queryITV (State := State) (Srt := Srt) (Query := Query) (Ctx := EvidenceClass.BinaryContext)
    PLNWorldModel.ITVSemantics.bayesCredibleExact90 ctx W q

noncomputable def queryITVSigmaWalleyIDM {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (ctx : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext) (W : State) (q : Sigma Query) : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV :=
  PLNWorldModel.WorldModelSigma.queryITV (State := State) (Srt := Srt) (Query := Query) (Ctx := Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext)
    PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q

noncomputable def queryITVSigmaBayes95Jeffreys {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (W : State) (q : Sigma Query) : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV :=
  queryITVSigmaBayes95 (State := State) (Srt := Srt) (Query := Query)
    EvidenceClass.BinaryContext.jeffreys W q

noncomputable def queryITVSigmaBayesExact95Jeffreys {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (W : State) (q : Sigma Query) : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV :=
  queryITVSigmaBayesExact95 (State := State) (Srt := Srt) (Query := Query)
    EvidenceClass.BinaryContext.jeffreys W q

noncomputable def queryITVSigmaWalleyIDMDefault {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (W : State) (q : Sigma Query) : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV :=
  queryITVSigmaWalleyIDM (State := State) (Srt := Srt) (Query := Query)
    Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext.default W q

noncomputable def queryTypedITVSigmaWalleyIDM {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (ctx : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext) (W : State) (q : Sigma Query) :
    Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV (Mettapedia.PLN.TruthValues.PLNTruthTower.walleyBinaryITVSemantics ctx.s) :=
  PLNWorldModel.WorldModelSigma.queryTypedITVWalley (State := State) (Srt := Srt) (Query := Query) ctx W q

noncomputable def queryTypedITVSigmaWalleyIDMDefault {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (W : State) (q : Sigma Query) :
    Mettapedia.PLN.TruthValues.PLNTruthTower.TypedITV
      (Mettapedia.PLN.TruthValues.PLNTruthTower.walleyBinaryITVSemantics
        Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext.default.s) :=
  queryTypedITVSigmaWalleyIDM (State := State) (Srt := Srt) (Query := Query)
    Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext.default W q

theorem queryITVWalley_width_add_credibility
    {State Query : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (ctx : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext) (W : State) (q : Query) :
    PLNWorldModel.BinaryWorldModel.queryITVWidth
      (State := State) (Query := Query)
      PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q
      +
      PLNWorldModel.BinaryWorldModel.queryITVCredibility
        (State := State) (Query := Query)
        PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q
      = 1 :=
  PLNWorldModel.BinaryWorldModel.queryITVWidth_add_queryITVCredibility_walley
    (State := State) (Query := Query) ctx W q

theorem queryITVWalley_width_eq_one_sub_credibility
    {State Query : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (ctx : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext) (W : State) (q : Query) :
    PLNWorldModel.BinaryWorldModel.queryITVWidth
      (State := State) (Query := Query)
      PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q
      =
      1 -
      PLNWorldModel.BinaryWorldModel.queryITVCredibility
        (State := State) (Query := Query)
        PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q :=
  PLNWorldModel.BinaryWorldModel.queryITVWidth_eq_one_sub_queryITVCredibility_walley
    (State := State) (Query := Query) ctx W q

theorem queryITVSigmaWalley_width_add_credibility
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (ctx : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext) (W : State) (q : Sigma Query) :
    PLNWorldModel.WorldModelSigma.queryITVWidth
      (State := State) (Srt := Srt) (Query := Query)
      PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q
      +
      PLNWorldModel.WorldModelSigma.queryITVCredibility
        (State := State) (Srt := Srt) (Query := Query)
        PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q
      = 1 :=
  PLNWorldModel.WorldModelSigma.queryITVWidth_add_queryITVCredibility_walley
    (State := State) (Srt := Srt) (Query := Query) ctx W q

theorem queryITVSigmaWalley_width_eq_one_sub_credibility
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    (ctx : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext) (W : State) (q : Sigma Query) :
    PLNWorldModel.WorldModelSigma.queryITVWidth
      (State := State) (Srt := Srt) (Query := Query)
      PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q
      =
      1 -
      PLNWorldModel.WorldModelSigma.queryITVCredibility
        (State := State) (Srt := Srt) (Query := Query)
        PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W q :=
  PLNWorldModel.WorldModelSigma.queryITVWidth_eq_one_sub_queryITVCredibility_walley
    (State := State) (Srt := Srt) (Query := Query) ctx W q

/-! ## Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV Hypercube canonical aliases -/

/-! ## OSLF/GSLT Hypercube canonical aliases -/

/-- One-call Bayes-exact threshold transport:
rewrite-preservation followed by typed query-equivalence transport. -/
theorem applyITVThreshold_then_queryEq_transport_bayesExact
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State} {q : Sigma Query}
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .bayesExact)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesExact).eval ctx (r.derive W)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) r.conclusion q) :
    PLNWorldModel.WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query) (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .bayesExact)
      (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesExact) ctx W q coord tau := by
  exact Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.WMQueryEqSigma.to_WMITVThresholdJudgmentSigma_bayesExact
    (State := State) (Srt := Srt) (Query := Query)
    (q₁ := r.conclusion) (q₂ := q)
    hEq ctx coord tau
    (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITVThreshold_bayesExact_selector
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) ctx coord tau hSide hW hTau)

/-- One-call Bayes-normal threshold transport:
rewrite-preservation followed by typed query-equivalence transport. -/
theorem applyITVThreshold_then_queryEq_transport_bayesNormal
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State} {q : Sigma Query}
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .bayesNormal)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesNormal).eval ctx (r.derive W)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) r.conclusion q) :
    PLNWorldModel.WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query) (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .bayesNormal)
      (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesNormal) ctx W q coord tau := by
  exact Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.WMQueryEqSigma.to_WMITVThresholdJudgmentSigmaOfInterval
    (State := State) (Srt := Srt) (Query := Query)
    (q₁ := r.conclusion) (q₂ := q)
    hEq .bayesNormal ctx coord tau
    (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITVThreshold_ofInterval
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) .bayesNormal ctx coord tau hSide hW hTau)

/-- One-call Walley threshold transport:
rewrite-preservation followed by typed query-equivalence transport. -/
theorem applyITVThreshold_then_queryEq_transport_walley
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W : State} {q : Sigma Query}
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .walleyIDM)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .walleyIDM).eval ctx (r.derive W)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query) r.conclusion q) :
    PLNWorldModel.WorldModelSigma.WMITVThresholdJudgmentSigma
      (State := State) (Srt := Srt) (Query := Query) (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .walleyIDM)
      (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .walleyIDM) ctx W q coord tau := by
  exact Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.WMQueryEqSigma.to_WMITVThresholdJudgmentSigma_walley
    (State := State) (Srt := Srt) (Query := Query)
    (q₁ := r.conclusion) (q₂ := q)
    hEq ctx coord tau
    (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.WMRewriteRuleSigma.applyITVThreshold_walley_selector
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) ctx coord tau hSide hW hTau)

/-- End-to-end Bayes-exact bundle:
rewrite/query transport + quantale/selector coherence in one call. -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_bayesExact
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesExact).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    (∀ _ : Unit,
      Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar L₂ (m.mapTerm p) (m.mapTerm p)) ∧
    Mettapedia.Algebra.QuantaleWeakness.weakness
      (Mettapedia.OSLF.Framework.QuantaleCoherence.sourceWeight
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0)
        (fun _ : Unit => p)) H =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.OSLF.Framework.QuantaleCoherence.targetWeight
          (PLNWMOSLFBridgeITVTyped.wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0)
          m.mapTerm (fun _ : Unit => p)) H ∧
    (∀ u : Unit,
      Mettapedia.OSLF.Formula.sem R
        (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
          (State := State) (Srt := Srt) (Query := Query) (Ctx := Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext)
          PLNWorldModel.ITVSemantics.bayesCredibleExact95 ctx W₂ tau coord queryOfAtom₂)
        (.atom a0) (m.mapTerm ((fun _ : Unit => p) u))) := by
  have hThresh :=
    applyITVThreshold_then_queryEq_transport_bayesExact
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) (q := queryOfAtom₁ a0 p)
      ctx coord tau hSide hW hTau hEq
  rcases hThresh with ⟨_hWq, hTauQ⟩
  have hTauP :
      tau ≤ coord (PLNWorldModel.ITVSemantics.bayesCredibleExact95.eval ctx
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)) := by
    simpa [PLNWorldModel.WorldModelSigma.queryITV, Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval,
      PLNWMOSLFBridgeITVTyped.wmPatternValuation] using hTauQ
  exact
    PLNWMOSLFBridgeITVTyped.language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesExact_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := coord) (tau := tau)
      (hVal := hVal)
      (pick := fun _ : Unit => p)
      (hReach := by
        intro _u
        exact Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar.refl p)
      (H := H)
      (hTau := by
        intro _u
        simpa using hTauP)

/-- End-to-end Bayes-normal bundle:
rewrite/query transport + quantale/selector coherence in one call. -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_bayesNormal
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesNormal).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    (∀ _ : Unit,
      Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar L₂ (m.mapTerm p) (m.mapTerm p)) ∧
    Mettapedia.Algebra.QuantaleWeakness.weakness
      (Mettapedia.OSLF.Framework.QuantaleCoherence.sourceWeight
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0)
        (fun _ : Unit => p)) H =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.OSLF.Framework.QuantaleCoherence.targetWeight
          (PLNWMOSLFBridgeITVTyped.wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0)
          m.mapTerm (fun _ : Unit => p)) H ∧
    (∀ u : Unit,
      Mettapedia.OSLF.Formula.sem R
        (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
          (State := State) (Srt := Srt) (Query := Query) (Ctx := Mettapedia.PLN.Evidence.EvidenceClass.BinaryContext)
          PLNWorldModel.ITVSemantics.bayesCredible95 ctx W₂ tau coord queryOfAtom₂)
        (.atom a0) (m.mapTerm ((fun _ : Unit => p) u))) := by
  have hThresh :=
    applyITVThreshold_then_queryEq_transport_bayesNormal
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) (q := queryOfAtom₁ a0 p)
      ctx coord tau hSide hW hTau hEq
  rcases hThresh with ⟨_hWq, hTauQ⟩
  have hTauP :
      tau ≤ coord (PLNWorldModel.ITVSemantics.bayesCredible95.eval ctx
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)) := by
    simpa [PLNWorldModel.WorldModelSigma.queryITV, Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval,
      PLNWMOSLFBridgeITVTyped.wmPatternValuation] using hTauQ
  exact
    PLNWMOSLFBridgeITVTyped.language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m)
      (itvSem := PLNWorldModel.ITVSemantics.bayesCredible95) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := coord) (tau := tau)
      (hVal := hVal)
      (pick := fun _ : Unit => p)
      (hReach := by
        intro _u
        exact Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar.refl p)
      (H := H)
      (hTau := by
        intro _u
        simpa using hTauP)

/-- End-to-end Walley bundle:
rewrite/query transport + quantale/selector coherence in one call. -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_walley
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .walleyIDM).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    (∀ _ : Unit,
      Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar L₂ (m.mapTerm p) (m.mapTerm p)) ∧
    Mettapedia.Algebra.QuantaleWeakness.weakness
      (Mettapedia.OSLF.Framework.QuantaleCoherence.sourceWeight
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0)
        (fun _ : Unit => p)) H =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.OSLF.Framework.QuantaleCoherence.targetWeight
          (PLNWMOSLFBridgeITVTyped.wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0)
          m.mapTerm (fun _ : Unit => p)) H ∧
    (∀ u : Unit,
      Mettapedia.OSLF.Formula.sem R
        (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
          (State := State) (Srt := Srt) (Query := Query) (Ctx := Mettapedia.PLN.Bridges.ProbabilityTheory.EvidenceDirichlet.IDMPredictiveContext)
          PLNWorldModel.ITVSemantics.walleyIDMPredictive ctx W₂ tau coord queryOfAtom₂)
        (.atom a0) (m.mapTerm ((fun _ : Unit => p) u))) := by
  have hThresh :=
    applyITVThreshold_then_queryEq_transport_walley
      (State := State) (Srt := Srt) (Query := Query)
      (r := r) (q := queryOfAtom₁ a0 p)
      ctx coord tau hSide hW hTau hEq
  rcases hThresh with ⟨_hWq, hTauQ⟩
  have hTauP :
      tau ≤ coord (PLNWorldModel.ITVSemantics.walleyIDMPredictive.eval ctx
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)) := by
    simpa [PLNWorldModel.WorldModelSigma.queryITV, Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval,
      PLNWMOSLFBridgeITVTyped.wmPatternValuation] using hTauQ
  exact
    PLNWMOSLFBridgeITVTyped.language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_walley_id
      (State := State) (Srt := Srt) (Query := Query)
      (R := R) (m := m) (ctx := ctx)
      (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (coord := coord) (tau := tau)
      (hVal := hVal)
      (pick := fun _ : Unit => p)
      (hReach := by
        intro _u
        exact Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar.refl p)
      (H := H)
      (hTau := by
        intro _u
        simpa using hTauP)

/-- Interval-indexed one-call bundle:
hypercube selector transport + rewrite/query transport + quantale coherence. -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_of_interval
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    (∀ _ : Unit,
      Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar L₂ (m.mapTerm p) (m.mapTerm p)) ∧
    Mettapedia.Algebra.QuantaleWeakness.weakness
      (Mettapedia.OSLF.Framework.QuantaleCoherence.sourceWeight
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0)
        (fun _ : Unit => p)) H =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.OSLF.Framework.QuantaleCoherence.targetWeight
          (PLNWMOSLFBridgeITVTyped.wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0)
          m.mapTerm (fun _ : Unit => p)) H ∧
    (∀ u : Unit,
      Mettapedia.OSLF.Formula.sem R
        (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
          (State := State) (Srt := Srt) (Query := Query)
          (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
          (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W₂ tau coord queryOfAtom₂)
        (.atom a0) (m.mapTerm ((fun _ : Unit => p) u))) := by
  cases i with
  | bayesNormal =>
      exact
        (end_to_end_quantale_selector_rewrite_query_threshold_bayesNormal
          (State := State) (Srt := Srt) (Query := Query)
          (R := R) (m := m) (ctx := ctx)
          (r := r) (W₁ := W₁) (W₂ := W₂)
          (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
          (a0 := a0) (p := p) (coord := coord) (tau := tau)
          hSide hW hTau hEq hVal H)
  | bayesExact =>
      exact
        (end_to_end_quantale_selector_rewrite_query_threshold_bayesExact
          (State := State) (Srt := Srt) (Query := Query)
          (R := R) (m := m) (ctx := ctx)
          (r := r) (W₁ := W₁) (W₂ := W₂)
          (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
          (a0 := a0) (p := p) (coord := coord) (tau := tau)
          hSide hW hTau hEq hVal H)
  | walleyIDM =>
      exact
        (end_to_end_quantale_selector_rewrite_query_threshold_walley
          (State := State) (Srt := Srt) (Query := Query)
          (R := R) (m := m) (ctx := ctx)
          (r := r) (W₁ := W₁) (W₂ := W₂)
          (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
          (a0 := a0) (p := p) (coord := coord) (tau := tau)
          hSide hW hTau hEq hVal H)

/-- Interval-indexed one-call bundle for genuinely dependent query families.
This composes rewrite/query Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV transport and quantale coherence in one theorem. -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_of_interval_dep
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    (∀ _ : Unit,
      Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar L₂ (m.mapTerm p) (m.mapTerm p)) ∧
    Mettapedia.Algebra.QuantaleWeakness.weakness
      (Mettapedia.OSLF.Framework.QuantaleCoherence.sourceWeight
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0)
        (fun _ : Unit => p)) H =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.OSLF.Framework.QuantaleCoherence.targetWeight
          (PLNWMOSLFBridgeITVTyped.wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0)
          m.mapTerm (fun _ : Unit => p)) H ∧
    (∀ u : Unit,
      Mettapedia.OSLF.Formula.sem R
        (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
          (State := State) (Srt := Srt) (Query := Query)
          (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
          (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W₂ tau coord queryOfAtom₂)
        (.atom a0) (m.mapTerm ((fun _ : Unit => p) u))) := by
  cases i with
  | bayesNormal =>
      have hThresh :=
        applyITVThreshold_then_queryEq_transport_bayesNormal
          (State := State) (Srt := Srt) (Query := Query)
          (r := r) (q := queryOfAtom₁ a0 p)
          ctx coord tau hSide hW hTau hEq
      rcases hThresh with ⟨_hWq, hTauQ⟩
      have hTauP :
          tau ≤ coord (PLNWorldModel.ITVSemantics.bayesCredible95.eval ctx
            (PLNWMOSLFBridgeITVTyped.wmPatternValuation
              (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)) := by
        simpa [PLNWorldModel.WorldModelSigma.queryITV, Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval,
          PLNWMOSLFBridgeITVTyped.wmPatternValuation] using hTauQ
      exact
        PLNWMOSLFBridgeITVTyped.language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesNormal_id
          (State := State) (Srt := Srt) (Query := Query)
          (R := R) (m := m) (ctx := ctx)
          (W₁ := W₁) (W₂ := W₂)
          (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
          (a0 := a0) (coord := coord) (tau := tau)
          (hVal := hVal)
          (pick := fun _ : Unit => p)
          (hReach := by
            intro _u
            exact Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar.refl p)
          (H := H)
          (hTau := by
            intro _u
            simpa using hTauP)
  | bayesExact =>
      have hThresh :=
        applyITVThreshold_then_queryEq_transport_bayesExact
          (State := State) (Srt := Srt) (Query := Query)
          (r := r) (q := queryOfAtom₁ a0 p)
          ctx coord tau hSide hW hTau hEq
      rcases hThresh with ⟨_hWq, hTauQ⟩
      have hTauP :
          tau ≤ coord (PLNWorldModel.ITVSemantics.bayesCredibleExact95.eval ctx
            (PLNWMOSLFBridgeITVTyped.wmPatternValuation
              (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)) := by
        simpa [PLNWorldModel.WorldModelSigma.queryITV, Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval,
          PLNWMOSLFBridgeITVTyped.wmPatternValuation] using hTauQ
      exact
        PLNWMOSLFBridgeITVTyped.language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_bayesExact_id
          (State := State) (Srt := Srt) (Query := Query)
          (R := R) (m := m) (ctx := ctx)
          (W₁ := W₁) (W₂ := W₂)
          (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
          (a0 := a0) (coord := coord) (tau := tau)
          (hVal := hVal)
          (pick := fun _ : Unit => p)
          (hReach := by
            intro _u
            exact Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar.refl p)
          (H := H)
          (hTau := by
            intro _u
            simpa using hTauP)
  | walleyIDM =>
      have hThresh :=
        applyITVThreshold_then_queryEq_transport_walley
          (State := State) (Srt := Srt) (Query := Query)
          (r := r) (q := queryOfAtom₁ a0 p)
          ctx coord tau hSide hW hTau hEq
      rcases hThresh with ⟨_hWq, hTauQ⟩
      have hTauP :
          tau ≤ coord (PLNWorldModel.ITVSemantics.walleyIDMPredictive.eval ctx
            (PLNWMOSLFBridgeITVTyped.wmPatternValuation
              (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p)) := by
        simpa [PLNWorldModel.WorldModelSigma.queryITV, Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval,
          PLNWMOSLFBridgeITVTyped.wmPatternValuation] using hTauQ
      exact
        PLNWMOSLFBridgeITVTyped.language_quantale_coherence_wmITV_threshold_atom_of_queryEncoders_walley_id
          (State := State) (Srt := Srt) (Query := Query)
          (R := R) (m := m) (ctx := ctx)
          (W₁ := W₁) (W₂ := W₂)
          (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
          (a0 := a0) (coord := coord) (tau := tau)
          (hVal := hVal)
          (pick := fun _ : Unit => p)
          (hReach := by
            intro _u
            exact Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar.refl p)
          (H := H)
          (hTau := by
            intro _u
            simpa using hTauP)

/-- Canonical structured output type for one-call end-to-end transport/coherence. -/
abbrev EndToEndQuantaleSelectorRewriteQueryThresholdBundle
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (H : Finset (Unit × Unit)) : Prop :=
  (∀ _ : Unit,
    Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar L₂ (m.mapTerm p) (m.mapTerm p)) ∧
  Mettapedia.Algebra.QuantaleWeakness.weakness
    (Mettapedia.OSLF.Framework.QuantaleCoherence.sourceWeight
      (PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0)
      (fun _ : Unit => p)) H =
    Mettapedia.Algebra.QuantaleWeakness.weakness
      (Mettapedia.OSLF.Framework.QuantaleCoherence.targetWeight
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0)
        m.mapTerm (fun _ : Unit => p)) H ∧
  (∀ u : Unit,
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Srt) (Query := Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W₂ tau coord queryOfAtom₂)
      (.atom a0) (m.mapTerm ((fun _ : Unit => p) u)))

/-- Bundle endpoint:
interval-indexed one-call transport from selector + rewrite/query + quantale coherence. -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_bundle_of_interval
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdBundle
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom₁ queryOfAtom₂ a0 p coord tau H := by
  exact end_to_end_quantale_selector_rewrite_query_threshold_of_interval
    (State := State) (Srt := Srt) (Query := Query)
    (i := i) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
    (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- Bundle endpoint for genuinely dependent query families. -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_bundle_of_interval_dep
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdBundle
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom₁ queryOfAtom₂ a0 p coord tau H := by
  exact end_to_end_quantale_selector_rewrite_query_threshold_of_interval_dep
    (State := State) (Srt := Srt) (Query := Query)
    (i := i) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
    (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- Record-valued end-to-end artifact (not a conjunction):
selector transport + rewrite/query transport + quantale coherence. -/
structure EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (H : Finset (Unit × Unit)) : Type where
  reachability :
    ∀ _ : Unit,
      Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar L₂ (m.mapTerm p) (m.mapTerm p)
  quantale_coherence :
    Mettapedia.Algebra.QuantaleWeakness.weakness
      (Mettapedia.OSLF.Framework.QuantaleCoherence.sourceWeight
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0)
        (fun _ : Unit => p)) H =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.OSLF.Framework.QuantaleCoherence.targetWeight
          (PLNWMOSLFBridgeITVTyped.wmPatternValuation
            (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0)
          m.mapTerm (fun _ : Unit => p)) H
  truth_transport :
    ∀ u : Unit,
      Mettapedia.OSLF.Formula.sem R
        (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
          (State := State) (Srt := Srt) (Query := Query)
          (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
          (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W₂ tau coord queryOfAtom₂)
        (.atom a0) (m.mapTerm ((fun _ : Unit => p) u))

/-- Final one-call record-valued endpoint (interval-indexed). -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_of_interval
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom₁ queryOfAtom₂ a0 p coord tau H := by
  rcases end_to_end_quantale_selector_rewrite_query_threshold_bundle_of_interval
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      (r := r) (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (p := p) (coord := coord) (tau := tau)
      hSide hW hTau hEq hVal H with ⟨hReach, hRest⟩
  rcases hRest with ⟨hWeak, hTruth⟩
  exact
    { reachability := hReach
      quantale_coherence := hWeak
      truth_transport := hTruth }

/-- Final one-call record-valued endpoint for dependent query families. -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_of_interval_dep
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom₁ queryOfAtom₂ a0 p coord tau H := by
  rcases end_to_end_quantale_selector_rewrite_query_threshold_bundle_of_interval_dep
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      (r := r) (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (p := p) (coord := coord) (tau := tau)
      hSide hW hTau hEq hVal H with ⟨hReach, hRest⟩
  rcases hRest with ⟨hWeak, hTruth⟩
  exact
    { reachability := hReach
      quantale_coherence := hWeak
      truth_transport := hTruth }

/-! ## Chapter-8 style threshold-acceptance endpoint -/

/-- Chapter-8 style threshold acceptance on the target side:
OSLF threshold-atom truth after WM rewrite + quantale/coherence transport. -/
def thresholdAccepted
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (W₂ : State)
    (queryOfAtom₂ : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ) : Prop :=
  Mettapedia.OSLF.Formula.sem R
    (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
      (State := State) (Srt := Srt) (Query := Query)
      (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
      (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W₂ tau coord queryOfAtom₂)
    (.atom a0) (m.mapTerm p)

/-- Any final-bundle witness gives Chapter-8 threshold acceptance directly. -/
theorem thresholdAccepted_of_finalBundle
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (W₁ W₂ : State)
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (H : Finset (Unit × Unit))
    (bundle :
      EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
        (State := State) (Srt := Srt) (Query := Query)
        (i := i) (R := R) (m := m) (ctx := ctx)
        W₁ W₂ queryOfAtom₁ queryOfAtom₂ a0 p coord tau H) :
    thresholdAccepted
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₂ queryOfAtom₂ a0 p coord tau := by
  simpa [thresholdAccepted] using bundle.truth_transport ()

/-- Single Chapter-8 one-call endpoint:
WM rewrite + OSLF transport + threshold acceptance as one theorem. -/
theorem wm_rewrite_oslf_threshold_acceptance_of_interval
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (H : Finset (Unit × Unit)) :
    thresholdAccepted
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₂ queryOfAtom₂ a0 p coord tau := by
  exact thresholdAccepted_of_finalBundle
    (State := State) (Srt := Srt) (Query := Query)
    (i := i) (R := R) (m := m) (ctx := ctx)
    (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
    (a0 := a0) (p := p) (coord := coord) (tau := tau) (H := H)
    (end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_of_interval
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      (r := r) (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (p := p) (coord := coord) (tau := tau)
      hSide hW hTau hEq hVal H)

/-! ## Chapter-9 positive composition endpoint (selector + rewrite + threshold) -/

/-- One-call composed endpoint for non-counterexample Chapter-9 development:
combine Chapter-13 algorithmic selector guarantees with Chapter-8
rewrite→OSLF→threshold acceptance.

The selector output `G` is mapped into the hypercube witness carrier via
`selectorWitness`, making the composition explicit while keeping the two
semantic layers modular. -/
theorem selector_rewrite_threshold_end_to_end_of_interval
    {Goal Fact Bin : Type*} [Fintype Fact] [DecidableEq Fact]
    (A : Mettapedia.PLN.InferenceControl.PremiseSelection.PriorNBAssumptionChecklist Goal Fact Bin)
    (η : Fact → ℝ)
    (globalPrior localPrior likelihood : Mettapedia.PLN.InferenceControl.PremiseSelection.Scorer Goal Fact)
    (g : Goal)
    (hLocal : A.localExchangeabilityInBin)
    (δ : Fact → ℝ) (ε : ℝ)
    (hTwoStage :
      Mettapedia.PLN.InferenceControl.PremiseSelection.Optimality.BayesOptimalRanking η
        (Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlCore.twoStageSelectorScore globalPrior localPrior likelihood g))
    (hbound : ∀ x, |δ x| ≤ ε)
    (hmargin : ∀ x y, η x < η y →
      Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlCore.pooledSelectorScore globalPrior localPrior likelihood g y
        - Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlCore.pooledSelectorScore globalPrior localPrior likelihood g x > 2 * ε)
    (htie : ∀ x y, η x = η y → δ x = δ y)
    (D : Finset Fact)
    {State Srt : Type*} {Query : Srt → Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (selectorWitness : Finset Fact → Finset (Unit × Unit)) :
    let G := Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlAlgorithms.greedySelect D A.topK
    (A.topK ≤ Fintype.card Fact
      ∧ (∀ g' f',
          0 ≤ (Mettapedia.PLN.InferenceControl.PremiseSelection.selectorDefaults_halfGate Goal Fact).gate g' f'
            ∧ (Mettapedia.PLN.InferenceControl.PremiseSelection.selectorDefaults_halfGate Goal Fact).gate g' f' ≤ 1)
      ∧ Mettapedia.PLN.InferenceControl.PremiseSelection.Optimality.BayesOptimalRanking η
          (Mettapedia.PLN.InferenceControl.PremiseSelection.Optimality.perturbedScore
            (Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlCore.pooledSelectorScore globalPrior localPrior likelihood g) δ)
      ∧ (1 - Real.exp (-1)) * (Nat.min A.topK D.card : ℝ) ≤
          Mettapedia.PLN.InferenceControl.PremiseSelection.dependencyCoverage D G)
      ∧ thresholdAccepted
          (State := State) (Srt := Srt) (Query := Query)
          (i := i) (R := R) (m := m) (ctx := ctx)
          W₂ queryOfAtom₂ a0 p coord tau := by
  intro G
  refine ⟨?_, ?_⟩
  · simpa [G] using
      (Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlAlgorithms.inferenceControl_end_to_end_algorithmic
        (A := A) (η := η)
        (globalPrior := globalPrior) (localPrior := localPrior)
        (likelihood := likelihood) (g := g)
        hLocal (δ := δ) (ε := ε) hTwoStage hbound hmargin htie
        (D := D))
  · exact wm_rewrite_oslf_threshold_acceptance_of_interval
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      (r := r) (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (p := p) (coord := coord) (tau := tau)
      hSide hW hTau hEq hVal (selectorWitness G)

/-! ### Formed-concept exactness interface -/

/-! ### Credal formed-concept interface -/

/-! ### Mixed-channel boundary canary -/

/-- Pattern-level mixed inheritance atom-query encoder. -/
def patternInheritanceQueryOfAtom_mixed
    {Query : Type}
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query) :
    String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query) :=
  fun a p => PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedQ enc
    (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a) p

/-- Mixed (extensional+ASSOC) rewrite-to-threshold endpoint under selected Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV semantics. -/
theorem intensional_mixed_assoc_threshold_atom_of_interval
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (Side : Prop)
    (hSound : Side →
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedPolicyAssoc
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : Side)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p := by
  simpa [patternInheritanceQueryOfAtom_mixed] using
    (PLNWMOSLFBridgeITVTyped.wmRewriteRuleSigma_itv_threshold_atom
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
      (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
      R (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx tau coord
      (r := PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_of_assoc
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query)
        enc combine Side hSound (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
      hSide W
      (queryOfAtom := patternInheritanceQueryOfAtom_mixed enc)
      (a := a0) (p := p) (hEnc := rfl) hTau)

/-- Composed endpoint: Solomonoff log-ratio bridge + mixed-ASSOC threshold transport. -/
theorem intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (Side : Prop)
    (hSound : Side →
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedPolicyAssoc
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : Side)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.UniversalAI.SolomonoffPrior.BinString)
    (liftScore : ℝ → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (hAssocLift :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) W enc
        (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
      liftScore (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ x F Wc))
    (hPrior : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc)
    (hExt : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (liftScore
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p := by
  have hLog :
      Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ x F Wc =
        Real.log
          (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc) /
        Real.log 2 :=
    Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional_eq_log2_ratio ξ x F Wc hPrior hExt
  have hTau' :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
        (combine
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
            (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
            (Query := Query) W enc
            (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
            (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
            (Query := Query) W enc
            (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p))) := by
    simpa [hAssocLift, hLog] using hTau
  exact intensional_mixed_assoc_threshold_atom_of_interval
    (State := State) (Query := Query)
    i R ctx enc combine Side hSound W a0 p coord tau hSide hTau'

/-- Semantic form of the Solomonoff-composed endpoint:
consumes ASSOC-score correspondences instead of a direct `hAssocLift`. -/
theorem intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.UniversalAI.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc)
    (hExt : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p := by
  have hSound :
      True →
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedPolicyAssoc
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine := by
    intro _
    exact
      PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedPolicyAssoc_of_assocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence hMixed hAssoc
  have hAssocLift :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) W enc
        (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
      scoreToEvidence (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ x F Wc) := by
    exact
      PLNIntensionalWorldModel.InheritanceQueryBuilder.assocEvidence_eq_scoreToEvidence_of_assocScore_eq
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence hAssoc
        (W := W) (a := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) (b := p)
        hAssocScore
  exact intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff
    (State := State) (Query := Query)
    i R ctx enc combine True hSound W a0 p coord tau trivial
    ξ x F Wc scoreToEvidence hAssocLift hPrior hExt hTau

/-- Canonical score-model alias for intensional inheritance channels. -/
abbrev InheritanceIntensionalScoreModel
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query) :=
  PLNIntensionalWorldModel.InheritanceQueryBuilder.IntensionalScoreModel
    (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) (Query := Query) enc

/-- Structured Solomonoff context used to tie query-level ASSOC scores to
universal-mixture intensional inheritance. -/
structure SolomonoffAssocContext where
  x : Mettapedia.UniversalAI.SolomonoffPrior.BinString
  F : Mettapedia.UniversalAI.SolomonoffPrior.BinString
  Wc : Mettapedia.UniversalAI.SolomonoffPrior.BinString

/-- Canonical model eliminating ad hoc per-query ASSOC-score bridge assumptions. -/
structure SolomonoffAssocLinkedModel
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query) where
  scoreModel : InheritanceIntensionalScoreModel (State := State) (Query := Query) enc
  contextOf : State → String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
    Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure → SolomonoffAssocContext
  assocScore_context :
    ∀ (W : State) (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
      (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure),
      scoreModel.assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ
          (contextOf W a0 p ξ).x
          (contextOf W a0 p ξ).F
          (contextOf W a0 p ξ).Wc

/-- Strong linked Solomonoff model:
extends `SolomonoffAssocLinkedModel` by internalizing mixed-channel and positivity
obligations, removing common Chapter-12 call-site hypotheses. -/
structure SolomonoffAssocLinkedModelStrong
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query) where
  linked : SolomonoffAssocLinkedModel (State := State) (Query := Query) enc
  combine : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence
  mixed_sound :
    PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
      (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
      (Query := Query) enc combine
      linked.scoreModel.assocScore linked.scoreModel.scoreToEvidence
  prior_pos :
    ∀ (W : State) (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
      (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure),
      0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
        (linked.contextOf W a0 p ξ).x
        (linked.contextOf W a0 p ξ).Wc
  ext_pos :
    ∀ (W : State) (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
      (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure),
      0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
        (linked.contextOf W a0 p ξ).x
        (linked.contextOf W a0 p ξ).F
        (linked.contextOf W a0 p ξ).Wc

/-- Model-based semantic Solomonoff endpoint:
same theorem as `..._semantic`, but consumes a canonical score model. -/
theorem intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_model
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (model : InheritanceIntensionalScoreModel (State := State) (Query := Query) enc)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine model.assocScore model.scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.UniversalAI.SolomonoffPrior.BinString)
    (hAssocScore :
      model.assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc)
    (hExt : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    i R ctx enc combine model.assocScore model.scoreToEvidence
    hMixed model.assoc_sound
    W a0 p coord tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Linked semantic Solomonoff endpoint with no explicit per-query
`hAssocScore` argument: the context linker carries that law canonically. -/
theorem intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_linked
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (model : SolomonoffAssocLinkedModel (State := State) (Query := Query) enc)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine
        model.scoreModel.assocScore model.scoreModel.scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (hPrior : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
      (model.contextOf W a0 p ξ).x
      (model.contextOf W a0 p ξ).Wc)
    (hExt : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
      (model.contextOf W a0 p ξ).x
      (model.contextOf W a0 p ξ).F
      (model.contextOf W a0 p ξ).Wc)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.scoreModel.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
              (model.contextOf W a0 p ξ).x
              (model.contextOf W a0 p ξ).F
              (model.contextOf W a0 p ξ).Wc /
             Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
              (model.contextOf W a0 p ξ).x
              (model.contextOf W a0 p ξ).Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p := by
  let c := model.contextOf W a0 p ξ
  have hAssocScore :
      model.scoreModel.assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ c.x c.F c.Wc := by
    simpa [c] using model.assocScore_context W a0 p ξ
  have hPrior' : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ c.x c.Wc := by
    simpa [c] using hPrior
  have hExt' : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ c.x c.F c.Wc := by
    simpa [c] using hExt
  have hTau' : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.scoreModel.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ c.x c.F c.Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ c.x c.Wc) /
            Real.log 2)))) := by
    simpa [c] using hTau
  exact intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_model
    (State := State) (Query := Query)
    i R ctx enc combine model.scoreModel hMixed
    W a0 p coord tau ξ c.x c.F c.Wc hAssocScore hPrior' hExt' hTau'

/-- Strong linked endpoint:
same as `..._semantic_linked`, but mixed-channel and positivity obligations are
carried by `SolomonoffAssocLinkedModelStrong`. -/
theorem intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_linked_strong
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : SolomonoffAssocLinkedModelStrong (State := State) (Query := Query) enc)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
              (model.linked.contextOf W a0 p ξ).x
              (model.linked.contextOf W a0 p ξ).F
              (model.linked.contextOf W a0 p ξ).Wc /
             Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
              (model.linked.contextOf W a0 p ξ).x
              (model.linked.contextOf W a0 p ξ).Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_linked
    (State := State) (Query := Query)
    i R ctx enc model.combine model.linked model.mixed_sound
    W a0 p coord tau ξ
    (model.prior_pos W a0 p ξ)
    (model.ext_pos W a0 p ξ)
    hTau

/-- Bayes-normal selector wrapper for the strong linked semantic endpoint. -/
theorem intensional_mixed_assoc_threshold_atom_bayesNormal_of_solomonoff_semantic_linked_strong
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .bayesNormal)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : SolomonoffAssocLinkedModelStrong (State := State) (Query := Query) enc)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesNormal).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
              (model.linked.contextOf W a0 p ξ).x
              (model.linked.contextOf W a0 p ξ).F
              (model.linked.contextOf W a0 p ξ).Wc /
             Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
              (model.linked.contextOf W a0 p ξ).x
              (model.linked.contextOf W a0 p ξ).Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .bayesNormal)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesNormal) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_linked_strong
    (State := State) (Query := Query)
    .bayesNormal R ctx enc model W a0 p coord tau ξ hTau

/-- Bayes-exact selector wrapper for the strong linked semantic endpoint. -/
theorem intensional_mixed_assoc_threshold_atom_bayesExact_of_solomonoff_semantic_linked_strong
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .bayesExact)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : SolomonoffAssocLinkedModelStrong (State := State) (Query := Query) enc)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesExact).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
              (model.linked.contextOf W a0 p ξ).x
              (model.linked.contextOf W a0 p ξ).F
              (model.linked.contextOf W a0 p ξ).Wc /
             Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
              (model.linked.contextOf W a0 p ξ).x
              (model.linked.contextOf W a0 p ξ).Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .bayesExact)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesExact) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_linked_strong
    (State := State) (Query := Query)
    .bayesExact R ctx enc model W a0 p coord tau ξ hTau

/-- Walley-IDM selector wrapper for the strong linked semantic endpoint. -/
theorem intensional_mixed_assoc_threshold_atom_walley_of_solomonoff_semantic_linked_strong
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .walleyIDM)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : SolomonoffAssocLinkedModelStrong (State := State) (Query := Query) enc)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .walleyIDM).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
              (model.linked.contextOf W a0 p ξ).x
              (model.linked.contextOf W a0 p ξ).F
              (model.linked.contextOf W a0 p ξ).Wc /
             Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
              (model.linked.contextOf W a0 p ξ).x
              (model.linked.contextOf W a0 p ξ).Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .walleyIDM)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .walleyIDM) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_linked_strong
    (State := State) (Query := Query)
    .walleyIDM R ctx enc model W a0 p coord tau ξ hTau

/-- Bayes-normal selector wrapper for semantic Solomonoff-composed intensional threshold transport. -/
theorem intensional_mixed_assoc_threshold_atom_bayesNormal_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .bayesNormal)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.UniversalAI.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc)
    (hExt : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesNormal).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .bayesNormal)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesNormal) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    .bayesNormal R ctx enc combine assocScore scoreToEvidence hMixed hAssoc
    W a0 p coord tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Bayes-exact selector wrapper for semantic Solomonoff-composed intensional threshold transport. -/
theorem intensional_mixed_assoc_threshold_atom_bayesExact_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .bayesExact)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.UniversalAI.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc)
    (hExt : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesExact).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .bayesExact)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesExact) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    .bayesExact R ctx enc combine assocScore scoreToEvidence hMixed hAssoc
    W a0 p coord tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Walley selector wrapper for semantic Solomonoff-composed intensional threshold transport. -/
theorem intensional_mixed_assoc_threshold_atom_walley_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .walleyIDM)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.UniversalAI.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc)
    (hExt : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .walleyIDM).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc) /
            Real.log 2))))) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .walleyIDM)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .walleyIDM) ctx W tau coord
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    .walleyIDM R ctx enc combine assocScore scoreToEvidence hMixed hAssoc
    W a0 p coord tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Lower-coordinate specialization of the semantic Solomonoff-composed endpoint. -/
theorem intensional_mixed_assoc_lower_threshold_atom_of_interval_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.UniversalAI.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc)
    (hExt : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc) /
            Real.log 2)))).lower) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W tau (fun itv => itv.lower)
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    i R ctx enc combine assocScore scoreToEvidence hMixed hAssoc
    W a0 p (fun itv => itv.lower) tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Upper-coordinate specialization of the semantic Solomonoff-composed endpoint. -/
theorem intensional_mixed_assoc_upper_threshold_atom_of_interval_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.UniversalAI.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc)
    (hExt : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc) /
            Real.log 2)))).upper) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W tau (fun itv => itv.upper)
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    i R ctx enc combine assocScore scoreToEvidence hMixed hAssoc
    W a0 p (fun itv => itv.upper) tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Credibility-coordinate specialization of the semantic Solomonoff-composed endpoint. -/
theorem intensional_mixed_assoc_credibility_threshold_atom_of_interval_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.UniversalAI.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc)
    (hExt : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc) /
            Real.log 2)))).credibility) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W tau (fun itv => itv.credibility)
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    i R ctx enc combine assocScore scoreToEvidence hMixed hAssoc
    W a0 p (fun itv => itv.credibility) tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Width-coordinate specialization of the semantic Solomonoff-composed endpoint. -/
theorem intensional_mixed_assoc_width_threshold_atom_of_interval_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.UniversalAI.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc)
    (hExt : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc) /
            Real.log 2)))).width) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W tau (fun itv => itv.width)
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    i R ctx enc combine assocScore scoreToEvidence hMixed hAssoc
    W a0 p (fun itv => itv.width) tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Strength-coordinate specialization of the semantic Solomonoff-composed endpoint. -/
theorem intensional_mixed_assoc_strength_threshold_atom_of_interval_of_solomonoff_semantic
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (assocScore : State → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → ℝ)
    (scoreToEvidence : ℝ → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine assocScore scoreToEvidence)
    (hAssoc :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.AssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc assocScore scoreToEvidence)
    (W : State)
    (a0 : String) (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (x F Wc : Mettapedia.UniversalAI.SolomonoffPrior.BinString)
    (hAssocScore :
      assocScore W (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
        Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ x F Wc)
    (hPrior : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc)
    (hExt : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc)
    (hTau : tau ≤ ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ x F Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ x Wc) /
            Real.log 2)))).strength) :
    Mettapedia.OSLF.Formula.sem R
      (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
        (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W tau (fun itv => itv.strength)
        (patternInheritanceQueryOfAtom_mixed enc))
      (.atom a0) p :=
  intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic
    (State := State) (Query := Query)
    i R ctx enc combine assocScore scoreToEvidence hMixed hAssoc
    W a0 p (fun itv => itv.strength) tau ξ x F Wc hAssocScore hPrior hExt hTau

/-- Inheritance-sort one-call bundle endpoint (generic query encoder). -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_bundle_inheritance_of_interval
    {State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)} {W₁ W₂ : State}
    (queryOfAtom : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Sigma (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern))
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
      r.conclusion (queryOfAtom a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
        W₂ queryOfAtom a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
        W₁ queryOfAtom a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdBundle
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom queryOfAtom a0 p coord tau H := by
  exact end_to_end_quantale_selector_rewrite_query_threshold_bundle_of_interval
    (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
    (i := i) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom) (queryOfAtom₂ := queryOfAtom)
    (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- Inheritance-sort one-call final-bundle endpoint (generic query encoder). -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_of_interval
    {State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)} {W₁ W₂ : State}
    (queryOfAtom : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Sigma (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern))
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
      r.conclusion (queryOfAtom a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
        W₂ queryOfAtom a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
        W₁ queryOfAtom a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom queryOfAtom a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_of_interval
    (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
    (i := i) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom) (queryOfAtom₂ := queryOfAtom)
    (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- Inheritance-sort final-bundle endpoint specialized to Bayes normal semantics. -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_bayesNormal
    {State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .bayesNormal)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)} {W₁ W₂ : State}
    (queryOfAtom : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Sigma (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern))
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesNormal).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
      r.conclusion (queryOfAtom a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
        W₂ queryOfAtom a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
        W₁ queryOfAtom a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
      (i := .bayesNormal) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom queryOfAtom a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_of_interval
    (State := State) (i := .bayesNormal) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom := queryOfAtom) (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- Inheritance-sort final-bundle endpoint specialized to Bayes exact semantics. -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_bayesExact
    {State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .bayesExact)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)} {W₁ W₂ : State}
    (queryOfAtom : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Sigma (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern))
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesExact).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
      r.conclusion (queryOfAtom a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
        W₂ queryOfAtom a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
        W₁ queryOfAtom a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
      (i := .bayesExact) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom queryOfAtom a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_of_interval
    (State := State) (i := .bayesExact) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom := queryOfAtom) (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- Inheritance-sort final-bundle endpoint specialized to Walley IDM semantics. -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_walley
    {State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .walleyIDM)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)} {W₁ W₂ : State}
    (queryOfAtom : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Sigma (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern))
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .walleyIDM).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
      r.conclusion (queryOfAtom a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
        W₂ queryOfAtom a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
        W₁ queryOfAtom a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Pattern)
      (i := .walleyIDM) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom queryOfAtom a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_of_interval
    (State := State) (i := .walleyIDM) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom := queryOfAtom) (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- One-call final-bundle endpoint for linked semantic Solomonoff intensional inheritance.

This endpoint composes:
1. rewrite/query/quantale transport via the generic final-bundle API, and
2. truth transport from the linked semantic Solomonoff theorem family.
-/
noncomputable def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linked_of_interval
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (combine : Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence → Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence)
    (model : SolomonoffAssocLinkedModel (State := State) (Query := Query) enc)
    (hMixed :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.MixedAssocScoreCorrespondence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query) enc combine
        model.scoreModel.assocScore model.scoreModel.scoreToEvidence)
    {W₁ W₂ : State}
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (hW : PLNWorldModel.WMJudgment W₁)
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        W₂ (patternInheritanceQueryOfAtom_mixed enc) a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        W₁ (patternInheritanceQueryOfAtom_mixed enc) a0 p')
    (hPrior : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
      (model.contextOf W₁ a0 p ξ).x
      (model.contextOf W₁ a0 p ξ).Wc)
    (hExt : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
      (model.contextOf W₁ a0 p ξ).x
      (model.contextOf W₁ a0 p ξ).F
      (model.contextOf W₁ a0 p ξ).Wc)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₁ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.scoreModel.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
              (model.contextOf W₁ a0 p ξ).x
              (model.contextOf W₁ a0 p ξ).F
              (model.contextOf W₁ a0 p ξ).Wc /
             Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
              (model.contextOf W₁ a0 p ξ).x
              (model.contextOf W₁ a0 p ξ).Wc) /
            Real.log 2)))))
    (hPriorTarget : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
      (model.contextOf W₂ a0 (m.mapTerm p) ξ).x
      (model.contextOf W₂ a0 (m.mapTerm p) ξ).Wc)
    (hExtTarget : 0 < Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
      (model.contextOf W₂ a0 (m.mapTerm p) ξ).x
      (model.contextOf W₂ a0 (m.mapTerm p) ξ).F
      (model.contextOf W₂ a0 (m.mapTerm p) ξ).Wc)
    (hTauTarget : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₂ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) (m.mapTerm p))
        (model.scoreModel.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
              (model.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.contextOf W₂ a0 (m.mapTerm p) ξ).F
              (model.contextOf W₂ a0 (m.mapTerm p) ξ).Wc /
             Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
              (model.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.contextOf W₂ a0 (m.mapTerm p) ξ).Wc) /
            Real.log 2)))))
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ (patternInheritanceQueryOfAtom_mixed enc) (patternInheritanceQueryOfAtom_mixed enc)
      a0 p coord tau H := by
  letI : PLNWorldModel.WorldModelSigma State Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query) :=
    PLNIntensionalWorldModel.worldModelSigmaInheritanceFromUntyped
      (State := State) (Query := Query)
  let r :
      PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort (Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query) :=
    PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_assocSemantic
      (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
      (Query := Query)
      enc combine model.scoreModel.assocScore model.scoreModel.scoreToEvidence
      hMixed model.scoreModel.assoc_sound
      (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p
  let c₁ := model.contextOf W₁ a0 p ξ
  have hAssocLift₁ :
      PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
        (Query := Query)
        W₁ enc (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
      model.scoreModel.scoreToEvidence
        (Real.log
          (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ c₁.x c₁.F c₁.Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ c₁.x c₁.Wc) /
          Real.log 2) := by
    have hAssocScore₁ :
        model.scoreModel.assocScore W₁
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p =
          Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ c₁.x c₁.F c₁.Wc := by
      simpa [c₁] using model.assocScore_context W₁ a0 p ξ
    have hLog₁ :
        Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ c₁.x c₁.F c₁.Wc =
          Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ c₁.x c₁.F c₁.Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ c₁.x c₁.Wc) /
          Real.log 2 :=
      Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional_eq_log2_ratio ξ c₁.x c₁.F c₁.Wc
        (by simpa [c₁] using hPrior)
        (by simpa [c₁] using hExt)
    calc
      PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query)
          W₁ enc (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p
          = model.scoreModel.scoreToEvidence
              (model.scoreModel.assocScore W₁
                (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p) :=
            model.scoreModel.assoc_sound W₁ (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p
      _ = model.scoreModel.scoreToEvidence (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.intensionalFromConditional ξ c₁.x c₁.F c₁.Wc) := by
            rw [hAssocScore₁]
      _ = model.scoreModel.scoreToEvidence
            (Real.log
              (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ c₁.x c₁.F c₁.Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ c₁.x c₁.Wc) /
              Real.log 2) := by
            rw [hLog₁]
  have hTauScore :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
        (combine
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
            (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
            (Query := Query) W₁ enc
            (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
          (model.scoreModel.scoreToEvidence
            (Real.log
              (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ c₁.x c₁.F c₁.Wc / Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ c₁.x c₁.Wc) /
              Real.log 2)))) := by
    simpa [c₁] using hTau
  have hTauAssoc :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
        (combine
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
            (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
            (Query := Query) W₁ enc
            (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
            (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
            (Query := Query) W₁ enc
            (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p))) := by
    simpa [hAssocLift₁] using hTauScore
  have hDerive :
      r.derive W₁ =
        combine
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
            (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
            (Query := Query) W₁ enc
            (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
          (PLNIntensionalWorldModel.InheritanceQueryBuilder.intensionalAssocEvidence
            (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
            (Query := Query) W₁ enc
            (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p) := by
    simp [r, PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_assocSemantic,
      PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_of_assoc]
  have hTau' :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx (r.derive W₁)) := by
    simpa [hDerive] using hTauAssoc
  have hSide : r.side := by
    simp [r,
      PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_assocSemantic,
      PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_of_assoc]
  have hEq :
      PLNWorldModel.WorldModelSigma.WMQueryEqSigma
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        r.conclusion ((patternInheritanceQueryOfAtom_mixed enc) a0 p) := by
    simpa [r, patternInheritanceQueryOfAtom_mixed,
      PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_assocSemantic,
      PLNIntensionalWorldModel.InheritanceQueryBuilder.mixedRewriteRule_of_assoc] using
      (PLNWorldModel.WorldModelSigma.WMQueryEqSigma.refl
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        ((patternInheritanceQueryOfAtom_mixed enc) a0 p))
  have hBase :=
    end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_of_interval
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      (r := r) (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := patternInheritanceQueryOfAtom_mixed enc)
      (queryOfAtom₂ := patternInheritanceQueryOfAtom_mixed enc)
      (a0 := a0) (p := p) (coord := coord) (tau := tau)
      hSide hW hTau' hEq hVal H
  have hTruthTarget :
      Mettapedia.OSLF.Formula.sem R
        (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
          (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
          (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
          (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W₂ tau coord
          (patternInheritanceQueryOfAtom_mixed enc))
        (.atom a0) (m.mapTerm p) :=
    intensional_mixed_assoc_threshold_atom_of_interval_of_solomonoff_semantic_linked
      (State := State) (Query := Query)
      i R ctx enc combine model hMixed
      W₂ a0 (m.mapTerm p) coord tau ξ hPriorTarget hExtTarget hTauTarget
  exact
    { reachability := hBase.reachability
      quantale_coherence := hBase.quantale_coherence
      truth_transport := by
        intro u
        cases u
        simpa using hTruthTarget }

/-- Strong linked one-call final bundle for Chapter-12 intensional inheritance.

This variant consumes `SolomonoffAssocLinkedModelStrong`, so mixed-channel and
positivity obligations are internalized in the model object. -/
noncomputable def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linkedStrong_of_interval
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : SolomonoffAssocLinkedModelStrong (State := State) (Query := Query) enc)
    {W₁ W₂ : State}
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (hW : PLNWorldModel.WMJudgment W₁)
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        W₂ (patternInheritanceQueryOfAtom_mixed enc) a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        W₁ (patternInheritanceQueryOfAtom_mixed enc) a0 p')
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₁ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
              (model.linked.contextOf W₁ a0 p ξ).x
              (model.linked.contextOf W₁ a0 p ξ).F
              (model.linked.contextOf W₁ a0 p ξ).Wc /
             Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
              (model.linked.contextOf W₁ a0 p ξ).x
              (model.linked.contextOf W₁ a0 p ξ).Wc) /
            Real.log 2)))))
    (hTauTarget : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₂ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) (m.mapTerm p))
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).F
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).Wc /
             Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).Wc) /
            Real.log 2)))))
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ (patternInheritanceQueryOfAtom_mixed enc) (patternInheritanceQueryOfAtom_mixed enc)
      a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linked_of_interval
    (State := State) (Query := Query)
    (i := i) (R := R) (m := m) (ctx := ctx)
    enc model.combine model.linked model.mixed_sound
    (W₁ := W₁) (W₂ := W₂) (a0 := a0) (p := p)
    (coord := coord) (tau := tau) (ξ := ξ)
    hW hVal
    (model.prior_pos W₁ a0 p ξ)
    (model.ext_pos W₁ a0 p ξ)
    hTau
    (model.prior_pos W₂ a0 (m.mapTerm p) ξ)
    (model.ext_pos W₂ a0 (m.mapTerm p) ξ)
    hTauTarget
    H

/-- Bayes-normal selector wrapper for strong linked Chapter-12 final-bundle endpoint. -/
noncomputable def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linkedStrong_bayesNormal
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .bayesNormal)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : SolomonoffAssocLinkedModelStrong (State := State) (Query := Query) enc)
    {W₁ W₂ : State}
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (hW : PLNWorldModel.WMJudgment W₁)
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        W₂ (patternInheritanceQueryOfAtom_mixed enc) a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        W₁ (patternInheritanceQueryOfAtom_mixed enc) a0 p')
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesNormal).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₁ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
              (model.linked.contextOf W₁ a0 p ξ).x
              (model.linked.contextOf W₁ a0 p ξ).F
              (model.linked.contextOf W₁ a0 p ξ).Wc /
             Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
              (model.linked.contextOf W₁ a0 p ξ).x
              (model.linked.contextOf W₁ a0 p ξ).Wc) /
            Real.log 2)))))
    (hTauTarget : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesNormal).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₂ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) (m.mapTerm p))
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).F
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).Wc /
             Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).Wc) /
            Real.log 2)))))
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
      (i := .bayesNormal) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ (patternInheritanceQueryOfAtom_mixed enc) (patternInheritanceQueryOfAtom_mixed enc)
      a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linkedStrong_of_interval
    (State := State) (Query := Query)
    (i := .bayesNormal) (R := R) (m := m) (ctx := ctx)
    enc model
    (W₁ := W₁) (W₂ := W₂) (a0 := a0) (p := p)
    (coord := coord) (tau := tau) (ξ := ξ)
    hW hVal hTau hTauTarget H

/-- Bayes-exact selector wrapper for strong linked Chapter-12 final-bundle endpoint. -/
noncomputable def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linkedStrong_bayesExact
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .bayesExact)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : SolomonoffAssocLinkedModelStrong (State := State) (Query := Query) enc)
    {W₁ W₂ : State}
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (hW : PLNWorldModel.WMJudgment W₁)
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        W₂ (patternInheritanceQueryOfAtom_mixed enc) a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        W₁ (patternInheritanceQueryOfAtom_mixed enc) a0 p')
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesExact).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₁ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
              (model.linked.contextOf W₁ a0 p ξ).x
              (model.linked.contextOf W₁ a0 p ξ).F
              (model.linked.contextOf W₁ a0 p ξ).Wc /
             Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
              (model.linked.contextOf W₁ a0 p ξ).x
              (model.linked.contextOf W₁ a0 p ξ).Wc) /
            Real.log 2)))))
    (hTauTarget : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .bayesExact).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₂ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) (m.mapTerm p))
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).F
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).Wc /
             Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).Wc) /
            Real.log 2)))))
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
      (i := .bayesExact) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ (patternInheritanceQueryOfAtom_mixed enc) (patternInheritanceQueryOfAtom_mixed enc)
      a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linkedStrong_of_interval
    (State := State) (Query := Query)
    (i := .bayesExact) (R := R) (m := m) (ctx := ctx)
    enc model
    (W₁ := W₁) (W₂ := W₂) (a0 := a0) (p := p)
    (coord := coord) (tau := tau) (ξ := ξ)
    hW hVal hTau hTauTarget H

/-- Walley-IDM selector wrapper for strong linked Chapter-12 final-bundle endpoint. -/
noncomputable def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linkedStrong_walley
    {State Query : Type}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.BinaryWorldModel State Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval .walleyIDM)
    (enc : Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder Mettapedia.OSLF.MeTTaIL.Syntax.Pattern Query)
    (model : SolomonoffAssocLinkedModelStrong (State := State) (Query := Query) enc)
    {W₁ W₂ : State}
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (ξ : Mettapedia.UniversalAI.SolomonoffInduction.Semimeasure)
    (hW : PLNWorldModel.WMJudgment W₁)
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        W₂ (patternInheritanceQueryOfAtom_mixed enc) a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
        W₁ (patternInheritanceQueryOfAtom_mixed enc) a0 p')
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .walleyIDM).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₁ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) p)
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
              (model.linked.contextOf W₁ a0 p ξ).x
              (model.linked.contextOf W₁ a0 p ξ).F
              (model.linked.contextOf W₁ a0 p ξ).Wc /
             Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
              (model.linked.contextOf W₁ a0 p ξ).x
              (model.linked.contextOf W₁ a0 p ξ).Wc) /
            Real.log 2)))))
    (hTauTarget : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval .walleyIDM).eval ctx
      (model.combine
        (PLNIntensionalWorldModel.InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
          (Query := Query) W₂ enc
          (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar a0) (m.mapTerm p))
        (model.linked.scoreModel.scoreToEvidence
          (Real.log
            (Mettapedia.KR.ConceptGeometry.IntensionalInheritance.extensionalFromConditional ξ
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).F
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).Wc /
             Mettapedia.KR.ConceptGeometry.IntensionalInheritance.priorFromConditional ξ
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).x
              (model.linked.contextOf W₂ a0 (m.mapTerm p) ξ).Wc) /
            Real.log 2)))))
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceSort) (Query := Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryFamily Query)
      (i := .walleyIDM) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ (patternInheritanceQueryOfAtom_mixed enc) (patternInheritanceQueryOfAtom_mixed enc)
      a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_inheritance_solomonoff_semantic_linkedStrong_of_interval
    (State := State) (Query := Query)
    (i := .walleyIDM) (R := R) (m := m) (ctx := ctx)
    enc model
    (W₁ := W₁) (W₂ := W₂) (a0 := a0) (p := p)
    (coord := coord) (tau := tau) (ξ := ξ)
    hW hVal hTau hTauTarget H

/-! ## Event Calculus (Chapter 14) canonical endpoints -/

/-- Event-calculus one-call bundle endpoint (generic query encoder). -/
theorem end_to_end_quantale_selector_rewrite_query_threshold_bundle_event_of_interval
    {State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily} {W₁ W₂ : State}
    (queryOfAtom : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
      r.conclusion (queryOfAtom a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
        W₂ queryOfAtom a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
        W₁ queryOfAtom a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdBundle
      (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom queryOfAtom a0 p coord tau H := by
  exact end_to_end_quantale_selector_rewrite_query_threshold_bundle_of_interval
    (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
    (i := i) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom) (queryOfAtom₂ := queryOfAtom)
    (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- Event-calculus one-call final-bundle endpoint (generic query encoder). -/
def end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_event_of_interval
    {State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    {r : PLNWorldModel.WorldModelSigma.WMRewriteRuleSigma State Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily} {W₁ W₂ : State}
    (queryOfAtom : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : PLNWorldModel.WMJudgment W₁)
    (hTau : tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : PLNWorldModel.WorldModelSigma.WMQueryEqSigma
      (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
      r.conclusion (queryOfAtom a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
        W₂ queryOfAtom a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
        W₁ queryOfAtom a0 p')
    (H : Finset (Unit × Unit)) :
    EndToEndQuantaleSelectorRewriteQueryThresholdFinalBundle
      (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₁ W₂ queryOfAtom queryOfAtom a0 p coord tau H :=
  end_to_end_quantale_selector_rewrite_query_threshold_finalBundle_of_interval
    (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
    (i := i) (R := R) (m := m) (ctx := ctx)
    (r := r) (W₁ := W₁) (W₂ := W₂)
    (queryOfAtom₁ := queryOfAtom) (queryOfAtom₂ := queryOfAtom)
    (a0 := a0) (p := p) (coord := coord) (tau := tau)
    hSide hW hTau hEq hVal H

/-- Temporal-hypercube one-call bundle for event queries:
composes GSLT forward transport on `Mettapedia.OSLF.Framework.VertexTemporalRewriteRules.vertexTemporalLanguageDef`, quantale
coherence transport, and Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV-threshold atom truth transport. -/
theorem end_to_end_temporal_hypercube_event_threshold_bundle_of_interval
    {State : Type*}
    [EvidenceClass.EvidenceType State]
    [PLNWorldModel.WorldModelSigma State Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily]
    {v w : Mettapedia.ProbabilityTheory.Hypercube.ProbabilityVertex}
    (hvw : v ≤ w)
    (f : Mettapedia.Algebra.QuantaleWeakness.QuantaleHom
      (Mettapedia.ProbabilityTheory.Hypercube.QuantaleSemantics.semanticsOfVertex w).Q
      (Mettapedia.ProbabilityTheory.Hypercube.QuantaleSemantics.semanticsOfVertex v).Q)
    (srcVal : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      (Mettapedia.ProbabilityTheory.Hypercube.QuantaleSemantics.semanticsOfVertex w).Q)
    (dstVal : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      (Mettapedia.ProbabilityTheory.Hypercube.QuantaleSemantics.semanticsOfVertex v).Q)
    (hValWeak : ∀ p, dstVal p = f (srcVal p))
    {U : Type*} [Fintype U]
    (pick : U → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    {p₀ : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (hReach : ∀ u,
      Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar
        (Mettapedia.OSLF.Framework.VertexTemporalRewriteRules.vertexTemporalLanguageDef w) p₀ (pick u))
    (H : Finset (U × U))
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (ctx : Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
    (W₁ W₂ : State)
    (queryOfAtom : String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Sigma Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
    (a0 : String)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hITV : ∀ p,
      (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
          W₂ queryOfAtom a0 p) =
      (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
          W₁ queryOfAtom a0 p))
    (hTau : ∀ u,
      tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
        (PLNWMOSLFBridgeITVTyped.wmPatternValuation
          (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
          W₁ queryOfAtom a0 (pick u)))) :
    (∀ u,
      Mettapedia.OSLF.Framework.LangMorphism.LangReducesStar
        (Mettapedia.OSLF.Framework.VertexTemporalRewriteRules.vertexTemporalLanguageDef v) p₀ (pick u)) ∧
    f (Mettapedia.Algebra.QuantaleWeakness.weakness
      (Mettapedia.OSLF.Framework.QuantaleCoherence.sourceWeight srcVal pick) H) =
      Mettapedia.Algebra.QuantaleWeakness.weakness
        (Mettapedia.OSLF.Framework.QuantaleCoherence.targetWeight dstVal id pick) H ∧
    (∀ u,
      Mettapedia.OSLF.Formula.sem R
        (PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma
          (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
          (Ctx := Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.CtxOfInterval i)
          (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W₂ tau coord queryOfAtom)
        (.atom a0) (pick u)) := by
  rcases Mettapedia.OSLF.Framework.QuantaleCoherence.hypercube_forward_quantale_coherence_bundle_temporal
      (v := v) (w := w)
      hvw f srcVal dstVal hValWeak pick (p₀ := p₀) hReach H with ⟨hForward, hWeak⟩
  refine ⟨hForward, hWeak, ?_⟩
  intro u
  have hEq : (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
        W₂ queryOfAtom a0 (pick u)) =
    (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
        W₁ queryOfAtom a0 (pick u)) := hITV (pick u)
  have hTauW₂ :
      tau ≤ coord
        (PLNWorldModel.WorldModelSigma.queryITV
          (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
          (Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i) ctx W₂ (queryOfAtom a0 (pick u))) := by
    change tau ≤ coord ((Mettapedia.PLN.WorldModel.PLNWorldModelITVHypercube.semanticsOfInterval i).eval ctx
      (PLNWMOSLFBridgeITVTyped.wmPatternValuation
        (State := State) (Srt := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.EventCalcSort) (Query := Mettapedia.PLN.RuleFamilies.Temporal.PLNProbabilisticEventCalculus.PatternEventQueryFamily)
        W₂ queryOfAtom a0 (pick u)))
    simpa [hEq] using hTau u
  simpa [Mettapedia.OSLF.Formula.sem, Mettapedia.OSLF.Formula.semEnv,
    PLNWMOSLFBridgeITVTyped.thresholdAtomSemOfWMITVQSigma,
    PLNWMOSLFBridgeITVTyped.wmITVAtomSemQSigma] using hTauW₂

/-! ## OSLF Bridge canonical aliases -/

/-! ## Derived BN Rules (canonical — no free side-condition hypotheses)

Fully derived PLN inference rules for BN structures. All side conditions
are derived from local Markov + d-separation — no free `hSO` arguments.

Import `Mettapedia.PLN.RuleFamilies.FirstOrder.PLNXiDerivedBNRules` and use directly:

### Deduction: Chain BN (A→B→C) — §1

**Tier A**: BN-PLN (structural, d-sep + local Markov → admissible rewrite)
- `ChainBNLocalMarkovAll` — type alias for the local Markov hypothesis
- `xi_deduction_rewrite_of_chainBN` — PLNWorldModel.WMRewriteRule (NO free hSO)
- `xi_deduction_admissible_of_chainBN` — query judgment from derivable WM state
- `xi_deduction_semE_atom_of_chainBN` — OSLF evidence = derived evidence
- `xi_deduction_threshold_of_chainBN` — threshold Prop from strength bound
- `xi_deduction_strength_eq_of_chainBN` — linkCond strength = link strength

**Tier A→B Composition** (end-to-end queryStrength → plnDeductionStrength)
- `xi_deduction_queryStrength_eq_plnDeduction_of_chainBN` — for singleton CPT state:
  `(queryStrength {cpt} (link A C)).toReal = plnDeductionStrength(P(B|A), P(C|B), P(B), P(C))`
  Consumes: singleton bridge + VEBridge + Tier B.

**Tier B**: Bernoulli-PLN (measure → formula bridge)
- `toStrength_evidenceOfProb` — `Mettapedia.PLN.Evidence.EvidenceQuantale.BinaryEvidence.toStrength ∘ evidenceOfProb = id` (for p ≤ 1)
- `xi_deduction_plnStrength_exact_of_chainBN` — P(C|A) = plnDeductionStrength(...)

**Tier C**: Beta-Bernoulli (computable from evidence counts)
- `plnStrength_lt_one` — `s_B < 1` when `nB_neg ≠ 0` (denominator safety)
- `plnDeductionStrength_denom_pos` — `0 < 1 - s_B` (denominator positivity)
- `plnDeductionStrength_of_plnStrength` — unfolds plnStrength in deduction formula
- `plnDeductionStrength_of_plnStrength_full` — all four arguments unfolded
- `evidence_hplus_is_conjugate` — Beta conjugate update for evidence aggregation

**Guardrail**: Beta is a modeling choice, not forced by exchangeability.
See `EvidenceBeta.not_beta_from_exchangeability_example`.

### Source Rule (Induction): Fork BN (A←B→C) — §4

**Tier A**: BN-PLN (structural, d-sep + local Markov → admissible rewrite)
- `ForkBNLocalMarkovAll` — type alias for the local Markov hypothesis
- `xi_sourceRule_rewrite_of_forkBN` — PLNWorldModel.WMRewriteRule (NO free hSO)
- `xi_sourceRule_admissible_of_forkBN` — query judgment from derivable WM state
- `xi_sourceRule_semE_atom_of_forkBN` — OSLF evidence = derived evidence
- `xi_sourceRule_threshold_of_forkBN` — threshold Prop from strength bound
- `xi_sourceRule_strength_eq_of_forkBN` — linkCond strength = link strength

The fork BN has edges B→A and B→C. The source rule derives link A→C from
links B→A and B→C via the same conditional independence A ⊥ C | B. The
screening-off PLNWorldModel.WMQueryEq has the same form as the chain BN deduction case;
the structural difference is the BN graph topology.

**Tier A→B Composition** (end-to-end queryStrength → plnInductionStrength)
- `xi_source_queryStrength_eq_plnInduction_of_forkBN` — for singleton CPT state:
  `(queryStrength {cpt} (link A C)).toReal = plnInductionStrength(P(A|B), P(C|B), P(A), P(B), P(C))`
  Uses `bayesInversion(P(A|B), P(A), P(B)) = P(B|A)` + fork screening-off + PLN deduction formula.
  Consumes: `forkBN_plnDeductionStrength_exact` (PLNBayesNetFastRules).

**Tier B**: Bernoulli-PLN (measure → formula bridge)
- `forkBN_plnDeductionStrength_exact` — P(C|A) = plnDeductionStrength(P(B|A), P(C|B), P(B), P(C))
  from CondIndepVertices (local Markov at C). ~30 lines vs ~900 for chain case.
- `forkBN_pos_screeningOff` / `forkBN_neg_screeningOff` — screening-off from CondIndepVertices
  via `condIndep_eventEq_mul_cond` + `real_ratio_of_ennreal_mul_eq`

### Sink Rule (Abduction): Collider BN (A→C←B) — §5

**Tier A**: BN-PLN (structural, d-sep + local Markov → admissible rewrite)
- `ColliderBNLocalMarkovAll` — type alias for the local Markov hypothesis
- `xi_sinkRule_rewrite_of_colliderBN` — PLNWorldModel.WMRewriteRule (NO free hSO)
- `xi_sinkRule_admissible_of_colliderBN` — query judgment from derivable WM state
- `xi_sinkRule_semE_atom_of_colliderBN` — OSLF evidence = derived evidence
- `xi_sinkRule_threshold_of_colliderBN` — threshold Prop from strength bound
- `xi_sinkRule_strength_eq_of_colliderBN` — link strength = prop strength

The collider BN has edges A→C and B→C. The sink rule derives link A→B from
links A→C and B→C. The side condition is marginal independence A ⊥ B | ∅,
which holds because A and B have no active path when C is not conditioned on.

Variable mapping: (A_rule, B_rule, C_rule) = (Three.A, Three.C, Three.B).
Sink center = Three.C. The PLNWorldModel.WMQueryEq rewrites `link ⟨A,valA⟩ ⟨B,valB⟩`
to `prop ⟨B,valB⟩` (marginal independence: P(B|A) = P(B)).

These require BN instances (Fintype, DecidableEq, etc.) which are
provided by `open Mettapedia.ProbabilityTheory.BayesianNetworks.Examples`.

**Tier A→B Composition: NOT EXACT (approximation)**
- `plnAbductionStrength_not_exact_collider` — counterexample showing PLN abduction
  formula gives 2/3 ≠ 1/2 for an OR-gate collider. The PLN abduction formula
  requires B ⊥ A | C, but conditioning on the collider C *opens* the explaining-away
  path, making A and B dependent given C.

### Generic tools (§6)

- `real_ratio_of_ennreal_mul_eq` — convert ENNReal multiplicative screening-off
  `a * d = b * c` to `.real` ratio form `a/b = c/d` (PLNBayesNetFastRules)
- `eventEq_false_eq_compl_true_of_bool` — Bool complement bridge for event sets (EventSets) -/

/-! ## Schema namespace

Rule templates parameterized by abstract side conditions. These are building
blocks for constructing new derived rules from other BN structures (fork,
collider, etc.), NOT standalone inference rules.

To build a derived rule from a schema template:
1. Prove the side condition from your model semantics
2. Instantiate the schema with the proved side condition
3. Add admissibility + OSLF bridge theorems
4. Export the derived rule (not the schema) as canonical -/

namespace Schema

/-! ### Screening-off side condition templates -/

/-! ### Carrier family template -/

end Schema

/-! ## Exactness Matrix

Summary of formula-level exactness across BN topologies:

| Rule | BN Topology | Tier A (WM/OSLF) | Tier A→B (formula) | Notes |
|------|-------------|-------------------|---------------------|-------|
| Deduction | Chain A→B→C | exact | exact | `plnDeductionStrength` via total probability + C ⊥ A given B |
| Source/Induction | Fork A←B→C | exact | exact | `plnInductionStrength` = Bayes inversion + deduction; C ⊥ A given B holds |
| Sink/Abduction | Collider A→C←B | exact (marginal) | **NOT exact** | Structural: P(B given A) = P(B); formula: explaining-away violates B ⊥ A given C |

### Key theorems

- Chain exact: `chainBN_plnDeductionStrength_exact` (`PLNBayesNetFastRules`)
- Fork exact (measure): `forkBN_plnDeductionStrength_exact` (`PLNBayesNetFastRules`)
- Fork exact (queryStrength): `xi_source_queryStrength_eq_plnInduction_of_forkBN` (`PLNXiDerivedBNRules`)
- Collider structural exact: `xi_sinkRule_strength_eq_of_colliderBN` (`PLNXiDerivedBNRules`)
- Collider .toReal exact: `xi_sink_queryStrength_toReal_eq_of_colliderBN` (`PLNXiDerivedBNRules`)
- Collider singleton short-name re-exports:
  `sinkLinkEqPropToReal`, `singletonPropToReal` (`PLNColliderSingletonBridge`)
- Collider formula counterexample: `plnAbductionStrength_not_exact_collider` (`PLNXiDerivedBNRules`)
- Error framework: `Comparison/ErrorCharacterization.lean` (decomposition + bounds + decision criteria)

### When is a PLN rule exact?

A PLN rule is exact when its internal screening-off assumption holds:
- **Deduction/Source**: requires C ⊥ A | B (holds in chain and fork by d-separation)
- **Abduction**: requires B ⊥ A | C (FAILS in collider: conditioning on C opens the explaining-away path)

The `ErrorCharacterization` module provides quantitative bounds on the error when
screening-off is violated (`error_bound_by_max_violation`, `conservative_estimate_is_bound`).

### Collider singleton composition pattern

Use this exact two-step composition:
```lean
have h1 := PLNColliderSingletonBridge.sinkLinkEqPropToReal
  valA valB hPos hLMarkov hDSep ({cpt} : BNWorldModel.State (bn := colliderBN))
have h2 := PLNColliderSingletonBridge.singletonPropToReal
  cpt Three.B valB
exact Eq.trans h1 h2
```
-/

/-! ## End-to-End Theorems (BN → WM → OSLF)

The proved BN, WM and OSLF links, by their own names.

### Formula exactness
- `PLNXiDerivedBNRules.xi_deduction_queryStrength_eq_plnDeduction_of_chainBN`
- `PLNXiDerivedBNRules.xi_source_queryStrength_eq_plnInduction_of_forkBN`

### Admissibility + OSLF bridge
- `PLNXiDerivedBNRules.xi_deduction_admissible_of_chainBN`, `PLNXiDerivedBNRules.xi_deduction_semE_atom_of_chainBN`, `PLNXiDerivedBNRules.xi_deduction_threshold_of_chainBN`
- `PLNXiDerivedBNRules.xi_sourceRule_admissible_of_forkBN`, `PLNXiDerivedBNRules.xi_sourceRule_semE_atom_of_forkBN`, `PLNXiDerivedBNRules.xi_sourceRule_threshold_of_forkBN`
- `PLNXiDerivedBNRules.xi_sinkRule_admissible_of_colliderBN`, `PLNXiDerivedBNRules.xi_sinkRule_semE_atom_of_colliderBN`, `PLNXiDerivedBNRules.xi_sinkRule_threshold_of_colliderBN`

### Collider split
- `PLNXiDerivedBNRules.xi_sinkRule_strength_eq_of_colliderBN`, `PLNXiDerivedBNRules.xi_sink_queryStrength_toReal_eq_of_colliderBN`
- `PLNXiDerivedBNRules.plnAbductionStrength_not_exact_collider`
- `PLNXiDerivedBNRules.plnAbductionStrength_exact_of_screeningOff`
- Singleton composition helpers: `PLNColliderSingletonBridge.sinkLinkEqPropToReal`,
  `PLNColliderSingletonBridge.singletonPropToReal`

### Generic context lifts
- `PLNWorldModel.WMRewriteRule.applyCtx`
- `PLNWMOSLFBridge.xiDerivesAtomEvidence_sound_ctx`
- `PLNWMOSLFBridge.xiDerivesAtomStrength_threshold_sound_ctx`
- `PLNWMOSLFBridge.xi_atom_revision_ctx`
-/

end Mettapedia.PLN.Core.PLNCanonical
