import Mettapedia.PLN.Core.PLNCanonicalAPI
import Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlExamples
import Mettapedia.PLN.RuleFamilies.FirstOrder.PLNXiDerivedBNRules

/-!
# Selector→Rewrite→Threshold Worked Examples

Concrete worked fixtures for the composed selector/rewrite/threshold API path.
-/

namespace Mettapedia.PLN.InferenceControl.SelectorRewriteThreshold.PLNSelectorRewriteThresholdExamples

open Mettapedia.PLN.Core.PLNCanonicalAPI
open Mettapedia.PLN.Bridges.Languages
open Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlExamples

noncomputable section

/-- Concrete selector fixture (`Bool`, `topK = 1`) composed with the generic
rewrite→OSLF→threshold endpoint in one theorem.

The selector side is fully concrete (Chapter-13 worked fixture); the rewrite/OSLF
side remains generic so this theorem can be instantiated in any WM/OSLF setting. -/
theorem bool_selector_rewrite_threshold_end_to_end_fixture
    {State Srt : Type*} {Query : Srt → Type*}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [Mettapedia.PLN.WorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.WorldModelITVHypercube.CtxOfInterval i)
    {r : Mettapedia.PLN.WorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : Mettapedia.PLN.WorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.WorldModelITVHypercube.semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : Mettapedia.PLN.WorldModel.WorldModelSigma.WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITV.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITV.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p')
    (selectorWitness : Finset Bool → Finset (Unit × Unit)) :
    let G := Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlAlgorithms.greedySelect
      dependencyBool checklistBool.topK
    (checklistBool.topK ≤ Fintype.card Bool
      ∧ (∀ g' f',
          0 ≤ (Mettapedia.PLN.InferenceControl.PremiseSelection.selectorDefaults_halfGate Bool Bool).gate g' f'
            ∧ (Mettapedia.PLN.InferenceControl.PremiseSelection.selectorDefaults_halfGate Bool Bool).gate g' f' ≤ 1)
      ∧ Mettapedia.PLN.InferenceControl.PremiseSelection.Optimality.BayesOptimalRanking etaBool
          (Mettapedia.PLN.InferenceControl.PremiseSelection.Optimality.perturbedScore
            (Mettapedia.PLN.InferenceControl.PremiseSelection.PLNInferenceControlCore.pooledSelectorScore globalPriorBool localPriorBool likelihoodBool true)
            deltaZero)
      ∧ (1 - Real.exp (-1)) * (Nat.min checklistBool.topK dependencyBool.card : ℝ) ≤
          Mettapedia.PLN.InferenceControl.PremiseSelection.dependencyCoverage dependencyBool G)
      ∧ thresholdAccepted
          (State := State) (Srt := Srt) (Query := Query)
          (i := i) (R := R) (m := m) (ctx := ctx)
          W₂ queryOfAtom₂ a0 p coord tau := by
  simpa [deltaZero] using
    (selector_rewrite_threshold_end_to_end_of_interval
      (A := checklistBool)
      (η := etaBool)
      (globalPrior := globalPriorBool)
      (localPrior := localPriorBool)
      (likelihood := likelihoodBool)
      (g := true)
      localExchangeabilityBool
      (δ := deltaZero) (ε := 0)
      twoStageRankingBool
      (hbound := by intro x; simp [deltaZero])
      (hmargin := marginBool)
      (htie := by intro x y hxy; simp [deltaZero])
      (D := dependencyBool)
      (i := i) (R := R) (m := m) (ctx := ctx)
      (r := r) (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (p := p) (coord := coord) (tau := tau)
      hSide hW hTau hEq hVal selectorWitness)

/-- Concrete Chapter-8 acceptance fixture:
instantiate the selector-witness channel with a fixed finite witness and project
the threshold-acceptance component from the composed selector/rewrite theorem. -/
theorem thresholdAccepted_bool_selector_fixture
    {State Srt : Type*} {Query : Srt → Type*}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [Mettapedia.PLN.WorldModel.WorldModelSigma State Srt Query]
    {L₁ L₂ : Mettapedia.OSLF.MeTTaIL.Syntax.LanguageDef}
    (i : Mettapedia.OSLF.Framework.PLNWMHypercubeBasis.WMIntervalSemantics)
    (R : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern →
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Prop)
    (m : Mettapedia.OSLF.Framework.LangMorphism.LanguageMorphism L₁ L₂ Eq)
    (ctx : Mettapedia.PLN.WorldModel.WorldModelITVHypercube.CtxOfInterval i)
    {r : Mettapedia.PLN.WorldModel.WorldModelSigma.WMRewriteRuleSigma State Srt Query} {W₁ W₂ : State}
    (queryOfAtom₁ queryOfAtom₂ :
      String → Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Sigma Query)
    (a0 : String)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (coord : Mettapedia.PLN.TruthValues.PLNIndefiniteTruth.ITV → ℝ) (tau : ℝ)
    (hSide : r.side) (hW : Mettapedia.PLN.WorldModel.WMJudgment W₁)
    (hTau :
      tau ≤ coord ((Mettapedia.PLN.WorldModel.WorldModelITVHypercube.semanticsOfInterval i).eval ctx (r.derive W₁)))
    (hEq : Mettapedia.PLN.WorldModel.WorldModelSigma.WMQueryEqSigma (State := State) (Srt := Srt) (Query := Query)
      r.conclusion (queryOfAtom₁ a0 p))
    (hVal : ∀ p',
      PLNWMOSLFBridgeITV.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₂ queryOfAtom₂ a0 (m.mapTerm p') =
      PLNWMOSLFBridgeITV.wmPatternValuation
        (State := State) (Srt := Srt) (Query := Query) W₁ queryOfAtom₁ a0 p') :
    thresholdAccepted
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      W₂ queryOfAtom₂ a0 p coord tau := by
  exact
    (bool_selector_rewrite_threshold_end_to_end_fixture
      (State := State) (Srt := Srt) (Query := Query)
      (i := i) (R := R) (m := m) (ctx := ctx)
      (r := r) (W₁ := W₁) (W₂ := W₂)
      (queryOfAtom₁ := queryOfAtom₁) (queryOfAtom₂ := queryOfAtom₂)
      (a0 := a0) (p := p) (coord := coord) (tau := tau)
      hSide hW hTau hEq hVal
      (selectorWitness := fun _ => ({((), ())} : Finset (Unit × Unit)))).2

end

end Mettapedia.PLN.InferenceControl.SelectorRewriteThreshold.PLNSelectorRewriteThresholdExamples
