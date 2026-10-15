import Mettapedia.GSLT.Causality.DoCalculus.Derivation
import Mettapedia.GSLT.Causality.DoCalculus.LatentMargin

/-!
# Front door inside the derivation tree

On the smoking graph the interventional query `P(c | do(s))` rewrites, by the
authored rules, to a do-free expression. Under the positivity that derivation
collects, and the positive smoking and tar rows of `frontDoor`, that
expression denotes `frontDoorOf`. The formula reads the joint only through
the margin of `S, T, C`, so the query `Factors` through that margin.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation
open Mettapedia.GSLT.Core.NonFactorization
open scoped BigOperators ENNReal

/-- The smoking coordinate. -/
def smokeS : Finset Smoke := {Smoke.s}

/-- The tar coordinate. -/
def smokeT : Finset Smoke := {Smoke.t}

/-- The cancer coordinate. -/
def smokeC : Finset Smoke := {Smoke.c}

/-- `P(t | do(s))` exchanges to `P(t | s)`. -/
theorem smoke_tar_given_smoking_checked :
    FiniteDSeparation.check (gout smokeGraph (∅ : Finset Smoke) smokeS)
      (rule2Profile smokeT smokeS ((∅ : Finset Smoke) ∪ ∅)) = true := by
  decide

/-- `P(c | do(s))` accepts an added `do(t)`. -/
theorem smoke_add_tar_checked :
    FiniteDSeparation.check (gout smokeGraph smokeS smokeT)
      (rule2Profile smokeC smokeT (smokeS ∪ (∅ : Finset Smoke))) = true := by
  decide

/-- `P(c | do(t), do(s))` drops `do(s)`. -/
theorem smoke_delete_smoking_checked :
    FiniteDSeparation.check (rule3Graph smokeGraph smokeT smokeS (∅ : Finset Smoke))
      (rule3Profile smokeC smokeS (smokeT ∪ (∅ : Finset Smoke))) = true := by
  decide

/-- `P(s | do(t))` drops `do(t)`. -/
theorem smoke_delete_tar_checked :
    FiniteDSeparation.check (rule3Graph smokeGraph (∅ : Finset Smoke) smokeT (∅ : Finset Smoke))
      (rule3Profile smokeS smokeT ((∅ : Finset Smoke) ∪ ∅)) = true := by
  decide

/-- `P(c | do(t), s)` exchanges to `P(c | t, s)`. -/
theorem smoke_cancer_given_tar_checked :
    FiniteDSeparation.check (gout smokeGraph (∅ : Finset Smoke) smokeT)
      (rule2Profile smokeC smokeT ((∅ : Finset Smoke) ∪ smokeS)) = true := by
  decide

/-- Two conditional expressions with the same three coordinate sets. -/
lemma cond_eq_of_sets {i n d i' n' d' : Finset Smoke}
    (hi : i = i') (hn : n = n') (hd : d = d') :
    (MassExpr.cond i n d : MassExpr Smoke) = .cond i' n' d' := by
  cases hi
  cases hn
  cases hd
  rfl

/-- `P(c | do(s))`, with the cancer and smoking coordinates in the numerator. -/
def smokingQuery : MassExpr Smoke :=
  .cond smokeS (smokeC ∪ smokeS) smokeS

def smokingMarginalSource : MassExpr Smoke :=
  .cond smokeS (smokeS ∪ smokeC ∪ (∅ : Finset Smoke)) (smokeS ∪ ∅)

theorem smokingQuery_eq_marginalSource :
    smokingQuery = smokingMarginalSource := by
  unfold smokingQuery smokingMarginalSource
  refine cond_eq_of_sets rfl ?_ ?_
  · ext v; cases v <;> simp [smokeS, smokeC]
  · ext v; cases v <;> simp [smokeS]

/-- Sum over tar of `P(c, t | do(s))`. -/
def smokingOpened : MassExpr Smoke :=
  .sum smokeT
    (.cond smokeS (smokeS ∪ smokeC ∪ smokeT ∪ (∅ : Finset Smoke)) (smokeS ∪ ∅))

def openSmoking : Deriv smokeGraph smokingMarginalSource smokingOpened :=
  .marginalIntro smokeS smokeC smokeT ∅
    (by
      rw [Finset.disjoint_left]
      intro v hv
      simp only [smokeT, smokeS, Finset.mem_singleton] at hv ⊢
      subst hv
      decide)
    (by
      rw [Finset.disjoint_left]
      intro v hv
      simp only [smokeT, smokeC, Finset.mem_singleton] at hv ⊢
      subst hv
      decide)
    (Finset.disjoint_empty_right _)

/-- Chain splits that summand into `P(c | do(s), t) P(t | do(s))`. -/
def smokingChainedBody : MassExpr Smoke :=
  .mul
    (.cond smokeS (smokeS ∪ smokeC ∪ smokeT ∪ (∅ : Finset Smoke)) (smokeS ∪ smokeT ∪ ∅))
    (.cond smokeS (smokeS ∪ smokeT ∪ (∅ : Finset Smoke)) (smokeS ∪ ∅))

def chainSmokingBody :
    Deriv smokeGraph
      (.cond smokeS (smokeS ∪ smokeC ∪ smokeT ∪ (∅ : Finset Smoke)) (smokeS ∪ ∅))
      smokingChainedBody :=
  .chain smokeS smokeC smokeT ∅

def smokingChained : MassExpr Smoke :=
  .sum smokeT smokingChainedBody

def chainSmoking : Deriv smokeGraph smokingOpened smokingChained :=
  .sumBody chainSmokingBody

def tarGivenSmokeSource : MassExpr Smoke :=
  .cond ((∅ : Finset Smoke) ∪ smokeS)
    (∅ ∪ smokeT ∪ smokeS ∪ ∅)
    (∅ ∪ smokeS ∪ ∅)

def tarGivenSmoke : MassExpr Smoke :=
  .cond (∅ : Finset Smoke)
    ((∅ : Finset Smoke) ∪ smokeT ∪ smokeS ∪ ∅)
    (∅ ∪ smokeS ∪ ∅)

theorem smoking_right_eq_rule2_source :
    (.cond smokeS (smokeS ∪ smokeT ∪ (∅ : Finset Smoke)) (smokeS ∪ ∅)) =
      tarGivenSmokeSource := by
  unfold tarGivenSmokeSource
  refine cond_eq_of_sets ?_ ?_ ?_
  · ext v; cases v <;> simp [smokeS]
  · ext v; cases v <;> simp [smokeS, smokeT]
  · ext v; cases v <;> simp [smokeS]

def exchangeTar : Deriv smokeGraph tarGivenSmokeSource tarGivenSmoke :=
  .rule2 ∅ smokeT smokeS ∅ smoke_tar_given_smoking_checked

def exchangeTarFromRight :
    Deriv smokeGraph
      (.cond smokeS (smokeS ∪ smokeT ∪ (∅ : Finset Smoke)) (smokeS ∪ ∅))
      tarGivenSmoke :=
  .rewriteEq smoking_right_eq_rule2_source.symm rfl exchangeTar

def afterTarExchange : MassExpr Smoke :=
  .sum smokeT
    (.mul
      (.cond smokeS (smokeS ∪ smokeC ∪ smokeT ∪ (∅ : Finset Smoke)) (smokeS ∪ smokeT ∪ ∅))
      tarGivenSmoke)

def stepTarExchange : Deriv smokeGraph smokingChained afterTarExchange :=
  .sumBody (.mulRight exchangeTarFromRight)

def cancerDoBoth : MassExpr Smoke :=
  .cond (smokeS ∪ smokeT)
    (smokeS ∪ smokeC ∪ smokeT ∪ (∅ : Finset Smoke))
    (smokeS ∪ smokeT ∪ ∅)

def addTar :
    Deriv smokeGraph
      (.cond smokeS (smokeS ∪ smokeC ∪ smokeT ∪ (∅ : Finset Smoke)) (smokeS ∪ smokeT ∪ ∅))
      cancerDoBoth :=
  .rule2Rev smokeS smokeC smokeT ∅ smoke_add_tar_checked

def cancerAbsorbSource : MassExpr Smoke :=
  .cond (smokeS ∪ smokeT)
    ((smokeT ∪ smokeC ∪ (∅ : Finset Smoke)) ∪ smokeS)
    ((smokeT ∪ ∅) ∪ smokeS)

def cancerDoBothDropped : MassExpr Smoke :=
  .cond (smokeS ∪ smokeT) (smokeT ∪ smokeC ∪ (∅ : Finset Smoke)) (smokeT ∪ ∅)

theorem cancerDoBoth_eq_absorb_source :
    cancerDoBoth = cancerAbsorbSource := by
  unfold cancerDoBoth cancerAbsorbSource
  refine cond_eq_of_sets rfl ?_ ?_
  · ext v; cases v <;> simp [smokeS, smokeT, smokeC]
  · ext v; cases v <;> simp [smokeS, smokeT]

def dropSmokingCoords :
    Deriv smokeGraph cancerAbsorbSource cancerDoBothDropped :=
  .absorb (smokeS ∪ smokeT) (smokeT ∪ smokeC ∪ (∅ : Finset Smoke)) (smokeT ∪ ∅) smokeS
    (fun _ hv => Finset.mem_union_left _ hv)

def cancerRule3Source : MassExpr Smoke :=
  .cond (smokeT ∪ smokeS) (smokeT ∪ smokeC ∪ (∅ : Finset Smoke)) (smokeT ∪ ∅)

/-- `P(c | do(t))`. -/
def cancerDoTar : MassExpr Smoke :=
  .cond smokeT (smokeT ∪ smokeC ∪ (∅ : Finset Smoke)) (smokeT ∪ ∅)

theorem cancerDropped_eq_rule3_source :
    cancerDoBothDropped = cancerRule3Source := by
  unfold cancerDoBothDropped cancerRule3Source
  refine cond_eq_of_sets ?_ rfl rfl
  · ext v; cases v <;> simp [smokeS, smokeT]

def deleteSmoking : Deriv smokeGraph cancerRule3Source cancerDoTar :=
  .rule3 smokeT smokeC smokeS ∅ smoke_delete_smoking_checked

def leftToCancerDoTar :
    Deriv smokeGraph
      (.cond smokeS (smokeS ∪ smokeC ∪ smokeT ∪ (∅ : Finset Smoke)) (smokeS ∪ smokeT ∪ ∅))
      cancerDoTar :=
  .trans addTar
    (.trans
      (.rewriteEq cancerDoBoth_eq_absorb_source.symm rfl dropSmokingCoords)
      (.rewriteEq cancerDropped_eq_rule3_source.symm rfl deleteSmoking))

def afterCancerDoTar : MassExpr Smoke :=
  .sum smokeT (.mul cancerDoTar tarGivenSmoke)

def stepCancer : Deriv smokeGraph afterTarExchange afterCancerDoTar :=
  .sumBody (.mulLeft leftToCancerDoTar)

def cancerSumSmoke : MassExpr Smoke :=
  .sum smokeS
    (.cond smokeT (smokeT ∪ smokeC ∪ smokeS ∪ (∅ : Finset Smoke)) (smokeT ∪ ∅))

def introSmoke : Deriv smokeGraph cancerDoTar cancerSumSmoke :=
  .marginalIntro smokeT smokeC smokeS ∅
    (by
      rw [Finset.disjoint_left]
      intro v hv
      simp only [smokeS, smokeT, Finset.mem_singleton] at hv ⊢
      subst hv
      decide)
    (by
      rw [Finset.disjoint_left]
      intro v hv
      simp only [smokeS, smokeC, Finset.mem_singleton] at hv ⊢
      subst hv
      decide)
    (Finset.disjoint_empty_right _)

def cancerLeft : MassExpr Smoke :=
  .cond smokeT (smokeT ∪ smokeC ∪ smokeS ∪ (∅ : Finset Smoke)) (smokeT ∪ smokeS ∪ ∅)

def smokeDoTarRight : MassExpr Smoke :=
  .cond smokeT (smokeT ∪ smokeS ∪ (∅ : Finset Smoke)) (smokeT ∪ ∅)

def cancerSmokeChained : MassExpr Smoke :=
  .mul cancerLeft smokeDoTarRight

def chainCancerSmoke :
    Deriv smokeGraph
      (.cond smokeT (smokeT ∪ smokeC ∪ smokeS ∪ (∅ : Finset Smoke)) (smokeT ∪ ∅))
      cancerSmokeChained :=
  .chain smokeT smokeC smokeS ∅

def smokeAbsorbSource : MassExpr Smoke :=
  .cond smokeT (smokeS ∪ smokeT) ((∅ : Finset Smoke) ∪ smokeT)

def smokeAbsorbTarget : MassExpr Smoke :=
  .cond smokeT smokeS ∅

theorem smokeRight_eq_absorb :
    smokeDoTarRight = smokeAbsorbSource := by
  unfold smokeDoTarRight smokeAbsorbSource
  refine cond_eq_of_sets rfl ?_ ?_
  · ext v; cases v <;> simp [smokeS, smokeT]
  · ext v; cases v <;> simp [smokeT]

def absorbTarFromSmoke : Deriv smokeGraph smokeAbsorbSource smokeAbsorbTarget :=
  .absorb smokeT smokeS ∅ smokeT (fun _ hv => hv)

def smokeRule3Source : MassExpr Smoke :=
  .cond ((∅ : Finset Smoke) ∪ smokeT)
    ((∅ : Finset Smoke) ∪ smokeS ∪ ∅)
    (∅ ∪ ∅)

/-- `P(s)`, do-free. -/
def smokeObservational : MassExpr Smoke :=
  .cond (∅ : Finset Smoke) ((∅ : Finset Smoke) ∪ smokeS ∪ ∅) (∅ ∪ ∅)

theorem smokeAbsorb_eq_rule3 :
    smokeAbsorbTarget = smokeRule3Source := by
  unfold smokeAbsorbTarget smokeRule3Source
  refine cond_eq_of_sets ?_ ?_ ?_
  · ext v; cases v <;> simp [smokeT]
  · ext v; cases v <;> simp [smokeS]
  · ext v; cases v <;> simp

def deleteTarFromSmoke : Deriv smokeGraph smokeRule3Source smokeObservational :=
  .rule3 ∅ smokeS smokeT ∅ smoke_delete_tar_checked

def rightToSmokeObs : Deriv smokeGraph smokeDoTarRight smokeObservational :=
  .trans
    (.rewriteEq smokeRight_eq_absorb.symm rfl absorbTarFromSmoke)
    (.rewriteEq smokeAbsorb_eq_rule3 rfl deleteTarFromSmoke)

def cancerRule2Source : MassExpr Smoke :=
  .cond ((∅ : Finset Smoke) ∪ smokeT)
    ((∅ : Finset Smoke) ∪ smokeC ∪ smokeT ∪ smokeS)
    (∅ ∪ smokeT ∪ smokeS)

/-- `P(c | t, s)`, do-free. -/
def cancerObservational : MassExpr Smoke :=
  .cond (∅ : Finset Smoke)
    ((∅ : Finset Smoke) ∪ smokeC ∪ smokeT ∪ smokeS)
    ((∅ : Finset Smoke) ∪ smokeT ∪ smokeS)

theorem cancerLeft_eq_rule2 :
    cancerLeft = cancerRule2Source := by
  unfold cancerLeft cancerRule2Source
  refine cond_eq_of_sets ?_ ?_ ?_
  · ext v; cases v <;> simp [smokeT]
  · ext v; cases v <;> simp [smokeS, smokeT, smokeC]
  · ext v; cases v <;> simp [smokeS, smokeT]

def exchangeCancer : Deriv smokeGraph cancerRule2Source cancerObservational :=
  .rule2 ∅ smokeC smokeT smokeS smoke_cancer_given_tar_checked

def leftToCancerObs : Deriv smokeGraph cancerLeft cancerObservational :=
  .rewriteEq cancerLeft_eq_rule2.symm rfl exchangeCancer

def cancerSmokeObs : MassExpr Smoke :=
  .mul cancerObservational smokeObservational

def innerObs : Deriv smokeGraph cancerSmokeChained cancerSmokeObs :=
  .trans (.mulLeft leftToCancerObs) (.mulRight rightToSmokeObs)

def cancerSumObs : MassExpr Smoke :=
  .sum smokeS cancerSmokeObs

def sumInner : Deriv smokeGraph cancerSumSmoke cancerSumObs :=
  .trans (.sumBody chainCancerSmoke) (.sumBody innerObs)

def cancerDoTarToObs : Deriv smokeGraph cancerDoTar cancerSumObs :=
  .trans introSmoke sumInner

/-- The do-free front-door expression reached from `smokingQuery`. -/
def frontDoorExpr : MassExpr Smoke :=
  .sum smokeT (.mul cancerSumObs tarGivenSmoke)

def stepFront : Deriv smokeGraph afterCancerDoTar frontDoorExpr :=
  .sumBody (.mulLeft cancerDoTarToObs)

def openQuery : Deriv smokeGraph smokingQuery smokingOpened :=
  .rewriteEq smokingQuery_eq_marginalSource.symm rfl openSmoking

/-- Derivation from `P(c | do(s))` to `frontDoorExpr`. -/
def frontDoorDeriv : Deriv smokeGraph smokingQuery frontDoorExpr :=
  .trans openQuery
    (.trans chainSmoking
      (.trans stepTarExchange
        (.trans stepCancer stepFront)))

theorem frontDoorExpr_doFree : doFree frontDoorExpr = true := by
  decide

section Denote

variable {β : Type}
variable [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
variable [MeasurableSingletonClass β] [StandardBorelSpace β]
variable [StandardBorelSpace (Smoke → β)]

omit [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
  [MeasurableSingletonClass β] [StandardBorelSpace β] [StandardBorelSpace (Smoke → β)] in
lemma doFinset_eq_doSmoke (anchor : Smoke → β) :
    doFinset smokeS anchor = doSmoke (anchor Smoke.s) := by
  funext vertex
  cases vertex <;> simp [doFinset, doSmoke, smokeS, Finset.mem_singleton]

omit [MeasurableSingletonClass β] [StandardBorelSpace β] [StandardBorelSpace (Smoke → β)] in
lemma truncSlice_forced_smoking
    (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (anchor : Smoke → β) :
    truncSlice smokeGraph smokeAcyclic cpt (doFinset smokeS anchor) smokeS anchor = 1 := by
  have hsum :=
    truncatedWeight_sum_eq_one smokeGraph smokeAcyclic cpt (doFinset smokeS anchor)
  unfold truncSlice
  rw [← hsum]
  refine Finset.sum_congr rfl fun assignment _ => ?_
  by_cases hagree : agreesOn smokeS anchor assignment = true
  · simp [hagree]
  · have hmiss : assignment Smoke.s ≠ anchor Smoke.s := by
      intro heq
      apply hagree
      rw [agreesOn_eq_true_iff]
      intro vertex hmember
      simp only [smokeS, Finset.mem_singleton] at hmember
      subst hmember
      exact heq
    have hzero :=
      truncatedWeight_zero_of_do_miss (intervention := smokeS) (vertex := Smoke.s)
        smokeGraph smokeAcyclic cpt (Finset.mem_singleton_self _) hmiss
    rw [if_neg hagree]
    exact hzero.symm

omit [Inhabited β] [MeasurableSingletonClass β] [StandardBorelSpace β]
  [StandardBorelSpace (Smoke → β)] in
lemma truncSlice_cancer_smoking
    (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (anchor : Smoke → β) {c0 : β} (hc : anchor Smoke.c = c0) :
    truncSlice smokeGraph smokeAcyclic cpt (doFinset smokeS anchor) (smokeC ∪ smokeS) anchor =
      doMass cpt (anchor Smoke.s) c0 := by
  unfold truncSlice doMass
  rw [doFinset_eq_doSmoke anchor]
  refine Finset.sum_congr rfl fun assignment _ => ?_
  by_cases hs : assignment Smoke.s = anchor Smoke.s
  · have hiff :
        agreesOn (smokeC ∪ smokeS) anchor assignment = true ↔
          assignment Smoke.c = anchor Smoke.c := by
      rw [agreesOn_eq_true_iff]
      constructor
      · intro hagree
        exact hagree Smoke.c (by simp [smokeC, smokeS])
      · intro hc' vertex hmember
        simp only [Finset.mem_union, smokeC, smokeS, Finset.mem_singleton] at hmember
        rcases hmember with hmember | hmember
        · subst hmember
          exact hc'
        · subst hmember
          exact hs
    by_cases hc' : assignment Smoke.c = anchor Smoke.c
    · simp [hiff.2 hc', hc, hc']
    · have hnot : agreesOn (smokeC ∪ smokeS) anchor assignment ≠ true := by
        intro hagree
        exact hc' (hiff.1 hagree)
      have hc0 : assignment Smoke.c ≠ c0 := by
        intro heq
        exact hc' (heq.trans hc.symm)
      simp [hnot, hc0]
  · have hzero :=
      truncatedWeight_zero_of_do_miss (intervention := smokeS) (vertex := Smoke.s)
        smokeGraph smokeAcyclic cpt (Finset.mem_singleton_self _) hs
    have hzeroSmoke :
        truncatedWeight smokeGraph smokeAcyclic cpt (doSmoke (anchor Smoke.s)) assignment = 0 := by
      rw [← doFinset_eq_doSmoke anchor]
      exact hzero
    have hnot : agreesOn (smokeC ∪ smokeS) anchor assignment ≠ true := by
      intro hagree
      exact hs ((agreesOn_eq_true_iff.mp hagree) Smoke.s (by simp [smokeC, smokeS]))
    rw [if_neg hnot, hzeroSmoke]
    split_ifs <;> rfl

omit [MeasurableSingletonClass β] [StandardBorelSpace β] [StandardBorelSpace (Smoke → β)] in
/-- `P(c | do(s))` is the interventional mass `doMass`. -/
theorem smoking_query_is_doMass
    (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (anchor : Smoke → β) :
    gDenote smokeGraph smokeAcyclic cpt anchor smokingQuery =
      doMass cpt (anchor Smoke.s) (anchor Smoke.c) := by
  simp only [smokingQuery, gDenote]
  rw [truncSlice_cancer_smoking cpt anchor rfl, truncSlice_forced_smoking cpt anchor,
    div_eq_mul_inv, inv_one, mul_one]

/-- Mass of a `U`-ignoring event, read from the margin of `S, T, C`. -/
noncomputable def marginMass
    (margin : ({v // v ∉ ({Smoke.u} : Finset Smoke)} → β) → ℝ≥0∞)
    (pred : (Smoke → β) → Prop) [DecidablePred pred] : ℝ≥0∞ :=
  ∑ out : {v // v ∉ ({Smoke.u} : Finset Smoke)} → β,
    if pred (glue {Smoke.u} (fun _ => default) out) then margin out else 0

omit [DecidableEq β] [MeasurableSpace β] [MeasurableSingletonClass β]
  [StandardBorelSpace β] [StandardBorelSpace (Smoke → β)] in
lemma smokeMass_through_u
    (joint : (Smoke → β) → ℝ≥0∞)
    {pred : (Smoke → β) → Prop} [DecidablePred pred]
    (hignore : ∀ a b, (∀ v, v ≠ Smoke.u → a v = b v) → (pred a ↔ pred b)) :
    smokeMass joint pred =
      marginMass (observedMargin {Smoke.u} joint) pred := by
  unfold smokeMass marginMass observedMargin
  rw [sum_glue {Smoke.u}
    (fun assignment : Smoke → β => if pred assignment then joint assignment else 0)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun out _ => ?_
  have hpred : ∀ inn,
      pred (glue {Smoke.u} inn out) ↔
        pred (glue {Smoke.u} (fun _ => default) out) := by
    intro inn
    apply hignore
    intro vertex hvertex
    have hnot : vertex ∉ ({Smoke.u} : Finset Smoke) := by
      simpa [Finset.mem_singleton] using hvertex
    simp [glue, hnot]
  by_cases hp : pred (glue {Smoke.u} (fun _ => default) out)
  · have hall : ∀ inn, pred (glue {Smoke.u} inn out) :=
      fun inn => (hpred inn).2 hp
    refine Eq.trans ?_ (if_pos hp).symm
    refine Finset.sum_congr rfl fun inn _ => ?_
    rw [if_pos (hall inn)]
  · have hnone : ∀ inn, ¬ pred (glue {Smoke.u} inn out) :=
      fun inn hpredInn => hp ((hpred inn).1 hpredInn)
    refine Eq.trans ?_ (if_neg hp).symm
    refine Finset.sum_eq_zero fun inn _ => ?_
    rw [if_neg (hnone inn)]

/-- `frontDoorOf` read from the margin of `S, T, C`. -/
noncomputable def frontDoorFromMargin (s0 c0 : β)
    (margin : ({v // v ∉ ({Smoke.u} : Finset Smoke)} → β) → ℝ≥0∞) : ℝ≥0∞ :=
  ∑ bt, (marginMass margin (fun f => f .s = s0 ∧ f .t = bt) /
      marginMass margin (fun f => f .s = s0)) *
    (∑ bs, (marginMass margin (fun f => f .c = c0 ∧ f .t = bt ∧ f .s = bs) /
        marginMass margin (fun f => f .s = bs ∧ f .t = bt)) *
      marginMass margin (fun f => f .s = bs))

omit [MeasurableSpace β] [MeasurableSingletonClass β] [StandardBorelSpace β]
  [StandardBorelSpace (Smoke → β)] in
theorem frontDoorOf_eq_margin (s0 c0 : β) (joint : (Smoke → β) → ℝ≥0∞) :
    frontDoorOf s0 c0 joint =
      frontDoorFromMargin s0 c0 (observedMargin {Smoke.u} joint) := by
  have hs : ∀ s0' t0,
      smokeMass joint (fun f => f .s = s0' ∧ f .t = t0) =
        marginMass (observedMargin {Smoke.u} joint) (fun f => f .s = s0' ∧ f .t = t0) := by
    intro s0' t0
    refine smokeMass_through_u joint ?_
    intro a b hab
    simp [hab Smoke.s (by decide), hab Smoke.t (by decide)]
  have hc : ∀ c0' t0 s0',
      smokeMass joint (fun f => f .c = c0' ∧ f .t = t0 ∧ f .s = s0') =
        marginMass (observedMargin {Smoke.u} joint)
          (fun f => f .c = c0' ∧ f .t = t0 ∧ f .s = s0') := by
    intro c0' t0 s0'
    refine smokeMass_through_u joint ?_
    intro a b hab
    simp [hab Smoke.c (by decide), hab Smoke.t (by decide), hab Smoke.s (by decide)]
  have honly : ∀ s0',
      smokeMass joint (fun f => f .s = s0') =
        marginMass (observedMargin {Smoke.u} joint) (fun f => f .s = s0') := by
    intro s0'
    refine smokeMass_through_u joint ?_
    intro a b hab
    simp [hab Smoke.s (by decide)]
  unfold frontDoorOf frontDoorFromMargin
  simp_rw [hs, hc, honly]

/-- Smoking tables whose smoking marginal and tar rows are positive at the anchor. -/
def FrontRows (anchor : Smoke → β) :=
  {cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT //
    obs cpt (fun assignment => assignment .s = anchor .s) ≠ 0 ∧
      ∀ smoking tar, pt cpt smoking tar ≠ 0}

omit [MeasurableSingletonClass β] [StandardBorelSpace β] [StandardBorelSpace (Smoke → β)] in
/-- The smoking query `Factors` through the margin of `S, T, C`. -/
theorem front_door_query_factors_stc_margin (anchor : Smoke → β) :
    Factors
      (fun cpt : FrontRows anchor =>
        observedMargin {Smoke.u} (fun assignment => cpt.1.jointWeight assignment))
      (fun cpt => gDenote smokeGraph smokeAcyclic cpt.1 anchor smokingQuery) := by
  refine ⟨fun margin => frontDoorFromMargin (anchor .s) (anchor .c) margin, fun cpt => ?_⟩
  have hquery := smoking_query_is_doMass cpt.1 anchor
  have hformula :=
    frontDoor_matches_formula (anchor .s) (anchor .c) cpt.1 cpt.2.1 cpt.2.2
  have hmargin := frontDoorOf_eq_margin (anchor .s) (anchor .c) cpt.1.jointWeight
  change frontDoorFromMargin (anchor .s) (anchor .c)
      (observedMargin {Smoke.u} (fun assignment => cpt.1.jointWeight assignment)) =
    gDenote smokeGraph smokeAcyclic cpt.1 anchor smokingQuery
  rw [hquery, hformula]
  exact hmargin.symm

/-- The derivation ends at a do-free expression denoting `frontDoorOf`. -/
theorem front_door_end_denotes
    (cpt : (network (β := β) smokeGraph smokeAcyclic).DiscreteCPT)
    (anchor : Smoke → β)
    (hpos : Positive smokeGraph smokeAcyclic frontDoorDeriv cpt anchor)
    (hsmoking : obs cpt (fun assignment => assignment .s = anchor .s) ≠ 0)
    (htar : ∀ smoking tar, pt cpt smoking tar ≠ 0) :
    doFree frontDoorExpr = true ∧
      gDenote smokeGraph smokeAcyclic cpt anchor frontDoorExpr =
        frontDoorOf (anchor .s) (anchor .c) cpt.jointWeight := by
  refine ⟨frontDoorExpr_doFree, ?_⟩
  have hends :=
    deriv_gDenote smokeGraph smokeAcyclic frontDoorDeriv cpt anchor hpos
  rw [← hends, smoking_query_is_doMass cpt anchor,
    frontDoor_matches_formula (anchor .s) (anchor .c) cpt hsmoking htar]

end Denote

end Mettapedia.GSLT.Causality.DoCalculus
