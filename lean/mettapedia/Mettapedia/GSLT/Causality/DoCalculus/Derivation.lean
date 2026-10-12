import Mettapedia.GSLT.Causality.DoCalculus.CheckerRules
import Mettapedia.GSLT.Causality.DoCalculus.CheckerSoundness
import Mettapedia.GSLT.Causality.DoCalculus.Soundness

/-!
# Derivation trees for the seven authored rules

A derivation is a tree of `MassExpr` on one graph. A leaf step is one of
`rule1`, `rule2`, `rule3`, `chain`, `bayes`, `empty-do`, and `marginal`,
the rules named by `authored_rule_ids`. The three do-calculus steps carry the
checker premise of `rule1_of_check`, `rule2_of_check`, or `rule3_of_check`.
Composition and a rewrite under `mul`, `div`, and `sum` are the tree
structure. `rule2Rev` and `rule3Rev` are rule 2 and rule 3 read the other
way. `divCond` is the chain rule read as a quotient. `absorbRev` is `absorb`
read the other way. Under the positivity
the tree collects, both ends have one
`gDenote`, and those values agree by the existing soundness theorem for the
step.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.DoCalculus

open Mettapedia.ProbabilityTheory.BayesianNetworks
open BayesianNetwork
open DiscreteCPT
open Mettapedia.ProbabilityTheory.BayesianNetworks.DiscreteLocalMarkov
open Mettapedia.ProbabilityTheory.BayesianNetworks.FiniteDSeparation
open Mettapedia.GSLT.Core.NonFactorization
open scoped BigOperators ENNReal

variable {V : Type}
variable [Fintype V] [DecidableEq V]
variable (graph : DirectedGraph V)
variable [DecidableRel graph.edges]
variable (hAcyclic : graph.IsAcyclic)
variable {β : Type}
variable [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
variable [MeasurableSingletonClass β] [StandardBorelSpace β]
variable [StandardBorelSpace (V → β)]

/-- The seven identifiers, in the order `authored_rule_ids` records. -/
theorem seven_authored_ids :
    (definition.rules.map fun rule => rule.id.value) =
      [rule1Id, rule2Id, rule3Id, chainId, bayesId, emptyDoId, marginalId] :=
  authored_rule_ids

omit [Fintype V] [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
  [MeasurableSingletonClass β] [StandardBorelSpace β]
  [StandardBorelSpace (V → β)] in
lemma doFinset_agree {target : Finset V} {left right : V → β}
    (hagree : ∀ v ∈ target, left v = right v) :
    doFinset target left = doFinset target right := by
  funext vertex
  by_cases hmember : vertex ∈ target
  · simp [doFinset, hmember, hagree vertex hmember]
  · simp [doFinset, hmember]

omit [Fintype V] [Fintype β] [DecidableEq β] [Inhabited β] [MeasurableSpace β]
  [MeasurableSingletonClass β] [StandardBorelSpace β]
  [StandardBorelSpace (V → β)] in
lemma doFinset_singleton_anchor (treatment : V) (anchor : V → β) :
    doFinset {treatment} anchor = doOne treatment (anchor treatment) := by
  funext vertex
  by_cases hmember : vertex = treatment
  · simp [doFinset, doOne, hmember, Finset.mem_singleton]
  · simp [doFinset, doOne, hmember, Finset.mem_singleton]

/-- Anchor coordinates on a finset. `intervenedNet` uses the alphabet `β`. -/
def anchorAssign (coords : Finset V) (anchor : V → β)
    (p : ((coords : Finset V) : Set V)) : β :=
  anchor p.1

omit [DecidableRel graph.edges] [MeasurableSingletonClass β]
  [StandardBorelSpace (V → β)] in
lemma mem_assignEvent_anchor (treatment : V) (coords : Finset V)
    (anchor assignment : V → β) :
    (assignment ∈ assignEvent (bn := intervenedNet graph hAcyclic treatment) coords
      (anchorAssign coords anchor)) ↔
      agreesOn coords anchor assignment = true := by
  rw [assignEvent, eventOfConstraints_constraintsOfRestrict,
    Set.mem_preimage, Set.mem_singleton_iff, agreesOn_eq_true_iff]
  constructor
  · intro hrestrict vertex hvertex
    have hcoord := congrFun hrestrict ⟨vertex, Finset.mem_coe.mpr hvertex⟩
    simpa [restrictToSet, anchorAssign] using hcoord
  · intro hagree
    funext packed
    have hvertex : packed.1 ∈ coords := Finset.mem_coe.mp packed.property
    simpa [restrictToSet, anchorAssign] using hagree packed.1 hvertex

omit [DecidableRel graph.edges] [MeasurableSingletonClass β]
  [StandardBorelSpace (V → β)] in
lemma assignEvent_union (treatment : V) (left right : Finset V) (anchor : V → β) :
    assignEvent (bn := intervenedNet graph hAcyclic treatment) (left ∪ right)
        (anchorAssign (left ∪ right) anchor) =
      assignEvent (bn := intervenedNet graph hAcyclic treatment) left
          (anchorAssign left anchor) ∩
        assignEvent (bn := intervenedNet graph hAcyclic treatment) right
          (anchorAssign right anchor) := by
  ext assignment
  rw [Set.mem_inter_iff,
    mem_assignEvent_anchor graph hAcyclic treatment (left ∪ right) anchor assignment,
    mem_assignEvent_anchor graph hAcyclic treatment left anchor assignment,
    mem_assignEvent_anchor graph hAcyclic treatment right anchor assignment]
  exact agreesOn_union

omit [StandardBorelSpace (V → β)] in
lemma truncSlice_eq_intervenedMeasure (treatment : V) (coords : Finset V)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT) (anchor : V → β) :
    truncSlice graph hAcyclic cpt (doFinset {treatment} anchor) coords anchor =
      (intervenedCPT graph hAcyclic cpt treatment (anchor treatment)).jointMeasure
        (assignEvent (bn := intervenedNet graph hAcyclic treatment) coords
          (anchorAssign coords anchor)) := by
  classical
  have hmeas :
      MeasurableSet (assignEvent (bn := intervenedNet graph hAcyclic treatment) coords
        (anchorAssign coords anchor)) :=
    assignEvent_measurable (bn := intervenedNet graph hAcyclic treatment) coords _
  rw [jointMeasure_apply_as_sum (bn := intervenedNet graph hAcyclic treatment)
      (intervenedCPT graph hAcyclic cpt treatment (anchor treatment)) hmeas,
    truncSlice, doFinset_singleton_anchor]
  refine Finset.sum_congr rfl fun assignment _ => ?_
  by_cases hagree : agreesOn coords anchor assignment = true
  · have hmem :
        assignment ∈ assignEvent (bn := intervenedNet graph hAcyclic treatment) coords
          (anchorAssign coords anchor) :=
      (mem_assignEvent_anchor graph hAcyclic treatment coords anchor assignment).2 hagree
    simp [hagree, hmem, intervened_jointWeight_eq_truncatedWeight]
  · have hnot :
        assignment ∉ assignEvent (bn := intervenedNet graph hAcyclic treatment) coords
          (anchorAssign coords anchor) := by
      intro hmem
      exact hagree
        ((mem_assignEvent_anchor graph hAcyclic treatment coords anchor assignment).1 hmem)
    simp [hagree, hnot]

omit [Fintype β] [Inhabited β] [MeasurableSingletonClass β] [StandardBorelSpace β]
  [StandardBorelSpace (V → β)] in
/-- A variable set by the intervention contributes `0` when the configuration misses it. -/
lemma truncatedWeight_zero_of_do_miss
    {intervention : Finset V} {anchor assignment : V → β}
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    {vertex : V} (hvertex : vertex ∈ intervention) (hmiss : assignment vertex ≠ anchor vertex) :
    truncatedWeight graph hAcyclic cpt (doFinset intervention anchor) assignment = 0 := by
  unfold truncatedWeight
  refine Finset.prod_eq_zero (Finset.mem_univ vertex) ?_
  simp [truncatedFactor, doFinset, hvertex, hmiss]

omit [Inhabited β] [MeasurableSingletonClass β] [StandardBorelSpace β]
  [StandardBorelSpace (V → β)] in
/-- Coordinates already fixed by the intervention do not change a truncated slice. -/
lemma truncSlice_absorb
    {intervention fixed coords : Finset V}
    (hsub : fixed ⊆ intervention)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (anchor : V → β) :
    truncSlice graph hAcyclic cpt (doFinset intervention anchor) (coords ∪ fixed) anchor =
      truncSlice graph hAcyclic cpt (doFinset intervention anchor) coords anchor := by
  unfold truncSlice
  refine Finset.sum_congr rfl fun assignment _ => ?_
  by_cases hcoords : agreesOn coords anchor assignment = true
  · by_cases hfixed : agreesOn fixed anchor assignment = true
    · have hunion : agreesOn (coords ∪ fixed) anchor assignment = true :=
        (agreesOn_union).2 ⟨hcoords, hfixed⟩
      simp [hcoords, hunion]
    · have hnot : agreesOn (coords ∪ fixed) anchor assignment ≠ true := by
        intro hagree
        exact hfixed ((agreesOn_union).1 hagree).2
      have hmiss : ∃ vertex, vertex ∈ fixed ∧ assignment vertex ≠ anchor vertex := by
        by_contra hnone
        apply hfixed
        rw [agreesOn_eq_true_iff]
        intro vertex hmember
        by_contra hneq
        exact hnone ⟨vertex, hmember, hneq⟩
      rcases hmiss with ⟨vertex, hmember, hneq⟩
      have hzero :=
        truncatedWeight_zero_of_do_miss graph hAcyclic cpt (hsub hmember) hneq
      simp [hcoords, hnot, hzero]
  · have hnot : agreesOn (coords ∪ fixed) anchor assignment ≠ true := by
      intro hagree
      exact hcoords ((agreesOn_union).1 hagree).1
    simp [hcoords, hnot]

/-- A derivation from `source` to `target` on `graph`. -/
inductive Deriv : MassExpr V → MassExpr V → Type where
  | refl (expr : MassExpr V) : Deriv expr expr
  | trans {a b c : MassExpr V} (left : Deriv a b) (right : Deriv b c) : Deriv a c
  | rewriteEq {a b a' b' : MassExpr V} (ha : a = a') (hb : b = b')
      (step : Deriv a b) : Deriv a' b'
  | mulLeft {a b right : MassExpr V} (step : Deriv a b) :
      Deriv (.mul a right) (.mul b right)
  | mulRight {left a b : MassExpr V} (step : Deriv a b) :
      Deriv (.mul left a) (.mul left b)
  | divNum {a b denominator : MassExpr V} (step : Deriv a b) :
      Deriv (.div a denominator) (.div b denominator)
  | divDen {numerator a b : MassExpr V} (step : Deriv a b) :
      Deriv (.div numerator a) (.div numerator b)
  | sumBody {bound : Finset V} {a b : MassExpr V} (step : Deriv a b) :
      Deriv (.sum bound a) (.sum bound b)
  | rule1 (treatment : V) (outcome covariate conditioning : Finset V)
      (hTreat : treatment ∈ conditioning)
      (hcheck : FiniteDSeparation.check (deleteIncoming graph {treatment})
        (rule1Profile outcome covariate conditioning) = true) :
      Deriv
        (.cond {treatment}
          (outcome ∪ covariate ∪ conditioning)
          (covariate ∪ conditioning))
        (.cond {treatment}
          (outcome ∪ conditioning)
          conditioning)
  | rule2 (intervention outcome exchanged conditioning : Finset V)
      (hcheck : FiniteDSeparation.check (gout graph intervention exchanged)
        (rule2Profile outcome exchanged (intervention ∪ conditioning)) = true) :
      Deriv
        (.cond (intervention ∪ exchanged)
          (intervention ∪ outcome ∪ exchanged ∪ conditioning)
          (intervention ∪ exchanged ∪ conditioning))
        (.cond intervention
          (intervention ∪ outcome ∪ exchanged ∪ conditioning)
          (intervention ∪ exchanged ∪ conditioning))
  | rule3 (intervention outcome deleted conditioning : Finset V)
      (hcheck : FiniteDSeparation.check
        (rule3Graph graph intervention deleted conditioning)
        (rule3Profile outcome deleted (intervention ∪ conditioning)) = true) :
      Deriv
        (.cond (intervention ∪ deleted)
          (intervention ∪ outcome ∪ conditioning)
          (intervention ∪ conditioning))
        (.cond intervention
          (intervention ∪ outcome ∪ conditioning)
          (intervention ∪ conditioning))
  | rule3Rev (intervention outcome deleted conditioning : Finset V)
      (hcheck : FiniteDSeparation.check
        (rule3Graph graph intervention deleted conditioning)
        (rule3Profile outcome deleted (intervention ∪ conditioning)) = true) :
      Deriv
        (.cond intervention
          (intervention ∪ outcome ∪ conditioning)
          (intervention ∪ conditioning))
        (.cond (intervention ∪ deleted)
          (intervention ∪ outcome ∪ conditioning)
          (intervention ∪ conditioning))
  | rule2Rev (intervention outcome exchanged conditioning : Finset V)
      (hcheck : FiniteDSeparation.check (gout graph intervention exchanged)
        (rule2Profile outcome exchanged (intervention ∪ conditioning)) = true) :
      Deriv
        (.cond intervention
          (intervention ∪ outcome ∪ exchanged ∪ conditioning)
          (intervention ∪ exchanged ∪ conditioning))
        (.cond (intervention ∪ exchanged)
          (intervention ∪ outcome ∪ exchanged ∪ conditioning)
          (intervention ∪ exchanged ∪ conditioning))
  | absorb (intervention numerator denominator fixed : Finset V)
      (hsub : fixed ⊆ intervention) :
      Deriv
        (.cond intervention (numerator ∪ fixed) (denominator ∪ fixed))
        (.cond intervention numerator denominator)
  | absorbRev (intervention numerator denominator fixed : Finset V)
      (hsub : fixed ⊆ intervention) :
      Deriv
        (.cond intervention numerator denominator)
        (.cond intervention (numerator ∪ fixed) (denominator ∪ fixed))
  | chain (intervention left right conditioning : Finset V) :
      Deriv
        (.cond intervention
          (intervention ∪ left ∪ right ∪ conditioning)
          (intervention ∪ conditioning))
        (.mul
          (.cond intervention
            (intervention ∪ left ∪ right ∪ conditioning)
            (intervention ∪ right ∪ conditioning))
          (.cond intervention
            (intervention ∪ right ∪ conditioning)
            (intervention ∪ conditioning)))
  | divCond (intervention left right conditioning : Finset V) :
      Deriv
        (.cond intervention
          (intervention ∪ left ∪ right ∪ conditioning)
          (intervention ∪ right ∪ conditioning))
        (.div
          (.cond intervention
            (intervention ∪ left ∪ right ∪ conditioning)
            (intervention ∪ conditioning))
          (.cond intervention
            (intervention ∪ right ∪ conditioning)
            (intervention ∪ conditioning)))
  | bayes (intervention left right conditioning : Finset V) :
      Deriv
        (.cond intervention
          (intervention ∪ left ∪ right ∪ conditioning)
          (intervention ∪ right ∪ conditioning))
        (.div
          (.mul
            (.cond intervention
              (intervention ∪ left ∪ right ∪ conditioning)
              (intervention ∪ left ∪ conditioning))
            (.cond intervention
              (intervention ∪ left ∪ conditioning)
              (intervention ∪ conditioning)))
          (.cond intervention
            (intervention ∪ right ∪ conditioning)
            (intervention ∪ conditioning)))
  | emptyDo (numerator denominator : Finset V) :
      Deriv (.cond ∅ numerator denominator) (.cond ∅ numerator denominator)
  | marginal (intervention outcome bound conditioning : Finset V)
      (hintervention : Disjoint bound intervention)
      (houtcome : Disjoint bound outcome)
      (hconditioning : Disjoint bound conditioning) :
      Deriv
        (.sum bound
          (.cond intervention
            (intervention ∪ outcome ∪ bound ∪ conditioning)
            (intervention ∪ conditioning)))
        (.cond intervention
          (intervention ∪ outcome ∪ conditioning)
          (intervention ∪ conditioning))
  | marginalIntro (intervention outcome bound conditioning : Finset V)
      (hintervention : Disjoint bound intervention)
      (houtcome : Disjoint bound outcome)
      (hconditioning : Disjoint bound conditioning) :
      Deriv
        (.cond intervention
          (intervention ∪ outcome ∪ conditioning)
          (intervention ∪ conditioning))
        (.sum bound
          (.cond intervention
            (intervention ∪ outcome ∪ bound ∪ conditioning)
            (intervention ∪ conditioning)))

/-- Positivity and anchor agreement collected by a derivation. -/
def Positive {source target : MassExpr V} :
    Deriv graph source target →
      (network (β := β) graph hAcyclic).DiscreteCPT → (V → β) → Prop
  | .refl _ => fun _ _ => True
  | .trans left right => fun cpt anchor =>
      Positive left cpt anchor ∧ Positive right cpt anchor
  | .rewriteEq _ _ step => fun cpt anchor => Positive step cpt anchor
  | .mulLeft step => fun cpt anchor => Positive step cpt anchor
  | .mulRight step => fun cpt anchor => Positive step cpt anchor
  | .divNum step => fun cpt anchor => Positive step cpt anchor
  | .divDen step => fun cpt anchor => Positive step cpt anchor
  | .sumBody (bound := bound) step => fun cpt anchor =>
      ∀ inn, Positive step cpt (extendAnchor bound inn anchor)
  | .rule1 treatment _ covariate conditioning _ _ => fun cpt anchor =>
      (intervenedCPT graph hAcyclic cpt treatment (anchor treatment)).jointMeasure
        (assignEvent (bn := intervenedNet graph hAcyclic treatment) covariate
            (anchorAssign covariate anchor) ∩
          assignEvent (bn := intervenedNet graph hAcyclic treatment) conditioning
            (anchorAssign conditioning anchor)) ≠ 0
  | .rule2 intervention _ exchanged conditioning _ => fun cpt anchor =>
      truncSlice graph hAcyclic cpt (doFinset intervention anchor)
        (intervention ∪ exchanged ∪ conditioning) anchor ≠ 0
  | .rule3 intervention _ deleted conditioning _ => fun cpt anchor =>
      truncSlice graph hAcyclic cpt (doFinset intervention anchor)
          (intervention ∪ conditioning) anchor ≠ 0 ∧
        truncSlice graph hAcyclic cpt (doFinset (intervention ∪ deleted) anchor)
          (intervention ∪ conditioning) anchor ≠ 0
  | .rule3Rev intervention _ deleted conditioning _ => fun cpt anchor =>
      truncSlice graph hAcyclic cpt (doFinset intervention anchor)
          (intervention ∪ conditioning) anchor ≠ 0 ∧
        truncSlice graph hAcyclic cpt (doFinset (intervention ∪ deleted) anchor)
          (intervention ∪ conditioning) anchor ≠ 0
  | .rule2Rev intervention _ exchanged conditioning _ => fun cpt anchor =>
      truncSlice graph hAcyclic cpt (doFinset intervention anchor)
        (intervention ∪ exchanged ∪ conditioning) anchor ≠ 0
  | .absorb _ _ _ _ _ => fun _ _ => True
  | .absorbRev _ _ _ _ _ => fun _ _ => True
  | .chain intervention _ right conditioning => fun cpt anchor =>
      truncSlice graph hAcyclic cpt (doFinset intervention anchor)
        (intervention ∪ right ∪ conditioning) anchor ≠ 0
  | .divCond intervention _ _ conditioning => fun cpt anchor =>
      truncSlice graph hAcyclic cpt (doFinset intervention anchor)
        (intervention ∪ conditioning) anchor ≠ 0
  | .bayes intervention left _ conditioning => fun cpt anchor =>
      truncSlice graph hAcyclic cpt (doFinset intervention anchor)
          (intervention ∪ left ∪ conditioning) anchor ≠ 0 ∧
        truncSlice graph hAcyclic cpt (doFinset intervention anchor)
          (intervention ∪ conditioning) anchor ≠ 0
  | .emptyDo _ _ => fun _ _ => True
  | .marginal _ _ _ _ _ _ _ => fun _ _ => True
  | .marginalIntro _ _ _ _ _ _ _ => fun _ _ => True

omit [Inhabited β] [MeasurableSingletonClass β] [StandardBorelSpace β]
  [StandardBorelSpace (V → β)] in
/-- An empty intervention denotes the observational ratio of the joint. -/
theorem empty_step_reads_joint
    (numerator denominator : Finset V)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (anchor : V → β) :
    gDenote graph hAcyclic cpt anchor (.cond ∅ numerator denominator) =
        gDenote graph hAcyclic cpt anchor (.cond ∅ numerator denominator) ∧
      gDenote graph hAcyclic cpt anchor (.cond ∅ numerator denominator) =
        denoteJoint anchor (fun assignment => cpt.jointWeight assignment)
          (.cond ∅ numerator denominator) :=
  ⟨rfl, empty_do_is_observational graph hAcyclic numerator denominator cpt anchor⟩

/-- Both ends of a derivation have one `gDenote`, and those values agree. -/
theorem deriv_gDenote {source target : MassExpr V}
    (step : Deriv graph source target)
    (cpt : (network (β := β) graph hAcyclic).DiscreteCPT)
    (anchor : V → β)
    (hpos : Positive graph hAcyclic step cpt anchor) :
    gDenote graph hAcyclic cpt anchor source =
      gDenote graph hAcyclic cpt anchor target := by
  induction step generalizing anchor with
  | refl _ =>
      cases hpos
      rfl
  | trans _ _ leftIh rightIh =>
      exact (leftIh anchor hpos.1).trans (rightIh anchor hpos.2)
  | rewriteEq ha hb _ childIh =>
      cases ha
      cases hb
      exact childIh anchor hpos
  | mulLeft _ childIh =>
      simp only [gDenote]
      rw [childIh anchor hpos]
  | mulRight _ childIh =>
      simp only [gDenote]
      rw [childIh anchor hpos]
  | divNum _ childIh =>
      simp only [gDenote]
      rw [childIh anchor hpos]
  | divDen _ childIh =>
      simp only [gDenote]
      rw [childIh anchor hpos]
  | sumBody _ childIh =>
      simp only [gDenote]
      refine Finset.sum_congr rfl fun inn _ => ?_
      exact childIh (extendAnchor _ inn anchor) (hpos inn)
  | rule1 treatment outcome covariate conditioning hTreat hcheck =>
      simp only [gDenote]
      have hslice :
          ∀ coords : Finset V,
            truncSlice graph hAcyclic cpt (doFinset {treatment} anchor) coords anchor =
              (intervenedCPT graph hAcyclic cpt treatment (anchor treatment)).jointMeasure
                (assignEvent (bn := intervenedNet graph hAcyclic treatment) coords
                  (anchorAssign coords anchor)) :=
        fun coords =>
          truncSlice_eq_intervenedMeasure graph hAcyclic treatment coords cpt anchor
      rw [hslice (outcome ∪ covariate ∪ conditioning),
        hslice (covariate ∪ conditioning),
        hslice (outcome ∪ conditioning),
        hslice conditioning]
      have hthree :
          assignEvent (bn := intervenedNet graph hAcyclic treatment)
              (outcome ∪ covariate ∪ conditioning)
              (anchorAssign (outcome ∪ covariate ∪ conditioning) anchor) =
            assignEvent (bn := intervenedNet graph hAcyclic treatment) outcome
                (anchorAssign outcome anchor) ∩
              assignEvent (bn := intervenedNet graph hAcyclic treatment) covariate
                (anchorAssign covariate anchor) ∩
              assignEvent (bn := intervenedNet graph hAcyclic treatment) conditioning
                (anchorAssign conditioning anchor) := by
        rw [assignEvent_union graph hAcyclic treatment (outcome ∪ covariate) conditioning
            anchor,
          assignEvent_union graph hAcyclic treatment outcome covariate anchor]
      have htwo :
          assignEvent (bn := intervenedNet graph hAcyclic treatment)
              (covariate ∪ conditioning)
              (anchorAssign (covariate ∪ conditioning) anchor) =
            assignEvent (bn := intervenedNet graph hAcyclic treatment) covariate
                (anchorAssign covariate anchor) ∩
              assignEvent (bn := intervenedNet graph hAcyclic treatment) conditioning
                (anchorAssign conditioning anchor) :=
        assignEvent_union graph hAcyclic treatment covariate conditioning anchor
      have hpair :
          assignEvent (bn := intervenedNet graph hAcyclic treatment)
              (outcome ∪ conditioning)
              (anchorAssign (outcome ∪ conditioning) anchor) =
            assignEvent (bn := intervenedNet graph hAcyclic treatment) outcome
                (anchorAssign outcome anchor) ∩
              assignEvent (bn := intervenedNet graph hAcyclic treatment) conditioning
                (anchorAssign conditioning anchor) :=
        assignEvent_union graph hAcyclic treatment outcome conditioning anchor
      rw [hthree, htwo, hpair]
      exact rule1_of_check graph hAcyclic cpt treatment (anchor treatment)
        outcome covariate conditioning
        (anchorAssign outcome anchor)
        (anchorAssign covariate anchor)
        (anchorAssign conditioning anchor)
        hTreat hcheck hpos
  | rule2 intervention outcome exchanged conditioning hcheck =>
      simp only [gDenote]
      have hmerge : mergeAssign intervention anchor anchor = anchor := by
        funext vertex
        simp [mergeAssign]
      have hdo :=
        congrArg (doFinset (intervention ∪ exchanged)) hmerge.symm
      rw [hdo]
      exact rule2_of_check graph hAcyclic cpt anchor anchor anchor
        (fun _ _ => rfl) hcheck hpos
  | rule2Rev intervention outcome exchanged conditioning hcheck =>
      simp only [gDenote]
      have hmerge : mergeAssign intervention anchor anchor = anchor := by
        funext vertex
        simp [mergeAssign]
      have hdo :=
        congrArg (doFinset (intervention ∪ exchanged)) hmerge.symm
      rw [hdo]
      exact (rule2_of_check graph hAcyclic cpt anchor anchor anchor
        (fun _ _ => rfl) hcheck hpos).symm
  | absorb intervention numerator denominator fixed hsub =>
      cases hpos
      simp only [gDenote]
      rw [truncSlice_absorb graph hAcyclic hsub cpt anchor,
        truncSlice_absorb graph hAcyclic hsub cpt anchor]
  | absorbRev intervention numerator denominator fixed hsub =>
      cases hpos
      simp only [gDenote]
      have hnum :=
        (truncSlice_absorb (coords := numerator) graph hAcyclic hsub cpt anchor).symm
      have hden :=
        (truncSlice_absorb (coords := denominator) graph hAcyclic hsub cpt anchor).symm
      rw [hnum, hden]
  | rule3 intervention outcome deleted conditioning hcheck =>
      rcases hpos with ⟨hidle, hforced⟩
      simp only [gDenote]
      have hmerge : mergeAssign intervention anchor anchor = anchor := by
        funext vertex
        simp [mergeAssign]
      have hdo :=
        congrArg (doFinset (intervention ∪ deleted)) hmerge.symm
      have hforcedMerge :
          truncSlice graph hAcyclic cpt
              (doFinset (intervention ∪ deleted) (mergeAssign intervention anchor anchor))
              (intervention ∪ conditioning) anchor ≠ 0 := by
        simpa [hmerge] using hforced
      rw [hdo]
      exact rule3_of_check graph hAcyclic cpt anchor anchor anchor hcheck hidle hforcedMerge
  | rule3Rev intervention outcome deleted conditioning hcheck =>
      rcases hpos with ⟨hidle, hforced⟩
      simp only [gDenote]
      have hmerge : mergeAssign intervention anchor anchor = anchor := by
        funext vertex
        simp [mergeAssign]
      have hdo :=
        congrArg (doFinset (intervention ∪ deleted)) hmerge.symm
      have hforcedMerge :
          truncSlice graph hAcyclic cpt
              (doFinset (intervention ∪ deleted) (mergeAssign intervention anchor anchor))
              (intervention ∪ conditioning) anchor ≠ 0 := by
        simpa [hmerge] using hforced
      rw [hdo]
      exact (rule3_of_check graph hAcyclic cpt anchor anchor anchor hcheck hidle hforcedMerge).symm
  | chain intervention left right conditioning =>
      simpa [gDenote] using
        chain_sound graph hAcyclic intervention left right conditioning cpt anchor hpos
  | divCond intervention left right conditioning =>
      simp only [gDenote]
      have hbaseTop :=
        truncSlice_ne_top graph hAcyclic cpt (doFinset intervention anchor)
          (intervention ∪ conditioning) anchor
      exact (ennreal_div_div_same
        (truncSlice graph hAcyclic cpt (doFinset intervention anchor)
          (intervention ∪ left ∪ right ∪ conditioning) anchor)
        (truncSlice graph hAcyclic cpt (doFinset intervention anchor)
          (intervention ∪ conditioning) anchor)
        (truncSlice graph hAcyclic cpt (doFinset intervention anchor)
          (intervention ∪ right ∪ conditioning) anchor)
        hpos hbaseTop).symm
  | bayes intervention left right conditioning =>
      simpa [gDenote] using
        bayes_sound graph hAcyclic intervention left right conditioning cpt anchor
          hpos.1 hpos.2
  | emptyDo numerator denominator =>
      cases hpos
      exact (empty_step_reads_joint graph hAcyclic numerator denominator cpt anchor).1
  | marginal intervention outcome bound conditioning hintervention houtcome hconditioning =>
      cases hpos
      exact marginal_sound graph hAcyclic hintervention houtcome hconditioning cpt anchor
  | marginalIntro intervention outcome bound conditioning
      hintervention houtcome hconditioning =>
      cases hpos
      exact (marginal_sound graph hAcyclic hintervention houtcome hconditioning cpt anchor).symm

/-- A do-free end is one function of the observational joint, and so is the
source, wherever the derivation's positivity holds. -/
theorem deriv_doFree_factors
    {source target : MassExpr V}
    (step : Deriv graph source target)
    (hfree : doFree target = true)
    (anchor : V → β)
    (hpos : ∀ cpt : (network (β := β) graph hAcyclic).DiscreteCPT,
      Positive graph hAcyclic step cpt anchor) :
    Factors (fun cpt : (network (β := β) graph hAcyclic).DiscreteCPT => cpt.jointWeight)
      (fun cpt => gDenote graph hAcyclic cpt anchor source) := by
  refine ⟨fun joint => denoteJoint anchor joint target, fun cpt => ?_⟩
  exact ((denote_eq_joint graph hAcyclic target hfree cpt anchor).symm).trans
    ((deriv_gDenote graph hAcyclic step cpt anchor (hpos cpt)).symm)

end Mettapedia.GSLT.Causality.DoCalculus
