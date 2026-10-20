import Mettapedia.GSLT.LanguageDef.BooleanTermSemantics
import Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusSemantics
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenChecker

/-!
# Recursive ledger semantics for instantiated evidence rules

Query, ledger and count expressions have separate interpretations. Their
constructors are interpreted recursively, so the result of one revision can
be an argument of a later revision or readout. Uninterpreted terms are supplied
by the model as atoms of the relevant sort; this does not identify their
meanings across sorts.

The ledger profile contains the six identified-observation rules from the
shared evidence module. Report, paired-sample and population rules retain
separate semantics.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.GSLT.LedgerTermSemantics

open Mettapedia.GSLT.LanguageDef.FirstOrderCalculus
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusModule
open Mettapedia.PLN.Bridges.GSLT.EvidenceCalculusSemantics
open Mettapedia.PLN.WorldModel.EvidenceContracts
open Mettapedia.PLN.WorldModel.EvidenceSpaces
open Mettapedia.PLN.WorldModel.EvidenceSpaces.Evidence

structure Model where
  Id : Type
  W : Type
  [decEq : DecidableEq Id]
  world : Id → W
  atomQuery : Pattern → W → Bool
  atomLedger : Pattern → Finset Id
  atomSummary : Pattern → Evidence ℕ
  atomValue : Pattern → Set ℝ × Finset Id
  priorStrength : ℝ
  priorStrength_pos : 0 < priorStrength

attribute [instance] Model.decEq

namespace Model

def query (model : Model) : Pattern → model.W → Bool :=
  BooleanTermSemantics.eval model.atomQuery

def ledger (model : Model) : Pattern → Finset model.Id
  | .apply "revise" [a, b] | .apply "lowerMerge" [a, b] => model.ledger a ∪ model.ledger b
  | .apply "swap" [e] => model.ledger e
  | other => model.atomLedger other
termination_by pattern => sizeOf pattern

def summary (model : Model) : Pattern → Evidence ℕ
  | .apply "revise" [a, b] => model.summary a + model.summary b
  | .apply "lowerMerge" [a, b] =>
      ⟨max (model.summary a).pos (model.summary b).pos,
        max (model.summary a).neg (model.summary b).neg⟩
  | .apply "swap" [e] => against (model.summary e)
  | other => model.atomSummary other
termination_by pattern => sizeOf pattern

@[simp] theorem query_atom (model : Model) (name : String) :
    model.query (.apply name []) = model.atomQuery (.apply name []) := by
  simp [query]

@[simp] theorem ledger_atom (model : Model) (name : String) :
    model.ledger (.apply name []) = model.atomLedger (.apply name []) := by
  rw [ledger] <;> simp

@[simp] theorem summary_atom (model : Model) (name : String) :
    model.summary (.apply name []) = model.atomSummary (.apply name []) := by
  rw [summary] <;> simp

noncomputable def value (model : Model) : Pattern → Set ℝ × Finset model.Id
  | .apply "strength" [e] => ({realStrength (model.summary e)}, model.ledger e)
  | .apply "interval" [e] =>
      (Set.Icc
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM.lowerEndpoint
          (model.summary e).pos (model.summary e).neg model.priorStrength)
        (Mettapedia.ProbabilityTheory.ImpreciseProbability.WalleyBinaryIDM.upperEndpoint
          (model.summary e).pos (model.summary e).neg model.priorStrength), model.ledger e)
  | .apply "frechet" [a, b] =>
      (Set.Icc (max 0 (realStrength (model.summary a) + realStrength (model.summary b) - 1))
        (min (realStrength (model.summary a)) (realStrength (model.summary b))),
        model.ledger a ∪ model.ledger b)
  | other => model.atomValue other

noncomputable def holds (model : Model) : Pattern → Prop
  | .apply "ObservationCounts" [q, e] =>
      model.summary e = ledgerEvidence model.world (model.query q) (model.ledger e)
  | .apply "ObservationLowerBound" [q, e] =>
      model.summary e ≤ ledgerEvidence model.world (model.query q) (model.ledger e)
  | .apply "LedgerHolds" [.apply "disjoint" [a, b]] => Disjoint (model.ledger a) (model.ledger b)
  | .apply "LedgerHolds" [.apply "oneWorld" [a, b]] => model.ledger a = model.ledger b
  | .apply "CountReadout" [q, v] =>
      realStrength (ledgerEvidence model.world (model.query q) (model.value v).2) ∈ (model.value v).1
  | _ => False

/-- Restrict a recursive interpretation to the variables of one source schema. -/
def schemaModel (model : Model) (binding : String → Pattern) : Ledger.Model where
  Id := model.Id
  W := model.W
  world := model.world
  interp :=
    { query := fun name => model.query (binding name)
      ledger := fun name => model.ledger (binding name)
      summary := fun name => model.summary (binding name)
      priorStrength := model.priorStrength
      priorStrength_pos := model.priorStrength_pos }

/-- Disjoint observation identities justify additive revision at arbitrary
nested arguments. -/
theorem revise (model : Model) (q first second : Pattern)
    (firstExact : model.holds (observationCounts q first))
    (secondExact : model.holds (observationCounts q second))
    (disjoint : model.holds (ledgerHolds (app "disjoint" [first, second]))) :
    model.holds (observationCounts q (app "revise" [first, second])) := by
  simp only [holds, observationCounts, ledgerHolds, app, summary, ledger] at *
  rw [ledgerEvidence_union_of_disjoint model.world _ disjoint]
  exact congrArg₂ (· + ·) firstExact secondExact

theorem revise_unknown_overlap (model : Model) (q first second : Pattern)
    (firstExact : model.holds (observationCounts q first))
    (secondExact : model.holds (observationCounts q second)) :
    model.holds (observationLowerBound q (app "lowerMerge" [first, second])) := by
  simp only [holds, observationCounts, observationLowerBound, app, summary, ledger] at *
  rw [firstExact, secondExact]
  exact (unknown_overlap_bounds model.world _ _ _).1

theorem negate (model : Model) (q e : Pattern)
    (exactCounts : model.holds (observationCounts q e)) :
    model.holds (observationCounts (app "not" [q]) (app "swap" [e])) := by
  simp only [holds, observationCounts, app, summary, ledger, query, BooleanTermSemantics.eval_not] at *
  rw [ledgerEvidence_not, exactCounts]

theorem read_strength (model : Model) (q e : Pattern)
    (exactCounts : model.holds (observationCounts q e)) :
    model.holds (countReadout q (app "strength" [e])) := by
  change realStrength (ledgerEvidence model.world (model.query q) (model.ledger e)) ∈
    {realStrength (model.summary e)}
  exact congrArg realStrength exactCounts.symm

theorem read_interval (model : Model) (q e : Pattern)
    (exactCounts : model.holds (observationCounts q e)) :
    model.holds (countReadout q (app "interval" [e])) := by
  let binding : String → Pattern := fun name => if name = "q" then q else e
  have sound := readInterval_sound
    (rule "read-interval" ["q", "e"] [observationCounts (fv "q") (fv "e")]
      (countReadout (fv "q") (app "interval" [fv "e"])))
    (by simp [evidenceCalculus, evidenceRules]) rfl (model.schemaModel binding)
  have premise : ∀ p ∈ [observationCounts (fv "q") (fv "e")],
      (model.schemaModel binding).holds p := by
    intro p member
    simp only [List.mem_singleton] at member
    subst p
    simpa [Ledger.Model.holds, Ledger.Interpretation.Holds, Ledger.Interpretation.queryOf,
      Ledger.Interpretation.ledgerOf, Ledger.Interpretation.summaryOf, schemaModel, binding,
      observationCounts, app, fv, holds] using exactCounts
  have result := sound premise
  simpa [Ledger.Model.holds, Ledger.Interpretation.Holds, Ledger.Interpretation.queryOf,
    Ledger.Interpretation.valueOf, schemaModel, binding, countReadout, app, fv,
    holds, value, rule] using result

theorem conjoin_one_world (model : Model) (a b first second : Pattern)
    (firstExact : model.holds (observationCounts a first))
    (secondExact : model.holds (observationCounts b second))
    (same : model.holds (ledgerHolds (app "oneWorld" [first, second]))) :
    model.holds (countReadout (app "and" [a, b]) (app "frechet" [first, second])) := by
  simp only [holds, observationCounts, ledgerHolds, countReadout, app, value, query, BooleanTermSemantics.eval_and] at *
  rw [firstExact, secondExact, same, Finset.union_self]
  simp only [ledgerEvidence_eq_ofSamples, Set.mem_Icc]
  exact frechet_strength _ _ _

end Model

/-- The identified-observation profile reuses the shared source rules. -/
def ledgerCalculus : CalculusLanguageDef :=
  { evidenceCalculus with
    name := "pln-ledger-calculus"
    rules := evidenceCalculus.rules.filter fun schema =>
      decide (settingOf schema.conclusion = some .ledger) }

theorem ledgerCalculus_admitted : ledgerCalculus.isAdmitted = true := by decide +kernel

def ledgerValidated : ValidatedCalculusLanguageDef :=
  ledgerCalculus.validated ledgerCalculus_admitted

/-- Portable text for the same six-rule profile consumed by the checker. -/
def ledgerModule : String := ModuleFormat.Portable.renderCalculus ledgerValidated.val

theorem ledgerModule_read :
    ModuleFormat.Portable.readValidatedCalculus? ledgerModule = some ledgerValidated :=
  ModuleFormat.Portable.readValidatedCalculus_renderCalculus _

/-- Every admitted rule application of the ledger profile preserves its
recursive interpretation. Rule lookup and positional instantiation use the
same checked definition as the generic proof checker. -/
theorem rule_application_sound (model : Model) (ruleInstance : RuleInstance)
    (premises : List Pattern) (conclusion : Pattern)
    (application : RuleApplication ledgerValidated ruleInstance premises conclusion)
    (premisesSound : ∀ premise ∈ premises, model.holds premise) : model.holds conclusion := by
  rcases ruleInstance with ⟨id, arguments⟩
  cases application with
  | intro schema lookup valid _ premisesInstantiate conclusionInstantiates =>
    have member := List.mem_of_find?_eq_some lookup
    change schema ∈ [evidenceRules.get ⟨0, by decide⟩, evidenceRules.get ⟨1, by decide⟩, evidenceRules.get ⟨2, by decide⟩,
      evidenceRules.get ⟨5, by decide⟩, evidenceRules.get ⟨7, by decide⟩, evidenceRules.get ⟨8, by decide⟩] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · have length : arguments.length = 3 := (argumentsValidAt_length valid).symm
      obtain ⟨q, first, second, argumentsEq⟩ := List.length_eq_three.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [evidenceRules, rule, fv, app, observationCounts, observationLowerBound,
        ledgerHolds, countReadout] at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      exact Model.revise model q first second (premisesSound _ List.mem_cons_self) (premisesSound _ (List.mem_cons_of_mem _ List.mem_cons_self)) (premisesSound _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    · have length : arguments.length = 3 := (argumentsValidAt_length valid).symm
      obtain ⟨q, first, second, argumentsEq⟩ := List.length_eq_three.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [evidenceRules, rule, fv, app, observationCounts, observationLowerBound,
        ledgerHolds, countReadout] at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      exact Model.revise_unknown_overlap model q first second (premisesSound _ List.mem_cons_self) (premisesSound _ (List.mem_cons_of_mem _ List.mem_cons_self))
    · have length : arguments.length = 2 := (argumentsValidAt_length valid).symm
      obtain ⟨q, e, argumentsEq⟩ := List.length_eq_two.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [evidenceRules, rule, fv, app, observationCounts, observationLowerBound,
        ledgerHolds, countReadout] at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      exact Model.negate model q e (premisesSound _ List.mem_cons_self)
    · have length : arguments.length = 4 := (argumentsValidAt_length valid).symm
      obtain ⟨a, b, first, second, argumentsEq⟩ := List.length_eq_four.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [evidenceRules, rule, fv, app, observationCounts, observationLowerBound,
        ledgerHolds, countReadout] at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      exact Model.conjoin_one_world model a b first second (premisesSound _ List.mem_cons_self) (premisesSound _ (List.mem_cons_of_mem _ List.mem_cons_self)) (premisesSound _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
    · have length : arguments.length = 2 := (argumentsValidAt_length valid).symm
      obtain ⟨q, e, argumentsEq⟩ := List.length_eq_two.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [evidenceRules, rule, fv, app, observationCounts, observationLowerBound,
        ledgerHolds, countReadout] at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      exact Model.read_strength model q e (premisesSound _ List.mem_cons_self)
    · have length : arguments.length = 2 := (argumentsValidAt_length valid).symm
      obtain ⟨q, e, argumentsEq⟩ := List.length_eq_two.mp length
      subst arguments
      have instantiatedPremises := instantiateSchemasAt?_complete premisesInstantiate
      have instantiatedConclusion := instantiateSchemaAt?_complete conclusionInstantiates
      dsimp only [evidenceRules, rule, fv, app, observationCounts, observationLowerBound,
        ledgerHolds, countReadout] at instantiatedPremises instantiatedConclusion
      simp [instantiateSchemasAt?, instantiateSchemaAt?, lookupArgumentAt?]
        at instantiatedPremises instantiatedConclusion
      cases instantiatedPremises
      cases instantiatedConclusion
      exact Model.read_interval model q e (premisesSound _ List.mem_cons_self)

/-- Checking a complete open proof now implies the semantic conclusion when
its external premise occurrences hold in the model. -/
theorem checked_proof_sound (model : Model) (context : List Pattern) (goal : Pattern)
    (proof : RawOpenProof) (checked : checkOpenRaw ledgerValidated context goal proof = true)
    (contextSound : ∀ premise ∈ context, model.holds premise) : model.holds goal := by
  obtain ⟨derivation, _⟩ := checkOpenRaw_exact_derivation checked
  exact derivation.sound_of_ruleApplications model.holds (rule_application_sound model) contextSound

end Mettapedia.PLN.Bridges.GSLT.LedgerTermSemantics
