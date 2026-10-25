import Mettapedia.Languages.Megalodon.CheckedTermReconstruction
import Mettapedia.Languages.Megalodon.RetainedDeltaNormalization
import Mettapedia.Languages.Megalodon.HenkinProofSoundness
import Mettapedia.Logic.HOL.ProofSyntaxHypothesisSubstitution

/-!
# Retained reconstruction of native monomorphic proof judgments

Native proof hypotheses retain their ordered positions. Named facts are
represented by explicit positions in a supplied list of closed HOL assumptions.
The reconstructed source context puts local hypotheses first and those global
assumptions second. Neither a successful name lookup nor native normalization
asserts the truth of the global assumptions.

Checked definition bodies and their explicit defining equations support the
native beta/eta/delta conversion policy. The opaque declaration profile is a
specialization requiring no definition premises. Prefix polymorphism is
outside the existing monomorphic fragment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.Megalodon.CheckedProofReconstruction

open MathdataKernel HenkinTermInterpretation HenkinTermInterpretation.NativeProof
open Mettapedia.Logic.HOL

variable {environment : Environment} {Γ : Ctx Base}

abbrev Opaque (environment : Environment) : Prop :=
  ∀ name declaration, environment.lookupTerm? name = some declaration → declaration.definition = none

/-- Known declarations retain actual source-theory positions, not only an
unindexed assertion of semantic validity. -/
def KnownSources (theory : List (ClosedFormula (Constant environment))) :=
  ∀ name raw, environment.lookupKnown? name = some raw →
    {index : Fin theory.length // erase (theory.get index) = some raw}

def facts (theory : List (ClosedFormula (Constant environment))) (Γ : Ctx Base) :
    List (Formula (Constant environment) Γ) := theory.map (weakenCtx Γ)

structure Result (hypotheses : List (Formula (Constant environment) Γ)) (raw : Tm) where
  formula : Formula (Constant environment) Γ
  erased : erase formula = some raw
  proof : ProofSyntax (Constant environment) hypotheses formula

private def implicationView (formula : Formula (Constant environment) Γ) {left right : Tm}
    (erased : erase formula = some (.imp left right)) :
    {parts : Formula (Constant environment) Γ × Formula (Constant environment) Γ //
      formula = .imp parts.1 parts.2 ∧ erase parts.1 = some left ∧ erase parts.2 = some right} := by
  cases formula with
  | imp first second =>
      refine ⟨(first, second), rfl, ?_⟩
      cases hf : erase first <;> cases hs : erase second <;> simp [erase, hf, hs] at erased
      obtain ⟨rfl, rfl⟩ := erased
      exact ⟨rfl, rfl⟩
  | _ =>
      exfalso
      obtain ⟨first, second, impossible, _, _⟩ := erase_imp_inv erased
      cases impossible

private def universalView (formula : Formula (Constant environment) Γ) {type : Tp} {raw : Tm}
    (erased : erase formula = some (.all type raw)) :
    Σ domain : Ty Base, {body : Formula (Constant environment) (domain :: Γ) //
      formula = .all body ∧ type = reifyType domain ∧ erase body = some raw} := by
  cases formula with
  | all body =>
      refine ⟨_, body, rfl, ?_⟩
      cases hb : erase body <;> simp [erase, hb] at erased
      obtain ⟨rfl, rfl⟩ := erased
      exact ⟨rfl, rfl⟩
  | _ =>
      exfalso
      obtain ⟨domain, body, impossible, _, _⟩ := erase_all_inv erased
      cases impossible

private def hypothesis (localHypotheses globalFacts : List (Formula (Constant environment) Γ))
    {rawHypotheses : List Tm} (erased : ErasedHypotheses localHypotheses rawHypotheses)
    (index : Nat) {raw : Tm} (lookup : rawHypotheses[index]? = some raw) :
    Result (localHypotheses ++ globalFacts) raw := by
  have lengths : localHypotheses.length = rawHypotheses.length := by
    simpa only [List.length_map] using congrArg List.length erased
  have inRange : index < localHypotheses.length := by
    rw [lengths]
    exact List.getElem?_eq_some_iff.mp lookup |>.1
  let occurrence : Fin localHypotheses.length := ⟨index, inRange⟩
  have formulaErased : erase (localHypotheses.get occurrence) = some raw := by
    have same := congrArg (fun list => list[index]?) erased
    simpa [List.getElem?_map, List.getElem?_eq_getElem inRange, lookup, occurrence] using same
  exact ⟨localHypotheses.get occurrence, formulaErased,
    (ProofSyntax.hyp occurrence).mono (ProofSyntax.OccurrenceMap.appendRight localHypotheses globalFacts)⟩

private def knownHypothesis (theory : List (ClosedFormula (Constant environment)))
    (localHypotheses : List (Formula (Constant environment) Γ)) (index : Fin theory.length) :
    ProofSyntax (Constant environment) (localHypotheses ++ facts theory Γ)
      (weakenCtx Γ (theory.get index)) := by
  let occurrence : Fin (facts theory Γ).length := index.cast (by simp [facts])
  have original : ProofSyntax (Constant environment) (facts theory Γ) (weakenCtx Γ (theory.get index)) :=
    ProofSyntax.castIndices rfl (by simp [facts, occurrence, List.get_eq_getElem]) (.hyp occurrence)
  exact original.mono (ProofSyntax.OccurrenceMap.appendLeft localHypotheses (facts theory Γ))

private def convert {hypotheses : List (Formula (Constant environment) Γ)}
    {source target : Formula (Constant environment) Γ}
    (equation : ProofSyntax (Constant environment) hypotheses (.eq source target))
    (proof : ProofSyntax (Constant environment) hypotheses source) :
    ProofSyntax (Constant environment) hypotheses target :=
  .impE (.eqPropEL equation) proof

private def underLocal (theory : List (ClosedFormula (Constant environment)))
    (hypotheses : List (Formula (Constant environment) Γ))
    {formula : Formula (Constant environment) Γ}
    (proof : ProofSyntax (Constant environment) (facts theory Γ) formula) :
    ProofSyntax (Constant environment) (hypotheses ++ facts theory Γ) formula :=
  proof.mono (ProofSyntax.OccurrenceMap.appendLeft hypotheses (facts theory Γ))

theorem opaqueChecked (opaqueTerms : Opaque environment) : CheckedPlainDefinitions environment where
  body := by
    intro name declaration body lookup defined _
    have contradiction := (opaqueTerms name declaration lookup).symm.trans defined
    cases contradiction

def opaqueEquations (opaqueTerms : Opaque environment)
    (theory : List (ClosedFormula (Constant environment))) :
    RetainedDeltaNormalization.DefinitionEquations (opaqueChecked opaqueTerms) theory := by
  intro type name declaration lookup typed body defined
  have contradiction := (opaqueTerms name declaration lookup).symm.trans defined
  cases contradiction

private theorem normalize_opaque (opaqueTerms : Opaque environment) (fuel : Nat) (raw : Tm) :
    MathdataKernel.normalize environment fuel raw = Tm.normalize fuel raw := by
  simp [MathdataKernel.normalize, deltaNormalize_of_primitive environment opaqueTerms]

private theorem proofApp_parts {depth : Nat} {first second : Pf}
    (fragment : Fragment environment depth (.proofApp first second)) :
    Fragment environment depth first ∧ Fragment environment depth second := by
  cases fragment with | proofApp first second => exact ⟨first, second⟩

private theorem termApp_parts {depth : Nat} {function : Pf} {argument : Tm}
    (fragment : Fragment environment depth (.termApp function argument)) :
    Fragment environment depth function ∧ supported argument = true ∧ PlainLookups environment depth argument := by
  cases fragment with | termApp function supported lookups => exact ⟨function, supported, lookups⟩

private theorem proofLam_parts {depth : Nat} {domain : Tm} {body : Pf}
    (fragment : Fragment environment depth (.proofLam domain body)) :
    supported domain = true ∧ PlainLookups environment depth domain ∧ Fragment environment depth body := by
  cases fragment with | proofLam supported lookups body => exact ⟨supported, lookups, body⟩

private theorem termLam_body {depth : Nat} {type : Tp} {body : Pf}
    (fragment : Fragment environment depth (.termLam type body)) : Fragment environment depth body := by
  cases fragment with | termLam body => exact body

private theorem facts_cons (theory : List (ClosedFormula (Constant environment))) (type : Ty Base) (Γ : Ctx Base) :
    facts theory (type :: Γ) = weakenHyps (σ := type) (facts theory Γ) := by
  simp [facts, weakenHyps, List.map_map, weakenCtx_cons]

/-- Reconstruct the actual checked proof, preserving its exact returned raw
formula and every ordered local assumption. Global known facts are explicit
source assumptions, and the declaration policy is stated independently. -/
def reconstructDefined (checked : CheckedPlainDefinitions environment)
    (theory : List (ClosedFormula (Constant environment)))
    (equations : RetainedDeltaNormalization.DefinitionEquations checked theory) (known : KnownSources theory)
    (fuel depth : Nat) {Γ : Ctx Base}
    (hypotheses : List (Formula (Constant environment) Γ)) {rawHypotheses : List Tm}
    (erased : ErasedHypotheses hypotheses rawHypotheses) (proof : Pf)
    (fragment : Fragment environment depth proof) {result : Tm}
    (accepted : inferProof environment fuel depth (Γ.map reifyType) rawHypotheses proof = some result) :
    Result (hypotheses ++ facts theory Γ) result :=
  match proof with
  | .hyp index => hypothesis hypotheses (facts theory Γ) erased index accepted
  | .gpa _ => by simp [inferProof] at accepted
  | .known name => by
      cases lookup : environment.lookupKnown? name with
      | none => simp [inferProof, lookup] at accepted
      | some raw =>
          have normalized : MathdataKernel.normalize environment fuel raw = some result := by
            simpa [inferProof, lookup] using accepted
          let source := known name raw lookup
          let formula := theory.get source.val
          have formulaErased : erase (weakenCtx Γ formula) = some raw :=
            (erase_weakenCtx formula Γ).trans source.property
          let output := RetainedDeltaNormalization.normalize checked theory equations fuel (weakenCtx Γ formula) formulaErased normalized
          exact ⟨output.target, output.erased,
            convert (underLocal theory hypotheses output.proof) (knownHypothesis theory hypotheses source.val)⟩
  | .proofApp function argument => by
      have parts := proofApp_parts fragment
      cases inferredFunction : inferProof environment fuel depth (Γ.map reifyType) rawHypotheses function with
      | none => simp [inferProof, inferredFunction] at accepted
      | some functionResult =>
          cases functionResult <;> try simp [inferProof, inferredFunction] at accepted
          case imp domain codomain =>
            cases inferredArgument : inferProof environment fuel depth (Γ.map reifyType) rawHypotheses argument with
            | none => simp [inferredArgument] at accepted
            | some argumentResult =>
                by_cases same : argumentResult = domain
                · subst argumentResult
                  have sameResult : codomain = result := by
                    simpa [inferProof, inferredFunction, inferredArgument] using accepted
                  subst result
                  obtain ⟨functionFormula, functionErased, functionProof⟩ :=
                    reconstructDefined checked theory equations known fuel depth hypotheses erased function parts.1 inferredFunction
                  obtain ⟨argumentFormula, argumentErased, argumentProof⟩ :=
                    reconstructDefined checked theory equations known fuel depth hypotheses erased argument parts.2 inferredArgument
                  obtain ⟨⟨domainFormula, codomainFormula⟩, rfl, domainErased, codomainErased⟩ :=
                    implicationView functionFormula functionErased
                  have equal := erase_injective_of_eq_some argumentErased domainErased
                  subst argumentFormula
                  exact ⟨codomainFormula, codomainErased, .impE functionProof argumentProof⟩
                · simp [inferredArgument, same] at accepted
  | .termApp function argument => by
      have parts := termApp_parts fragment
      cases inferredFunction : inferProof environment fuel depth (Γ.map reifyType) rawHypotheses function with
      | none => simp [inferProof, inferredFunction] at accepted
      | some functionResult =>
          cases functionResult <;> try simp [inferProof, inferredFunction] at accepted
          case all domain body =>
            cases inferredArgument : inferTerm environment depth (Γ.map reifyType) argument with
            | none => simp [inferredArgument] at accepted
            | some argumentType =>
                by_cases same : argumentType = domain
                · subst argumentType
                  cases expandedArgument : deltaNormalize environment fuel argument with
                  | none => simp [inferredArgument, expandedArgument] at accepted
                  | some argumentRaw =>
                    have normalized : MathdataKernel.normalize environment fuel
                        (Tm.instantiate argumentRaw body) = some result := by
                      simpa [inferProof, inferredFunction, inferredArgument, expandedArgument] using accepted
                    obtain ⟨functionFormula, functionErased, functionProof⟩ :=
                      reconstructDefined checked theory equations known fuel depth hypotheses erased function parts.1 inferredFunction
                    obtain ⟨type, bodyFormula, rfl, typeErased, bodyErased⟩ :=
                      universalView functionFormula functionErased
                    let argumentTerm := CheckedTermReconstruction.atType (context := Γ) (type := type) argument
                      parts.2.2 parts.2.1 (inferredArgument.trans (congrArg some typeErased))
                    let expandedTerm := RetainedDeltaNormalization.delta checked theory equations fuel
                      argumentTerm.val argumentTerm.property expandedArgument
                    have instantiated : erase (instantiate expandedTerm.target bodyFormula) =
                        some (Tm.instantiate argumentRaw body) := by
                      rw [erase_instantiate expandedTerm.target bodyFormula expandedTerm.erased, bodyErased]
                      rfl
                    let output := RetainedDeltaNormalization.normalize checked theory equations fuel
                      (instantiate expandedTerm.target bodyFormula) instantiated normalized
                    exact ⟨output.target, output.erased,
                      convert (underLocal theory hypotheses output.proof) (.allE expandedTerm.target functionProof)⟩
                · simp [inferredArgument, same] at accepted
  | .proofLam proposition body => by
      have parts := proofLam_parts fragment
      cases inferred : inferTerm environment depth (Γ.map reifyType) proposition with
      | none => simp [inferProof, inferred] at accepted
      | some propositionType =>
          cases propositionType <;> try simp [inferProof, inferred] at accepted
          case prop =>
            cases normalized : MathdataKernel.normalize environment fuel proposition with
            | none => simp [normalized] at accepted
            | some rawDomain =>
              cases inferredBody : inferProof environment fuel depth (Γ.map reifyType)
                  (rawDomain :: rawHypotheses) body with
              | none => simp [normalized, inferredBody] at accepted
              | some rawBody =>
                  have sameResult : Tm.imp rawDomain rawBody = result := by
                    simpa [inferProof, inferred, normalized, inferredBody] using accepted
                  subst result
                  let propositionTerm := CheckedTermReconstruction.atType (context := Γ) (type := .prop)
                    proposition parts.2.1 parts.1 inferred
                  let domain := RetainedDeltaNormalization.normalize checked theory equations fuel
                    propositionTerm.val propositionTerm.property normalized
                  obtain ⟨bodyFormula, bodyErased, bodyProof⟩ :=
                    reconstructDefined checked theory equations known fuel depth (domain.target :: hypotheses)
                      (erased.cons domain.erased) body parts.2.2 inferredBody
                  exact ⟨.imp domain.target bodyFormula,
                    by simp [erase, domain.erased, bodyErased], .impI bodyProof⟩
  | .termLam type body => by
      have bodyFragment := termLam_body fragment
      by_cases plain : type.plainWellFormed depth = true
      · let domain := CheckedTermReconstruction.reconstructType plain
        cases inferredBody : inferProof environment fuel depth (type :: Γ.map reifyType)
            (rawHypotheses.map (Tm.shift 0 1)) body with
        | none => simp [inferProof, plain, inferredBody] at accepted
        | some rawBody =>
            have sameResult : Tm.all type rawBody = result := by
              simpa [inferProof, plain, inferredBody] using accepted
            subst result
            have bodyAccepted : inferProof environment fuel depth ((domain.val :: Γ).map reifyType)
                (rawHypotheses.map (Tm.shift 0 1)) body = some rawBody := by
              simpa only [List.map_cons, domain.property] using inferredBody
            obtain ⟨bodyFormula, bodyErased, bodyProof⟩ :=
              reconstructDefined checked theory equations known fuel depth (weakenHyps (σ := domain.val) hypotheses)
                erased.weaken body bodyFragment bodyAccepted
            have rearranged : ProofSyntax (Constant environment)
                (weakenHyps (σ := domain.val) (hypotheses ++ facts theory Γ)) bodyFormula :=
              ProofSyntax.castIndices (by simp [weakenHyps, facts_cons, List.map_append]) rfl bodyProof
            exact ⟨.all bodyFormula, by simp [erase, bodyErased, domain.property], .allI rearranged⟩
      · simp [inferProof, plain] at accepted
  | .typeApp _ _ => by exfalso; cases fragment
  | .typeLam _ => by exfalso; cases fragment

/-- Checking against an authored, typed proposition reconstructs a proof of
that proposition, not merely of its normalized representation. -/
def checkedSourceDefined (checked : CheckedPlainDefinitions environment)
    (theory : List (ClosedFormula (Constant environment)))
    (equations : RetainedDeltaNormalization.DefinitionEquations checked theory) (known : KnownSources theory)
    (fuel depth : Nat) {Γ : Ctx Base}
    (hypotheses : List (Formula (Constant environment) Γ)) {rawHypotheses : List Tm}
    (erased : ErasedHypotheses hypotheses rawHypotheses) (proof : Pf)
    (fragment : Fragment environment depth proof) (goal : Formula (Constant environment) Γ)
    {rawGoal : Tm} (goalErased : erase goal = some rawGoal)
    (accepted : checkProof environment fuel depth (Γ.map reifyType) rawHypotheses proof rawGoal = true) :
    ProofSyntax (Constant environment) (hypotheses ++ facts theory Γ) goal := by
  cases normalized : MathdataKernel.normalize environment fuel rawGoal with
  | none => simp [checkProof, normalized] at accepted
  | some target =>
      have inferred : inferProof environment fuel depth (Γ.map reifyType) rawHypotheses proof = some target := by
        simpa [checkProof, normalized, checkNormalizedProof] using accepted
      let result := reconstructDefined checked theory equations known fuel depth hypotheses erased proof fragment inferred
      let goalNormal := RetainedDeltaNormalization.normalize checked theory equations fuel goal goalErased normalized
      have same : result.formula = goalNormal.target :=
        erase_injective_of_eq_some result.erased goalNormal.erased
      exact convert (underLocal theory hypotheses (.eqSymm goalNormal.proof)) (same ▸ result.proof)

/-- Opaque declarations are the equation-free specialization of the same
reconstruction, not a second proof traversal. -/
def reconstruct (opaqueTerms : Opaque environment)
    (theory : List (ClosedFormula (Constant environment))) (known : KnownSources theory) :=
  reconstructDefined (opaqueChecked opaqueTerms) theory (opaqueEquations opaqueTerms theory) known

/-- Exact authored-goal checking under the opaque declaration policy. -/
def checkedSource (opaqueTerms : Opaque environment)
    (theory : List (ClosedFormula (Constant environment))) (known : KnownSources theory) :=
  checkedSourceDefined (opaqueChecked opaqueTerms) theory (opaqueEquations opaqueTerms theory) known

universe w

/-- Semantic soundness is now a consequence of the computed ordinary HOL
proof, relative to the stated local and global assumptions. -/
theorem checkedSource_sound (opaqueTerms : Opaque environment)
    (theory : List (ClosedFormula (Constant environment))) (known : KnownSources theory)
    (fuel depth : Nat) {Γ : Ctx Base}
    (hypotheses : List (Formula (Constant environment) Γ)) {rawHypotheses : List Tm}
    (erased : ErasedHypotheses hypotheses rawHypotheses) (proof : Pf)
    (fragment : Fragment environment depth proof) (goal : Formula (Constant environment) Γ)
    {rawGoal : Tm} (goalErased : erase goal = some rawGoal)
    (accepted : checkProof environment fuel depth (Γ.map reifyType) rawHypotheses proof rawGoal = true)
    (model : HenkinModel.{0, 0, w} Base (Constant environment)) (respects : model.FunctionsRespectEqv)
    (valuation : model.Valuation Γ) (admissible : model.ValuationAdmissible valuation)
    (satisfied : Soundness.SatisfiesHyps model valuation (hypotheses ++ facts theory Γ)) :
    (model.denote goal valuation).down :=
  Soundness.extDerivation_sound
    (checkedSource opaqueTerms theory known fuel depth hypotheses erased proof fragment goal goalErased accepted).erase
    respects admissible satisfied

/-- The reconstructed definition-sensitive derivation is sound under its
explicit local assumptions, known facts and defining equations. -/
theorem checkedSourceDefined_sound (checked : CheckedPlainDefinitions environment)
    (theory : List (ClosedFormula (Constant environment)))
    (equations : RetainedDeltaNormalization.DefinitionEquations checked theory) (known : KnownSources theory)
    (fuel depth : Nat) {Γ : Ctx Base}
    (hypotheses : List (Formula (Constant environment) Γ)) {rawHypotheses : List Tm}
    (erased : ErasedHypotheses hypotheses rawHypotheses) (proof : Pf)
    (fragment : Fragment environment depth proof) (goal : Formula (Constant environment) Γ)
    {rawGoal : Tm} (goalErased : erase goal = some rawGoal)
    (accepted : checkProof environment fuel depth (Γ.map reifyType) rawHypotheses proof rawGoal = true)
    (model : HenkinModel.{0, 0, w} Base (Constant environment)) (respects : model.FunctionsRespectEqv)
    (valuation : model.Valuation Γ) (admissible : model.ValuationAdmissible valuation)
    (satisfied : Soundness.SatisfiesHyps model valuation (hypotheses ++ facts theory Γ)) :
    (model.denote goal valuation).down :=
  Soundness.extDerivation_sound
    (checkedSourceDefined checked theory equations known fuel depth hypotheses erased proof fragment goal goalErased accepted).erase
    respects admissible satisfied

namespace Controls

abbrev NoConstants := Constant ({} : Environment)

theorem noDefinitions : Opaque ({} : Environment) := by
  intro name declaration lookup
  simp [Environment.lookupTerm?, lookupTermList?] at lookup

def noKnown : KnownSources (environment := {}) [] := by
  intro name raw lookup
  simp [Environment.lookupKnown?, lookupKnownList?] at lookup

def identityGoal : ClosedFormula NoConstants := .all (.imp (.var .vz) (.var .vz))
def identityRaw : Tm := .all .prop (.imp (.db 0) (.db 0))
def identityProof : Pf := .termLam .prop (.proofLam (.db 0) (.hyp 0))

theorem identity_fragment : Fragment {} 0 identityProof := .termLam (.proofLam rfl trivial (.hyp 0))
theorem identity_erased : erase identityGoal = some identityRaw := rfl

theorem identity_native_checked : checkProof {} 2 0 [] [] identityProof identityRaw = true := by
  simp [checkProof, checkNormalizedProof, identityProof, identityRaw, normalize_opaque noDefinitions,
    inferProof, inferTerm, Tp.plainWellFormed, Tm.normalize, Tm.normalizeOne]

def identityRetained : ProofSyntax NoConstants [] identityGoal :=
  checkedSource noDefinitions [] noKnown 2 0 (Γ := []) [] (rawHypotheses := []) rfl identityProof identity_fragment
    identityGoal identity_erased identity_native_checked

theorem false_goal_refused : checkProof {} 2 0 [] [] identityProof (.all .prop (.db 0)) = false := by
  simp [checkProof, checkNormalizedProof, identityProof, normalize_opaque noDefinitions,
    inferProof, inferTerm, Tp.plainWellFormed, Tm.normalize, Tm.normalizeOne]

def proposition : Formula NoConstants [.prop] := .var .vz

def secondHypothesis := reconstruct noDefinitions [] noKnown 0 0 [proposition, proposition]
  (rawHypotheses := [.db 0, .db 0]) rfl (.hyp 1) (.hyp 1) rfl

theorem second_occurrence_retained : secondHypothesis.proof.rootObservation.hypothesisOccurrence = some 1 := rfl

end Controls

end Mettapedia.Languages.Megalodon.CheckedProofReconstruction
