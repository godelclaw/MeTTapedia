import Mettapedia.Languages.Megalodon.ExtensionalityAxiomProofs
import Mettapedia.Languages.Megalodon.SetOperationCompilerAcceptance
import Mettapedia.Logic.HOL.Syntax.TypeSubstitutionComposition

/-!
# Retained reconstruction under the common material declaration profile

Each declared extensionality fact has an independently constructed source
proof at its exact normalized native reading. Reconstruction preserves local
hypothesis occurrences and discharges these global facts by proof substitution.
The common operation names retain their declaration lookup and typed roles.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.Megalodon.SetOperationProofReconstruction
open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation
open HenkinTermInterpretation.NativeProof
open SetOperationExtensionality

private def knownPosition (declarations : List KnownDecl) (name : Name) (raw : Tm)
    (found : lookupKnownList? declarations name = some raw) :
    {index : Fin declarations.length // (declarations.get index).proposition = raw} := by
  match declarations with
  | [] => cases found
  | head :: tail =>
      if same : (head.name == name) = true then
        have literal : some head.proposition = some raw := by
          simpa only [lookupKnownList?, if_pos same] using found
        exact ⟨⟨0, by simp⟩, Option.some.inj literal⟩
      else
        have rest : lookupKnownList? tail name = some raw := by
          simpa only [lookupKnownList?, if_neg same] using found
        let later := knownPosition tail name raw rest
        exact ⟨later.val.succ, later.property⟩
termination_by declarations.length

def sourceTheory (instances : List (Ty Base × Ty Base)) : List (ClosedFormula (Constant (environment instances))) :=
  (ExtensionalityAxiomProofs.propositionalNative (environment := environment instances)).formula ::
    instances.map (fun pair => (ExtensionalityAxiomProofs.functionalNative
      (environment := environment instances) pair.1 pair.2).formula)

theorem sourceTheory_erased (instances : List (Ty Base × Ty Base)) :
    (sourceTheory instances).map erase = (SetOperationExtensionality.facts instances).map (fun fact => some fact.proposition) := by
  have first := (ExtensionalityAxiomProofs.propositionalNative (environment := environment instances)).erased
  have each (pair : Ty Base × Ty Base) :=
    (ExtensionalityAxiomProofs.functionalNative (environment := environment instances) pair.1 pair.2).erased
  simp only [sourceTheory, SetOperationExtensionality.facts, List.map_cons, List.map_map, first]
  apply congrArg (List.cons (some ExtensionalityAxioms.Native.propositional))
  calc
    _ = instances.map (fun pair => some (ExtensionalityAxioms.Native.functional (reifyType pair.1) (reifyType pair.2))) := by
      apply List.map_congr_left
      intro pair _
      exact each pair
    _ = _ := by
      conv_lhs => rw [← List.zipIdx_map_fst 0 instances]
      rw [List.map_map]
      rfl

def proofAt (instances : List (Ty Base × Ty Base)) (index : Fin (sourceTheory instances).length) :
    ProofSyntax (Constant (environment instances)) [] ((sourceTheory instances).get index) := by
  rcases index with ⟨number, bounded⟩
  cases number with
  | zero => exact (ExtensionalityAxiomProofs.propositionalNative (environment := environment instances)).proof
  | succ number =>
      have smaller : number < instances.length := by simpa only [sourceTheory, List.length_cons, List.length_map, Nat.succ_lt_succ_iff] using bounded
      simpa only [sourceTheory, List.get_eq_getElem, List.getElem_cons_succ, List.getElem_map] using
        (ExtensionalityAxiomProofs.functionalNative (environment := environment instances)
          (instances[number]).1 (instances[number]).2).proof

def knownSources (instances : List (Ty Base × Ty Base)) :
    CheckedProofReconstruction.KnownSources (environment := environment instances) (sourceTheory instances) := by
  intro name raw found
  let selected := knownPosition (SetOperationExtensionality.facts instances) name raw found
  have lengths : (sourceTheory instances).length = (SetOperationExtensionality.facts instances).length := by
    simp [sourceTheory, SetOperationExtensionality.facts]
  let index : Fin (sourceTheory instances).length := selected.val.cast lengths.symm
  refine ⟨index, ?_⟩
  have aligned := congrArg (fun entries : List (Option Tm) => entries[selected.val.val]?) (sourceTheory_erased instances)
  have sourceBound : selected.val.val < (sourceTheory instances).length := by simpa only [index, Fin.val_cast] using index.isLt
  simp only [List.getElem?_map, List.getElem?_eq_getElem sourceBound,
    List.getElem?_eq_getElem selected.val.isLt, Option.map_some, Option.some.injEq] at aligned
  have literal : erase ((sourceTheory instances).get index) = some ((SetOperationExtensionality.facts instances).get selected.val).proposition := aligned
  exact literal.trans (congrArg some selected.property)

theorem opaqueTerms (instances : List (Ty Base × Ty Base)) : CheckedProofReconstruction.Opaque (environment instances) := by
  intro name declaration found
  exact SetOperationSemantics.lookup_opaque name declaration found

def withoutGlobalFacts (instances : List (Ty Base × Ty Base)) {gamma : Ctx Base}
    (localHypotheses : List (Formula (Constant (environment instances)) gamma)) {goal : Formula (Constant (environment instances)) gamma}
    (proof : ProofSyntax (Constant (environment instances))
      (localHypotheses ++ CheckedProofReconstruction.facts (sourceTheory instances) gamma) goal) :
    ProofSyntax (Constant (environment instances)) localHypotheses goal := by
  have supplied : ProofSyntax.HypothesisSubstitution
      (CheckedProofReconstruction.facts (sourceTheory instances) gamma) localHypotheses := by
    intro occurrence
    let original : Fin (sourceTheory instances).length := occurrence.cast (by simp [CheckedProofReconstruction.facts])
    have closed := ProofSyntax.weakenContext gamma (proofAt instances original)
    have carried := closed.mono (ProofSyntax.emptyOccurrenceMap localHypotheses)
    simpa only [CheckedProofReconstruction.facts, List.get_eq_getElem, List.getElem_map, original, Fin.val_cast] using carried
  exact proof.substituteHypotheses
    (ProofSyntax.HypothesisSubstitution.append _ _ _ (ProofSyntax.HypothesisSubstitution.identity _) supplied)

def nativeSource (instances : List (Ty Base × Ty Base)) (fuel depth : Nat) {gamma : Ctx Base}
    (hypotheses : List (Formula (Constant (environment instances)) gamma)) {rawHypotheses : List Tm}
    (erased : ErasedHypotheses hypotheses rawHypotheses) (program : Pf)
    (fragment : Fragment (environment instances) depth program) (goal : Formula (Constant (environment instances)) gamma)
    {rawGoal : Tm} (goalErased : erase goal = some rawGoal)
    (accepted : checkProof (environment instances) fuel depth (gamma.map reifyType) rawHypotheses program rawGoal = true) :
    ProofSyntax (Constant (environment instances)) hypotheses goal :=
  withoutGlobalFacts instances hypotheses
    (CheckedProofReconstruction.checkedSource (opaqueTerms instances) (sourceTheory instances) (knownSources instances)
      fuel depth hypotheses erased program fragment goal goalErased accepted)

def canonicalSource (instances : List (Ty Base × Ty Base)) (fuel depth : Nat) {gamma : Ctx Base}
    (hypotheses : List (Formula (Constant (environment instances)) gamma))
    (goal : Formula (Constant (environment instances)) gamma) (program : Pf)
    (fragment : Fragment (environment instances) depth program)
    (accepted : checkProof (environment instances) fuel depth (gamma.map reifyType)
      (hypotheses.map HOLNormalForms.normalFormCode) program (HOLTermEncoding.native goal) = true) :
    ProofSyntax (Constant (environment instances)) hypotheses goal := by
  let canonical := hypotheses.map HOLNormalForms.normalForm
  have erased : ErasedHypotheses canonical (hypotheses.map HOLNormalForms.normalFormCode) := by
    change (hypotheses.map HOLNormalForms.normalForm).map erase = (hypotheses.map HOLNormalForms.normalFormCode).map some
    simp only [List.map_map]
    apply List.map_congr_left
    intro formula _
    exact HOLNormalForms.normalForm_erased formula
  let retained := nativeSource instances fuel depth canonical erased program fragment
    (HOLTermEncoding.encode goal) (HOLTermEncoding.native_erased goal) accepted
  have supplied : ProofSyntax.HypothesisSubstitution canonical hypotheses := by
    intro occurrence
    let original : Fin hypotheses.length := occurrence.cast (by simp [canonical])
    let equation := (HOLTermEncodingProofs.normalFormEquation (hypotheses.get original)).mono
      (ProofSyntax.emptyOccurrenceMap hypotheses)
    have normalized : ProofSyntax (Constant (environment instances)) hypotheses (HOLNormalForms.normalForm (hypotheses.get original)) :=
      .impE (.eqPropEL equation) (.hyp original)
    simpa only [canonical, List.get_eq_getElem, List.getElem_map, original, Fin.val_cast] using normalized
  exact .impE (.eqPropER (HOLTermEncodingProofs.equation goal hypotheses)) (retained.substituteHypotheses supplied)

open Embedding.ZFSetHenkinInterpretation (Symbol)
open SetOperationProofCompilation (base type)

def materialConstant (instances : List (Ty Base × Ty Base)) {value : Ty Base}
    (constant : Constant (SetOperationExtensionality.environment instances) value) :
    Symbol (SetOperationSemantics.materialType value) :=
  SetOperationSemantics.materialSymbol (SetOperationExtensionality.forgetConstant constant)

theorem materialConstant_symbol (instances : List (Ty Base × Ty Base)) {value : Ty Unit} (symbol : Symbol value) :
    HEq (materialConstant instances (SetOperationExtensionality.symbol instances symbol)) symbol := by
  cases symbol <;> rfl

private theorem type_roundTrip (value : Ty Unit) :
    Ty.substitute SetOperationSemantics.materialBase (Ty.substitute base value) = value :=
  SetOperationSemantics.materialType_type value

theorem context_roundTrip (gamma : Ctx Unit) :
    (gamma.map (Ty.substitute base)).map (Ty.substitute SetOperationSemantics.materialBase) = gamma := by
  simp only [List.map_map, Function.comp_def, type_roundTrip]
  change gamma.map id = gamma
  exact List.map_id gamma

private theorem context_comp (gamma : Ctx Unit) :
    gamma.map (Ty.substitute SetOperationSemantics.materialBase ∘ Ty.substitute base) = gamma := by
  simpa only [List.map_map] using context_roundTrip gamma

theorem variable_roundTrip {gamma : Ctx Unit} {value : Ty Unit} (index : Var gamma value) :
    HEq ((index.mapTypes base).mapTypes SetOperationSemantics.materialBase) index := by
  induction index <;> simp only [Var.mapTypes] <;> congr 1 <;>
    first | assumption | exact type_roundTrip _ | exact context_roundTrip _

def materialTerm (instances : List (Ty Base × Ty Base)) {gamma : Ctx Base} {value : Ty Base}
    (source : Term (Constant (SetOperationExtensionality.environment instances)) gamma value) :
    Term Symbol (gamma.map SetOperationSemantics.materialType) (SetOperationSemantics.materialType value) :=
  mapTypes SetOperationSemantics.materialBase (materialConstant instances) source

theorem term_roundTrip (instances : List (Ty Base × Ty Base)) {gamma : Ctx Unit} {value : Ty Unit}
    (source : Term Symbol gamma value) :
    HEq (materialTerm instances (SetOperationExtensionality.term instances source)) source := by
  induction source <;> simp only [materialTerm, SetOperationExtensionality.term, mapTypes] <;>
    congr 1 <;> first
    | assumption
    | exact type_roundTrip _
    | exact context_roundTrip _
    | exact context_comp _
    | exact variable_roundTrip _
    | exact materialConstant_symbol instances _

private def changeContext {gamma delta : Ctx Unit} (same : gamma = delta)
    {assumptions : List (Formula Symbol gamma)} {goal : Formula Symbol gamma}
    (proof : ProofSyntax Symbol assumptions goal) : ProofSyntax Symbol (same ▸ assumptions) (same ▸ goal) := by
  cases same
  exact proof

private theorem contextCast_heq {gamma delta : Ctx Unit} (same : gamma = delta) (formula : Formula Symbol gamma) :
    HEq (same ▸ formula) formula := by cases same; rfl

private theorem contextCast_map {gamma delta source : Ctx Unit} (same : gamma = delta)
    (interpret : Formula Symbol source → Formula Symbol gamma) (inputs : List (Formula Symbol source)) :
    (same ▸ inputs.map interpret) = inputs.map (fun formula => same ▸ interpret formula) := by cases same; rfl

theorem cast_term_roundTrip (instances : List (Ty Base × Ty Base)) {gamma : Ctx Unit} (formula : Formula Symbol gamma) :
    (context_roundTrip gamma ▸ materialTerm instances (SetOperationExtensionality.term instances formula)) = formula :=
  eq_of_heq ((contextCast_heq (context_roundTrip gamma) _).trans (term_roundTrip instances formula))

def commonSignature (instances : List (Ty Base × Ty Base)) {gamma : Ctx Unit}
    {assumptions : List (Formula Symbol gamma)} {goal : Formula Symbol gamma}
    (proof : ProofSyntax (Constant (SetOperationExtensionality.environment instances))
      (assumptions.map (SetOperationExtensionality.term instances)) (SetOperationExtensionality.term instances goal)) :
    ProofSyntax Symbol assumptions goal := by
  let mapped := ProofSyntax.mapTypes SetOperationSemantics.materialBase (materialConstant instances) proof
  let restored := changeContext (context_roundTrip gamma) mapped
  have assumptionEq : (context_roundTrip gamma ▸
      ((assumptions.map (SetOperationExtensionality.term instances)).map (materialTerm instances))) = assumptions := by
    have merge : ((assumptions.map (SetOperationExtensionality.term instances)).map (materialTerm instances)) =
        assumptions.map (fun (formula : Formula Symbol gamma) => materialTerm instances (SetOperationExtensionality.term instances formula)) := by
      simp only [List.map_map, Function.comp_def]
    calc
      _ = context_roundTrip gamma ▸ assumptions.map (fun (formula : Formula Symbol gamma) => materialTerm instances (SetOperationExtensionality.term instances formula)) :=
        congrArg (fun values : List (Formula Symbol ((gamma.map type).map SetOperationSemantics.materialType)) => context_roundTrip gamma ▸ values) merge
      _ = assumptions.map (fun (formula : Formula Symbol gamma) => context_roundTrip gamma ▸ materialTerm instances (SetOperationExtensionality.term instances formula)) :=
        contextCast_map (context_roundTrip gamma) _ assumptions
      _ = assumptions.map id := by
        apply List.map_congr_left
        intro formula _
        exact cast_term_roundTrip instances formula
      _ = assumptions := List.map_id assumptions
  exact ProofSyntax.castIndices assumptionEq (cast_term_roundTrip instances goal) restored

def checkedSource (instances : List (Ty Base × Ty Base)) (fuel depth : Nat) {gamma : Ctx Unit}
    (assumptions : List (Formula Embedding.ZFSetHenkinInterpretation.Symbol gamma))
    (goal : Formula Embedding.ZFSetHenkinInterpretation.Symbol gamma) (program : Pf)
    (fragment : Fragment (environment instances) depth program)
    (accepted : checkProof (environment instances) fuel depth ((gamma.map SetOperationProofCompilation.type).map reifyType)
      (assumptions.map (fun formula => HOLNormalForms.normalFormCode (SetOperationExtensionality.term instances formula)))
      program (HOLTermEncoding.native (SetOperationExtensionality.term instances goal)) = true) :
    ProofSyntax Embedding.ZFSetHenkinInterpretation.Symbol assumptions goal := by
  let translated := assumptions.map (fun formula => SetOperationExtensionality.term instances formula)
  have admitted : checkProof (environment instances) fuel depth ((gamma.map type).map reifyType)
      (translated.map HOLNormalForms.normalFormCode) program (HOLTermEncoding.native (SetOperationExtensionality.term instances goal)) = true := by
    simpa only [translated, List.map_map, Function.comp_def] using accepted
  exact commonSignature instances (canonicalSource instances fuel depth translated
    (SetOperationExtensionality.term instances goal) program fragment admitted)

theorem accepted_source (instances : List (Ty Base × Ty Base)) (fuel depth : Nat) {gamma : Ctx Unit}
    (assumptions : List (Formula Embedding.ZFSetHenkinInterpretation.Symbol gamma))
    (goal : Formula Embedding.ZFSetHenkinInterpretation.Symbol gamma) (program : Pf)
    (fragment : Fragment (environment instances) depth program)
    (accepted : checkProof (environment instances) fuel depth ((gamma.map SetOperationProofCompilation.type).map reifyType)
      (assumptions.map (fun formula => HOLNormalForms.normalFormCode (SetOperationExtensionality.term instances formula)))
      program (HOLTermEncoding.native (SetOperationExtensionality.term instances goal)) = true) :
    ExtDerivation Embedding.ZFSetHenkinInterpretation.Symbol assumptions goal :=
  (checkedSource instances fuel depth assumptions goal program fragment accepted).erase

/-- A supplied proof uses finitely many extensionality instances. Conversely,
every accepted program in one such admitted profile yields a source derivation.
The profile union here concerns these explicit schemas and opaque declarations. -/
theorem accepted_profile_iff_source {gamma : Ctx Unit}
    (assumptions : List (Formula Embedding.ZFSetHenkinInterpretation.Symbol gamma))
    (goal : Formula Embedding.ZFSetHenkinInterpretation.Symbol gamma) :
    (∃ (instances : List (Ty Base × Ty Base)) (fuel depth : Nat) (program : Pf),
      Fragment (environment instances) depth program ∧
      checkProof (environment instances) fuel depth ((gamma.map SetOperationProofCompilation.type).map reifyType)
        (assumptions.map (fun formula => HOLNormalForms.normalFormCode (SetOperationExtensionality.term instances formula)))
        program (HOLTermEncoding.native (SetOperationExtensionality.term instances goal)) = true) ↔
      ExtDerivation Embedding.ZFSetHenkinInterpretation.Symbol assumptions goal := by
  constructor
  · rintro ⟨instances, fuel, depth, program, fragment, accepted⟩
    exact accepted_source instances fuel depth assumptions goal program fragment accepted
  · intro derivation
    obtain ⟨source⟩ := ProofSyntax.nonempty_of_derivation derivation
    let instances := SetOperationCompilerAcceptance.requiredInstances source
    obtain ⟨fuel, accepted⟩ := SetOperationCompilerAcceptance.accepted_required source
    exact ⟨instances, fuel, 0, SetOperationExtensionality.compile instances source,
      SetOperationCompilerAcceptance.compiled_fragment instances source, accepted⟩

universe w

/-- The reconstructed source judgment is sound in every extensional Henkin
model at admissible valuations. Full function domains are not required. -/
theorem accepted_meaning (instances : List (Ty Base × Ty Base)) (fuel depth : Nat) {gamma : Ctx Unit}
    (assumptions : List (Formula Embedding.ZFSetHenkinInterpretation.Symbol gamma))
    (goal : Formula Embedding.ZFSetHenkinInterpretation.Symbol gamma) (program : Pf)
    (fragment : Fragment (environment instances) depth program)
    (accepted : checkProof (environment instances) fuel depth ((gamma.map SetOperationProofCompilation.type).map reifyType)
      (assumptions.map (fun formula => HOLNormalForms.normalFormCode (SetOperationExtensionality.term instances formula)))
      program (HOLTermEncoding.native (SetOperationExtensionality.term instances goal)) = true)
    (model : HenkinModel.{0, 0, w} Unit Embedding.ZFSetHenkinInterpretation.Symbol)
    (respects : model.FunctionsRespectEqv) (valuation : model.Valuation gamma)
    (admissible : model.ValuationAdmissible valuation)
    (satisfied : Soundness.SatisfiesHyps model valuation assumptions) :
    (model.denote goal valuation).down :=
  Soundness.extDerivation_sound (accepted_source instances fuel depth assumptions goal program fragment accepted)
    respects admissible satisfied

#print axioms accepted_meaning
#print axioms materialConstant_symbol
#print axioms term_roundTrip
#print axioms checkedSource
#print axioms accepted_source
#print axioms accepted_profile_iff_source
#print axioms canonicalSource
#print axioms sourceTheory_erased
#print axioms proofAt
#print axioms knownSources
#print axioms withoutGlobalFacts
#print axioms nativeSource
end Mettapedia.Languages.Megalodon.SetOperationProofReconstruction
