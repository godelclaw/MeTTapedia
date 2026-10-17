import Mettapedia.Languages.HOLLight.ScopedSpecEmission
import Mettapedia.Languages.HOLLight.InferenceRuleExpansion

/-!
# Original authored-row descriptors for executed SPEC specialization

The descriptor is computed solely from an original RuleSchema and the fixed
number of earlier universal eliminations. It retains the original rule theorem
as fixed provenance, closes the remaining inner formals, and exposes the exact
typed authored body. Earlier operand values generate the changing incoming
universal theorem in the original elimination order.

The fixed descriptor's copier emits the original eighteen-node SPEC graph
from earlier/current raw and original named operand words and origin bytes.
Neither a changing theorem nor a predicate nor a precomputed block is a machine
input. The original instantiateMany/specBlock computations provide the reference
output and the original primitive replay remains the logical authority.

The descriptor length charges its complete fixed payload. This realizes one
fixed authored calculus; it is not a compiler for runtime calculus specifications.
Original row selection, source admission, and operand rendering remain separate.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.ScopedRuleSpecialization
open Mettapedia.Languages.OpenTheory
open PrimitiveTransport QuantifierExpansion
open Mettapedia.Logic
open TemplateInstantiationMachine.Indexed (sequence sequence_typed)

/-- The original uniform universal spine, in original outermost-first order. -/
def close (domain : Ty) : Nat → DBTerm → DBTerm
  | 0,authored => authored
  | count+1,authored => close domain count (DerivedRules.forallAppDB domain (.abs domain authored))

theorem sequence_forall (arguments : List CanonicalTerm) (depth : Nat) (domain : Ty) (predicate : DBTerm) :
    sequence arguments depth (DerivedRules.forallAppDB domain predicate) =
      DerivedRules.forallAppDB domain (sequence arguments depth predicate) := by
  induction arguments generalizing depth with
  | nil => rfl
  | cons argument rest ih => simp only [TemplateInstantiationMachine.Indexed.sequence,ih,DerivedRules.instantiateAt_forallAppDB]

def specialized (seed : Theorem) (domain : Ty) (arguments : List CanonicalTerm) (authored : DBTerm)
    (checked : authored.inferType (domain::arguments.map CanonicalTerm.ty) = some Ty.bool) : Theorem :=
  Theorem.preserveAxiomsResult seed seed.sequent.hyp
    ⟨DerivedRules.forallAppDB domain (.abs domain (sequence arguments 1 authored)),Ty.bool,
      DerivedRules.inferType_forallAppDB_iff.mpr
        ⟨DBTerm.inferType_abs_of (sequence_typed arguments [domain] authored Ty.bool checked),rfl⟩⟩

/-- Original specialization consumes the reversed earlier operands. The changing
incoming theorem is constructed without a theorem payload or semantic callback. -/
theorem specialize_reverse (arguments : List CanonicalTerm) (domain : Ty)
    (typed : ∀ argument ∈ arguments, argument.ty=domain) (authored : DBTerm)
    (checked : authored.inferType (domain::arguments.map CanonicalTerm.ty) = some Ty.bool)
    (seed : Theorem)
    (shape : seed.sequent.concl.term = close domain (arguments.length+1) authored) :
    instantiateMany? seed arguments.reverse = some (specialized seed domain arguments authored checked) := by
  induction arguments generalizing authored seed with
  | nil =>
      simp only [List.reverse_nil,instantiateMany?]
      congr 1
      apply Theorem.ext
      · rfl
      · apply Sequent.ext
        · rfl
        · apply CanonicalTerm.ext_term
          exact shape
  | cons argument rest ih =>
      have argumentType := typed argument (by simp)
      have restTypes : ∀ value ∈ rest, value.ty=domain := fun value member => typed value (by simp [member])
      let lifted := DerivedRules.forallAppDB domain (.abs domain authored)
      have liftedChecked : lifted.inferType (domain::rest.map CanonicalTerm.ty) = some Ty.bool := by
        apply DerivedRules.inferType_forallAppDB_iff.mpr
        refine ⟨DBTerm.inferType_abs_of ?_,rfl⟩
        simpa only [List.map_cons,argumentType] using checked
      have first : instantiateMany? seed rest.reverse = some (specialized seed domain rest lifted liftedChecked) :=
        ih restTypes lifted liftedChecked seed (by simpa only [List.length_cons,close] using shape)
      let intermediate := specialized seed domain rest lifted liftedChecked
      have nextShape : intermediate.sequent.concl.term =
          DerivedRules.forallAppDB domain (.abs domain (sequence rest 1 lifted)) := rfl
      have nextChecked : (sequence rest 1 lifted).inferType [domain] = some Ty.bool :=
        sequence_typed rest [domain] lifted Ty.bool liftedChecked
      have next := instantiate?_eq_some intermediate domain (sequence rest 1 lifted) nextChecked argument argumentType nextShape
      have same : specResult intermediate domain (sequence rest 1 lifted) nextChecked argument argumentType =
          specialized seed domain (argument::rest) authored checked := by
        apply Theorem.ext
        · rfl
        · apply Sequent.ext
          · rfl
          · apply CanonicalTerm.ext_term
            simp only [specResult,Theorem.preserveAxiomsResult,betaReduced,specialized,lifted,
              sequence_forall,TemplateInstantiationMachine.Indexed.sequence_abs,
              DerivedRules.instantiateAt_forallAppDB,DBTerm.instantiateAt,TemplateInstantiationMachine.Indexed.sequence,Nat.zero_add]
      dsimp only [intermediate] at next same
      rw [List.reverse_cons,instantiateMany?_append,first]
      simp only [Bind.bind,Option.bind_some,instantiateMany?,next,same]

/-- Rendering the original HOL closure computes this descriptor's exact spine. -/
theorem render_closeAll (count : Nat)
    (formula : HOL.Formula HOL.Embedding.InferenceRules.Symbol
      (HOL.Embedding.FirstOrder.CtxOfArity count)) :
    (InferenceHosting.render (HOL.closeAll (HOL.Embedding.FirstOrder.CtxOfArity count) formula)).term =
      close InferenceHosting.dataType count (InferenceRuleExpansion.renderOpen formula) := by
  induction count with
  | zero => exact ReverseTranslation.reverseTerm_eq_reverseTermOpen _
  | succ count ih =>
      simp only [List.replicate_succ,HOL.closeAll]
      rw [ih (.all formula),InferenceRuleExpansion.renderOpen_all]
      rfl


theorem close_add (domain : Ty) (first second : Nat) (authored : DBTerm) :
    close domain (first+second) authored = close domain first (close domain second authored) := by
  induction second generalizing authored with
  | zero => rfl
  | succ second ih =>
      simp only [close]
      exact ih _

/-- Closing a uniform spine removes exactly those authored binder types. -/
theorem close_type (domain : Ty) (count : Nat) (authored : DBTerm) (context : List Ty) :
    (close domain count authored).inferType context=some Ty.bool ↔
      authored.inferType (List.replicate count domain++context)=some Ty.bool := by
  induction count generalizing authored with
  | zero => rfl
  | succ count ih =>
      rw [close,ih]
      rw [DerivedRules.inferType_forallAppDB_iff]
      constructor
      · rintro ⟨predicateChecked,_⟩
        obtain ⟨codomain,bodyChecked,same⟩ := DBTerm.inferType_abs_eq_some_iff.mp predicateChecked
        obtain ⟨_,rfl⟩ := Ty.function_inj same
        simpa only [List.replicate_succ,List.cons_append] using bodyChecked
      · intro bodyChecked
        refine ⟨DBTerm.inferType_abs_of ?_,rfl⟩
        simpa only [List.replicate_succ,List.cons_append] using bodyChecked

open Mettapedia.OSLF.MeTTaIL.Syntax (RuleSchema)
open Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation (inferenceRule)

/-- No semantic field is supplied: the descriptor starts at the original row. -/
def rowBody (rule : RuleSchema) : DBTerm :=
  InferenceRuleExpansion.renderOpen (HOL.Embedding.InferenceRules.openRule (inferenceRule rule))
def rowArity (rule : RuleSchema) : Nat := (inferenceRule rule).vars.length

theorem row_shape (rule : RuleSchema) :
    (InferenceRuleExpansion.ruleTheorem rule).sequent.concl.term =
      close InferenceHosting.dataType (rowArity rule) (rowBody rule) :=
  render_closeAll _ _

/-- The fixed stage body closes only the remaining inner formals. Earlier
operands and the current operand have no part in the descriptor computation. -/
def stageBody (rule : RuleSchema) (prior : Nat) : DBTerm :=
  close InferenceHosting.dataType (rowArity rule-(prior+1)) (rowBody rule)

theorem stage_shape (rule : RuleSchema) (prior : Nat) (within : prior<rowArity rule) :
    (InferenceRuleExpansion.ruleTheorem rule).sequent.concl.term =
      close InferenceHosting.dataType (prior+1) (stageBody rule prior) := by
  rw [row_shape,stageBody,← close_add]
  congr 1
  omega

theorem stage_checked (rule : RuleSchema) (prior : Nat) (within : prior<rowArity rule) :
    (stageBody rule prior).inferType
      (InferenceHosting.dataType::List.replicate prior InferenceHosting.dataType)=some Ty.bool := by
  have checked : (InferenceRuleExpansion.ruleTheorem rule).sequent.concl.term.inferType []=some Ty.bool := by
    have original := (InferenceRuleExpansion.ruleTheorem rule).sequent.concl.checked
    change (InferenceRuleExpansion.ruleSequent rule).concl.term.inferType [] =
      some (InferenceRuleExpansion.ruleSequent rule).concl.ty at original
    rw [(InferenceRuleExpansion.ruleSequent_isBool rule).1] at original
    exact original
  rw [stage_shape rule prior within,close_type] at checked
  simpa only [List.append_nil,List.replicate_succ] using checked

/-- Every stage consumes the original earlier arguments in universal elimination order. -/
theorem original_stage (rule : RuleSchema) (prior : Nat) (within : prior<rowArity rule)
    (previous : Fin prior → CanonicalTerm) (typed : ∀ index, (previous index).ty=InferenceHosting.dataType) :
    instantiateMany? (InferenceRuleExpansion.ruleTheorem rule) (List.ofFn previous).reverse =
      some (specialized (InferenceRuleExpansion.ruleTheorem rule) InferenceHosting.dataType
        (List.ofFn previous) (stageBody rule prior) (by
          simpa only [ScopedBetaEmission.previous_types previous InferenceHosting.dataType typed] using
            stage_checked rule prior within)) := by
  apply specialize_reverse _ InferenceHosting.dataType _ _ _ _ _
  · intro value member
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
    exact typed index
  · simpa only [List.length_ofFn] using stage_shape rule prior within


/-- The machine's computed input equals the original row-stage theorem. -/
theorem original_input (rule : RuleSchema) (prior : Nat) (within : prior<rowArity rule)
    (previous : Fin prior → CanonicalTerm) (typed : ∀ index, (previous index).ty=InferenceHosting.dataType) :
    instantiateMany? (InferenceRuleExpansion.ruleTheorem rule) (List.ofFn previous).reverse =
      some (ScopedSpecEmission.input (InferenceRuleExpansion.ruleTheorem rule) prior InferenceHosting.dataType
        (stageBody rule prior) (stage_checked rule prior within) previous typed) := by
  rw [original_stage rule prior within previous typed]
  congr 1

open Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open ProofDataEncoding
open ProofExecution (Origin)

/-- Every fixed original row and stage computes its own eighteen-node descriptor. -/
def template (rule : RuleSchema) (prior : Nat) (within : prior<rowArity rule) : ScopedBetaEmission.Plan prior :=
  ScopedSpecEmission.template (InferenceRuleExpansion.ruleTheorem rule) prior InferenceHosting.dataType
    (stageBody rule prior) (stage_checked rule prior within)

/-- The independent reference computation uses original rule specialization and SPEC. -/
def originalBlock? (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema) (prior : Nat)
    (previous : Fin prior → CanonicalTerm) (argument : CanonicalTerm) (origin : Origin) :
    Option ProofSystem.Certificate := do
  let incoming ← instantiateMany? (InferenceRuleExpansion.ruleTheorem rule) (List.ofFn previous).reverse
  specBlock? policy incoming argument origin

theorem originalBlock_computed (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema)
    (prior : Nat) (within : prior<rowArity rule)
    (previous : Fin prior → CanonicalTerm) (typed : ∀ index, (previous index).ty=InferenceHosting.dataType)
    (argument : CanonicalTerm) (argumentType : argument.ty=InferenceHosting.dataType) (origin : Origin) :
    originalBlock? policy rule prior previous argument origin =
      specTypedBlock? policy
        (ScopedSpecEmission.input (InferenceRuleExpansion.ruleTheorem rule) prior InferenceHosting.dataType
          (stageBody rule prior) (stage_checked rule prior within) previous typed)
        InferenceHosting.dataType (ScopedBetaEmission.body previous (stageBody rule prior))
        (ScopedBetaEmission.checkedBody prior InferenceHosting.dataType Ty.bool (stageBody rule prior)
          (stage_checked rule prior within) previous typed) argument argumentType
        (ScopedSpecEmission.input_shape (InferenceRuleExpansion.ruleTheorem rule) prior InferenceHosting.dataType
          (stageBody rule prior) (stage_checked rule prior within) previous typed) origin := by
  unfold originalBlock?
  rw [original_input rule prior within previous typed]
  simp only [Bind.bind,Option.bind_some]
  unfold specBlock?
  rw [universalBody?_complete _ InferenceHosting.dataType
    (ScopedBetaEmission.body previous (stageBody rule prior))
    (ScopedBetaEmission.checkedBody prior InferenceHosting.dataType Ty.bool (stageBody rule prior)
      (stage_checked rule prior within) previous typed)
    (ScopedSpecEmission.input_shape (InferenceRuleExpansion.ruleTheorem rule) prior InferenceHosting.dataType
      (stageBody rule prior) (stage_checked rule prior within) previous typed)]
  have sameType := (Ty.same_eq_true_iff InferenceHosting.dataType argument.ty).mpr argumentType.symm
  simp only [Bind.bind,Option.bind_some]
  rw [dif_pos sameType]

theorem originalBlock_isSome (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema)
    (prior : Nat) (within : prior<rowArity rule)
    (previous : Fin prior → CanonicalTerm) (typed : ∀ index, (previous index).ty=InferenceHosting.dataType)
    (argument : CanonicalTerm) (argumentType : argument.ty=InferenceHosting.dataType) (origin : Origin) :
    (originalBlock? policy rule prior previous argument origin).isSome = true := by
  rw [originalBlock_computed policy rule prior within previous typed argument argumentType origin]
  exact QuantifierEmission.built_isSome _ _ _ _ _ _ _ _ _

def built (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema)
    (prior : Nat) (within : prior<rowArity rule)
    (previous : Fin prior → CanonicalTerm) (typed : ∀ index, (previous index).ty=InferenceHosting.dataType)
    (argument : CanonicalTerm) (argumentType : argument.ty=InferenceHosting.dataType) (origin : Origin) :
    ProofSystem.Certificate :=
  (originalBlock? policy rule prior previous argument origin).get
    (originalBlock_isSome policy rule prior within previous typed argument argumentType origin)

theorem built_computed (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema)
    (prior : Nat) (within : prior<rowArity rule)
    (previous : Fin prior → CanonicalTerm) (typed : ∀ index, (previous index).ty=InferenceHosting.dataType)
    (argument : CanonicalTerm) (argumentType : argument.ty=InferenceHosting.dataType) (origin : Origin) :
    originalBlock? policy rule prior previous argument origin =
      some (built policy rule prior within previous typed argument argumentType origin) :=
  (Option.some_get _).symm

/-- Original rule bytes and earlier/current operand bytes determine all output
fields; no incoming theorem, predicate, or precomputed block is an input. -/
theorem emitted_original (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema)
    (prior : Nat) (within : prior<rowArity rule)
    (previous : Fin prior → CanonicalTerm) (typed : ∀ index, (previous index).ty=InferenceHosting.dataType)
    (argument : CanonicalTerm) (argumentType : argument.ty=InferenceHosting.dataType) (origin : Origin)
    (empty : ∀ index, freeNames (previous index).term = [])
    (independent : ∀ index binders, named? (previous index).term binders = some (checkedSource (previous index)).source) :
    Indexed.instantiate (template rule prior within) (ScopedBetaEmission.fields previous argument origin) =
      encodeCertificate (built policy rule prior within previous typed argument argumentType origin) := by
  apply ScopedSpecEmission.emitted_exact policy _ _ _ _ previous typed argument argumentType origin empty independent
  rw [← originalBlock_computed policy rule prior within previous typed argument argumentType origin]
  exact built_computed policy rule prior within previous typed argument argumentType origin

def outputs (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema)
    (prior : Nat) (within : prior<rowArity rule)
    (previous : Fin prior → CanonicalTerm) (typed : ∀ index, (previous index).ty=InferenceHosting.dataType)
    (argument : CanonicalTerm) (argumentType : argument.ty=InferenceHosting.dataType) (origin : Origin)
    (empty : ∀ index, freeNames (previous index).term = [])
    (independent : ∀ index binders, named? (previous index).term binders = some (checkedSource (previous index)).source) :
    Turing.TM2OutputsInTime (Indexed.machine (template rule prior within))
      (Indexed.argumentWire (ScopedBetaEmission.fields previous argument origin))
      (some (encodeCertificate (built policy rule prior within previous typed argument argumentType origin)))
      (4*((template rule prior within).length+1)*
        ((Indexed.argumentWire (ScopedBetaEmission.fields previous argument origin)).length+1)) := by
  rw [← emitted_original policy rule prior within previous typed argument argumentType origin empty independent]
  exact Indexed.outputs _ _

/-- The target root is exactly the next original source specialization. -/
theorem original_chain_result (rule : RuleSchema) (prior : Nat) (within : prior<rowArity rule)
    (previous : Fin prior → CanonicalTerm) (typed : ∀ index, (previous index).ty=InferenceHosting.dataType)
    (argument : CanonicalTerm) (argumentType : argument.ty=InferenceHosting.dataType) :
    instantiateMany? (InferenceRuleExpansion.ruleTheorem rule) ((List.ofFn previous).reverse++[argument]) =
      some (specResult
        (ScopedSpecEmission.input (InferenceRuleExpansion.ruleTheorem rule) prior InferenceHosting.dataType
          (stageBody rule prior) (stage_checked rule prior within) previous typed)
        InferenceHosting.dataType (ScopedBetaEmission.body previous (stageBody rule prior))
        (ScopedBetaEmission.checkedBody prior InferenceHosting.dataType Ty.bool (stageBody rule prior)
          (stage_checked rule prior within) previous typed) argument argumentType) := by
  rw [instantiateMany?_append,original_input rule prior within previous typed]
  simp only [Bind.bind,Option.bind_some,instantiateMany?]
  rw [instantiate?_eq_some _ InferenceHosting.dataType
    (ScopedBetaEmission.body previous (stageBody rule prior))
    (ScopedBetaEmission.checkedBody prior InferenceHosting.dataType Ty.bool (stageBody rule prior)
      (stage_checked rule prior within) previous typed) argument argumentType
    (ScopedSpecEmission.input_shape (InferenceRuleExpansion.ruleTheorem rule) prior InferenceHosting.dataType
      (stageBody rule prior) (stage_checked rule prior within) previous typed)]
  rfl

/-- The decoded generated block earns its logical authority through the original
primitive replay, with the original next specialized theorem as its root. -/
theorem built_checked (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema)
    (prior : Nat) (within : prior<rowArity rule)
    (previous : Fin prior → CanonicalTerm) (typed : ∀ index, (previous index).ty=InferenceHosting.dataType)
    (argument : CanonicalTerm) (argumentType : argument.ty=InferenceHosting.dataType) (origin : Origin)
    (empty : ∀ index, freeNames (previous index).term = [])
    (independent : ∀ index binders, named? (previous index).term binders = some (checkedSource (previous index)).source) :
    GraphExpansion.BlockChecked policy
      [ScopedSpecEmission.input (InferenceRuleExpansion.ruleTheorem rule) prior InferenceHosting.dataType
        (stageBody rule prior) (stage_checked rule prior within) previous typed]
      (specResult
        (ScopedSpecEmission.input (InferenceRuleExpansion.ruleTheorem rule) prior InferenceHosting.dataType
          (stageBody rule prior) (stage_checked rule prior within) previous typed)
        InferenceHosting.dataType (ScopedBetaEmission.body previous (stageBody rule prior))
        (ScopedBetaEmission.checkedBody prior InferenceHosting.dataType Ty.bool (stageBody rule prior)
          (stage_checked rule prior within) previous typed) argument argumentType)
      (built policy rule prior within previous typed argument argumentType origin) ∧
      (built policy rule prior within previous typed argument argumentType origin).1.length=18 ∧
      (built policy rule prior within previous typed argument argumentType origin).1.map (fun node => node.origin)=
        List.replicate 18 origin := by
  obtain ⟨block,decoded,valid,count,origins⟩ := ScopedSpecEmission.decodes_checked policy
    (InferenceRuleExpansion.ruleTheorem rule) InferenceHosting.dataType (stageBody rule prior)
    (stage_checked rule prior within) previous typed argument argumentType origin empty independent
  change decodeCertificate (Indexed.instantiate (template rule prior within)
    (ScopedBetaEmission.fields previous argument origin)) = some block at decoded
  rw [emitted_original policy rule prior within previous typed argument argumentType origin empty independent,
    decodeCertificate_encodeCertificate] at decoded
  cases Option.some.inj decoded
  exact ⟨valid,count,origins⟩

end Mettapedia.Languages.HOLLight.ScopedRuleSpecialization
