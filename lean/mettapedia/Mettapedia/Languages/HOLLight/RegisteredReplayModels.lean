import Mettapedia.Languages.HOLLight.InferenceInterpretation
import Mettapedia.Languages.HOLLight.UniversalDefinitionModels
import Mettapedia.Languages.HOLLight.ProofExecution

/-!
# Constructed models for registered HOL declaration replay

Proof, constant-definition and carrier-changing type-definition commands
transform a semantic frame at the same declaration context and theorem cache.
The type existence licence is derived from the actual cached theorem's earlier
proof. Each declaration constructs its interpretation and universal schemas,
proves the old licensed schemas remain true, and earns the new background.

Finite replay and registered reachability preserve these constructions. The
empty-policy corollary builds its initial frame from the primitive declaration
context itself, yielding a full-domain model of the actual received cache under
its sequent hypotheses. Other policies require an actually interpreted initial
frame licensing their axioms; no such profile interpretation is inferred from
replay acceptance or from the source axiom list. Native implementation refinement
and identification with a particular relational model remain separate.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.RegisteredReplayModels
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open DefinitionAdapters SignatureFormation TypeFamilySemantics
open ModelInterpretation ModelInstanceCoherence DefinitionModelFamily
open UniversalDefinitionHistory DefinitionSchemaClosure DefinitionSchemaInstances DefinitionSchemaSubstitution
open DefinitionHistorySchemas DefinitionSchemaInstances SourceTypeDefinitionTransport UniformTypeDefinitionModels

universe w

structure Frame (initial : TheoryContext) (policy : AxiomPolicy)
    (context : TheoryContext) (cache : Array Theorem) : Type (w+2) where
  schemas : List (HOL.ClosedFormula Symbol)
  ordinary : ∀ formula ∈ schemas, OrdinarySymbols formula
  licensed : ∀ formula ∈ schemas, LicensedSchema context.signature formula
  family : Family.{w} initial context (schemaBackground schemas)
  authorized : ∀ sequent, policy sequent → TranslatedProvable (schemaBackground schemas) sequent
  cacheProvable : ∀ fact ∈ cache, TranslatedProvable (schemaBackground schemas) fact.sequent
  valid : ∀ fact ∈ cache, TheoryDerives policy context fact

private theorem translated_mono {first second : HOL.ClosedTheorySet Symbol}
    (included : first ⊆ second) {sequent : Sequent} (proof : TranslatedProvable first sequent) :
    TranslatedProvable second sequent := by
  obtain ⟨formula,translated,proven⟩ := proof
  exact ⟨formula,translated,HOL.ClosedTheorySet.provable_mono
    (fun member => member.elim (fun member => Or.inl (included member)) Or.inr) proven⟩

private theorem background_prefix (first second : List (HOL.ClosedFormula Symbol)) :
    schemaBackground first ⊆ schemaBackground (first++second) := by
  rintro formula ⟨schema,member,image⟩
  exact ⟨schema,List.mem_append_left _ member,image⟩

namespace Frame
variable {initial context : TheoryContext} {policy : AxiomPolicy} {cache : Array Theorem}

theorem background_closed (frame : Frame.{w} initial policy context cache) :
    VariableFreeSubstitutionClosed (schemaBackground frame.schemas) where
  variableFree := by
    rintro formula ⟨schema,member,image⟩ sourceVar
    exact (image.ordinary (frame.ordinary schema member)).variableFree sourceVar
  substitutionClosed := by
    rintro substitution formula ⟨schema,member,image⟩
    rw [targetMap_eq_typeMap (image.ordinary (frame.ordinary schema member))]
    exact ⟨schema,member,TypeImageOrbit.image substitution.raw.types image⟩

noncomputable def emptyWithFamily (initialFamily : Family.{w} initial initial ∅)
    (licensed : ∀ sequent, policy sequent → TranslatedProvable ∅ sequent) :
    Frame.{w} initial policy initial #[] where
  schemas := []
  ordinary := by simp
  licensed := by simp
  family := initialFamily.retheorize (schemaBackground []) (by
    rintro other assignment formula ⟨schema,member,image⟩
    simp at member)
  authorized := by
    intro sequent authorized
    apply translated_mono (first := ∅) (Set.empty_subset _)
    exact licensed sequent authorized
  cacheProvable := by simp
  valid := by simp

noncomputable def empty (primitives : Primitives initial)
    (licensed : ∀ sequent, policy sequent → TranslatedProvable ∅ sequent) :
    Frame.{w} initial policy initial #[] :=
  emptyWithFamily (Family.nil primitives) licensed

/-- Interpreted, formed source schemas may enlarge the background and the
selected axiom policy. The model is retained; truth of the added schemas and
syntactic authorization of the new policy are separate obligations. -/
noncomputable def adjoinSchemas (primitives : Primitives initial)
    (frame : Frame.{w} initial policy context cache)
    (added : List (HOL.ClosedFormula Symbol))
    (ordinary : ∀ formula ∈ added, OrdinarySymbols formula)
    (licensed : ∀ formula ∈ added, LicensedSchema context.signature formula)
    (holds : ∀ other assignment formula, formula ∈ added →
      (frame.family.model other assignment).models formula)
    (nextPolicy : AxiomPolicy) (included : ∀ sequent, policy sequent → nextPolicy sequent)
    (authorized : ∀ sequent, nextPolicy sequent →
      TranslatedProvable (schemaBackground (frame.schemas ++ added)) sequent) :
    Frame.{w} initial nextPolicy context cache := by
  have allLicensed : ∀ formula ∈ frame.schemas ++ added, LicensedSchema context.signature formula := by
    intro formula member
    exact (List.mem_append.mp member).elim (frame.licensed formula) (licensed formula)
  have allTruth : ∀ other assignment formula, formula ∈ frame.schemas ++ added →
      (frame.family.model other assignment).models formula := by
    intro other assignment formula member
    rcases List.mem_append.mp member with earlier | later
    · exact frame.family.equations other assignment formula ⟨formula, earlier, TypeImageOrbit.original⟩
    · exact holds other assignment formula later
  refine {
    schemas := frame.schemas ++ added
    ordinary := ?_
    licensed := allLicensed
    family := frame.family.retheorize _ ?_
    authorized := authorized
    cacheProvable := fun fact member => translated_mono (background_prefix _ _) (frame.cacheProvable fact member)
    valid := fun fact member => (frame.valid fact member).mono_policy included }
  · intro formula member
    exact (List.mem_append.mp member).elim (frame.ordinary formula) (ordinary formula)
  · exact UniversalDefinitionModels.background_models_of_schemas frame.family primitives _ allLicensed allTruth

def transfer {other : TheoryContext} {next : Array Theorem}
    (frame : Frame.{w} initial policy context cache) (sameContext : context = other) (sameCache : cache = next) :
    Frame.{w} initial policy other next := sameContext ▸ sameCache ▸ frame

theorem transfer_model {otherContext : TheoryContext} {nextCache : Array Theorem}
    (frame : Frame.{w} initial policy context cache) (sameContext : context = otherContext)
    (sameCache : cache = nextCache) (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (frame.transfer sameContext sameCache).family.model other assignment =
      frame.family.model other assignment := by
  cases sameContext
  cases sameCache
  rfl

theorem existence_provable (frame : Frame.{w} initial policy context cache)
    {instances : InstanceWitnesses} {request : TypeOperatorDefinitionRequest} {result : SourceTypeDefinitionResult}
    (accepted : admitSourceTypeInTheory context instances request = some result)
    (known : request.existence ∈ cache) :
    HOL.ClosedTheorySet.Provable (schemaBackground frame.schemas) (TypeAdmission.admittedImage accepted).formula := by
  obtain ⟨formula,translated,proven⟩ := (translatedProvable_iff_compositionallyProvable _ _).mp
    (frame.cacheProvable _ known)
  have same := eq_of_heq (translated.unique (TypeAdmission.admittedImage accepted).conclusionTranslated).2
  subst formula
  apply HOL.ClosedTheorySet.provable_mono _ proven
  rintro sentence (backgroundMember | hypotheses)
  · exact backgroundMember
  · obtain ⟨term,member,_⟩ := hypotheses
    rw [(UniformTypeDefinitionFamily.admitted_parameter_guards accepted).2.2] at member
    exact absurd member (Finset.notMem_empty _)

private theorem proof_output {context : TheoryContext} {policy : AxiomPolicy} [DecidablePred policy]
    {cache : Array Theorem} {node : ProofExecution.Receipt} {instances : InstanceWitnesses}
    {output : ProofExecution.Registered.Output}
    (accepted : (ProofExecution.Registered.Command.proof node instances).check policy context cache = some output) :
    output.context = context ∧ output.theorems = [node.conclusion] := by
  simp only [ProofExecution.Registered.Command.check] at accepted
  cases replayed : node.replay (ruleWitness policy) cache with
  | none => simp [replayed] at accepted
  | some next =>
    rw [replayed] at accepted
    change (if ProofExecution.Registered.requestFormedB context.signature instances node.witness = true ∧
        theoremFormedB context.signature instances node.conclusion = true then
        some (⟨context,[node.conclusion]⟩ : ProofExecution.Registered.Output) else none) = some output at accepted
    split at accepted
    · cases Option.some.inj accepted
      exact ⟨rfl,rfl⟩
    · contradiction

private theorem proof_conclusion_translated {initial context : TheoryContext} {policy : AxiomPolicy}
    [DecidablePred policy] {cache : Array Theorem}
    (frame : RegisteredReplayModels.Frame.{w} initial policy context cache)
    (node : ProofExecution.Receipt) (instances : InstanceWitnesses) (output : ProofExecution.Registered.Output)
    (accepted : (ProofExecution.Registered.Command.proof node instances).check policy context cache = some output) :
    TranslatedProvable (schemaBackground frame.schemas) node.conclusion.sequent := by
  have valid := ProofExecution.Registered.Command.check_sound policy context cache frame.valid accepted
  have derived : TheoryDerives policy context node.conclusion := by
    rw [← (proof_output accepted).1]
    apply valid.2
    rw [(proof_output accepted).2]
    simp
  cases replayed : node.replay (ruleWitness policy) cache with
  | none => simp [ProofExecution.Registered.Command.check,replayed] at accepted
  | some next =>
    obtain ⟨premises,found,checked,_⟩ :=
      (node.replay_eq_some_iff (ruleWitness policy) cache next).mp replayed
    have sourceCheck : node.witness.isInstance policy premises node.conclusion = true := checked
    obtain ⟨samePremises,sourceStep⟩ :=
      (RuleRequest.isInstance_eq_true_iff policy _ _ _).mp sourceCheck
    cases source : node.witness with
    | inference request =>
      rw [source] at sourceStep samePremises
      apply InferenceInterpretation.inference frame.background_closed sourceStep
      · intro input member
        apply frame.cacheProvable input
        exact DerivationGraph.lookupPremises_mem cache found input (samePremises ▸ member)
      · intro tagged member
        exact frame.authorized tagged (derived.authorizedAxioms tagged member)
    | «axiom» sequent =>
      rw [source] at sourceStep
      rw [Sequent.ext sourceStep.2.2.2.2.1 sourceStep.2.2.2.2.2]
      exact frame.authorized sequent sourceStep.2.1

noncomputable def proof {initial context : TheoryContext} {policy : AxiomPolicy}
    [DecidablePred policy] {cache : Array Theorem}
    (frame : RegisteredReplayModels.Frame.{w} initial policy context cache)
    (node : ProofExecution.Receipt) (instances : InstanceWitnesses) (output : ProofExecution.Registered.Output)
    (accepted : (ProofExecution.Registered.Command.proof node instances).check policy context cache = some output) :
    Frame.{w} initial policy output.context (cache ++ output.theorems.toArray) where
  schemas := frame.schemas
  ordinary := frame.ordinary
  licensed := by rw [(proof_output accepted).1]; exact frame.licensed
  family := {
    includes := by rw [(proof_output accepted).1]; exact frame.family.includes
    operators := frame.family.operators
    model := frame.family.model
    carrier := frame.family.carrier
    fullDomains := frame.family.fullDomains
    localSymbols := frame.family.localSymbols
    equations := frame.family.equations
    freshOperators := by rw [(proof_output accepted).1]; exact frame.family.freshOperators
    freshModels := by rw [(proof_output accepted).1]; exact frame.family.freshModels
    instances := by rw [(proof_output accepted).1]; exact frame.family.instances }
  authorized := frame.authorized
  cacheProvable := by
    intro fact member
    rw [(proof_output accepted).2] at member
    have present : fact ∈ cache ∨ fact = node.conclusion := by simpa using member
    rcases present with old | rfl
    · exact frame.cacheProvable _ old
    · exact proof_conclusion_translated frame node instances output accepted
  valid := by
    have valid := ProofExecution.Registered.Command.check_sound policy context cache frame.valid accepted
    intro fact member
    rw [(proof_output accepted).2] at member
    have present : fact ∈ cache ∨ fact = node.conclusion := by simpa using member
    rcases present with old | rfl
    · rw [(proof_output accepted).1]
      exact frame.valid _ old
    · exact valid.2 _ (by rw [(proof_output accepted).2]; simp)

theorem proof_model {initial context : TheoryContext} {policy : AxiomPolicy} [DecidablePred policy]
    {cache : Array Theorem} (frame : RegisteredReplayModels.Frame.{w} initial policy context cache)
    (node : ProofExecution.Receipt) (instances : InstanceWitnesses) (output : ProofExecution.Registered.Output)
    (accepted : (ProofExecution.Registered.Command.proof node instances).check policy context cache = some output)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ((proof frame node instances output accepted).family.model other assignment) =
      frame.family.model other assignment := rfl


private theorem constant_result [DecidablePred policy]
    {origin : ProofExecution.Origin} {name : Name} {source : SourceTerm} {instances : InstanceWitnesses}
    {output : ProofExecution.Registered.Output}
    (accepted : (ProofExecution.Registered.Command.constant origin name source instances).check policy context cache = some output) :
    ∃ result, admitConstantInTheory context instances name source = some result ∧
      TheoremFormed result.context.signature result.output.definitionTheorem ∧
      output = ⟨result.context,[result.output.definitionTheorem]⟩ := by
  simp only [ProofExecution.Registered.Command.check] at accepted
  cases admitted : admitConstantInTheory context instances name source with
  | none => simp [admitted] at accepted
  | some result =>
    rw [admitted] at accepted
    change (if theoremFormedB result.context.signature instances result.output.definitionTheorem then
      some (⟨result.context,[result.output.definitionTheorem]⟩ : ProofExecution.Registered.Output)
      else none) = some output at accepted
    split at accepted
    · rename_i formed
      exact ⟨result,rfl,theoremFormedB_sound _ _ formed,(Option.some.inj accepted).symm⟩
    · contradiction

/-- Construct the exact constant-admission frame from its checked source and
formed defining equation. The new native derivation is earned here. -/
noncomputable def constantAdmitted
    (primitives : Primitives initial) (frame : Frame.{w} initial policy context cache)
    (instances : InstanceWitnesses) (name : Name) (source : SourceTerm)
    (result : ContextConstantDefinitionResult)
    (admitted : admitConstantInTheory context instances name source = some result)
    (formed : TheoremFormed result.context.signature result.output.definitionTheorem) :
    Frame.{w} initial policy result.context (cache ++ [result.output.definitionTheorem].toArray) := by
  let schemas := frame.schemas ++ [constantSchema result]
  let core := Family.constantCore primitives frame.family instances name source result admitted
  have included := (admitConstantInTheory_result admitted).2.2.1
  have functionRegistered := frame.family.includes.1 _ _ primitives.functionArity
  have equalityRegistered := frame.family.includes.2 _ _ primitives.equalityRegistered
  have licensed : ∀ formula ∈ schemas, LicensedSchema result.context.signature formula := by
    intro formula member
    rcases List.mem_append.mp member with old | added
    · exact (frame.licensed _ old).mono included
    · obtain rfl := List.mem_singleton.mp added
      exact constantSchema_licensed admitted functionRegistered primitives.equalityParameter equalityRegistered
  have ordinary : ∀ formula ∈ schemas, OrdinarySymbols formula := by
    intro formula member
    rcases List.mem_append.mp member with old | added
    · exact frame.ordinary _ old
    · obtain rfl := List.mem_singleton.mp added
      exact constantSchema_ordinary admitted primitives.equalityParameter equalityRegistered
  have base : ∀ other assignment formula, formula ∈ schemas →
      (core.model other assignment).models formula := by
    intro other assignment formula member
    rcases List.mem_append.mp member with old | added
    · apply (LicensedSchema.models_agreement
        (constant_old_agreement admitted (frame.family.model other assignment))
        functionRegistered (core.fullDomains other assignment) (frame.family.fullDomains other assignment)
        (frame.licensed formula old)).mpr
      exact frame.family.equations other assignment formula ⟨formula,old,TypeImageOrbit.original⟩
    · obtain rfl := List.mem_singleton.mp added
      exact ConstantAdmission.sourceExtension_models_source_equation admitted _ TypeSubst.empty
        ((constantSchema_translated admitted).of_term_eq (TermSubst.typeInstance_identity _).symm)
  let family := core.retheorize (schemaBackground schemas)
    (UniversalDefinitionModels.background_models_of_schemas core primitives schemas licensed base)
  have newProof : TranslatedProvable (schemaBackground schemas) result.output.definitionTheorem.sequent := by
    apply (translatedProvable_iff_compositionallyProvable _ _).mpr
    refine ⟨constantSchema result,constantSchema_translated admitted,?_⟩
    exact HOL.ClosedTheorySet.provable_of_mem
      (Or.inl ⟨_,List.mem_append_right _ List.mem_cons_self,TypeImageOrbit.original⟩)
  refine {
    schemas := schemas
    ordinary := ordinary
    licensed := licensed
    family := family
    authorized := ?_
    cacheProvable := ?_
    valid := ?_}
  · intro sequent authorized
    exact translated_mono (background_prefix _ _) (frame.authorized sequent authorized)
  · intro fact member
    have present : fact ∈ cache ∨ fact = result.output.definitionTheorem := by simpa using member
    rcases present with old | rfl
    · exact translated_mono (background_prefix _ _) (frame.cacheProvable _ old)
    · exact newProof
  · intro fact member
    have present : fact ∈ cache ∨ fact = result.output.definitionTheorem := by simpa using member
    rcases present with old | rfl
    · exact .weaken included (frame.valid _ old)
    · exact .constantDefinition admitted formed

noncomputable def constant [DecidablePred policy]
    (primitives : Primitives initial) (frame : Frame.{w} initial policy context cache)
    (origin : ProofExecution.Origin) (name : Name) (source : SourceTerm) (instances : InstanceWitnesses)
    (output : ProofExecution.Registered.Output)
    (accepted : (ProofExecution.Registered.Command.constant origin name source instances).check policy context cache = some output) :
    Frame.{w} initial policy output.context (cache ++ output.theorems.toArray) :=
  let result := (constant_result accepted).choose
  let facts := (constant_result accepted).choose_spec
  (constantAdmitted primitives frame instances name source result facts.1 facts.2.1).transfer
    (by rw [facts.2.2]) (by rw [facts.2.2])

private theorem type_definition_result [DecidablePred policy]
    {origin : ProofExecution.Origin} {request : TypeOperatorDefinitionRequest}
    {index : Nat} {instances : InstanceWitnesses} {output : ProofExecution.Registered.Output}
    (accepted : (ProofExecution.Registered.Command.typeDefinition origin request index instances).check policy context cache = some output) :
    ∃ result, admitSourceTypeInTheory context instances request = some result ∧ request.existence ∈ cache ∧
      (TheoremFormed result.context.signature result.output.abstractionRepresentationTheorem ∧
        TheoremFormed result.context.signature result.output.representationAbstractionTheorem) ∧
      output = ⟨result.context,[result.output.abstractionRepresentationTheorem,
        result.output.representationAbstractionTheorem]⟩ := by
  simp only [ProofExecution.Registered.Command.check] at accepted
  cases found : cache[index]? with
  | none => simp [found] at accepted
  | some existence =>
    rw [found] at accepted
    change (if existence.structuralSame request.existence then do
      let result ← admitSourceTypeInTheory context instances request
      if theoremFormedB result.context.signature instances result.output.abstractionRepresentationTheorem = true ∧
          theoremFormedB result.context.signature instances result.output.representationAbstractionTheorem = true then
        some (⟨result.context,[result.output.abstractionRepresentationTheorem,
          result.output.representationAbstractionTheorem]⟩ : ProofExecution.Registered.Output)
      else none
    else none) = some output at accepted
    split at accepted
    · rename_i matched
      have same := (Theorem.structuralSame_eq_true_iff _ _).mp matched
      cases admitted : admitSourceTypeInTheory context instances request with
      | none => simp [admitted] at accepted
      | some result =>
        rw [admitted] at accepted
        change (if theoremFormedB result.context.signature instances result.output.abstractionRepresentationTheorem = true ∧
            theoremFormedB result.context.signature instances result.output.representationAbstractionTheorem = true then
          some (⟨result.context,[result.output.abstractionRepresentationTheorem,
            result.output.representationAbstractionTheorem]⟩ : ProofExecution.Registered.Output)
          else none) = some output at accepted
        split at accepted
        · rename_i formed
          exact ⟨result,rfl,same ▸ Array.mem_of_getElem? found,
            ⟨theoremFormedB_sound _ _ formed.1,theoremFormedB_sound _ _ formed.2⟩,(Option.some.inj accepted).symm⟩
        · contradiction
    · contradiction

/-- Construct a type-admission frame from the actual cached existence proof
and formed equations. Its family is the witnessed subtype construction. -/
noncomputable def typeAdmitted
    (primitives : Primitives initial) (frame : Frame.{w} initial policy context cache)
    (instances : InstanceWitnesses) (request : TypeOperatorDefinitionRequest) (result : SourceTypeDefinitionResult)
    (admitted : admitSourceTypeInTheory context instances request = some result)
    (known : request.existence ∈ cache)
    (formed : TheoremFormed result.context.signature result.output.abstractionRepresentationTheorem ∧
      TheoremFormed result.context.signature result.output.representationAbstractionTheorem) :
    Frame.{w} initial policy result.context
      (cache ++ [result.output.abstractionRepresentationTheorem,result.output.representationAbstractionTheorem].toArray) := by
  have proof := frame.existence_provable admitted known
  let additions := [abstractionRepresentationSchema (request := request) (result := result) TypeSubst.empty,
    representationAbstractionSchema admitted TypeSubst.empty]
  let schemas := frame.schemas ++ additions
  let core := Family.typeDefinitionCore primitives frame.family instances request result admitted proof
  have included := (admitSourceTypeInTheory_result admitted).1
  have functionRegistered := frame.family.includes.1 _ _ primitives.functionArity
  have equalityRegistered := frame.family.includes.2 _ _ primitives.equalityRegistered
  have licensed : ∀ formula ∈ schemas, LicensedSchema result.context.signature formula := by
    intro formula member
    rcases List.mem_append.mp member with old | added
    · exact (frame.licensed _ old).mono included
    · rcases List.mem_cons.mp added with rfl | added
      · exact abstractionSchema_licensed admitted functionRegistered primitives.equalityParameter equalityRegistered
      · obtain rfl := List.mem_singleton.mp added
        exact representationSchema_licensed admitted functionRegistered primitives.equalityParameter equalityRegistered
  have ordinary : ∀ formula ∈ schemas, OrdinarySymbols formula := by
    intro formula member
    rcases List.mem_append.mp member with old | added
    · exact frame.ordinary _ old
    · rcases List.mem_cons.mp added with rfl | added
      · exact ordinary_abstractionSchema admitted
      · obtain rfl := List.mem_singleton.mp added
        exact ordinary_representationSchema admitted primitives.equalityParameter equalityRegistered
  have base : ∀ other assignment formula, formula ∈ schemas →
      (core.model other assignment).models formula := by
    intro other assignment formula member
    rcases List.mem_append.mp member with old | added
    · apply (LicensedSchema.models_agreement
        (TypeDefinitionModels.model_old_agreement frame.family admitted proof other assignment)
        functionRegistered (core.fullDomains other assignment) (frame.family.fullDomains other assignment)
        (frame.licensed formula old)).mpr
      exact frame.family.equations other assignment formula ⟨formula,old,TypeImageOrbit.original⟩
    · rcases List.mem_cons.mp added with rfl | added
      · exact family_models_abstractionRepresentation frame.family admitted proof other assignment TypeSubst.empty
      · obtain rfl := List.mem_singleton.mp added
        apply family_models_representationAbstraction frame.family admitted proof other assignment primitives TypeSubst.empty
        have annotation := result.context.constantTypes _ _ (UniformTypeDefinitionInstances.new_constants_registered admitted).1
        simpa only [abstractionAnnotation,TypeSubst.apply_empty] using (annotation.function_components _).2
  let family := core.retheorize (schemaBackground schemas)
    (UniversalDefinitionModels.background_models_of_schemas core primitives schemas licensed base)
  have localSubset : typeDefinitionTheory admitted ⊆ schemaBackground schemas := by
    rintro formula (first | second)
    · exact ⟨_,List.mem_append_right _ List.mem_cons_self,first⟩
    · exact ⟨_,List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self),second⟩
  have firstProof : TranslatedProvable (schemaBackground schemas) result.output.abstractionRepresentationTheorem.sequent :=
    translated_mono localSubset (definition_rows_translated_provable admitted _ List.mem_cons_self)
  have secondProof : TranslatedProvable (schemaBackground schemas) result.output.representationAbstractionTheorem.sequent :=
    translated_mono localSubset (definition_rows_translated_provable admitted _ (List.mem_cons_of_mem _ List.mem_cons_self))
  refine {
    schemas := schemas
    ordinary := ordinary
    licensed := licensed
    family := family
    authorized := ?_
    cacheProvable := ?_
    valid := ?_}
  · intro sequent authorized
    exact translated_mono (background_prefix _ _) (frame.authorized sequent authorized)
  · intro fact member
    have present : fact ∈ cache ∨ fact = result.output.abstractionRepresentationTheorem ∨
        fact = result.output.representationAbstractionTheorem := by simpa using member
    rcases present with old | rfl | rfl
    · exact translated_mono (background_prefix _ _) (frame.cacheProvable _ old)
    · exact firstProof
    · exact secondProof
  · intro fact member
    have present : fact ∈ cache ∨ fact = result.output.abstractionRepresentationTheorem ∨
        fact = result.output.representationAbstractionTheorem := by simpa using member
    rcases present with old | rfl | rfl
    · exact .weaken included (frame.valid _ old)
    · exact .typeAbstractionDefinition admitted (frame.valid _ known) formed.1
    · exact .typeRepresentationDefinition admitted (frame.valid _ known) formed.2

noncomputable def typeDefinition [DecidablePred policy]
    (primitives : Primitives initial) (frame : Frame.{w} initial policy context cache)
    (origin : ProofExecution.Origin) (request : TypeOperatorDefinitionRequest)
    (index : Nat) (instances : InstanceWitnesses) (output : ProofExecution.Registered.Output)
    (accepted : (ProofExecution.Registered.Command.typeDefinition origin request index instances).check policy context cache = some output) :
    Frame.{w} initial policy output.context (cache ++ output.theorems.toArray) :=
  let result := (type_definition_result accepted).choose
  let facts := (type_definition_result accepted).choose_spec
  (typeAdmitted primitives frame instances request result facts.1 facts.2.1 facts.2.2.1).transfer
    (by rw [facts.2.2.2]) (by rw [facts.2.2.2])

noncomputable def command [DecidablePred policy]
    (primitives : Primitives initial) (frame : Frame.{w} initial policy context cache)
    (command : ProofExecution.Registered.Command) (output : ProofExecution.Registered.Output)
    (accepted : command.check policy context cache = some output) :
    Frame.{w} initial policy output.context (cache ++ output.theorems.toArray) := by
  cases command with
  | proof node instances => exact proof frame node instances output accepted
  | constant origin name source instances => exact constant primitives frame origin name source instances output accepted
  | typeDefinition origin request index instances => exact typeDefinition primitives frame origin request index instances output accepted

private theorem apply_result [DecidablePred policy]
    {before after : ProofExecution.Registered.State} {next : ProofExecution.Registered.Command}
    (accepted : ProofExecution.Registered.apply policy before next = some after) :
    ∃ output, next.check policy before.context before.cache = some output ∧
      after = ⟨output.context,before.cache ++ output.theorems.toArray,
        before.receipts.push ⟨next,output.theorems⟩⟩ := by
  cases checked : next.check policy before.context before.cache with
  | none => simp [ProofExecution.Registered.apply,checked] at accepted
  | some output =>
    exact ⟨output,rfl,Option.some.inj (by simpa [ProofExecution.Registered.apply,checked] using accepted.symm)⟩

noncomputable def apply [DecidablePred policy]
    (primitives : Primitives initial) (before after : ProofExecution.Registered.State)
    (frame : Frame.{w} initial policy before.context before.cache) (next : ProofExecution.Registered.Command)
    (accepted : ProofExecution.Registered.apply policy before next = some after) :
    Frame.{w} initial policy after.context after.cache :=
  let output := (apply_result accepted).choose
  let facts := (apply_result accepted).choose_spec
  (command primitives frame next output facts.1).transfer
    (by rw [facts.2]) (by rw [facts.2])

private theorem replay_cons_result [DecidablePred policy]
    {before after : ProofExecution.Registered.State} {head : ProofExecution.Registered.Command}
    {tail : List ProofExecution.Registered.Command}
    (accepted : ProofExecution.Registered.replayFrom policy before (head::tail) = some after) :
    ∃ middle, ProofExecution.Registered.apply policy before head = some middle ∧
      ProofExecution.Registered.replayFrom policy middle tail = some after := by
  cases applied : ProofExecution.Registered.apply policy before head with
  | none => simp [ProofExecution.Registered.replayFrom,applied] at accepted
  | some middle => exact ⟨middle,rfl,by simpa [ProofExecution.Registered.replayFrom,applied] using accepted⟩

noncomputable def replay [DecidablePred policy]
    (primitives : Primitives initial) (before after : ProofExecution.Registered.State)
    (frame : Frame.{w} initial policy before.context before.cache) (commands : List ProofExecution.Registered.Command)
    (accepted : ProofExecution.Registered.replayFrom policy before commands = some after) :
    Frame.{w} initial policy after.context after.cache :=
  match commands with
  | [] => frame.transfer
      (congrArg ProofExecution.Registered.State.context (Option.some.inj accepted))
      (congrArg ProofExecution.Registered.State.cache (Option.some.inj accepted))
  | head::tail =>
    let middle := (replay_cons_result accepted).choose
    let facts := (replay_cons_result accepted).choose_spec
    replay primitives middle after (apply primitives before middle frame head facts.1) tail facts.2
termination_by commands

noncomputable def model (frame : Frame.{w} initial policy context cache)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol := frame.family.model other assignment

theorem model_fullDomains (frame : Frame.{w} initial policy context cache)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (frame.model other assignment).FullDomains := frame.family.fullDomains other assignment

theorem cached_models (frame : Frame.{w} initial policy context cache)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    {fact : Theorem} (known : fact ∈ cache) :
    ∃ formula, Translates [] fact.sequent.concl.term .prop formula ∧
      ((∀ hypothesis ∈ translatedHypotheses fact.sequent.hyp, (frame.model other assignment).models hypothesis) →
        (frame.model other assignment).models formula) := by
  obtain ⟨formula,translated,proven⟩ := frame.cacheProvable fact known
  refine ⟨formula,translated,?_⟩
  intro hypotheses
  apply provable_models proven (frame.model other assignment)
    (HOL.HenkinModel.functionsRespectEqv_of_fullDomains _ (frame.model_fullDomains other assignment))
  rintro sentence (background | hypothesis)
  · exact frame.family.equations other assignment sentence background
  · exact hypotheses sentence hypothesis

theorem cached_models_of_translation (frame : Frame.{w} initial policy context cache)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    {fact : Theorem} (known : fact ∈ cache) {formula : HOL.ClosedFormula Symbol}
    (translated : Translates [] fact.sequent.concl.term .prop formula)
    (hypotheses : ∀ hypothesis ∈ translatedHypotheses fact.sequent.hyp, (frame.model other assignment).models hypothesis) :
    (frame.model other assignment).models formula := by
  obtain ⟨actual,translation,holds⟩ := frame.cached_models other assignment known
  cases translation.unique_eq translated
  exact holds hypotheses

/-- Cached admitted definition equations determine all their actual source
type images in the constructed model. Formation comes from the cached proof. -/
theorem cached_constant_schema (frame : RegisteredReplayModels.Frame.{w} initial policy context cache)
    {before : TheoryContext} {instances : InstanceWitnesses} {name : Name}
    {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory before instances name source = some result)
    (known : result.output.definitionTheorem ∈ cache)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    (frame.model other assignment).models (constantSchema result) := by
  obtain ⟨formula, translated, proven⟩ :=
    (translatedProvable_iff_compositionallyProvable _ _).mp (frame.cacheProvable _ known)
  cases translated.unique_eq (constantSchema_translated accepted)
  apply provable_models proven (frame.model other assignment)
    (HOL.HenkinModel.functionsRespectEqv_of_fullDomains _ (frame.model_fullDomains other assignment))
  rintro sentence (background | hypothesis)
  · exact frame.family.equations other assignment sentence background
  · obtain ⟨term, member, _⟩ := hypothesis
    obtain ⟨_, _, _, _, _, _, _, empty⟩ := admitConstantInTheory_result accepted
    rw [empty] at member
    exact absurd member (Finset.notMem_empty _)

theorem cached_constant_schema_instance
    (frame : RegisteredReplayModels.Frame.{w} initial policy context cache)
    (primitives : Primitives initial)
    {before : TheoryContext} {instances : InstanceWitnesses} {name : Name}
    {source : SourceTerm} {result : ContextConstantDefinitionResult}
    (accepted : admitConstantInTheory before instances name source = some result)
    (known : result.output.definitionTheorem ∈ cache)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (substitution : TypeSubst) :
    (frame.model other assignment).models
      (HOL.mapTypes substitution.baseInstance substitution.symbolInstance (constantSchema result)) := by
  have formed := (frame.valid _ known).wellFormed.1.1
  exact (family_models_closeAll_instance frame.family primitives other assignment substitution
    (constantSchema_translated accepted) formed (ContextFormed.nil _)).mp
      (frame.cached_constant_schema accepted known other _)

/-- A cached equation can be read through another successful admission of
the same resolved source declaration, without identifying their contexts. -/
theorem cached_source_definition_instance
    {initial context : TheoryContext} {policy : AxiomPolicy} {cache : Array Theorem}
    (frame : RegisteredReplayModels.Frame.{w} initial policy context cache) (primitives : Primitives initial)
    {referenceContext receivedContext : TheoryContext} {referenceInstances receivedInstances : InstanceWitnesses}
    {name : Name} {source : SourceTerm} {reference received : ContextConstantDefinitionResult}
    (referenceAccepted : admitConstantInTheory referenceContext referenceInstances name source = some reference)
    (receivedAccepted : admitConstantInTheory receivedContext receivedInstances name source = some received)
    (known : received.output.definitionTheorem ∈ cache)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) (substitution : TypeSubst) :
    (frame.model other assignment).models
      (HOL.mapTypes substitution.baseInstance substitution.symbolInstance (constantSchema reference)) := by
  have same := (admitConstantInTheory_payload_eq referenceAccepted receivedAccepted).2
  apply frame.cached_constant_schema_instance primitives referenceAccepted _ other assignment substitution
  rw [same]
  exact known

theorem model_refuses_falsity (frame : Frame.{w} initial policy context cache)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ¬ (frame.model other assignment).models PrimitiveSentences.falsityFormula := by
  intro holds
  have atFalse := holds (ULift.up False)
    (frame.model_fullDomains other assignment .prop (ULift.up False))
  exact atFalse.mpr fun _ _ => Iff.rfl

theorem cached_falsity_refused (frame : Frame.{w} initial policy context cache)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w})
    (fact : Theorem) (empty : fact.sequent.hyp = ∅)
    (translated : Translates [] fact.sequent.concl.term .prop PrimitiveSentences.falsityFormula) :
    fact ∉ cache := by
  intro known
  apply frame.model_refuses_falsity other assignment
  apply frame.cached_models_of_translation other assignment known translated
  rintro hypothesis ⟨term,member,_⟩
  rw [empty] at member
  exact absurd member (Finset.notMem_empty _)

#print axioms model_refuses_falsity
#print axioms cached_falsity_refused

theorem reachable [DecidablePred policy] (primitives : Primitives initial) :
    ∀ {before after : ProofExecution.Registered.State},
      Frame.{w} initial policy before.context before.cache →
      (ProofExecution.Registered.gslt policy).MultiStep before after →
      Nonempty (Frame.{w} initial policy after.context after.cache)
  | _,_,frame,.refl _ => ⟨frame⟩
  | before,_,frame,.step step rest => by
      obtain ⟨next,applied⟩ := step
      exact reachable primitives (apply primitives before _ frame next applied) rest

#print axioms reachable

#print axioms command
#print axioms apply
#print axioms replay
#print axioms cached_models

#print axioms typeDefinition

#print axioms constant

#print axioms proof

#print axioms background_closed
#print axioms existence_provable
end Frame

local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

noncomputable def initialFrame (context : TheoryContext) (primitives : Primitives context) :
    Frame.{w} context emptyAxiomPolicy context #[] :=
  Frame.empty primitives (fun _ unauthorized => False.elim unauthorized)

noncomputable def replayFrame (context : TheoryContext) (primitives : Primitives context)
    (commands : List ProofExecution.Registered.Command) (after : ProofExecution.Registered.State)
    (accepted : ProofExecution.Registered.replayFrom emptyAxiomPolicy
      (ProofExecution.Registered.empty context) commands = some after) :
    Frame.{w} context emptyAxiomPolicy after.context after.cache :=
  Frame.replay primitives (ProofExecution.Registered.empty context) after (initialFrame context primitives) commands accepted

theorem replay_models (context : TheoryContext) (primitives : Primitives context)
    (commands : List ProofExecution.Registered.Command) (after : ProofExecution.Registered.State)
    (accepted : ProofExecution.Registered.replayFrom emptyAxiomPolicy
      (ProofExecution.Registered.empty context) commands = some after)
    (other : OperatorFamilies.{w}) (assignment : Assignment.{w}) :
    ∃ model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol,
      model.FullDomains ∧ ∀ fact ∈ after.cache,
        ∃ formula, Translates [] fact.sequent.concl.term .prop formula ∧
          ((∀ hypothesis ∈ translatedHypotheses fact.sequent.hyp, model.models hypothesis) → model.models formula) := by
  let frame := replayFrame context primitives commands after accepted
  exact ⟨frame.model other assignment,frame.model_fullDomains other assignment,
    fun _ known => frame.cached_models other assignment known⟩

#print axioms replayFrame
#print axioms replay_models

end Mettapedia.Languages.HOLLight.RegisteredReplayModels
