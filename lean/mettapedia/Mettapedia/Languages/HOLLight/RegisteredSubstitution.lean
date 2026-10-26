import Mettapedia.Languages.HOLLight.PrimitiveTransport
import Mettapedia.Languages.HOLLight.TypeInstantiationCertificates

/-!
# Registered native type and term instantiation

Formation is preserved by the existing type-correct substitution. All stored
maplets are checked, including unused entries. The two original native
operations, `INST_TYPE` followed by `INST`, run through the registered source
receiver with its executable instance finder. Their actual execution retains
earlier proof addresses and derivations, adds two theorem outputs and two
receipts, and supplies a path in the existing registered GSLT.

The controls change both a carrier type and a free term. Unused undeclared
type and term maplets and a missing premise are refused. The OSLF observation
asserts theorem reachability; execution costs and occurrence-sensitive
observations remain separate. No native implementation refinement is assumed.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.HOLLight.DefinitionAdapters
open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open SignatureFormation

theorem TheoremFormed.substitute (signature : Signature)
    (substitution : TypeCorrectTermSubstitution)
    (typesFormed : ∀ name replacement, substitution.raw.types.lookup name = some replacement →
      TypeFormed signature replacement)
    (termsFormed : ∀ sourceVar replacement, substitution.raw.lookup sourceVar = some replacement →
      AnnotationsFormed signature replacement.canonical.term)
    {fact : Theorem} (formed : TheoremFormed signature fact) :
    TheoremFormed signature (substituteTheorem substitution fact) := by
  refine ⟨⟨AnnotationsFormed.substitute signature substitution.raw typesFormed termsFormed formed.1.1,?_⟩,?_⟩
  · intro hypothesis member
    change hypothesis ∈ fact.sequent.hyp.image substitution.apply at member
    obtain ⟨source,sourceMember,rfl⟩ := Finset.mem_image.mp member
    exact AnnotationsFormed.substitute signature substitution.raw typesFormed termsFormed
      (formed.1.2 source sourceMember)
  · exact formed.2

#print axioms TheoremFormed.substitute

structure SubstitutionFormed (signature : Signature) (substitution : TypeCorrectTermSubstitution) : Prop where
  types : ∀ entry ∈ substitution.raw.types.entries, TypeFormed signature entry.2
  keys : ∀ entry ∈ substitution.raw.entries, TypeFormed signature entry.1.ty
  terms : ∀ entry ∈ substitution.raw.entries, AnnotationsFormed signature entry.2.canonical.term

namespace SubstitutionFormed
variable {signature : Signature} {substitution : TypeCorrectTermSubstitution}

theorem type_replacements (formed : SubstitutionFormed signature substitution)
    (name : Name) (replacement : Ty)
    (found : substitution.raw.types.lookup name = some replacement) :
    TypeFormed signature replacement := by
  obtain ⟨left,right,equal,_⟩ := List.lookup_eq_some_iff.mp found
  exact formed.types (name,replacement) (by rw [equal]; simp)

theorem term_replacements (formed : SubstitutionFormed signature substitution)
    (sourceVar : SourceVar) (replacement : CheckedSourceTerm)
    (found : substitution.raw.lookup sourceVar = some replacement) :
    AnnotationsFormed signature replacement.canonical.term := by
  obtain ⟨entry,member,_,rfl⟩ := TermSubst.lookup_mem found
  exact formed.terms entry member

theorem preserves_theorem (formed : SubstitutionFormed signature substitution)
    {fact : Theorem} (factFormed : TheoremFormed signature fact) :
    TheoremFormed signature (substituteTheorem substitution fact) :=
  factFormed.substitute signature substitution formed.type_replacements formed.term_replacements

theorem type_parameters (formed : SubstitutionFormed signature substitution) (input : Theorem) :
    InferenceFormation.Formed signature
      (.instType (PrimitiveTransport.typeEntries substitution.raw.types) input) := by
  constructor
  · intro type member
    simp only [InferenceFormation.types, PrimitiveTransport.typeEntries,
      List.mem_flatMap, List.mem_map] at member
    obtain ⟨entry,⟨source,sourceMember,rfl⟩,member⟩ := member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact formed.types source sourceMember
    · simp [TypeFormed]
  · simp [InferenceFormation.terms]

theorem term_parameters (formed : SubstitutionFormed signature substitution) (input : Theorem) :
    InferenceFormation.Formed signature
      (.inst (PrimitiveTransport.termEntries substitution) input) := by
  constructor
  · simp [InferenceFormation.types]
  · intro term member
    simp only [InferenceFormation.terms, PrimitiveTransport.termEntries,
      List.mem_flatMap, List.mem_map] at member
    obtain ⟨entry,⟨source,sourceMember,rfl⟩,member⟩ := member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact formed.terms source sourceMember
    · simpa [SourceTerm.toDB, boundIndex] using AnnotationsFormed.free (formed.keys source sourceMember)

theorem type_stage_preserves (formed : SubstitutionFormed signature substitution)
    {input : Theorem} (inputFormed : TheoremFormed signature input) :
    TheoremFormed signature (substituteTheorem
      (SourceSubstitution.typeOnlySubstitution (PrimitiveTransport.typeEntries substitution.raw.types)) input) := by
  apply inputFormed.substitute
  · intro name replacement found
    have original : TypeFormed signature (substitution.raw.types.apply (.var name)) :=
      TypeFormed.substitute signature substitution.raw.types formed.type_replacements (by simp [TypeFormed])
    have same := PrimitiveTransport.typeEntries_apply substitution.raw.types (.var name)
    have typed : TypeFormed signature
        ((SourceSubstitution.typeSubstitution (PrimitiveTransport.typeEntries substitution.raw.types)).apply (.var name)) :=
      same ▸ original
    change (SourceSubstitution.typeSubstitution (PrimitiveTransport.typeEntries substitution.raw.types)).lookup name = some replacement at found
    simpa only [TypeSubst.apply, found, Option.getD_some] using typed
  · intro sourceVar replacement found
    simp [SourceSubstitution.typeOnlySubstitution, TypeCorrectTermSubstitution.ofTypes,
      TermSubst.lookup] at found

end SubstitutionFormed
#print axioms SubstitutionFormed.preserves_theorem
#print axioms SubstitutionFormed.type_parameters
#print axioms SubstitutionFormed.term_parameters
end Mettapedia.Languages.HOLLight.DefinitionAdapters

namespace Mettapedia.Languages.HOLLight.RegisteredSubstitution
open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open DefinitionAdapters SignatureFormation
open ProofExecution.Registered (State)

def typePart (substitution : TypeCorrectTermSubstitution) : TypeCorrectTermSubstitution :=
  SourceSubstitution.typeOnlySubstitution (PrimitiveTransport.typeEntries substitution.raw.types)

def firstNode (substitution : TypeCorrectTermSubstitution) (input : Theorem)
    (index : Nat) (origin : ProofExecution.Origin) : ProofExecution.Receipt :=
  ⟨substituteTheorem (typePart substitution) input,
    .inference (.instType (PrimitiveTransport.typeEntries substitution.raw.types) input),
    [index],origin⟩

def secondNode (substitution : TypeCorrectTermSubstitution) (input : Theorem)
    (index : Nat) (origin : ProofExecution.Origin) : ProofExecution.Receipt :=
  ⟨substituteTheorem substitution input,
    .inference (.inst (PrimitiveTransport.termEntries substitution)
      (substituteTheorem (typePart substitution) input)),[index],origin⟩

def apply (policy : AxiomPolicy) [DecidablePred policy]
    (substitution : TypeCorrectTermSubstitution) (before : State) (index : Nat)
    (origin : ProofExecution.Origin) : Option State := do
  let input ← before.cache[index]?
  let instances := ExportReplay.instanceCertificates before.context.signature
  let middle ← ProofExecution.Registered.apply policy before
    (.proof (firstNode substitution input index origin) instances)
  ProofExecution.Registered.apply policy middle
    (.proof (secondNode substitution input before.cache.size origin) instances)

theorem first_checked (substitution : TypeCorrectTermSubstitution) (input : Theorem) :
    (InferenceRequest.instType (PrimitiveTransport.typeEntries substitution.raw.types) input).check =
      some (substituteTheorem (typePart substitution) input) :=
  (InferenceRequest.check_eq_some_iff _ _).mpr (substituteTheorem_semantics _ _)

theorem second_checked (substitution : TypeCorrectTermSubstitution) (input : Theorem) :
    (InferenceRequest.inst (PrimitiveTransport.termEntries substitution)
      (substituteTheorem (typePart substitution) input)).check =
      some (substituteTheorem substitution input) := by
  apply (InferenceRequest.check_eq_some_iff _ _).mpr
  refine ⟨PrimitiveTransport.termOnly substitution, PrimitiveTransport.termEntries_admitted substitution, ?_⟩
  rw [show substituteTheorem substitution input =
    substituteTheorem (PrimitiveTransport.termOnly substitution)
      (substituteTheorem (typePart substitution) input) from
        (PrimitiveTransport.substituteTheorem_split substitution input).symm]
  exact substituteTheorem_semantics _ _

private theorem apply_proof (policy : AxiomPolicy) [DecidablePred policy]
    (before : State) (node : ProofExecution.Receipt)
    (replayed : node.replay (ruleWitness policy) before.cache = some (before.cache.push node.conclusion))
    (parameters : ProofExecution.Registered.requestFormedB before.context.signature
      (ExportReplay.instanceCertificates before.context.signature) node.witness = true)
    (result : theoremFormedB before.context.signature
      (ExportReplay.instanceCertificates before.context.signature) node.conclusion = true) :
    ProofExecution.Registered.apply policy before
      (.proof node (ExportReplay.instanceCertificates before.context.signature)) =
        some ⟨before.context,before.cache.push node.conclusion,
          before.receipts.push ⟨.proof node (ExportReplay.instanceCertificates before.context.signature),[node.conclusion]⟩⟩ := by
  simp only [ProofExecution.Registered.apply, ProofExecution.Registered.Command.check,
    replayed, parameters, result, and_self, ↓reduceIte]
  change some (⟨before.context,before.cache ++ #[node.conclusion],
    before.receipts.push ⟨.proof node (ExportReplay.instanceCertificates before.context.signature),[node.conclusion]⟩⟩ : State) = _
  rw [Array.append_singleton]

#print axioms first_checked
#print axioms second_checked
#print axioms apply_proof

theorem apply_available (policy : AxiomPolicy) [DecidablePred policy]
    (substitution : TypeCorrectTermSubstitution) (before : State) (index : Nat)
    (origin : ProofExecution.Origin) {input : Theorem}
    (known : before.cache[index]? = some input)
    (inputFormed : TheoremFormed before.context.signature input)
    (formed : SubstitutionFormed before.context.signature substitution) :
    ∃ after, apply policy substitution before index origin = some after ∧
      after.context = before.context ∧
      after.cache = (before.cache.push (substituteTheorem (typePart substitution) input)).push
        (substituteTheorem substitution input) ∧
      after.cache[before.cache.size + 1]? = some (substituteTheorem substitution input) ∧
      after.receipts.size = before.receipts.size + 2 := by
  let typed := substituteTheorem (typePart substitution) input
  let final := substituteTheorem substitution input
  let first := firstNode substitution input index origin
  let second := secondNode substitution input before.cache.size origin
  have firstReplay : first.replay (ruleWitness policy) before.cache = some (before.cache.push typed) := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    refine ⟨?_,first_checked substitution input,rfl⟩
    simp [first,firstNode,DerivationGraph.lookupPremises,RuleRequest.premises,
      InferenceRequest.premises,known]
  have firstParameters : ProofExecution.Registered.requestFormedB before.context.signature
      (ExportReplay.instanceCertificates before.context.signature) first.witness = true :=
    (TypeInstantiationCertificates.inferenceFormationCheck_exact _ _).mpr (formed.type_parameters input)
  have typedFormed : theoremFormedB before.context.signature
      (ExportReplay.instanceCertificates before.context.signature) typed = true :=
    (TypeInstantiationCertificates.theoremFormedB_exact _ _).mpr (formed.type_stage_preserves inputFormed)
  let middle : State := ⟨before.context,before.cache.push typed,
    before.receipts.push ⟨.proof first (ExportReplay.instanceCertificates before.context.signature),[typed]⟩⟩
  have firstApply : ProofExecution.Registered.apply policy before
      (.proof first (ExportReplay.instanceCertificates before.context.signature)) = some middle :=
    apply_proof policy before first firstReplay firstParameters typedFormed
  have secondReplay : second.replay (ruleWitness policy) middle.cache = some (middle.cache.push final) := by
    apply (ProofSystem.node_replay_iff policy _ _ _).mpr
    refine ⟨?_,second_checked substitution input,rfl⟩
    simp [second,secondNode,DerivationGraph.lookupPremises,RuleRequest.premises,
      InferenceRequest.premises,middle,typed]
  have secondParameters : ProofExecution.Registered.requestFormedB middle.context.signature
      (ExportReplay.instanceCertificates middle.context.signature) second.witness = true :=
    (TypeInstantiationCertificates.inferenceFormationCheck_exact _ _).mpr (formed.term_parameters typed)
  have finalFormed : theoremFormedB middle.context.signature
      (ExportReplay.instanceCertificates middle.context.signature) final = true :=
    (TypeInstantiationCertificates.theoremFormedB_exact _ _).mpr (formed.preserves_theorem inputFormed)
  let after : State := ⟨middle.context,middle.cache.push final,
    middle.receipts.push ⟨.proof second (ExportReplay.instanceCertificates middle.context.signature),[final]⟩⟩
  have secondApply : ProofExecution.Registered.apply policy middle
      (.proof second (ExportReplay.instanceCertificates before.context.signature)) = some after :=
    apply_proof policy middle second secondReplay secondParameters finalFormed
  refine ⟨after,?_,rfl,rfl,?_,?_⟩
  · simpa [apply,known] using (show
      (do let next ← ProofExecution.Registered.apply policy before
            (.proof first (ExportReplay.instanceCertificates before.context.signature))
          ProofExecution.Registered.apply policy next
            (.proof second (ExportReplay.instanceCertificates before.context.signature))) = some after by
        rw [firstApply]
        exact secondApply)
  · change ((before.cache.push typed).push final)[before.cache.size + 1]? = some final
    simpa only [Array.size_push] using
      (Array.getElem?_push_size (xs := before.cache.push typed) (x := final))
  · simp [after,middle,Nat.add_assoc]

#print axioms apply_available

theorem apply_steps (policy : AxiomPolicy) [DecidablePred policy]
    {substitution : TypeCorrectTermSubstitution} {before after : State} {index : Nat}
    {origin : ProofExecution.Origin}
    (accepted : apply policy substitution before index origin = some after) :
    ∃ input middle, before.cache[index]? = some input ∧
      ProofExecution.Registered.apply policy before
        (.proof (firstNode substitution input index origin)
          (ExportReplay.instanceCertificates before.context.signature)) = some middle ∧
      ProofExecution.Registered.apply policy middle
        (.proof (secondNode substitution input before.cache.size origin)
          (ExportReplay.instanceCertificates before.context.signature)) = some after := by
  obtain ⟨input,known,rest⟩ := Option.bind_eq_some_iff.mp accepted
  obtain ⟨middle,first,second⟩ := Option.bind_eq_some_iff.mp rest
  exact ⟨input,middle,known,first,second⟩

theorem preserves_derivations (policy : AxiomPolicy) [DecidablePred policy]
    {substitution : TypeCorrectTermSubstitution} {before after : State} {index : Nat}
    {origin : ProofExecution.Origin} (valid : ProofExecution.Registered.Valid policy before)
    (accepted : apply policy substitution before index origin = some after) :
    ProofExecution.Registered.Valid policy after := by
  obtain ⟨_,_,_,first,second⟩ := apply_steps policy accepted
  exact ProofExecution.Registered.apply_preserves_derivations policy
    (ProofExecution.Registered.apply_preserves_derivations policy valid first) second

theorem preserves_lookup (policy : AxiomPolicy) [DecidablePred policy]
    {substitution : TypeCorrectTermSubstitution} {before after : State} {index previous : Nat}
    {origin : ProofExecution.Origin} {fact : Theorem}
    (accepted : apply policy substitution before index origin = some after)
    (known : before.cache[previous]? = some fact) :
    after.cache[previous]? = some fact := by
  obtain ⟨_,_,_,first,second⟩ := apply_steps policy accepted
  exact ProofExecution.Registered.apply_preserves_lookup policy second
    (ProofExecution.Registered.apply_preserves_lookup policy first known)

#print axioms apply_steps
#print axioms preserves_derivations
#print axioms preserves_lookup


theorem execution_path (policy : AxiomPolicy) [DecidablePred policy]
    {substitution : TypeCorrectTermSubstitution} {before after : State} {index : Nat}
    {origin : ProofExecution.Origin}
    (accepted : apply policy substitution before index origin = some after) :
    (ProofExecution.Registered.gslt policy).MultiStep before after := by
  obtain ⟨_,_,_,first,second⟩ := apply_steps policy accepted
  exact .step ⟨_,first⟩ (.step ⟨_,second⟩ (.refl _))

namespace Controls
local instance : DecidablePred emptyAxiomPolicy := fun _ => isFalse id

def parameter : Name := Name.global "sourceParameter"
def valueName : Name := Name.global "sourceValue"
def operand : CanonicalTerm :=
  ⟨.free ⟨valueName,.var parameter⟩,.var parameter,by simp [DBTerm.inferType]⟩
def inputFact : Theorem := Theorem.emptyResult ∅ (CanonicalTerm.equalityOfSameType operand operand rfl)
def inputNode : ProofExecution.Receipt := ⟨inputFact,.inference (.refl operand),[],("substitution-input",0)⟩
def inputCommand : ProofExecution.Registered.Command := .proof inputNode
  (ExportReplay.instanceCertificates ContextControls.coreContext.signature)
def before : State := ⟨ContextControls.coreContext,#[inputFact],#[⟨inputCommand,[inputFact]⟩]⟩

theorem input_replayed : inputNode.replay (ruleWitness emptyAxiomPolicy) #[] = some #[inputFact] := by
  apply (ProofSystem.node_replay_iff emptyAxiomPolicy _ _ _).mpr
  exact ⟨rfl,by decide +kernel,rfl⟩

theorem input_parameters : ProofExecution.Registered.requestFormedB ContextControls.coreContext.signature
    (ExportReplay.instanceCertificates ContextControls.coreContext.signature) inputNode.witness = true := by
  decide +kernel

theorem input_result_formed : theoremFormedB ContextControls.coreContext.signature
    (ExportReplay.instanceCertificates ContextControls.coreContext.signature) inputFact = true := by
  decide +kernel

theorem before_replayed : ProofExecution.Registered.apply emptyAxiomPolicy
    (ProofExecution.Registered.empty ContextControls.coreContext) inputCommand = some before :=
  apply_proof emptyAxiomPolicy _ inputNode input_replayed input_parameters input_result_formed

theorem before_valid : ProofExecution.Registered.Valid emptyAxiomPolicy before :=
  ProofExecution.Registered.apply_preserves_derivations emptyAxiomPolicy
    (ProofExecution.Registered.empty_valid _ _) before_replayed

def destination : Ty := Ty.function Ty.bool Ty.bool

def replacement : CheckedSourceTerm := PrimitiveTransport.checkedSource DefinitionAdapters.Controls.identityTerm

def substitution : TypeCorrectTermSubstitution :=
  { raw := ⟨⟨[(parameter,destination)]⟩,[(⟨valueName,destination⟩,replacement)]⟩
    typeCorrect := by
      intro entry member
      simp only [List.mem_singleton] at member
      subst entry
      exact congrArg CanonicalTerm.ty (PrimitiveTransport.checkedSource_exact DefinitionAdapters.Controls.identityTerm) }

theorem boolean_formed : TypeFormed ContextControls.coreContext.signature Ty.bool :=
  ContextControls.boolean_formed.mono ContextControls.core_includes

theorem destination_formed : TypeFormed ContextControls.coreContext.signature destination :=
  TypeFormed.function _ (ContextControls.core_includes.1 _ _ ContextControls.function_registered)
    boolean_formed boolean_formed

theorem substitution_formed : SubstitutionFormed ContextControls.coreContext.signature substitution := by
  constructor
  · intro entry member
    simp only [substitution,List.mem_singleton] at member
    subst entry
    exact destination_formed
  · intro entry member
    simp only [substitution,List.mem_singleton] at member
    subst entry
    exact destination_formed
  · intro entry member
    simp only [substitution,List.mem_singleton] at member
    subst entry
    change AnnotationsFormed _ (PrimitiveTransport.checkedSource DefinitionAdapters.Controls.identityTerm).canonical.term
    rw [PrimitiveTransport.checkedSource_exact]
    exact .abs boolean_formed (.bound 0)

theorem substitution_applied :
    ∃ after, apply emptyAxiomPolicy substitution before 0 ("substitution",0) = some after ∧
      after.context = before.context ∧
      after.cache = (before.cache.push (substituteTheorem (typePart substitution) inputFact)).push
        (substituteTheorem substitution inputFact) ∧
      after.cache[before.cache.size + 1]? = some (substituteTheorem substitution inputFact) ∧
      after.receipts.size = before.receipts.size + 2 :=
  apply_available emptyAxiomPolicy substitution before 0 ("substitution",0) rfl
    ((TypeInstantiationCertificates.theoremFormedB_exact _ _).mp input_result_formed) substitution_formed

def unsupported : Ty := .op ⟨Name.global "undeclaredCarrier", .undefined⟩ []

def unusedBadType : TypeCorrectTermSubstitution :=
  { substitution with raw := {substitution.raw with types :=
      ⟨substitution.raw.types.entries ++ [(Name.global "unusedParameter",unsupported)]⟩} }

def unusedBadTerm : TypeCorrectTermSubstitution :=
  let source : CheckedSourceTerm :=
    ⟨.const ⟨Name.global "undeclaredTerm" , .undefined⟩ Ty.bool,Ty.bool,by simp [SourceTerm.inferType]⟩
  { raw := {substitution.raw with entries := substitution.raw.entries ++
      [(⟨Name.global "unusedValue",Ty.bool⟩,source)]}
    typeCorrect := by
      intro entry member
      rcases List.mem_append.mp member with member | member
      · exact substitution.typeCorrect entry member
      · simp only [List.mem_singleton] at member
        subst entry
        rfl }

theorem unused_type_refused :
    (apply emptyAxiomPolicy unusedBadType before 0 ("bad-type",0)).isNone = true := by
  decide +kernel

theorem unused_term_refused :
    (apply emptyAxiomPolicy unusedBadTerm before 0 ("bad-term",0)).isNone = true := by
  decide +kernel

theorem missing_input_refused :
    (apply emptyAxiomPolicy substitution before 1 ("missing",0)).isNone = true := by
  decide +kernel

theorem application_checked :
    (apply emptyAxiomPolicy substitution before 0 ("substitution",0)).isSome = true := by
  decide +kernel

theorem changed_value :
    (substituteTheorem substitution inputFact).sequent.concl ≠ inputFact.sequent.concl := by
  decide +kernel


def after : State := (apply emptyAxiomPolicy substitution before 0 ("substitution",0)).get application_checked

theorem after_applied : apply emptyAxiomPolicy substitution before 0 ("substitution",0) = some after :=
  (Option.some_get application_checked).symm

theorem after_valid : ProofExecution.Registered.Valid emptyAxiomPolicy after :=
  preserves_derivations emptyAxiomPolicy before_valid after_applied

theorem original_address_preserved : after.cache[0]? = some inputFact :=
  preserves_lookup emptyAxiomPolicy after_applied rfl

theorem actual_two_commands :
    ∃ input middle, before.cache[0]? = some input ∧
      ProofExecution.Registered.apply emptyAxiomPolicy before
        (.proof (firstNode substitution input 0 ("substitution",0))
          (ExportReplay.instanceCertificates before.context.signature)) = some middle ∧
      ProofExecution.Registered.apply emptyAxiomPolicy middle
        (.proof (secondNode substitution input before.cache.size ("substitution",0))
          (ExportReplay.instanceCertificates before.context.signature)) = some after :=
  apply_steps emptyAxiomPolicy after_applied

theorem closed_final_formation :
    TheoremFormed before.context.signature (substituteTheorem substitution inputFact) :=
  TheoremFormed.substitute _ _ substitution_formed.type_replacements substitution_formed.term_replacements
    ((TypeInstantiationCertificates.theoremFormedB_exact _ _).mp input_result_formed)

theorem closed_type_stage :
    TheoremFormed before.context.signature (substituteTheorem (typePart substitution) inputFact) :=
  substitution_formed.type_stage_preserves
    ((TypeInstantiationCertificates.theoremFormedB_exact _ _).mp input_result_formed)

theorem closed_type_parameters : InferenceFormation.Formed before.context.signature
    (.instType (PrimitiveTransport.typeEntries substitution.raw.types) inputFact) :=
  substitution_formed.type_parameters inputFact

theorem closed_term_parameters : InferenceFormation.Formed before.context.signature
    (.inst (PrimitiveTransport.termEntries substitution) inputFact) :=
  substitution_formed.term_parameters inputFact

theorem final_root_and_receipts : after.cache[2]? = some (substituteTheorem substitution inputFact) ∧
    after.receipts.size = 3 := by
  obtain ⟨result,replayed,_,_,root,count⟩ := substitution_applied
  have equal : result = after := Option.some.inj (replayed.symm.trans after_applied)
  subst result
  exact ⟨root,count⟩

theorem after_path : (ProofExecution.Registered.gslt emptyAxiomPolicy).MultiStep before after :=
  execution_path emptyAxiomPolicy after_applied

theorem after_reachable : (ProofExecution.Registered.gslt emptyAxiomPolicy).MultiStep
    (ProofExecution.Registered.empty ContextControls.coreContext) after :=
  .step ⟨inputCommand,before_replayed⟩ after_path


open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

theorem final_observed :
    (gsltOSLF (ProofExecution.Registered.gslt emptyAxiomPolicy).closure).satisfies (S := ())
      (ProofExecution.Registered.empty ContextControls.coreContext)
      (ProofExecution.Registered.theoremNativeType emptyAxiomPolicy
        (substituteTheorem substitution inputFact)).pred :=
  (ProofExecution.Registered.satisfies_theoremNativeType_iff_reachable _ _ _).mpr
    ⟨after,after_reachable,Array.mem_of_getElem? final_root_and_receipts.1⟩


def verdicts : List (String × Bool) :=
  [("registered-substitution/type-and-term", (apply emptyAxiomPolicy substitution before 0 ("substitution",0)).isSome),
   ("registered-substitution/cache-and-receipts", after.cache.size == 3 && after.receipts.size == 3),
   ("registered-substitution/original-address", decide (after.cache[0]? = some inputFact)),
   ("registered-substitution/final-root", decide (after.cache[2]? = some (substituteTheorem substitution inputFact))),
   ("registered-substitution/changed-value", !((substituteTheorem substitution inputFact).sequent.concl.same inputFact.sequent.concl)),
   ("registered-substitution/unused-type-refused", (apply emptyAxiomPolicy unusedBadType before 0 ("bad-type",0)).isNone),
   ("registered-substitution/unused-term-refused", (apply emptyAxiomPolicy unusedBadTerm before 0 ("bad-term",0)).isNone),
   ("registered-substitution/missing-input-refused", (apply emptyAxiomPolicy substitution before 1 ("missing",0)).isNone)]

end Controls
#print axioms Controls.final_observed
#print axioms execution_path
#print axioms Controls.after_valid
#print axioms Controls.final_root_and_receipts
#print axioms Controls.before_valid
#print axioms Controls.substitution_applied
end Mettapedia.Languages.HOLLight.RegisteredSubstitution
