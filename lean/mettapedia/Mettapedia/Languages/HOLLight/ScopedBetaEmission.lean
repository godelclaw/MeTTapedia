import Mettapedia.Languages.HOLLight.QuantifierEmission
import Mettapedia.Languages.HOLLight.ScopedNamedTemplates

/-!
# Original BETA fields for changing authored bodies

A fixed typed authored de Bruijn body yields both original BETA/INST node
fields from independently encoded earlier raw and named operands, the current
operand, and its origin. The compiled plan does not receive a precomputed
changing body, beta source, intermediate theorem, or conclusion.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.ScopedBetaEmission
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability.WordTemplateMachine
open PrimitiveTransport EqualityExpansion EqualityExpansion.Emission
open ProofDataEncoding
open ProofExecution (Origin)
abbrev FieldCount (arity : Nat) := (arity+arity)+3
abbrev Plan (arity : Nat) := Indexed.Template Alphabet (FieldCount arity)

def rawIndex {arity : Nat} (index : Fin arity) : Fin (FieldCount arity) := (index.castAdd arity).castAdd 3
def namedIndex {arity : Nat} (index : Fin arity) : Fin (FieldCount arity) := (Fin.natAdd arity index).castAdd 3
def rawOperandIndex (arity : Nat) : Fin (FieldCount arity) := Fin.natAdd (arity+arity) 0
def namedOperandIndex (arity : Nat) : Fin (FieldCount arity) := Fin.natAdd (arity+arity) 1
def originIndex (arity : Nat) : Fin (FieldCount arity) := Fin.natAdd (arity+arity) 2

def fields {arity : Nat} (previous : Fin arity → CanonicalTerm) (argument : CanonicalTerm) (origin : Origin) :
    Fin (FieldCount arity) → List Alphabet :=
  Fin.addCases (Fin.addCases (fun index => encodeWith dbTermCodec (previous index).term)
      (fun index => encodeWith sourceTermCodec (checkedSource (previous index)).source))
    ![encodeWith dbTermCodec argument.term,encodeWith sourceTermCodec (checkedSource argument).source,
      encodeWith originCodec origin]

@[simp] theorem raw_field {arity : Nat} (previous : Fin arity → CanonicalTerm) (argument : CanonicalTerm) (origin : Origin) (index : Fin arity) :
    fields previous argument origin (rawIndex index) = encodeWith dbTermCodec (previous index).term := by
  simp [fields,rawIndex]
@[simp] theorem named_field {arity : Nat} (previous : Fin arity → CanonicalTerm) (argument : CanonicalTerm) (origin : Origin) (index : Fin arity) :
    fields previous argument origin (namedIndex index) = encodeWith sourceTermCodec (checkedSource (previous index)).source := by
  simp only [fields,namedIndex,Fin.addCases_left,Fin.addCases_right]
@[simp] theorem operand_field {arity : Nat} (previous : Fin arity → CanonicalTerm) (argument : CanonicalTerm) (origin : Origin) :
    fields previous argument origin (rawOperandIndex arity) = encodeWith dbTermCodec argument.term := by
  simp [fields,rawOperandIndex]
@[simp] theorem named_operand_field {arity : Nat} (previous : Fin arity → CanonicalTerm) (argument : CanonicalTerm) (origin : Origin) :
    fields previous argument origin (namedOperandIndex arity) = encodeWith sourceTermCodec (checkedSource argument).source := by
  simp [fields,namedOperandIndex]
@[simp] theorem origin_field {arity : Nat} (previous : Fin arity → CanonicalTerm) (argument : CanonicalTerm) (origin : Origin) :
    fields previous argument origin (originIndex arity) = encodeWith originCodec origin := by
  simp [fields,originIndex]

/-- The changing original body is the actual ordered earlier instantiation. -/
def body {arity : Nat} (previous : Fin arity → CanonicalTerm) (authored : DBTerm) : DBTerm :=
  TemplateInstantiationMachine.Indexed.sequence (List.ofFn previous) 1 authored

theorem previous_types {arity : Nat} (previous : Fin arity → CanonicalTerm) (domain : Ty)
    (typed : ∀ index, (previous index).ty=domain) :
    (List.ofFn previous).map CanonicalTerm.ty = List.replicate arity domain := by
  rw [List.map_ofFn]
  change List.ofFn (fun index => (previous index).ty) = _
  rw [show (fun index => (previous index).ty) = (fun _ : Fin arity => domain) from funext typed]
  exact List.ofFn_const _ _

theorem checkedBody (arity : Nat) (domain codomain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some codomain)
    (previous : Fin arity → CanonicalTerm) (typed : ∀ index, (previous index).ty=domain) :
    (body previous authored).inferType [domain] = some codomain := by
  apply TemplateInstantiationMachine.Indexed.sequence_typed (List.ofFn previous) [domain] authored codomain
  simpa only [previous_types previous domain typed,List.singleton_append] using checked

/-- All substitution choices are authored static holes, not input predicates. -/
def rawBody (arity : Nat) (authored : DBTerm) : Plan arity :=
  Templates.substitute (TemplateInstantiationMachine.Indexed.compile arity 1 authored)
    (fun index => [.inr (rawIndex index)])

theorem rawBody_exact {arity : Nat} (authored : DBTerm)
    (previous : Fin arity → CanonicalTerm) (argument : CanonicalTerm) (origin : Origin) :
    Indexed.instantiate (rawBody arity authored) (fields previous argument origin) =
      encodeWith dbTermCodec (body previous authored) := by
  rw [rawBody,Templates.substitute_exact]
  simpa only [Indexed.instantiate_hole,Indexed.instantiate_nil,List.append_nil,raw_field,TemplateInstantiationMachine.termWire,body,encodeWith,dbTermCodec] using
    TemplateInstantiationMachine.Indexed.compile_exact_values arity 1 authored previous

def abstraction {arity : Nat} (domain : Ty) (plan : Plan arity) : Plan arity :=
  Templates.pair (Templates.literal (.atom 4)) (Templates.pair (Templates.literal (putTy domain)) plan)

theorem abstraction_exact {arity : Nat} (domain : Ty) (plan : Plan arity)
    (words : Fin (FieldCount arity) → List Alphabet) (term : DBTerm)
    (exactBody : Indexed.instantiate plan words = encodeWith dbTermCodec term) :
    Indexed.instantiate (abstraction domain plan) words = encodeWith dbTermCodec (.abs domain term) := by
  simp only [abstraction,Templates.pair_exact,Templates.literal_exact,exactBody]
  simp only [encodeWith,dbTermCodec,putTerm,encodeData_pair]
  rfl

def reduced (arity : Nat) (authored : DBTerm) (replacement : Plan arity) : Plan arity :=
  Templates.substitute (TemplateInstantiationMachine.Indexed.compile (arity+1) 0 authored)
    (Fin.cases replacement (fun index => [.inr (rawIndex index)]))

theorem reduced_exact {arity : Nat} (authored : DBTerm) (replacement : Plan arity)
    (previous : Fin arity → CanonicalTerm) (argument value : CanonicalTerm) (origin : Origin)
    (exactReplacement : Indexed.instantiate replacement (fields previous argument origin) = encodeWith dbTermCodec value.term) :
    Indexed.instantiate (reduced arity authored replacement) (fields previous argument origin) =
      encodeWith dbTermCodec (DBTerm.instantiateAt value.term 0 (body previous authored)) := by
  rw [reduced,Templates.substitute_exact]
  have actual := TemplateInstantiationMachine.Indexed.compile_exact_values (arity+1) 0 authored (Fin.cases value previous)
  have aligned : (fun index => Indexed.instantiate (Fin.cases replacement
      (fun index => [.inr (rawIndex index)]) index : Plan arity) (fields previous argument origin)) =
      (fun index => encodeWith dbTermCodec (Fin.cases value previous index : CanonicalTerm).term) := by
    funext index
    refine Fin.cases ?_ (fun index => ?_) index
    · exact exactReplacement
    · simp only [Fin.cases_succ,Indexed.instantiate_hole,Indexed.instantiate_nil,List.append_nil,raw_field]
  rw [aligned]
  simpa only [List.ofFn_succ,Fin.cases_zero,Fin.cases_succ,TemplateInstantiationMachine.Indexed.sequence,
    body,TemplateInstantiationMachine.termWire,encodeWith,dbTermCodec,Nat.zero_add] using actual



theorem body_scope (arity : Nat) (domain codomain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some codomain) :
    authored.LooseBelow (1+arity) := by
  simpa only [List.length_cons,List.length_replicate,Nat.add_comm] using DBTerm.looseBelow_of_inferType checked

theorem freeNames_body {arity : Nat} (previous : Fin arity → CanonicalTerm)
    (empty : ∀ index, freeNames (previous index).term = []) (authored : DBTerm) :
    freeNames (body previous authored) = freeNames authored := by
  apply ScopedNamedTemplates.freeNames_sequence (List.ofFn previous) _ 1 authored
  intro value member
  obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
  exact empty index

theorem needle_body {arity : Nat} (domain : Ty) (previous : Fin arity → CanonicalTerm)
    (empty : ∀ index, freeNames (previous index).term = []) (authored : DBTerm) :
    betaNeedle domain (body previous authored) = betaNeedle domain authored := by
  simp only [betaNeedle,freeNames_body previous empty authored]

def namedBody (arity : Nat) (domain codomain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some codomain) : Plan arity :=
  Templates.substitute
    (ScopedNamedTemplates.plan arity authored [betaNeedle domain authored]
      (by simpa only [List.length_singleton] using body_scope arity domain codomain authored checked))
    (fun index => [.inr (namedIndex index)])

theorem namedBody_exact {arity : Nat} (domain codomain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some codomain)
    (previous : Fin arity → CanonicalTerm) (argument : CanonicalTerm) (origin : Origin)
    (empty : ∀ index, freeNames (previous index).term = [])
    (independent : ∀ index binders, named? (previous index).term binders = some (checkedSource (previous index)).source)
    (source : SourceTerm) (computed : named? (body previous authored) [betaNeedle domain authored] = some source) :
    Indexed.instantiate (namedBody arity domain codomain authored checked) (fields previous argument origin) =
      encodeWith sourceTermCodec source := by
  rw [namedBody,Templates.substitute_exact]
  have exactResult := ScopedNamedTemplates.compile_exact_values arity previous
    (fun index => (checkedSource (previous index)).source) empty independent 1 authored [betaNeedle domain authored]
  have planned := ScopedNamedTemplates.plan_computed arity authored [betaNeedle domain authored]
    (by simpa only [List.length_singleton] using body_scope arity domain codomain authored checked)
  simp only [List.length_singleton] at planned
  rw [planned] at exactResult
  rw [show named? (TemplateInstantiationMachine.Indexed.sequence (List.ofFn previous) 1 authored)
    [betaNeedle domain authored] = some source from computed] at exactResult
  simpa only [Option.map_some,Option.some.injEq,Indexed.instantiate_hole,Indexed.instantiate_nil,
    List.append_nil,named_field] using exactResult

/-- The original fresh BETA source changes with previous operands; its bytes
are generated by one fixed scoped plan. -/
def betaSourceTemplate (arity : Nat) (domain codomain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some codomain) : Plan arity :=
  let needle := betaNeedle domain authored
  Templates.pair (Templates.sourceApplication
    (Templates.sourceAbstraction needle.name domain (namedBody arity domain codomain authored checked))
    (Templates.literal (putSourceTerm (.var needle.name domain)))) (Templates.literal (putTy codomain))

theorem betaSource_exact {arity : Nat} (domain codomain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some codomain)
    (previous : Fin arity → CanonicalTerm) (typed : ∀ index, (previous index).ty=domain)
    (argument : CanonicalTerm) (origin : Origin)
    (empty : ∀ index, freeNames (previous index).term = [])
    (independent : ∀ index binders, named? (previous index).term binders = some (checkedSource (previous index)).source) :
    Indexed.instantiate (betaSourceTemplate arity domain codomain authored checked) (fields previous argument origin) =
      encodeWith checkedSourceCodec (betaSource domain (body previous authored) codomain
        (checkedBody arity domain codomain authored checked previous typed)) := by
  let needle := betaNeedle domain authored
  let nextBody := body previous authored
  let checkedNext := checkedBody arity domain codomain authored checked previous typed
  have scope : nextBody.LooseBelow [needle].length := DBTerm.looseBelow_of_inferType checkedNext
  have unique : ([needle].map Var.name).Nodup := by simp
  have fresh : ∀ name ∈ freeNames nextBody, name ∉ [needle].map Var.name := by
    rw [show freeNames nextBody=freeNames authored from freeNames_body previous empty authored]
    intro name member
    simp only [List.map_cons,List.map_nil,List.mem_singleton]
    exact fun equal => betaNeedle_fresh domain authored (equal ▸ member)
  let source := named nextBody [needle] scope unique fresh
  have computed : named? nextBody [needle] = some source :=
    TemplateInstantiationMachine.Named.named_computed nextBody [needle] scope unique fresh
  have namedExact := namedBody_exact domain codomain authored checked previous argument origin empty independent source computed
  have needleSame := needle_body domain previous empty authored
  simp only [betaSourceTemplate,Templates.sourceApplication,Templates.sourceAbstraction,Templates.pair_exact,
    Templates.literal_exact,namedExact]
  simp only [betaSource,needleSame,checkedSourceCodec,Codec.mapped,Codec.prod,encodeWith,sourceTermCodec,tyCodec,
    putSourceTerm,encodeData_pair]
  rfl



def betaEquation (arity : Nat) (domain codomain : Ty) (authored : DBTerm) (replacement : Plan arity) : Plan arity :=
  Templates.theoremTemplate ∅ ∅ (Templates.canonical Ty.bool (Templates.equality codomain
    (Templates.application (abstraction domain (rawBody arity authored)) replacement)
    (reduced arity authored replacement)))

theorem betaEquation_exact {arity : Nat} (domain codomain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some codomain)
    (previous : Fin arity → CanonicalTerm) (typed : ∀ index, (previous index).ty=domain)
    (argument value : CanonicalTerm) (valueType : value.ty=domain) (origin : Origin)
    (replacement : Plan arity)
    (exactReplacement : Indexed.instantiate replacement (fields previous argument origin) = encodeWith dbTermCodec value.term) :
    Indexed.instantiate (betaEquation arity domain codomain authored replacement) (fields previous argument origin) =
      encodeWith theoremCodec (Theorem.emptyResult ∅ (CanonicalTerm.equalityOfSameType
        (betaRedex domain (body previous authored) codomain (checkedBody arity domain codomain authored checked previous typed) value valueType)
        (betaReduced domain (body previous authored) codomain (checkedBody arity domain codomain authored checked previous typed) value valueType) rfl)) := by
  apply Templates.theoremTemplate_exact ∅ ∅ _ _ _ rfl rfl
  apply Templates.canonical_exact Ty.bool _ _ _ rfl
  refine Templates.equality_exact codomain _ _ _ _ _ ?_ ?_
  · apply Templates.application_exact _ _ _ _ _ _ exactReplacement
    exact abstraction_exact domain _ _ _ (rawBody_exact authored previous argument origin)
  · exact reduced_exact authored replacement previous argument value origin exactReplacement

/-- Both original BETA/INST occurrences generate their changing complete
fields from the authored body and independent operands. -/
def nodes (arity : Nat) (domain codomain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some codomain) :
    List (Mettapedia.Logic.DerivationGraph.Node (Plan arity) (Plan arity) (Plan arity)) :=
  let operand : Plan arity := [.inr (rawOperandIndex arity)]
  let namedOperand : Plan arity := [.inr (namedOperandIndex arity)]
  let origin : Plan arity := [.inr (originIndex arity)]
  let needle := betaNeedle domain authored
  let intermediate := betaEquation arity domain codomain authored (Templates.literal (putTerm (.free needle)))
  let conclusion := betaEquation arity domain codomain authored operand
  let argumentSource := Templates.pair namedOperand (Templates.literal (putTy domain))
  let entries := Templates.pair (Templates.pair argumentSource
    (Templates.literal (putSourceTerm (.var needle.name domain)))) (Templates.literal (.atom 0))
  [⟨intermediate,unaryRequest 4 (betaSourceTemplate arity domain codomain authored checked),[],origin⟩,
   ⟨conclusion,unaryRequest 9 (Templates.pair entries intermediate),[0],origin⟩]

theorem nodes_exact {arity : Nat} (domain codomain : Ty) (authored : DBTerm)
    (checked : authored.inferType (domain::List.replicate arity domain) = some codomain)
    (previous : Fin arity → CanonicalTerm) (typed : ∀ index, (previous index).ty=domain)
    (argument : CanonicalTerm) (argumentType : argument.ty=domain) (origin : Origin)
    (empty : ∀ index, freeNames (previous index).term = [])
    (independent : ∀ index binders, named? (previous index).term binders = some (checkedSource (previous index)).source) :
    (nodes arity domain codomain authored checked).map
      (Mettapedia.Logic.DerivationGraph.Node.map
        (fun template => Indexed.instantiate template (fields previous argument origin))
        (fun template => Indexed.instantiate template (fields previous argument origin))
        (fun template => Indexed.instantiate template (fields previous argument origin))) =
    (betaBlock (betaExpansion domain (body previous authored) codomain
      (checkedBody arity domain codomain authored checked previous typed) argument argumentType) origin).1.map
      (Mettapedia.Logic.DerivationGraph.Node.map (encodeWith theoremCodec) (encodeWith requestCodec) (encodeWith originCodec)) := by
  let nextBody := body previous authored
  let checkedNext := checkedBody arity domain codomain authored checked previous typed
  let expansion := betaExpansion domain nextBody codomain checkedNext argument argumentType
  let needle := betaNeedle domain authored
  have needleSame : betaNeedle domain nextBody = needle := needle_body domain previous empty authored
  have sourceSame : expansion.source=betaSource domain nextBody codomain checkedNext := rfl
  have sourceType : (checkedSource argument).ty=domain := (congrArg CanonicalTerm.ty (checkedSource_exact argument)).trans argumentType
  have intermediate : Indexed.instantiate (betaEquation arity domain codomain authored
      (Templates.literal (putTerm (.free needle)))) (fields previous argument origin) = encodeWith theoremCodec expansion.intermediate := by
    rw [betaIntermediate_exact]
    simpa only [nextBody,dbTermCodec,betaRedex,betaReduced,CanonicalTerm.equalityOfSameType,CanonicalTerm.free,needleSame] using
      betaEquation_exact domain codomain authored checked previous typed argument (CanonicalTerm.free needle) rfl origin
        _ (Templates.literal_exact _ _)
  have conclusion : Indexed.instantiate (betaEquation arity domain codomain authored
      [.inr (rawOperandIndex arity)]) (fields previous argument origin) = encodeWith theoremCodec expansion.conclusion := by
    rw [betaExpansion_conclusion]
    exact betaEquation_exact domain codomain authored checked previous typed argument argument argumentType origin _ (by simp)
  have source := betaSource_exact domain codomain authored checked previous typed argument origin empty independent
  dsimp only [nextBody,checkedNext,expansion,needle] at intermediate conclusion sourceSame
  simp only [nodes,betaBlock,List.map_cons,List.map_nil,Mettapedia.Logic.DerivationGraph.Node.map,
    intermediate,conclusion,betaExpansion_source_exact,source,unaryRequest,Templates.pair_exact,Templates.literal_exact,
    Indexed.instantiate_hole,Indexed.instantiate_nil,List.append_nil,named_operand_field,origin_field]
  simp [betaEntries_exact,needleSame,nextBody,needle,requestCodec,putRequest,putInference,
    Codec.list,Codec.putList,termMapletCodec,checkedSourceCodec,Codec.mapped,Codec.prod,encodeWith,sourceTermCodec,tyCodec,
    sourceType,putSourceTerm,encodeData_pair,List.append_assoc]

end Mettapedia.Languages.HOLLight.ScopedBetaEmission
