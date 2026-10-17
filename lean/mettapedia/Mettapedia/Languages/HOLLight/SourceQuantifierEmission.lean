import Mettapedia.Languages.HOLLight.QuantifierArgumentEmission
import Mettapedia.Languages.HOLLight.ArgumentVectorRendering

/-!
# Source admission, argument rendering and SPEC emission under one clock

The original Pattern and origin are the only supplied dynamic fields. A
scope/metadata gate retains this packet and either refuses or runs the
original renderer, parses its complete canonical term/type storage, computes
the original named operand, and emits the original eighteen-node SPEC block.
Every copy, parse, field delimiter and handoff belongs to the same finite
machine. Refusal emits no decodable certificate and clears auxiliary stacks.

For each fixed typed predicate and incoming theorem, the execution bound is
cubic in the source packet bytes; the coefficient includes the fixed template.
The input domain includes every encoded Pattern, including scope failures.
Admission of arbitrary malformed bytes, compilation of changing predicates,
and the complete translator driver remain distinct obligations. The checker
judgment is relative to the supplied original incoming theorem and policy.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.SourceQuantifierEmission
open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open ArgumentRenderingMachine PrimitiveTransport ProofDataEncoding
open EqualityExpansion.Emission
open ProofExecution (Origin)
open InferenceStorageBounds InferenceHosting GraphExpansion

abbrev rawWire (pattern : Pattern) : List Alphabet := encodeWith dbTermCodec (renderedArgument pattern).term
abbrev firstField := Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.machine false

def rawIdentity : FinTM2 := WordHomomorphismMachine.machine (fun symbol : Alphabet => [symbol])
def stripStatus : FinTM2 := StackMachineComposition.Dispatch.machine rawIdentity
  AdmittedArgumentRendering.accept []
local instance : Fintype (firstField.Γ firstField.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (firstField.Γ firstField.k₁) := inferInstanceAs (Inhabited Alphabet)
def rawMachine : FinTM2 := StackMachineComposition.machine firstField stripStatus (Equiv.refl Alphabet)

theorem term_length_le (value : CanonicalTerm) :
    (encodeWith dbTermCodec value.term).length ≤ (encodeWith canonicalCodec value).length := by
  exact Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.selected_length_le false
    (dbTermCodec.put value.term) (tyCodec.put value.ty)

noncomputable def rawOutputs (value : CanonicalTerm) :
    TM2OutputsInTime rawMachine (encodeWith canonicalCodec value)
      (some (encodeWith dbTermCodec value.term)) (10 * ((encodeWith canonicalCodec value).length + 1)) := by
  have selected := Constructor.Spine.canonicalTermOutputs value
  dsimp only [Constructor.Spine.canonicalTermOutputs,
    Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.selectFirstCodec,
    Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.computable,
    Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.successEncoding] at selected
  simp only [eval_add, eval_mul, eval_C, eval_X] at selected
  change TM2OutputsInTime firstField ((encodeWith canonicalCodec value).map id)
    (some (((1 : Alphabet) :: encodeWith dbTermCodec value.term).map id))
    (4 * (encodeWith canonicalCodec value).length + 3) at selected
  simp only [List.map_id] at selected
  have copied := WordHomomorphismMachine.outputs (fun symbol : Alphabet => [symbol])
    (encodeWith dbTermCodec value.term)
  simp only [List.flatMap_singleton'] at copied
  have stripped := StackMachineComposition.Dispatch.outputs_success rawIdentity
    AdmittedArgumentRendering.accept [] (1 : Alphabet) (encodeWith dbTermCodec value.term)
    (encodeWith dbTermCodec value.term) _ (by decide) copied
  have joined := StackMachineComposition.outputs firstField stripStatus (Equiv.refl Alphabet)
    (encodeWith canonicalCodec value) ((1 : Alphabet) :: encodeWith dbTermCodec value.term)
    (encodeWith dbTermCodec value.term) _ _ selected (by
      change TM2OutputsInTime stripStatus (((1 : Alphabet) :: encodeWith dbTermCodec value.term).map id) _ _
      simpa only [List.map_id, stripStatus] using stripped)
  apply WordEqualityMachine.within joined
  have bounded := term_length_le value
  simp only [List.length_cons]
  omega

local instance : Fintype (Full.machine.Γ Full.machine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (Full.machine.Γ Full.machine.k₁) := inferInstanceAs (Inhabited Alphabet)
def renderMachine : FinTM2 := StackMachineComposition.machine Full.machine rawMachine (Equiv.refl Alphabet)

noncomputable def renderOutputs (pattern : Pattern) (admitted : argumentValidAt 0 pattern = true) :
    TM2OutputsInTime renderMachine (patternWire pattern) (some (rawWire pattern))
      (3000100000 * ((patternWire pattern).length + 1)^3) := by
  have rendered := Classical.choice (Full.outputs pattern admitted)
  have joined := StackMachineComposition.outputs Full.machine rawMachine (Equiv.refl Alphabet)
    (patternWire pattern) (argumentWire pattern) (rawWire pattern) _ _ rendered (by
      change TM2OutputsInTime rawMachine ((argumentWire pattern).map id) _ _
      simpa only [List.map_id, argumentWire, rawWire] using rawOutputs (renderedArgument pattern))
  apply WordEqualityMachine.within joined
  have time := Full.clock_polynomial pattern
  have size := ArgumentVectorRendering.argument_length pattern
  have cube : (patternWire pattern).length + 1 ≤ ((patternWire pattern).length + 1)^3 :=
    le_self_pow (by omega) (by decide)
  change Full.clock pattern + 2 * (argumentWire pattern).length + 2 +
    10 * ((argumentWire pattern).length + 1) ≤ _
  nlinarith

def inputFields (pattern : Pattern) (origin : Origin) : Fin 2 → List Alphabet :=
  ![patternWire pattern, encodeWith originCodec origin]
def inputWire (pattern : Pattern) (origin : Origin) : List (Option Alphabet) :=
  Indexed.argumentWire (inputFields pattern origin)
def selector : Indexed.Template Alphabet 2 := [.inr 0]

local instance : Fintype ((Indexed.machine selector).Γ (Indexed.machine selector).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((Indexed.machine selector).Γ (Indexed.machine selector).k₁) :=
  inferInstanceAs (Inhabited Alphabet)
def selectedMachine : FinTM2 := StackMachineComposition.machine (Indexed.machine selector) renderMachine
  (Equiv.refl Alphabet)
local instance : Fintype (selectedMachine.Γ selectedMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (selectedMachine.Γ selectedMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Inhabited (selectedMachine.Γ selectedMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
def preparedMachine : FinTM2 := RetainedWordExecution.WithOutput.Framed.machine selectedMachine
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)

def preparedFields (pattern : Pattern) (origin : Origin) : Fin 3 → List Alphabet :=
  ![patternWire pattern, encodeWith originCodec origin, rawWire pattern]
def preparedWire (pattern : Pattern) (origin : Origin) : List (Option Alphabet) :=
  Indexed.argumentWire (preparedFields pattern origin)

theorem input_expanded (pattern : Pattern) (origin : Origin) :
    inputWire pattern origin = (patternWire pattern).map some ++ [none] ++
      (encodeWith originCodec origin).map some ++ [none] := by
  simp [inputWire, inputFields, Indexed.argumentWire, Indexed.frame, List.finRange_succ, List.append_assoc]
theorem pattern_length_le (pattern : Pattern) (origin : Origin) :
    (patternWire pattern).length ≤ (inputWire pattern origin).length := by
  rw [input_expanded]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

theorem raw_length (pattern : Pattern) (origin : Origin) :
    (rawWire pattern).length ≤ 7400 * ((inputWire pattern origin).length + 1) := by
  have small := term_length_le (renderedArgument pattern)
  have canonical := ArgumentVectorRendering.argument_length pattern
  have input := pattern_length_le pattern origin
  change (rawWire pattern).length ≤ (argumentWire pattern).length at small
  omega

theorem prepared_exact (pattern : Pattern) (origin : Origin) :
    RetainedWordExecution.WithOutput.Framed.outputWord selectedMachine
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (inputWire pattern origin) (rawWire pattern) =
      preparedWire pattern origin := by
  change (inputWire pattern origin).map id ++ (rawWire pattern).map some ++ [none] = _
  rw [List.map_id, input_expanded]
  simp [preparedWire, preparedFields, Indexed.argumentWire, Indexed.frame,
    List.finRange_succ, List.append_assoc]

theorem prepared_length (pattern : Pattern) (origin : Origin) :
    (preparedWire pattern origin).length ≤ 7401 * ((inputWire pattern origin).length + 1) := by
  rw [← prepared_exact]
  simp only [RetainedWordExecution.WithOutput.Framed.outputWord, List.length_append,
    List.length_map, List.length_cons, List.length_nil]
  have bounded := raw_length pattern origin
  omega

noncomputable def selectedOutputs (pattern : Pattern) (origin : Origin)
    (admitted : argumentValidAt 0 pattern = true) :
    TM2OutputsInTime selectedMachine (inputWire pattern origin) (some (rawWire pattern))
      (3000100020 * ((inputWire pattern origin).length + 1)^3) := by
  have selected := Indexed.outputs selector (inputFields pattern origin)
  simp only [selector, Indexed.instantiate_hole, Indexed.instantiate_nil, List.append_nil,
    inputFields, Matrix.cons_val_zero] at selected
  have rendered := renderOutputs pattern admitted
  have joined := StackMachineComposition.outputs (Indexed.machine selector) renderMachine
    (Equiv.refl Alphabet) (inputWire pattern origin) (patternWire pattern) (rawWire pattern)
    _ _ selected (by
      change TM2OutputsInTime renderMachine ((patternWire pattern).map id) _ _
      simpa only [List.map_id] using rendered)
  apply WordEqualityMachine.within joined
  have bound := pattern_length_le pattern origin
  have cube := Nat.pow_le_pow_left (Nat.add_le_add_right bound 1) 3
  have linear : (inputWire pattern origin).length + 1 ≤ ((inputWire pattern origin).length + 1)^3 :=
    le_self_pow (by omega) (by decide)
  change 4 * (1 + 1) * ((inputWire pattern origin).length + 1) +
    2 * (patternWire pattern).length + 2 + 3000100000 * ((patternWire pattern).length + 1)^3 ≤ _
  nlinarith

noncomputable def preparedOutputs (pattern : Pattern) (origin : Origin)
    (admitted : argumentValidAt 0 pattern = true) :
    TM2OutputsInTime preparedMachine (inputWire pattern origin) (some (preparedWire pattern origin))
      (3000300000 * ((inputWire pattern origin).length + 1)^3) := by
  have saved := RetainedWordExecution.WithOutput.Framed.outputs selectedMachine
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (inputWire pattern origin) (rawWire pattern)
    _ (selectedOutputs pattern origin admitted)
  rw [prepared_exact] at saved
  apply WordEqualityMachine.within saved
  have bound := raw_length pattern origin
  have linear : (inputWire pattern origin).length + 1 ≤ ((inputWire pattern origin).length + 1)^3 :=
    le_self_pow (by omega) (by decide)
  nlinarith


def namingSelector : Indexed.Template Alphabet 3 := [.inr 2]
local instance : Fintype ((Indexed.machine namingSelector).Γ (Indexed.machine namingSelector).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((Indexed.machine namingSelector).Γ (Indexed.machine namingSelector).k₁) :=
  inferInstanceAs (Inhabited Alphabet)
def selectedNamingMachine : FinTM2 := StackMachineComposition.machine (Indexed.machine namingSelector)
  ArgumentNamingMachine.machine (Equiv.refl Alphabet)
local instance : Fintype (selectedNamingMachine.Γ selectedNamingMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (selectedNamingMachine.Γ selectedNamingMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Inhabited (selectedNamingMachine.Γ selectedNamingMachine.k₁) := inferInstanceAs (Inhabited Alphabet)
def namedMachine : FinTM2 := RetainedWordExecution.WithOutput.Framed.machine selectedNamingMachine
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)

def namedFields (pattern : Pattern) (origin : Origin) : Fin 4 → List Alphabet :=
  ![patternWire pattern, encodeWith originCodec origin, rawWire pattern, QuantifierArgumentEmission.namedWire pattern]
def namedWire (pattern : Pattern) (origin : Origin) : List (Option Alphabet) :=
  Indexed.argumentWire (namedFields pattern origin)

theorem raw_prepared_length (pattern : Pattern) (origin : Origin) :
    (rawWire pattern).length ≤ (preparedWire pattern origin).length := by
  rw [← prepared_exact]
  simp only [RetainedWordExecution.WithOutput.Framed.outputWord, List.length_append,
    List.length_map, List.length_cons, List.length_nil]
  omega

theorem named_exact (pattern : Pattern) (origin : Origin) :
    RetainedWordExecution.WithOutput.Framed.outputWord selectedNamingMachine
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (preparedWire pattern origin)
      (QuantifierArgumentEmission.namedWire pattern) = namedWire pattern origin := by
  change (preparedWire pattern origin).map id ++
    (QuantifierArgumentEmission.namedWire pattern).map some ++ [none] = _
  rw [List.map_id]
  simp [preparedWire, preparedFields, namedWire, namedFields, Indexed.argumentWire,
    Indexed.frame, List.finRange_succ, List.append_assoc]

theorem named_length (pattern : Pattern) (origin : Origin) :
    (namedWire pattern origin).length ≤ 2 * (preparedWire pattern origin).length + 1 := by
  rw [← named_exact]
  simp only [RetainedWordExecution.WithOutput.Framed.outputWord, List.length_append,
    List.length_map, List.length_cons, List.length_nil]
  have lengthSame := QuantifierArgumentEmission.named_length pattern
  change (QuantifierArgumentEmission.namedWire pattern).length = (rawWire pattern).length at lengthSame
  have bounded := raw_prepared_length pattern origin
  omega

noncomputable def selectedNamingOutputs (pattern : Pattern) (origin : Origin) :
    TM2OutputsInTime selectedNamingMachine (preparedWire pattern origin)
      (some (QuantifierArgumentEmission.namedWire pattern))
      (14 * ((preparedWire pattern origin).length + 1)) := by
  have selected := Indexed.outputs namingSelector (preparedFields pattern origin)
  simp only [namingSelector, Indexed.instantiate_hole, Indexed.instantiate_nil, List.append_nil,
    preparedFields] at selected
  have named := ArgumentNamingMachine.argumentOutputs pattern
  have joined := StackMachineComposition.outputs (Indexed.machine namingSelector) ArgumentNamingMachine.machine
    (Equiv.refl _) (preparedWire pattern origin) (rawWire pattern)
    (QuantifierArgumentEmission.namedWire pattern) _ _ selected (by
      change TM2OutputsInTime ArgumentNamingMachine.machine ((rawWire pattern).map id)
        (some (QuantifierArgumentEmission.namedWire pattern)) _
      simpa only [List.map_id, QuantifierArgumentEmission.namedWire] using named)
  apply WordEqualityMachine.within joined
  have bound := raw_prepared_length pattern origin
  change 4 * (1 + 1) * ((preparedWire pattern origin).length + 1) +
    2 * (rawWire pattern).length + 2 + (3 * ((rawWire pattern).length + 1) + 1) ≤ _
  omega

noncomputable def namedOutputs (pattern : Pattern) (origin : Origin) :
    TM2OutputsInTime namedMachine (preparedWire pattern origin) (some (namedWire pattern origin))
      (60 * ((preparedWire pattern origin).length + 1)) := by
  have saved := RetainedWordExecution.WithOutput.Framed.outputs selectedNamingMachine
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (preparedWire pattern origin)
    (QuantifierArgumentEmission.namedWire pattern) _ (selectedNamingOutputs pattern origin)
  rw [named_exact] at saved
  apply WordEqualityMachine.within saved
  rw [QuantifierArgumentEmission.named_length]
  have bound := raw_prepared_length pattern origin
  change (encodeWith dbTermCodec (renderedArgument pattern).term).length ≤ _ at bound
  omega

def fieldPermutation : Fin 3 → Indexed.Template Alphabet 4 :=
  ![[.inr 2], [.inr 3], [.inr 1]]
def template (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool) : Indexed.Template Alphabet 4 :=
  Templates.substitute (QuantifierEmission.template input dataType body checked) fieldPermutation

theorem fields_exact (pattern : Pattern) (origin : Origin) :
    (fun index => Indexed.instantiate (fieldPermutation index) (namedFields pattern origin)) =
      betaFields (renderedArgument pattern) origin := by
  funext index
  fin_cases index <;> simp [fieldPermutation, namedFields, betaFields, rawWire, QuantifierArgumentEmission.namedWire,
    Indexed.instantiate_hole, Indexed.instantiate_nil]

theorem emitted_exact (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB dataType (.abs dataType body))
    (pattern : Pattern) (origin : Origin) :
    Indexed.instantiate (template input body checked) (namedFields pattern origin) =
      encodeCertificate (QuantifierEmission.built policy input dataType body checked
        (renderedArgument pattern) (renderedArgument_ty pattern) shape origin) := by
  rw [template, Templates.substitute_exact, fields_exact]
  exact QuantifierEmission.emitted_exact policy input dataType body checked
    (renderedArgument pattern) (renderedArgument_ty pattern) shape origin _
    (QuantifierEmission.built_computed policy input dataType body checked
      (renderedArgument pattern) (renderedArgument_ty pattern) shape origin)

local instance : Fintype (namedMachine.Γ namedMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (namedMachine.Γ namedMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def emissionMachine (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool) : FinTM2 :=
  StackMachineComposition.machine namedMachine (Indexed.machine (template input body checked))
    (Equiv.refl (Option Alphabet))

noncomputable def emissionOutputs (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB dataType (.abs dataType body))
    (pattern : Pattern) (origin : Origin) :
    TM2OutputsInTime (emissionMachine input body checked) (preparedWire pattern origin)
      (some (encodeCertificate (QuantifierEmission.built policy input dataType body checked
        (renderedArgument pattern) (renderedArgument_ty pattern) shape origin)))
      ((8 * ((template input body checked).length + 1) + 64) * ((preparedWire pattern origin).length + 1)) := by
  have prepared := namedOutputs pattern origin
  have emitted := Indexed.outputs (template input body checked) (namedFields pattern origin)
  rw [emitted_exact policy input body checked shape pattern origin] at emitted
  have joined := StackMachineComposition.outputs namedMachine (Indexed.machine (template input body checked))
    (Equiv.refl (Option Alphabet)) (preparedWire pattern origin) (namedWire pattern origin)
    (encodeCertificate (QuantifierEmission.built policy input dataType body checked
      (renderedArgument pattern) (renderedArgument_ty pattern) shape origin)) _ _ prepared (by
        change TM2OutputsInTime (Indexed.machine (template input body checked))
          ((namedWire pattern origin).map id) _ _
        simpa only [List.map_id, namedWire] using emitted)
  apply WordEqualityMachine.within joined
  have size := named_length pattern origin
  change 60 * ((preparedWire pattern origin).length + 1) + 2 * (namedWire pattern origin).length + 2 +
    4 * ((template input body checked).length + 1) * ((namedWire pattern origin).length + 1) ≤ _
  nlinarith

local instance : Fintype (preparedMachine.Γ preparedMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (preparedMachine.Γ preparedMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def successMachine (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool) : FinTM2 :=
  StackMachineComposition.machine preparedMachine (emissionMachine input body checked) (Equiv.refl _)

def coefficient (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool) : Nat :=
  3001000000 + 60000 * ((template input body checked).length + 1)

noncomputable def successOutputs (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB dataType (.abs dataType body))
    (pattern : Pattern) (origin : Origin) (admitted : argumentValidAt 0 pattern = true) :
    TM2OutputsInTime (successMachine input body checked) (inputWire pattern origin)
      (some (encodeCertificate (QuantifierEmission.built policy input dataType body checked
        (renderedArgument pattern) (renderedArgument_ty pattern) shape origin)))
      (coefficient input body checked * ((inputWire pattern origin).length + 1)^3) := by
  have rendered := preparedOutputs pattern origin admitted
  have emitted := emissionOutputs policy input body checked shape pattern origin
  have joined := StackMachineComposition.outputs preparedMachine (emissionMachine input body checked)
    (Equiv.refl (Option Alphabet)) (inputWire pattern origin) (preparedWire pattern origin)
    (encodeCertificate (QuantifierEmission.built policy input dataType body checked
      (renderedArgument pattern) (renderedArgument_ty pattern) shape origin)) _ _ rendered (by
        change TM2OutputsInTime (emissionMachine input body checked)
          ((preparedWire pattern origin).map id) _ _
        simpa only [List.map_id] using emitted)
  apply WordEqualityMachine.within joined
  have size := prepared_length pattern origin
  have linear : (inputWire pattern origin).length + 1 ≤ ((inputWire pattern origin).length + 1)^3 :=
    le_self_pow (by omega) (by decide)
  have scaled := Nat.mul_le_mul_left (8 * ((template input body checked).length + 1) + 66)
    (show (preparedWire pattern origin).length + 1 ≤ 7402 * ((inputWire pattern origin).length + 1) by omega)
  have enlarged := Nat.mul_le_mul_left
    ((8 * ((template input body checked).length + 1) + 66) * 7402) linear
  change 3000300000 * ((inputWire pattern origin).length + 1)^3 +
    2 * (preparedWire pattern origin).length + 2 +
    (8 * ((template input body checked).length + 1) + 64) * ((preparedWire pattern origin).length + 1) ≤ _
  unfold coefficient
  nlinarith


abbrev scopeMachine := Mettapedia.GSLT.LanguageDef.PatternScopeExecution.OriginalAdmission.machine
def selectedScopeMachine : FinTM2 := StackMachineComposition.machine (Indexed.machine selector)
  scopeMachine (Equiv.refl Alphabet)
local instance : Fintype (selectedScopeMachine.Γ selectedScopeMachine.k₁) := inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited (selectedScopeMachine.Γ selectedScopeMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
def savedScopeMachine : FinTM2 := RetainedWordExecution.machine selectedScopeMachine
  AdmittedArgumentRendering.readResult
local instance : Fintype (savedScopeMachine.Γ savedScopeMachine.k₁) :=
  inferInstanceAs (Fintype (Option Alphabet ⊕ Bool))
local instance : Inhabited (savedScopeMachine.Γ savedScopeMachine.k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet ⊕ Bool))

def status (accepted : Bool) : Option Alphabet := some (AdmittedArgumentRendering.status accepted)
def project : Option Alphabet ⊕ Bool → List (Option Alphabet)
  | .inl symbol => [symbol]
  | .inr accepted => [status accepted]
def tagged (pattern : Pattern) (origin : Origin) : List (Option Alphabet ⊕ Bool) :=
  .inr (argumentValidAt 0 pattern) :: (inputWire pattern origin).map Sum.inl

def admissionMachine : FinTM2 := StackMachineComposition.machine savedScopeMachine
  (WordHomomorphismMachine.machine project) (Equiv.refl _)

noncomputable def scopeOutputs (pattern : Pattern) (origin : Origin) :
    TM2OutputsInTime selectedScopeMachine (inputWire pattern origin)
      (some [some (argumentValidAt 0 pattern)])
      (20020 * ((inputWire pattern origin).length + 1)^2) := by
  have selected := Indexed.outputs selector (inputFields pattern origin)
  simp only [selector, Indexed.instantiate_hole, Indexed.instantiate_nil, List.append_nil,
    inputFields, Matrix.cons_val_zero] at selected
  have admissionRun := Mettapedia.GSLT.LanguageDef.PatternScopeExecution.OriginalAdmission.outputs pattern
  have joined := StackMachineComposition.outputs (Indexed.machine selector) scopeMachine (Equiv.refl Alphabet)
    (inputWire pattern origin) (patternWire pattern) [some (argumentValidAt 0 pattern)] _ _ selected (by
      change TM2OutputsInTime scopeMachine ((patternWire pattern).map id) _ _
      simpa only [List.map_id, scopeMachine, patternWire] using admissionRun)
  apply WordEqualityMachine.within joined
  have bound := pattern_length_le pattern origin
  have square := Nat.pow_le_pow_left (Nat.add_le_add_right bound 1) 2
  have linear : (inputWire pattern origin).length + 1 ≤ ((inputWire pattern origin).length + 1)^2 :=
    le_self_pow (by omega) (by decide)
  change 4 * (1+1) * ((inputWire pattern origin).length + 1) + 2 * (patternWire pattern).length + 2 +
    20000 * ((patternWire pattern).length + 1)^2 ≤ _
  nlinarith

noncomputable def savedScopeOutputs (pattern : Pattern) (origin : Origin) :
    TM2OutputsInTime savedScopeMachine (inputWire pattern origin) (some (tagged pattern origin))
      (20030 * ((inputWire pattern origin).length + 1)^2) := by
  have saved := RetainedWordExecution.outputs selectedScopeMachine AdmittedArgumentRendering.readResult
    (inputWire pattern origin) (some (argumentValidAt 0 pattern)) [] _ (scopeOutputs pattern origin)
  change TM2OutputsInTime savedScopeMachine (inputWire pattern origin) (some (tagged pattern origin))
    (20020 * ((inputWire pattern origin).length + 1)^2 + 3 * (inputWire pattern origin).length + 0 + 5) at saved
  apply WordEqualityMachine.within saved
  have linear : (inputWire pattern origin).length + 1 ≤ ((inputWire pattern origin).length + 1)^2 :=
    le_self_pow (by omega) (by decide)
  nlinarith

theorem projected (pattern : Pattern) (origin : Origin) :
    (tagged pattern origin).flatMap project =
      status (argumentValidAt 0 pattern) :: inputWire pattern origin := by
  simp only [tagged, List.flatMap_cons, project, List.singleton_append, List.flatMap_map]
  congr 1
  induction inputWire pattern origin with
  | nil => rfl
  | cons symbol rest ih => simp [ih]

noncomputable def admissionOutputs (pattern : Pattern) (origin : Origin) :
    TM2OutputsInTime admissionMachine (inputWire pattern origin)
      (some (status (argumentValidAt 0 pattern) :: inputWire pattern origin))
      (20050 * ((inputWire pattern origin).length + 1)^2) := by
  have mapped := WordHomomorphismMachine.outputs project (tagged pattern origin)
  rw [projected] at mapped
  have joined := StackMachineComposition.outputs savedScopeMachine
    (WordHomomorphismMachine.machine project) (Equiv.refl _)
    (inputWire pattern origin) (tagged pattern origin)
    (status (argumentValidAt 0 pattern) :: inputWire pattern origin) _ _ (savedScopeOutputs pattern origin) (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine project) ((tagged pattern origin).map id) _ _
      simpa only [List.map_id] using mapped)
  apply WordEqualityMachine.within joined
  simp only [tagged, List.length_cons, List.length_map]
  have linear : (inputWire pattern origin).length + 1 ≤ ((inputWire pattern origin).length + 1)^2 :=
    le_self_pow (by omega) (by decide)
  nlinarith

def accept (symbol : Option Alphabet) : Bool := decide (symbol = some 1)
def guardedMachine (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool) : FinTM2 :=
  StackMachineComposition.Dispatch.machine (successMachine input body checked) accept []
local instance : Fintype (admissionMachine.Γ admissionMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (admissionMachine.Γ admissionMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def machine (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool) : FinTM2 :=
  StackMachineComposition.machine admissionMachine (guardedMachine input body checked) (Equiv.refl _)

def output (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB dataType (.abs dataType body))
    (pattern : Pattern) (origin : Origin) : List Alphabet :=
  if argumentValidAt 0 pattern then
    encodeCertificate (QuantifierEmission.built policy input dataType body checked
      (renderedArgument pattern) (renderedArgument_ty pattern) shape origin)
  else []

noncomputable def guardedOutputs (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB dataType (.abs dataType body))
    (pattern : Pattern) (origin : Origin) :
    TM2OutputsInTime (guardedMachine input body checked)
      (status (argumentValidAt 0 pattern) :: inputWire pattern origin)
      (some (output policy input body checked shape pattern origin))
      (coefficient input body checked * ((inputWire pattern origin).length + 1)^3 +
        (inputWire pattern origin).length + 2) := by
  cases admitted : argumentValidAt 0 pattern with
  | false =>
      have refused := StackMachineComposition.Dispatch.outputs_refused (successMachine input body checked)
        accept [] (status false) (inputWire pattern origin) (by decide)
      have result : TM2OutputsInTime (guardedMachine input body checked)
          (status false :: inputWire pattern origin)
          (some (output policy input body checked shape pattern origin))
          ((inputWire pattern origin).length + 2) := by
        simpa only [output, admitted, Bool.false_eq_true, if_false, guardedMachine] using refused
      exact WordEqualityMachine.within result (by omega)
  | true =>
      have executed := successOutputs policy input body checked shape pattern origin admitted
      have guarded := StackMachineComposition.Dispatch.outputs_success (successMachine input body checked)
        accept [] (status true) (inputWire pattern origin) _ _ (by decide) executed
      have result : TM2OutputsInTime (guardedMachine input body checked)
          (status true :: inputWire pattern origin)
          (some (output policy input body checked shape pattern origin))
          (coefficient input body checked * ((inputWire pattern origin).length + 1)^3 + 1) := by
        simpa only [output, admitted, if_true, guardedMachine] using guarded
      exact WordEqualityMachine.within result (by omega)

/-- Admission, raw rendering, original naming and the complete SPEC block
execute on one physical machine, including the scope/metadata refusal branch. -/
noncomputable def outputs (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB dataType (.abs dataType body))
    (pattern : Pattern) (origin : Origin) :
    TM2OutputsInTime (machine input body checked) (inputWire pattern origin)
      (some (output policy input body checked shape pattern origin))
      ((coefficient input body checked + 30000) * ((inputWire pattern origin).length + 1)^3) := by
  have joined := StackMachineComposition.outputs admissionMachine (guardedMachine input body checked)
    (Equiv.refl (Option Alphabet)) (inputWire pattern origin)
    (status (argumentValidAt 0 pattern) :: inputWire pattern origin)
    (output policy input body checked shape pattern origin) _ _ (admissionOutputs pattern origin) (by
      change TM2OutputsInTime (guardedMachine input body checked)
        ((status (argumentValidAt 0 pattern) :: inputWire pattern origin).map id) _ _
      simpa only [List.map_id] using guardedOutputs policy input body checked shape pattern origin)
  apply WordEqualityMachine.within joined
  have square : ((inputWire pattern origin).length + 1)^2 ≤ ((inputWire pattern origin).length + 1)^3 :=
    Nat.pow_le_pow_right (by omega) (by decide)
  have linear : (inputWire pattern origin).length + 1 ≤ ((inputWire pattern origin).length + 1)^2 :=
    le_self_pow (by omega) (by decide)
  simp only [List.length_cons]
  nlinarith

/-- Uniqueness identifies every terminating run, including source refusal. -/
theorem run_output_eq (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB dataType (.abs dataType body))
    (pattern : Pattern) (origin : Origin) (word : List Alphabet)
    (run : TM2Outputs (machine input body checked) (inputWire pattern origin) (some word)) :
    word = output policy input body checked shape pattern origin :=
  StackMachineComposition.outputs_unique run (outputs policy input body checked shape pattern origin).toTM2Outputs

theorem run_decodes (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB dataType (.abs dataType body))
    (pattern : Pattern) (origin : Origin) (word : List Alphabet)
    (run : TM2Outputs (machine input body checked) (inputWire pattern origin) (some word)) :
    decodeCertificate word = if argumentValidAt 0 pattern then
      some (QuantifierEmission.built policy input dataType body checked
        (renderedArgument pattern) (renderedArgument_ty pattern) shape origin) else none := by
  rw [run_output_eq policy input body checked shape pattern origin word run]
  unfold output
  split
  · exact decodeCertificate_encodeCertificate _
  · rfl

noncomputable def realization (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB dataType (.abs dataType body)) :
    TM2ComputableInPolyTime
      (fun data : Pattern × Origin => inputWire data.1 data.2) id
      (fun data => output policy input body checked shape data.1 data.2) where
  tm := machine input body checked
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Alphabet
  time := C (coefficient input body checked + 30000) * (X + C 1)^3
  outputsFun data := by
    change TM2OutputsInTime (machine input body checked) ((inputWire data.1 data.2).map id)
      (some ((output policy input body checked shape data.1 data.2).map id)) _
    simp only [List.map_id_fun, eval_mul, eval_pow, eval_add, eval_C, eval_X]
    exact outputs policy input body checked shape data.1 data.2

/-- Accepted readout earns source admission and the original relative checker
judgment; every occurrence retains its supplied origin. -/
theorem run_accepted (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB dataType (.abs dataType body))
    (pattern : Pattern) (origin : Origin) (word : List Alphabet) (block : ProofSystem.Certificate)
    (run : TM2Outputs (machine input body checked) (inputWire pattern origin) (some word))
    (decoded : decodeCertificate word = some block) :
    argumentValidAt 0 pattern = true ∧
      BlockChecked policy [input]
        (QuantifierExpansion.specResult input dataType body checked (renderedArgument pattern) (renderedArgument_ty pattern)) block ∧
      block.1.length = 18 ∧ block.1.map (·.origin) = List.replicate 18 origin := by
  have result := run_decodes policy input body checked shape pattern origin word run
  rw [decoded] at result
  cases admitted : argumentValidAt 0 pattern with
  | false => simp only [admitted, Bool.false_eq_true, if_false] at result; contradiction
  | true =>
      simp only [admitted, if_true, Option.some.injEq] at result
      subst block
      refine ⟨rfl, QuantifierEmission.built_checked policy input dataType body checked
        (renderedArgument pattern) (renderedArgument_ty pattern) shape origin, ?_, ?_⟩
      · exact QuantifierExpansion.specTypedBlock?_size policy input dataType body checked
          (renderedArgument pattern) (renderedArgument_ty pattern) shape origin
          (QuantifierEmission.built_computed policy input dataType body checked
            (renderedArgument pattern) (renderedArgument_ty pattern) shape origin)
      · exact QuantifierExpansion.specTypedBlock?_origins policy input dataType body checked
          (renderedArgument pattern) (renderedArgument_ty pattern) shape origin
          (QuantifierEmission.built_computed policy input dataType body checked
            (renderedArgument pattern) (renderedArgument_ty pattern) shape origin)

/-- A source scope failure cannot yield any certificate through this machine. -/
theorem refused_not_decodable (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB dataType (.abs dataType body))
    (pattern : Pattern) (origin : Origin) (word : List Alphabet)
    (refused : argumentValidAt 0 pattern = false)
    (run : TM2Outputs (machine input body checked) (inputWire pattern origin) (some word)) :
    decodeCertificate word = none := by
  simpa only [refused, Bool.false_eq_true, if_false] using
    run_decodes policy input body checked shape pattern origin word run

end Mettapedia.Languages.HOLLight.SourceQuantifierEmission
