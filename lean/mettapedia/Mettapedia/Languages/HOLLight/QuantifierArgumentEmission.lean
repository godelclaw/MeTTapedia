import Mettapedia.Languages.HOLLight.ArgumentNamingMachine
import Mettapedia.Languages.HOLLight.QuantifierEmission
import Mettapedia.Computability.RetainedWordExecution

/-!
# Executed naming and SPEC emission under one clock

For a fixed original universal theorem and typed predicate, the input contains
only the raw rendered source argument and its origin. The first physical
machine derives the original named argument, retaining the supplied fields;
the second emits the complete original eighteen-node SPEC certificate. The
clock counts both runs, copying, field framing and the intermediate handoff.

The parameter coefficient includes the complete fixed predicate and theorem.
The input is the codec image of an already-rendered source argument: producing
that raw operand, compiling variable predicates and rejecting all malformed
source packets belong to further stages of the whole translator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.QuantifierArgumentEmission
open Turing Polynomial
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.MeTTaIL.Syntax
open ArgumentRenderingMachine PrimitiveTransport ProofDataEncoding
open EqualityExpansion.Emission
open ProofExecution (Origin)

/-- The raw operand and origin are the only supplied dynamic fields. -/
def inputFields (pattern : Pattern) (origin : Origin) : Fin 2 → List Alphabet :=
  ![encodeWith dbTermCodec (renderedArgument pattern).term, encodeWith originCodec origin]
def inputWire (pattern : Pattern) (origin : Origin) : List (Option Alphabet) :=
  Indexed.argumentWire (inputFields pattern origin)
def namedWire (pattern : Pattern) : List Alphabet :=
  encodeWith sourceTermCodec (checkedSource (renderedArgument pattern)).source

def selector : Indexed.Template Alphabet 2 := [.inr 0]
local instance : Fintype ((Indexed.machine selector).Γ (Indexed.machine selector).k₁) :=
  inferInstanceAs (Fintype Alphabet)

local instance : Inhabited ((Indexed.machine selector).Γ (Indexed.machine selector).k₁) :=
  inferInstanceAs (Inhabited Alphabet)

def selectedMachine : FinTM2 := StackMachineComposition.machine (Indexed.machine selector)
  ArgumentNamingMachine.machine (Equiv.refl Alphabet)

local instance : Fintype (selectedMachine.Γ selectedMachine.k₁) := inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (selectedMachine.Γ selectedMachine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Inhabited (selectedMachine.Γ selectedMachine.k₁) := inferInstanceAs (Inhabited Alphabet)

def preparedMachine : FinTM2 := RetainedWordExecution.WithOutput.Framed.machine selectedMachine
  (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)

def preparedFields (pattern : Pattern) (origin : Origin) : Fin 3 → List Alphabet :=
  ![encodeWith dbTermCodec (renderedArgument pattern).term, encodeWith originCodec origin, namedWire pattern]
def preparedWire (pattern : Pattern) (origin : Origin) : List (Option Alphabet) :=
  Indexed.argumentWire (preparedFields pattern origin)

theorem input_expanded (pattern : Pattern) (origin : Origin) :
    inputWire pattern origin = (encodeWith dbTermCodec (renderedArgument pattern).term).map some ++ [none] ++
      (encodeWith originCodec origin).map some ++ [none] := by
  simp [inputWire, inputFields, Indexed.argumentWire, Indexed.frame, List.finRange_succ, List.append_assoc]

theorem raw_length_le (pattern : Pattern) (origin : Origin) :
    (encodeWith dbTermCodec (renderedArgument pattern).term).length ≤ (inputWire pattern origin).length := by
  rw [input_expanded]
  simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
  omega

theorem named_length (pattern : Pattern) :
    (namedWire pattern).length = (encodeWith dbTermCodec (renderedArgument pattern).term).length :=
  ArgumentNamingMachine.wire_length (ArgumentNamingMachine.rendered_shape pattern)

theorem prepared_exact (pattern : Pattern) (origin : Origin) :
    RetainedWordExecution.WithOutput.Framed.outputWord selectedMachine
      (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (inputWire pattern origin) (namedWire pattern) =
      preparedWire pattern origin := by
  change (inputWire pattern origin).map id ++ (namedWire pattern).map some ++ [none] = _
  rw [List.map_id]
  rw [input_expanded]
  simp [preparedWire, preparedFields, Indexed.argumentWire, Indexed.frame,
    List.finRange_succ, List.append_assoc]

theorem prepared_length (pattern : Pattern) (origin : Origin) :
    (preparedWire pattern origin).length ≤ 2 * (inputWire pattern origin).length + 1 := by
  rw [← prepared_exact]
  simp only [RetainedWordExecution.WithOutput.Framed.outputWord, List.length_append,
    List.length_map, List.length_cons, List.length_nil]
  have lengthSame := named_length pattern
  have bounded := raw_length_le pattern origin
  omega

noncomputable def selectedOutputs (pattern : Pattern) (origin : Origin) :
    TM2OutputsInTime selectedMachine (inputWire pattern origin) (some (namedWire pattern))
      (14 * ((inputWire pattern origin).length + 1)) := by
  have selected := Indexed.outputs selector (inputFields pattern origin)
  simp only [selector, Indexed.instantiate_hole, Indexed.instantiate_nil, List.append_nil,
    inputFields, Matrix.cons_val_zero] at selected
  have named := ArgumentNamingMachine.argumentOutputs pattern
  have joined := StackMachineComposition.outputs (Indexed.machine selector) ArgumentNamingMachine.machine
    (Equiv.refl _) (inputWire pattern origin) (encodeWith dbTermCodec (renderedArgument pattern).term)
    (namedWire pattern) _ _ selected (by
      change TM2OutputsInTime ArgumentNamingMachine.machine
        ((encodeWith dbTermCodec (renderedArgument pattern).term).map id) (some (namedWire pattern)) _
      simpa only [List.map_id, namedWire] using named)
  apply WordEqualityMachine.within joined
  have bound := raw_length_le pattern origin
  simp only [selector, List.length_cons, List.length_nil]
  change 4 * (1 + 1) * ((inputWire pattern origin).length + 1) +
    2 * (encodeWith dbTermCodec (renderedArgument pattern).term).length + 2 +
    (3 * ((encodeWith dbTermCodec (renderedArgument pattern).term).length + 1) + 1) ≤ _
  omega

noncomputable def preparedOutputs (pattern : Pattern) (origin : Origin) :
    TM2OutputsInTime preparedMachine (inputWire pattern origin) (some (preparedWire pattern origin))
      (60 * ((inputWire pattern origin).length + 1)) := by
  have saved := RetainedWordExecution.WithOutput.Framed.outputs selectedMachine
    (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet) (inputWire pattern origin) (namedWire pattern)
    _ (selectedOutputs pattern origin)
  rw [prepared_exact] at saved
  apply WordEqualityMachine.within saved
  rw [named_length]
  have bound := raw_length_le pattern origin
  omega


open InferenceStorageBounds InferenceHosting GraphExpansion

/-- The supplied fields are raw operand and origin; the generated third field
is selected as the original emitter's named operand. -/
def fieldPermutation : Fin 3 → Indexed.Template Alphabet 3 :=
  ![[.inr 0], [.inr 2], [.inr 1]]

def template (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool) : Indexed.Template Alphabet 3 :=
  Templates.substitute (QuantifierEmission.template input dataType body checked) fieldPermutation

theorem fields_exact (pattern : Pattern) (origin : Origin) :
    (fun index => Indexed.instantiate (fieldPermutation index) (preparedFields pattern origin)) =
      betaFields (renderedArgument pattern) origin := by
  funext index
  fin_cases index <;> simp [fieldPermutation, preparedFields, betaFields, namedWire,
    Indexed.instantiate_hole, Indexed.instantiate_nil]

theorem emitted_exact (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB dataType (.abs dataType body))
    (pattern : Pattern) (origin : Origin) :
    Indexed.instantiate (template input body checked) (preparedFields pattern origin) =
      encodeCertificate (QuantifierEmission.built policy input dataType body checked
        (renderedArgument pattern) (renderedArgument_ty pattern) shape origin) := by
  rw [template, Templates.substitute_exact, fields_exact]
  exact QuantifierEmission.emitted_exact policy input dataType body checked
    (renderedArgument pattern) (renderedArgument_ty pattern) shape origin _
    (QuantifierEmission.built_computed policy input dataType body checked
      (renderedArgument pattern) (renderedArgument_ty pattern) shape origin)

local instance : Fintype (preparedMachine.Γ preparedMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited (preparedMachine.Γ preparedMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def machine (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool) : FinTM2 :=
  StackMachineComposition.machine preparedMachine (Indexed.machine (template input body checked))
    (Equiv.refl (Option Alphabet))

/-- One finite machine derives the named field, retains the original operand
and origin, and emits the original complete eighteen-node SPEC certificate. -/
noncomputable def outputs (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB dataType (.abs dataType body))
    (pattern : Pattern) (origin : Origin) :
    TM2OutputsInTime (machine input body checked) (inputWire pattern origin)
      (some (encodeCertificate (QuantifierEmission.built policy input dataType body checked
        (renderedArgument pattern) (renderedArgument_ty pattern) shape origin)))
      ((8 * ((template input body checked).length + 1) + 64) * ((inputWire pattern origin).length + 1)) := by
  have prepared := preparedOutputs pattern origin
  have emitted := Indexed.outputs (template input body checked) (preparedFields pattern origin)
  rw [emitted_exact policy input body checked shape pattern origin] at emitted
  have joined := StackMachineComposition.outputs preparedMachine (Indexed.machine (template input body checked))
    (Equiv.refl (Option Alphabet)) (inputWire pattern origin) (preparedWire pattern origin)
    (encodeCertificate (QuantifierEmission.built policy input dataType body checked
      (renderedArgument pattern) (renderedArgument_ty pattern) shape origin)) _ _ prepared (by
        change TM2OutputsInTime (Indexed.machine (template input body checked))
          ((preparedWire pattern origin).map id) _ _
        simpa only [List.map_id, preparedWire] using emitted)
  apply WordEqualityMachine.within joined
  have size := prepared_length pattern origin
  change 60 * ((inputWire pattern origin).length + 1) + 2 * (preparedWire pattern origin).length + 2 +
    4 * ((template input body checked).length + 1) * ((preparedWire pattern origin).length + 1) ≤ _
  nlinarith

/-- Its independent certificate readout is accepted by the original relative
graph checker, preserving every supplied hypothesis, axiom and origin. -/
theorem emitted_checked (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB dataType (.abs dataType body))
    (pattern : Pattern) (origin : Origin) :
    ∃ block, decodeCertificate (Indexed.instantiate (template input body checked) (preparedFields pattern origin)) = some block ∧
      BlockChecked policy [input]
        (QuantifierExpansion.specResult input dataType body checked (renderedArgument pattern) (renderedArgument_ty pattern)) block ∧
      block.1.length = 18 ∧ block.1.map (·.origin) = List.replicate 18 origin := by
  rw [template, Templates.substitute_exact, fields_exact]
  exact QuantifierEmission.emitted_checked policy input dataType body checked
    (renderedArgument pattern) (renderedArgument_ty pattern) shape origin

/-- Every terminating execution on the stated input domain reads back the
same original checked certificate, not merely the chosen witness run. -/
theorem arbitrary_run_checked (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB dataType (.abs dataType body))
    (pattern : Pattern) (origin : Origin) (word : List Alphabet)
    (run : TM2Outputs (machine input body checked) (inputWire pattern origin) (some word)) :
    ∃ block, decodeCertificate word = some block ∧
      BlockChecked policy [input]
        (QuantifierExpansion.specResult input dataType body checked (renderedArgument pattern) (renderedArgument_ty pattern)) block ∧
      block.1.length = 18 ∧ block.1.map (·.origin) = List.replicate 18 origin := by
  have same := StackMachineComposition.outputs_unique run
    (outputs policy input body checked shape pattern origin).toTM2Outputs
  rw [same, ← emitted_exact policy input body checked shape pattern origin]
  exact emitted_checked policy input body checked shape pattern origin

noncomputable def realization (policy : AxiomPolicy) [DecidablePred policy]
    (input : Theorem) (body : DBTerm)
    (checked : body.inferType [dataType] = some Ty.bool)
    (shape : input.sequent.concl.term = DerivedRules.forallAppDB dataType (.abs dataType body)) :
    TM2ComputableInPolyTime
      (fun data : Pattern × Origin => inputWire data.1 data.2) encodeCertificate
      (fun data => QuantifierEmission.built policy input dataType body checked
        (renderedArgument data.1) (renderedArgument_ty data.1) shape data.2) where
  tm := machine input body checked
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Alphabet
  time := C (8 * ((template input body checked).length + 1) + 64) * (X + C 1)
  outputsFun data := by
    change TM2OutputsInTime (machine input body checked) ((inputWire data.1 data.2).map id)
      (some ((encodeCertificate (QuantifierEmission.built policy input dataType body checked
        (renderedArgument data.1) (renderedArgument_ty data.1) shape data.2)).map id)) _
    simp only [List.map_id_fun]
    simpa using outputs policy input body checked shape data.1 data.2

end Mettapedia.Languages.HOLLight.QuantifierArgumentEmission
