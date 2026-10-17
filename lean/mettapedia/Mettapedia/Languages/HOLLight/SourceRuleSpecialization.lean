import Mettapedia.Languages.HOLLight.ScopedRuleSpecialization
import Mettapedia.Languages.HOLLight.SourceQuantifierEmission
import Mettapedia.Languages.HOLLight.ArgumentListRendering
import Mettapedia.GSLT.LanguageDef.CertificateRuleAdmission
import Mettapedia.Computability.FramedFieldSelection

/-!
# Original source arguments execute an authored-row specialization

The runtime packet contains the original Pattern argument list and origin.
Original arity and every source scope judgment are executed before rendering.
The original list renderer, canonical-term field parser, operand namer, ordered
field selectors and authored eighteen-node SPEC descriptor share one clock.
Earlier arguments are retained in de Bruijn order; their reversal is exactly
the original chronological universal-elimination prefix. Source binders remain
opaque data. Refusal drains the packet and emits no certificate.

The row and specialization stage are fixed program parameters. The compiled
payload includes the complete authored descriptor; runtime calculus compilation
and the chronological whole-driver clock are separate obligations. The stated
input domain is the image of the original list and origin codecs.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.SourceRuleSpecialization
open Turing Polynomial
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateDataEncoding
open ArgumentRenderingMachine PrimitiveTransport ProofDataEncoding
open ProofExecution (Origin)
open InferenceHosting

def inputFields (arguments : List Pattern) (origin : Origin) : Fin 2 → List Alphabet :=
  ![ArgumentListRendering.input arguments, encodeWith originCodec origin]
def inputWire (arguments : List Pattern) (origin : Origin) : List (Option Alphabet) :=
  Indexed.argumentWire (inputFields arguments origin)
def sourceSelector : Indexed.Template Alphabet 2 := [.inr 0]

theorem input_expanded (arguments : List Pattern) (origin : Origin) :
    inputWire arguments origin = (ArgumentListRendering.input arguments).map some ++ [none] ++
      (encodeWith originCodec origin).map some ++ [none] := by
  simp [inputWire,inputFields,Indexed.argumentWire,Indexed.frame,List.finRange_succ,List.append_assoc]

theorem source_length_le (arguments : List Pattern) (origin : Origin) :
    (ArgumentListRendering.input arguments).length ≤ (inputWire arguments origin).length := by
  rw [input_expanded]
  simp only [List.length_append,List.length_map,List.length_cons,List.length_nil]
  omega

abbrev scopeProgram := CertificateRuleAdmission.ArgumentScope.machine
def scopeAccepted (symbol : Option Alphabet) : Bool := decide (symbol = some 1)
local instance : Fintype (scopeProgram.Γ scopeProgram.k₁) :=
  inferInstanceAs (Fintype (Option Alphabet ⊕ Bool))
local instance (arity : Nat) : Fintype ((CertificateArgumentFraming.Execution.machine arity).Γ
    (CertificateArgumentFraming.Execution.machine arity).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((CertificateArgumentFraming.Execution.machine arity).Γ
    (CertificateArgumentFraming.Execution.machine arity).k₁) := inferInstanceAs (Inhabited (Option Alphabet))

def scopeDispatch : FinTM2 := StackMachineComposition.Dispatch.machine scopeProgram scopeAccepted [.inr false]
def listAdmissionMachine (arity : Nat) : FinTM2 := StackMachineComposition.machine
  (CertificateArgumentFraming.Execution.machine arity) scopeDispatch (Equiv.refl (Option Alphabet))
local instance : Fintype ((Indexed.machine sourceSelector).Γ (Indexed.machine sourceSelector).k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited ((Indexed.machine sourceSelector).Γ (Indexed.machine sourceSelector).k₁) :=
  inferInstanceAs (Inhabited Alphabet)
def selectedAdmissionMachine (arity : Nat) : FinTM2 := StackMachineComposition.machine
  (Indexed.machine sourceSelector) (listAdmissionMachine arity) (Equiv.refl Alphabet)

def admitted (arity : Nat) (arguments : List Pattern) : Bool :=
  decide (arguments.length = arity) && arguments.all (argumentValidAt 0)
def admissionResult (arity : Nat) (arguments : List Pattern) : List (Option Alphabet ⊕ Bool) :=
  if arguments.length = arity then CertificateRuleAdmission.ArgumentScope.output arguments else [.inr false]
def admissionClock (arity : Nat) (arguments : List Pattern) : Nat :=
  7 * (ArgumentListRendering.input arguments).length + 8 +
    2 * (ArgumentListRendering.middle arity arguments).length + 2 +
    (if arguments.length = arity then
      20020 * ((CertificateRuleAdmission.ArgumentScope.vector arguments).length + 1)^2 + 1 else 2)

attribute [local implicit_reducible] scopeDispatch listAdmissionMachine selectedAdmissionMachine
  CertificateArgumentFraming.Execution.machine
  CertificateRuleAdmission.ArgumentScope.machine FramedWordValidation.retainedMachine
  FramedWordValidation.machine RetainedWordExecution.machine StackMachineComposition.machine
  StackMachineComposition.Dispatch.machine

noncomputable def listAdmissionOutputs (arity : Nat) (arguments : List Pattern) :
    TM2OutputsInTime (listAdmissionMachine arity) (ArgumentListRendering.input arguments)
      (some (admissionResult arity arguments)) (admissionClock arity arguments) := by
  have later : TM2OutputsInTime scopeDispatch (ArgumentListRendering.middle arity arguments)
      (some (admissionResult arity arguments))
      (if arguments.length = arity then
        20020 * ((CertificateRuleAdmission.ArgumentScope.vector arguments).length + 1)^2 + 1 else 2) := by
    by_cases same : arguments.length = arity
    · simpa only [ArgumentListRendering.middle,CertificateArgumentFraming.Execution.frameAtArity,
        if_pos same,CertificateArgumentFraming.statusWire,admissionResult,
        CertificateRuleAdmission.ArgumentScope.vector,scopeDispatch] using
        StackMachineComposition.Dispatch.outputs_success scopeProgram scopeAccepted [.inr false]
          (some (1 : Alphabet)) (CertificateRuleAdmission.ArgumentScope.vector arguments)
          (CertificateRuleAdmission.ArgumentScope.output arguments) _ (by decide)
          (CertificateRuleAdmission.ArgumentScope.outputs arguments)
    · simpa only [ArgumentListRendering.middle,CertificateArgumentFraming.Execution.frameAtArity,
        if_neg same,CertificateArgumentFraming.statusWire,admissionResult,List.length_nil,Nat.zero_add,scopeDispatch] using
        StackMachineComposition.Dispatch.outputs_refused scopeProgram scopeAccepted [.inr false]
          (some (0 : Alphabet)) [] (by decide)
  exact StackMachineComposition.outputs (CertificateArgumentFraming.Execution.machine arity) scopeDispatch
    (Equiv.refl (Option Alphabet)) (ArgumentListRendering.input arguments)
    (ArgumentListRendering.middle arity arguments) (admissionResult arity arguments) _ _
    (CertificateArgumentFraming.Execution.outputsAtArity patternCodec arity arguments)
    (by
      change TM2OutputsInTime scopeDispatch ((ArgumentListRendering.middle arity arguments).map id) _ _
      simpa only [List.map_id] using later)

def selectedAdmissionClock (arity : Nat) (arguments : List Pattern) (origin : Origin) : Nat :=
  8 * ((inputWire arguments origin).length + 1) +
    2 * (ArgumentListRendering.input arguments).length + 2 + admissionClock arity arguments

noncomputable def selectedAdmissionOutputs (arity : Nat) (arguments : List Pattern) (origin : Origin) :
    TM2OutputsInTime (selectedAdmissionMachine arity) (inputWire arguments origin)
      (some (admissionResult arity arguments)) (selectedAdmissionClock arity arguments origin) := by
  have selected := Indexed.outputs sourceSelector (inputFields arguments origin)
  simp only [sourceSelector,Indexed.instantiate_hole,Indexed.instantiate_nil,List.append_nil,
    inputFields,Matrix.cons_val_zero] at selected
  exact StackMachineComposition.outputs (Indexed.machine sourceSelector) (listAdmissionMachine arity)
    (Equiv.refl Alphabet) (inputWire arguments origin) (ArgumentListRendering.input arguments)
    (admissionResult arity arguments) _ _ selected
    (by
      change TM2OutputsInTime (listAdmissionMachine arity) ((ArgumentListRendering.input arguments).map id) _ _
      simpa only [List.map_id] using listAdmissionOutputs arity arguments)

local instance (arity : Nat) : Fintype ((selectedAdmissionMachine arity).Γ
    (selectedAdmissionMachine arity).k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Bool))
local instance (arity : Nat) : Inhabited ((selectedAdmissionMachine arity).Γ
    (selectedAdmissionMachine arity).k₀) := inferInstanceAs (Inhabited (Option Alphabet))
def retainedAdmissionMachine (arity : Nat) : FinTM2 := RetainedWordExecution.machine
  (selectedAdmissionMachine arity) CertificateRuleAdmission.ScopedApplication.readScope
def admissionTail (arity : Nat) (arguments : List Pattern) : List (Option Alphabet ⊕ Bool) :=
  if arguments.length = arity then (CertificateRuleAdmission.ArgumentScope.vector arguments).map Sum.inl else []

theorem admission_result (arity : Nat) (arguments : List Pattern) :
    admissionResult arity arguments = .inr (admitted arity arguments) :: admissionTail arity arguments := by
  by_cases same : arguments.length = arity <;>
    simp [admissionResult,admitted,admissionTail,same,CertificateRuleAdmission.ArgumentScope.output]

def status (accepted : Bool) : Option Alphabet := some (if accepted then 1 else 0)
def project : Option Alphabet ⊕ Bool → List (Option Alphabet)
  | .inl symbol => [symbol]
  | .inr accepted => [status accepted]
local instance (arity : Nat) : Fintype ((retainedAdmissionMachine arity).Γ
    (retainedAdmissionMachine arity).k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Bool))
local instance (arity : Nat) : Inhabited ((retainedAdmissionMachine arity).Γ
    (retainedAdmissionMachine arity).k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Bool))
def admissionMachine (arity : Nat) : FinTM2 := StackMachineComposition.machine
  (retainedAdmissionMachine arity) (WordHomomorphismMachine.machine project) (Equiv.refl _)
def gateClock (arity : Nat) (arguments : List Pattern) (origin : Origin) : Nat :=
  selectedAdmissionClock arity arguments origin + 11 * (inputWire arguments origin).length +
    (admissionTail arity arguments).length + 16

attribute [local implicit_reducible] retainedAdmissionMachine admissionMachine

noncomputable def admissionOutputs (arity : Nat) (arguments : List Pattern) (origin : Origin) :
    TM2OutputsInTime (admissionMachine arity) (inputWire arguments origin)
      (some (status (admitted arity arguments) :: inputWire arguments origin))
      (gateClock arity arguments origin) := by
  have saved := RetainedWordExecution.outputs (selectedAdmissionMachine arity)
    CertificateRuleAdmission.ScopedApplication.readScope (inputWire arguments origin)
    (.inr (admitted arity arguments)) (admissionTail arity arguments) _
    (by rw [← admission_result]; exact selectedAdmissionOutputs arity arguments origin)
  simp only [CertificateRuleAdmission.ScopedApplication.readScope] at saved
  have projected : (.inr (admitted arity arguments) :: (inputWire arguments origin).map Sum.inl).flatMap project =
      status (admitted arity arguments) :: inputWire arguments origin := by
    simp [project,List.flatMap_map]
  have mapped := WordHomomorphismMachine.outputs project
    (.inr (admitted arity arguments) :: (inputWire arguments origin).map Sum.inl)
  rw [projected] at mapped
  have joined := StackMachineComposition.outputs (retainedAdmissionMachine arity)
    (WordHomomorphismMachine.machine project) (Equiv.refl _) (inputWire arguments origin)
    (.inr (admitted arity arguments) :: (inputWire arguments origin).map Sum.inl)
    (status (admitted arity arguments) :: inputWire arguments origin) _ _ saved
    (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine project)
        ((.inr (admitted arity arguments) :: (inputWire arguments origin).map Sum.inl).map id) _ _
      simpa only [List.map_id] using mapped)
  apply WordEqualityMachine.within joined
  simp only [List.length_cons,List.length_map]
  unfold gateClock
  omega

abbrev rawWire := SourceQuantifierEmission.rawWire
abbrev namedWire := QuantifierArgumentEmission.namedWire
def rawVector (arguments : List Pattern) : List (Option Alphabet) :=
  Indexed.frame (arguments.map rawWire)
def namedVector (arguments : List Pattern) : List (Option Alphabet) :=
  Indexed.frame (arguments.map namedWire)

local instance : Fintype (SourceQuantifierEmission.rawMachine.Γ SourceQuantifierEmission.rawMachine.k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (SourceQuantifierEmission.rawMachine.Γ SourceQuantifierEmission.rawMachine.k₀) :=
  inferInstanceAs (Inhabited Alphabet)
local instance : Inhabited (SourceQuantifierEmission.rawMachine.Γ SourceQuantifierEmission.rawMachine.k₁) :=
  inferInstanceAs (Inhabited Alphabet)
def rawVectorMachine : FinTM2 := FramedWordMapping.machine SourceQuantifierEmission.rawMachine
def rawVectorClock (arguments : List Pattern) : Nat := FramedWordMapping.totalClock
  SourceQuantifierEmission.rawMachine (fun pattern => encodeWith canonicalCodec (renderedArgument pattern))
  rawWire (fun pattern => 10 * ((encodeWith canonicalCodec (renderedArgument pattern)).length + 1)) arguments

noncomputable def rawVectorOutputs (arguments : List Pattern) :
    TM2OutputsInTime rawVectorMachine
      (Indexed.frame (arguments.map fun pattern => encodeWith canonicalCodec (renderedArgument pattern)))
      (some (rawVector arguments)) (rawVectorClock arguments) :=
  FramedWordMapping.outputs SourceQuantifierEmission.rawMachine
    (fun pattern => encodeWith canonicalCodec (renderedArgument pattern)) rawWire
    (fun pattern => 10 * ((encodeWith canonicalCodec (renderedArgument pattern)).length + 1))
    (fun pattern => SourceQuantifierEmission.rawOutputs (renderedArgument pattern)) arguments

local instance (arity : Nat) : Fintype ((ArgumentListRendering.machine arity).Γ
    (ArgumentListRendering.machine arity).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((ArgumentListRendering.machine arity).Γ
    (ArgumentListRendering.machine arity).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def renderedRawMachine (arity : Nat) : FinTM2 := StackMachineComposition.machine
  (ArgumentListRendering.machine arity)
  (StackMachineComposition.Dispatch.machine rawVectorMachine scopeAccepted []) (Equiv.refl _)
def selectedRawMachine (arity : Nat) : FinTM2 := StackMachineComposition.machine
  (Indexed.machine sourceSelector) (renderedRawMachine arity) (Equiv.refl Alphabet)
def selectedRawClock (arity : Nat) (arguments : List Pattern) (origin : Origin) : Nat :=
  8 * ((inputWire arguments origin).length + 1) +
    2 * (ArgumentListRendering.input arguments).length + 2 +
    ArgumentListRendering.clock arity arguments +
    2 * (ArgumentListRendering.output arity arguments).length + 2 + rawVectorClock arguments + 1

attribute [local implicit_reducible] rawVectorMachine renderedRawMachine selectedRawMachine
  ArgumentListRendering.machine ArgumentListRendering.dispatched ArgumentListRendering.successMachine
  FramedWordMapping.machine SourceQuantifierEmission.rawMachine SourceQuantifierEmission.stripStatus
  SourceQuantifierEmission.rawIdentity

theorem rendered_vector (arguments : List Pattern) (valid : arguments.all (argumentValidAt 0) = true) :
    ArgumentVectorRendering.output arguments =
      Indexed.frame (arguments.map fun pattern => encodeWith canonicalCodec (renderedArgument pattern)) := by
  unfold ArgumentVectorRendering.output
  congr 1
  apply List.map_congr_left
  intro pattern member
  rw [AdmittedArgumentRendering.output,List.all_eq_true.mp valid pattern member]
  rfl

noncomputable def selectedRawOutputs (arity : Nat) (arguments : List Pattern) (origin : Origin)
    (same : arguments.length = arity) (valid : arguments.all (argumentValidAt 0) = true) :
    TM2OutputsInTime (selectedRawMachine arity) (inputWire arguments origin)
      (some (rawVector arguments)) (selectedRawClock arity arguments origin) := by
  have later := StackMachineComposition.Dispatch.outputs_success rawVectorMachine scopeAccepted []
    (some (1 : Alphabet))
    (Indexed.frame (arguments.map fun pattern => encodeWith canonicalCodec (renderedArgument pattern)))
    (rawVector arguments) _ (by decide) (rawVectorOutputs arguments)
  have intermediate : ArgumentListRendering.output arity arguments =
      some 1 :: Indexed.frame (arguments.map fun pattern => encodeWith canonicalCodec (renderedArgument pattern)) := by
    rw [ArgumentListRendering.output,if_pos same,CertificateArgumentFraming.statusWire,rendered_vector arguments valid]
  rw [← intermediate] at later
  have rendered := StackMachineComposition.outputs (ArgumentListRendering.machine arity)
    (StackMachineComposition.Dispatch.machine rawVectorMachine scopeAccepted []) (Equiv.refl _)
    (ArgumentListRendering.input arguments) (ArgumentListRendering.output arity arguments)
    (rawVector arguments) _ _ (ArgumentListRendering.outputs arity arguments)
    (by
      change TM2OutputsInTime (StackMachineComposition.Dispatch.machine rawVectorMachine scopeAccepted [])
        ((ArgumentListRendering.output arity arguments).map id) _ _
      simpa only [List.map_id] using later)
  have selected := Indexed.outputs sourceSelector (inputFields arguments origin)
  simp only [sourceSelector,Indexed.instantiate_hole,Indexed.instantiate_nil,List.append_nil,
    inputFields,Matrix.cons_val_zero] at selected
  have joined := StackMachineComposition.outputs (Indexed.machine sourceSelector) (renderedRawMachine arity)
    (Equiv.refl Alphabet) (inputWire arguments origin) (ArgumentListRendering.input arguments)
    (rawVector arguments) _ _ selected
    (by
      change TM2OutputsInTime (renderedRawMachine arity) ((ArgumentListRendering.input arguments).map id) _ _
      simpa only [List.map_id,renderedRawMachine] using rendered)
  apply WordEqualityMachine.within joined
  simp only [List.length_cons,List.length_nil]
  unfold selectedRawClock inputWire inputFields
  omega

def collapse : Option Alphabet ⊕ Option Alphabet → List (Option Alphabet) := Sum.elim (fun cell => [cell]) (fun cell => [cell])
theorem collapse_exact (input output : List (Option Alphabet)) :
    (input.map Sum.inl ++ output.map Sum.inr).flatMap collapse = input ++ output := by
  simp [collapse,List.flatMap_map]

local instance (arity : Nat) : Fintype ((selectedRawMachine arity).Γ (selectedRawMachine arity).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((selectedRawMachine arity).Γ (selectedRawMachine arity).k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))
local instance (arity : Nat) : Inhabited ((selectedRawMachine arity).Γ (selectedRawMachine arity).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))
def retainedRawMachine (arity : Nat) : FinTM2 := RetainedWordExecution.WithOutput.machine (selectedRawMachine arity)
local instance (arity : Nat) : Fintype ((retainedRawMachine arity).Γ (retainedRawMachine arity).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet ⊕ Option Alphabet))
local instance (arity : Nat) : Inhabited ((retainedRawMachine arity).Γ (retainedRawMachine arity).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet ⊕ Option Alphabet))
def rawMachine (arity : Nat) : FinTM2 := StackMachineComposition.machine (retainedRawMachine arity)
  (WordHomomorphismMachine.machine collapse) (Equiv.refl _)
def rawPacket (arguments : List Pattern) (origin : Origin) : List (Option Alphabet) :=
  inputWire arguments origin ++ rawVector arguments
def rawClock (arity : Nat) (arguments : List Pattern) (origin : Origin) : Nat :=
  selectedRawClock arity arguments origin + 9 * (inputWire arguments origin).length +
    8 * (rawVector arguments).length + 9

attribute [local implicit_reducible] retainedRawMachine rawMachine RetainedWordExecution.WithOutput.machine

noncomputable def rawOutputs (arity : Nat) (arguments : List Pattern) (origin : Origin)
    (same : arguments.length = arity) (valid : arguments.all (argumentValidAt 0) = true) :
    TM2OutputsInTime (rawMachine arity) (inputWire arguments origin)
      (some (rawPacket arguments origin)) (rawClock arity arguments origin) := by
  have saved := RetainedWordExecution.WithOutput.outputs (selectedRawMachine arity)
    (inputWire arguments origin) (rawVector arguments) _ (selectedRawOutputs arity arguments origin same valid)
  have mapped := WordHomomorphismMachine.outputs collapse
    ((inputWire arguments origin).map (Sum.inl : Option Alphabet → Option Alphabet ⊕ Option Alphabet) ++
      (rawVector arguments).map (Sum.inr : Option Alphabet → Option Alphabet ⊕ Option Alphabet))
  rw [collapse_exact] at mapped
  have joined := StackMachineComposition.outputs (retainedRawMachine arity)
    (WordHomomorphismMachine.machine collapse) (Equiv.refl _)
    (inputWire arguments origin)
    ((inputWire arguments origin).map (Sum.inl : Option Alphabet → Option Alphabet ⊕ Option Alphabet) ++
      (rawVector arguments).map (Sum.inr : Option Alphabet → Option Alphabet ⊕ Option Alphabet))
    (rawPacket arguments origin) _ _ saved
    (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine collapse)
        (((inputWire arguments origin).map Sum.inl ++ (rawVector arguments).map Sum.inr).map id) _ _
      simpa only [List.map_id,rawPacket] using mapped)
  apply WordEqualityMachine.within joined
  unfold rawClock
  simp only [List.length_append,List.length_map]
  omega

theorem frame_append (first second : List (List Alphabet)) :
    Indexed.frame (first ++ second) = Indexed.frame first ++ Indexed.frame second := by
  exact List.flatMap_append

theorem wire_add {first second : Nat} (left : Fin first → List Alphabet) (right : Fin second → List Alphabet) :
    Indexed.argumentWire (Fin.addCases left right) = Indexed.argumentWire left ++ Indexed.argumentWire right := by
  simp only [Indexed.argumentWire,← List.ofFn_eq_map,List.ofFn_add,Fin.addCases_right,frame_append]
  congr 2
  apply congrArg List.ofFn
  funext index
  change Fin.addCases left right (index.castAdd second) = left index
  exact Fin.addCases_left index

def rawFields {arity : Nat} (values : Fin arity → Pattern) (origin : Origin) : Fin (2+arity) → List Alphabet :=
  Fin.addCases (inputFields (List.ofFn values) origin) (fun index => rawWire (values index))

theorem raw_packet_exact {arity : Nat} (values : Fin arity → Pattern) (origin : Origin) :
    rawPacket (List.ofFn values) origin = Indexed.argumentWire (rawFields values origin) := by
  unfold rawFields
  rw [wire_add]
  simp only [rawPacket,inputWire,rawVector,List.map_ofFn]
  congr 1
  simp only [Indexed.argumentWire,← List.ofFn_eq_map]
  rfl

def rawIndices (arity : Nat) : List (Fin (2+arity)) := List.ofFn (fun index : Fin arity => Fin.natAdd 2 index)
local instance : Fintype (ArgumentNamingMachine.machine.Γ ArgumentNamingMachine.machine.k₁) :=
  inferInstanceAs (Fintype Alphabet)
local instance : Inhabited (ArgumentNamingMachine.machine.Γ ArgumentNamingMachine.machine.k₀) :=
  inferInstanceAs (Inhabited Alphabet)
local instance : Inhabited (ArgumentNamingMachine.machine.Γ ArgumentNamingMachine.machine.k₁) :=
  inferInstanceAs (Inhabited Alphabet)
def namedVectorMachine : FinTM2 := FramedWordMapping.machine ArgumentNamingMachine.machine
def namedVectorClock (arguments : List Pattern) : Nat := FramedWordMapping.totalClock
  ArgumentNamingMachine.machine rawWire namedWire (fun pattern => 3 * ((rawWire pattern).length+1)+1) arguments

noncomputable def namedVectorOutputs (arguments : List Pattern) :
    TM2OutputsInTime namedVectorMachine (rawVector arguments)
      (some (namedVector arguments)) (namedVectorClock arguments) :=
  FramedWordMapping.outputs ArgumentNamingMachine.machine rawWire namedWire
    (fun pattern => 3 * ((rawWire pattern).length+1)+1) ArgumentNamingMachine.argumentOutputs arguments

local instance (arity : Nat) : Fintype ((FramedFieldSelection.machine (Γ := Alphabet) (rawIndices arity)).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) (rawIndices arity)).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((FramedFieldSelection.machine (Γ := Alphabet) (rawIndices arity)).Γ
    (FramedFieldSelection.machine (Γ := Alphabet) (rawIndices arity)).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def selectedNamingMachine (arity : Nat) : FinTM2 := StackMachineComposition.machine
  (FramedFieldSelection.machine (Γ := Alphabet) (rawIndices arity)) namedVectorMachine (Equiv.refl _)
def selectedNamingClock (arity : Nat) (arguments : List Pattern) (origin : Origin) : Nat :=
  (8*arity+12)*((rawPacket arguments origin).length+1) +
    2*(rawVector arguments).length+2+namedVectorClock arguments

attribute [local implicit_reducible] namedVectorMachine selectedNamingMachine FramedFieldSelection.machine

theorem raw_selection {arity : Nat} (values : Fin arity → Pattern) (origin : Origin) :
    (rawIndices arity).map (rawFields values origin) = (List.ofFn values).map rawWire := by
  simp only [rawIndices,List.map_ofFn,Function.comp_def,rawFields,Fin.addCases_right]

noncomputable def selectedNamingOutputs {arity : Nat} (values : Fin arity → Pattern) (origin : Origin) :
    TM2OutputsInTime (selectedNamingMachine arity) (rawPacket (List.ofFn values) origin)
      (some (namedVector (List.ofFn values))) (selectedNamingClock arity (List.ofFn values) origin) := by
  have selected := FramedFieldSelection.outputs (rawIndices arity) (rawFields values origin)
  rw [raw_selection,← raw_packet_exact] at selected
  simp only [rawIndices,List.length_ofFn] at selected
  exact StackMachineComposition.outputs (FramedFieldSelection.machine (Γ := Alphabet) (rawIndices arity)) namedVectorMachine
    (Equiv.refl _) (rawPacket (List.ofFn values) origin) (rawVector (List.ofFn values))
    (namedVector (List.ofFn values)) _ _ selected (by
      change TM2OutputsInTime namedVectorMachine ((rawVector (List.ofFn values)).map id) _ _
      simpa only [List.map_id] using namedVectorOutputs (List.ofFn values))

local instance (arity : Nat) : Fintype ((selectedNamingMachine arity).Γ (selectedNamingMachine arity).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((selectedNamingMachine arity).Γ (selectedNamingMachine arity).k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))
local instance (arity : Nat) : Inhabited ((selectedNamingMachine arity).Γ (selectedNamingMachine arity).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))
def retainedNamingMachine (arity : Nat) : FinTM2 := RetainedWordExecution.WithOutput.machine (selectedNamingMachine arity)
local instance (arity : Nat) : Fintype ((retainedNamingMachine arity).Γ (retainedNamingMachine arity).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet ⊕ Option Alphabet))
local instance (arity : Nat) : Inhabited ((retainedNamingMachine arity).Γ (retainedNamingMachine arity).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet ⊕ Option Alphabet))
def namingMachine (arity : Nat) : FinTM2 := StackMachineComposition.machine (retainedNamingMachine arity)
  (WordHomomorphismMachine.machine collapse) (Equiv.refl _)
def preparedPacket (arguments : List Pattern) (origin : Origin) : List (Option Alphabet) :=
  rawPacket arguments origin ++ namedVector arguments
def namingClock (arity : Nat) (arguments : List Pattern) (origin : Origin) : Nat :=
  selectedNamingClock arity arguments origin + 9*(rawPacket arguments origin).length +
    8*(namedVector arguments).length+9

attribute [local implicit_reducible] retainedNamingMachine namingMachine

noncomputable def namingOutputs {arity : Nat} (values : Fin arity → Pattern) (origin : Origin) :
    TM2OutputsInTime (namingMachine arity) (rawPacket (List.ofFn values) origin)
      (some (preparedPacket (List.ofFn values) origin)) (namingClock arity (List.ofFn values) origin) := by
  have saved := RetainedWordExecution.WithOutput.outputs (selectedNamingMachine arity)
    (rawPacket (List.ofFn values) origin) (namedVector (List.ofFn values)) _ (selectedNamingOutputs values origin)
  have mapped := WordHomomorphismMachine.outputs collapse
    ((rawPacket (List.ofFn values) origin).map Sum.inl ++ (namedVector (List.ofFn values)).map Sum.inr)
  rw [collapse_exact] at mapped
  have joined := StackMachineComposition.outputs (retainedNamingMachine arity)
    (WordHomomorphismMachine.machine collapse) (Equiv.refl _)
    (rawPacket (List.ofFn values) origin)
    ((rawPacket (List.ofFn values) origin).map (Sum.inl : Option Alphabet → Option Alphabet ⊕ Option Alphabet) ++
      (namedVector (List.ofFn values)).map (Sum.inr : Option Alphabet → Option Alphabet ⊕ Option Alphabet))
    (preparedPacket (List.ofFn values) origin) _ _ saved (by
      change TM2OutputsInTime (WordHomomorphismMachine.machine collapse)
        (((rawPacket (List.ofFn values) origin).map Sum.inl ++ (namedVector (List.ofFn values)).map Sum.inr).map id) _ _
      simpa only [List.map_id,preparedPacket] using mapped)
  apply WordEqualityMachine.within joined
  unfold namingClock
  simp only [List.length_append,List.length_map]
  omega

local instance (arity : Nat) : Fintype ((rawMachine arity).Γ (rawMachine arity).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((rawMachine arity).Γ (rawMachine arity).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))
def preparedMachine (arity : Nat) : FinTM2 := StackMachineComposition.machine (rawMachine arity)
  (namingMachine arity) (Equiv.refl _)
def preparedClock (arity : Nat) (arguments : List Pattern) (origin : Origin) : Nat :=
  rawClock arity arguments origin + 2*(rawPacket arguments origin).length+2+namingClock arity arguments origin

noncomputable def preparedOutputs {arity : Nat} (values : Fin arity → Pattern) (origin : Origin)
    (valid : (List.ofFn values).all (argumentValidAt 0) = true) :
    TM2OutputsInTime (preparedMachine arity) (inputWire (List.ofFn values) origin)
      (some (preparedPacket (List.ofFn values) origin)) (preparedClock arity (List.ofFn values) origin) :=
  StackMachineComposition.outputs (rawMachine arity) (namingMachine arity) (Equiv.refl _)
    (inputWire (List.ofFn values) origin) (rawPacket (List.ofFn values) origin)
    (preparedPacket (List.ofFn values) origin) _ _
    (rawOutputs arity (List.ofFn values) origin List.length_ofFn valid)
    (by
      change TM2OutputsInTime (namingMachine arity) ((rawPacket (List.ofFn values) origin).map id) _ _
      simpa only [List.map_id] using namingOutputs values origin)

def preparedFields {arity : Nat} (values : Fin arity → Pattern) (origin : Origin) : Fin ((2+arity)+arity) → List Alphabet :=
  Fin.addCases (rawFields values origin) (fun index => namedWire (values index))
theorem prepared_packet_exact {arity : Nat} (values : Fin arity → Pattern) (origin : Origin) :
    preparedPacket (List.ofFn values) origin = Indexed.argumentWire (preparedFields values origin) := by
  unfold preparedFields
  rw [wire_add,← raw_packet_exact]
  simp only [preparedPacket,namedVector,List.map_ofFn]
  congr 1
  simp only [Indexed.argumentWire,← List.ofFn_eq_map]
  rfl

def source (arity : Nat) (arguments : List Pattern) (index : Fin arity) : Pattern :=
  arguments[index.val]?.getD (.apply "" [])
theorem source_ofFn {arity : Nat} (values : Fin arity → Pattern) :
    source arity (List.ofFn values) = values := by
  funext index
  simp [source]
theorem source_reconstruct (arity : Nat) (arguments : List Pattern) (same : arguments.length = arity) :
    List.ofFn (source arity arguments) = arguments := by
  subst arity
  have pointwise : source arguments.length arguments = arguments.get := by
    funext index
    simp [source]
  rw [pointwise,List.ofFn_get]

def previousIndex (arity prior : Nat) (within : prior < arity) (index : Fin prior) : Fin arity :=
  ⟨arity-prior+index.val,by omega⟩
def currentIndex (arity prior : Nat) (within : prior < arity) : Fin arity :=
  ⟨arity-(prior+1),by omega⟩
def previousPatterns (arity prior : Nat) (within : prior < arity) (arguments : List Pattern) : Fin prior → Pattern :=
  fun index => source arity arguments (previousIndex arity prior within index)
def currentPattern (arity prior : Nat) (within : prior < arity) (arguments : List Pattern) : Pattern :=
  source arity arguments (currentIndex arity prior within)
def previous (arity prior : Nat) (within : prior < arity) (arguments : List Pattern) : Fin prior → CanonicalTerm :=
  fun index => renderedArgument (previousPatterns arity prior within arguments index)
def current (arity prior : Nat) (within : prior < arity) (arguments : List Pattern) : CanonicalTerm :=
  renderedArgument (currentPattern arity prior within arguments)

theorem previous_typed (arity prior : Nat) (within : prior < arity) (arguments : List Pattern) (index : Fin prior) :
    (previous arity prior within arguments index).ty = dataType := renderedArgument_ty _
theorem current_typed (arity prior : Nat) (within : prior < arity) (arguments : List Pattern) :
    (current arity prior within arguments).ty = dataType := renderedArgument_ty _
theorem previous_empty (arity prior : Nat) (within : prior < arity) (arguments : List Pattern) (index : Fin prior) :
    freeNames (previous arity prior within arguments index).term = [] := by
  rw [previous,renderedArgument_term]
  exact Named.dataTerm_freeNames _
theorem previous_independent (arity prior : Nat) (within : prior < arity) (arguments : List Pattern)
    (index : Fin prior) (binders : List SourceVar) :
    named? (previous arity prior within arguments index).term binders =
      some (checkedSource (previous arity prior within arguments index)).source := Named.checkedSource_context _ _

/-- Source positions used by earlier eliminations form the original final suffix. -/
theorem previous_suffix (arity prior : Nat) (within : prior < arity) (arguments : List Pattern)
    (same : arguments.length = arity) :
    List.ofFn (previousPatterns arity prior within arguments) = arguments.drop (arity-prior) := by
  apply List.ext_getElem
  · simp only [List.length_ofFn,List.length_drop,same]
    omega
  · intro index first second
    simp only [List.length_ofFn] at first
    simp only [List.getElem_ofFn,previousPatterns,source,previousIndex,List.getElem_drop]
    rw [List.getElem?_eq_getElem (by omega),Option.getD_some]

/-- The reversed earlier tuple is exactly the original chronological prefix. -/
theorem chronological_prefix (arity prior : Nat) (within : prior < arity) (arguments : List Pattern)
    (same : arguments.length = arity) :
    (List.ofFn (previous arity prior within arguments)).reverse =
      (arguments.reverse.take prior).map renderedArgument := by
  have suffix := previous_suffix arity prior within arguments same
  have mapped : List.ofFn (previous arity prior within arguments) =
      (List.ofFn (previousPatterns arity prior within arguments)).map renderedArgument := by
    rw [List.map_ofFn]
    rfl
  rw [mapped,← List.map_reverse,suffix,List.reverse_drop,same]
  congr 2
  omega

def tupleIndex (arity prior : Nat) (within : prior < arity) :
    Fin (ScopedBetaEmission.FieldCount prior) → Fin ((2+arity)+arity) :=
  Fin.addCases (Fin.addCases
    (fun index => (Fin.natAdd 2 (previousIndex arity prior within index)).castAdd arity)
    (fun index => Fin.natAdd (2+arity) (previousIndex arity prior within index)))
    ![(Fin.natAdd 2 (currentIndex arity prior within)).castAdd arity,
      Fin.natAdd (2+arity) (currentIndex arity prior within),
      ((1 : Fin 2).castAdd arity).castAdd arity]
def tupleIndices (arity prior : Nat) (within : prior < arity) : List (Fin ((2+arity)+arity)) :=
  List.ofFn (tupleIndex arity prior within)

/-- Executed rendering and naming earn all earlier/current fields. No coherence
predicate, supplied named operand or changing theorem is a runtime input. -/
theorem tuple_fields {arity : Nat} (values : Fin arity → Pattern) (origin : Origin)
    (prior : Nat) (within : prior < arity) :
    (fun index => preparedFields values origin (tupleIndex arity prior within index)) =
      ScopedBetaEmission.fields (previous arity prior within (List.ofFn values))
        (current arity prior within (List.ofFn values)) origin := by
  funext index
  refine Fin.addCases ?_ ?_ index
  · intro earlier
    refine Fin.addCases ?_ ?_ earlier
    · intro raw
      simp only [tupleIndex,preparedFields,rawFields,ScopedBetaEmission.fields,previous,previousPatterns,
        source_ofFn,Fin.addCases_left,Fin.addCases_right]
    · intro named
      simp only [tupleIndex,preparedFields,ScopedBetaEmission.fields,previous,previousPatterns,source_ofFn,
        QuantifierArgumentEmission.namedWire,Fin.addCases_left,Fin.addCases_right]
  · intro operand
    fin_cases operand <;>
      simp [tupleIndex,preparedFields,rawFields,inputFields,ScopedBetaEmission.fields,current,currentPattern,
        source_ofFn,QuantifierArgumentEmission.namedWire]
    all_goals rfl

theorem tuple_selection {arity : Nat} (values : Fin arity → Pattern) (origin : Origin)
    (prior : Nat) (within : prior < arity) :
    Indexed.frame ((tupleIndices arity prior within).map (preparedFields values origin)) =
      Indexed.argumentWire (ScopedBetaEmission.fields (previous arity prior within (List.ofFn values))
        (current arity prior within (List.ofFn values)) origin) := by
  simp only [tupleIndices,List.map_ofFn,Function.comp_def,tuple_fields]
  simp only [Indexed.argumentWire,← List.ofFn_eq_map]

local instance (arity prior : Nat) (within : prior < arity) : Fintype
    ((FramedFieldSelection.machine (Γ := Alphabet) (tupleIndices arity prior within)).Γ
      (FramedFieldSelection.machine (Γ := Alphabet) (tupleIndices arity prior within)).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (arity prior : Nat) (within : prior < arity) : Inhabited
    ((FramedFieldSelection.machine (Γ := Alphabet) (tupleIndices arity prior within)).Γ
      (FramedFieldSelection.machine (Γ := Alphabet) (tupleIndices arity prior within)).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))
def tupleMachine (arity prior : Nat) (within : prior < arity) : FinTM2 :=
  FramedFieldSelection.machine (Γ := Alphabet) (tupleIndices arity prior within)
def tupleWire (arity prior : Nat) (within : prior < arity) (arguments : List Pattern) (origin : Origin) :
    List (Option Alphabet) :=
  Indexed.argumentWire (ScopedBetaEmission.fields (previous arity prior within arguments)
    (current arity prior within arguments) origin)
def tupleClock (_arity prior : Nat) (arguments : List Pattern) (origin : Origin) : Nat :=
  (8*(ScopedBetaEmission.FieldCount prior)+12)*((preparedPacket arguments origin).length+1)

noncomputable def tupleOutputs {arity : Nat} (values : Fin arity → Pattern) (origin : Origin)
    (prior : Nat) (within : prior < arity) :
    TM2OutputsInTime (tupleMachine arity prior within) (preparedPacket (List.ofFn values) origin)
      (some (tupleWire arity prior within (List.ofFn values) origin)) (tupleClock arity prior (List.ofFn values) origin) := by
  have selected := FramedFieldSelection.outputs (tupleIndices arity prior within) (preparedFields values origin)
  rw [tuple_selection,← prepared_packet_exact] at selected
  simp only [tupleIndices,List.length_ofFn] at selected
  exact selected

def built (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema) (prior : Nat)
    (within : prior < ScopedRuleSpecialization.rowArity rule) (arguments : List Pattern) (origin : Origin) :
    ProofSystem.Certificate :=
  ScopedRuleSpecialization.built policy rule prior within
    (previous (ScopedRuleSpecialization.rowArity rule) prior within arguments)
    (previous_typed _ _ _ _) (current (ScopedRuleSpecialization.rowArity rule) prior within arguments)
    (current_typed _ _ _ _) origin

theorem emitted_original (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema) (prior : Nat)
    (within : prior < ScopedRuleSpecialization.rowArity rule) (arguments : List Pattern) (origin : Origin) :
    Indexed.instantiate (ScopedRuleSpecialization.template rule prior within)
      (ScopedBetaEmission.fields (previous (ScopedRuleSpecialization.rowArity rule) prior within arguments)
        (current (ScopedRuleSpecialization.rowArity rule) prior within arguments) origin) =
      encodeCertificate (built policy rule prior within arguments origin) :=
  ScopedRuleSpecialization.emitted_original policy rule prior within _ (previous_typed _ _ _ _) _
    (current_typed _ _ _ _) origin (previous_empty _ _ _ _) (previous_independent _ _ _ _)

local instance (arity : Nat) : Fintype ((preparedMachine arity).Γ (preparedMachine arity).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((preparedMachine arity).Γ (preparedMachine arity).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))
def sourceTupleMachine (arity prior : Nat) (within : prior < arity) : FinTM2 :=
  StackMachineComposition.machine (preparedMachine arity) (tupleMachine arity prior within) (Equiv.refl _)
def sourceTupleClock (arity prior : Nat) (arguments : List Pattern) (origin : Origin) : Nat :=
  preparedClock arity arguments origin + 2*(preparedPacket arguments origin).length+2+tupleClock arity prior arguments origin

noncomputable def sourceTupleOutputs {arity : Nat} (values : Fin arity → Pattern) (origin : Origin)
    (prior : Nat) (within : prior < arity) (valid : (List.ofFn values).all (argumentValidAt 0) = true) :
    TM2OutputsInTime (sourceTupleMachine arity prior within) (inputWire (List.ofFn values) origin)
      (some (tupleWire arity prior within (List.ofFn values) origin))
      (sourceTupleClock arity prior (List.ofFn values) origin) :=
  StackMachineComposition.outputs (preparedMachine arity) (tupleMachine arity prior within) (Equiv.refl _)
    (inputWire (List.ofFn values) origin) (preparedPacket (List.ofFn values) origin)
    (tupleWire arity prior within (List.ofFn values) origin) _ _ (preparedOutputs values origin valid)
    (by
      change TM2OutputsInTime (tupleMachine arity prior within) ((preparedPacket (List.ofFn values) origin).map id) _ _
      simpa only [List.map_id] using tupleOutputs values origin prior within)

local instance (arity prior : Nat) (within : prior < arity) : Fintype
    ((sourceTupleMachine arity prior within).Γ (sourceTupleMachine arity prior within).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (arity prior : Nat) (within : prior < arity) : Inhabited
    ((sourceTupleMachine arity prior within).Γ (sourceTupleMachine arity prior within).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))
def successMachine (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) : FinTM2 :=
  StackMachineComposition.machine (sourceTupleMachine (ScopedRuleSpecialization.rowArity rule) prior within)
    (Indexed.machine (ScopedRuleSpecialization.template rule prior within)) (Equiv.refl _)

/-- The entire compiled descriptor is charged at its actual template length. -/
def emissionClock (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (arguments : List Pattern) (origin : Origin) : Nat :=
  4*((ScopedRuleSpecialization.template rule prior within).length+1)*
    ((tupleWire (ScopedRuleSpecialization.rowArity rule) prior within arguments origin).length+1)
def successClock (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (arguments : List Pattern) (origin : Origin) : Nat :=
  sourceTupleClock (ScopedRuleSpecialization.rowArity rule) prior arguments origin +
    2*(tupleWire (ScopedRuleSpecialization.rowArity rule) prior within arguments origin).length+2+
    emissionClock rule prior within arguments origin

noncomputable def successOutputs (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema) (prior : Nat)
    (within : prior < ScopedRuleSpecialization.rowArity rule) (arguments : List Pattern) (origin : Origin)
    (same : arguments.length = ScopedRuleSpecialization.rowArity rule)
    (valid : arguments.all (argumentValidAt 0) = true) :
    TM2OutputsInTime (successMachine rule prior within) (inputWire arguments origin)
      (some (encodeCertificate (built policy rule prior within arguments origin)))
      (successClock rule prior within arguments origin) := by
  let values := source (ScopedRuleSpecialization.rowArity rule) arguments
  have reconstructed : List.ofFn values = arguments := source_reconstruct _ _ same
  have prepared := sourceTupleOutputs values origin prior within (by simpa only [reconstructed] using valid)
  rw [reconstructed] at prepared
  have emitted := Indexed.outputs (ScopedRuleSpecialization.template rule prior within)
    (ScopedBetaEmission.fields (previous (ScopedRuleSpecialization.rowArity rule) prior within arguments)
      (current (ScopedRuleSpecialization.rowArity rule) prior within arguments) origin)
  rw [emitted_original policy rule prior within arguments origin] at emitted
  exact StackMachineComposition.outputs (sourceTupleMachine (ScopedRuleSpecialization.rowArity rule) prior within)
    (Indexed.machine (ScopedRuleSpecialization.template rule prior within)) (Equiv.refl _)
    (inputWire arguments origin) (tupleWire (ScopedRuleSpecialization.rowArity rule) prior within arguments origin)
    (encodeCertificate (built policy rule prior within arguments origin)) _ _ prepared (by
      change TM2OutputsInTime (Indexed.machine (ScopedRuleSpecialization.template rule prior within))
        ((tupleWire (ScopedRuleSpecialization.rowArity rule) prior within arguments origin).map id) _ _
      simpa only [List.map_id,tupleWire,emissionClock] using emitted)

def guardedMachine (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) : FinTM2 :=
  StackMachineComposition.Dispatch.machine (successMachine rule prior within) scopeAccepted []
local instance (arity : Nat) : Fintype ((admissionMachine arity).Γ (admissionMachine arity).k₁) :=
  inferInstanceAs (Fintype (Option Alphabet))
local instance (arity : Nat) : Inhabited ((admissionMachine arity).Γ (admissionMachine arity).k₁) :=
  inferInstanceAs (Inhabited (Option Alphabet))
def machine (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) : FinTM2 :=
  StackMachineComposition.machine (admissionMachine (ScopedRuleSpecialization.rowArity rule))
    (guardedMachine rule prior within) (Equiv.refl _)
def output (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema) (prior : Nat)
    (within : prior < ScopedRuleSpecialization.rowArity rule) (arguments : List Pattern) (origin : Origin) : List Alphabet :=
  if admitted (ScopedRuleSpecialization.rowArity rule) arguments then
    encodeCertificate (built policy rule prior within arguments origin) else []
def guardedClock (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (arguments : List Pattern) (origin : Origin) : Nat :=
  if admitted (ScopedRuleSpecialization.rowArity rule) arguments then successClock rule prior within arguments origin+1
    else (inputWire arguments origin).length+2
def clock (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (arguments : List Pattern) (origin : Origin) : Nat :=
  gateClock (ScopedRuleSpecialization.rowArity rule) arguments origin +
    2*(status (admitted (ScopedRuleSpecialization.rowArity rule) arguments) :: inputWire arguments origin).length+2+
    guardedClock rule prior within arguments origin

noncomputable def guardedOutputs (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema) (prior : Nat)
    (within : prior < ScopedRuleSpecialization.rowArity rule) (arguments : List Pattern) (origin : Origin) :
    TM2OutputsInTime (guardedMachine rule prior within)
      (status (admitted (ScopedRuleSpecialization.rowArity rule) arguments) :: inputWire arguments origin)
      (some (output policy rule prior within arguments origin)) (guardedClock rule prior within arguments origin) := by
  cases accepted : admitted (ScopedRuleSpecialization.rowArity rule) arguments with
  | false =>
    simpa only [guardedMachine,output,guardedClock,accepted,Bool.false_eq_true,if_false] using
      StackMachineComposition.Dispatch.outputs_refused (successMachine rule prior within) scopeAccepted []
        (status false) (inputWire arguments origin) (by decide)
  | true =>
    have both : arguments.length = ScopedRuleSpecialization.rowArity rule ∧
        arguments.all (argumentValidAt 0) = true := by
      simpa only [admitted,Bool.and_eq_true,decide_eq_true_eq] using accepted
    simpa only [guardedMachine,output,guardedClock,accepted,if_true] using
      StackMachineComposition.Dispatch.outputs_success (successMachine rule prior within) scopeAccepted []
        (status true) (inputWire arguments origin) _ _ (by decide)
        (successOutputs policy rule prior within arguments origin both.1 both.2)

/-- Every original encoded argument list, including wrong arity and scope
failures, halts through the same source-to-original-SPEC instruction graph. -/
noncomputable def outputs (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema) (prior : Nat)
    (within : prior < ScopedRuleSpecialization.rowArity rule) (arguments : List Pattern) (origin : Origin) :
    TM2OutputsInTime (machine rule prior within) (inputWire arguments origin)
      (some (output policy rule prior within arguments origin)) (clock rule prior within arguments origin) :=
  StackMachineComposition.outputs (admissionMachine (ScopedRuleSpecialization.rowArity rule))
    (guardedMachine rule prior within) (Equiv.refl _)
    (inputWire arguments origin)
    (status (admitted (ScopedRuleSpecialization.rowArity rule) arguments) :: inputWire arguments origin)
    (output policy rule prior within arguments origin) _ _
    (admissionOutputs (ScopedRuleSpecialization.rowArity rule) arguments origin) (by
      change TM2OutputsInTime (guardedMachine rule prior within)
        ((status (admitted (ScopedRuleSpecialization.rowArity rule) arguments) :: inputWire arguments origin).map id) _ _
      simpa only [List.map_id] using guardedOutputs policy rule prior within arguments origin)

theorem run_output_eq (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema) (prior : Nat)
    (within : prior < ScopedRuleSpecialization.rowArity rule) (arguments : List Pattern) (origin : Origin) (word : List Alphabet)
    (run : TM2Outputs (machine rule prior within) (inputWire arguments origin) (some word)) :
    word = output policy rule prior within arguments origin :=
  StackMachineComposition.outputs_unique run (outputs policy rule prior within arguments origin).toTM2Outputs

theorem run_decodes (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema) (prior : Nat)
    (within : prior < ScopedRuleSpecialization.rowArity rule) (arguments : List Pattern) (origin : Origin) (word : List Alphabet)
    (run : TM2Outputs (machine rule prior within) (inputWire arguments origin) (some word)) :
    decodeCertificate word = if admitted (ScopedRuleSpecialization.rowArity rule) arguments then
      some (built policy rule prior within arguments origin) else none := by
  rw [run_output_eq policy rule prior within arguments origin word run]
  unfold output
  split
  · exact decodeCertificate_encodeCertificate _
  · rfl

/-- The original primitive replay supplies authority for the generated block. -/
theorem built_checked (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema) (prior : Nat)
    (within : prior < ScopedRuleSpecialization.rowArity rule) (arguments : List Pattern) (origin : Origin) :
    let earlier := previous (ScopedRuleSpecialization.rowArity rule) prior within arguments
    let operand := current (ScopedRuleSpecialization.rowArity rule) prior within arguments
    let authored := ScopedRuleSpecialization.stageBody rule prior
    let authoredChecked := ScopedRuleSpecialization.stage_checked rule prior within
    let incoming := ScopedSpecEmission.input (InferenceRuleExpansion.ruleTheorem rule) prior dataType
      authored authoredChecked earlier (previous_typed _ _ _ _)
    let result := QuantifierExpansion.specResult incoming dataType (ScopedBetaEmission.body earlier authored)
      (ScopedBetaEmission.checkedBody prior dataType Ty.bool authored authoredChecked earlier (previous_typed _ _ _ _))
      operand (current_typed _ _ _ _)
    GraphExpansion.BlockChecked policy [incoming] result (built policy rule prior within arguments origin) ∧
      (built policy rule prior within arguments origin).1.length = 18 ∧
      (built policy rule prior within arguments origin).1.map (·.origin) = List.replicate 18 origin :=
  ScopedRuleSpecialization.built_checked policy rule prior within _ (previous_typed _ _ _ _) _
    (current_typed _ _ _ _) origin (previous_empty _ _ _ _) (previous_independent _ _ _ _)

theorem wrong_arity_refused (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema) (prior : Nat)
    (within : prior < ScopedRuleSpecialization.rowArity rule) (arguments : List Pattern) (origin : Origin)
    (wrong : arguments.length ≠ ScopedRuleSpecialization.rowArity rule) :
    output policy rule prior within arguments origin = [] := by simp [output,admitted,wrong]
theorem invalid_scope_refused (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema) (prior : Nat)
    (within : prior < ScopedRuleSpecialization.rowArity rule) (arguments : List Pattern) (origin : Origin)
    (invalid : arguments.all (argumentValidAt 0) = false) :
    output policy rule prior within arguments origin = [] := by simp [output,admitted,invalid]

def incoming (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (arguments : List Pattern) : Theorem :=
  ScopedSpecEmission.input (InferenceRuleExpansion.ruleTheorem rule) prior dataType
    (ScopedRuleSpecialization.stageBody rule prior) (ScopedRuleSpecialization.stage_checked rule prior within)
    (previous (ScopedRuleSpecialization.rowArity rule) prior within arguments) (previous_typed _ _ _ _)
def result (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (arguments : List Pattern) : Theorem :=
  QuantifierExpansion.specResult (incoming rule prior within arguments) dataType
    (ScopedBetaEmission.body (previous (ScopedRuleSpecialization.rowArity rule) prior within arguments)
      (ScopedRuleSpecialization.stageBody rule prior))
    (ScopedBetaEmission.checkedBody prior dataType Ty.bool (ScopedRuleSpecialization.stageBody rule prior)
      (ScopedRuleSpecialization.stage_checked rule prior within)
      (previous (ScopedRuleSpecialization.rowArity rule) prior within arguments) (previous_typed _ _ _ _))
    (current (ScopedRuleSpecialization.rowArity rule) prior within arguments) (current_typed _ _ _ _)

theorem original_incoming (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (arguments : List Pattern) (same : arguments.length = ScopedRuleSpecialization.rowArity rule) :
    QuantifierExpansion.instantiateMany? (InferenceRuleExpansion.ruleTheorem rule)
      ((arguments.reverse.take prior).map renderedArgument) = some (incoming rule prior within arguments) := by
  rw [← chronological_prefix _ _ within arguments same]
  exact ScopedRuleSpecialization.original_input rule prior within _ (previous_typed _ _ _ _)

theorem current_chronological (arity prior : Nat) (within : prior < arity) (arguments : List Pattern)
    (same : arguments.length = arity) :
    currentPattern arity prior within arguments = arguments.reverse[prior]'(by simp [same,within]) := by
  simp only [currentPattern,source,currentIndex,List.getElem_reverse,same]
  rw [List.getElem?_eq_getElem (by omega),Option.getD_some]
  congr 1
  omega

/-- The generated root is the next original chronological specialization. -/
theorem original_next (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (arguments : List Pattern) (same : arguments.length = ScopedRuleSpecialization.rowArity rule) :
    QuantifierExpansion.instantiateMany? (InferenceRuleExpansion.ruleTheorem rule)
      ((arguments.reverse.take (prior+1)).map renderedArgument) = some (result rule prior within arguments) := by
  have earlierPrefix := chronological_prefix _ _ within arguments same
  have operand := current_chronological _ _ within arguments same
  have extended : (List.ofFn (previous (ScopedRuleSpecialization.rowArity rule) prior within arguments)).reverse ++
      [current (ScopedRuleSpecialization.rowArity rule) prior within arguments] =
      (arguments.reverse.take (prior+1)).map renderedArgument := by
    rw [List.take_succ_eq_append_getElem (by simp [same,within]),List.map_append,earlierPrefix]
    rw [current,operand]
    rfl
  rw [← extended]
  exact ScopedRuleSpecialization.original_chain_result rule prior within _ (previous_typed _ _ _ _) _ (current_typed _ _ _ _)

theorem run_authorized (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema) (prior : Nat)
    (within : prior < ScopedRuleSpecialization.rowArity rule) (arguments : List Pattern) (origin : Origin) (word : List Alphabet)
    (run : TM2Outputs (machine rule prior within) (inputWire arguments origin) (some word))
    (accepted : admitted (ScopedRuleSpecialization.rowArity rule) arguments = true) :
    ∃ block, decodeCertificate word = some block ∧
      GraphExpansion.BlockChecked policy [incoming rule prior within arguments] (result rule prior within arguments) block ∧
      block.1.length=18 ∧ block.1.map (·.origin)=List.replicate 18 origin := by
  refine ⟨built policy rule prior within arguments origin,?_,?_⟩
  · rw [run_decodes policy rule prior within arguments origin word run,accepted]
    rfl
  · exact built_checked policy rule prior within arguments origin

def canonicalVector (arguments : List Pattern) : List (Option Alphabet) :=
  Indexed.frame (arguments.map fun pattern => encodeWith canonicalCodec (renderedArgument pattern))

theorem canonical_length_bound (arguments : List Pattern) :
    (canonicalVector arguments).length ≤ 7401 * (ArgumentVectorRendering.input arguments).length := by
  induction arguments with
  | nil => simp [canonicalVector,ArgumentVectorRendering.input,Indexed.frame]
  | cons pattern rest ih =>
    have bound := ArgumentVectorRendering.argument_length pattern
    change (encodeWith canonicalCodec (renderedArgument pattern)).length ≤ 7400*((patternWire pattern).length+1) at bound
    simp only [canonicalVector,ArgumentVectorRendering.input,Indexed.frame,List.map_cons,List.flatMap_cons,
      List.length_append,List.length_map,List.length_cons,List.length_nil] at *
    omega

theorem raw_length_le_canonical (arguments : List Pattern) :
    (rawVector arguments).length ≤ (canonicalVector arguments).length := by
  induction arguments with
  | nil => rfl
  | cons pattern rest ih =>
    have bound := SourceQuantifierEmission.term_length_le (renderedArgument pattern)
    change (rawWire pattern).length ≤ (encodeWith canonicalCodec (renderedArgument pattern)).length at bound
    simp only [rawVector,canonicalVector,Indexed.frame,List.map_cons,List.flatMap_cons,
      List.length_append,List.length_map,List.length_cons,List.length_nil] at *
    omega

theorem raw_length_bound (arguments : List Pattern) (origin : Origin) :
    (rawVector arguments).length ≤ 7401*(inputWire arguments origin).length := by
  have first := raw_length_le_canonical arguments
  have second := canonical_length_bound arguments
  have sourceBound := source_length_le arguments origin
  have original := ArgumentListRendering.vector_input_length arguments
  omega

theorem named_vector_length (arguments : List Pattern) : (namedVector arguments).length = (rawVector arguments).length := by
  induction arguments with
  | nil => rfl
  | cons pattern rest ih =>
    have same := QuantifierArgumentEmission.named_length pattern
    change (namedWire pattern).length=(rawWire pattern).length at same
    simp only [namedVector,rawVector,Indexed.frame,List.map_cons,List.flatMap_cons,
      List.length_append,List.length_map,List.length_cons,List.length_nil] at *
    omega

theorem raw_vector_clock_bound (arguments : List Pattern) :
    rawVectorClock arguments ≤ 14*(canonicalVector arguments).length+2 := by
  unfold rawVectorClock
  rw [FramedWordMapping.totalClock_eq]
  have summed : (arguments.map (fun pattern =>
      10*((encodeWith canonicalCodec (renderedArgument pattern)).length+1)+
      2*(encodeWith canonicalCodec (renderedArgument pattern)).length+2*(rawWire pattern).length+4)).sum ≤
      14*(canonicalVector arguments).length := by
    induction arguments with
    | nil => simp [canonicalVector,Indexed.frame]
    | cons pattern rest ih =>
      have bound := SourceQuantifierEmission.term_length_le (renderedArgument pattern)
      change (rawWire pattern).length ≤ (encodeWith canonicalCodec (renderedArgument pattern)).length at bound
      simp only [List.map_cons,List.sum_cons,canonicalVector,Indexed.frame,List.flatMap_cons,
        List.length_append,List.length_map,List.length_cons,List.length_nil] at *
      omega
  omega

theorem named_vector_clock_bound (arguments : List Pattern) :
    namedVectorClock arguments ≤ 8*(rawVector arguments).length+2 := by
  unfold namedVectorClock
  rw [FramedWordMapping.totalClock_eq]
  have summed : (arguments.map (fun pattern => 3*((rawWire pattern).length+1)+1+
      2*(rawWire pattern).length+2*(namedWire pattern).length+4)).sum ≤ 8*(rawVector arguments).length := by
    induction arguments with
    | nil => simp [rawVector,Indexed.frame]
    | cons pattern rest ih =>
      have same := QuantifierArgumentEmission.named_length pattern
      change (namedWire pattern).length=(rawWire pattern).length at same
      simp only [List.map_cons,List.sum_cons,rawVector,Indexed.frame,List.flatMap_cons,
        List.length_append,List.length_map,List.length_cons,List.length_nil] at *
      omega
  omega

theorem raw_packet_length_bound (arguments : List Pattern) (origin : Origin) :
    (rawPacket arguments origin).length ≤ 7402*(inputWire arguments origin).length := by
  have bound := raw_length_bound arguments origin
  simp only [rawPacket,List.length_append]
  omega
theorem prepared_length_bound (arguments : List Pattern) (origin : Origin) :
    (preparedPacket arguments origin).length ≤ 14803*(inputWire arguments origin).length := by
  have first := raw_packet_length_bound arguments origin
  have second := raw_length_bound arguments origin
  simp only [preparedPacket,List.length_append,named_vector_length]
  omega

theorem gate_clock_bound (arity : Nat) (arguments : List Pattern) (origin : Origin) :
    gateClock arity arguments origin ≤ 20100*((inputWire arguments origin).length+1)^2 := by
  have sourceBound := source_length_le arguments origin
  have middleBound := CertificateArgumentFraming.Execution.result_length_le patternCodec arity arguments
  change (ArgumentListRendering.middle arity arguments).length ≤ (ArgumentListRendering.input arguments).length at middleBound
  have vectorBound := ArgumentListRendering.vector_input_length arguments
  change (CertificateRuleAdmission.ArgumentScope.vector arguments).length+2=(ArgumentListRendering.input arguments).length at vectorBound
  have tailBound : (admissionTail arity arguments).length ≤ (ArgumentListRendering.input arguments).length := by
    unfold admissionTail
    split <;> simp only [List.length_map,List.length_nil] <;> omega
  have squares := Nat.pow_le_pow_left (show (CertificateRuleAdmission.ArgumentScope.vector arguments).length+1 ≤
      (inputWire arguments origin).length+1 by omega) 2
  have linear : (inputWire arguments origin).length+1 ≤ ((inputWire arguments origin).length+1)^2 :=
    le_self_pow (by omega) (by decide)
  unfold gateClock selectedAdmissionClock admissionClock
  split <;> nlinarith

theorem raw_clock_bound (arity : Nat) (arguments : List Pattern) (origin : Origin) :
    rawClock arity arguments origin ≤ 3000500000*((inputWire arguments origin).length+1)^3 := by
  have sourceBound := source_length_le arguments origin
  have renderTime := ArgumentListRendering.clock_polynomial arity arguments
  have original := ArgumentListRendering.vector_input_length arguments
  have renderedSize := ArgumentListRendering.vector_output_length arguments
  have canonicalSize := canonical_length_bound arguments
  have rawSize := raw_length_bound arguments origin
  have parseTime := raw_vector_clock_bound arguments
  have outputSize : (ArgumentListRendering.output arity arguments).length ≤
      7401*(ArgumentListRendering.input arguments).length+1 := by
    unfold ArgumentListRendering.output
    split <;> simp only [CertificateArgumentFraming.statusWire,List.length_cons,List.length_nil] <;> omega
  have cubes := Nat.pow_le_pow_left (Nat.add_le_add_right sourceBound 1) 3
  have linear : (inputWire arguments origin).length+1 ≤ ((inputWire arguments origin).length+1)^3 :=
    le_self_pow (by omega) (by decide)
  unfold rawClock selectedRawClock
  nlinarith

theorem naming_clock_bound (arity : Nat) (arguments : List Pattern) (origin : Origin) :
    namingClock arity arguments origin ≤ (60000*arity+310000)*((inputWire arguments origin).length+1) := by
  have packetSize := raw_packet_length_bound arguments origin
  have rawSize := raw_length_bound arguments origin
  have namingTime := named_vector_clock_bound arguments
  have scaled := Nat.mul_le_mul_left (8*arity+21)
    (show (rawPacket arguments origin).length+1 ≤ 7403*((inputWire arguments origin).length+1) by omega)
  unfold namingClock selectedNamingClock
  rw [named_vector_length]
  nlinarith

theorem prepared_clock_bound (arity : Nat) (arguments : List Pattern) (origin : Origin) :
    preparedClock arity arguments origin ≤
      (3000900000+60000*arity)*((inputWire arguments origin).length+1)^3 := by
  have first := raw_clock_bound arity arguments origin
  have second := naming_clock_bound arity arguments origin
  have packet := raw_packet_length_bound arguments origin
  have linear : (inputWire arguments origin).length+1 ≤ ((inputWire arguments origin).length+1)^3 :=
    le_self_pow (by omega) (by decide)
  have namingScaled := Nat.mul_le_mul_left (60000*arity+310000) linear
  unfold preparedClock
  nlinarith

theorem tuple_length_bound (arity prior : Nat) (within : prior < arity) (arguments : List Pattern) (origin : Origin)
    (same : arguments.length = arity) :
    (tupleWire arity prior within arguments origin).length ≤
      2*(ScopedBetaEmission.FieldCount prior)*((preparedPacket arguments origin).length+1) := by
  let values := source arity arguments
  have reconstructed : List.ofFn values=arguments := source_reconstruct _ _ same
  have exactFields := tuple_selection values origin prior within
  have bound := Indexed.instantiateWire_length (FramedFieldSelection.template (Γ := Alphabet) (tupleIndices arity prior within))
    (Indexed.argumentWire (FramedFieldSelection.liftedFields (preparedFields values origin)))
  rw [Indexed.instantiateWire_argumentWire,FramedFieldSelection.template_exact,exactFields,
    FramedFieldSelection.template_length,tupleIndices,List.length_ofFn] at bound
  have lengthSame := FramedFieldSelection.lifted_length (Indexed.argumentWire (preparedFields values origin))
  rw [FramedFieldSelection.lift_exact,← prepared_packet_exact,reconstructed] at lengthSame
  rw [lengthSame,reconstructed] at bound
  exact bound

/-- Fixed coefficients charge authored arity, selection programs and every
symbol of the complete compiled eighteen-node descriptor. -/
def coefficient (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule) : Nat :=
  20106 + (3000900000+60000*ScopedRuleSpecialization.rowArity rule) +
    (8*ScopedBetaEmission.FieldCount prior+14)*14804 +
    (4*((ScopedRuleSpecialization.template rule prior within).length+1)+2)*
      (2*ScopedBetaEmission.FieldCount prior*14804+1)

theorem success_clock_bound (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (arguments : List Pattern) (origin : Origin) (same : arguments.length = ScopedRuleSpecialization.rowArity rule) :
    successClock rule prior within arguments origin ≤
      (coefficient rule prior within-20106)*((inputWire arguments origin).length+1)^3 := by
  have prepTime := prepared_clock_bound (ScopedRuleSpecialization.rowArity rule) arguments origin
  have prepSize := prepared_length_bound arguments origin
  have tupleSize := tuple_length_bound (ScopedRuleSpecialization.rowArity rule) prior within arguments origin same
  let size := (inputWire arguments origin).length+1
  let selection := 8*ScopedBetaEmission.FieldCount prior+14
  let emission := 4*((ScopedRuleSpecialization.template rule prior within).length+1)+2
  have prepared : (preparedPacket arguments origin).length+1 ≤ 14804*size := by dsimp [size]; omega
  have selected := Nat.mul_le_mul_left selection prepared
  have tuple : (tupleWire (ScopedRuleSpecialization.rowArity rule) prior within arguments origin).length+1 ≤
      (2*ScopedBetaEmission.FieldCount prior*14804+1)*size := by
    have scaled := Nat.mul_le_mul_left (2*ScopedBetaEmission.FieldCount prior) prepared
    have positive : 1 ≤ size := by dsimp [size]; omega
    nlinarith
  have emitted := Nat.mul_le_mul_left emission tuple
  have linear : size ≤ size^3 := le_self_pow (by dsimp [size]; omega) (by decide)
  have selectionTime := Nat.mul_le_mul_left (selection*14804) linear
  have emissionTime := Nat.mul_le_mul_left (emission*(2*ScopedBetaEmission.FieldCount prior*14804+1)) linear
  have exactClock : successClock rule prior within arguments origin =
      preparedClock (ScopedRuleSpecialization.rowArity rule) arguments origin +
        selection*((preparedPacket arguments origin).length+1) +
        emission*((tupleWire (ScopedRuleSpecialization.rowArity rule) prior within arguments origin).length+1) := by
    unfold successClock sourceTupleClock emissionClock tupleClock
    dsimp [selection,emission]
    ring
  rw [exactClock]
  have charged : coefficient rule prior within-20106 =
      (3000900000+60000*ScopedRuleSpecialization.rowArity rule)+selection*14804+
        emission*(2*ScopedBetaEmission.FieldCount prior*14804+1) := by
    dsimp [coefficient,selection,emission]
    omega
  rw [charged]
  change _ ≤ _*size^3
  change preparedClock (ScopedRuleSpecialization.rowArity rule) arguments origin ≤
    (3000900000+60000*ScopedRuleSpecialization.rowArity rule)*size^3 at prepTime
  rw [← Nat.mul_assoc] at selected emitted
  have selectedBound := selected.trans selectionTime
  have emittedBound := emitted.trans emissionTime
  exact (Nat.add_le_add (Nat.add_le_add prepTime selectedBound) emittedBound).trans_eq (by ring)

theorem clock_polynomial (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (arguments : List Pattern) (origin : Origin) :
    clock rule prior within arguments origin ≤ coefficient rule prior within*((inputWire arguments origin).length+1)^3 := by
  have gate := gate_clock_bound (ScopedRuleSpecialization.rowArity rule) arguments origin
  let size := (inputWire arguments origin).length+1
  have positive : 1 ≤ size := by dsimp [size]; omega
  have linear : size ≤ size^3 := le_self_pow (by omega) (by decide)
  have square : size^2 ≤ size^3 := Nat.pow_le_pow_right (by omega) (by decide)
  have gateScaled := Nat.mul_le_mul_left 20100 square
  change gateClock (ScopedRuleSpecialization.rowArity rule) arguments origin ≤ 20100*size^2 at gate
  have gateBound := gate.trans gateScaled
  have gap : 20106 ≤ coefficient rule prior within := by unfold coefficient; omega
  cases accepted : admitted (ScopedRuleSpecialization.rowArity rule) arguments with
  | true =>
    have same : arguments.length=ScopedRuleSpecialization.rowArity rule := by
      have both : arguments.length=ScopedRuleSpecialization.rowArity rule ∧
          arguments.all (argumentValidAt 0)=true := by
        simpa only [admitted,Bool.and_eq_true,decide_eq_true_eq] using accepted
      exact both.1
    have success := success_clock_bound rule prior within arguments origin same
    change successClock rule prior within arguments origin ≤ (coefficient rule prior within-20106)*size^3 at success
    unfold clock guardedClock
    simp only [accepted,if_true,List.length_cons]
    change gateClock (ScopedRuleSpecialization.rowArity rule) arguments origin + 2*size+2+
      (successClock rule prior within arguments origin+1) ≤ coefficient rule prior within*size^3
    have restore : coefficient rule prior within-20106+20106=coefficient rule prior within := by omega
    nlinarith
  | false =>
    unfold clock guardedClock
    simp only [accepted,Bool.false_eq_true,if_false,List.length_cons]
    change gateClock (ScopedRuleSpecialization.rowArity rule) arguments origin + 2*size+2+
      (size+1) ≤ coefficient rule prior within*size^3
    nlinarith

noncomputable def realization (policy : AxiomPolicy) [DecidablePred policy] (rule : RuleSchema) (prior : Nat)
    (within : prior < ScopedRuleSpecialization.rowArity rule) :
    TM2ComputableInPolyTime (fun data : List Pattern × Origin => inputWire data.1 data.2)
      (fun data => output policy rule prior within data.1 data.2) (id : List Pattern × Origin → List Pattern × Origin) where
  tm := machine rule prior within
  inputAlphabet := Equiv.refl (Option Alphabet)
  outputAlphabet := Equiv.refl Alphabet
  time := C (coefficient rule prior within)*(X+C 1)^3
  outputsFun data := by
    change TM2OutputsInTime (machine rule prior within) ((inputWire data.1 data.2).map id)
      (some ((output policy rule prior within data.1 data.2).map id)) _
    simp only [List.map_id]
    have executed := outputs policy rule prior within data.1 data.2
    refine ⟨executed.toEvalsTo,?_⟩
    simpa only [eval_mul,eval_pow,eval_add,eval_C,eval_X] using
      executed.steps_le_m.trans (clock_polynomial rule prior within data.1 data.2)

private theorem composition_finite (first second : FinTM2)
    (left : ∀ key, Finite (first.Γ key)) (right : ∀ key, Finite (second.Γ key))
    (key : StackMachineComposition.Key first second) :
    Finite (StackMachineComposition.Alphabet first second key) := by
  cases key with
  | none => exact left _
  | some key => cases key with
    | inl key => exact left key
    | inr key => exact right key
private theorem extra_finite {Key Cell : Type} [Finite Cell] (cells : Key → Type)
    (finite : ∀ key, Finite (cells key)) (key : Option Key) :
    Finite (StackMachineRegisters.withStackAlphabet cells Cell key) := by
  cases key with
  | none => infer_instance
  | some key => exact finite key
private theorem homomorphism_finite {A B : Type} [Fintype A] [Fintype B] [Inhabited B]
    (images : A → List B) (key : (WordHomomorphismMachine.machine images).K) :
    Finite ((WordHomomorphismMachine.machine images).Γ key) := by
  change Finite (WordHomomorphismMachine.Alphabet (A := A) (B := B) key)
  cases key <;> infer_instance
private theorem indexed_finite {A : Type} [Fintype A] [Inhabited A] {arity : Nat}
    (plan : Indexed.Template A arity) (key : (Indexed.machine plan).K) :
    Finite ((Indexed.machine plan).Γ key) := by
  change Finite (Indexed.Alphabet A key)
  cases key <;> infer_instance
private theorem retained_output_finite (program : FinTM2)
    [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)] [Inhabited (program.Γ program.k₁)]
    (finite : ∀ key, Finite (program.Γ key)) (key : (RetainedWordExecution.WithOutput.machine program).K) :
    Finite ((RetainedWordExecution.WithOutput.machine program).Γ key) := by
  let := finite program.k₀
  let := finite program.k₁
  exact extra_finite _ (extra_finite _ (extra_finite _ (extra_finite _ finite))) key
private theorem retained_tag_finite (program : FinTM2) {Tag : Type} [Fintype Tag] [Inhabited Tag]
    [Fintype (program.Γ program.k₁)] [Inhabited (program.Γ program.k₀)] (read : program.Γ program.k₁ → Tag)
    (finite : ∀ key, Finite (program.Γ key)) (key : (RetainedWordExecution.machine program read).K) :
    Finite ((RetainedWordExecution.machine program read).Γ key) := by
  let := finite program.k₀
  exact extra_finite _ (extra_finite _ (extra_finite _ finite)) key

attribute [local implicit_reducible] PatternScopeExecution.OriginalAdmission.machine
  PatternScopeExecution.OriginalAdmission.projectedMachine PatternScopeExecution.VisitorAdapter.machine
  PatternScopeExecution.Binary.machine ArgumentNamingMachine.machine
  CertificateDataTraversal.ProductField.machine
  preparedMachine sourceTupleMachine tupleMachine successMachine guardedMachine machine

private theorem pattern_scope_finite (key : PatternScopeExecution.OriginalAdmission.machine.K) :
    Finite (PatternScopeExecution.OriginalAdmission.machine.Γ key) := by
  apply composition_finite
  · apply composition_finite
    · intro address
      change Finite (PatternScopeExecution.VisitorAdapter.Cells address)
      cases address with
      | none => exact inferInstanceAs (Finite PatternSpanExecution.Event)
      | some address => cases address <;> infer_instance
    · exact homomorphism_finite _
  · intro address
    exact inferInstanceAs (Finite (PatternScopeExecution.Binary.Cells address))

local instance : Fintype (PatternScopeExecution.OriginalAdmission.machine.Γ
    PatternScopeExecution.OriginalAdmission.machine.k₁) := inferInstanceAs (Fintype (Option Bool))
local instance : Inhabited (PatternScopeExecution.OriginalAdmission.machine.Γ
    PatternScopeExecution.OriginalAdmission.machine.k₀) := inferInstanceAs (Inhabited Alphabet)
local instance : Inhabited
    ((FramedWordValidation.machine PatternScopeExecution.OriginalAdmission.machine FramedWordValidation.readBoolean).Γ
      (FramedWordValidation.machine PatternScopeExecution.OriginalAdmission.machine FramedWordValidation.readBoolean).k₀) :=
  inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype
    ((FramedWordValidation.machine PatternScopeExecution.OriginalAdmission.machine FramedWordValidation.readBoolean).Γ
      (FramedWordValidation.machine PatternScopeExecution.OriginalAdmission.machine FramedWordValidation.readBoolean).k₁) :=
  inferInstanceAs (Fintype (Option Bool))
private theorem scope_finite (key : scopeProgram.K) : Finite (scopeProgram.Γ key) := by
  apply retained_tag_finite
  intro address
  let := pattern_scope_finite PatternScopeExecution.OriginalAdmission.machine.k₀
  exact extra_finite _ (extra_finite _ (extra_finite _ pattern_scope_finite)) address
private theorem selected_admission_finite (arity : Nat) (key : (selectedAdmissionMachine arity).K) :
    Finite ((selectedAdmissionMachine arity).Γ key) := by
  apply composition_finite _ _ (indexed_finite sourceSelector)
  apply composition_finite
  · intro address
    exact inferInstanceAs (Finite (CertificateArgumentFraming.Execution.Cells address))
  · exact scope_finite
private theorem admission_finite (arity : Nat) (key : (admissionMachine arity).K) :
    Finite ((admissionMachine arity).Γ key) :=
  composition_finite _ _
    (retained_tag_finite _ _ (selected_admission_finite arity)) (homomorphism_finite project) key

private theorem raw_parser_finite (key : SourceQuantifierEmission.rawMachine.K) :
    Finite (SourceQuantifierEmission.rawMachine.Γ key) := by
  apply composition_finite
  · intro address
    cases address with
    | none => exact inferInstanceAs (Finite Alphabet)
    | some address => cases address <;> exact inferInstanceAs (Finite Alphabet)
  · exact homomorphism_finite (fun symbol : Alphabet => [symbol])
private theorem raw_selected_finite (arity : Nat) (key : (selectedRawMachine arity).K) :
    Finite ((selectedRawMachine arity).Γ key) := by
  apply composition_finite _ _ (indexed_finite sourceSelector)
  apply composition_finite _ _ (ArgumentListRendering.finiteAlphabet arity)
  exact FramedWordMapping.finiteAlphabet _ raw_parser_finite
private theorem raw_finite (arity : Nat) (key : (rawMachine arity).K) : Finite ((rawMachine arity).Γ key) :=
  composition_finite _ _ (retained_output_finite _ (raw_selected_finite arity)) (homomorphism_finite collapse) key
private theorem selector_finite {arity : Nat} (indices : List (Fin arity))
    (key : (FramedFieldSelection.machine (Γ := Alphabet) indices).K) :
    Finite ((FramedFieldSelection.machine (Γ := Alphabet) indices).Γ key) :=
  composition_finite _ _ (homomorphism_finite _) (indexed_finite _) key
private theorem naming_selected_finite (arity : Nat) (key : (selectedNamingMachine arity).K) :
    Finite ((selectedNamingMachine arity).Γ key) := by
  apply composition_finite _ _ (selector_finite (rawIndices arity))
  apply FramedWordMapping.finiteAlphabet
  intro address
  exact inferInstanceAs (Finite Alphabet)
private theorem naming_finite (arity : Nat) (key : (namingMachine arity).K) : Finite ((namingMachine arity).Γ key) :=
  composition_finite _ _ (retained_output_finite _ (naming_selected_finite arity)) (homomorphism_finite collapse) key

/-- Every prepared field and all parser workspaces contain finite symbols;
the original Pattern syntax and represented numbers remain byte streams. -/
theorem prepared_finiteAlphabet (arity : Nat) (key : (preparedMachine arity).K) :
    Finite ((preparedMachine arity).Γ key) :=
  composition_finite _ _ (raw_finite arity) (naming_finite arity) key

/-- The whole source-to-SPEC machine has finite stack alphabets throughout. -/
theorem finiteAlphabet (rule : RuleSchema) (prior : Nat) (within : prior < ScopedRuleSpecialization.rowArity rule)
    (key : (machine rule prior within).K) : Finite ((machine rule prior within).Γ key) := by
  apply composition_finite _ _ (admission_finite _)
  apply composition_finite
  · exact composition_finite _ _ (prepared_finiteAlphabet _) (selector_finite (tupleIndices _ prior within))
  · exact indexed_finite _

end Mettapedia.Languages.HOLLight.SourceRuleSpecialization
