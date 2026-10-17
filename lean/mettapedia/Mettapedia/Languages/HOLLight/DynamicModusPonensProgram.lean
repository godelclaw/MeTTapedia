import Mettapedia.Languages.HOLLight.DynamicModusPonensEmission
import Mettapedia.Languages.HOLLight.ClaimCheckingProgram
import Mettapedia.Computability.FramedWordMappingProgram

/-!
# Computed original instructions for changing MP fields

The executable table, initialization and endpoints have checked equality to
those of the original composed physical machine. Computed literals omit
bundled finite-state enumeration arguments. Numeric fuel and snapshot policy
are supplied by the executor; all steps are original machine transitions.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option allowUnsafeReducibility true
namespace Mettapedia.Languages.HOLLight.DynamicModusPonensProgram
open Turing
open Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Languages.HOLLight Mettapedia.Languages.OpenTheory
open DynamicModusPonensEmission

attribute [local reducible] FinTM2.Cfg
 DynamicModusPonensEmission.machine routedMachine supportsMachine theoremFieldsMachine
 retainedUnionMachine selectedUnionMachine unionBody unionStrip retainedAxiomMachine selectedAxiomMachine axiomMachine
 selector
 AuthoredAxiomUnion.machine AuthoredAxiomUnion.preparedMachine AuthoredAxiomUnion.core AuthoredAxiomUnion.scanner
 AuthoredAxiomUnion.assembler AuthoredAxiomUnion.strippedFramer AuthoredAxiomUnion.rawIdentity
 AuthoredListFraming.machine FiniteWordClassifier.Union.machine
 FramedFieldSelection.machine
 StackMachineComposition.machine StackMachineComposition.Dispatch.machine
 StackMachineComposition.liftFirst StackMachineComposition.liftSecond StackMachineComposition.Dispatch.lift
 StackMachineComposition.leftKey StackMachineComposition.rightKey
 RetainedWordExecution.WithOutput.Framed.machine RetainedWordExecution.WithOutput.Framed.taggedMachine
 RetainedWordExecution.WithOutput.Framed.untag
 RetainedWordExecution.WithOutput.machine RetainedWordExecution.WithOutput.statement RetainedWordExecution.WithOutput.body
 FramedWordMapping.machine FramedWordMapping.statement FramedWordMapping.body FramedWordMapping.initial
 WordHomomorphismMachine.machine WordTemplateMachine.machine Indexed.machine Indexed.Alphabet
 SourceQuantifierEmission.stripStatus SourceQuantifierEmission.rawIdentity
 Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.machine
 Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.PrefixField.machine
 Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming.ListAssembly.machine

abbrev target (basis : AuthoredAxiomUnion.Basis) := DynamicModusPonensEmission.machine basis

private theorem composition_exact (first second : FinTM2)
    [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)]
    (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    {firstBody : first.Λ → first.Stmt} {secondBody : second.Λ → second.Stmt}
    (firstSame : firstBody = first.m) (secondSame : secondBody = second.m) :
    StackMachineComposition.Programs.body first.k₁ second.k₀ second.main default bridge firstBody secondBody =
      (StackMachineComposition.machine first second bridge).m := by
  cases firstSame; cases secondSame
  exact StackMachineComposition.body_eq first second bridge

local instance  : Fintype ((projection).Γ (projection).k₁) := inferInstanceAs (Fintype Alphabet)
local instance  : Inhabited ((projection).Γ (projection).k₁) := inferInstanceAs (Inhabited Alphabet)
def axiomInstructions  : (axiomMachine).Λ → (axiomMachine).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (projection).k₁ (SourceQuantifierEmission.stripStatus).k₀ (SourceQuantifierEmission.stripStatus).main (default : Alphabet) id
    (ClaimCheckingProgram.firstFieldBody) (ClaimCheckingProgram.stripBody))
theorem axiomInstructions_exact  : axiomInstructions  = (axiomMachine).m :=
  composition_exact (projection) (SourceQuantifierEmission.stripStatus) (Equiv.refl Alphabet) (ClaimCheckingProgram.firstFieldBody_exact) (ClaimCheckingProgram.stripBody_exact)

local instance {arity : Nat} (index : Fin arity) : Fintype ((Indexed.machine (selector index)).Γ (Indexed.machine (selector index)).k₁) := inferInstanceAs (Fintype Alphabet)
local instance {arity : Nat} (index : Fin arity) : Inhabited ((Indexed.machine (selector index)).Γ (Indexed.machine (selector index)).k₁) := inferInstanceAs (Inhabited Alphabet)
def selectedAxiomInstructions {arity : Nat} (index : Fin arity) : (selectedAxiomMachine index).Λ → (selectedAxiomMachine index).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (Indexed.machine (selector index)).k₁ (axiomMachine).k₀ (axiomMachine).main (default : Alphabet) id
    (Indexed.program (selector index)) (axiomInstructions))
theorem selectedAxiomInstructions_exact {arity : Nat} (index : Fin arity) : selectedAxiomInstructions index = (selectedAxiomMachine index).m :=
  composition_exact (Indexed.machine (selector index)) (axiomMachine) (Equiv.refl Alphabet) (rfl) (axiomInstructions_exact)

def retainedAxiomInstructionsInner {arity : Nat} (index : Fin arity) : (RetainedWordExecution.WithOutput.machine (selectedAxiomMachine index)).Λ → (RetainedWordExecution.WithOutput.machine (selectedAxiomMachine index)).Stmt := by
  claim_program_literal_endpoints (RetainedWordExecution.WithOutput.Programs.statement
    (selectedAxiomMachine index).k₀ (selectedAxiomMachine index).k₁ (none : Option Alphabet) (0 : Alphabet)
    (selectedAxiomMachine index).initialState (selectedAxiomMachine index).main (selectedAxiomInstructions index))
theorem retainedAxiomInstructionsInner_exact {arity : Nat} (index : Fin arity) : retainedAxiomInstructionsInner index = (RetainedWordExecution.WithOutput.machine (selectedAxiomMachine index)).m := by
  unfold retainedAxiomInstructionsInner
  rw [selectedAxiomInstructions_exact index]
  rfl

local instance {arity : Nat} (index : Fin arity) : Fintype ((RetainedWordExecution.WithOutput.machine (selectedAxiomMachine index)).Γ (RetainedWordExecution.WithOutput.machine (selectedAxiomMachine index)).k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Alphabet))
local instance {arity : Nat} (index : Fin arity) : Inhabited ((RetainedWordExecution.WithOutput.machine (selectedAxiomMachine index)).Γ (RetainedWordExecution.WithOutput.machine (selectedAxiomMachine index)).k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Alphabet))
def retainedAxiomInstructionsTagged {arity : Nat} (index : Fin arity) : (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedAxiomMachine index) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Λ → (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedAxiomMachine index) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (RetainedWordExecution.WithOutput.machine (selectedAxiomMachine index)).k₁ (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (selectedAxiomMachine index) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).k₀ (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (selectedAxiomMachine index) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).main (default : (Option Alphabet ⊕ Alphabet)) id
    (retainedAxiomInstructionsInner index) (WordHomomorphismMachine.program (RetainedWordExecution.WithOutput.Framed.untag (selectedAxiomMachine index) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))))
theorem retainedAxiomInstructionsTagged_exact {arity : Nat} (index : Fin arity) : retainedAxiomInstructionsTagged index = (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedAxiomMachine index) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).m :=
  composition_exact (RetainedWordExecution.WithOutput.machine (selectedAxiomMachine index)) (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (selectedAxiomMachine index) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))) (Equiv.refl (Option Alphabet ⊕ Alphabet)) (retainedAxiomInstructionsInner_exact index) (rfl)

local instance {arity : Nat} (index : Fin arity) : Fintype ((RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedAxiomMachine index) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Γ (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedAxiomMachine index) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance {arity : Nat} (index : Fin arity) : Inhabited ((RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedAxiomMachine index) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Γ (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedAxiomMachine index) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def retainedAxiomInstructions {arity : Nat} (index : Fin arity) : (retainedAxiomMachine index).Λ → (retainedAxiomMachine index).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedAxiomMachine index) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).k₀ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).main (default : (Option Alphabet)) id
    (retainedAxiomInstructionsTagged index) (WordTemplateMachine.program (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))))
theorem retainedAxiomInstructions_exact {arity : Nat} (index : Fin arity) : retainedAxiomInstructions index = (retainedAxiomMachine index).m :=
  composition_exact (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedAxiomMachine index) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)) (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))) (Equiv.refl (Option Alphabet)) (retainedAxiomInstructionsTagged_exact index) (rfl)

def strippedFramerInstructionsTable  : { body : (AuthoredAxiomUnion.strippedFramer).Λ → (AuthoredAxiomUnion.strippedFramer).Stmt // body = (AuthoredAxiomUnion.strippedFramer).m } := by
  extract_rule_program (AuthoredAxiomUnion.strippedFramer).m
def strippedFramerInstructions  := (strippedFramerInstructionsTable ).val
theorem strippedFramerInstructions_exact  : strippedFramerInstructions  = (AuthoredAxiomUnion.strippedFramer).m := (strippedFramerInstructionsTable ).property

local instance (basis : AuthoredAxiomUnion.Basis) : Fintype ((AuthoredListFraming.machine (AuthoredAxiomUnion.dictionary basis)).Γ (AuthoredListFraming.machine (AuthoredAxiomUnion.dictionary basis)).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (basis : AuthoredAxiomUnion.Basis) : Inhabited ((AuthoredListFraming.machine (AuthoredAxiomUnion.dictionary basis)).Γ (AuthoredListFraming.machine (AuthoredAxiomUnion.dictionary basis)).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def scannerInstructions (basis : AuthoredAxiomUnion.Basis) : (AuthoredAxiomUnion.scanner basis).Λ → (AuthoredAxiomUnion.scanner basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (AuthoredListFraming.machine (AuthoredAxiomUnion.dictionary basis)).k₁ (AuthoredAxiomUnion.strippedFramer).k₀ (AuthoredAxiomUnion.strippedFramer).main (default : (Option Alphabet)) id
    (AuthoredListFraming.program (AuthoredAxiomUnion.dictionary basis)) (strippedFramerInstructions))
theorem scannerInstructions_exact (basis : AuthoredAxiomUnion.Basis) : scannerInstructions basis = (AuthoredAxiomUnion.scanner basis).m :=
  composition_exact (AuthoredListFraming.machine (AuthoredAxiomUnion.dictionary basis)) (AuthoredAxiomUnion.strippedFramer) (Equiv.refl (Option Alphabet)) (rfl) (strippedFramerInstructions_exact)

def mappedScannerInstructions (basis : AuthoredAxiomUnion.Basis) : (FramedWordMapping.machine (AuthoredAxiomUnion.scanner basis)).Λ → (FramedWordMapping.machine (AuthoredAxiomUnion.scanner basis)).Stmt := by
  claim_program_literal_endpoints (FramedWordMapping.Programs.body
    (AuthoredAxiomUnion.scanner basis).k₀ (AuthoredAxiomUnion.scanner basis).k₁
    (AuthoredAxiomUnion.scanner basis).initialState (AuthoredAxiomUnion.scanner basis).main
    (0 : Alphabet) (none : Option Alphabet) (scannerInstructions basis))
theorem mappedScannerInstructions_exact (basis : AuthoredAxiomUnion.Basis) : mappedScannerInstructions basis = (FramedWordMapping.machine (AuthoredAxiomUnion.scanner basis)).m := by
  unfold mappedScannerInstructions
  rw [scannerInstructions_exact]
  exact FramedWordMapping.Programs.body_eq _

local instance (basis : AuthoredAxiomUnion.Basis) : Fintype ((FramedWordMapping.machine (AuthoredAxiomUnion.scanner basis)).Γ (FramedWordMapping.machine (AuthoredAxiomUnion.scanner basis)).k₁) := inferInstanceAs (Fintype (Option (Option Alphabet)))
local instance (basis : AuthoredAxiomUnion.Basis) : Inhabited ((FramedWordMapping.machine (AuthoredAxiomUnion.scanner basis)).Γ (FramedWordMapping.machine (AuthoredAxiomUnion.scanner basis)).k₁) := inferInstanceAs (Inhabited (Option (Option Alphabet)))
def preparedInstructions (basis : AuthoredAxiomUnion.Basis) : (AuthoredAxiomUnion.preparedMachine basis).Λ → (AuthoredAxiomUnion.preparedMachine basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (FramedWordMapping.machine (AuthoredAxiomUnion.scanner basis)).k₁ (WordHomomorphismMachine.machine AuthoredAxiomUnion.flatten).k₀ (WordHomomorphismMachine.machine AuthoredAxiomUnion.flatten).main (default : (Option (Option Alphabet))) id
    (mappedScannerInstructions basis) (WordHomomorphismMachine.program AuthoredAxiomUnion.flatten))
theorem preparedInstructions_exact (basis : AuthoredAxiomUnion.Basis) : preparedInstructions basis = (AuthoredAxiomUnion.preparedMachine basis).m :=
  composition_exact (FramedWordMapping.machine (AuthoredAxiomUnion.scanner basis)) (WordHomomorphismMachine.machine AuthoredAxiomUnion.flatten) (Equiv.refl (Option (Option Alphabet))) (mappedScannerInstructions_exact basis) (rfl)

def assemblerInstructionsTable  : { body : (AuthoredAxiomUnion.assembler).Λ → (AuthoredAxiomUnion.assembler).Stmt // body = (AuthoredAxiomUnion.assembler).m } := by
  extract_rule_program (AuthoredAxiomUnion.assembler).m
def assemblerInstructions  := (assemblerInstructionsTable ).val
theorem assemblerInstructions_exact  : assemblerInstructions  = (AuthoredAxiomUnion.assembler).m := (assemblerInstructionsTable ).property

local instance (basis : AuthoredAxiomUnion.Basis) : Fintype ((FiniteWordClassifier.Union.machine (AuthoredAxiomUnion.words basis) (0 : Alphabet) 1).Γ (FiniteWordClassifier.Union.machine (AuthoredAxiomUnion.words basis) (0 : Alphabet) 1).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (basis : AuthoredAxiomUnion.Basis) : Inhabited ((FiniteWordClassifier.Union.machine (AuthoredAxiomUnion.words basis) (0 : Alphabet) 1).Γ (FiniteWordClassifier.Union.machine (AuthoredAxiomUnion.words basis) (0 : Alphabet) 1).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def coreInstructions (basis : AuthoredAxiomUnion.Basis) : (AuthoredAxiomUnion.core basis).Λ → (AuthoredAxiomUnion.core basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (FiniteWordClassifier.Union.machine (AuthoredAxiomUnion.words basis) (0 : Alphabet) 1).k₁ (AuthoredAxiomUnion.assembler).k₀ (AuthoredAxiomUnion.assembler).main (default : (Option Alphabet)) id
    (FiniteWordClassifier.Union.program (AuthoredAxiomUnion.words basis) (0 : Alphabet) 1) (assemblerInstructions))
theorem coreInstructions_exact (basis : AuthoredAxiomUnion.Basis) : coreInstructions basis = (AuthoredAxiomUnion.core basis).m :=
  composition_exact (FiniteWordClassifier.Union.machine (AuthoredAxiomUnion.words basis) (0 : Alphabet) 1) (AuthoredAxiomUnion.assembler) (Equiv.refl (Option Alphabet)) (rfl) (assemblerInstructions_exact)

local instance (basis : AuthoredAxiomUnion.Basis) : Fintype ((AuthoredAxiomUnion.preparedMachine basis).Γ (AuthoredAxiomUnion.preparedMachine basis).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (basis : AuthoredAxiomUnion.Basis) : Inhabited ((AuthoredAxiomUnion.preparedMachine basis).Γ (AuthoredAxiomUnion.preparedMachine basis).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def sourceUnionInstructions (basis : AuthoredAxiomUnion.Basis) : (AuthoredAxiomUnion.machine basis).Λ → (AuthoredAxiomUnion.machine basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (AuthoredAxiomUnion.preparedMachine basis).k₁ (AuthoredAxiomUnion.core basis).k₀ (AuthoredAxiomUnion.core basis).main (default : (Option Alphabet)) id
    (preparedInstructions basis) (coreInstructions basis))
theorem sourceUnionInstructions_exact (basis : AuthoredAxiomUnion.Basis) : sourceUnionInstructions basis = (AuthoredAxiomUnion.machine basis).m :=
  composition_exact (AuthoredAxiomUnion.preparedMachine basis) (AuthoredAxiomUnion.core basis) (Equiv.refl (Option Alphabet)) (preparedInstructions_exact basis) (coreInstructions_exact basis)

def unionStripInstructionsTable  : { body : (unionStrip).Λ → (unionStrip).Stmt // body = (unionStrip).m } := by
  extract_rule_program (unionStrip).m
def unionStripInstructions  := (unionStripInstructionsTable ).val
theorem unionStripInstructions_exact  : unionStripInstructions  = (unionStrip).m := (unionStripInstructionsTable ).property

local instance (basis : AuthoredAxiomUnion.Basis) : Fintype ((AuthoredAxiomUnion.machine basis).Γ (AuthoredAxiomUnion.machine basis).k₁) := inferInstanceAs (Fintype Alphabet)
local instance (basis : AuthoredAxiomUnion.Basis) : Inhabited ((AuthoredAxiomUnion.machine basis).Γ (AuthoredAxiomUnion.machine basis).k₁) := inferInstanceAs (Inhabited Alphabet)
def unionBodyInstructions (basis : AuthoredAxiomUnion.Basis) : (unionBody basis).Λ → (unionBody basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (AuthoredAxiomUnion.machine basis).k₁ (unionStrip).k₀ (unionStrip).main (default : Alphabet) id
    (sourceUnionInstructions basis) (unionStripInstructions))
theorem unionBodyInstructions_exact (basis : AuthoredAxiomUnion.Basis) : unionBodyInstructions basis = (unionBody basis).m :=
  composition_exact (AuthoredAxiomUnion.machine basis) (unionStrip) (Equiv.refl Alphabet) (sourceUnionInstructions_exact basis) (unionStripInstructions_exact)

def unionFieldInstructionsTable  : { body : (FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))).Λ → (FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))).Stmt // body = (FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))).m } := by
  extract_rule_program (FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))).m
def unionFieldInstructions  := (unionFieldInstructionsTable ).val
theorem unionFieldInstructions_exact  : unionFieldInstructions  = (FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))).m := (unionFieldInstructionsTable ).property

local instance : Fintype ((FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))).Γ (FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))).Γ (FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def selectedUnionInstructions (basis : AuthoredAxiomUnion.Basis) : (selectedUnionMachine basis).Λ → (selectedUnionMachine basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))).k₁ (unionBody basis).k₀ (unionBody basis).main (default : (Option Alphabet)) id
    (unionFieldInstructions) (unionBodyInstructions basis))
theorem selectedUnionInstructions_exact (basis : AuthoredAxiomUnion.Basis) : selectedUnionInstructions basis = (selectedUnionMachine basis).m :=
  composition_exact (FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))) (unionBody basis) (Equiv.refl (Option Alphabet)) (unionFieldInstructions_exact) (unionBodyInstructions_exact basis)

def retainedUnionInstructionsInner (basis : AuthoredAxiomUnion.Basis) : (RetainedWordExecution.WithOutput.machine (selectedUnionMachine basis)).Λ → (RetainedWordExecution.WithOutput.machine (selectedUnionMachine basis)).Stmt := by
  claim_program_literal_endpoints (RetainedWordExecution.WithOutput.Programs.statement
    (selectedUnionMachine basis).k₀ (selectedUnionMachine basis).k₁ (none : Option Alphabet) (0 : Alphabet)
    (selectedUnionMachine basis).initialState (selectedUnionMachine basis).main (selectedUnionInstructions basis))
theorem retainedUnionInstructionsInner_exact (basis : AuthoredAxiomUnion.Basis) : retainedUnionInstructionsInner basis = (RetainedWordExecution.WithOutput.machine (selectedUnionMachine basis)).m := by
  unfold retainedUnionInstructionsInner
  rw [selectedUnionInstructions_exact basis]
  rfl

local instance (basis : AuthoredAxiomUnion.Basis) : Fintype ((RetainedWordExecution.WithOutput.machine (selectedUnionMachine basis)).Γ (RetainedWordExecution.WithOutput.machine (selectedUnionMachine basis)).k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Alphabet))
local instance (basis : AuthoredAxiomUnion.Basis) : Inhabited ((RetainedWordExecution.WithOutput.machine (selectedUnionMachine basis)).Γ (RetainedWordExecution.WithOutput.machine (selectedUnionMachine basis)).k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Alphabet))
def retainedUnionInstructionsTagged (basis : AuthoredAxiomUnion.Basis) : (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Λ → (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (RetainedWordExecution.WithOutput.machine (selectedUnionMachine basis)).k₁ (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).k₀ (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).main (default : (Option Alphabet ⊕ Alphabet)) id
    (retainedUnionInstructionsInner basis) (WordHomomorphismMachine.program (RetainedWordExecution.WithOutput.Framed.untag (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))))
theorem retainedUnionInstructionsTagged_exact (basis : AuthoredAxiomUnion.Basis) : retainedUnionInstructionsTagged basis = (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).m :=
  composition_exact (RetainedWordExecution.WithOutput.machine (selectedUnionMachine basis)) (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))) (Equiv.refl (Option Alphabet ⊕ Alphabet)) (retainedUnionInstructionsInner_exact basis) (rfl)

local instance (basis : AuthoredAxiomUnion.Basis) : Fintype ((RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Γ (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (basis : AuthoredAxiomUnion.Basis) : Inhabited ((RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Γ (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def retainedUnionInstructions (basis : AuthoredAxiomUnion.Basis) : (retainedUnionMachine basis).Λ → (retainedUnionMachine basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).k₀ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).main (default : (Option Alphabet)) id
    (retainedUnionInstructionsTagged basis) (WordTemplateMachine.program (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))))
theorem retainedUnionInstructions_exact (basis : AuthoredAxiomUnion.Basis) : retainedUnionInstructions basis = (retainedUnionMachine basis).m :=
  composition_exact (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)) (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))) (Equiv.refl (Option Alphabet)) (retainedUnionInstructionsTagged_exact basis) (rfl)

local instance  : Fintype ((retainedAxiomMachine (0 : Fin 9)).Γ (retainedAxiomMachine (0 : Fin 9)).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance  : Inhabited ((retainedAxiomMachine (0 : Fin 9)).Γ (retainedAxiomMachine (0 : Fin 9)).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def theoremFieldsInstructions  : (theoremFieldsMachine).Λ → (theoremFieldsMachine).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (retainedAxiomMachine (0 : Fin 9)).k₁ (retainedAxiomMachine (1 : Fin 10)).k₀ (retainedAxiomMachine (1 : Fin 10)).main (default : (Option Alphabet)) id
    (retainedAxiomInstructions (0 : Fin 9)) (retainedAxiomInstructions (1 : Fin 10)))
theorem theoremFieldsInstructions_exact  : theoremFieldsInstructions  = (theoremFieldsMachine).m :=
  composition_exact (retainedAxiomMachine (0 : Fin 9)) (retainedAxiomMachine (1 : Fin 10)) (Equiv.refl (Option Alphabet)) (retainedAxiomInstructions_exact (0 : Fin 9)) (retainedAxiomInstructions_exact (1 : Fin 10))

local instance : Fintype ((theoremFieldsMachine).Γ (theoremFieldsMachine).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance : Inhabited ((theoremFieldsMachine).Γ (theoremFieldsMachine).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def supportsInstructions (basis : AuthoredAxiomUnion.Basis) : (supportsMachine basis).Λ → (supportsMachine basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (theoremFieldsMachine).k₁ (retainedUnionMachine basis).k₀ (retainedUnionMachine basis).main (default : (Option Alphabet)) id
    (theoremFieldsInstructions) (retainedUnionInstructions basis))
theorem supportsInstructions_exact (basis : AuthoredAxiomUnion.Basis) : supportsInstructions basis = (supportsMachine basis).m :=
  composition_exact (theoremFieldsMachine) (retainedUnionMachine basis) (Equiv.refl (Option Alphabet)) (theoremFieldsInstructions_exact) (retainedUnionInstructions_exact basis)

def routingInstructionsTable  : { body : (FramedFieldSelection.machine (Γ := Alphabet) routing).Λ → (FramedFieldSelection.machine (Γ := Alphabet) routing).Stmt // body = (FramedFieldSelection.machine (Γ := Alphabet) routing).m } := by
  extract_rule_program (FramedFieldSelection.machine (Γ := Alphabet) routing).m
def routingInstructions  := (routingInstructionsTable ).val
theorem routingInstructions_exact  : routingInstructions  = (FramedFieldSelection.machine (Γ := Alphabet) routing).m := (routingInstructionsTable ).property

local instance (basis : AuthoredAxiomUnion.Basis) : Fintype ((supportsMachine basis).Γ (supportsMachine basis).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (basis : AuthoredAxiomUnion.Basis) : Inhabited ((supportsMachine basis).Γ (supportsMachine basis).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def routedInstructions (basis : AuthoredAxiomUnion.Basis) : (routedMachine basis).Λ → (routedMachine basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (supportsMachine basis).k₁ (FramedFieldSelection.machine (Γ := Alphabet) routing).k₀ (FramedFieldSelection.machine (Γ := Alphabet) routing).main (default : (Option Alphabet)) id
    (supportsInstructions basis) (routingInstructions))
theorem routedInstructions_exact (basis : AuthoredAxiomUnion.Basis) : routedInstructions basis = (routedMachine basis).m :=
  composition_exact (supportsMachine basis) (FramedFieldSelection.machine (Γ := Alphabet) routing) (Equiv.refl (Option Alphabet)) (supportsInstructions_exact basis) (routingInstructions_exact)

local instance (basis : AuthoredAxiomUnion.Basis) : Fintype ((routedMachine basis).Γ (routedMachine basis).k₁) := inferInstanceAs (Fintype (Option Alphabet))
local instance (basis : AuthoredAxiomUnion.Basis) : Inhabited ((routedMachine basis).Γ (routedMachine basis).k₁) := inferInstanceAs (Inhabited (Option Alphabet))
def instructions (basis : AuthoredAxiomUnion.Basis) : (target basis).Λ → (target basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (routedMachine basis).k₁ (Indexed.machine DynamicModusPonensTemplates.template).k₀ (Indexed.machine DynamicModusPonensTemplates.template).main (default : (Option Alphabet)) id
    (routedInstructions basis) (Indexed.arrayProgram DynamicModusPonensTemplates.template.length DynamicModusPonensTemplates.template.toArray))
theorem instructions_exact (basis : AuthoredAxiomUnion.Basis) : instructions basis = (target basis).m :=
  composition_exact (routedMachine basis) (Indexed.machine DynamicModusPonensTemplates.template) (Equiv.refl (Option Alphabet)) (routedInstructions_exact basis) (Indexed.arrayProgram_eq_program DynamicModusPonensTemplates.template)

def inputKey (basis : AuthoredAxiomUnion.Basis) : (target basis).K := by
  claim_program_literal_endpoints (target basis).k₀
def outputKey (basis : AuthoredAxiomUnion.Basis) : (target basis).K := by
  claim_program_literal_endpoints (target basis).k₁
def mainLabel (basis : AuthoredAxiomUnion.Basis) : (target basis).Λ := by
  claim_program_literal_endpoints (target basis).main
def initialRegisters (basis : AuthoredAxiomUnion.Basis) : (target basis).σ := by
  claim_program_literal_endpoints (target basis).initialState

@[instance_reducible] def keyEquality (basis : AuthoredAxiomUnion.Basis) : DecidableEq (target basis).K := by
  claim_program_key_equality

/-- No finite-enumeration witness is evaluated by the direct transition interface. -/
def step (basis : AuthoredAxiomUnion.Basis) := @TM2.step (target basis).K (target basis).Γ
  (target basis).Λ (target basis).σ (keyEquality basis) (instructions basis)
theorem step_exact (basis : AuthoredAxiomUnion.Basis) : step basis = (target basis).step := by
  unfold step
  rw [instructions_exact,show keyEquality basis = (target basis).kDecidableEq from Subsingleton.elim _ _]
  rfl

theorem inputKey_exact (basis : AuthoredAxiomUnion.Basis) : inputKey basis = (target basis).k₀ := rfl
theorem outputKey_exact (basis : AuthoredAxiomUnion.Basis) : outputKey basis = (target basis).k₁ := rfl
theorem mainLabel_exact (basis : AuthoredAxiomUnion.Basis) : mainLabel basis = (target basis).main := rfl
theorem initialRegisters_exact (basis : AuthoredAxiomUnion.Basis) : initialRegisters basis = (target basis).initialState := rfl


local instance (basis : AuthoredAxiomUnion.Basis) : DecidableEq (target basis).K := keyEquality basis

def keys (basis : AuthoredAxiomUnion.Basis) : List (target basis).K := by claim_program_keys
local instance (basis : AuthoredAxiomUnion.Basis) : BEq (target basis).K := ⟨fun a b => decide (a=b)⟩
local instance (basis : AuthoredAxiomUnion.Basis) : LawfulBEq (target basis).K where
  eq_of_beq h := of_decide_eq_true h
  rfl := by intro a; exact decide_eq_true rfl
noncomputable local instance (basis : AuthoredAxiomUnion.Basis) : Fintype (target basis).K := (target basis).kFin

theorem all_keys (basis : AuthoredAxiomUnion.Basis) : ∀ key : (target basis).K, key ∈ keys basis := by
  change ∀ key : (target ∅).K, key ∈ keys ∅
  decide +kernel
theorem keys_nodup (basis : AuthoredAxiomUnion.Basis) : (keys basis).Nodup := by
  change (keys ∅).Nodup
  decide +kernel

def initial (basis : AuthoredAxiomUnion.Basis) (word : List (Option Alphabet)) : (target basis).Cfg where
  l := some (mainLabel basis)
  var := initialRegisters basis
  stk key := if same : key=inputKey basis then by cases same; exact word else []

theorem initial_exact (basis : AuthoredAxiomUnion.Basis) (word : List (Option Alphabet)) :
    initial basis word = initList (target basis) word := by
  simp only [initial,initList]
  congr 1
  funext key
  by_cases same : key = inputKey basis
  · subst key
    have original : inputKey basis = (target basis).k₀ := rfl
    simp only [dif_pos original]
    rfl
  · have original : key ≠ (target basis).k₀ := same
    simp only [dif_neg same,dif_neg original]


/-- Cache a finite dependent register function without changing any value. -/
def snapshotFunction {Index : Type} [DecidableEq Index] {Cells : Index → Type}
    (keys : List Index) (defaults values : ∀ index, Cells index) : ∀ index, Cells index :=
  let cached := StackMachineRegisters.StackSnapshot.snapshot Cells (fun index => [values index]) keys
  fun index => (StackMachineRegisters.StackSnapshot.lookup Cells cached index).head?.getD (defaults index)

theorem snapshotFunction_exact {Index : Type} [DecidableEq Index] {Cells : Index → Type}
    (keys : List Index) (all : ∀ index, index ∈ keys) (defaults values : ∀ index, Cells index) :
    snapshotFunction keys defaults values = values := by
  funext index
  have same := StackMachineRegisters.StackSnapshot.lookup_snapshot Cells (fun index => [values index]) keys index (all index)
  dsimp only [snapshotFunction]
  rw [same]
  rfl

open Lean Elab Tactic Meta in
private partial def cachedRegisters (type value : Expr) : MetaM Expr := do
  let type ← withTransparency .reducible (whnf type)
  match type with
  | .forallE _ indexType _ _ =>
    let indexType ← withTransparency .all (whnf indexType)
    unless indexType.isAppOf ``Fin do throwError "Register function index is not finite numeric: {indexType}"
    let n := indexType.getAppArgs.back!
    let keys ← mkAppM ``List.finRange #[n]
    let defaults ← withLocalDeclD `index indexType fun index => do
      let cellType ← withTransparency .all (whnf (← inferType (mkApp value index)))
      let fallback ← match cellType.getAppFn.constName? with
        | some ``Option => mkAppOptM ``Option.none #[some cellType.getAppArgs.back!]
        | some ``Bool => pure (mkConst ``Bool.false)
        | _ => throwError "Unsupported register function cell: {cellType}"
      mkLambdaFVars #[index] fallback
    mkAppM ``snapshotFunction #[keys,defaults,value]
  | _ =>
    match type.getAppFn.constName?,type.getAppArgs.toList with
    | some ``Prod,[first,second] =>
      let a ← cachedRegisters first (← mkAppM ``Prod.fst #[value])
      let b ← cachedRegisters second (← mkAppM ``Prod.snd #[value])
      mkAppM ``Prod.mk #[a,b]
    | some ``FiniteWordClassifier.Union.State,_ =>
      let cursors := Expr.proj ``FiniteWordClassifier.Union.State 0 value
      let seen := Expr.proj ``FiniteWordClassifier.Union.State 1 value
      let a ← cachedRegisters (← inferType cursors) cursors
      let b ← cachedRegisters (← inferType seen) seen
      mkAppM ``FiniteWordClassifier.Union.State.mk #[a,b,
        Expr.proj ``FiniteWordClassifier.Union.State 2 value,
        Expr.proj ``FiniteWordClassifier.Union.State 3 value,
        Expr.proj ``FiniteWordClassifier.Union.State 4 value]
    | _,_ => pure value

open Lean Elab Tactic Meta in
elab "cache_dynamic_registers " expression:term : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let value ← Elab.Term.elabTerm expression (← goal.getType)
    goal.assign (← cachedRegisters (← inferType value) value)
  replaceMainGoal []

def refreshRegisters (basis : AuthoredAxiomUnion.Basis) (values : (target basis).σ) : (target basis).σ := by
  cache_dynamic_registers values

theorem refreshRegisters_exact (basis : AuthoredAxiomUnion.Basis) (values : (target basis).σ) :
    refreshRegisters basis values = values := by
  simp only [refreshRegisters]
  simp only [snapshotFunction_exact _ (fun index => List.mem_finRange index)]


deriving instance DecidableEq for FiniteWordClassifier.Union.State

def registerEquality (basis : AuthoredAxiomUnion.Basis) : DecidableEq (target basis).σ := by
  claim_program_key_equality

/-- Materializing all stack cells and finite functions preserves the complete configuration. -/
def refresh (basis : AuthoredAxiomUnion.Basis) (state : (target basis).Cfg) : (target basis).Cfg :=
  let cells := StackMachineRegisters.StackSnapshot.snapshot (target basis).Γ state.stk (keys basis)
  ⟨state.l,refreshRegisters basis state.var,StackMachineRegisters.StackSnapshot.lookup (target basis).Γ cells⟩

theorem refresh_exact (basis : AuthoredAxiomUnion.Basis) (state : (target basis).Cfg) : refresh basis state=state := by
  have stacksSame : StackMachineRegisters.StackSnapshot.lookup (target basis).Γ
      (StackMachineRegisters.StackSnapshot.snapshot (target basis).Γ state.stk (keys basis)) = state.stk := by
    funext key
    exact StackMachineRegisters.StackSnapshot.lookup_snapshot _ _ _ key (all_keys basis key)
  dsimp only [refresh]
  rw [refreshRegisters_exact,stacksSame]


def periodicRefresh (basis : AuthoredAxiomUnion.Basis) (period used : Nat) (state : (target basis).Cfg) : (target basis).Cfg :=
  if used % period == 0 then refresh basis state else state

theorem periodicRefresh_exact (basis : AuthoredAxiomUnion.Basis) (period used : Nat) (state : (target basis).Cfg) :
    periodicRefresh basis period used state = state := by
  unfold periodicRefresh
  split <;> simp only [refresh_exact]

def run (basis : AuthoredAxiomUnion.Basis) (period : Nat) : Nat → Nat → (target basis).Cfg → Option (Nat × (target basis).Cfg)
  | 0, _, _ => none
  | fuel+1, used, state =>
    if state.l.isNone then some (used,state)
    else match step basis state with
      | none => none
      | some next => run basis period fuel (used+1) (periodicRefresh basis period (used+1) next)


theorem run_actual (basis : AuthoredAxiomUnion.Basis) (period fuel used : Nat) (before : (target basis).Cfg)
    {count : Nat} {after : (target basis).Cfg}
    (completed : run basis period fuel used before = some (count,after)) :
    used ≤ count ∧
      (∃ path : StateTransition.EvalsToInTime (target basis).step before (some after) (count-used),
        path.steps = count-used) ∧
      after.l = none := by
  induction fuel generalizing used before with
  | zero => cases completed
  | succ fuel ih =>
    simp only [run] at completed
    split at completed
    · rename_i halted
      have pair := Option.some.inj completed
      have countSame := congrArg Prod.fst pair
      have stateSame := congrArg Prod.snd pair
      change used = count at countSame
      change before = after at stateSame
      subst count
      subst after
      refine ⟨le_rfl,?_,Option.isNone_iff_eq_none.mp halted⟩
      rw [Nat.sub_self]
      exact ⟨StateTransition.EvalsToInTime.refl (target basis).step before,rfl⟩
    · cases advanced : step basis before with
      | none => simp only [advanced,reduceCtorEq] at completed
      | some next =>
        simp only [advanced] at completed
        rw [periodicRefresh_exact] at completed
        rcases ih (used+1) next completed with ⟨countBound,⟨tail,tailCount⟩,halted⟩
        have original : (target basis).step before = some next := by
          rw [← step_exact basis]
          exact advanced
        let first : StateTransition.EvalsToInTime (target basis).step before (some next) 1 :=
          ⟨⟨1,by change (some before).bind (target basis).step = some next; exact original⟩,le_rfl⟩
        have relative : count-used = (count-(used+1))+1 := by omega
        refine ⟨by omega,?_,halted⟩
        rw [relative]
        refine ⟨StateTransition.EvalsToInTime.trans (target basis).step 1 (count-(used+1))
          before next (some after) first tail,?_⟩
        change tail.steps+first.steps = (count-(used+1))+1
        rw [tailCount]


end Mettapedia.Languages.HOLLight.DynamicModusPonensProgram
