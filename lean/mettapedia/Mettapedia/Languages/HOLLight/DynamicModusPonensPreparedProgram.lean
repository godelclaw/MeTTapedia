import Mettapedia.Languages.HOLLight.DynamicModusPonensTreeProgram
import Mettapedia.Computability.TreeStackSnapshot

/-!
# Prepared original instructions for changing MP fields

The fixed authored basis is sorted and encoded into retained word rows before
execution. Literal initializer extraction avoids evaluating bundled machine
metadata; finite register snapshots retain the actual cursor and membership
columns. The descriptor composes the original physical instruction interfaces.
Its complete instruction function equals the original machine function.

This is a fixed-authority, finite-register execution interface. It does not
construct an enumerated finite-control table or change the formal TM clock.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true
namespace Mettapedia.Languages.HOLLight.DynamicModusPonensPreparedProgram
open Mettapedia.Languages.HOLLight
open Turing Lean Elab Tactic Meta
open Mettapedia.Computability.TreeStackSnapshot

open Turing Mettapedia.Computability Mettapedia.Computability.WordTemplateMachine Mettapedia.Languages.HOLLight.DynamicModusPonensEmission
attribute [local reducible] FinTM2.Cfg FinTM2.Stmt
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


open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Languages.HOLLight.DynamicModusPonensProgram
open Mettapedia.Computability.FiniteWordClassifier Turing.TM2.Stmt

def framingProgram {n : Nat} (sourceWords : Fin n → List Alphabet) (phase : AuthoredListFraming.Phase) : TM2.Stmt AuthoredListFraming.Cells AuthoredListFraming.Phase (Residuals sourceWords × Option Alphabet × Option (Option Alphabet)) :=
  match phase with
  | .spine => pop .input (fun state cell => (state.1,cell,state.2.2))
      (branch (fun state => state.2.1 == some 4)
        (load (fun _ => (initial sourceWords,none,none)) (goto fun _ => .word))
        (branch (fun state => state.2.1 == some 3) (goto fun _ => .nilEnd) (goto fun _ => .rejectInput)))
  | .word => branch (fun state => (finish (sourceWords) state.1).isSome)
      (push .temporary (fun _ => none) (load (fun _ => (initial sourceWords,none,none)) (goto fun _ => .spine)))
      (pop .input (fun state cell => (state.1,cell,state.2.2))
        (branch (fun state => state.2.1.isSome)
          (push .temporary (fun state => some (state.2.1.getD 0))
            (load (fun state => (advanceAll (sourceWords) state.1 (state.2.1.getD 0),state.2))
              (goto fun _ => .word))) (goto fun _ => .rejectTemporary)))
  | .nilEnd => pop .input (fun state cell => (state.1,cell,state.2.2))
      (branch (fun state => state.2.1 == some 2) (goto fun _ => .tail) (goto fun _ => .rejectInput))
  | .tail => pop .input (fun state cell => (state.1,cell,state.2.2))
      (branch (fun state => state.2.1.isNone) (goto fun _ => .reverse) (goto fun _ => .rejectInput))
  | .reverse => pop .temporary (fun state cell => (state.1,state.2.1,cell))
      (branch (fun state => state.2.2.isSome)
        (push .result (fun state => state.2.2.getD none) (goto fun _ => .reverse))
        (push .result (fun _ => some 1) (load (fun _ => (initial sourceWords,none,none)) halt)))
  | .rejectInput => pop .input (fun state cell => (state.1,cell,state.2.2))
      (branch (fun state => state.2.1.isSome) (goto fun _ => .rejectInput) (goto fun _ => .rejectTemporary))
  | .rejectTemporary => pop .temporary (fun state cell => (state.1,state.2.1,cell))
      (branch (fun state => state.2.2.isSome) (goto fun _ => .rejectTemporary)
        (push .result (fun _ => some 0) (load (fun _ => (initial sourceWords,none,none)) halt)))


theorem framingProgram_exact {n : Nat} (dictionary : Fin n → Mettapedia.OSLF.Binding.WireCodec.Data) :
    framingProgram (AuthoredListFraming.words dictionary)=AuthoredListFraming.program dictionary := rfl

private def framingCached {n : Nat} (sourceWords : Fin n → List Alphabet)
    (cache : Snapshot (Fin n) (fun _ => List Alphabet)) (same : cache.read=sourceWords) :
    AuthoredListFraming.Phase → TM2.Stmt AuthoredListFraming.Cells AuthoredListFraming.Phase
      (Residuals sourceWords × Option Alphabet × Option (Option Alphabet)) :=
  same ▸ framingProgram cache.read

private theorem framingCached_exact {n : Nat} (sourceWords : Fin n → List Alphabet)
    (cache : Snapshot (Fin n) (fun _ => List Alphabet)) (same : cache.read=sourceWords) :
    framingCached sourceWords cache same=framingProgram sourceWords := by
  cases same
  rfl

private def unionCached {n : Nat} (sourceWords : Fin n → List Alphabet)
    (cache : Snapshot (Fin n) (fun _ => List Alphabet)) (same : cache.read=sourceWords) :
    (FiniteWordClassifier.Union.machine sourceWords (0 : Alphabet) 1).Λ →
      (FiniteWordClassifier.Union.machine sourceWords (0 : Alphabet) 1).Stmt :=
  same ▸ FiniteWordClassifier.Union.program cache.read 0 1

private theorem unionCached_exact {n : Nat} (sourceWords : Fin n → List Alphabet)
    (cache : Snapshot (Fin n) (fun _ => List Alphabet)) (same : cache.read=sourceWords) :
    unionCached sourceWords cache same=FiniteWordClassifier.Union.program sourceWords 0 1 := by
  cases same
  rfl

def scannerInstructionsPrepared (basis : AuthoredAxiomUnion.Basis) (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ) : (AuthoredAxiomUnion.scanner basis).Λ → (AuthoredAxiomUnion.scanner basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (AuthoredListFraming.machine (AuthoredAxiomUnion.dictionary basis)).k₁ (AuthoredAxiomUnion.strippedFramer).k₀ (AuthoredAxiomUnion.strippedFramer).main (default : (Option Alphabet)) id
    (framingCached (AuthoredAxiomUnion.words basis) cache same) (strippedFramerInstructions))
theorem scannerInstructionsPrepared_exact (basis : AuthoredAxiomUnion.Basis)
    (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ)
    (_scannerSame : _scannerInitial=(AuthoredAxiomUnion.scanner basis).initialState)
    (_selectedSame : _selectedInitial=(selectedUnionMachine basis).initialState) :
    scannerInstructionsPrepared basis cache same _scannerInitial _selectedInitial=DynamicModusPonensProgram.scannerInstructions basis := by
  unfold scannerInstructionsPrepared DynamicModusPonensProgram.scannerInstructions
  rw [framingCached_exact]
  all_goals rfl


def mappedScannerInstructionsPrepared (basis : AuthoredAxiomUnion.Basis) (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ) : (FramedWordMapping.machine (AuthoredAxiomUnion.scanner basis)).Λ → (FramedWordMapping.machine (AuthoredAxiomUnion.scanner basis)).Stmt := by
  claim_program_literal_endpoints (FramedWordMapping.Programs.body
    (AuthoredAxiomUnion.scanner basis).k₀ (AuthoredAxiomUnion.scanner basis).k₁
    _scannerInitial (AuthoredAxiomUnion.scanner basis).main
    (0 : Alphabet) (none : Option Alphabet) (scannerInstructionsPrepared basis cache same _scannerInitial _selectedInitial))
theorem mappedScannerInstructionsPrepared_exact (basis : AuthoredAxiomUnion.Basis)
    (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ)
    (_scannerSame : _scannerInitial=(AuthoredAxiomUnion.scanner basis).initialState)
    (_selectedSame : _selectedInitial=(selectedUnionMachine basis).initialState) :
    mappedScannerInstructionsPrepared basis cache same _scannerInitial _selectedInitial=DynamicModusPonensProgram.mappedScannerInstructions basis := by
  unfold mappedScannerInstructionsPrepared DynamicModusPonensProgram.mappedScannerInstructions
  rw [scannerInstructionsPrepared_exact basis cache same _scannerInitial _selectedInitial _scannerSame _selectedSame]
  rw [_scannerSame]


def preparedInstructionsPrepared (basis : AuthoredAxiomUnion.Basis) (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ) : (AuthoredAxiomUnion.preparedMachine basis).Λ → (AuthoredAxiomUnion.preparedMachine basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (FramedWordMapping.machine (AuthoredAxiomUnion.scanner basis)).k₁ (WordHomomorphismMachine.machine AuthoredAxiomUnion.flatten).k₀ (WordHomomorphismMachine.machine AuthoredAxiomUnion.flatten).main (default : (Option (Option Alphabet))) id
    (mappedScannerInstructionsPrepared basis cache same _scannerInitial _selectedInitial) (WordHomomorphismMachine.program AuthoredAxiomUnion.flatten))
theorem preparedInstructionsPrepared_exact (basis : AuthoredAxiomUnion.Basis)
    (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ)
    (_scannerSame : _scannerInitial=(AuthoredAxiomUnion.scanner basis).initialState)
    (_selectedSame : _selectedInitial=(selectedUnionMachine basis).initialState) :
    preparedInstructionsPrepared basis cache same _scannerInitial _selectedInitial=DynamicModusPonensProgram.preparedInstructions basis := by
  unfold preparedInstructionsPrepared DynamicModusPonensProgram.preparedInstructions
  rw [mappedScannerInstructionsPrepared_exact basis cache same _scannerInitial _selectedInitial _scannerSame _selectedSame]


def coreInstructionsPrepared (basis : AuthoredAxiomUnion.Basis) (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ) : (AuthoredAxiomUnion.core basis).Λ → (AuthoredAxiomUnion.core basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (FiniteWordClassifier.Union.machine (AuthoredAxiomUnion.words basis) (0 : Alphabet) 1).k₁ (AuthoredAxiomUnion.assembler).k₀ (AuthoredAxiomUnion.assembler).main (default : (Option Alphabet)) id
    (unionCached (AuthoredAxiomUnion.words basis) cache same) (assemblerInstructions))
theorem coreInstructionsPrepared_exact (basis : AuthoredAxiomUnion.Basis)
    (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ)
    (_scannerSame : _scannerInitial=(AuthoredAxiomUnion.scanner basis).initialState)
    (_selectedSame : _selectedInitial=(selectedUnionMachine basis).initialState) :
    coreInstructionsPrepared basis cache same _scannerInitial _selectedInitial=DynamicModusPonensProgram.coreInstructions basis := by
  unfold coreInstructionsPrepared DynamicModusPonensProgram.coreInstructions
  rw [unionCached_exact]


def sourceUnionInstructionsPrepared (basis : AuthoredAxiomUnion.Basis) (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ) : (AuthoredAxiomUnion.machine basis).Λ → (AuthoredAxiomUnion.machine basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (AuthoredAxiomUnion.preparedMachine basis).k₁ (AuthoredAxiomUnion.core basis).k₀ (AuthoredAxiomUnion.core basis).main (default : (Option Alphabet)) id
    (preparedInstructionsPrepared basis cache same _scannerInitial _selectedInitial) (coreInstructionsPrepared basis cache same _scannerInitial _selectedInitial))
theorem sourceUnionInstructionsPrepared_exact (basis : AuthoredAxiomUnion.Basis)
    (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ)
    (_scannerSame : _scannerInitial=(AuthoredAxiomUnion.scanner basis).initialState)
    (_selectedSame : _selectedInitial=(selectedUnionMachine basis).initialState) :
    sourceUnionInstructionsPrepared basis cache same _scannerInitial _selectedInitial=DynamicModusPonensProgram.sourceUnionInstructions basis := by
  unfold sourceUnionInstructionsPrepared DynamicModusPonensProgram.sourceUnionInstructions
  rw [preparedInstructionsPrepared_exact basis cache same _scannerInitial _selectedInitial _scannerSame _selectedSame]
  rw [coreInstructionsPrepared_exact basis cache same _scannerInitial _selectedInitial _scannerSame _selectedSame]


def unionBodyInstructionsPrepared (basis : AuthoredAxiomUnion.Basis) (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ) : (unionBody basis).Λ → (unionBody basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (AuthoredAxiomUnion.machine basis).k₁ (unionStrip).k₀ (unionStrip).main (default : Alphabet) id
    (sourceUnionInstructionsPrepared basis cache same _scannerInitial _selectedInitial) (unionStripInstructions))
theorem unionBodyInstructionsPrepared_exact (basis : AuthoredAxiomUnion.Basis)
    (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ)
    (_scannerSame : _scannerInitial=(AuthoredAxiomUnion.scanner basis).initialState)
    (_selectedSame : _selectedInitial=(selectedUnionMachine basis).initialState) :
    unionBodyInstructionsPrepared basis cache same _scannerInitial _selectedInitial=DynamicModusPonensProgram.unionBodyInstructions basis := by
  unfold unionBodyInstructionsPrepared DynamicModusPonensProgram.unionBodyInstructions
  rw [sourceUnionInstructionsPrepared_exact basis cache same _scannerInitial _selectedInitial _scannerSame _selectedSame]


def selectedUnionInstructionsPrepared (basis : AuthoredAxiomUnion.Basis) (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ) : (selectedUnionMachine basis).Λ → (selectedUnionMachine basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (FramedFieldSelection.machine (Γ := Alphabet) ([9,10] : List (Fin 11))).k₁ (unionBody basis).k₀ (unionBody basis).main (default : (Option Alphabet)) id
    (unionFieldInstructions) (unionBodyInstructionsPrepared basis cache same _scannerInitial _selectedInitial))
theorem selectedUnionInstructionsPrepared_exact (basis : AuthoredAxiomUnion.Basis)
    (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ)
    (_scannerSame : _scannerInitial=(AuthoredAxiomUnion.scanner basis).initialState)
    (_selectedSame : _selectedInitial=(selectedUnionMachine basis).initialState) :
    selectedUnionInstructionsPrepared basis cache same _scannerInitial _selectedInitial=DynamicModusPonensProgram.selectedUnionInstructions basis := by
  unfold selectedUnionInstructionsPrepared DynamicModusPonensProgram.selectedUnionInstructions
  rw [unionBodyInstructionsPrepared_exact basis cache same _scannerInitial _selectedInitial _scannerSame _selectedSame]


def retainedUnionInstructionsInnerPrepared (basis : AuthoredAxiomUnion.Basis) (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ) : (RetainedWordExecution.WithOutput.machine (selectedUnionMachine basis)).Λ → (RetainedWordExecution.WithOutput.machine (selectedUnionMachine basis)).Stmt := by
  claim_program_literal_endpoints (RetainedWordExecution.WithOutput.Programs.statement
    (selectedUnionMachine basis).k₀ (selectedUnionMachine basis).k₁ (none : Option Alphabet) (0 : Alphabet)
    _selectedInitial (selectedUnionMachine basis).main (selectedUnionInstructionsPrepared basis cache same _scannerInitial _selectedInitial))
theorem retainedUnionInstructionsInnerPrepared_exact (basis : AuthoredAxiomUnion.Basis)
    (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ)
    (_scannerSame : _scannerInitial=(AuthoredAxiomUnion.scanner basis).initialState)
    (_selectedSame : _selectedInitial=(selectedUnionMachine basis).initialState) :
    retainedUnionInstructionsInnerPrepared basis cache same _scannerInitial _selectedInitial=DynamicModusPonensProgram.retainedUnionInstructionsInner basis := by
  unfold retainedUnionInstructionsInnerPrepared DynamicModusPonensProgram.retainedUnionInstructionsInner
  rw [selectedUnionInstructionsPrepared_exact basis cache same _scannerInitial _selectedInitial _scannerSame _selectedSame]
  rw [_selectedSame]


def retainedUnionInstructionsTaggedPrepared (basis : AuthoredAxiomUnion.Basis) (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ) : (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Λ → (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (RetainedWordExecution.WithOutput.machine (selectedUnionMachine basis)).k₁ (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).k₀ (WordHomomorphismMachine.machine (RetainedWordExecution.WithOutput.Framed.untag (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))).main (default : (Option Alphabet ⊕ Alphabet)) id
    (retainedUnionInstructionsInnerPrepared basis cache same _scannerInitial _selectedInitial) (WordHomomorphismMachine.program (RetainedWordExecution.WithOutput.Framed.untag (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet))))
theorem retainedUnionInstructionsTaggedPrepared_exact (basis : AuthoredAxiomUnion.Basis)
    (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ)
    (_scannerSame : _scannerInitial=(AuthoredAxiomUnion.scanner basis).initialState)
    (_selectedSame : _selectedInitial=(selectedUnionMachine basis).initialState) :
    retainedUnionInstructionsTaggedPrepared basis cache same _scannerInitial _selectedInitial=DynamicModusPonensProgram.retainedUnionInstructionsTagged basis := by
  unfold retainedUnionInstructionsTaggedPrepared DynamicModusPonensProgram.retainedUnionInstructionsTagged
  rw [retainedUnionInstructionsInnerPrepared_exact basis cache same _scannerInitial _selectedInitial _scannerSame _selectedSame]


def retainedUnionInstructionsPrepared (basis : AuthoredAxiomUnion.Basis) (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ) : (retainedUnionMachine basis).Λ → (retainedUnionMachine basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (RetainedWordExecution.WithOutput.Framed.taggedMachine (selectedUnionMachine basis) (Equiv.refl (Option Alphabet)) (Equiv.refl Alphabet)).k₁ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).k₀ (WordTemplateMachine.machine (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))).main (default : (Option Alphabet)) id
    (retainedUnionInstructionsTaggedPrepared basis cache same _scannerInitial _selectedInitial) (WordTemplateMachine.program (RetainedWordExecution.WithOutput.Framed.closeTemplate (Γ := Alphabet))))
theorem retainedUnionInstructionsPrepared_exact (basis : AuthoredAxiomUnion.Basis)
    (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ)
    (_scannerSame : _scannerInitial=(AuthoredAxiomUnion.scanner basis).initialState)
    (_selectedSame : _selectedInitial=(selectedUnionMachine basis).initialState) :
    retainedUnionInstructionsPrepared basis cache same _scannerInitial _selectedInitial=DynamicModusPonensProgram.retainedUnionInstructions basis := by
  unfold retainedUnionInstructionsPrepared DynamicModusPonensProgram.retainedUnionInstructions
  rw [retainedUnionInstructionsTaggedPrepared_exact basis cache same _scannerInitial _selectedInitial _scannerSame _selectedSame]


def supportsInstructionsPrepared (basis : AuthoredAxiomUnion.Basis) (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ) : (supportsMachine basis).Λ → (supportsMachine basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (theoremFieldsMachine).k₁ (retainedUnionMachine basis).k₀ (retainedUnionMachine basis).main (default : (Option Alphabet)) id
    (theoremFieldsInstructions) (retainedUnionInstructionsPrepared basis cache same _scannerInitial _selectedInitial))
theorem supportsInstructionsPrepared_exact (basis : AuthoredAxiomUnion.Basis)
    (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ)
    (_scannerSame : _scannerInitial=(AuthoredAxiomUnion.scanner basis).initialState)
    (_selectedSame : _selectedInitial=(selectedUnionMachine basis).initialState) :
    supportsInstructionsPrepared basis cache same _scannerInitial _selectedInitial=DynamicModusPonensProgram.supportsInstructions basis := by
  unfold supportsInstructionsPrepared DynamicModusPonensProgram.supportsInstructions
  rw [retainedUnionInstructionsPrepared_exact basis cache same _scannerInitial _selectedInitial _scannerSame _selectedSame]


def routedInstructionsPrepared (basis : AuthoredAxiomUnion.Basis) (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ) : (routedMachine basis).Λ → (routedMachine basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (supportsMachine basis).k₁ (FramedFieldSelection.machine (Γ := Alphabet) routing).k₀ (FramedFieldSelection.machine (Γ := Alphabet) routing).main (default : (Option Alphabet)) id
    (supportsInstructionsPrepared basis cache same _scannerInitial _selectedInitial) (routingInstructions))
theorem routedInstructionsPrepared_exact (basis : AuthoredAxiomUnion.Basis)
    (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ)
    (_scannerSame : _scannerInitial=(AuthoredAxiomUnion.scanner basis).initialState)
    (_selectedSame : _selectedInitial=(selectedUnionMachine basis).initialState) :
    routedInstructionsPrepared basis cache same _scannerInitial _selectedInitial=DynamicModusPonensProgram.routedInstructions basis := by
  unfold routedInstructionsPrepared DynamicModusPonensProgram.routedInstructions
  rw [supportsInstructionsPrepared_exact basis cache same _scannerInitial _selectedInitial _scannerSame _selectedSame]


def instructionsPrepared (basis : AuthoredAxiomUnion.Basis) (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ) : (target basis).Λ → (target basis).Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (routedMachine basis).k₁ (Indexed.machine DynamicModusPonensTemplates.template).k₀ (Indexed.machine DynamicModusPonensTemplates.template).main (default : (Option Alphabet)) id
    (routedInstructionsPrepared basis cache same _scannerInitial _selectedInitial) (Indexed.arrayProgram DynamicModusPonensTemplates.template.length DynamicModusPonensTemplates.template.toArray))
theorem instructionsPrepared_exact (basis : AuthoredAxiomUnion.Basis)
    (cache : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet))
    (same : cache.read=AuthoredAxiomUnion.words basis)
    (_scannerInitial : (AuthoredAxiomUnion.scanner basis).σ)
    (_selectedInitial : (selectedUnionMachine basis).σ)
    (_scannerSame : _scannerInitial=(AuthoredAxiomUnion.scanner basis).initialState)
    (_selectedSame : _selectedInitial=(selectedUnionMachine basis).initialState) :
    instructionsPrepared basis cache same _scannerInitial _selectedInitial=DynamicModusPonensProgram.instructions basis := by
  unfold instructionsPrepared DynamicModusPonensProgram.instructions
  rw [routedInstructionsPrepared_exact basis cache same _scannerInitial _selectedInitial _scannerSame _selectedSame]


def scannerInitialRaw (basis : AuthoredAxiomUnion.Basis) : (AuthoredAxiomUnion.scanner basis).σ := by
  claim_program_literal_endpoints (AuthoredAxiomUnion.scanner basis).initialState

def selectedInitialRaw (basis : AuthoredAxiomUnion.Basis) : (selectedUnionMachine basis).σ := by
  claim_program_literal_endpoints (selectedUnionMachine basis).initialState

def scannerInitial (basis : AuthoredAxiomUnion.Basis) : (AuthoredAxiomUnion.scanner basis).σ := by
  materialized_registers (scannerInitialRaw basis)

def selectedInitial (basis : AuthoredAxiomUnion.Basis) : (selectedUnionMachine basis).σ := by
  materialized_registers (selectedInitialRaw basis)

theorem scannerInitial_exact (basis : AuthoredAxiomUnion.Basis) : scannerInitial basis=(AuthoredAxiomUnion.scanner basis).initialState := by
  simp only [scannerInitial,function_identity]
  rfl

theorem selectedInitial_exact (basis : AuthoredAxiomUnion.Basis) : selectedInitial basis=(selectedUnionMachine basis).initialState := by
  simp only [selectedInitial,function_identity]
  rfl

structure Prepared (basis : AuthoredAxiomUnion.Basis) where
  words : Snapshot (AuthoredAxiomUnion.Index basis) (fun _ => List Alphabet)
  scannerInitial : (AuthoredAxiomUnion.scanner basis).σ
  selectedInitial : (selectedUnionMachine basis).σ
  body : (DynamicModusPonensProgram.target basis).Λ → (DynamicModusPonensProgram.target basis).Stmt

@[noinline] def prepare (basis : AuthoredAxiomUnion.Basis) : Prepared basis :=
  let cache := functionCache (fun _ => []) (AuthoredAxiomUnion.words basis)
  let scannerState := scannerInitial basis
  let selectedState := selectedInitial basis
  ⟨cache,scannerState,selectedState,instructionsPrepared basis cache (function_identity _ _) scannerState selectedState⟩

theorem prepare_exact (basis : AuthoredAxiomUnion.Basis) : (prepare basis).body=DynamicModusPonensProgram.instructions basis := by
  dsimp only [prepare]
  exact instructionsPrepared_exact _ _ _ _ _ (scannerInitial_exact basis) (selectedInitial_exact basis)

def preparedStep (basis : AuthoredAxiomUnion.Basis) (compiled : Prepared basis) :=
  @Turing.TM2.step (DynamicModusPonensProgram.target basis).K (DynamicModusPonensProgram.target basis).Γ
    (DynamicModusPonensProgram.target basis).Λ (DynamicModusPonensProgram.target basis).σ
    (DynamicModusPonensProgram.keyEquality basis) compiled.body

theorem preparedStep_exact (basis : AuthoredAxiomUnion.Basis) : preparedStep basis (prepare basis)=DynamicModusPonensProgram.step basis := by
  unfold preparedStep DynamicModusPonensProgram.step
  rw [prepare_exact]

theorem instructions_original (basis : AuthoredAxiomUnion.Basis) :
    (prepare basis).body=(DynamicModusPonensProgram.target basis).m := by
  rw [prepare_exact,DynamicModusPonensProgram.instructions_exact]

private def runBody (basis : AuthoredAxiomUnion.Basis) (compiled : Prepared basis) (period : Nat) :
    Nat → Nat → (DynamicModusPonensProgram.target basis).Cfg →
      Option (Nat × (DynamicModusPonensProgram.target basis).Cfg)
  | 0,_,_ => none
  | fuel+1,used,state =>
      if state.l.isNone then some (used,state)
      else match preparedStep basis compiled state with
        | none => none
        | some next => runBody basis compiled period fuel (used+1)
            (DynamicModusPonensTreeProgram.periodicRefresh basis period (used+1) next)

private theorem runBody_exact (basis : AuthoredAxiomUnion.Basis) (period fuel used : Nat)
    (before : (DynamicModusPonensProgram.target basis).Cfg) :
    runBody basis (prepare basis) period fuel used before=DynamicModusPonensTreeProgram.run basis period fuel used before := by
  induction fuel generalizing used before with
  | zero => rfl
  | succ fuel ih =>
      simp only [runBody,DynamicModusPonensTreeProgram.run,preparedStep_exact]
      split
      · rfl
      · cases advanced : DynamicModusPonensProgram.step basis before with
        | none => rfl
        | some next => exact ih _ _

/-- Prepare fixed authored data once, then execute counted original transitions. -/
@[noinline] def run (basis : AuthoredAxiomUnion.Basis) (period fuel used : Nat)
    (before : (DynamicModusPonensProgram.target basis).Cfg) :
    Option (Nat × (DynamicModusPonensProgram.target basis).Cfg) :=
  let compiled := prepare basis
  runBody basis compiled period fuel used before

theorem run_exact (basis : AuthoredAxiomUnion.Basis) (period fuel used : Nat)
    (before : (DynamicModusPonensProgram.target basis).Cfg) :
    run basis period fuel used before=DynamicModusPonensTreeProgram.run basis period fuel used before :=
  runBody_exact basis period fuel used before

theorem run_actual (basis : AuthoredAxiomUnion.Basis) (period fuel used : Nat)
    (before : (DynamicModusPonensProgram.target basis).Cfg) {count : Nat}
    {after : (DynamicModusPonensProgram.target basis).Cfg}
    (completed : run basis period fuel used before=some (count,after)) :
    used ≤ count ∧
      (∃ path : StateTransition.EvalsToInTime (DynamicModusPonensProgram.target basis).step before (some after) (count-used),
        path.steps=count-used) ∧ after.l=none := by
  rw [run_exact] at completed
  exact DynamicModusPonensTreeProgram.run_actual basis period fuel used before completed

end Mettapedia.Languages.HOLLight.DynamicModusPonensPreparedProgram
