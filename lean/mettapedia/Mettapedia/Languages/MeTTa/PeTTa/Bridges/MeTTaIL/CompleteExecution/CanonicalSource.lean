import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.LawsSource

/-!
# Canonical forms, as a MeTTa source

`gslt_canonical.metta` computes canonical forms sorted by a name table, and
the standard form followed by the canonical form. Its pinned operations use
the same interpreted runtime as collection matching and declared laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open SpaceSemantics (Program)
open scoped ProgramQuotation
open LibraryCheck

def canonicalSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../metta/gslt/lib/gslt_canonical.metta"
    sha256 "43e88bc231cafbcf276cdd566d90a9160634f9582539c4832a6e37f55af8c9c5"

/-- Canonical operations use the shared interpreted runtime. -/
def canonicalLibrary : BridgeKit.Library := RetainedMatchingWire.interpretedLibrary

theorem canonical_checked : canonicalLibrary.check = true := RetainedMatchingWire.interpreted_checked


section CanonicalProofMetadata

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program Equation)
open Eval BridgeKit

private def canonicalProofSource : Program := (RuleExecutionProgram.interpretedPremiseSupportSources[4]'(by decide +kernel)).program

theorem canonicalProof_source_quote : canonicalProofSource = canonicalSource.program := by rfl

private def canonicalObservedInheritedHeads : List String :=
  ((canonicalProofSource.equations.flatMap (fun row => sourceLiteralHeads row.body)).filter
    (fun head => head.startsWith "gslt:" && !(canonicalProofSource.equations.map (·.head)).contains head)).eraseDups

/-- Direct outward calls derived from the actual family bodies. -/
def canonicalProofInheritedHeads : List String := ["gslt:automata:append", "gslt:rule:scope-reflective-normalize-finish", "gslt:laws:law-for", "gslt:laws:standard"]

theorem canonicalProofInheritedHeads_derived :
    canonicalObservedInheritedHeads = canonicalProofInheritedHeads := by decide +kernel

theorem canonicalProof_source_count : canonicalProofSource.equations.length = 30 := by decide +kernel

theorem canonicalProof_inherited_count : canonicalObservedInheritedHeads.length = 4 := by
  rw [canonicalProofInheritedHeads_derived]
  decide +kernel

private def canonicalScopedMetadataEquations : List Equation :=
  [RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[183]'(by decide +kernel)]

private def canonicalPriorMetadataEquations : List Equation :=
  [(RuleExecutionProgram.interpretedPremiseSupportSources[3]'(by decide +kernel)).program.equations[0]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[3]'(by decide +kernel)).program.equations[10]'(by decide +kernel)]

private def canonicalScopedMetadataDeclarations : List Atom :=
  [RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[183]'(by decide +kernel)]

private def canonicalPriorMetadataDeclarations : List Atom :=
  [(RuleExecutionProgram.interpretedPremiseSupportSources[3]'(by decide +kernel)).program.declarations[0]'(by decide +kernel),
    (RuleExecutionProgram.interpretedPremiseSupportSources[3]'(by decide +kernel)).program.declarations[10]'(by decide +kernel)]

private def canonicalMetadataBase : Program where
  equations := canonicalScopedMetadataEquations ++ canonicalPriorMetadataEquations
  declarations := canonicalScopedMetadataDeclarations ++ canonicalPriorMetadataDeclarations

/-- Bounded call and constructor metadata; execution remains in the shared Raw program. -/
def canonicalProofLibrary : Library := ⟨canonicalMetadataBase, canonicalProofSource, ["gslt:canon:"]⟩

def canonicalProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || canonicalProofLibrary.owns head || canonicalProofInheritedHeads.contains head

theorem canonicalProof_checked : canonicalProofLibrary.check = true := by decide +kernel

theorem canonicalProof_equation_count : canonicalProofLibrary.runtime.equations.length = 34 := by decide +kernel

private def canonicalPriorSources := RuleExecutionProgram.interpretedPremiseSupportSources.take 4
private def canonicalLaterSources := RuleExecutionProgram.interpretedPremiseSupportSources.drop 5

private theorem canonicalScoped_equations_indices :
    (List.finRange RuleExecutionProgram.scopedProgram.equations.length).filter (fun index => (fun row => canonicalProofHeads row.head) (RuleExecutionProgram.scopedProgram.equations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨183, by decide +kernel⟩] := by decide +kernel

private theorem canonicalScoped_equations : RuleExecutionProgram.scopedProgram.equations.filter (fun row => canonicalProofHeads row.head) = canonicalScopedMetadataEquations := by
  rw [source_filter_indices, canonicalScoped_equations_indices]
  rfl

private theorem canonicalPrior_equations_indices :
    (List.finRange (canonicalPriorSources.flatMap (fun source => source.program.equations)).length).filter (fun index => (fun row => canonicalProofHeads row.head) ((canonicalPriorSources.flatMap (fun source => source.program.equations)).get index)) =
      [⟨119, by decide +kernel⟩, ⟨129, by decide +kernel⟩] := by decide +kernel

private theorem canonicalPrior_equations : (canonicalPriorSources.flatMap (fun source => source.program.equations)).filter (fun row => canonicalProofHeads row.head) = canonicalPriorMetadataEquations := by
  rw [source_filter_indices, canonicalPrior_equations_indices]
  rfl

private theorem canonicalOwned_equations : canonicalProofSource.equations.filter (fun row => canonicalProofHeads row.head) = canonicalProofSource.equations := by
  apply List.filter_eq_self.mpr
  exact List.all_eq_true.mp (by decide +kernel)

private theorem canonicalLater_equations : (canonicalLaterSources.flatMap (fun source => source.program.equations)).filter (fun row => canonicalProofHeads row.head) = [] := by
  have checked : (canonicalLaterSources.flatMap (fun source => source.program.equations)).all (fun row => !((fun row => canonicalProofHeads row.head) row)) = true := by decide +kernel
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have rejected := List.all_eq_true.mp checked row member
  simp [kept] at rejected

private theorem canonicalSupport_equations :
    RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun source => source.program.equations) =
      (canonicalPriorSources.flatMap (fun source => source.program.equations)) ++ canonicalProofSource.equations ++ (canonicalLaterSources.flatMap (fun source => source.program.equations)) := by
  have split : RuleExecutionProgram.interpretedPremiseSupportSources =
      canonicalPriorSources ++ (RuleExecutionProgram.interpretedPremiseSupportSources[4]'(by decide +kernel)) :: canonicalLaterSources := rfl
  rw [split, List.flatMap_append, List.flatMap_cons]
  rfl

private theorem canonicalProof_physical_equations : canonicalProofLibrary.runtime.equations =
    (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
      (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram).equations.filter (fun row => canonicalProofHeads row.head) := by
  rw [PhysicalSourceAgreement.fold_equations, canonicalSupport_equations]
  simp only [List.filter_append, canonicalScoped_equations, canonicalPrior_equations,
    canonicalOwned_equations, canonicalLater_equations, List.append_nil]
  change (canonicalScopedMetadataEquations ++ canonicalPriorMetadataEquations) ++ canonicalProofSource.equations = _
  simp only [List.append_assoc]

private theorem canonicalScoped_declarations_indices :
    (List.finRange RuleExecutionProgram.scopedProgram.declarations.length).filter (fun index => (retainedCallDeclaration canonicalProofHeads) (RuleExecutionProgram.scopedProgram.declarations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨183, by decide +kernel⟩] := by decide +kernel

private theorem canonicalScoped_declarations : RuleExecutionProgram.scopedProgram.declarations.filter (retainedCallDeclaration canonicalProofHeads) = canonicalScopedMetadataDeclarations := by
  rw [source_filter_indices, canonicalScoped_declarations_indices]
  rfl

private theorem canonicalPrior_declarations_indices :
    (List.finRange (canonicalPriorSources.flatMap (fun source => source.program.declarations)).length).filter (fun index => (retainedCallDeclaration canonicalProofHeads) ((canonicalPriorSources.flatMap (fun source => source.program.declarations)).get index)) =
      [⟨119, by decide +kernel⟩, ⟨129, by decide +kernel⟩] := by decide +kernel

private theorem canonicalPrior_declarations : (canonicalPriorSources.flatMap (fun source => source.program.declarations)).filter (retainedCallDeclaration canonicalProofHeads) = canonicalPriorMetadataDeclarations := by
  rw [source_filter_indices, canonicalPrior_declarations_indices]
  rfl

private theorem canonicalOwned_declarations : canonicalProofSource.declarations.filter (retainedCallDeclaration canonicalProofHeads) = canonicalProofSource.declarations := by
  apply List.filter_eq_self.mpr
  exact List.all_eq_true.mp (by decide +kernel)

private theorem canonicalLater_declarations : (canonicalLaterSources.flatMap (fun source => source.program.declarations)).filter (retainedCallDeclaration canonicalProofHeads) = [] := by
  have checked : (canonicalLaterSources.flatMap (fun source => source.program.declarations)).all (fun row => !((retainedCallDeclaration canonicalProofHeads) row)) = true := by decide +kernel
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have rejected := List.all_eq_true.mp checked row member
  simp [kept] at rejected

private theorem canonicalSupport_declarations :
    RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun source => source.program.declarations) =
      (canonicalPriorSources.flatMap (fun source => source.program.declarations)) ++ canonicalProofSource.declarations ++ (canonicalLaterSources.flatMap (fun source => source.program.declarations)) := by
  have split : RuleExecutionProgram.interpretedPremiseSupportSources =
      canonicalPriorSources ++ (RuleExecutionProgram.interpretedPremiseSupportSources[4]'(by decide +kernel)) :: canonicalLaterSources := rfl
  rw [split, List.flatMap_append, List.flatMap_cons]
  rfl

private theorem canonicalProof_physical_declarations : canonicalProofLibrary.runtime.declarations =
    (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
      (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram).declarations.filter (retainedCallDeclaration canonicalProofHeads) := by
  rw [PhysicalSourceAgreement.fold_declarations, canonicalSupport_declarations]
  simp only [List.filter_append, canonicalScoped_declarations, canonicalPrior_declarations,
    canonicalOwned_declarations, canonicalLater_declarations, List.append_nil]
  change (canonicalScopedMetadataDeclarations ++ canonicalPriorMetadataDeclarations) ++ canonicalProofSource.declarations = _
  simp only [List.append_assoc]

theorem canonicalProof_agreement :
    ProgramAgreementOn canonicalProofHeads canonicalProofLibrary.runtime RuleExecutionProgram.interpretedPremiseProgram := by
  have physical : ProgramAgreementOn canonicalProofHeads canonicalProofLibrary.runtime
      (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
        (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram) :=
    fragment_agreement _ _ canonicalProof_physical_equations canonicalProof_physical_declarations
      (fun _ supported => supported)
  exact agreement_trans physical
    (agreement_mono (fun _ _ => rfl) PhysicalSourceAgreement.physical_interpreted_agreement)

/-- The metadata does not assert closure of inherited primitive bodies. -/
theorem canonicalProof_not_closed : ¬ ProgramClosed canonicalProofHeads canonicalProofLibrary.runtime := by
  intro closed
  let row := canonicalMetadataBase.equations[3]'(by decide +kernel)
  have member : row ∈ canonicalProofLibrary.runtime.equations := by
    apply List.mem_append_left
    exact List.getElem_mem _
  have supported : canonicalProofHeads row.head = true := by decide +kernel
  have outside : codeWithin canonicalProofHeads row.body = false := by decide +kernel
  have inside := closed.bodies row member supported
  rw [outside] at inside
  cases inside

#print axioms canonicalProof_source_quote
#print axioms canonicalProofInheritedHeads_derived
#print axioms canonicalProof_source_count
#print axioms canonicalProof_inherited_count
#print axioms canonicalProof_checked
#print axioms canonicalProof_equation_count
#print axioms canonicalProof_agreement
#print axioms canonicalProof_not_closed

end CanonicalProofMetadata

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
