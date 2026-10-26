import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution.Source

/-!
# The collection laws, as a MeTTa source

`gslt_collection_laws.metta` supplies the standard form of declared collection
and scope-extrusion laws. Its pinned operations share the interpreted runtime
with matching, typed descent and the complete machine.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution

open SpaceSemantics (Program)
open Eval (codeWithin)
open scoped ProgramQuotation

def lawsSource : ProgramQuotation.QuotedProgram :=
  petta_source_file%
    "../../../../../../../../../metta/gslt/lib/gslt_collection_laws.metta"
    sha256 "24a3e67c782270ba3ac7633d38c91b76ec14b2d4bd37269f811776e64fd30212"

/-- The declared-law operations use the shared interpreted runtime. -/
def lawsLibrary : BridgeKit.Library := RetainedMatchingWire.interpretedLibrary

/-! ## The checks, decided by the kernel file by file -/

set_option maxRecDepth 100000

namespace LibraryCheck

/-- A program's bodies keep to the heads a library inherits. -/
abbrev keptBy (L : BridgeKit.Library) (program : Program) : Bool :=
  program.equations.all fun equation => L.inherited equation.head && codeWithin L.inherited equation.body

theorem keptBy_append (L : BridgeKit.Library) (first second : Program) :
    keptBy L (first.append second) = (keptBy L first && keptBy L second) := by
  simp [keptBy, SpaceSemantics.Program.append, List.all_append]

/-- A library's check, from its own source and its base file by file. -/
theorem check_of (L : BridgeKit.Library) (binding : L.inherited "let" = true)
    (base : keptBy L L.base = true)
    (equations : (L.source.equations.all fun equation => L.owns equation.head) = true)
    (declarations : (L.source.declarations.all fun declaration =>
      (BridgeKit.arrowHead declaration).all L.owns) = true) : L.check = true := by
  simp only [BridgeKit.Library.check, Bool.and_eq_true]
  exact ⟨⟨⟨binding, base⟩, equations⟩, declarations⟩

end LibraryCheck

theorem laws_checked : lawsLibrary.check = true := RetainedMatchingWire.interpreted_checked


section LawsProofMetadata

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open SpaceSemantics (Program Equation)
open Eval BridgeKit

private def lawsProofSource : Program := (RuleExecutionProgram.interpretedPremiseSupportSources[3]'(by decide +kernel)).program

theorem lawsProof_source_quote : lawsProofSource = lawsSource.program := by rfl

private def lawsObservedInheritedHeads : List String :=
  ((lawsProofSource.equations.flatMap (fun row => sourceLiteralHeads row.body)).filter
    (fun head => head.startsWith "gslt:" && !(lawsProofSource.equations.map (·.head)).contains head)).eraseDups

/-- Direct outward calls derived from the actual family bodies. -/
def lawsProofInheritedHeads : List String := ["gslt:automata:append", "gslt:rule:lift-bvars-list", "gslt:deep:nodes-list", "gslt:automata:length"]

theorem lawsProofInheritedHeads_derived :
    lawsObservedInheritedHeads = lawsProofInheritedHeads := by decide +kernel

theorem lawsProof_source_count : lawsProofSource.equations.length = 11 := by decide +kernel

theorem lawsProof_inherited_count : lawsObservedInheritedHeads.length = 4 := by
  rw [lawsProofInheritedHeads_derived]
  decide +kernel

private def lawsScopedMetadataEquations : List Equation :=
  [RuleExecutionProgram.scopedProgram.equations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[1]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.equations[81]'(by decide +kernel)]

private def lawsPriorMetadataEquations : List Equation :=
  [(RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel)).program.equations[1]'(by decide +kernel)]

private def lawsScopedMetadataDeclarations : List Atom :=
  [RuleExecutionProgram.scopedProgram.declarations[0]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[1]'(by decide +kernel),
    RuleExecutionProgram.scopedProgram.declarations[81]'(by decide +kernel)]

private def lawsPriorMetadataDeclarations : List Atom :=
  [(RuleExecutionProgram.interpretedPremiseSupportSources[2]'(by decide +kernel)).program.declarations[1]'(by decide +kernel)]

private def lawsMetadataBase : Program where
  equations := lawsScopedMetadataEquations ++ lawsPriorMetadataEquations
  declarations := lawsScopedMetadataDeclarations ++ lawsPriorMetadataDeclarations

/-- Bounded call and constructor metadata; execution remains in the shared Raw program. -/
def lawsProofLibrary : Library := ⟨lawsMetadataBase, lawsProofSource, ["gslt:laws:"]⟩

def lawsProofHeads (head : String) : Bool :=
  !head.startsWith "gslt:" || lawsProofLibrary.owns head || lawsProofInheritedHeads.contains head

theorem lawsProof_checked : lawsProofLibrary.check = true := by decide +kernel

theorem lawsProof_equation_count : lawsProofLibrary.runtime.equations.length = 15 := by decide +kernel

private def lawsPriorSources := RuleExecutionProgram.interpretedPremiseSupportSources.take 3
private def lawsLaterSources := RuleExecutionProgram.interpretedPremiseSupportSources.drop 4

private theorem lawsScoped_equations_indices :
    (List.finRange RuleExecutionProgram.scopedProgram.equations.length).filter (fun index => (fun row => lawsProofHeads row.head) (RuleExecutionProgram.scopedProgram.equations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨81, by decide +kernel⟩] := by decide +kernel

private theorem lawsScoped_equations : RuleExecutionProgram.scopedProgram.equations.filter (fun row => lawsProofHeads row.head) = lawsScopedMetadataEquations := by
  rw [source_filter_indices, lawsScoped_equations_indices]
  rfl

private theorem lawsPrior_equations_indices :
    (List.finRange (lawsPriorSources.flatMap (fun source => source.program.equations)).length).filter (fun index => (fun row => lawsProofHeads row.head) ((lawsPriorSources.flatMap (fun source => source.program.equations)).get index)) =
      [⟨35, by decide +kernel⟩] := by decide +kernel

private theorem lawsPrior_equations : (lawsPriorSources.flatMap (fun source => source.program.equations)).filter (fun row => lawsProofHeads row.head) = lawsPriorMetadataEquations := by
  rw [source_filter_indices, lawsPrior_equations_indices]
  rfl

private theorem lawsOwned_equations : lawsProofSource.equations.filter (fun row => lawsProofHeads row.head) = lawsProofSource.equations := by
  apply List.filter_eq_self.mpr
  exact List.all_eq_true.mp (by decide +kernel)

private theorem lawsLater_equations : (lawsLaterSources.flatMap (fun source => source.program.equations)).filter (fun row => lawsProofHeads row.head) = [] := by
  have checked : (lawsLaterSources.flatMap (fun source => source.program.equations)).all (fun row => !((fun row => lawsProofHeads row.head) row)) = true := by decide +kernel
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have rejected := List.all_eq_true.mp checked row member
  simp [kept] at rejected

private theorem lawsSupport_equations :
    RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun source => source.program.equations) =
      (lawsPriorSources.flatMap (fun source => source.program.equations)) ++ lawsProofSource.equations ++ (lawsLaterSources.flatMap (fun source => source.program.equations)) := by
  have split : RuleExecutionProgram.interpretedPremiseSupportSources =
      lawsPriorSources ++ (RuleExecutionProgram.interpretedPremiseSupportSources[3]'(by decide +kernel)) :: lawsLaterSources := rfl
  rw [split, List.flatMap_append, List.flatMap_cons]
  rfl

private theorem lawsProof_physical_equations : lawsProofLibrary.runtime.equations =
    (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
      (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram).equations.filter (fun row => lawsProofHeads row.head) := by
  rw [PhysicalSourceAgreement.fold_equations, lawsSupport_equations]
  simp only [List.filter_append, lawsScoped_equations, lawsPrior_equations,
    lawsOwned_equations, lawsLater_equations, List.append_nil]
  change (lawsScopedMetadataEquations ++ lawsPriorMetadataEquations) ++ lawsProofSource.equations = _
  simp only [List.append_assoc]

private theorem lawsScoped_declarations_indices :
    (List.finRange RuleExecutionProgram.scopedProgram.declarations.length).filter (fun index => (retainedCallDeclaration lawsProofHeads) (RuleExecutionProgram.scopedProgram.declarations.get index)) =
      [⟨0, by decide +kernel⟩, ⟨1, by decide +kernel⟩, ⟨81, by decide +kernel⟩] := by decide +kernel

private theorem lawsScoped_declarations : RuleExecutionProgram.scopedProgram.declarations.filter (retainedCallDeclaration lawsProofHeads) = lawsScopedMetadataDeclarations := by
  rw [source_filter_indices, lawsScoped_declarations_indices]
  rfl

private theorem lawsPrior_declarations_indices :
    (List.finRange (lawsPriorSources.flatMap (fun source => source.program.declarations)).length).filter (fun index => (retainedCallDeclaration lawsProofHeads) ((lawsPriorSources.flatMap (fun source => source.program.declarations)).get index)) =
      [⟨35, by decide +kernel⟩] := by decide +kernel

private theorem lawsPrior_declarations : (lawsPriorSources.flatMap (fun source => source.program.declarations)).filter (retainedCallDeclaration lawsProofHeads) = lawsPriorMetadataDeclarations := by
  rw [source_filter_indices, lawsPrior_declarations_indices]
  rfl

private theorem lawsOwned_declarations : lawsProofSource.declarations.filter (retainedCallDeclaration lawsProofHeads) = lawsProofSource.declarations := by
  apply List.filter_eq_self.mpr
  exact List.all_eq_true.mp (by decide +kernel)

private theorem lawsLater_declarations : (lawsLaterSources.flatMap (fun source => source.program.declarations)).filter (retainedCallDeclaration lawsProofHeads) = [] := by
  have checked : (lawsLaterSources.flatMap (fun source => source.program.declarations)).all (fun row => !((retainedCallDeclaration lawsProofHeads) row)) = true := by decide +kernel
  apply List.filter_eq_nil_iff.mpr
  intro row member kept
  have rejected := List.all_eq_true.mp checked row member
  simp [kept] at rejected

private theorem lawsSupport_declarations :
    RuleExecutionProgram.interpretedPremiseSupportSources.flatMap (fun source => source.program.declarations) =
      (lawsPriorSources.flatMap (fun source => source.program.declarations)) ++ lawsProofSource.declarations ++ (lawsLaterSources.flatMap (fun source => source.program.declarations)) := by
  have split : RuleExecutionProgram.interpretedPremiseSupportSources =
      lawsPriorSources ++ (RuleExecutionProgram.interpretedPremiseSupportSources[3]'(by decide +kernel)) :: lawsLaterSources := rfl
  rw [split, List.flatMap_append, List.flatMap_cons]
  rfl

private theorem lawsProof_physical_declarations : lawsProofLibrary.runtime.declarations =
    (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
      (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram).declarations.filter (retainedCallDeclaration lawsProofHeads) := by
  rw [PhysicalSourceAgreement.fold_declarations, lawsSupport_declarations]
  simp only [List.filter_append, lawsScoped_declarations, lawsPrior_declarations,
    lawsOwned_declarations, lawsLater_declarations, List.append_nil]
  change (lawsScopedMetadataDeclarations ++ lawsPriorMetadataDeclarations) ++ lawsProofSource.declarations = _
  simp only [List.append_assoc]

theorem lawsProof_agreement :
    ProgramAgreementOn lawsProofHeads lawsProofLibrary.runtime RuleExecutionProgram.interpretedPremiseProgram := by
  have physical : ProgramAgreementOn lawsProofHeads lawsProofLibrary.runtime
      (RuleExecutionProgram.interpretedPremiseSupportSources.foldl
        (fun loaded source => loaded.append source.program) RuleExecutionProgram.scopedProgram) :=
    fragment_agreement _ _ lawsProof_physical_equations lawsProof_physical_declarations
      (fun _ supported => supported)
  exact agreement_trans physical
    (agreement_mono (fun _ _ => rfl) PhysicalSourceAgreement.physical_interpreted_agreement)

/-- The metadata does not assert closure of inherited primitive bodies. -/
theorem lawsProof_not_closed : ¬ ProgramClosed lawsProofHeads lawsProofLibrary.runtime := by
  intro closed
  let row := lawsMetadataBase.equations[2]'(by decide +kernel)
  have member : row ∈ lawsProofLibrary.runtime.equations := by
    apply List.mem_append_left
    exact List.getElem_mem _
  have supported : lawsProofHeads row.head = true := by decide +kernel
  have outside : codeWithin lawsProofHeads row.body = false := by decide +kernel
  have inside := closed.bodies row member supported
  rw [outside] at inside
  cases inside

#print axioms lawsProof_source_quote
#print axioms lawsProofInheritedHeads_derived
#print axioms lawsProof_source_count
#print axioms lawsProof_inherited_count
#print axioms lawsProof_checked
#print axioms lawsProof_equation_count
#print axioms lawsProof_agreement
#print axioms lawsProof_not_closed

end LawsProofMetadata

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.CompleteExecution
