import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendSource
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestPackageControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SchemaTableLinking

/-!
# The informative generated vector package in append checking

The actual generated vector candidate supplies its declarations and two
ordered computation schemas. Joining the independently checked natural prefix
recovers the reference table, and the existing level instance gives the
dependent append checking policy. The finite executable specialization is
proved equal to that generated policy; no new eliminator is constructed.

The host payload used by the source inventory does not replace the explicit
guest type parameter. This selected comparison does not authorize all raw
computations, establish general compilation, or supply the annotated-calculus
comparison. Candidate and uniform computational authority remain distinct.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.AppendChecking

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies
open Declaration.IndexedFamily

abbrev naturalTable := NativeNaturalVectorFamilies.Checking.table.take 2
abbrev vectorTable := NativeNaturalVectorFamilies.Checking.table.drop 2

/-- This is the actual informative package generated and checked in the
authoring lane. The guest element type remains a lexical parameter. -/
noncomputable abbrev candidate := Guest.PackageControls.vectorCandidate

noncomputable def generatedTable : AlgebraicSchema.SchemaTable Tower.Head :=
  naturalTable ++ Checking.table (Checking.candidateSchemas candidate)

theorem generated_table_reference : generatedTable = NativeNaturalVectorFamilies.Checking.table := by
  unfold generatedTable
  rw [Guest.PackageControls.candidate_vector_table_reference]
  exact List.take_append_drop 2 _

noncomputable def generatedLibrary : List (DeclName × Declaration.Entry Tower.Head) :=
  Guest.Package.library (Guest.TypedControls.indexSyntax Bool)
    (Guest.DeclarationControls.vectorParameters Bool) Guest.DeclarationControls.vectorNames
    (IndexedInductiveNatVec.Vectors.admitted Bool) Guest.PackageControls.vectorPrior

theorem generated_library_reference : generatedLibrary = NativeNaturalVectorFamilies.declarations := by
  change Guest.PackageControls.vectorPrior ++ Guest.DeclarationControls.vectorEntries Bool = _
  rw [Guest.DeclarationControls.vector_entries_reference]
  exact List.take_append_drop 4 _

theorem candidate_entries_reference :
    candidate.signature.entries =
      (Declaration.Signature.ofList NativeNaturalVectorFamilies.declarations).entries := by
  change (Declaration.Signature.ofList generatedLibrary).entries = _
  rw [generated_library_reference]

theorem candidate_root_inclusion {n : Nat} {left right : Tower.Tm n}
    (step : candidate.signature.computation.step left right) :
    rawSignature.computation.step left right := by
  change (SchemaTableConversionCode.root vectorTable (fun _ => true)).step left right at step
  have joined := SchemaTableConversionCode.Linking.root_inclusion
    (SchemaTableConversionCode.Linking.right naturalTable vectorTable) (fun _ => true) step
  have tables : naturalTable ++ vectorTable = NativeNaturalVectorFamilies.Checking.table :=
    List.take_append_drop 2 _
  rw [tables] at joined
  obtain ⟨evidence⟩ := joined
  exact ⟨Checking.realizeEvidence NativeNaturalVectorFamilies.Checking.schemas evidence⟩

theorem candidate_extension : candidate.signature.Extends rawSignature where
  entries := by
    intro name entry found
    rw [candidate_entries_reference] at found
    exact found
  computation := candidate_root_inclusion

/-- The declared generated calculus includes into the independently authored
reference calculus. This is forward judgment preservation, not conservativity
or authorization of every raw computation. -/
theorem candidate_judgment_inclusion {n : Nat} {context : Tower.Ctx n}
    {term type : Tower.Tm n}
    (derived : FormationSensitive.Judgment
      (Declaration.extendRules Tower.rules candidate.signature) context term type) :
    FormationSensitive.Judgment NativeNaturalVectorFamilies.rules context term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
    derived.mapHead (Declaration.extensionMorphism Tower.rules candidate_extension)

/-- The same judgment route composes with the actual maximum-level
instantiation used by append; contexts, terms and result types all move. -/
theorem candidate_judgment_to_program {n : Nat} {context : Tower.Ctx n}
    {term type : Tower.Tm n}
    (derived : FormationSensitive.Judgment
      (Declaration.extendRules Tower.rules candidate.signature) context term type) :
    FormationSensitive.Judgment Programs.rules
      (RussellTarski.substLevelsCtx Programs.levels context)
      (RussellTarski.substLevelsTm Programs.levels term)
      (RussellTarski.substLevelsTm Programs.levels type) :=
  Programs.judgment_map (candidate_judgment_inclusion derived)

/-- Permission addresses are ordinals of the joined table, after source
bounds have been checked. Universe instantiation reuses the admitted morphism. -/
noncomputable def generatedSignature (allowed : Nat → Bool) : Declaration.Signature Tower.Head :=
  candidate.signature.instantiateLevels Programs.levels
    (SchemaTableConversionCode.root generatedTable (fun index => allowed index.val))

def selection (allowed : Nat → Bool) : Programs.ComputationProfiles.Selection :=
  fun index => allowed index.val

local instance (allowed : Nat → Bool) :
    DecidableRel (Programs.ComputationProfiles.rules (selection allowed)).headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance (allowed : Nat → Bool) :
    DecidablePred (Programs.ComputationProfiles.rules (selection allowed)).isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance (allowed : Nat → Bool) : ∀ u v w,
    Decidable ((Programs.ComputationProfiles.rules (selection allowed)).join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance (allowed : Nat → Bool) :
    DecidableRel (Programs.ComputationProfiles.rules (selection allowed)).cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance (allowed : Nat → Bool) :
    DecidableRel (Programs.ComputationProfiles.rules (selection allowed)).headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

/-- The executable table is the existing finite reference specialization.
Its entries and roots both agree with the generated package, not merely names. -/
theorem signature_comparison (allowed : Nat → Bool) :
    generatedSignature allowed = Programs.ComputationProfiles.signature (selection allowed) := by
  change (Declaration.Signature.ofList generatedLibrary).instantiateLevels Programs.levels
    (SchemaTableConversionCode.root generatedTable (fun index => allowed index.val)) = _
  rw [generated_library_reference, generated_table_reference]
  rfl

theorem textual_candidate_table :
    (((OperationSource.selectModule AppendSource.IndexedNatVecAppend.module).bind fun source =>
      ModuleSource.IndexedNatVecSource.admitModule Bool AppendSource.names source.declarations).map
        (Guest.Package.table (Guest.TypedControls.indexSyntax Bool)
          (Guest.DeclarationControls.vectorParameters Bool) Guest.DeclarationControls.vectorNames)) =
      some (Checking.table (Checking.candidateSchemas candidate)) := by
  rw [AppendSource.text_admitted]
  rfl

/-- The same actual declaration source supplies the entire opaque library,
not merely two equations with the expected names. -/
theorem textual_candidate_library :
    (((OperationSource.selectModule AppendSource.IndexedNatVecAppend.module).bind fun source =>
      ModuleSource.IndexedNatVecSource.admitModule Bool AppendSource.names source.declarations).map
        (fun admitted => Guest.Package.library (Guest.TypedControls.indexSyntax Bool)
          (Guest.DeclarationControls.vectorParameters Bool) Guest.DeclarationControls.vectorNames
          admitted Guest.PackageControls.vectorPrior)) = some generatedLibrary := by
  rw [AppendSource.text_admitted]
  rfl

def naturalOnly (row : Nat) : Bool := decide (row < 2)

theorem textual_append_typed (term : Tower.Tm 0) (compiled : AppendSource.proposedAppend = some term) :
    FormationSensitive.Judgment
      (Declaration.extendRules Tower.rules (generatedSignature naturalOnly))
      .nil term Programs.appendType := by
  rw [signature_comparison]
  exact AppendSource.append_typed_naturalOnly term compiled

def replayProposal (allowed : Nat → Bool) (proposal : Option (Tower.Tm 0)) : Bool :=
  match proposal with
  | none => false
  | some term => FormationSensitiveElaboration.replay
      (Programs.ComputationProfiles.rules (selection allowed))
      (Programs.ComputationProfiles.decoder (selection allowed))
      .nil term Programs.appendType Programs.appendEvidence

/-- The live source reader submits its actual proposed term through the same
finite decoder. No fixture term replaces the proposal at this boundary. -/
def replaySource (allowed : Nat → Bool) (source : ModuleSource.Module) : Bool :=
  replayProposal allowed ((AppendSource.propose .declaredNullary source).map (·.appendFunction))

def replay (allowed : Nat → Bool) : Bool :=
  replaySource allowed AppendSource.IndexedNatVecAppend.module

theorem replayProposal_sound (allowed : Nat → Bool) (proposal : Option (Tower.Tm 0))
    (accepted : replayProposal allowed proposal = true) :
    ∃ term, proposal = some term ∧
      FormationSensitive.Judgment
        (Declaration.extendRules Tower.rules (generatedSignature allowed))
        .nil term Programs.appendType := by
  cases proposed : proposal with
  | none => simp [replayProposal, proposed] at accepted
  | some term =>
      refine ⟨term, rfl, ?_⟩
      rw [signature_comparison]
      exact FormationSensitiveElaboration.replay_sound _ _
        (by simpa only [replayProposal, proposed] using accepted)

theorem replaySource_sound (allowed : Nat → Bool) (source : ModuleSource.Module)
    (accepted : replaySource allowed source = true) :
    ∃ proposed, AppendSource.propose .declaredNullary source = some proposed ∧
      FormationSensitive.Judgment
        (Declaration.extendRules Tower.rules (generatedSignature allowed))
        .nil proposed.appendFunction Programs.appendType := by
  obtain ⟨term, produced, typed⟩ := replayProposal_sound allowed _ accepted
  obtain ⟨proposed, found, same⟩ := Option.map_eq_some_iff.mp produced
  exact ⟨proposed, found, same ▸ typed⟩

theorem replay_sound (allowed : Nat → Bool) (accepted : replay allowed = true) :
    ∃ term, AppendSource.proposedAppend = some term ∧
      FormationSensitive.Judgment
        (Declaration.extendRules Tower.rules (generatedSignature allowed))
        .nil term Programs.appendType := by
  exact replayProposal_sound allowed AppendSource.proposedAppend accepted

/-- A vector citation is first validated in the candidate's own two-row
inventory, then relocated past the natural prefix. -/
def linkVector {n : Nat} (code : SchemaTableConversionCode.Code Tower.Head n) :=
  SchemaTableConversionCode.Linking.relocate
    (SchemaTableConversionCode.Linking.right naturalTable vectorTable) code

theorem linked_vector_replay {n : Nat}
    (allowed : Fin (naturalTable ++ vectorTable).length → Bool)
    (code : SchemaTableConversionCode.Code Tower.Head n) :
    (linkVector code).bind (SchemaTableConversionCode.decode (naturalTable ++ vectorTable) allowed) =
      SchemaTableConversionCode.decode vectorTable
        (fun index => allowed ((SchemaTableConversionCode.Linking.right naturalTable vectorTable).address index))
        code := SchemaTableConversionCode.Linking.decode_relocate _ _ _

def nilCode : SchemaTableConversionCode.Code Tower.Head 4 :=
  ⟨0, List.ofFn (fun index : Fin 4 => .var index)⟩

def consCode : SchemaTableConversionCode.Code Tower.Head 7 :=
  ⟨1, List.ofFn (fun index : Fin 7 => .var index)⟩

def linkedCheck {n : Nat} (allowed : Nat → Bool)
    (code : SchemaTableConversionCode.Code Tower.Head n) : Bool :=
  ((linkVector code).bind (SchemaTableConversionCode.decode
    NativeNaturalVectorFamilies.Checking.table (selection allowed))).isSome

def verdicts : List (String × Bool) := [
  ("textual append checks against the generated package policy", replay naturalOnly),
  ("vector-only rows do not check this append typing evidence", !(replay (fun row => decide (2 ≤ row)))),
  ("generated nil citation relocates to row two", (linkVector nilCode).map (·.row) == some 2),
  ("generated cons citation relocates to row three", (linkVector consCode).map (·.row) == some 3),
  ("full computation permits generated vector nil", linkedCheck (fun _ => true) nilCode),
  ("full computation permits generated vector cons", linkedCheck (fun _ => true) consCode),
  ("checking-only policy refuses generated vector computation", !(linkedCheck naturalOnly nilCode)),
  ("source-invalid vector citation refuses before global lookup", (linkVector
    ({ nilCode with row := 2 })).isNone),
  ("the same bare global row would name vector nil", (SchemaTableConversionCode.decode
    NativeNaturalVectorFamilies.Checking.table (selection (fun _ => true))
    ({ nilCode with row := 2 })).isSome),
  ("linked cons still checks every explicit argument", !(linkedCheck (fun _ => true)
    { consCode with arguments := consCode.arguments.take 6 }))]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

theorem replay_naturalOnly : replay naturalOnly = true :=
  (List.all_eq_true.mp all_verdicts) _ (List.get_mem verdicts ⟨0, by decide⟩)

end Mettapedia.GSLT.LanguageDef.IndexedInductive.AppendChecking
