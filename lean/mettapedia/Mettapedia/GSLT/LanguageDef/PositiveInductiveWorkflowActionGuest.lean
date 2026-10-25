import Mettapedia.GSLT.LanguageDef.ModuleSource.MutualWorkflowActionLowering
import Mettapedia.GSLT.LanguageDef.PositiveInductiveBlockBridge
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestPackageControls

/-!
# Typed object guest for the textual Workflow/Action block

The accepted two-family `.module` source erases to a direct Boolean-indexed
polynomial.  This module sends that exact direct block through the existing
indexed-family declaration generator.  It produces an opaque family, four
constructors, a dependent eliminator, and one typed proof-relevant iota receipt
per constructor.

Boolean family tags are represented by zero and successor-zero in the guest
natural index type.  The authored permission payload is retained as its own
opaque object type rather than identified with that tag encoding.  The source
bridge and constructor inventory are exact; a semantic equivalence between
the source Boolean payload and an object Boolean implementation is a separate
interpretation obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveWorkflowActionGuest

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Declaration Declaration.IndexedFamily
open IndexedInductive.Guest
open IndexedInductive.Guest.Declarations

namespace Source

abbrev interface := PositiveInductiveScenarios.Workflow.interface

def admitted : IndexedInductive.Admitted interface [] :=
  ⟨[ ⟨"done", .result false⟩
    , ⟨"schedule", .recursive true (.result false)⟩
    , ⟨"action", .data .action (.result true)⟩
    , ⟨"subworkflow", .recursive false (.result true)⟩ ], by decide⟩

/-- The two textual headers and the direct indexed guest compiler select the
same complete polynomial, including both cross-family child indices. -/
theorem textual_erasure_eq_direct_bridge :
    ModuleSource.MutualWorkflowActionLowering.Controls.block.erase =
      PositiveInductiveBlockBridge.Direct.admitted 0 admitted := by
  rfl

theorem textual_module_admitted :
    ModuleSource.MutualWorkflowActionLowering.lowerModule
        ModuleSource.MutualWorkflowActionLowering.Controls.textualModule =
      some ModuleSource.MutualWorkflowActionLowering.Controls.resolvedModule :=
  ModuleSource.MutualWorkflowActionLowering.Controls.module_roundtrip

end Source

abbrev baseDecoder := IndexedInductive.Guest.DeclarationControls.baseDecoder
abbrev choices := IndexedInductive.Guest.DeclarationControls.choices

def permissionName : DeclName := `Generated.WorkflowAction.Permission

def permissionTm {n : Nat} : Tower.Tm n := .const permissionName

def tag {n : Nat} (value : Bool) : Tower.Tm n :=
  if value then NativeNaturalVectorFamilies.succApp NativeNaturalVectorFamilies.zeroTm
  else NativeNaturalVectorFamilies.zeroTm

def indices : IndexSyntax Source.interface Tower.Head where
  term expression _ := tag expression
  substitute := by
    intro context n m expression environment substitution
    cases expression <;> rfl

def names : Names where
  family := `Generated.WorkflowAction
  constructor name := .str `Generated.WorkflowAction name
  eliminator := `Generated.WorkflowAction.eliminate

def parameters : Parameters Source.interface Tower.Head 0 where
  context := .nil
  dataType
    | .action => permissionTm
  indexType := NativeNaturalVectorFamilies.natTm
  familyUniverse := .sort Tower.zero
  motiveUniverse := .sort Tower.zero

def permissionEntry : DeclName × Entry Tower.Head :=
  (permissionName, ⟨sortTm Tower.zero, none⟩)

def prior : List (DeclName × Entry Tower.Head) :=
  NativeNaturalVectorFamilies.declarations.take 3 ++ [permissionEntry]

def generated := entries indices parameters names Source.admitted
def library := prior ++ generated

abbrev opaqueSignature : Signature Tower.Head := Signature.ofList library
abbrev signature : Signature Tower.Head :=
  Package.signature indices parameters names Source.admitted prior
abbrev rules := extendRules Tower.rules opaqueSignature
def decoder := DeclarationConversionCode.ofList Tower.rules baseDecoder library

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem libraryAccepted :
    IndexedInductive.Guest.DeclarationControls.accepted [] library = true := by
  decide +kernel

theorem library_admitted :
    DeclarationAdmissionReplay.Admitted Tower.rules [] library :=
  IndexedInductive.Guest.DeclarationControls.accepted_sound _ _ libraryAccepted

private theorem prior_opaque : ∀ item ∈ prior, item.2.value? = none := by
  intro item member
  simp only [prior, NativeNaturalVectorFamilies.declarations,
    List.take_succ_cons, List.take_zero, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with priorMember | permissionMember
  · rcases priorMember with rfl | rfl | rfl <;> rfl
  · rcases permissionMember with rfl
    rfl

private theorem indices_free : Types.IndexFree indices names.family := by
  intro context n expression environment free
  cases expression <;> unfold indices tag
  · exact .const (by decide)
  · exact .app (.const (by decide)) (.const (by decide))

private theorem data_free : ∀ sort, FreeOf names.family (parameters.dataType sort) := by
  intro sort
  cases sort
  exact .const (by decide)

noncomputable def publishedCandidate : Option (Candidate Tower.rules) :=
  Package.fromAdmitted indices parameters names Tower.rules baseDecoder choices 64 prior
    prior_opaque indices_free trivial data_free Source.admitted

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem publishedCandidate_isSome : publishedCandidate.isSome = true := by
  decide +kernel

noncomputable def candidate : Candidate Tower.rules :=
  publishedCandidate.get (by simpa using publishedCandidate_isSome)

theorem publishedCandidate_eq : publishedCandidate = some candidate :=
  (Option.some_get (by simpa using publishedCandidate_isSome)).symm

theorem candidate_table :
    Checking.table (Checking.candidateSchemas candidate) =
      Package.table indices parameters names Source.admitted :=
  Package.fromAdmitted_sound indices parameters names Tower.rules baseDecoder choices 64 prior
    prior_opaque indices_free trivial data_free Source.admitted candidate publishedCandidate_eq

theorem signature_formed : signature.Formed Tower.rules := by
  apply Package.formed _ _ _ _ Tower.rules _ library_admitted prior_opaque

def rowsChecked : Bool :=
  Package.checkRows indices parameters names Source.admitted Tower.rules
    baseDecoder choices 64 prior

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem rows_checked : rowsChecked = true := by
  decide +kernel

private theorem package_rows_checked :
    Package.checkRows indices parameters names Source.admitted Tower.rules
      baseDecoder choices 64 prior = true := by
  simpa [rowsChecked] using rows_checked

noncomputable def schemas := Checking.candidateSchemas candidate

theorem schemas_length : schemas.length = 4 := by
  have lengths := congrArg List.length candidate_table
  calc
    schemas.length = Source.admitted.constructors.length := by
      simpa [schemas, Checking.table, Package.table] using lengths
    _ = 4 := rfl

/-- Each address returns the exact typed proof-relevant receipt generated from
the corresponding source constructor. -/
noncomputable def typedReceiptAt
    (index : Fin (Checking.table schemas).length) :=
  Checking.receiptAt schemas index

noncomputable def iotaRules :=
  Package.rules indices parameters names Source.admitted Tower.rules
    baseDecoder choices 64 prior rows_checked

theorem iota_rule_names :
    iotaRules.map IotaRule.constructorName =
      [ names.constructor "done"
      , names.constructor "schedule"
      , names.constructor "action"
      , names.constructor "subworkflow" ] := by
  rfl

def termAccepted {n : Nat} (context : Tower.Ctx n)
    (term type : Tower.Tm n) : Bool :=
  (FormationSensitiveElaboration.elaborate rules decoder choices 64 context term type).isSome

def family {n : Nat} (isAction : Bool) : Tower.Tm n :=
  .app (.const names.family) (tag isAction)

def done : Tower.Tm 0 := .const (names.constructor "done")
def schedule (next : Tower.Tm 0) : Tower.Tm 0 :=
  .app (.const (names.constructor "schedule")) next
def action {n : Nat} (permitted : Tower.Tm n) : Tower.Tm n :=
  .app (.const (names.constructor "action")) permitted
def subworkflow (plan : Tower.Tm 0) : Tower.Tm 0 :=
  .app (.const (names.constructor "subworkflow")) plan

def permissionContext : Tower.Ctx 1 := .snoc .nil permissionTm

def verdicts : List (String × Bool) :=
  [ ("textual mutual source reaches the direct guest block",
      (ModuleSource.MutualWorkflowActionLowering.lowerModule
        ModuleSource.MutualWorkflowActionLowering.Controls.textualModule).isSome)
  , ("generated workflow/action declarations form",
      IndexedInductive.Guest.DeclarationControls.accepted [] library)
  , ("all four canonical iota endpoints form without iota authority",
      rowsChecked)
  , ("done inhabits Workflow", termAccepted .nil done (family false))
  , ("schedule accepts an Action child",
      termAccepted .nil (schedule (subworkflow done)) (family false))
  , ("subworkflow accepts a Workflow child",
      termAccepted .nil (subworkflow done) (family true))
  , ("action accepts its opaque permission payload",
      termAccepted permissionContext (action (.var 0)) (family true))
  , ("schedule refuses a Workflow child",
      !(termAccepted .nil (schedule done) (family false))) ]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem verdicts_all : verdicts.all Prod.snd = true := by
  decide +kernel

section AxiomAudit

#print axioms Source.textual_erasure_eq_direct_bridge
#print axioms Source.textual_module_admitted
#print axioms library_admitted
#print axioms publishedCandidate_isSome
#print axioms publishedCandidate_eq
#print axioms candidate_table
#print axioms signature_formed
#print axioms rows_checked
#print axioms schemas_length
#print axioms typedReceiptAt
#print axioms iota_rule_names
#print axioms verdicts_all

end AxiomAudit

end Mettapedia.GSLT.LanguageDef.PositiveInductiveWorkflowActionGuest
