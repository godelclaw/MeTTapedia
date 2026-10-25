import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestPlans
import Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestControls
import Mettapedia.GSLT.LanguageDef.PositiveInductiveSearchTreeElaboration
import Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeElaboration
import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendElaboration

/-!
# Source-call plans for the admitted List and Vector constructor codes

The actual authored SearchTree producer now uses the generic scan. A mixed
Vector source exercises all field classes and keeps its earlier length through
an intervening payload. Three separate source bodies select its direct call,
complete nested bundle and final direct call. Their compiled methods retain
the method ABI order and beta-reconstruct those bodies.

These additional mixed clauses test the raw clause compiler. They do not
install a new eliminator or prove a result-view adapter well typed. The
independently typed authored SearchTree fold remains the qualified client.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestPlansControls

open Mettapedia.TypeTheory.IndexedPositiveContainer
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open IndexedInductive.CaseElaboration
open IndexedPositiveContainerGuestPlans
open TypedEquality.Normalization (lams)

namespace VectorCalls

abbrev I := VectorControl.interface
abbrev registry := VectorControl.registry

open PositiveInductiveVectorTreeElaboration (operations)

abbrev source := IndexedPositiveContainerGuestControls.Vectors.Mixed.source
abbrev code := source.body.erase
def generated : BranchPlan Tower.Head 3 := plan operations source.name code

def expectedCalls : List (Tower.Tm 8) :=
  [PositiveInductiveVectorTreeGuest.eliminateApp (.var 7) (.var 6) (.var 5) (.var 3),
   PositiveInductiveVectorTreeGuest.liftChildren (.var 7) (.var 6) (.var 5) (.var 4) (.var 1),
   PositiveInductiveVectorTreeGuest.eliminateApp (.var 7) (.var 6) (.var 5) (.var 0)]

def expected : BranchPlan Tower.Head 3 := ⟨source.name, 5, expectedCalls⟩

theorem generated_exact : generated = expected := by
  decide +kernel

theorem fields_exact : generated.fields = 5 :=
  congrArg BranchPlan.fields generated_exact

theorem calls_exact : Eq (α := List (Tower.Tm 8)) generated.recursiveCalls expectedCalls := by
  exact eq_of_heq (congr_arg_heq BranchPlan.recursiveCalls generated_exact)

theorem three_hypotheses : generated.recursiveCalls.length = 3 :=
  plan_call_count operations source.name code

def clauses : List (Clause Tower.Head 3) :=
  expectedCalls.map fun body => ⟨source.name, 5, body⟩

def compiled : List (Option (Tower.Tm 3)) :=
  clauses.map (compilePlan generated PositiveInductiveVectorTreeGuest.eliminateName)

def expectedMethods : List (Tower.Tm 3) :=
  [lams 5 (lams 3 (.var 2)), lams 5 (lams 3 (.var 1)), lams 5 (lams 3 (.var 0))]

theorem compilation_exact : compiled = expectedMethods.map some := by
  decide +kernel

def firstClause : Clause Tower.Head 3 :=
  ⟨source.name, 5,
    PositiveInductiveVectorTreeGuest.eliminateApp (.var 7) (.var 6) (.var 5) (.var 3)⟩

def firstMethod : Tower.Tm 3 := lams 5 (lams 3 (.var 2))

theorem first_compiled :
    compilePlan generated PositiveInductiveVectorTreeGuest.eliminateName firstClause = some firstMethod := by
  decide +kernel

/-- Every successfully compiled body keeps its source fields and exact
substitution reconstruction, with no residual unlicensed recursive name. -/
theorem compiled_reconstructs (clause : Clause Tower.Head 3) (method : Tower.Tm 3)
    (accepted : compilePlan generated PositiveInductiveVectorTreeGuest.eliminateName clause = some method) :
    clause.constructor = source.name ∧ clause.fields = 5 ∧
      ∃ original body,
        adaptFields source.name generated.fields clause = some original ∧
        subst generated.substitution body = original ∧
        PositiveInductiveVectorTreeGuest.eliminateName ∉ ConstantExpansion.constantNames body ∧
        method = generated.method body := by
  obtain ⟨named, arity, _count, original, body, adapted, restored, free, emitted⟩ :=
    IndexedPositiveContainerGuestPlans.compile_reconstructs operations source.name code
      PositiveInductiveVectorTreeGuest.eliminateName clause method accepted
  exact ⟨named, arity, original, body, adapted, restored, free, emitted⟩

theorem first_reconstructs :
    firstClause.constructor = source.name ∧ firstClause.fields = 5 ∧
      ∃ original body,
        adaptFields source.name generated.fields firstClause = some original ∧
        subst generated.substitution body = original ∧
        PositiveInductiveVectorTreeGuest.eliminateName ∉ ConstantExpansion.constantNames body ∧
        firstMethod = generated.method body :=
  compiled_reconstructs firstClause firstMethod first_compiled

theorem first_beta :
    ∃ original, adaptFields generated.name generated.fields firstClause = some original ∧
      TypedEquality.Reduces PositiveInductiveVectorTreeGuest.inventoryRules
        (TypedEquality.Normalization.appSpine
          (rename (TypedEquality.Normalization.wkN generated.fields) firstMethod)
          (TypedEquality.Normalization.fieldVars 3 generated.fields ++ generated.recursiveCalls)) original :=
  compilePlan_reduces generated PositiveInductiveVectorTreeGuest.eliminateName
    firstClause firstMethod first_compiled

def weaken : Sub Tower.Head (3 + fieldCount code) (3 + fieldCount code + 1) :=
  fun index => .var index.succ

theorem substitution_witness :
    (calls operations code (outerTerms code) PUnit.unit (fieldTerms code)).map (subst weaken) =
      calls operations code (fun i => subst weaken (outerTerms code i)) PUnit.unit
        (fun i => subst weaken (fieldTerms code i)) :=
  calls_substitute operations code (outerTerms code) PUnit.unit (fieldTerms code) weaken

/-- Identify the two direct children without deleting their source occurrences. -/
def sameChildren : Sub Tower.Head 8 8 :=
  fun index => if index = 3 then .var 0 else .var index

def coincidentCalls : List (Tower.Tm 8) := expectedCalls.map (subst sameChildren)

theorem coincident_children_keep_slots :
    coincidentCalls.length = 3 ∧ coincidentCalls[0]? = coincidentCalls[2]? := by
  decide +kernel

/-- Sharing a value can keep both ABI slots; value-only deduplication cannot
serve as the original three-argument induction-hypothesis interface. -/
theorem value_dedup_drops_slot : coincidentCalls.eraseDups.length = 2 := by
  decide +kernel

def wrongChild : Clause Tower.Head 3 :=
  ⟨source.name, 5,
    PositiveInductiveVectorTreeGuest.eliminateApp (.var 7) (.var 6) (.var 5) (.var 2)⟩

def wrongLength : Clause Tower.Head 3 :=
  ⟨source.name, 5,
    PositiveInductiveVectorTreeGuest.liftChildren (.var 7) (.var 6) (.var 5) (.var 2) (.var 1)⟩

theorem wrong_child_refused :
    compilePlan generated PositiveInductiveVectorTreeGuest.eliminateName wrongChild = none := by
  decide +kernel

theorem wrong_length_refused :
    compilePlan generated PositiveInductiveVectorTreeGuest.eliminateName wrongLength = none := by
  decide +kernel

theorem correct_order_not_reversed : expectedCalls ≠ expectedCalls.reverse := by
  decide +kernel


/-! The same mixed code also drives a named clause header; all five fields
are read before recursive calls are abstracted. -/

def header : IndexedInductive.OperationSource.Header 3 :=
  IndexedInductive.OperationSource.Header.fromPlan generated "Fold" []

def sourceRow (body : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule :=
  ⟨"MixedBefore", [], [], .apply "Fold"
    [.fvar "P", .fvar "S", .fvar "B", .apply source.name
      [.fvar "arity", .fvar "before", .fvar "tag", .fvar "children", .fvar "after"]], body, none⟩

def beforeRow := sourceRow (.apply "Fold" [.fvar "P", .fvar "S", .fvar "B", .fvar "before"])

def namedCompilation (row : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule) :=
  IndexedInductive.OperationSource.compileRule PositiveInductiveVectorTreeElaboration.sourceSymbols 64
    PositiveInductiveVectorTreeGuest.eliminateName header generated.recursiveCalls row

theorem named_before_compiled : namedCompilation beforeRow = some firstMethod := by
  decide +kernel

theorem named_slots_count : header.slots.length = 8 :=
  IndexedInductive.OperationSource.Header.fromPlan_slot_count generated "Fold" []

def payloadRow := sourceRow (.apply "Fold" [.fvar "P", .fvar "S", .fvar "B", .fvar "tag"])

theorem named_payload_refused : (namedCompilation payloadRow).isNone = true := by
  decide +kernel

def aliasRow : Mettapedia.OSLF.MeTTaIL.Syntax.RewriteRule :=
  { beforeRow with left := (.apply "Fold"
    [.fvar "P", .fvar "S", .fvar "B", .apply source.name
      [.fvar "arity", .fvar "before", .fvar "tag", .fvar "children", .fvar "before"]]) }

theorem source_alias_refused : (namedCompilation aliasRow).isNone = true := by
  decide +kernel

end VectorCalls

def verdicts : List (String × Bool) :=
  [("generic mixed plan retains five source fields", VectorCalls.generated.fields == 5),
   ("generic mixed plan retains three complete IH arguments", VectorCalls.generated.recursiveCalls.length == 3),
   ("generic mixed calls retain earlier arity and field order",
      VectorCalls.generated.recursiveCalls == VectorCalls.expectedCalls),
   ("compiled mixed calls occupy their ABI slots", VectorCalls.compiled == VectorCalls.expectedMethods.map some),
   ("unlisted recursive payload refuses", (compilePlan VectorCalls.generated
      PositiveInductiveVectorTreeGuest.eliminateName VectorCalls.wrongChild).isNone),
   ("changed nested output length refuses", (compilePlan VectorCalls.generated
      PositiveInductiveVectorTreeGuest.eliminateName VectorCalls.wrongLength).isNone),
   ("coincident calls keep all method slots", VectorCalls.coincidentCalls.length == 3 &&
      VectorCalls.coincidentCalls[0]? == VectorCalls.coincidentCalls[2]?),
   ("value-only deduplication drops an IH slot", VectorCalls.coincidentCalls.eraseDups.length == 2),
   ("source call order differs from reversal", VectorCalls.expectedCalls != VectorCalls.expectedCalls.reverse),
   ("named mixed clause retains all five source fields", VectorCalls.namedCompilation VectorCalls.beforeRow == some VectorCalls.firstMethod),
   ("named mixed recursive payload refuses", (VectorCalls.namedCompilation VectorCalls.payloadRow).isNone),
   ("named mixed source alias refuses", (VectorCalls.namedCompilation VectorCalls.aliasRow).isNone)]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  decide +kernel


namespace OrdinaryAppend

noncomputable def operations : CallSyntax IndexedPositiveContainerGuestControls.OrdinaryVectors.I
    IndexedPositiveContainerGuestControls.OrdinaryVectors.registry Tower.Head 5 :=
  templateCalls (IndexedInductive.Guest.TypedControls.indexSyntax Bool)
    IndexedInductive.AppendElaboration.callTemplate (fun _ => rfl)

/-- Actual Nat-indexed Vec tail calls retain the existing append plan. This
is a theory comparison; the source interpretation is noncomputable. -/
theorem cons_plan_exact :
    IndexedPositiveContainerGuestPlans.plan operations "Cons"
      (IndexedPositiveContainerGuestTypes.ordinaryCode (parameters := 0)
        (IndexedInductiveNatVec.Vectors.consCode Bool)) =
      IndexedInductive.CaseElaboration.plan (IndexedInductive.Guest.TypedControls.indexSyntax Bool)
        ((IndexedInductiveNatVec.Vectors.admitted Bool).constructors.get
          (IndexedInductive.Guest.TypedControls.consOccurrence Bool))
        IndexedInductive.AppendElaboration.callTemplate := by
  decide +kernel


noncomputable abbrev consCode := IndexedPositiveContainerGuestTypes.ordinaryCode
  (registry := IndexedPositiveContainerGuestControls.OrdinaryVectors.registry)
  (parameters := 0) (IndexedInductiveNatVec.Vectors.consCode Bool)

theorem cons_fields_exact : fieldCount consCode = 3 :=
  fieldCount_ordinary (registry := IndexedPositiveContainerGuestControls.OrdinaryVectors.registry)
    (parameters := 0) (IndexedInductiveNatVec.Vectors.consCode Bool)

theorem calls_ordinary_witness :
    calls operations consCode (outerTerms consCode) PUnit.unit (fieldTerms consCode) =
      (IndexedInductive.Guest.recursiveArguments
        (IndexedInductive.Guest.TypedControls.indexSyntax Bool)
        (IndexedInductiveNatVec.Vectors.consCode Bool) PUnit.unit
        (ordinaryArguments (IndexedInductiveNatVec.Vectors.consCode Bool) (fieldTerms consCode))).map
          (fun pair => subst (consSub pair.2 (consSub pair.1 (outerTerms consCode)))
            IndexedInductive.AppendElaboration.callTemplate) :=
  calls_ordinary operations (IndexedInductive.Guest.TypedControls.indexSyntax Bool)
    IndexedInductive.AppendElaboration.callTemplate (by intros; rfl)
    (IndexedInductiveNatVec.Vectors.consCode Bool) (outerTerms consCode) PUnit.unit (fieldTerms consCode)

end OrdinaryAppend

end Mettapedia.GSLT.LanguageDef.IndexedPositiveContainerGuestPlansControls
