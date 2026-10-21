import Mettapedia.Algebra.HyperstructureQuantale
import Mettapedia.GSLT.Core.RelationPresentation
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Portable
import Mettapedia.OSLF.MeTTaIL.ContextualStep
import Mathlib.Data.List.Range
import Std.Data.String.ToNat

/-!+# Finite multivalued operations as occurrence-preserving modules

The source is an ordered table of triples over a finite carrier. Each row
compiles to one ground rewrite. The independently defined table scan and the
generic executor agree as lists, before support forgets order and duplicates.
Row positions also supply the witnesses of a proof-relevant relation.
The finite carrier size is exported separately: it cannot be recovered from
the rows of an empty or partial operation.

The signature uses the existing upstream-style Lean quotation. Text and UTF-8
transport use the established canonical module envelope and presentation
codec; no equivalence with another `.module` grammar or external runtime is
asserted by these constructions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.HyperoperationModule

open Mettapedia.Algebra
open HyperOp.Finite
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.UpstreamTheoryQuotation

variable {n : Nat}

def signature : QuotedTheory := moduleTheory! Theory FiniteHyperoperation() {
  Types { Value; State; }
  Terms {
    Zero . |- : Value;
    Succ . previous:Value |- : Value;
    Request . left:Value, right:Value |- : State;
    Returned . result:Value |- : State;
  }
  Exports { Value; State; }
}

def numeral : Nat → Pattern
  | 0 => .apply "Zero" []
  | k + 1 => .apply "Succ" [numeral k]

def request (a b : Fin n) : Pattern := .apply "Request" [numeral a.val, numeral b.val]

def returned (c : Fin n) : Pattern := .apply "Returned" [numeral c.val]

theorem numeral_injective : Function.Injective numeral := by
  intro a
  induction a with
  | zero => intro b same; cases b <;> simp_all [numeral]
  | succ a ih =>
    intro b same
    cases b with
    | zero => simp [numeral] at same
    | succ b => simpa using ih (by simpa [numeral] using same)

theorem returned_injective : Function.Injective (returned (n := n)) := by
  intro a b same
  apply Fin.ext
  apply numeral_injective
  simpa [returned] using same

def readNumeral? : Pattern → Option Nat
  | .apply "Zero" [] => some 0
  | .apply "Succ" [previous] => (readNumeral? previous).map Nat.succ
  | _ => none

def readReturned? (n : Nat) : Pattern → Option (Fin n)
  | .apply "Returned" [value] => do
      let value ← readNumeral? value
      if bounded : value < n then some ⟨value, bounded⟩ else none
  | _ => none

@[simp] theorem readNumeral_numeral (value : Nat) : readNumeral? (numeral value) = some value := by
  induction value with
  | zero => rfl
  | succ value ih => simp [numeral, readNumeral?, ih]

@[simp] theorem readReturned_returned (value : Fin n) :
    readReturned? n (returned value) = some value := by
  simp [returned, readReturned?, value.isLt]

/-- A stable name for each row position, including repeated equal rows. -/
def ruleName (index : Nat) : String := "Row" ++ Nat.repr index

theorem ruleName_injective : Function.Injective ruleName := by
  intro first second same
  exact Nat.repr_injective ((String.append_right_inj "Row").mp same)

def rowRule (index : Nat) (row : Row n) : RewriteRule :=
  RewriteRule.mk (bindings := none) (ruleName index) [] []
    (request row.left row.right) (returned row.result)

def rulesFrom (start : Nat) : Table n → List RewriteRule
  | [] => []
  | row :: rest => rowRule start row :: rulesFrom (start + 1) rest

@[simp] theorem rulesFrom_length (table : Table n) (start : Nat) :
    (rulesFrom start table).length = table.length := by
  induction table generalizing start with
  | nil => rfl
  | cons row rest ih => simp [rulesFrom, ih]

theorem rowRule_get_mem (table : Table n) (start : Nat) (index : Fin table.length) :
    rowRule (start + index.val) (table.get index) ∈ rulesFrom start table := by
  induction table generalizing start with
  | nil => exact Fin.elim0 index
  | cons row rest ih =>
    refine Fin.cases ?_ (fun index => ?_) index
    · simp [rulesFrom]
    · simp only [Fin.val_succ, rulesFrom, List.mem_cons]
      right
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (start + 1) index

theorem mem_rulesFrom_row {table : Table n} {start : Nat} {rule : RewriteRule}
    (member : rule ∈ rulesFrom start table) :
    ∃ (index : Nat) (row : Row n), rule = rowRule index row := by
  induction table generalizing start with
  | nil => simp [rulesFrom] at member
  | cons row rest ih =>
    simp only [rulesFrom, List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨start, row, rfl⟩
    · exact ih member

def language (table : Table n) : LanguageDef :=
  { signature.toLanguageDef with «rewrites» := rulesFrom 0 table }

def quoted (table : Table n) : QuotedTheory := ofCore (language table) ["Value", "State"]

theorem numeral_match (a b : Nat) :
    matchPattern (numeral a) (numeral b) = if a = b then [[]] else [] := by
  induction a generalizing b with
  | zero => cases b <;> simp [numeral, matchPattern, matchArgs]
  | succ a ih =>
    cases b with
    | zero => simp [numeral, matchPattern]
    | succ b =>
      simp only [numeral, matchPattern, beq_self_eq_true, List.length_cons,
        List.length_nil, Bool.and_self, ↓reduceIte, matchArgs, ih]
      by_cases same : a = b <;> simp [same, mergeBindings]

theorem request_match (row : Row n) (a b : Fin n) :
    matchPattern (request row.left row.right) (request a b) =
      if row.left = a ∧ row.right = b then [[]] else [] := by
  simp only [request, matchPattern, beq_self_eq_true, List.length_cons,
    List.length_nil, Bool.and_self, ↓reduceIte, matchArgs, numeral_match, Fin.val_inj]
  by_cases left : row.left = a <;> by_cases right : row.right = b <;>
    simp [left, right, mergeBindings]

theorem numeral_substitute (left : Pattern) (bindings : Bindings) (depth value : Nat) :
    applyBindingsScoped left bindings depth (numeral value) = numeral value := by
  induction value with
  | zero => simp [numeral]
  | succ value ih => simp [numeral, ih]

/-- A row has exactly one output when its two inputs match, and none otherwise.
The supplied premise evaluator and recursive engine are not invoked. -/
theorem apply_row (base : BasePremiseEvaluator) (lang : LanguageDef)
    (recursive : Pattern → List Pattern) (index : Nat) (row : Row n) (a b : Fin n) :
    applyRuleUsing base lang recursive (rowRule index row) (request a b) =
      if row.left = a ∧ row.right = b then [returned row.result] else [] := by
  simp only [applyRuleUsing, matchPatternForRule, matchPatternForRuleUsing,
    matchingPresentationForRule?_eq_none_of_no_presentations (profile := .empty) rfl,
    rowRule, request_match]
  by_cases matched : row.left = a ∧ row.right = b
  · simp [matched, premisesUsing, applyBindingsForRule,
      applyBindingsForRuleUsing_empty, applyRuleBindings, returned, numeral_substitute]
  · simp [matched]

theorem execute_rulesFrom (base : BasePremiseEvaluator) (lang : LanguageDef)
    (recursive : Pattern → List Pattern) (table : Table n) (start : Nat) (a b : Fin n) :
    (rulesFrom start table).flatMap
        (fun rule => applyRuleUsing base lang recursive rule (request a b)) =
      (outputs table a b).map returned := by
  induction table generalizing start with
  | nil => rfl
  | cons row rest ih =>
    simp only [rulesFrom, List.flatMap_cons, apply_row, ih, outputs_cons]
    split_ifs <;> simp

def successors (table : Table n) (source : Pattern) : List Pattern :=
  rewriteAt (engineBasePremises .empty) (language table) 1 source

/-- The complete ordered successor list is exactly the source table scan.
This simultaneously proves preservation and absence of invented outcomes. -/
theorem successors_request (table : Table n) (a b : Fin n) :
    successors table (request a b) = (outputs table a b).map returned := by
  exact execute_rulesFrom _ _ _ table 0 a b

theorem successors_returned (table : Table n) (c : Fin n) :
    successors table (returned c) = [] := by
  unfold successors rewriteAt
  change (rulesFrom 0 table).flatMap _ = []
  apply List.flatMap_eq_nil_iff.mpr
  intro rule member
  obtain ⟨index, row, rfl⟩ := mem_rulesFrom_row member
  simp [applyRuleUsing, rowRule, request, returned, matchPatternForRule,
    matchPatternForRuleUsing, matchPattern,
    matchingPresentationForRule?_eq_none_of_no_presentations (profile := .empty) rfl]

/-- Possibility is a proved observation of the ordered execution. -/
theorem output_iff (table : Table n) (a b c : Fin n) :
    returned c ∈ successors table (request a b) ↔ c ∈ operation table a b := by
  rw [successors_request, List.mem_map]
  constructor
  · rintro ⟨value, member, same⟩
    obtain rfl := returned_injective same
    exact (mem_outputs ..).mp member
  · intro member
    exact ⟨c, (mem_outputs ..).mpr member, rfl⟩

/-- The operational observer decodes actual engine results. -/
def observed (table : Table n) (a b : Fin n) : List (Fin n) :=
  (successors table (request a b)).filterMap (readReturned? n)

theorem observed_eq_outputs (table : Table n) (a b : Fin n) :
    observed table a b = outputs table a b := by
  simp [observed, successors_request, List.filterMap_map]

/-- The finite checker governs the two actual composed executions, observed
at support. It does not assert equality of lists or derivation counts. -/
theorem associative_iff_execution (table : Table n) :
    associative? table = true ↔ ∀ a b c : Fin n,
      ((observed table a b).flatMap (fun intermediate => observed table intermediate c)).toFinset =
        ((observed table b c).flatMap (fun intermediate => observed table a intermediate)).toFinset := by
  simp only [observed_eq_outputs, associative?, decide_eq_true_eq]

/-! ## Admission of the complete finite presentation -/

theorem rulesFrom_names (table : Table n) (start : Nat) :
    (rulesFrom start table).map (·.name) = (List.range' start table.length).map ruleName := by
  induction table generalizing start with
  | nil => rfl
  | cons row rest ih => simp [rulesFrom, rowRule, List.range'_succ, ih]

theorem rulesFrom_names_nodup (table : Table n) (start : Nat) :
    ((rulesFrom start table).map (·.name)).Nodup := by
  rw [rulesFrom_names]
  exact (List.nodup_range' 1).map ruleName_injective

theorem numeral_free (value : Nat) : (numeral value).freeFvarNames = [] := by
  induction value with
  | zero => simp [numeral, Pattern.freeFvarNames]
  | succ value ih => simp [numeral, Pattern.freeFvarNames, ih]

theorem numeral_binders (value : Nat) : LanguageDef.patternBinderNames (numeral value) = [] := by
  induction value with
  | zero => simp [numeral, LanguageDef.patternBinderNames]
  | succ value ih => simp [numeral, LanguageDef.patternBinderNames, ih]

theorem numeral_scoped (value depth : Nat) : (numeral value).isWellScopedAt depth = true := by
  induction value with
  | zero => rfl
  | succ value ih => simp [numeral, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, ih]

theorem numeral_valid (context : String) (value : Nat) :
    LanguageDef.validatePatternConstructors context signature.terms (numeral value) = [] := by
  induction value with
  | zero => rfl
  | succ value ih =>
    simpa [LanguageDef.validatePatternConstructors, numeral, Pattern.constructorRefs,
      Pattern.constructorRefsList, signature, ofCore, LanguageDef.ofCore,
      LanguageDef.resolveNullaryPatterns, LanguageDef.resolveNullaryWith] using ih

theorem row_validates (table : Table n) (index : Nat) (row : Row n) :
    LanguageDef.validateRewrite (language table) (rowRule index row) = [] := by
  have requestValid (context : String) :
      LanguageDef.validatePatternConstructors context signature.terms
        (request row.left row.right) = [] := by
    simpa [LanguageDef.validatePatternConstructors, request, Pattern.constructorRefs,
      Pattern.constructorRefsList, signature, ofCore, LanguageDef.ofCore,
      LanguageDef.resolveNullaryPatterns, LanguageDef.resolveNullaryWith] using
      congrArg₂ List.append (numeral_valid context row.left.val) (numeral_valid context row.right.val)
  have returnedValid (context : String) :
      LanguageDef.validatePatternConstructors context signature.terms (returned row.result) = [] := by
    simpa [LanguageDef.validatePatternConstructors, returned, Pattern.constructorRefs,
      Pattern.constructorRefsList, signature, ofCore, LanguageDef.ofCore,
      LanguageDef.resolveNullaryPatterns, LanguageDef.resolveNullaryWith] using numeral_valid context row.result.val
  simp only [LanguageDef.validateRewrite, rowRule, language, List.flatMap_nil,
    List.nil_append, List.append_nil, requestValid, returnedValid]
  simp [LanguageDef.validateRulePatterns, request, returned,
    LanguageDef.patternFvarNames, Pattern.freeFvarNames, numeral_free,
    LanguageDef.patternBinderNames, numeral_binders,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt, numeral_scoped]

theorem language_validates (table : Table n) : (language table).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · simp only [language, LanguageDef.typeNames]; decide
  · simp only [language]; decide
  · exact rulesFrom_names_nodup table 0
  · simp only [language, LanguageDef.typeNames]; decide
  · simp only [language, LanguageDef.typeNames]; decide
  · simp only [language]; decide
  · intro rule member
    change rule ∈ rulesFrom 0 table at member
    obtain ⟨index, row, rfl⟩ := mem_rulesFrom_row member
    exact row_validates table index row

theorem quoted_admitted (table : Table n) : (admit? (quoted table)).isSome = true := by
  apply (admit_isSome_iff _).mpr
  constructor
  · change (language table).validate.isEmpty = true
    rw [language_validates]
    rfl
  · simp only [exportsValid, quoted, ofCore, language, LanguageDef.typeNames]; decide

/-! ## Proof-relevant row occurrences -/

/-- The witness is a row position, so equal triples at different positions
remain different witnesses. -/
def Occurrence (table : Table n) (a b c : Fin n) :=
  {index : Fin table.length //
    (table.get index).left = a ∧ (table.get index).right = b ∧ (table.get index).result = c}

def relation (table : Table n) : RelationPresentation.Rel (Fin n × Fin n) (Fin n) where
  evidence pair result := Occurrence table pair.1 pair.2 result

theorem occurrence_iff (table : Table n) (a b c : Fin n) :
    Nonempty (Occurrence table a b c) ↔ c ∈ operation table a b := by
  constructor
  · rintro ⟨⟨index, matched⟩⟩
    exact ⟨table.get index, List.get_mem .., matched⟩
  · rintro ⟨row, member, matched⟩
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    exact ⟨⟨index, matched⟩⟩

/-- A retained row occurrence identifies an actual compiled rule and its
successful application; it is not reconstructed from the output value. -/
theorem occurrence_executes {table : Table n} {a b c : Fin n}
    (witness : Occurrence table a b c) :
    rowRule witness.val.val (table.get witness.val) ∈ (language table).rewrites ∧
      applyRuleUsing (engineBasePremises .empty) (language table) (fun _ => [])
        (rowRule witness.val.val (table.get witness.val)) (request a b) = [returned c] := by
  constructor
  · simpa [language] using rowRule_get_mem table 0 witness.val
  · rw [apply_row]
    simp only [witness.property.1, witness.property.2.1, witness.property.2.2,
      and_self, ↓reduceIte]

theorem occurrence_name_injective {table : Table n} {a b c : Fin n} :
    Function.Injective (fun witness : Occurrence table a b c => ruleName witness.val.val) := by
  intro first second same
  apply Subtype.ext
  apply Fin.ext
  exact ruleName_injective same

theorem relation_iff_execution (table : Table n) (a b c : Fin n) :
    Nonempty ((relation table).evidence (a, b) c) ↔
      returned c ∈ successors table (request a b) := by
  rw [output_iff]
  exact occurrence_iff table a b c

/-! ## Canonical module text and UTF-8 transport -/

def schema : String := "finite-hyperoperation/1"

def envelope (table : Table n) : ModuleFormat.Module ModuleFormat.upstreamLimits :=
  ⟨⟨"FiniteHyperoperation", [], [⟨"Operation",
    ModuleFormat.Portable.specification schema ModuleFormat.Portable.exportsCodec (quoted table)⟩,
    ⟨"CarrierSize", .integer n⟩]⟩,
    by
      simp [ModuleFormat.RawModule.Valid, ModuleFormat.Export.Valid, ModuleFormat.upstreamLimits]
      decide⟩

def moduleText (table : Table n) : String :=
  ModuleFormat.renderText ModuleFormat.upstreamLimits (envelope table)

def moduleBytes (table : Table n) : ByteArray :=
  ModuleFormat.Text.renderBytes
    (ModuleFormat.Value.Wire.encode (ModuleFormat.encodeRaw (envelope table).val))

theorem read_moduleText (table : Table n) :
    ModuleFormat.readText? ModuleFormat.upstreamLimits (moduleText table) = some (envelope table) :=
  ModuleFormat.readText_renderText _ _

theorem moduleBytes_eq_utf8 (table : Table n) : moduleBytes table = (moduleText table).toUTF8 := rfl

theorem read_moduleBytes (table : Table n) :
    (ModuleFormat.Text.readBytes? (moduleBytes table)).bind (fun term =>
      (ModuleFormat.Value.Wire.decode? term).bind
        (ModuleFormat.decode? ModuleFormat.upstreamLimits)) = some (envelope table) := by
  simp [moduleBytes]

theorem read_export (table : Table n) :
    (ModuleFormat.readText? ModuleFormat.upstreamLimits (moduleText table)).bind (fun parsed =>
      parsed.val.exports.head?.bind (fun entry =>
        ModuleFormat.Portable.admitSpecification? schema ModuleFormat.Portable.exportsCodec entry.spec)) =
      some (quoted table) := by
  rw [read_moduleText]
  exact ModuleFormat.Portable.specification_roundtrip _ _ _

theorem read_carrierSize (table : Table n) :
    (ModuleFormat.readText? ModuleFormat.upstreamLimits (moduleText table)).bind
      (fun parsed => parsed.val.exports[1]?.map (·.spec)) =
      some (.integer n) := by
  rw [read_moduleText]
  rfl

/-- Decode the finite observation profile as well as the rewrite theory.
Checking the declared size prevents silent changes to the query domain.
This is a structural decoder; exact execution is established for compiled
tables by `read_successors`, rather than asserted for arbitrary input modules. -/
def readOperation? (expectedSize : Nat) (text : String) : Option QuotedTheory := do
  let parsed ← ModuleFormat.readText? ModuleFormat.upstreamLimits text
  match parsed.val.exports with
  | [operationExport, carrierExport] =>
      if operationExport.name = "Operation" ∧ carrierExport.name = "CarrierSize" ∧
          carrierExport.spec = .integer expectedSize then
        ModuleFormat.Portable.admitSpecification? schema ModuleFormat.Portable.exportsCodec
          operationExport.spec
      else none
  | _ => none

theorem read_operation (table : Table n) :
    readOperation? n (moduleText table) = some (quoted table) := by
  simp [readOperation?, read_moduleText, envelope, ModuleFormat.Portable.specification_roundtrip]

theorem read_wrong_carrier (table : Table n) (expectedSize : Nat) (different : n ≠ expectedSize) :
    readOperation? expectedSize (moduleText table) = none := by
  simp [readOperation?, read_moduleText, envelope, different]

/-- Carrier information survives serialization even if no row mentions the
extra elements. -/
theorem moduleText_preserves_carrier {m : Nat} (first : Table n) (second : Table m)
    (same : moduleText first = moduleText second) : n = m := by
  have sizes := congrArg (fun text =>
    (ModuleFormat.readText? ModuleFormat.upstreamLimits text).bind
      (fun parsed => parsed.val.exports[1]?.map (·.spec))) same
  rw [read_carrierSize, read_carrierSize] at sizes
  exact Int.ofNat.inj (ModuleFormat.Value.integer.inj (Option.some.inj sizes))

theorem moduleText_ne_of_carrier_ne {m : Nat} (first : Table n) (second : Table m)
    (different : n ≠ m) : moduleText first ≠ moduleText second :=
  fun same => different (moduleText_preserves_carrier first second same)

/-- Read the actual serialized module before invoking the existing executor;
the complete ordered answer still agrees with the independent table scan. -/
theorem read_successors (table : Table n) (a b : Fin n) :
    (readOperation? n (moduleText table)).map
      (fun theory => rewriteAt (engineBasePremises .empty) theory.toLanguageDef 1 (request a b)) =
      some ((outputs table a b).map returned) := by
  rw [read_operation]
  exact congrArg some (successors_request table a b)

theorem wrong_schema_refused (table : Table n) :
    ModuleFormat.Portable.readTheory? "other/1" ModuleFormat.Portable.exportsCodec
      (ModuleFormat.Portable.renderTheory schema ModuleFormat.Portable.exportsCodec (quoted table)) = none :=
  ModuleFormat.Portable.readTheory_renderTheory_otherSchema _ _ _ _ _ (by decide)

namespace Controls

def singletonCarrier : Table 1 := [⟨0, 0, 0⟩]
def largerCarrier : Table 2 := [⟨0, 0, 0⟩]

theorem carrier_changes_totality :
    total? singletonCarrier = true ∧ total? largerCarrier = false := by
  decide

theorem equal_rewrite_core_distinct_carrier_profile :
    language singletonCarrier = language largerCarrier ∧
      moduleText singletonCarrier ≠ moduleText largerCarrier := by
  constructor
  · rfl
  · exact moduleText_ne_of_carrier_ne _ _ (by decide)

def single : Table 2 := [⟨0, 0, 1⟩]
def duplicate : Table 2 := [⟨0, 0, 1⟩, ⟨0, 0, 1⟩]
def extra : Table 2 := [⟨0, 0, 1⟩, ⟨0, 0, 0⟩]

theorem duplicate_execution_retains_both :
    successors duplicate (request (n := 2) 0 0) = [returned (n := 2) 1, returned (n := 2) 1] := by
  rw [successors_request]
  rfl

theorem duplicate_rows_have_distinct_names :
    ((language duplicate).rewrites.map (·.name)).Nodup ∧
      (language duplicate).rewrites.length = 2 :=
  ⟨rulesFrom_names_nodup _ _, rfl⟩

theorem duplicate_witnesses_distinct :
    ∃ first second : (relation duplicate).evidence (0, 0) 1, first ≠ second := by
  refine ⟨⟨⟨0, by decide⟩, by decide⟩, ⟨⟨1, by decide⟩, by decide⟩, ?_⟩
  intro same
  have impossible := congrArg (fun witness => witness.val.val) same
  contradiction

theorem omitted_row_loses_behavior :
    returned (n := 2) 1 ∈ successors single (request (n := 2) 0 0) ∧
      returned (n := 2) 1 ∉ successors ([] : Table 2) (request (n := 2) 0 0) := by
  simp [successors_request, single, outputs]

theorem extra_row_invents_behavior :
    returned (n := 2) 0 ∈ successors extra (request (n := 2) 0 0) ∧
      returned (n := 2) 0 ∉ successors single (request (n := 2) 0 0) := by
  simp [successors_request, extra, single, outputs, returned, numeral]

/-- Retaining every old outcome is weaker than exact interpretation. -/
theorem forward_only_is_insufficient :
    (∀ a b, operation single a b ⊆ operation extra a b) ∧
      successors single (request (n := 2) 0 0) ≠ successors extra (request (n := 2) 0 0) := by
  constructor
  · intro a b
    change operation (single ++ [⟨0, 0, 0⟩]) a b ⊇ operation single a b
    rw [operation_append]
    exact Set.subset_union_left
  · rw [successors_request, successors_request]
    decide

/-- Equal possible outputs do not justify identifying execution histories. -/
theorem same_support_different_execution :
    operation single = operation duplicate ∧
      successors single (request (n := 2) 0 0) ≠ successors duplicate (request (n := 2) 0 0) := by
  constructor
  · exact HyperOp.Finite.Controls.duplicate_rows_same_operation
  · rw [successors_request, successors_request]
    decide

theorem choice_execution_support_associative :
    ∀ a b c : Fin 2,
      ((observed HyperOp.Finite.Controls.choiceTable a b).flatMap
          (fun intermediate => observed HyperOp.Finite.Controls.choiceTable intermediate c)).toFinset =
        ((observed HyperOp.Finite.Controls.choiceTable b c).flatMap
          (fun intermediate => observed HyperOp.Finite.Controls.choiceTable a intermediate)).toFinset :=
  (associative_iff_execution _).mp HyperOp.Finite.Controls.choice_passes.1

/-- The same associative support operation fails associativity when the
observer retains counts. The left bracketing has two zeroes, the right three. -/
theorem choice_execution_not_bag_associative :
    (((observed HyperOp.Finite.Controls.choiceTable 0 0).flatMap
        (fun middle => observed HyperOp.Finite.Controls.choiceTable middle 1)) : Multiset (Fin 2)) ≠
      (((observed HyperOp.Finite.Controls.choiceTable 0 1).flatMap
        (fun middle => observed HyperOp.Finite.Controls.choiceTable 0 middle)) : Multiset (Fin 2)) := by
  simp only [observed_eq_outputs]
  decide

def toggle : Table 2 := [⟨0, 0, 1⟩, ⟨1, 0, 0⟩]
def fusedToggle : Table 2 := [⟨0, 0, 0⟩, ⟨1, 0, 1⟩]

/-- Two actual table applications can be fused into one while preserving
ordered answers. The intermediate result is an additional observation. -/
theorem fused_execution_same_answer (a : Fin 2) :
    (observed toggle a 0).flatMap (fun middle => observed toggle middle 0) =
      observed fusedToggle a 0 := by
  simp only [observed_eq_outputs]
  fin_cases a <;> decide

theorem fusion_changes_intermediate_observation :
    observed toggle 0 0 ≠ observed fusedToggle 0 0 := by
  simp only [observed_eq_outputs]
  decide

theorem malformed_result_refused :
    readReturned? 2 (.apply "Returned" [numeral 2]) = none ∧
      readReturned? 2 (.apply "Returned" []) = none := by
  decide

end Controls

end Mettapedia.GSLT.LanguageDef.HyperoperationModule
