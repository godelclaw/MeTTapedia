import Mettapedia.OSLF.MeTTaIL.ConditionalEquationExecution

/-!
# Typed finite providers and immutable contextual captures

Provider signatures declare both argument sorts and input/output modes. Rows
are actual finite data, with stable declaration positions. Checking a row in
the full caller context does not identify a missing provider with a complete
empty relation. Closed-row admission is a separately executable condition.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- The complete captured value, including dependency sorts and ambient
context, remains available under its original name. -/
def Extension (initial final : Assignment) : Prop :=
  ∀ name value, lookup initial name = some value → lookup final name = some value

theorem Extension.refl (assignment : Assignment) : Extension assignment assignment := by
  intro name value found
  exact found

theorem Extension.trans {first second third : Assignment}
    (front : Extension first second) (back : Extension second third) :
    Extension first third := by
  intro name value found
  exact back name value (front name value found)

/-- Check first-match lookups, so duplicate list entries do not change the
meaning of the assignment interface. -/
def checkExtension (initial final : Assignment) : Bool :=
  initial.all fun (name, _) =>
    match lookup initial name with
    | none => true
    | some value => lookup final name == some value

theorem checkExtension_sound {initial final : Assignment}
    (checked : checkExtension initial final = true) : Extension initial final := by
  intro name value found
  have member := ConditionalEquationExecution.lookup_assignment_member initial name value found
  have preserved := List.all_eq_true.mp checked (name, value) member
  simpa only [found, beq_iff_eq] using preserved

theorem checkExtension_complete {initial final : Assignment}
    (preserved : Extension initial final) : checkExtension initial final = true := by
  apply List.all_eq_true.mpr
  intro entry _
  cases found : lookup initial entry.1 with
  | none => simp [found]
  | some value => simp [found, preserved entry.1 value found]

@[simp] theorem checkExtension_eq_true_iff (initial final : Assignment) :
    checkExtension initial final = true ↔ Extension initial final :=
  ⟨checkExtension_sound, checkExtension_complete⟩

/-- A relation's row positions have authored sorts and execution modes. -/
structure Signature where
  relation : String
  argumentTypes : List TypeExpr
  modes : List RelationArgMode
  deriving DecidableEq, Repr

structure ProviderRow where
  relation : String
  values : List Pattern
  deriving DecidableEq, Repr

structure ProviderSnapshot where
  signatures : List Signature
  rows : List ProviderRow
  /-- Relations implemented by admitted dynamic services have no finite-table
  output-shape guarantee merely because the static row inventory is empty. -/
  dynamicRelations : List String := []
  deriving DecidableEq, Repr

/-- A source relation and its executable finite response. The source relation
is supplied by the primitive's independent semantics, including occurrence
multiplicity. A missing response is distinct from a complete empty response. -/
structure DynamicProvider where
  Source : String → List Pattern → List (List Pattern) → Prop
  rows? : String → List Pattern → Option (List (List Pattern))
  rows_exact : ∀ relation arguments rows,
    rows? relation arguments = some rows ↔ Source relation arguments rows

namespace DynamicProvider

def empty : DynamicProvider where
  Source := fun _ _ _ => False
  rows? := fun _ _ => none
  rows_exact := by intro relation arguments rows; simp

/-- A source relation with an executable exact finite response is functional;
the list retains the provider's occurrences rather than identifying duplicates. -/
theorem source_unique (provider : DynamicProvider) {relation : String}
    {arguments : List Pattern} {first last : List (List Pattern)}
    (left : provider.Source relation arguments first)
    (right : provider.Source relation arguments last) : first = last :=
  Option.some.inj (((provider.rows_exact _ _ _).mpr left).symm.trans
    ((provider.rows_exact _ _ _).mpr right))

theorem unknown_iff (provider : DynamicProvider) (relation : String)
    (arguments : List Pattern) :
    provider.rows? relation arguments = none ↔
      ∀ rows, ¬ provider.Source relation arguments rows := by
  constructor
  · intro missing rows source
    have answer := (provider.rows_exact _ _ _).mpr source
    rw [missing] at answer
    contradiction
  · intro missing
    cases found : provider.rows? relation arguments with
    | none => rfl
    | some rows => exact (missing rows ((provider.rows_exact _ _ _).mp found)).elim

end DynamicProvider

/-- Ambiguous or unavailable signatures remain unavailable. -/
def signature? (provider : ProviderSnapshot) (relation : String) (arity : Nat) :
    Option Signature :=
  match provider.signatures.filter fun signature =>
    signature.relation == relation && signature.argumentTypes.length == arity with
  | [signature] =>
      if signature.modes.length == arity then some signature else none
  | _ => none

theorem signature?_readout (provider : ProviderSnapshot) (relation : String) (arity : Nat)
    (signature : Signature) (found : signature? provider relation arity = some signature) :
    signature ∈ provider.signatures ∧ signature.relation = relation ∧
      signature.argumentTypes.length = arity ∧ signature.modes.length = arity := by
  unfold signature? at found
  split at found
  · rename_i actual selected
    split at found
    · rename_i modes
      cases Option.some.inj found
      have selectedMember : signature ∈ provider.signatures.filter (fun candidate =>
          candidate.relation == relation && candidate.argumentTypes.length == arity) := by
        rw [selected]
        simp
      rcases List.mem_filter.mp selectedMember with ⟨member, matching⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at matching modes
      exact ⟨member, matching.1, matching.2, modes⟩
    · contradiction
  · contradiction

/-- Heterogeneous row typing against the declared argument sorts. -/
inductive ValuesTyped (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) : List Pattern → List TypeExpr → Prop where
  | nil : ValuesTyped language free bound [] []
  | cons {value : Pattern} {values : List Pattern} {type : TypeExpr}
      {types : List TypeExpr} :
      OpenPatternWellSorted language free bound type value →
      ValuesTyped language free bound values types →
      ValuesTyped language free bound (value :: values) (type :: types)

def checkValues (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) : List Pattern → List TypeExpr → Bool
  | [], [] => true
  | value :: values, type :: types =>
      checkOpenPatternWellSorted language free bound type value &&
        checkValues language free bound values types
  | _, _ => false

theorem checkValues_sound (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (values : List Pattern) (types : List TypeExpr)
    (checked : checkValues language free bound values types = true) :
    ValuesTyped language free bound values types := by
  induction values generalizing types with
  | nil =>
      cases types with
      | nil => exact .nil
      | cons _ _ => simp [checkValues] at checked
  | cons value values inductionHypothesis =>
      cases types with
      | nil => simp [checkValues] at checked
      | cons type types =>
          simp only [checkValues, Bool.and_eq_true] at checked
          exact .cons (checkOpenPatternWellSorted_sound checked.1)
            (inductionHypothesis types checked.2)

theorem checkValues_complete {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {values : List Pattern} {types : List TypeExpr}
    (typed : ValuesTyped language free bound values types) :
    checkValues language free bound values types = true := by
  induction typed with
  | nil => rfl
  | cons head _ inductionHypothesis =>
      simp [checkValues, checkOpenPatternWellSorted_complete head, inductionHypothesis]

theorem ValuesTyped.length {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {values : List Pattern} {types : List TypeExpr}
    (typed : ValuesTyped language free bound values types) : values.length = types.length := by
  induction typed <;> simp_all

def RowTyped (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (signature : Signature) (row : ProviderRow) : Prop :=
  row.relation = signature.relation ∧
    ValuesTyped language free bound row.values signature.argumentTypes

def checkRow (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (signature : Signature) (row : ProviderRow) : Bool :=
  row.relation == signature.relation &&
    checkValues language free bound row.values signature.argumentTypes

theorem checkRow_sound {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {signature : Signature} {row : ProviderRow}
    (checked : checkRow language free bound signature row = true) :
    RowTyped language free bound signature row := by
  simp only [checkRow, Bool.and_eq_true, beq_iff_eq] at checked
  exact ⟨checked.1, checkValues_sound _ _ _ _ _ checked.2⟩

theorem checkRow_complete {language : LanguageDef} {free : FreeTypeContext}
    {bound : List TypeExpr} {signature : Signature} {row : ProviderRow}
    (typed : RowTyped language free bound signature row) :
    checkRow language free bound signature row = true := by
  simp [checkRow, typed.1, checkValues_complete typed.2]

/-- Closed rows can be checked once as a finite admission obligation. Queries
still validate them in their actual full caller contexts. -/
def checkProviderClosed (language : LanguageDef) (free : FreeTypeContext)
    (provider : ProviderSnapshot) : Bool :=
  provider.signatures.all (fun signature =>
    signature.argumentTypes.length == signature.modes.length) &&
  decide ((provider.signatures.map fun signature =>
    (signature.relation, signature.argumentTypes.length)).Nodup) &&
  provider.rows.all (fun row =>
    match signature? provider row.relation row.values.length with
    | none => false
    | some signature => checkRow language free [] signature row)

theorem checkProviderClosed_row (language : LanguageDef) (free : FreeTypeContext)
    (provider : ProviderSnapshot) (checked : checkProviderClosed language free provider = true)
    (row : ProviderRow) (member : row ∈ provider.rows) :
    ∃ signature, signature? provider row.relation row.values.length = some signature ∧
      RowTyped language free [] signature row := by
  simp only [checkProviderClosed, Bool.and_eq_true] at checked
  have accepted := List.all_eq_true.mp checked.2 row member
  cases found : signature? provider row.relation row.values.length with
  | none => simp [found] at accepted
  | some signature =>
      exact ⟨signature, rfl, checkRow_sound (by simpa only [found] using accepted)⟩

end Mettapedia.OSLF.MeTTaIL.GeneralPremise

/-! ## Free-name coverage of the original operations -/

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Mettapedia.OSLF.MeTTaIL.Syntax
open RuleBinding
open ScopedRuleMatching
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem check_values_congr_free (language : LanguageDef)
    (first second : FreeTypeContext) (bound : List TypeExpr)
    (values : List Pattern) (types : List TypeExpr)
    (agreement : ∀ name ∈ values.flatMap Pattern.freeFvarNames, first name = second name) :
    checkValues language first bound values types = checkValues language second bound values types := by
  induction values generalizing types with
  | nil => cases types <;> rfl
  | cons value values inductionHypothesis =>
      cases types with
      | nil => rfl
      | cons type types =>
          simp only [checkValues]
          rw [check_open_pattern_congr_free language first second bound type value
            (fun name membership => agreement name (by simp [membership]))]
          rw [inductionHypothesis types (fun name membership => agreement name (by simp [membership]))]

theorem check_row_congr_free (language : LanguageDef)
    (first second : FreeTypeContext) (bound : List TypeExpr)
    (signature : Signature) (row : ProviderRow)
    (agreement : ∀ name ∈ row.values.flatMap Pattern.freeFvarNames, first name = second name) :
    checkRow language first bound signature row = checkRow language second bound signature row := by
  unfold checkRow
  rw [check_values_congr_free language first second bound row.values signature.argumentTypes agreement]

def providerFreeNames (provider : ProviderSnapshot) : List String :=
  provider.rows.flatMap fun row => row.values.flatMap Pattern.freeFvarNames

theorem provider_free_lookup (provider : ProviderSnapshot) (free : FreeTypeContext)
    (row : ProviderRow) (member : row ∈ provider.rows) (name : String)
    (occurs : name ∈ row.values.flatMap Pattern.freeFvarNames) :
    FreeTypeContext.ofList (free.entriesOn (providerFreeNames provider)) name = free name := by
  rw [FreeTypeContext.ofList_entriesOn, if_pos]
  exact List.mem_flatMap.mpr ⟨row, member, occurs⟩

theorem check_row_provider_finite_free (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (provider : ProviderSnapshot) (signature : Signature)
    (row : ProviderRow) (member : row ∈ provider.rows) :
    checkRow language (FreeTypeContext.ofList (free.entriesOn (providerFreeNames provider)))
      bound signature row = checkRow language free bound signature row := by
  apply check_row_congr_free
  intro name occurs
  exact provider_free_lookup provider free row member name occurs

theorem check_row_provider_cursor_finite_free (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (provider : ProviderSnapshot) (signature : Signature)
    (cursor : Nat) (row : ProviderRow) (found : provider.rows[cursor]? = some row) :
    checkRow language (FreeTypeContext.ofList (free.entriesOn (providerFreeNames provider)))
      bound signature row = checkRow language free bound signature row :=
  check_row_provider_finite_free language free bound provider signature row
    (List.mem_of_getElem? found)
theorem check_row_snapshot (language : LanguageDef) (free : FreeTypeContext) (bound : List TypeExpr)
    (provider : ProviderSnapshot) (signature : Signature) (row : ProviderRow)
    (member : row ∈ provider.rows) (footprint : List String)
    (covers : ∀ name ∈ providerFreeNames provider, name ∈ footprint) :
    checkRow language (FreeTypeContext.ofList (free.entriesOn footprint)) bound signature row =
      checkRow language free bound signature row := by
  apply check_row_congr_free
  intro name occurs
  rw [FreeTypeContext.ofList_entriesOn, if_pos]
  exact covers name (List.mem_flatMap.mpr ⟨row, member, occurs⟩)
theorem provider_covered_by_own_names (provider : ProviderSnapshot) :
    ∀ row ∈ provider.rows, patternsFreeWithin (providerFreeNames provider) row.values := by
  intro row member pattern patternMember name occurs
  exact List.mem_flatMap.mpr ⟨row, member, List.mem_flatMap.mpr ⟨pattern, patternMember, occurs⟩⟩

theorem provider_coverage_mono (first second : List String) (provider : ProviderSnapshot)
    (subset : ∀ name ∈ first, name ∈ second)
    (stored : ∀ row ∈ provider.rows, patternsFreeWithin first row.values) :
    ∀ row ∈ provider.rows, patternsFreeWithin second row.values := by
  intro row member pattern patternMember name occurs
  exact subset name (stored row member pattern patternMember name occurs)

#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.check_values_congr_free
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.check_row_congr_free
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.providerFreeNames
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.provider_free_lookup
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.check_row_provider_finite_free
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.check_row_provider_cursor_finite_free
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.check_row_snapshot
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.provider_covered_by_own_names
#print axioms Mettapedia.OSLF.MeTTaIL.GeneralPremise.provider_coverage_mono

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
