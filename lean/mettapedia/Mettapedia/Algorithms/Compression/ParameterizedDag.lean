import Mettapedia.Algorithms.Compression.TypedDag
import Mettapedia.Algorithms.Compression.ParameterRegion

/-!
# Finite shared parameters in chronological DAG templates

Preparation assigns one slot to each named parameter. Retained producers
enumerate occurrence indices rather than packed constants. Materialization
selects one payload per slot and uses it at every reference to that slot.
The ordered index product agrees with the value product, including duplicate
alternatives. Instantiation preserves record positions and agrees with direct
template execution. Decoder admission and physical payload ownership remain
separate implementation boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.ParameterizedDag

open KolmogorovComplexity CompactDag

variable {α : Type*}

def indexDomains (domains : List (List α)) : List (List Nat) :=
  domains.map fun choices => List.range choices.length

def select : List (List α) → List Nat → Option (List α)
  | [], [] => some []
  | choices :: remaining, index :: indices =>
      choices[index]?.bind fun choice => (select remaining indices).map (choice :: ·)
  | _, _ => none

theorem select_length (domains : List (List α)) (indices : List Nat) (values : List α)
    (found : select domains indices = some values) :
    values.length = domains.length ∧ indices.length = domains.length := by
  induction domains generalizing indices values with
  | nil =>
      cases indices with
      | nil => cases Option.some.inj found; simp
      | cons index rest => simp [select] at found
  | cons choices remaining ih =>
      cases indices with
      | nil => simp [select] at found
      | cons index indices =>
          cases first : choices[index]? with
          | none => simp [select, first] at found
          | some value =>
              cases tail : select remaining indices with
              | none => simp [select, first, tail] at found
              | some rest =>
                  simp [select, first, tail] at found
                  subst values
                  obtain ⟨lengths, counts⟩ := ih indices rest tail
                  simp [lengths, counts]

theorem lookup_range (choices : List α) :
    (List.range choices.length).map (fun index => choices[index]?) = choices.map some := by
  induction choices with
  | nil => rfl
  | cons first rest ih =>
      simpa only [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map,
        Function.comp_def, List.getElem?_cons_zero, List.getElem?_cons_succ] using
        congrArg (some first :: ·) ih

/-- Index-based work retains exactly the ordered value alternatives. Distinct
domain occurrences remain separate even when their payloads are equal. -/
theorem selected_product (domains : List (List α)) :
    (ParameterRegion.product (indexDomains domains)).map (select domains) =
      (ParameterRegion.product domains).map some := by
  induction domains with
  | nil => rfl
  | cons choices remaining ih =>
      have step (index : Nat) :
          (ParameterRegion.product (indexDomains remaining)).map
              (fun indices => select (choices :: remaining) (index :: indices)) =
            (ParameterRegion.product remaining).map
              (fun values => (choices[index]?).map (fun value => value :: values)) := by
        have mapped := congrArg (List.map (fun tail =>
          (choices[index]?).bind fun value => tail.map (value :: ·))) ih
        cases found : choices[index]? <;>
          simpa [select, List.map_map, found, Function.comp_def] using mapped
      change (ParameterRegion.product (List.range choices.length :: indexDomains remaining)).map
          (select (choices :: remaining)) = (ParameterRegion.product (choices :: remaining)).map some
      simp only [ParameterRegion.product, List.map_flatMap, List.map_map, Function.comp_def, step]
      calc
        (List.range choices.length).flatMap (fun index =>
            (ParameterRegion.product remaining).map
              (fun values => (choices[index]?).map (fun value => value :: values))) =
          ((List.range choices.length).map (fun index => choices[index]?)).flatMap
            (fun first => (ParameterRegion.product remaining).map
              (fun values => first.map (fun value => value :: values))) := by
                rw [List.flatMap_map]
        _ = (choices.map some).flatMap (fun first =>
            (ParameterRegion.product remaining).map
              (fun values => first.map (fun value => value :: values))) := by rw [lookup_range]
        _ = choices.flatMap (fun first => (ParameterRegion.product remaining).map
            (fun values => some (first :: values))) := by simp [List.flatMap_map]

theorem complete_selected_product (domains : List (List α)) :
    ((ParameterRegion.run
      (ParameterRegion.work [([], indexDomains domains)]) [([], indexDomains domains)]).1).map
        (select domains) = (ParameterRegion.product domains).map some := by
  rw [ParameterRegion.complete_product, selected_product]

theorem selected_product_coverage (domains : List (List α)) (values : List α) :
    values ∈ ParameterRegion.product domains ↔
      ∃ indices, indices ∈ ParameterRegion.product (indexDomains domains) ∧
        select domains indices = some values := by
  constructor
  · intro present
    have member : some values ∈ (ParameterRegion.product domains).map some :=
      List.mem_map.mpr ⟨values, present, rfl⟩
    rw [← selected_product] at member
    exact List.mem_map.mp member
  · rintro ⟨indices, present, selected⟩
    have member : some values ∈ (ParameterRegion.product (indexDomains domains)).map (select domains) :=
      List.mem_map.mpr ⟨indices, present, selected⟩
    rw [selected_product] at member
    obtain ⟨actual, occurs, agrees⟩ := List.mem_map.mp member
    cases Option.some.inj agrees
    exact occurs

/-- Complete traversal is optimal only in the supplied finite value region,
under the actual artifact validator and cost, not a shortest-feature premise. -/
theorem fit_complete_optimal {Artifact : Type} (valid : Artifact → Bool) (cost : Artifact → Nat)
    (current : Artifact) (build : Option (List α) → Artifact) (domains : List (List α))
    (admitted : valid current = true) (values : List α)
    (present : values ∈ ParameterRegion.product domains) (checked : valid (build (some values)) = true) :
    cost (ParameterRegion.fit valid cost current (fun indices => build (select domains indices))
      (ParameterRegion.work [([], indexDomains domains)]) [([], indexDomains domains)]) ≤
        cost (build (some values)) := by
  obtain ⟨indices, occurs, selected⟩ := (selected_product_coverage domains values).mp present
  simpa only [selected] using ParameterRegion.fit_complete_optimal valid cost current
    (fun indices => build (select domains indices)) (indexDomains domains) admitted indices occurs
      (by simpa only [selected] using checked)

inductive TemplateRecord where
  | fixed : Record → TemplateRecord
  | parameter : Nat → TemplateRecord
  deriving DecidableEq, Repr

def instantiateRecord (parameters : List BinString) : TemplateRecord → Option Record
  | .fixed record => some record
  | .parameter index => parameters[index]?.map Record.leaf

def instantiate (parameters : List BinString) : List TemplateRecord → Option (List Record)
  | [] => some []
  | first :: rest => do
      let record ← instantiateRecord parameters first
      let tail ← instantiate parameters rest
      pure (record :: tail)

def interpretTemplate (leaf : BinString → α) (node : BinString → List α → α)
    (parameters : List BinString) (values : List α) : TemplateRecord → Option α
  | .fixed record => CompactDag.interpret leaf node values record
  | .parameter index => parameters[index]?.map leaf

def foldTemplate (leaf : BinString → α) (node : BinString → List α → α)
    (parameters : List BinString) : List TemplateRecord → List α → Option (List α)
  | [], values => some values
  | record :: rest, values => do
      let result ← interpretTemplate leaf node parameters values record
      foldTemplate leaf node parameters rest (values ++ [result])

theorem instantiate_record_agrees (leaf : BinString → α) (node : BinString → List α → α)
    (parameters : List BinString) (values : List α) (template : TemplateRecord) (record : Record)
    (built : instantiateRecord parameters template = some record) :
    CompactDag.interpret leaf node values record =
      interpretTemplate leaf node parameters values template := by
  cases template with
  | fixed original => cases Option.some.inj built; rfl
  | parameter index =>
      cases found : parameters[index]? with
      | none => simp [instantiateRecord, found] at built
      | some bytes =>
          simp [instantiateRecord, found] at built
          subst record
          simp [CompactDag.interpret, interpretTemplate, found]

/-- The materialized concrete DAG and the independent template interpreter
agree for any pure algebra, including algebras returning explicit faults. -/
theorem instantiate_fold_agrees (leaf : BinString → α) (node : BinString → List α → α)
    (parameters : List BinString) (template : List TemplateRecord) (records : List Record)
    (built : instantiate parameters template = some records) (values : List α) :
    CompactDag.foldRecords leaf node records values = foldTemplate leaf node parameters template values := by
  induction template generalizing records values with
  | nil => cases Option.some.inj built; rfl
  | cons first rest ih =>
      cases firstBuilt : instantiateRecord parameters first with
      | none => simp [instantiate, firstBuilt] at built
      | some record =>
          cases restBuilt : instantiate parameters rest with
          | none => simp [instantiate, firstBuilt, restBuilt] at built
          | some tail =>
              simp [instantiate, firstBuilt, restBuilt] at built
              subst records
              rw [CompactDag.foldRecords, foldTemplate, instantiate_record_agrees leaf node _ _ _ _ firstBuilt]
              cases result : interpretTemplate leaf node parameters values first with
              | none => rfl
              | some value => simpa [result] using ih tail restBuilt (values ++ [value])

theorem instantiate_length (parameters : List BinString) (template : List TemplateRecord)
    (records : List Record) (built : instantiate parameters template = some records) :
    records.length = template.length := by
  induction template generalizing records with
  | nil => cases Option.some.inj built; rfl
  | cons first rest ih =>
      cases firstBuilt : instantiateRecord parameters first with
      | none => simp [instantiate, firstBuilt] at built
      | some record =>
          cases restBuilt : instantiate parameters rest with
          | none => simp [instantiate, firstBuilt, restBuilt] at built
          | some tail =>
              simp [instantiate, firstBuilt, restBuilt] at built
              subst records
              simp [ih tail restBuilt]

def references : TemplateRecord → List Nat
  | .fixed (.node _ children) => children
  | _ => []

theorem instantiate_preserves_references (parameters : List BinString) (template : TemplateRecord)
    (record : Record) (built : instantiateRecord parameters template = some record) :
    references (.fixed record) = references template := by
  cases template with
  | fixed original => cases Option.some.inj built; rfl
  | parameter index =>
      cases found : parameters[index]? with
      | none => simp [instantiateRecord, found] at built
      | some bytes => simp [instantiateRecord, found] at built; subst record; rfl

section Types

variable {Label : Type}

def DomainsTyped (leafType : BinString → Option Label)
    (sorts : List Label) (domains : List (List BinString)) : Prop :=
  List.Forall₂ (fun sort choices => ∀ bytes ∈ choices, leafType bytes = some sort) sorts domains

theorem select_sorted (leafType : BinString → Option Label)
    {sorts : List Label} {domains : List (List BinString)}
    (typed : DomainsTyped leafType sorts domains) (indices : List Nat) (parameters : List BinString)
    (selected : select domains indices = some parameters) :
    List.Forall₂ (fun sort bytes => leafType bytes = some sort) sorts parameters := by
  induction typed generalizing indices parameters with
  | nil =>
      cases indices with
      | nil => cases Option.some.inj selected; exact .nil
      | cons first rest => simp [select] at selected
  | @cons sort choices sorts domains first rest ih =>
      cases indices with
      | nil => simp [select] at selected
      | cons index indices =>
          cases choice : choices[index]? with
          | none => simp [select, choice] at selected
          | some bytes =>
              cases remaining : select domains indices with
              | none => simp [select, choice, remaining] at selected
              | some tail =>
                  simp [select, choice, remaining] at selected
                  subst parameters
                  exact .cons (first bytes (List.mem_iff_getElem?.mpr ⟨index, choice⟩))
                    (ih indices tail remaining)

theorem parameter_lookup (leafType : BinString → Option Label)
    {sorts : List Label} {parameters : List BinString}
    (typed : List.Forall₂ (fun sort bytes => leafType bytes = some sort) sorts parameters)
    (index : Nat) : parameters[index]?.bind leafType = sorts[index]? := by
  induction typed generalizing index with
  | nil => simp
  | cons first rest ih => cases index <;> simp [first, ih]

variable [DecidableEq Label]

def inferTemplateRecord (leafType : BinString → Option Label)
    (contract : BinString → Option (TypedDag.Contract Label))
    (parameters types : List Label) : TemplateRecord → Option Label
  | .fixed record => TypedDag.inferRecord leafType contract types record
  | .parameter index => parameters[index]?

def inferTemplateRecords (leafType : BinString → Option Label)
    (contract : BinString → Option (TypedDag.Contract Label)) (parameters : List Label) :
    List TemplateRecord → List Label → Option (List Label)
  | [], types => some types
  | first :: rest, types => do
      let output ← inferTemplateRecord leafType contract parameters types first
      inferTemplateRecords leafType contract parameters rest (types ++ [output])

theorem instantiate_record_infers (leafType : BinString → Option Label)
    (contract : BinString → Option (TypedDag.Contract Label))
    {sorts : List Label} {parameters : List BinString}
    (typed : List.Forall₂ (fun sort bytes => leafType bytes = some sort) sorts parameters)
    (types : List Label) (template : TemplateRecord) (record : Record)
    (built : instantiateRecord parameters template = some record) :
    TypedDag.inferRecord leafType contract types record =
      inferTemplateRecord leafType contract sorts types template := by
  cases template with
  | fixed original => cases Option.some.inj built; rfl
  | parameter index =>
      cases found : parameters[index]? with
      | none => simp [instantiateRecord, found] at built
      | some bytes =>
          simp [instantiateRecord, found] at built
          subst record
          simpa [TypedDag.inferRecord, inferTemplateRecord, found] using
            parameter_lookup leafType typed index

theorem instantiate_records_infer (leafType : BinString → Option Label)
    (contract : BinString → Option (TypedDag.Contract Label))
    {sorts : List Label} {parameters : List BinString}
    (typed : List.Forall₂ (fun sort bytes => leafType bytes = some sort) sorts parameters)
    (template : List TemplateRecord) (records : List Record)
    (built : instantiate parameters template = some records) (types : List Label) :
    TypedDag.inferRecords leafType contract records types =
      inferTemplateRecords leafType contract sorts template types := by
  induction template generalizing records types with
  | nil => cases Option.some.inj built; rfl
  | cons first rest ih =>
      cases firstBuilt : instantiateRecord parameters first with
      | none => simp [instantiate, firstBuilt] at built
      | some record =>
          cases restBuilt : instantiate parameters rest with
          | none => simp [instantiate, firstBuilt, restBuilt] at built
          | some tail =>
              simp [instantiate, firstBuilt, restBuilt] at built
              subst records
              rw [TypedDag.inferRecords, inferTemplateRecords,
                instantiate_record_infers leafType contract typed _ _ _ firstBuilt]
              cases result : inferTemplateRecord leafType contract sorts types first with
              | none => rfl
              | some output => simpa [result] using ih tail restBuilt (types ++ [output])

/-- Actual domain validation and static template inference establish the
existing checked-DAG runtime contract for every selected parameter assignment.
Partial kernels still retain their ordinary checked failure results. -/
theorem selected_roots_sound {Value : Type} (kind : Value → Option Label)
    (leafType : BinString → Option Label) (contract : BinString → Option (TypedDag.Contract Label))
    (fetch : BinString → Option Value) (kernel : BinString → List Value → Option Value)
    (sorts : List Label) (domains : List (List BinString)) (indices : List Nat) (parameters : List BinString)
    (template : List TemplateRecord) (records : List Record) (roots : List Nat) (types rootTypes : List Label)
    (typedDomains : DomainsTyped leafType sorts domains)
    (selected : select domains indices = some parameters)
    (built : instantiate parameters template = some records)
    (typed : inferTemplateRecords leafType contract sorts template [] = some types)
    (rootSorts : gather types roots = some rootTypes) :
    ∃ results, CompactDag.evaluate (TypedDag.leafValue kind leafType fetch)
        (TypedDag.nodeValue kind contract kernel) ⟨roots, records⟩ = some results ∧
      TypedDag.Aligned kind rootTypes results := by
  have aligned := select_sorted leafType typedDomains indices parameters selected
  apply TypedDag.roots_sound kind leafType contract fetch kernel ⟨roots, records⟩ types rootTypes
  · rw [instantiate_records_infer leafType contract aligned template records built]
    exact typed
  · exact rootSorts

end Types

end Mettapedia.Algorithms.Compression.ParameterizedDag
