import Mettapedia.OSLF.NativeTypes.Decision.Reference.Recorded

open Mettapedia.OSLF.Framework

/-!
# Witness and coverage evidence at a computed stopping horizon

A positive existential decision retains an actual receipt with a positive
continuation certificate. A negative outgoing universal decision retains
an actual counterreceipt. The opposite polarities imply checked local
coverage. These laws apply to the recorded algorithm, rather than to an
arbitrarily supplied record.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Reference.EvidenceLaws

open Mettapedia.GSLT
open GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core Mettapedia.OSLF.NativeTypes.Decision.Reference.Receipts
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Recorded

universe u v w

theorem map_answer {first second : Prop} (equivalent : first ↔ second)
    (result : Outcome first) : (Outcome.map equivalent result).answer = result.answer := by
  cases result <;> rfl

theorem exists_answer_true {Item : Type v} (predicate : Item → Prop)
    (check : ∀ item, Outcome (predicate item)) (items : List Item) :
    (Outcome.existsIn predicate check items).answer = some true ↔
      ∃ item, item ∈ items ∧ (check item).answer = some true := by
  induction items with
  | nil => simp [Outcome.existsIn, Outcome.answer]
  | cons item rest ih =>
    rw [Outcome.existsIn, map_answer, Outcome.lazyDisjunction_eq]
    cases first : check item <;> cases remaining : Outcome.existsIn predicate check rest <;>
      simp [Outcome.disjunction, Outcome.answer, first, remaining, List.mem_cons] at ih ⊢
    all_goals aesop

theorem forall_answer_false {Item : Type v} (predicate : Item → Prop)
    (check : ∀ item, Outcome (predicate item)) (items : List Item) :
    (Outcome.forallIn predicate check items).answer = some false ↔
      ∃ item, item ∈ items ∧ (check item).answer = some false := by
  induction items with
  | nil => simp [Outcome.forallIn, Outcome.answer]
  | cons item rest ih =>
    rw [Outcome.forallIn, map_answer, Outcome.lazyConjunction_eq]
    cases first : check item <;> cases remaining : Outcome.forallIn predicate check rest <;>
      simp [Outcome.conjunction, Outcome.answer, first, remaining, List.mem_cons] at ih ⊢
    all_goals aesop

theorem retained_positive_witness {Item : Type v} {predicate : Item → Prop}
    (check : ∀ item, Outcome (predicate item)) (items : List Item)
    (item : Item) (listed : item ∈ items) (positive : (check item).answer = some true) :
    ∃ family ∈ retainPositive check items, family.1 = item := by
  have filtered : item ∈ items.filter (fun current => (check current).answer == some true) := by
    simp only [List.mem_filter]
    exact ⟨listed, by simp [positive]⟩
  rw [← positive_projection check items] at filtered
  exact List.mem_map.mp filtered

theorem retained_negative_witness {Item : Type v} {predicate : Item → Prop}
    (check : ∀ item, Outcome (predicate item)) (items : List Item)
    (item : Item) (listed : item ∈ items) (negative : (check item).answer = some false) :
    ∃ family ∈ retainNegative check items, family.1 = item := by
  have filtered : item ∈ items.filter (fun current => (check current).answer == some false) := by
    simp only [List.mem_filter]
    exact ⟨listed, by simp [negative]⟩
  rw [← negative_projection check items] at filtered
  exact List.mem_map.mp filtered

theorem possibility_positive_receipt {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : Backend.{u,v} system admitted) (predicate : EquationPredicate system)
    (budget : Nat) (source : system.Term)
    (check : ∀ receipt : backend.Receipt source, Outcome (predicate (backend.target source receipt)))
    (positive : (possibilityOutcome backend predicate budget source check).answer = some true) :
    ∃ receipt, receipt ∈ backend.frontier budget source ∧ (check receipt).answer = some true := by
  apply (exists_answer_true _ _ _).mp
  unfold possibilityOutcome at positive
  generalize Outcome.existsIn (fun receipt => predicate (backend.target source receipt)) check
    (backend.frontier budget source) = result at positive ⊢
  cases result with
  | proved proof => rfl
  | refuted refutation =>
    by_cases complete : backend.closed budget source = true <;>
      simp [complete, Outcome.answer] at positive
  | unknown => simp [Outcome.answer] at positive

theorem universal_negative_receipt {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : Backend.{u,v} system admitted) (predicate : EquationPredicate system)
    (budget : Nat) (source : system.Term)
    (check : ∀ receipt : backend.Receipt source, Outcome (predicate (backend.target source receipt)))
    (negative : (universalOutcome backend predicate budget source check).answer = some false) :
    ∃ receipt, receipt ∈ backend.frontier budget source ∧ (check receipt).answer = some false := by
  apply (forall_answer_false _ _ _).mp
  unfold universalOutcome at negative
  generalize Outcome.forallIn (fun receipt => predicate (backend.target source receipt)) check
    (backend.frontier budget source) = result at negative ⊢
  cases result with
  | proved proof =>
    by_cases complete : backend.closed budget source = true <;>
      simp [complete, Outcome.answer] at negative
  | refuted refutation => rfl
  | unknown => simp [Outcome.answer] at negative

theorem possibility_negative_closed {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : Backend.{u,v} system admitted) (predicate : EquationPredicate system)
    (budget : Nat) (source : system.Term)
    (check : ∀ receipt : backend.Receipt source, Outcome (predicate (backend.target source receipt)))
    (negative : (possibilityOutcome backend predicate budget source check).answer = some false) :
    backend.closed budget source = true := by
  unfold possibilityOutcome at negative
  generalize Outcome.existsIn (fun receipt => predicate (backend.target source receipt)) check
    (backend.frontier budget source) = result at negative
  cases result with
  | proved proof => simp [Outcome.answer] at negative
  | refuted refutation =>
    by_cases complete : backend.closed budget source = true
    · exact complete
    · simp [complete, Outcome.answer] at negative
  | unknown => simp [Outcome.answer] at negative

theorem universal_positive_closed {system : GSLT.{u}} {admitted : system.Term → Prop}
    (backend : Backend.{u,v} system admitted) (predicate : EquationPredicate system)
    (budget : Nat) (source : system.Term)
    (check : ∀ receipt : backend.Receipt source, Outcome (predicate (backend.target source receipt)))
    (positive : (universalOutcome backend predicate budget source check).answer = some true) :
    backend.closed budget source = true := by
  unfold universalOutcome at positive
  generalize Outcome.forallIn (fun receipt => predicate (backend.target source receipt)) check
    (backend.frontier budget source) = result at positive
  cases result with
  | proved proof =>
    by_cases complete : backend.closed budget source = true
    · exact complete
    · simp [complete, Outcome.answer] at positive
  | refuted refutation => simp [Outcome.answer] at positive
  | unknown => simp [Outcome.answer] at positive

theorem raw_positive_witness {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat)
    (positive : (raw backend tests budget (.possibility formula) source).answer = some true) :
    ∃ family, family ∈ positiveOutputs backend tests formula source budget := by
  cases budget with
  | zero => cases positive
  | succ budget =>
    obtain ⟨receipt, listed, read⟩ := possibility_positive_receipt backend (denotation tests formula)
      (budget + 1) source (fun receipt => raw backend tests budget formula (backend.target source receipt)) positive
    obtain ⟨family, selected, _⟩ := retained_positive_witness
      (fun receipt => raw backend tests budget formula (backend.target source receipt)) _ receipt listed read
    exact ⟨family, selected⟩

theorem raw_negative_counterreceipt {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat)
    (negative : (raw backend tests budget (.outgoingUniversal formula) source).answer = some false) :
    ∃ family, family ∈ negativeOutputs backend tests formula source budget := by
  cases budget with
  | zero => cases negative
  | succ budget =>
    obtain ⟨receipt, listed, read⟩ := universal_negative_receipt backend (denotation tests formula)
      (budget + 1) source (fun receipt => raw backend tests budget formula (backend.target source receipt)) negative
    obtain ⟨family, selected, _⟩ := retained_negative_witness
      (fun receipt => raw backend tests budget formula (backend.target source receipt)) _ receipt listed read
    exact ⟨family, selected⟩

theorem raw_negative_possibility_closed {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat)
    (negative : (raw backend tests budget (.possibility formula) source).answer = some false) :
    backend.closed budget source = true := by
  cases budget with
  | zero => cases negative
  | succ budget =>
    exact possibility_negative_closed backend (denotation tests formula)
      (budget + 1) source (fun receipt => raw backend tests budget formula (backend.target source receipt)) negative

theorem raw_positive_universal_closed {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat)
    (positive : (raw backend tests budget (.outgoingUniversal formula) source).answer = some true) :
    backend.closed budget source = true := by
  cases budget with
  | zero => cases positive
  | succ budget =>
    exact universal_positive_closed backend (denotation tests formula)
      (budget + 1) source (fun receipt => raw backend tests budget formula (backend.target source receipt)) positive

theorem recorded_positive_witness {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat)
    (positive : (run backend tests (.possibility formula) source budget).outcome.answer = some true) :
    ∃ family, family ∈ positiveOutputs backend tests formula source
      (run backend tests (.possibility formula) source budget).horizon :=
  raw_positive_witness backend tests formula source _
    (run_stopped_at_answer backend tests (.possibility formula) source budget true positive)

theorem recorded_negative_counterreceipt {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat)
    (negative : (run backend tests (.outgoingUniversal formula) source budget).outcome.answer = some false) :
    ∃ family, family ∈ negativeOutputs backend tests formula source
      (run backend tests (.outgoingUniversal formula) source budget).horizon :=
  raw_negative_counterreceipt backend tests formula source _
    (run_stopped_at_answer backend tests (.outgoingUniversal formula) source budget false negative)

theorem recorded_negative_possibility_closed {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat)
    (negative : (run backend tests (.possibility formula) source budget).outcome.answer = some false) :
    (frontierView backend (run backend tests (.possibility formula) source budget)).closed = true :=
  raw_negative_possibility_closed backend tests formula source _
    (run_stopped_at_answer backend tests (.possibility formula) source budget false negative)

theorem recorded_positive_universal_closed {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat)
    (positive : (run backend tests (.outgoingUniversal formula) source budget).outcome.answer = some true) :
    (frontierView backend (run backend tests (.outgoingUniversal formula) source budget)).closed = true :=
  raw_positive_universal_closed backend tests formula source _
    (run_stopped_at_answer backend tests (.outgoingUniversal formula) source budget true positive)

theorem recorded_positive_receipt_evidence {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat)
    (positive : (run backend tests (.possibility formula) source budget).outcome.answer = some true) :
    ∃ receipt, receipt ∈ (frontierView backend (run backend tests (.possibility formula) source budget)).receipts ∧
      system.Step source (backend.target source receipt) ∧ denotation tests formula (backend.target source receipt) := by
  obtain ⟨family, selected⟩ := recorded_positive_witness backend tests formula source budget positive
  have listed := positive_member _ _ family selected
  exact ⟨family.1, listed, backend.sound _ source family.1 listed, family.2.down⟩

theorem recorded_negative_receipt_evidence {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat)
    (negative : (run backend tests (.outgoingUniversal formula) source budget).outcome.answer = some false) :
    ∃ receipt, receipt ∈ (frontierView backend (run backend tests (.outgoingUniversal formula) source budget)).receipts ∧
      system.Step source (backend.target source receipt) ∧ ¬ denotation tests formula (backend.target source receipt) := by
  obtain ⟨family, selected⟩ := recorded_negative_counterreceipt backend tests formula source budget negative
  have listed := negative_member _ _ family selected
  exact ⟨family.1, listed, backend.sound _ source family.1 listed, family.2.down⟩

theorem recorded_negative_possibility_coverage {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat)
    (negative : (run backend tests (.possibility formula) source budget).outcome.answer = some false)
    (target : system.Term) (step : system.Step source target) :
    ∃ receipt, receipt ∈ (frontierView backend (run backend tests (.possibility formula) source budget)).receipts ∧
      system.Equiv target (backend.target source receipt) :=
  view_coverage _ (recorded_negative_possibility_closed backend tests formula source budget negative) target step

theorem recorded_positive_universal_coverage {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat)
    (positive : (run backend tests (.outgoingUniversal formula) source budget).outcome.answer = some true)
    (target : system.Term) (step : system.Step source target) :
    ∃ receipt, receipt ∈ (frontierView backend (run backend tests (.outgoingUniversal formula) source budget)).receipts ∧
      system.Equiv target (backend.target source receipt) :=
  view_coverage _ (recorded_positive_universal_closed backend tests formula source budget positive) target step

end Mettapedia.OSLF.NativeTypes.Decision.Reference.EvidenceLaws
