import Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

open Mettapedia.OSLF.Framework

/-!
# Retained evidence for composite native questions

Proof and refutation families annotate the backend's actual physical receipts.
Filtering keeps their original order and duplicates. Each selected receipt
retains its checked recursive continuation certificate.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Reference.Receipts

open Mettapedia.GSLT
open GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core

universe u v w

def retainPositive {Item : Type v} {predicate : Item → Prop}
    (check : ∀ item, Outcome (predicate item)) : List Item → List (Sigma fun item => PLift (predicate item))
  | [] => []
  | item :: rest => match check item with
    | .proved proof => ⟨item, ⟨proof⟩⟩ :: retainPositive check rest
    | .refuted _ => retainPositive check rest
    | .unknown => retainPositive check rest

def retainNegative {Item : Type v} {predicate : Item → Prop}
    (check : ∀ item, Outcome (predicate item)) : List Item → List (Sigma fun item => PLift (¬ predicate item))
  | [] => []
  | item :: rest => match check item with
    | .proved _ => retainNegative check rest
    | .refuted refutation => ⟨item, ⟨refutation⟩⟩ :: retainNegative check rest
    | .unknown => retainNegative check rest

theorem positive_projection {Item : Type v} {predicate : Item → Prop}
    (check : ∀ item, Outcome (predicate item)) (items : List Item) :
    (retainPositive check items).map Sigma.fst =
      items.filter (fun item => (check item).answer == some true) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [retainPositive]
    cases result : check item <;> simp [Outcome.answer, result, ih]

theorem negative_projection {Item : Type v} {predicate : Item → Prop}
    (check : ∀ item, Outcome (predicate item)) (items : List Item) :
    (retainNegative check items).map Sigma.fst =
      items.filter (fun item => (check item).answer == some false) := by
  induction items with
  | nil => rfl
  | cons item rest ih =>
    simp only [retainNegative]
    cases result : check item <;> simp [Outcome.answer, result, ih]

theorem positive_member {Item : Type v} {predicate : Item → Prop}
    (check : ∀ item, Outcome (predicate item)) (items : List Item)
    (family : Sigma fun item => PLift (predicate item)) (selected : family ∈ retainPositive check items) :
    family.1 ∈ items := by
  have projected : family.1 ∈ (retainPositive check items).map Sigma.fst := List.mem_map.mpr ⟨family, selected, rfl⟩
  rw [positive_projection] at projected
  exact List.mem_of_mem_filter projected

theorem negative_member {Item : Type v} {predicate : Item → Prop}
    (check : ∀ item, Outcome (predicate item)) (items : List Item)
    (family : Sigma fun item => PLift (¬ predicate item)) (selected : family ∈ retainNegative check items) :
    family.1 ∈ items := by
  have projected : family.1 ∈ (retainNegative check items).map Sigma.fst := List.mem_map.mpr ⟨family, selected, rfl⟩
  rw [negative_projection] at projected
  exact List.mem_of_mem_filter projected

def positiveOutputs {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat) :
    List (Sigma fun receipt : backend.Receipt source =>
      PLift (denotation tests formula (backend.target source receipt))) :=
  retainPositive (fun receipt => raw backend tests (budget - 1) formula (backend.target source receipt))
    (backend.frontier budget source)

def negativeOutputs {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat) :
    List (Sigma fun receipt : backend.Receipt source =>
      PLift (¬ denotation tests formula (backend.target source receipt))) :=
  retainNegative (fun receipt => raw backend tests (budget - 1) formula (backend.target source receipt))
    (backend.frontier budget source)

theorem positive_output_native {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat)
    (family : Sigma fun receipt : backend.Receipt source =>
      PLift (denotation tests formula (backend.target source receipt)))
    (selected : family ∈ positiveOutputs backend tests formula source budget) :
    denotation tests (.possibility formula) source := by
  have listed := positive_member _ _ family selected
  exact (gsltDiamond_spec system (denotation tests formula).1 source).mpr
    ⟨backend.target source family.1, backend.sound budget source family.1 listed, family.2.down⟩

theorem negative_output_native {system : GSLT.{u}} {admitted : system.Term → Prop} {Leaf : Type w}
    (backend : Backend.{u,v} system admitted) (tests : Leaf → Test system admitted)
    (formula : Formula Leaf) (source : system.Term) (budget : Nat)
    (family : Sigma fun receipt : backend.Receipt source =>
      PLift (¬ denotation tests formula (backend.target source receipt)))
    (selected : family ∈ negativeOutputs backend tests formula source budget) :
    ¬ denotation tests (.outgoingUniversal formula) source := by
  intro all
  have listed := negative_member _ _ family selected
  exact family.2.down (all (backend.target source family.1) (backend.sound budget source family.1 listed))

end Mettapedia.OSLF.NativeTypes.Decision.Reference.Receipts
