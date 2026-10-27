import Mettapedia.Algorithms.Compression.TemplateMatching

/-!
# Finite typed template search beyond pairwise anti-unification

Constructor depth bounds an explicitly generated region. A fresh parameter is
named by its first position in the hole-occurrence stream; a reuse advances
that stream but keeps the previous name. A single state is threaded through
the entire forest, including both sides of a rule. Reuse requires both role
and sort agreement.

The relational grammar below is independent of the executable list generator.
Soundness and completeness concern this finite first-order region, not every
possible abstraction or an optimality claim about an interrupted search.
-/

namespace Mettapedia.Algorithms.Compression.TemplateGrammar

open Mettapedia.GSLT.LanguageDef.GauthierCanonicalSchema
open Mettapedia.GSLT.LanguageDef.GauthierRoleAntiUnification

structure Slot where
  role : HoleRole
  sort : String
  deriving DecidableEq, Repr

structure Operator where
  result : String
  inputs : List Slot
  deriving DecidableEq, Repr

structure Binding where
  slot : Slot
  index : Nat
  deriving DecidableEq, Repr

structure State where
  position : Nat
  holes : List Binding
  deriving DecidableEq, Repr

def fresh (slot : Slot) (state : State) : SchemaPattern × State :=
  (.hole slot.role state.position,
    ⟨state.position + 1, ⟨slot, state.position⟩ :: state.holes⟩)

def reuse (state : State) (binding : Binding) : SchemaPattern × State :=
  (.hole binding.slot.role binding.index, ⟨state.position + 1, state.holes⟩)

def holes (slot : Slot) (state : State) : List (SchemaPattern × State) :=
  fresh slot state ::
    (state.holes.filter (fun binding => binding.slot == slot)).map (reuse state)

def forests (generate : Slot → State → List (SchemaPattern × State)) :
    List Slot → State → List (List SchemaPattern × State)
  | [], state => [([], state)]
  | slot :: rest, state =>
      (generate slot state).flatMap fun (pattern, middle) =>
        (forests generate rest middle).map fun (patterns, final) =>
          (pattern :: patterns, final)

def terms (signature : List Operator) :
    Nat → Slot → State → List (SchemaPattern × State)
  | 0, slot, state => holes slot state
  | depth + 1, slot, state =>
      holes slot state ++ (signature.zipIdx.flatMap fun (op, index) =>
        if op.result = slot.sort then
          (forests (terms signature depth) op.inputs state).map fun (children, final) =>
            (.node index children, final)
        else [])

inductive Forest (relation : Slot → State → SchemaPattern → State → Prop) :
    List Slot → State → List SchemaPattern → State → Prop where
  | nil (state) : Forest relation [] state [] state
  | cons {slot slots before middle after pattern patterns} :
      relation slot before pattern middle → Forest relation slots middle patterns after →
      Forest relation (slot :: slots) before (pattern :: patterns) after

mutual

inductive Derives (signature : List Operator) :
    Nat → Slot → State → SchemaPattern → State → Prop where
  | fresh (depth slot state) :
      Derives signature depth slot state (fresh slot state).1 (fresh slot state).2
  | reuse (depth slot state binding) (present : binding ∈ state.holes)
      (typed : binding.slot = slot) :
      Derives signature depth slot state (reuse state binding).1 (reuse state binding).2
  | node {depth slot state op index children final} :
      (op, index) ∈ signature.zipIdx → op.result = slot.sort →
      DerivesForest signature depth op.inputs state children final →
      Derives signature (depth + 1) slot state (.node index children) final

inductive DerivesForest (signature : List Operator) :
    Nat → List Slot → State → List SchemaPattern → State → Prop where
  | nil (depth state) : DerivesForest signature depth [] state [] state
  | cons {depth slot slots before middle after pattern patterns} :
      Derives signature depth slot before pattern middle →
      DerivesForest signature depth slots middle patterns after →
      DerivesForest signature depth (slot :: slots) before (pattern :: patterns) after

end

theorem Forest.mono {first second : Slot → State → SchemaPattern → State → Prop}
    (implication : ∀ slot before pattern after,
      first slot before pattern after → second slot before pattern after)
    {slots before patterns after} (found : Forest first slots before patterns after) :
    Forest second slots before patterns after := by
  induction found with
  | nil state => exact .nil state
  | cons head _ tail => exact .cons (implication _ _ _ _ head) tail

theorem forests_mem_iff (generate : Slot → State → List (SchemaPattern × State))
    (slots : List Slot) (before after : State) (patterns : List SchemaPattern) :
    (patterns, after) ∈ forests generate slots before ↔
      Forest (fun slot state pattern final => (pattern, final) ∈ generate slot state)
        slots before patterns after := by
  induction slots generalizing before after patterns with
  | nil =>
      constructor
      · intro found
        simp only [forests, List.mem_singleton, Prod.mk.injEq] at found
        rcases found with ⟨rfl, rfl⟩
        exact .nil _
      · intro found
        cases found
        simp [forests]
  | cons slot slots ih =>
      constructor
      · intro found
        simp only [forests, List.mem_flatMap, List.mem_map] at found
        obtain ⟨⟨pattern, middle⟩, head, ⟨rest, final⟩, tail, equality⟩ := found
        cases equality
        exact .cons head ((ih middle final rest).mp tail)
      · intro found
        cases found with
        | cons head tail =>
            exact List.mem_flatMap.mpr ⟨_, head,
              List.mem_map.mpr ⟨_, (ih _ _ _).mpr tail, rfl⟩⟩

theorem holes_mem_iff (slot : Slot) (state : State) (pattern : SchemaPattern) (final : State) :
    (pattern, final) ∈ holes slot state ↔
      (pattern, final) = fresh slot state ∨
        ∃ binding ∈ state.holes, binding.slot = slot ∧ (pattern, final) = reuse state binding := by
  simp only [holes, List.mem_cons, List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro (equal | ⟨binding, ⟨present, typed⟩, equal⟩)
    · exact Or.inl equal
    · exact Or.inr ⟨binding, present, typed, equal.symm⟩
  · rintro (equal | ⟨binding, present, typed, equal⟩)
    · exact Or.inl equal
    · exact Or.inr ⟨binding, ⟨present, typed⟩, equal.symm⟩

theorem Forest.toDerives {signature depth slots before patterns after}
    (found : Forest (Derives signature depth) slots before patterns after) :
    DerivesForest signature depth slots before patterns after := by
  induction found with
  | nil state => exact .nil depth state
  | cons head _ tail => exact .cons head tail

theorem DerivesForest.toForest {signature depth slots before patterns after}
    (found : DerivesForest signature depth slots before patterns after) :
    Forest (Derives signature depth) slots before patterns after := by
  induction slots generalizing before patterns after with
  | nil => cases found; exact .nil _
  | cons slot slots ih =>
      cases found with
      | cons head tail => exact .cons head (ih tail)

/-- Exact agreement between the finite enumerator and independent productions. -/
theorem terms_mem_iff (signature : List Operator) (depth : Nat)
    (slot : Slot) (state final : State) (pattern : SchemaPattern) :
    (pattern, final) ∈ terms signature depth slot state ↔
      Derives signature depth slot state pattern final := by
  induction depth generalizing slot state final pattern with
  | zero =>
      constructor
      · intro found
        rcases (holes_mem_iff _ _ _ _).mp found with fresh | ⟨binding, present, typed, reused⟩
        · obtain ⟨hp, hs⟩ := Prod.mk.inj fresh
          rw [hp, hs]
          exact .fresh _ _ _
        · obtain ⟨hp, hs⟩ := Prod.mk.inj reused
          rw [hp, hs]
          exact .reuse _ _ _ _ present typed
      · intro found
        cases found with
        | fresh => exact (holes_mem_iff _ _ _ _).mpr (Or.inl rfl)
        | reuse _ _ _ binding present typed =>
            exact (holes_mem_iff _ _ _ _).mpr (Or.inr ⟨binding, present, typed, rfl⟩)
  | succ depth ih =>
      constructor
      · intro found
        rcases List.mem_append.mp found with hole | node
        · rcases (holes_mem_iff _ _ _ _).mp hole with fresh | ⟨binding, present, typed, reused⟩
          · obtain ⟨hp, hs⟩ := Prod.mk.inj fresh
            rw [hp, hs]
            exact .fresh _ _ _
          · obtain ⟨hp, hs⟩ := Prod.mk.inj reused
            rw [hp, hs]
            exact .reuse _ _ _ _ present typed
        · obtain ⟨⟨op, index⟩, present, generated⟩ := List.mem_flatMap.mp node
          by_cases typed : op.result = slot.sort
          · simp only [typed, ↓reduceIte] at generated
            obtain ⟨⟨children, after⟩, childrenFound, equality⟩ := List.mem_map.mp generated
            cases equality
            exact .node present typed
              ((((forests_mem_iff _ _ _ _ _).mp childrenFound).mono
                (fun _ _ _ _ member => (ih _ _ _ _).mp member)).toDerives)
          · simp [typed] at generated
      · intro found
        cases found with
        | fresh => exact List.mem_append_left _ ((holes_mem_iff _ _ _ _).mpr (Or.inl rfl))
        | reuse _ _ _ binding present typed =>
            exact List.mem_append_left _
              ((holes_mem_iff _ _ _ _).mpr (Or.inr ⟨binding, present, typed, rfl⟩))
        | node present typed childrenFound =>
            rename_i op index children
            apply List.mem_append_right
            apply List.mem_flatMap.mpr
            refine ⟨_, present, ?_⟩
            simp only [typed, ↓reduceIte]
            apply List.mem_map.mpr
            refine ⟨(children, final), ?_, rfl⟩
            apply (forests_mem_iff _ _ _ _ _).mpr
            exact childrenFound.toForest.mono (fun _ _ _ _ derived => (ih _ _ _ _).mpr derived)

theorem enumerate_mem_iff (signature : List Operator) (slots : List Slot) (depth : Nat)
    (patterns : List SchemaPattern) (final : State) :
    (patterns, final) ∈ forests (terms signature depth) slots ⟨0, []⟩ ↔
      DerivesForest signature depth slots ⟨0, []⟩ patterns final := by
  rw [forests_mem_iff]
  constructor
  · exact fun found => (found.mono
      (fun _ _ _ _ member => (terms_mem_iff _ _ _ _ _ _).mp member)).toDerives
  · exact fun found => found.toForest.mono
      (fun _ _ _ _ derived => (terms_mem_iff _ _ _ _ _ _).mpr derived)

private def valueT : Slot := ⟨.value, "T"⟩
private def rootT : Slot := ⟨.root, "T"⟩

example : (forests (terms [] 0) [valueT, valueT, valueT] ⟨0, []⟩).length = 5 := by decide

example : (forests (terms [] 0) [valueT, rootT, valueT] ⟨0, []⟩).length = 2 := by decide

example : (forests (terms [] 0) [valueT, ⟨.value, "Different"⟩] ⟨0, []⟩).length = 1 := by decide

end Mettapedia.Algorithms.Compression.TemplateGrammar
