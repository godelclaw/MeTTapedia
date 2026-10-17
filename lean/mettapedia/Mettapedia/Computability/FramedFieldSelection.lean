import Mettapedia.Computability.WordHomomorphismMachine

/-!
# Executed selection of complete framed fields

One fixed finite machine selects a supplied list of field indices from an
original framed packet. Reordering, omission and duplicate occurrences are
explicit in the selector. Delimiters remain outside the data alphabet, and
both alphabet lifting and physical handoff are charged.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Computability.FramedFieldSelection
open Turing WordTemplateMachine
variable {Γ : Type} {arity : Nat}

def liftSymbol : Option Γ → List (Option (Option Γ))
  | none => [none]
  | some value => [some (some value)]

def liftedFields (fields : Fin arity → List Γ) : Fin arity → List (Option Γ) :=
  fun index => (fields index).map some

def template (indices : List (Fin arity)) : Indexed.Template (Option Γ) arity :=
  indices.flatMap fun index => [.inr index, .inl none]

theorem lift_frame (words : List (List Γ)) :
    (Indexed.frame words).flatMap liftSymbol = Indexed.frame (words.map (List.map some)) := by
  induction words with
  | nil => rfl
  | cons word rest ih =>
    simp only [Indexed.frame, List.flatMap_cons, List.flatMap_append, List.flatMap_nil, List.map_cons]
    change (word.map some).flatMap liftSymbol ++ (liftSymbol none ++ []) ++
      (Indexed.frame rest).flatMap liftSymbol = (word.map some).map some ++ [none] ++
        Indexed.frame (rest.map (List.map some))
    rw [ih]
    have inner : (word.map some).flatMap liftSymbol = (word.map some).map some := by
      induction word <;> simp_all [liftSymbol]
    rw [inner]
    rfl

theorem lift_exact (fields : Fin arity → List Γ) :
    (Indexed.argumentWire fields).flatMap liftSymbol = Indexed.argumentWire (liftedFields fields) := by
  unfold Indexed.argumentWire
  rw [lift_frame]
  simp only [List.map_map, Function.comp_def]
  rfl

theorem lifted_length (word : List (Option Γ)) : (word.flatMap liftSymbol).length = word.length := by
  induction word with
  | nil => rfl
  | cons symbol rest ih => cases symbol <;> simp [liftSymbol, ih]

theorem template_cons (index : Fin arity) (rest : List (Fin arity)) :
    template (Γ := Γ) (index :: rest) = [.inr index, .inl none] ++ template rest := by
  simp [template]

theorem template_length (indices : List (Fin arity)) : (template (Γ := Γ) indices).length = 2 * indices.length := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    rw [template_cons]
    simp only [List.length_append, List.length_cons, List.length_nil, ih]
    omega

theorem template_exact (indices : List (Fin arity)) (fields : Fin arity → List Γ) :
    Indexed.instantiate (template indices) (liftedFields fields) = Indexed.frame (indices.map fields) := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    rw [template_cons, Indexed.instantiate_append, ih]
    simp only [Indexed.instantiate_hole, Indexed.instantiate_literal, Indexed.instantiate_nil,
      List.map_cons, Indexed.frame, List.flatMap_cons, liftedFields]

variable [Fintype Γ] [Inhabited Γ]
local instance : Fintype ((WordHomomorphismMachine.machine (liftSymbol (Γ := Γ))).Γ
    (WordHomomorphismMachine.machine (liftSymbol (Γ := Γ))).k₁) := inferInstanceAs (Fintype (Option (Option Γ)))
local instance : Inhabited ((WordHomomorphismMachine.machine (liftSymbol (Γ := Γ))).Γ
    (WordHomomorphismMachine.machine (liftSymbol (Γ := Γ))).k₁) := inferInstanceAs (Inhabited (Option (Option Γ)))

def machine (indices : List (Fin arity)) : FinTM2 := StackMachineComposition.machine
  (WordHomomorphismMachine.machine (liftSymbol (Γ := Γ)))
  (Indexed.machine (template indices)) (Equiv.refl (Option (Option Γ)))

/-- Every selected occurrence and every delimiter is emitted by the machine.
The index list is fixed in its finite program; complete field bytes are input. -/
noncomputable def outputs (indices : List (Fin arity)) (fields : Fin arity → List Γ) :
    TM2OutputsInTime (machine indices) (Indexed.argumentWire fields)
      (some (Indexed.frame (indices.map fields)))
      ((8 * indices.length + 12) * ((Indexed.argumentWire fields).length + 1)) := by
  have lifted := WordHomomorphismMachine.outputs (liftSymbol (Γ := Γ)) (Indexed.argumentWire fields)
  have length := lifted_length (Indexed.argumentWire fields)
  rw [lift_exact] at lifted length
  have selected := Indexed.outputs (template indices) (liftedFields fields)
  rw [template_exact] at selected
  have joined := StackMachineComposition.outputs
    (WordHomomorphismMachine.machine (liftSymbol (Γ := Γ))) (Indexed.machine (template indices))
    (Equiv.refl (Option (Option Γ))) (Indexed.argumentWire fields)
    (Indexed.argumentWire (liftedFields fields)) (Indexed.frame (indices.map fields)) _ _ lifted (by
      change TM2OutputsInTime (Indexed.machine (template indices))
        ((Indexed.argumentWire (liftedFields fields)).map id) _ _
      simpa only [List.map_id] using selected)
  refine ⟨joined.toEvalsTo, joined.steps_le_m.trans ?_⟩
  simp only [template_length]
  change 2 * (Indexed.argumentWire fields).length + 2 * (Indexed.argumentWire (liftedFields fields)).length + 2 +
    2 * (Indexed.argumentWire (liftedFields fields)).length + 2 +
    4 * (2 * indices.length + 1) * ((Indexed.argumentWire (liftedFields fields)).length + 1) ≤ _
  rw [length]
  nlinarith

omit [Fintype Γ] [Inhabited Γ] in
theorem output_length (indices : List (Fin arity)) (fields : Fin arity → List Γ) :
    (Indexed.frame (indices.map fields)).length = (indices.map fun index => (fields index).length + 1).sum := by
  induction indices with
  | nil => rfl
  | cons index rest ih =>
    change ((fields index).map some ++ [none] ++ Indexed.frame (rest.map fields)).length =
      (fields index).length + 1 + (rest.map fun index => (fields index).length + 1).sum
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil, ih]

namespace Controls

theorem ordered_repeated_fields :
    Indexed.instantiate (template [1, 0, 1]) (liftedFields (![ [false], [true] ] : Fin 2 → List Bool)) =
      [some true, none, some false, none, some true, none] := by decide

theorem omitted_field_not_reflected :
    (![ [false], [false] ] : Fin 2 → List Bool) ≠ ![ [false], [true] ] ∧
      Indexed.instantiate (template [0]) (liftedFields (![ [false], [false] ] : Fin 2 → List Bool)) =
      Indexed.instantiate (template [0]) (liftedFields (![ [false], [true] ] : Fin 2 → List Bool)) := by decide
end Controls
end Mettapedia.Computability.FramedFieldSelection
