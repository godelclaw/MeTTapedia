import Mettapedia.TypeTheory.IndexedPolynomialInduction
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.DeclarationLists

/-!
# Polynomial interpretation of generated simple-inductive recursors

The existing declaration generator uses recursive fields and closed field types.
This module interprets that same constructor inventory as a polynomial: closed
field values belong to its shapes, and recursive fields are its positions.
Encoding its initial trees uses the generator's constructor applications.

The generated guest recursor reduces to the corresponding displayed section.
This is a reduction theorem about the existing guest syntax and generated iota
rules, rather than a second recursor syntax or an assumed semantic equation.
Closed field interpretations and their encodings remain explicit parameters;
this theorem does not infer a universe policy or the meaning of arbitrary guest
closed types.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace IndexedPolynomialGenerated

open TypedEquality Normalization Annotated
open Mettapedia.TypeTheory

universe u

variable {Head : Type}

/-- The nonrecursive data in a constructor, in source order. -/
def ClosedData (Value : Tm Head 0 → Type u) : List (Field Head) → Type u
  | [] => PUnit
  | .recursive :: rest => ClosedData Value rest
  | .closed type :: rest => Value type × ClosedData Value rest

/-- A recursive position retains its place in the original field list. -/
inductive RecursivePosition : List (Field Head) → Type where
  | here {rest} : RecursivePosition (.recursive :: rest)
  | recursiveTail {rest} : RecursivePosition rest → RecursivePosition (.recursive :: rest)
  | closedTail {type rest} : RecursivePosition rest → RecursivePosition (.closed type :: rest)

/-- Put the closed data and recursive arguments back in source field order. -/
def arguments {Value : Tm Head 0 → Type u} {n : Nat}
    (quote : ∀ type, Value type → Tm Head n) :
    (fields : List (Field Head)) → ClosedData Value fields →
      (RecursivePosition fields → Tm Head n) → List (Tm Head n)
  | [], _, _ => []
  | .recursive :: rest, data, children =>
      children .here :: arguments quote rest data (fun p => children (.recursiveTail p))
  | .closed type :: rest, data, children =>
      quote type data.1 :: arguments quote rest data.2 (fun p => children (.closedTail p))

/-- List just the recursive values, in the generator's order. -/
def recursiveArguments {α : Type u} : (fields : List (Field Head)) →
    (RecursivePosition fields → α) → List α
  | [], _ => []
  | .recursive :: rest, children =>
      children .here :: recursiveArguments rest (fun p => children (.recursiveTail p))
  | .closed _ :: rest, children =>
      recursiveArguments rest (fun p => children (.closedTail p))

theorem arguments_length {Value : Tm Head 0 → Type u} {n : Nat}
    (quote : ∀ type, Value type → Tm Head n) :
    ∀ (fields : List (Field Head)) (data : ClosedData Value fields) children,
      (arguments quote fields data children).length = fields.length
  | [], _, _ => rfl
  | .recursive :: rest, data, children => by
      simp [arguments, arguments_length quote rest data]
  | .closed _ :: rest, data, children => by
      simp [arguments, arguments_length quote rest data.2]

theorem recArgs_arguments {Value : Tm Head 0 → Type u} {n : Nat}
    (quote : ∀ type, Value type → Tm Head n) :
    ∀ (fields : List (Field Head)) (data : ClosedData Value fields) children,
      recArgs fields (arguments quote fields data children) = recursiveArguments fields children
  | [], _, _ => rfl
  | .recursive :: rest, data, children => by
      simp [arguments, recArgs, recursiveArguments, recArgs_arguments quote rest data]
  | .closed _ :: rest, data, children => by
      simp [arguments, recArgs, recursiveArguments, recArgs_arguments quote rest data.2]

theorem recursiveArguments_map {α : Type u} {β : Type u} (map : α → β) :
    ∀ (fields : List (Field Head)) (children : RecursivePosition fields → α),
      (recursiveArguments fields children).map map =
        recursiveArguments fields (fun p => map (children p))
  | [], _ => rfl
  | .recursive :: rest, children => by
      simp [recursiveArguments, recursiveArguments_map map rest]
  | .closed _ :: rest, children => recursiveArguments_map map rest _

/-- The polynomial is derived from the generator's constructor rows. -/
def polynomial (ctors : List (DeclName × List (Field Head)))
    (Value : Tm Head 0 → Type u) : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Σ index : Fin ctors.length, ClosedData Value ctors[index].2
  Position shape := RecursivePosition ctors[shape.1].2
  next _ _ := ()

abbrev Tree (ctors : List (DeclName × List (Field Head)))
    (Value : Tm Head 0 → Type u) := IndexedPolynomial.Fix (polynomial ctors Value) () ()

variable (ctors : List (DeclName × List (Field Head)))
  {Value : Tm Head 0 → Type u} {n : Nat}
  (quote : ∀ type, Value type → Tm Head n)

/-- The existing guest constructor applications form a polynomial algebra. -/
def encodingAlgebra : IndexedPolynomial.Algebra (polynomial ctors Value)
    (fun _ _ => Tm Head n) where
  act _ _ layer := appSpine (.const ctors[layer.1.1].1)
    (arguments quote ctors[layer.1.1].2 layer.1.2 layer.2)

/-- Encode a polynomial tree into the established guest term grammar. -/
noncomputable def encode {base index : Unit} :
    IndexedPolynomial.Fix (polynomial ctors Value) base index → Tm Head n :=
  IndexedPolynomial.Fix.fold (polynomial ctors Value) (encodingAlgebra ctors quote).act base index

@[simp] theorem encode_roll {base index : Unit}
    (shape : (polynomial ctors Value).Shape base index)
    (children : ∀ _p, IndexedPolynomial.Fix (polynomial ctors Value) base ()) :
    encode ctors quote (.roll shape children) =
      appSpine (.const ctors[shape.1].1)
        (arguments quote ctors[shape.1].2 shape.2 (fun p => encode ctors quote (children p))) := rfl

/-- Constructor methods of the guest recursor, now as a displayed algebra.
The original fields are retained before the recursively computed hypotheses. -/
noncomputable def methods (method : Fin ctors.length → Tm Head n) :
    IndexedPolynomial.Algebra.Displayed (IndexedPolynomial.Algebra.initial (polynomial ctors Value))
      (fun _ _ _ => Tm Head n) where
  act _ _ shape children hypotheses :=
    appSpine (method shape.1)
      (arguments quote ctors[shape.1].2 shape.2 (fun p => encode ctors quote (children p)) ++
        recursiveArguments ctors[shape.1].2 hypotheses)

/-- The semantic result is derived by polynomial dependent elimination. -/
noncomputable def eliminate (method : Fin ctors.length → Tm Head n) {base index : Unit}
    (tree : IndexedPolynomial.Fix (polynomial ctors Value) base index) : Tm Head n :=
  (methods ctors quote method).initialSection.toFun base index tree

@[simp] theorem eliminate_roll (method : Fin ctors.length → Tm Head n)
    {base index : Unit} (shape : (polynomial ctors Value).Shape base index)
    (children : ∀ _p, IndexedPolynomial.Fix (polynomial ctors Value) base ()) :
    eliminate ctors quote method (.roll shape children) =
      appSpine (method shape.1)
        (arguments quote ctors[shape.1].2 shape.2 (fun p => encode ctors quote (children p)) ++
          recursiveArguments ctors[shape.1].2 (fun p => eliminate ctors quote method (children p))) := rfl

/-- Reduction uses the generated guest iota rules and the existing compatible
closure. No equations between semantic trees are assumed. -/
abbrev Steps (rec : DeclName) (source target : Tm Head n) : Prop :=
  Relation.ReflTransGen (StepCore (iotaComputation rec ctors) (fun _ _ => False)) source target

private theorem steps_app {rec : DeclName} {f f' a a' : Tm Head n}
    (function : Steps ctors rec f f') (argument : Steps ctors rec a a') :
    Steps ctors rec (.app f a) (.app f' a') := by
  have left : Steps ctors rec (.app f a) (.app f' a) := by
    induction function with
    | refl => exact .refl
    | tail _ step ih => exact .tail ih (.congAppFun step)
  have right : Steps ctors rec (.app f' a) (.app f' a') := by
    induction argument with
    | refl => exact .refl
    | tail _ step ih => exact .tail ih (.congAppArg step)
  exact left.trans right

private theorem steps_spine {rec : DeclName} {args args' : List (Tm Head n)}
    (arguments : List.Forall₂ (Steps ctors rec) args args') {f f' : Tm Head n}
    (function : Steps ctors rec f f') :
    Steps ctors rec (appSpine f args) (appSpine f' args') := by
  induction arguments generalizing f f' with
  | nil => exact function
  | cons head _ ih => exact ih (steps_app ctors function head)

private theorem forall₂_refl {rec : DeclName} (args : List (Tm Head n)) :
    List.Forall₂ (Steps ctors rec) args args := by
  induction args with
  | nil => exact .nil
  | cons _ _ ih => exact .cons .refl ih

private theorem forall₂_append {α β : Type} {R : α → β → Prop}
    {xs xs' : List α} {ys ys' : List β}
    (first : List.Forall₂ R xs ys) (second : List.Forall₂ R xs' ys') :
    List.Forall₂ R (xs ++ xs') (ys ++ ys') := by
  induction first with
  | nil => exact second
  | cons h _ ih => exact .cons h ih

private theorem recursiveArguments_forall₂ {α β : Type} {R : α → β → Prop} :
    ∀ (fields : List (Field Head)) (first : RecursivePosition fields → α)
      (second : RecursivePosition fields → β),
      (∀ p, R (first p) (second p)) →
      List.Forall₂ R (recursiveArguments fields first) (recursiveArguments fields second)
  | [], _, _, _ => .nil
  | .recursive :: rest, _first, _second, pointwise =>
      .cons (pointwise .here)
        (recursiveArguments_forall₂ rest _ _ (fun p => pointwise (.recursiveTail p)))
  | .closed _ :: rest, _first, _second, pointwise =>
      recursiveArguments_forall₂ rest _ _ (fun p => pointwise (.closedTail p))

/-- The syntactically generated guest recursor computes the polynomial
displayed section on every finite constructor tree. The result retains the
original arguments and the recursively computed hypotheses in source order. -/
theorem recursor_reduces (rec : DeclName) (motive : Tm Head n)
    (method : Fin ctors.length → Tm Head n) {base index : Unit}
    (tree : IndexedPolynomial.Fix (polynomial ctors Value) base index) :
    Steps ctors rec (recApp rec (motive :: List.ofFn method) (encode ctors quote tree))
      (eliminate ctors quote method tree) := by
  refine IndexedPolynomial.Fix.eliminate (polynomial ctors Value)
    (fun _ _ value => Steps ctors rec
      (recApp rec (motive :: List.ofFn method) (encode ctors quote value))
      (eliminate ctors quote method value)) ?_ base index tree
  intro _ _ shape children ih
  rw [encode_roll, eliminate_roll]
  let args := arguments quote ctors[shape.1].2 shape.2
    (fun p => encode ctors quote (children p))
  have root : IotaStep rec ctors
      (recApp rec (motive :: List.ofFn method) (appSpine (.const ctors[shape.1].1) args))
      (appSpine (method shape.1)
        (args ++ (recArgs ctors[shape.1].2 args).map
          (recApp rec (motive :: List.ofFn method)))) := by
    exact ⟨motive, List.ofFn method, shape.1.val, ctors[shape.1].1,
      ctors[shape.1].2, args, method shape.1, by simp,
      List.getElem?_eq_getElem shape.1.isLt, arguments_length quote _ _ _,
      by simp, rfl, rfl⟩
  refine Relation.ReflTransGen.head (.root root) ?_
  change Steps ctors rec _ (appSpine _ (args ++ _))
  have select := recArgs_arguments quote ctors[shape.1].2 shape.2
    (fun p => encode ctors quote (children p))
  change recArgs ctors[shape.1].2 args = _ at select
  rw [select, recursiveArguments_map]
  apply steps_spine ctors _ (Relation.ReflTransGen.refl)
  exact forall₂_append (forall₂_refl ctors args)
    (recursiveArguments_forall₂ _ _ _ ih)

end IndexedPolynomialGenerated
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
