import Mettapedia.GSLT.LanguageDef.IndexedInductiveElimination
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedPolynomialGenerated

/-!
# The generated guest constructor inventory as an authored inductive

The established simple-inductive generator and the finite coGSLT admission
route share the same constructor rows here. Each closed field becomes an
interpreted data field, and each recursive field becomes one recursive
position. The comparison retains ordered payloads and constructor occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Generated

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality Normalization


universe u v w

variable {Head : Type}

def interface (Value : Tm Head 0 → Type u) : Interface.{u} where
  SortCode := Tm Head 0
  Value := Value
  Index := ULift.{u} Unit
  IndexExpr := fun _ => Unit
  evalIndex := fun _ _ => ⟨()⟩

/-- Interpret the generator's actual ordered field list as a source telescope. -/
def code (Value : Tm Head 0 → Type u) :
    List (Field Head) → {context : List (Tm Head 0)} → Code (interface Value) context
  | [], _ => .result ()
  | .recursive :: rest, _ => .recursive () (code Value rest)
  | .closed type :: rest, _ => .data type (code Value rest)

variable {Value : Tm Head 0 → Type u}

abbrev FieldArguments (fields : List (Field Head))
    {context : List (Tm Head 0)} (environment : Env Value context) (X : Type v) :=
  Arguments (I := interface Value) (fun _ => X) (code Value fields) environment ⟨()⟩

/-- Separate the ordered source arguments into the generator's data and children. -/
def split {X : Type v} : (fields : List (Field Head)) →
    {context : List (Tm Head 0)} → {environment : Env Value context} →
    FieldArguments fields environment X →
      IndexedPolynomialGenerated.ClosedData Value fields × (IndexedPolynomialGenerated.RecursivePosition fields → X)
  | [], _, _, _ => (⟨⟩, fun position => nomatch position)
  | .recursive :: rest, _, _, arguments =>
      let tail := split rest arguments.2
      (tail.1, fun position => match position with
        | .here => arguments.1
        | .recursiveTail prior => tail.2 prior)
  | .closed _ :: rest, _, _, arguments =>
      let tail := split rest arguments.2
      ((arguments.1, tail.1), fun position => match position with
        | .closedTail prior => tail.2 prior)

/-- Reinsert the generator's data and children into their original source positions. -/
def join {X : Type v} : (fields : List (Field Head)) →
    {context : List (Tm Head 0)} → {environment : Env Value context} →
    IndexedPolynomialGenerated.ClosedData Value fields → (IndexedPolynomialGenerated.RecursivePosition fields → X) →
      FieldArguments fields environment X
  | [], _, _, _, _ => ⟨⟨rfl⟩⟩
  | .recursive :: rest, _, _, data, children =>
      (children .here, join rest data (fun position => children (.recursiveTail position)))
  | .closed _ :: rest, _, _, data, children =>
      ⟨data.1, join rest data.2 (fun position => children (.closedTail position))⟩

theorem join_split {X : Type v} (fields : List (Field Head))
    {context : List (Tm Head 0)} {environment : Env Value context}
    (arguments : FieldArguments fields environment X) :
    join fields (split fields arguments).1 (split fields arguments).2 = arguments := by
  induction fields generalizing context with
  | nil =>
      rcases arguments with ⟨⟨equality⟩⟩
      rfl
  | cons field rest ih =>
      cases field with
      | recursive =>
          rcases arguments with ⟨child, arguments⟩
          simp only [split, join]
          exact congrArg (Prod.mk child) (ih arguments)
      | closed type =>
          rcases arguments with ⟨value, arguments⟩
          simp only [split, join]
          exact congrArg (fun remaining =>
            (⟨value, remaining⟩ : FieldArguments (.closed type :: rest) environment X))
            (ih arguments)

theorem split_join {X : Type v} (fields : List (Field Head))
    {context : List (Tm Head 0)} {environment : Env Value context}
    (data : IndexedPolynomialGenerated.ClosedData Value fields) (children : IndexedPolynomialGenerated.RecursivePosition fields → X) :
    split fields (join fields (environment := environment) data children) = (data, children) := by
  induction fields generalizing context with
  | nil =>
      cases data
      refine Prod.ext ?_ ?_
      · rfl
      · funext position
        cases position
  | cons field rest ih =>
      cases field with
      | recursive =>
          simp only [split, join]
          erw [ih]
          refine Prod.ext ?_ ?_
          · rfl
          · funext position
            cases position <;> rfl
      | closed type =>
          rcases data with ⟨value, data⟩
          simp only [split, join]
          erw [ih]
          refine Prod.ext ?_ ?_
          · rfl
          · funext position
            cases position
            rfl

/-- Every closed payload and recursive position agrees between the two routes. -/
def fieldArgumentsEquiv (fields : List (Field Head))
    {context : List (Tm Head 0)} (environment : Env Value context) (X : Type v) :
    FieldArguments fields environment X ≃
      IndexedPolynomialGenerated.ClosedData Value fields × (IndexedPolynomialGenerated.RecursivePosition fields → X) where
  toFun := split fields
  invFun := fun packed => join fields packed.1 packed.2
  left_inv := join_split fields
  right_inv := fun packed => split_join fields packed.1 packed.2

/-- The argument comparison is natural in recursive children: mapping them
does not change any closed payload or recursive occurrence. -/
theorem split_map {X : Type v} {Y : Type w} (mapping : X → Y)
    (fields : List (Field Head))
    {context : List (Tm Head 0)} {environment : Env Value context}
    (arguments : FieldArguments fields environment X) :
    split fields (Arguments.map (fun _ => mapping) (code Value fields) arguments) =
      ((split fields arguments).1, fun position => mapping ((split fields arguments).2 position)) := by
  induction fields generalizing context with
  | nil =>
      refine Prod.ext ?_ ?_
      · rfl
      · funext position
        cases position
  | cons field rest ih =>
      cases field with
      | recursive =>
          simp only [code, Arguments.map, split]
          erw [ih]
          refine Prod.ext ?_ ?_
          · rfl
          · funext position
            cases position <;> rfl
      | closed type =>
          simp only [code, Arguments.map, split]
          erw [ih]
          refine Prod.ext ?_ ?_
          · rfl
          · funext position
            cases position
            rfl

/-- Interpret source arguments directly as the guest's ordered term arguments. -/
def argumentTerms {n : Nat} (quote : ∀ type, Value type → Tm Head n) :
    (fields : List (Field Head)) → {context : List (Tm Head 0)} →
    {environment : Env Value context} →
    FieldArguments fields environment (Tm Head n) → List (Tm Head n)
  | [], _, _, _ => []
  | .recursive :: rest, _, _, arguments =>
      arguments.1 :: argumentTerms quote rest arguments.2
  | .closed type :: rest, _, _, arguments =>
      quote type arguments.1 :: argumentTerms quote rest arguments.2

theorem argumentTerms_eq_generated {n : Nat}
    (quote : ∀ type, Value type → Tm Head n) (fields : List (Field Head))
    {context : List (Tm Head 0)} {environment : Env Value context}
    (arguments : FieldArguments fields environment (Tm Head n)) :
    argumentTerms quote fields arguments =
      IndexedPolynomialGenerated.arguments quote fields (split fields arguments).1 (split fields arguments).2 := by
  induction fields generalizing context with
  | nil => rfl
  | cons field rest ih =>
      cases field with
      | recursive =>
          exact congrArg (List.cons arguments.1) (ih arguments.2)
      | closed type =>
          exact congrArg (List.cons (quote type arguments.1)) (ih arguments.2)

/-- Encode a constructor directly from the authored ordered arguments. -/
def constructorTerm {n : Nat} (quote : ∀ type, Value type → Tm Head n)
    (rows : List (DeclName × List (Field Head))) (occurrence : Fin rows.length)
    (arguments : FieldArguments (Value := Value) rows[occurrence].2 (context := [])
      ⟨⟩ (Tm Head n)) : Tm Head n :=
  appSpine (.const rows[occurrence].1) (argumentTerms quote rows[occurrence].2 arguments)

/-- The source route produces exactly the established guest encoding algebra's
constructor term, including the full ordered payload. -/
theorem constructorTerm_eq_generated {n : Nat} (quote : ∀ type, Value type → Tm Head n)
    (rows : List (DeclName × List (Field Head))) (occurrence : Fin rows.length)
    (arguments : FieldArguments (Value := Value) rows[occurrence].2 (context := [])
      ⟨⟩ (Tm Head n)) :
    constructorTerm quote rows occurrence arguments =
      (IndexedPolynomialGenerated.encodingAlgebra rows quote).act () ()
        ⟨⟨occurrence, (split rows[occurrence].2 arguments).1⟩,
          (split rows[occurrence].2 arguments).2⟩ :=
  congrArg (appSpine (.const rows[occurrence].1))
    (argumentTerms_eq_generated quote rows[occurrence].2 arguments)

/-- The same rows are authored, with public string names checked by admission. -/
def constructor (row : DeclName × List (Field Head)) : NamedConstructor (interface Value) [] :=
  ⟨row.1.toString, code Value row.2⟩

def constructors (rows : List (DeclName × List (Field Head))) :
    List (NamedConstructor (interface Value) []) := rows.map constructor

def admitted (rows : List (DeclName × List (Field Head)))
    (uniqueNames : (rows.map (fun row => row.1.toString)).Nodup) :
    Admitted (interface Value) [] where
  constructors := constructors rows
  uniqueNames := by simpa [constructors, constructor, List.map_map, Function.comp_def] using uniqueNames

/-- The generated rows pass through the actual coGSLT admission function. -/
theorem admitted_quote (rows : List (DeclName × List (Field Head)))
    (uniqueNames : (rows.map (fun row => row.1.toString)).Nodup) :
    admit? (IndexedInductive.quote (admitted (Value := Value) rows uniqueNames)) =
      some (admitted rows uniqueNames) := admit_quote _

/-- List mapping preserves the exact constructor occurrence number. -/
def occurrenceEquiv (rows : List (DeclName × List (Field Head))) :
    Fin (constructors (Value := Value) rows).length ≃ Fin rows.length where
  toFun := fun occurrence => ⟨occurrence.val, by
    simpa only [constructors, List.length_map] using occurrence.isLt⟩
  invFun := fun occurrence => ⟨occurrence.val, by
    simpa only [constructors, List.length_map] using occurrence.isLt⟩
  left_inv := fun _ => Fin.ext rfl
  right_inv := fun _ => Fin.ext rfl

/-- Constructor-indexed source arguments agree with the guest generator's layers. -/
def inventoryArgumentsEquivGenerated (rows : List (DeclName × List (Field Head)))
    (X : Type v) :
    InventoryArguments (constructors (Value := Value) rows) ⟨⟩ (fun _ => X) ⟨()⟩ ≃
      (Σ occurrence : Fin rows.length,
        IndexedPolynomialGenerated.ClosedData Value rows[occurrence].2 ×
          (IndexedPolynomialGenerated.RecursivePosition rows[occurrence].2 → X)) := by
  apply Equiv.sigmaCongr (occurrenceEquiv rows)
  intro occurrence
  have row : (constructors (Value := Value) rows).get occurrence =
      constructor (Value := Value) rows[(occurrenceEquiv (Value := Value) rows) occurrence] := by
    unfold constructors
    erw [List.get_eq_getElem, List.getElem_map]
    rfl
  rw [row]
  exact fieldArgumentsEquiv _ (context := []) ⟨⟩ X

/-- Reassociate the guest shape and children; no field value is transformed. -/
def generatedLayerEquiv (rows : List (DeclName × List (Field Head))) (X : Type v) :
    (Σ occurrence : Fin rows.length,
        IndexedPolynomialGenerated.ClosedData Value rows[occurrence].2 ×
          (IndexedPolynomialGenerated.RecursivePosition rows[occurrence].2 → X)) ≃
      (IndexedPolynomialGenerated.polynomial rows Value).Extension (fun _ _ => X) () () where
  toFun := fun layer => ⟨⟨layer.1, layer.2.1⟩, layer.2.2⟩
  invFun := fun layer => ⟨layer.1.1, layer.1.2, layer.2⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

/-- The polynomial compiled from the authored rows and the existing guest
generator have equivalent layers, including their payloads and recursive children. -/
def layerEquiv (rows : List (DeclName × List (Field Head))) (X : Type v) :
    (inventoryPolynomial (constructors (Value := Value) rows)).Extension
      (fun _ _ => X) ⟨⟩ ⟨()⟩ ≃
    (IndexedPolynomialGenerated.polynomial rows Value).Extension (fun _ _ => X) () () :=
  (inventoryArgumentsEquiv (constructors rows) ⟨⟩ (fun _ => X) ⟨()⟩).symm |>.trans
    ((inventoryArgumentsEquivGenerated rows X).trans (generatedLayerEquiv rows X))

namespace Canary

private def fields : List (Field Unit) :=
  [.closed (.head ()), .recursive, .closed (.head ())]

private def values (_ : Tm Unit 0) := Bool

private def arguments : FieldArguments (Value := values) fields (context := []) ⟨⟩ Nat :=
  ⟨true, 9, false, ⟨⟨rfl⟩⟩⟩

theorem ordered_closed_payloads :
    (split fields arguments).1 = (true, false, PUnit.unit) := rfl

theorem recursive_value_retained :
    (split fields arguments).2 (.closedTail .here) = 9 := rfl

theorem altered_closed_payload_rejected :
    (split fields arguments).1 ≠ (false, true, PUnit.unit) := by
  intro equal
  have same := congrArg Prod.fst equal
  cases same

theorem changed_recursive_value_rejected :
    (split fields arguments).2 (.closedTail .here) ≠ 8 := by decide

end Canary

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Generated
