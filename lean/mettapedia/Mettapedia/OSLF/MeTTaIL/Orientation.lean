import Mettapedia.GSLT.LanguageDef.WellSorted
import Mathlib.Algebra.Group.Defs

/-!
# Orientation: a group acting on the data of a language

In Meredith's oriented processes the data carried by names and messages lie in a group, and the
group acts on terms: an element `g` multiplies every datum of a term on the left, at every depth of
quotation, inside patterns, messages and binder bodies. A language declares the sort of its data,
the constructors that write the group's multiplication, inverse and unit, and the constructor that
applies the action (`OrientationDecl`).

The traversal here, `mapData`, follows the declared parameter types and applies a function at every
data position that does not hold a variable. At a variable the action is not applied but recorded,
and a bound variable keeps its frame; an equation over patterns cannot make those distinctions,
which is why the action is computed rather than declared by equations.

- `read`: the group element a closed data word denotes; `dataNormal` writes every readable datum as
  its canonical word;
- `mapData_comp`, `mapData_congr`: traversals fuse, and agree when their functions agree on the
  data a term holds.

The action itself is frame-normal and defers at variables (`OrientationFrame`); data words with
variables have their normal form in `OrientationWords`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Orientation

open Syntax Mettapedia.GSLT.LanguageDef.WellSorted

/-- A language's orientation: its data sort, the group's constructors, and the action. -/
structure OrientationDecl where
  dataSort : String
  multiply : String
  inverse : String
  unit : String
  action : String
deriving Repr, DecidableEq

variable (language : LanguageDef) (decl : OrientationDecl)

/-- The declared parameter types of a constructor. -/
def paramTypes (label : String) : Option (List TypeExpr) :=
  (language.terms.find? (·.label == label)).bind fun rule => rule.params.mapM parameterType?

/-- The element type of a collection at a type: a collection type's element, or the element of the
bare collection constructor of a sort. -/
def elementType : TypeExpr → CollType → Option TypeExpr
  | .collection kind element, actual => if kind = actual then some element else none
  | .base sort, actual => language.terms.findSome? fun rule =>
      if rule.category = sort then
        match rule.params with
        | [.simple _ (.collection kind element)] => if kind = actual then some element else none
        | _ => none
      else none
  | _, _ => none

/-- A variable occurrence. -/
def isVariable : Pattern → Bool
  | .bvar _ | .fvar _ => true
  | _ => false

mutual
  /-- **Apply a function at every data position** of a term at a type that does not hold a variable,
  following the declared parameter types. -/
  def mapData (f : Pattern → Pattern) (type : TypeExpr) (pattern : Pattern) : Pattern :=
    if isVariable pattern then pattern
    else if type = .base decl.dataSort then f pattern
    else
      match pattern with
      | .apply label arguments =>
          match paramTypes language label with
          | some types => .apply label (mapArgs f types arguments)
          | none => .apply label arguments
      | .lambda binder body =>
          match type with
          | .arrow _ codomain => .lambda binder (mapData f codomain body)
          | _ => .lambda binder body
      | .multiLambda arity binders body =>
          match type with
          | .arrow _ codomain => .multiLambda arity binders (mapData f codomain body)
          | _ => .multiLambda arity binders body
      | .collection kind elements rest =>
          match elementType language type kind with
          | some element => .collection kind (mapList f element elements) rest
          | none => .collection kind elements rest
      | other => other
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  def mapArgs (f : Pattern → Pattern) : List TypeExpr → List Pattern → List Pattern
    | type :: types, argument :: arguments => mapData f type argument :: mapArgs f types arguments
    | _, arguments => arguments
  termination_by _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  def mapList (f : Pattern → Pattern) (element : TypeExpr) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => mapData f element pattern :: mapList f element patterns
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  /-- The data a term holds at its data positions, other than variables. -/
  def dataOf (type : TypeExpr) (pattern : Pattern) : List Pattern :=
    if isVariable pattern then []
    else if type = .base decl.dataSort then [pattern]
    else
      match pattern with
      | .apply label arguments =>
          match paramTypes language label with
          | some types => dataArgs types arguments
          | none => []
      | .lambda _ body =>
          match type with
          | .arrow _ codomain => dataOf codomain body
          | _ => []
      | .multiLambda _ _ body =>
          match type with
          | .arrow _ codomain => dataOf codomain body
          | _ => []
      | .collection kind elements _ =>
          match elementType language type kind with
          | some element => dataList element elements
          | none => []
      | _ => []
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  def dataArgs : List TypeExpr → List Pattern → List Pattern
    | type :: types, argument :: arguments => dataOf type argument ++ dataArgs types arguments
    | _, _ => []
  termination_by _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  def dataList (element : TypeExpr) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => dataOf element pattern ++ dataList element patterns
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-! ## Fusion and congruence -/

variable {language decl}

theorem mapData_variable {f : Pattern → Pattern} {type : TypeExpr} {pattern : Pattern}
    (isVar : isVariable pattern = true) : mapData language decl f type pattern = pattern := by
  rw [mapData.eq_def, if_pos isVar]

theorem mapData_data {f : Pattern → Pattern} {type : TypeExpr} {pattern : Pattern}
    (notVariable : isVariable pattern = false) (data : type = .base decl.dataSort) :
    mapData language decl f type pattern = f pattern := by
  rw [mapData.eq_def, if_neg (by simp [notVariable]), if_pos data]

theorem mapData_apply {f : Pattern → Pattern} {type : TypeExpr} (notData : type ≠ .base decl.dataSort)
    (label : String) (arguments : List Pattern) :
    mapData language decl f type (.apply label arguments) =
      match paramTypes language label with
      | some types => .apply label (mapArgs language decl f types arguments)
      | none => .apply label arguments := by
  rw [mapData.eq_def, if_neg (by simp [isVariable]), if_neg notData]

theorem mapData_lambda_arrow {f : Pattern → Pattern} (domain codomain : TypeExpr) (binder : Option String)
    (body : Pattern) :
    mapData language decl f (.arrow domain codomain) (.lambda binder body) =
      .lambda binder (mapData language decl f codomain body) := by
  rw [mapData.eq_def, if_neg (by simp [isVariable]), if_neg (by simp)]

theorem mapData_lambda_other {f : Pattern → Pattern} {type : TypeExpr} (notData : type ≠ .base decl.dataSort)
    (notArrow : ∀ domain codomain, type ≠ .arrow domain codomain) (binder : Option String) (body : Pattern) :
    mapData language decl f type (.lambda binder body) = .lambda binder body := by
  rw [mapData.eq_def, if_neg (by simp [isVariable]), if_neg notData]
  simp only

theorem mapData_multiLambda_arrow {f : Pattern → Pattern} (domain codomain : TypeExpr) (arity : Nat)
    (binders : List String) (body : Pattern) :
    mapData language decl f (.arrow domain codomain) (.multiLambda arity binders body) =
      .multiLambda arity binders (mapData language decl f codomain body) := by
  rw [mapData.eq_def, if_neg (by simp [isVariable]), if_neg (by simp)]

theorem mapData_multiLambda_other {f : Pattern → Pattern} {type : TypeExpr} (notData : type ≠ .base decl.dataSort)
    (notArrow : ∀ domain codomain, type ≠ .arrow domain codomain) (arity : Nat) (binders : List String)
    (body : Pattern) :
    mapData language decl f type (.multiLambda arity binders body) = .multiLambda arity binders body := by
  rw [mapData.eq_def, if_neg (by simp [isVariable]), if_neg notData]
  simp only

theorem mapData_subst {f : Pattern → Pattern} {type : TypeExpr} (notData : type ≠ .base decl.dataSort)
    (body replacement : Pattern) :
    mapData language decl f type (.subst body replacement) = .subst body replacement := by
  rw [mapData.eq_def, if_neg (by simp [isVariable]), if_neg notData]

theorem mapData_collection {f : Pattern → Pattern} {type : TypeExpr} (notData : type ≠ .base decl.dataSort)
    (kind : CollType) (elements : List Pattern) (rest : Option String) :
    mapData language decl f type (.collection kind elements rest) =
      match elementType language type kind with
      | some element => .collection kind (mapList language decl f element elements) rest
      | none => .collection kind elements rest := by
  rw [mapData.eq_def, if_neg (by simp [isVariable]), if_neg notData]

mutual
  /-- **Traversals fuse**, when the inner function never turns a datum into a variable. -/
  theorem mapData_comp {f g : Pattern → Pattern}
      (keeps : ∀ datum, isVariable datum = false → isVariable (g datum) = false) :
      ∀ (type : TypeExpr) (pattern : Pattern),
        mapData language decl f type (mapData language decl g type pattern) =
          mapData language decl (f ∘ g) type pattern
    | type, .bvar index => by
      rw [mapData_variable (f := g) (pattern := .bvar index) (by rfl), mapData_variable (f := f) (by rfl),
        mapData_variable (f := f ∘ g) (by rfl)]
    | type, .fvar name => by
      rw [mapData_variable (f := g) (pattern := .fvar name) (by rfl), mapData_variable (f := f) (by rfl),
        mapData_variable (f := f ∘ g) (by rfl)]
    | type, .apply label arguments => by
      by_cases data : type = .base decl.dataSort
      · rw [mapData_data (f := g) (by rfl) data, mapData_data (f := f) (keeps _ (by rfl)) data,
          mapData_data (f := f ∘ g) (by rfl) data]
        rfl
      · rw [mapData_apply data, mapData_apply data]
        cases found : paramTypes language label with
        | none => simp only; rw [mapData_apply data, found]
        | some types =>
          simp only
          rw [mapData_apply data, found]
          simp only
          rw [mapArgs_comp keeps types arguments]
    | type, .lambda binder body => by
      by_cases data : type = .base decl.dataSort
      · rw [mapData_data (f := g) (by rfl) data, mapData_data (f := f) (keeps _ (by rfl)) data,
          mapData_data (f := f ∘ g) (by rfl) data]
        rfl
      · by_cases arrow : ∃ domain codomain, type = .arrow domain codomain
        · obtain ⟨domain, codomain, rfl⟩ := arrow
          rw [mapData_lambda_arrow, mapData_lambda_arrow, mapData_lambda_arrow, mapData_comp keeps codomain body]
        · have notArrow : ∀ domain codomain, type ≠ .arrow domain codomain := fun domain codomain same =>
            arrow ⟨domain, codomain, same⟩
          rw [mapData_lambda_other data notArrow, mapData_lambda_other data notArrow,
            mapData_lambda_other data notArrow]
    | type, .multiLambda arity binders body => by
      by_cases data : type = .base decl.dataSort
      · rw [mapData_data (f := g) (by rfl) data, mapData_data (f := f) (keeps _ (by rfl)) data,
          mapData_data (f := f ∘ g) (by rfl) data]
        rfl
      · by_cases arrow : ∃ domain codomain, type = .arrow domain codomain
        · obtain ⟨domain, codomain, rfl⟩ := arrow
          rw [mapData_multiLambda_arrow, mapData_multiLambda_arrow, mapData_multiLambda_arrow,
            mapData_comp keeps codomain body]
        · have notArrow : ∀ domain codomain, type ≠ .arrow domain codomain := fun domain codomain same =>
            arrow ⟨domain, codomain, same⟩
          rw [mapData_multiLambda_other data notArrow, mapData_multiLambda_other data notArrow,
            mapData_multiLambda_other data notArrow]
    | type, .subst body replacement => by
      by_cases data : type = .base decl.dataSort
      · rw [mapData_data (f := g) (by rfl) data, mapData_data (f := f) (keeps _ (by rfl)) data,
          mapData_data (f := f ∘ g) (by rfl) data]
        rfl
      · rw [mapData_subst data, mapData_subst data, mapData_subst data]
    | type, .collection kind elements rest => by
      by_cases data : type = .base decl.dataSort
      · rw [mapData_data (f := g) (by rfl) data, mapData_data (f := f) (keeps _ (by rfl)) data,
          mapData_data (f := f ∘ g) (by rfl) data]
        rfl
      · rw [mapData_collection data, mapData_collection data]
        cases found : elementType language type kind with
        | none => simp only; rw [mapData_collection data, found]
        | some element =>
          simp only
          rw [mapData_collection data, found]
          simp only
          rw [mapList_comp keeps element elements]
  termination_by _ pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mapArgs_comp {f g : Pattern → Pattern}
      (keeps : ∀ datum, isVariable datum = false → isVariable (g datum) = false) :
      ∀ (types : List TypeExpr) (arguments : List Pattern),
        mapArgs language decl f types (mapArgs language decl g types arguments) =
          mapArgs language decl (f ∘ g) types arguments
    | type :: types, argument :: arguments => by
      simp only [mapArgs]
      rw [mapData_comp keeps type argument, mapArgs_comp keeps types arguments]
    | [], arguments => by simp [mapArgs]
    | _ :: _, [] => by simp [mapArgs]
  termination_by _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mapList_comp {f g : Pattern → Pattern}
      (keeps : ∀ datum, isVariable datum = false → isVariable (g datum) = false) :
      ∀ (element : TypeExpr) (patterns : List Pattern),
        mapList language decl f element (mapList language decl g element patterns) =
          mapList language decl (f ∘ g) element patterns
    | _, [] => by simp [mapList]
    | element, pattern :: patterns => by
      simp only [mapList]
      rw [mapData_comp keeps element pattern, mapList_comp keeps element patterns]
  termination_by _ patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

theorem dataOf_variable {type : TypeExpr} {pattern : Pattern} (isVar : isVariable pattern = true) :
    dataOf language decl type pattern = [] := by
  rw [dataOf.eq_def, if_pos isVar]

theorem dataOf_data {type : TypeExpr} {pattern : Pattern} (notVariable : isVariable pattern = false)
    (data : type = .base decl.dataSort) : dataOf language decl type pattern = [pattern] := by
  rw [dataOf.eq_def, if_neg (by simp [notVariable]), if_pos data]

theorem dataOf_apply {type : TypeExpr} (notData : type ≠ .base decl.dataSort) (label : String)
    (arguments : List Pattern) :
    dataOf language decl type (.apply label arguments) =
      match paramTypes language label with
      | some types => dataArgs language decl types arguments
      | none => [] := by
  rw [dataOf.eq_def, if_neg (by simp [isVariable]), if_neg notData]

theorem dataOf_lambda_arrow (domain codomain : TypeExpr) (binder : Option String) (body : Pattern) :
    dataOf language decl (.arrow domain codomain) (.lambda binder body) = dataOf language decl codomain body := by
  rw [dataOf.eq_def, if_neg (by simp [isVariable]), if_neg (by simp)]

theorem dataOf_multiLambda_arrow (domain codomain : TypeExpr) (arity : Nat) (binders : List String) (body : Pattern) :
    dataOf language decl (.arrow domain codomain) (.multiLambda arity binders body) =
      dataOf language decl codomain body := by
  rw [dataOf.eq_def, if_neg (by simp [isVariable]), if_neg (by simp)]

theorem dataOf_collection {type : TypeExpr} (notData : type ≠ .base decl.dataSort) (kind : CollType)
    (elements : List Pattern) (rest : Option String) :
    dataOf language decl type (.collection kind elements rest) =
      match elementType language type kind with
      | some element => dataList language decl element elements
      | none => [] := by
  rw [dataOf.eq_def, if_neg (by simp [isVariable]), if_neg notData]

mutual
  /-- **Traversals agree** when their functions agree on the data the term holds. -/
  theorem mapData_congr {f g : Pattern → Pattern} :
      ∀ (type : TypeExpr) (pattern : Pattern), (∀ datum ∈ dataOf language decl type pattern, f datum = g datum) →
        mapData language decl f type pattern = mapData language decl g type pattern
    | type, .bvar index, _ => by rw [mapData_variable (by rfl), mapData_variable (by rfl)]
    | type, .fvar name, _ => by rw [mapData_variable (by rfl), mapData_variable (by rfl)]
    | type, .apply label arguments, agree => by
      by_cases data : type = .base decl.dataSort
      · rw [dataOf_data (by rfl) data] at agree
        rw [mapData_data (by rfl) data, mapData_data (by rfl) data]
        exact agree _ (.head _)
      · rw [dataOf_apply data] at agree
        rw [mapData_apply data, mapData_apply data]
        cases found : paramTypes language label with
        | none => rfl
        | some types =>
          rw [found] at agree
          simp only
          rw [mapArgs_congr types arguments agree]
    | type, .lambda binder body, agree => by
      by_cases data : type = .base decl.dataSort
      · rw [dataOf_data (by rfl) data] at agree
        rw [mapData_data (by rfl) data, mapData_data (by rfl) data]
        exact agree _ (.head _)
      · by_cases arrow : ∃ domain codomain, type = .arrow domain codomain
        · obtain ⟨domain, codomain, rfl⟩ := arrow
          rw [dataOf_lambda_arrow] at agree
          rw [mapData_lambda_arrow, mapData_lambda_arrow, mapData_congr codomain body agree]
        · have notArrow : ∀ domain codomain, type ≠ .arrow domain codomain := fun domain codomain same =>
            arrow ⟨domain, codomain, same⟩
          rw [mapData_lambda_other data notArrow, mapData_lambda_other data notArrow]
    | type, .multiLambda arity binders body, agree => by
      by_cases data : type = .base decl.dataSort
      · rw [dataOf_data (by rfl) data] at agree
        rw [mapData_data (by rfl) data, mapData_data (by rfl) data]
        exact agree _ (.head _)
      · by_cases arrow : ∃ domain codomain, type = .arrow domain codomain
        · obtain ⟨domain, codomain, rfl⟩ := arrow
          rw [dataOf_multiLambda_arrow] at agree
          rw [mapData_multiLambda_arrow, mapData_multiLambda_arrow, mapData_congr codomain body agree]
        · have notArrow : ∀ domain codomain, type ≠ .arrow domain codomain := fun domain codomain same =>
            arrow ⟨domain, codomain, same⟩
          rw [mapData_multiLambda_other data notArrow, mapData_multiLambda_other data notArrow]
    | type, .subst body replacement, agree => by
      by_cases data : type = .base decl.dataSort
      · rw [dataOf_data (by rfl) data] at agree
        rw [mapData_data (by rfl) data, mapData_data (by rfl) data]
        exact agree _ (.head _)
      · rw [mapData_subst data, mapData_subst data]
    | type, .collection kind elements rest, agree => by
      by_cases data : type = .base decl.dataSort
      · rw [dataOf_data (by rfl) data] at agree
        rw [mapData_data (by rfl) data, mapData_data (by rfl) data]
        exact agree _ (.head _)
      · rw [dataOf_collection data] at agree
        rw [mapData_collection data, mapData_collection data]
        cases found : elementType language type kind with
        | none => rfl
        | some element =>
          rw [found] at agree
          simp only
          rw [mapList_congr element elements agree]
  termination_by _ pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mapArgs_congr {f g : Pattern → Pattern} :
      ∀ (types : List TypeExpr) (arguments : List Pattern),
        (∀ datum ∈ dataArgs language decl types arguments, f datum = g datum) →
        mapArgs language decl f types arguments = mapArgs language decl g types arguments
    | type :: types, argument :: arguments, agree => by
      simp only [dataArgs, List.mem_append] at agree
      simp only [mapArgs]
      rw [mapData_congr type argument fun datum member => agree datum (.inl member),
        mapArgs_congr types arguments fun datum member => agree datum (.inr member)]
    | [], arguments, _ => by simp [mapArgs]
    | _ :: _, [], _ => by simp [mapArgs]
  termination_by _ arguments => sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec

  theorem mapList_congr {f g : Pattern → Pattern} :
      ∀ (element : TypeExpr) (patterns : List Pattern),
        (∀ datum ∈ dataList language decl element patterns, f datum = g datum) →
        mapList language decl f element patterns = mapList language decl g element patterns
    | _, [], _ => by simp [mapList]
    | element, pattern :: patterns, agree => by
      simp only [dataList, List.mem_append] at agree
      simp only [mapList]
      rw [mapData_congr element pattern fun datum member => agree datum (.inl member),
        mapList_congr element patterns fun datum member => agree datum (.inr member)]
  termination_by _ patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-! ## Reading data -/

variable (language decl)

variable {G : Type} [Group G]

/-- The group element a data word denotes, given the elements its constants denote. -/
def read (constant : String → Option G) : Pattern → Option G
  | .apply label [] => if label = decl.unit then some 1 else constant label
  | .apply label [argument] => if label = decl.inverse then (read constant argument).map (·⁻¹) else none
  | .apply label [left, right] =>
      if label = decl.multiply then
        match read constant left, read constant right with
        | some x, some y => some (x * y)
        | _, _ => none
      else none
  | _ => none
termination_by pattern => sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

/-- A reading of a language's data in a group, with a canonical word for every element. -/
structure DataReading (G : Type) [Group G] where
  constant : String → Option G
  write : G → Pattern
  read_write : ∀ x, read decl constant (write x) = some x

/-- A datum's canonical word, when it is readable. -/
def canonicalData (reading : DataReading decl G) (datum : Pattern) : Pattern :=
  match read decl reading.constant datum with
  | some x => reading.write x
  | none => datum

/-- Every readable datum written as its canonical word. -/
def dataNormal (reading : DataReading decl G) (type : TypeExpr) (pattern : Pattern) : Pattern :=
  mapData language decl (canonicalData decl reading) type pattern

variable {language decl}

theorem read_multiply (constant : String → Option G) (left right : Pattern) :
    read decl constant (.apply decl.multiply [left, right]) =
      match read decl constant left, read decl constant right with
      | some x, some y => some (x * y)
      | _, _ => none := by
  rw [read, if_pos rfl]

theorem read_unit (constant : String → Option G) : read decl constant (.apply decl.unit []) = some 1 := by
  rw [read, if_pos rfl]

theorem read_variable (constant : String → Option G) {datum : Pattern} (isVar : isVariable datum = true) :
    read decl constant datum = none := by
  cases datum <;> simp_all [isVariable, read]

theorem write_notVariable (reading : DataReading decl G) (x : G) : isVariable (reading.write x) = false := by
  cases written : isVariable (reading.write x) with
  | false => rfl
  | true =>
    have := reading.read_write x
    rw [read_variable reading.constant written] at this
    cases this

theorem canonicalData_notVariable (reading : DataReading decl G) {datum : Pattern}
    (notVariable : isVariable datum = false) : isVariable (canonicalData decl reading datum) = false := by
  unfold canonicalData
  split
  · exact write_notVariable reading _
  · exact notVariable

end Mettapedia.OSLF.MeTTaIL.Orientation
