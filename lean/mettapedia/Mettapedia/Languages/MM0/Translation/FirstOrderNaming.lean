import Mettapedia.Languages.MM0.Translation.FirstOrderSyntax
import Mettapedia.Languages.MM0.Kernel.FirstOrderTheories
import Mettapedia.GSLT.LanguageDef.DefinitionalEquations
import Std.Data.String.ToNat

/-!
# Naming the positions of a numbered pattern

An MM0 expression refers to the formals of its declaration by position. A
source schema refers to them by name. `named` writes a numbered first-order
pattern over a list of names, and `numbered` of the rule layer reads it
back: on patterns whose positions are all named, the two are inverse.

`Numbered count` is the class of patterns on which this holds: first-order
patterns over the first `count` positions. Every encoding of an expression
whose formalNames are below `count` is in the class, and typing an expression
bounds its formalNames by the length of its context.

The last section carries constructor support in the direction from MM0 to
the source: a constraint on the term symbols of an expression is a
constraint on the constructor names of the pattern it encodes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderNaming

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules
open Mettapedia.GSLT.LanguageDef.DefinitionalEquations
open Kernel FirstOrderSyntax

/-! ## Names for positions -/

/-- The name of the formal at a position. -/
def variableName (index : Nat) : String := "v" ++ Nat.repr index

theorem variableName_injective : Function.Injective variableName := by
  intro first second same
  exact Nat.repr_injective ((String.append_right_inj "v").mp same)

/-- The formals of a declaration with the given number of arguments. -/
def formalNames (count : Nat) : List String := (List.range count).map variableName

@[simp]
theorem formalNames_length (count : Nat) : (formalNames count).length = count := by
  simp [formalNames]

theorem formalNames_nodup (count : Nat) : (formalNames count).Nodup :=
  List.Nodup.map variableName_injective List.nodup_range

/-! ## Numbered patterns and their named form -/

mutual
  /-- Replace each position by its name. Other forms are left as they are. -/
  def named (names : List String) : Pattern → Pattern
    | .bvar index => .fvar (names[index]?.getD "")
    | .apply name arguments => .apply name (namedList names arguments)
    | pattern => pattern
  termination_by pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  def namedList (names : List String) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns => named names pattern :: namedList names patterns
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  /-- A first-order pattern over the first `count` positions. -/
  inductive Numbered (count : Nat) : Pattern → Prop where
    | position {index : Nat} : index < count → Numbered count (.bvar index)
    | constructor {name : String} {arguments : List Pattern} :
        NumberedList count arguments → Numbered count (.apply name arguments)

  inductive NumberedList (count : Nat) : List Pattern → Prop where
    | nil : NumberedList count []
    | cons {pattern : Pattern} {patterns : List Pattern} :
        Numbered count pattern → NumberedList count patterns →
        NumberedList count (pattern :: patterns)
end

mutual
  /-- The named form of a numbered pattern is a schema over the names. -/
  theorem Numbered.named_schema {names : List String} {pattern : Pattern}
      (wellNumbered : Numbered names.length pattern) : Schema names (named names pattern) := by
    cases wellNumbered with
    | @position index below =>
        have lookup : names[index]? = some names[index] := List.getElem?_eq_getElem below
        simp only [named, lookup, Option.getD_some]
        exact .metavariable (List.getElem_mem below)
    | constructor children =>
        simp only [named]
        exact .constructor children.named_schemas
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem NumberedList.named_schemas {names : List String} {patterns : List Pattern}
      (wellNumbered : NumberedList names.length patterns) :
      Schemas names (namedList names patterns) := by
    cases wellNumbered with
    | nil =>
        simp only [namedList]
        exact .nil
    | cons first rest =>
        simp only [namedList]
        exact .cons first.named_schema rest.named_schemas
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  /-- Numbering the named form gives the pattern back. -/
  theorem Numbered.numbered_named {names : List String} (distinct : names.Nodup)
      {pattern : Pattern} (wellNumbered : Numbered names.length pattern) :
      numbered names (named names pattern) = pattern := by
    cases wellNumbered with
    | @position index below =>
        have lookup : names[index]? = some names[index] := List.getElem?_eq_getElem below
        simp only [named, lookup, Option.getD_some, numbered]
        exact applyBindings_fvar_of_find (numberedBindings_lookup distinct lookup)
    | @constructor name arguments children =>
        have rest := children.numbered_named distinct
        simp only [named, numbered, applyBindings_apply]
        exact congrArg (Pattern.apply name) rest
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem NumberedList.numbered_named {names : List String} (distinct : names.Nodup)
      {patterns : List Pattern} (wellNumbered : NumberedList names.length patterns) :
      (namedList names patterns).map (numbered names) = patterns := by
    cases wellNumbered with
    | nil => simp [namedList]
    | cons first rest =>
        simp only [namedList, List.map_cons]
        rw [first.numbered_named distinct, rest.numbered_named distinct]
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  /-- Naming positions changes no constructor. -/
  theorem Numbered.constructorsWithin_named {allowed : String → Prop} {names : List String}
      {count : Nat} {pattern : Pattern} (wellNumbered : Numbered count pattern)
      (within : ConstructorsWithin allowed pattern) :
      ConstructorsWithin allowed (named names pattern) := by
    cases wellNumbered with
    | position _ =>
        simp only [named]
        trivial
    | constructor children =>
        simp only [named]
        exact ⟨within.1, children.constructorsWithin_named within.2⟩
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem NumberedList.constructorsWithin_named {allowed : String → Prop}
      {names : List String} {count : Nat} {patterns : List Pattern}
      (wellNumbered : NumberedList count patterns)
      (within : ConstructorListWithin allowed patterns) :
      ConstructorListWithin allowed (namedList names patterns) := by
    cases wellNumbered with
    | nil =>
        simp only [namedList]
        trivial
    | cons first rest =>
        simp only [namedList]
        exact ⟨first.constructorsWithin_named within.1, rest.constructorsWithin_named within.2⟩
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-! ## Encodings are numbered patterns -/

mutual
  /-- The pattern encoded by an expression is first-order over the
  formalNames of the expression. -/
  theorem encodes_numbered {names : List String} {count : Nat} {pattern : Pattern}
      {expression : Preterm} (encoded : Encodes names pattern expression)
      (below : Preterm.VarsBelow count expression) : Numbered count pattern := by
    cases encoded with
    | boundVariable index => exact .position below
    | constructor found arguments =>
        rw [Preterm.varsBelow_applyArgs] at below
        exact .constructor (encodesList_numbered arguments below.2)
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem encodesList_numbered {names : List String} {count : Nat} {patterns : List Pattern}
      {expressions : List Preterm}
      (encoded : List.Forall₂ (Encodes names) patterns expressions)
      (below : ∀ expression ∈ expressions, Preterm.VarsBelow count expression) :
      NumberedList count patterns := by
    cases encoded with
    | nil => exact .nil
    | cons first rest =>
        exact .cons (encodes_numbered first (below _ (by simp)))
          (encodesList_numbered rest fun expression member =>
            below expression (by simp [member]))
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-! ## Constructor support, from expressions to patterns -/

mutual
  /-- A constraint on the term symbols of an expression is a constraint on
  the constructors of the pattern it encodes. -/
  theorem encodes_constructorsWithin {names : List String} {allowedIndex : Nat → Prop}
      {allowedName : String → Prop}
      (transfer : ∀ name index, index? names name = some index →
        allowedIndex index → allowedName name)
      {pattern : Pattern} {expression : Preterm} (encoded : Encodes names pattern expression)
      (within : Preterm.SymbolsWithin allowedIndex expression) :
      ConstructorsWithin allowedName pattern := by
    cases encoded with
    | boundVariable index => trivial
    | constructor found arguments =>
        rw [Preterm.symbolsWithin_applyArgs] at within
        exact ⟨transfer _ _ found within.1,
          encodesList_constructorsWithin transfer arguments within.2⟩
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  theorem encodesList_constructorsWithin {names : List String} {allowedIndex : Nat → Prop}
      {allowedName : String → Prop}
      (transfer : ∀ name index, index? names name = some index →
        allowedIndex index → allowedName name)
      {patterns : List Pattern} {expressions : List Preterm}
      (encoded : List.Forall₂ (Encodes names) patterns expressions)
      (within : ∀ expression ∈ expressions, Preterm.SymbolsWithin allowedIndex expression) :
      ConstructorListWithin allowedName patterns := by
    cases encoded with
    | nil => trivial
    | cons first rest =>
        exact ⟨encodes_constructorsWithin transfer first (within _ (by simp)),
          encodesList_constructorsWithin transfer rest fun expression member =>
            within expression (by simp [member])⟩
  termination_by sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-! ## Controls -/

/-- Naming and numbering are inverse on a numbered pattern. -/
example : numbered ["ph", "ps"] (named ["ph", "ps"] (.apply "wi" [.bvar 1, .bvar 0])) =
    .apply "wi" [.bvar 1, .bvar 0] :=
  Numbered.numbered_named (by decide)
    (.constructor (.cons (.position (by decide)) (.cons (.position (by decide)) .nil)))

/-- A position without a name is not in the class. -/
example : ¬ Numbered 1 (.bvar 1) := by
  intro wellNumbered
  cases wellNumbered with
  | position below => exact absurd below (by decide)

/-- Distinct positions have distinct names. -/
example : variableName 3 ≠ variableName 12 :=
  fun same => absurd (variableName_injective same) (by decide)

end Mettapedia.Languages.MM0.Translation.FirstOrderNaming
