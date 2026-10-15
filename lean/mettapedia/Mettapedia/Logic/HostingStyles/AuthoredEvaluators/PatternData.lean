import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ExtractionComparisonLaws
import Mettapedia.OSLF.MeTTaIL.Match

/-!
# Patterns as data of the equation engine

An equation program computes on the engine's first-order terms.  For a
program to answer the premises of a presented language, the patterns of the
language are given to it as such terms.  This module fixes that reading once,
for every program.

* A list is a chain of cells (`cells`), so that equations can take a list
  apart by matching.
* A name is the list of the codes of its characters (`encodeName`), so that a
  program can compare names and can build one.
* A pattern is a tagged expression, one tag for each of its seven forms
  (`encodePattern`).  Nothing is left out: the labels, the names of the
  variables, the indices, the binders and the kinds of collections are all in
  the term.
* The reading has a left inverse (`decodePattern`,
  `decodePattern_encodePattern`), so it is injective
  (`encodePattern_injective`), and the equality primitive of the shared host
  decides the equality of two patterns from their terms.
* The terms of names are data for every program and every host for which the
  tags of cells are constructors (`encodeName_passive`): a program may write a
  name in the body of an equation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AuthoredEvaluators

open Mettapedia.GSLT.LanguageDef.DeterministicEquations
open Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction (encodeOption)
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Lists and names -/

/-- **A list, as cells.** -/
def cells : List Term → Term
  | [] => .sym "Nil"
  | head :: tail => .expr [.sym "Cons", head, cells tail]

/-- The items of a chain of cells. -/
def uncells : Term → Option (List Term)
  | .sym "Nil" => some []
  | .expr [.sym "Cons", head, tail] => (uncells tail).map (head :: ·)
  | _ => none

@[simp] theorem uncells_cells : ∀ items : List Term, uncells (cells items) = some items
  | [] => rfl
  | head :: tail => by simp [cells, uncells, uncells_cells tail]

theorem cells_injective : Function.Injective cells := fun first second same =>
  Option.some.inj (by rw [← uncells_cells first, same, uncells_cells second])

/-- **Negative**: a list value of the engine is no chain of cells. -/
theorem uncells_list (items : List Term) : uncells (.list items) = none := rfl

/-- A character, as its code. -/
def encodeCharacter (character : Char) : Term := natural character.toNat

/-- The character of a code. -/
def decodeCharacter (code : Term) : Option Char := (natural? code).map Char.ofNat

@[simp] theorem decodeCharacter_encodeCharacter (character : Char) :
    decodeCharacter (encodeCharacter character) = some character := by
  simp [decodeCharacter, encodeCharacter]

/-- **Negative**: a symbol is the code of no character. -/
theorem decodeCharacter_symbol (name : String) : decodeCharacter (.sym name) = none := rfl

/-- **A name, as the list of the codes of its characters.** -/
def encodeName (name : String) : Term := cells (name.toList.map encodeCharacter)

/-- The name of a list of codes. -/
def decodeName (data : Term) : Option String :=
  (uncells data).bind fun items => (items.mapM decodeCharacter).map String.ofList

theorem mapM_decodeCharacter (characters : List Char) :
    characters.mapM (decodeCharacter ∘ encodeCharacter) = some characters := by
  induction characters with
  | nil => rfl
  | cons head tail ih => simp [List.mapM_cons, ih]

@[simp] theorem decodeName_encodeName (name : String) : decodeName (encodeName name) = some name := by
  simp [decodeName, encodeName, mapM_decodeCharacter, String.ofList_toList]

theorem encodeName_injective : Function.Injective encodeName := fun first second same =>
  Option.some.inj (by rw [← decodeName_encodeName first, same, decodeName_encodeName second])

/-- **Positive**: the name `x`, one cell. -/
theorem encodeName_x : encodeName "x" = cells [encodeCharacter 'x'] := by rfl

/-- **Negative**: two names are two data. -/
theorem encodeName_ne : encodeName "x" ≠ encodeName "y" := fun same => by
  have names := encodeName_injective same
  simp at names

/-- **Negative**: a symbol that is no empty list is the data of no name. -/
theorem decodeName_symbol : decodeName (.sym "x") = none := rfl

/-- A name of several equal characters. -/
theorem encodeName_ofList_replicate (count : Nat) (character : Char) :
    encodeName (String.ofList (List.replicate count character)) =
      cells (List.replicate count (encodeCharacter character)) := by
  simp [encodeName, String.toList_ofList]

/-- An optional name. -/
def decodeOptionalName : Term → Option (Option String)
  | .sym "None" => some none
  | .expr [.sym "Some", name] => (decodeName name).map some
  | _ => none

@[simp] theorem decodeOptionalName_encodeOption (name : Option String) :
    decodeOptionalName (encodeOption encodeName name) = some name := by
  cases name <;> simp [encodeOption, decodeOptionalName]

/-- **Negative**: the empty list is no optional name. -/
theorem decodeOptionalName_nil : decodeOptionalName (.sym "Nil") = none := rfl

/-- The kind of a collection. -/
def encodeKind : CollType → Term
  | .vec => .sym "vec"
  | .hashBag => .sym "bag"
  | .hashSet => .sym "set"

/-- The kind of a symbol. -/
def decodeKind : Term → Option CollType
  | .sym "vec" => some .vec
  | .sym "bag" => some .hashBag
  | .sym "set" => some .hashSet
  | _ => none

@[simp] theorem decodeKind_encodeKind (kind : CollType) : decodeKind (encodeKind kind) = some kind := by
  cases kind <;> rfl

/-- **Negative**: the empty list is no kind. -/
theorem decodeKind_nil : decodeKind (.sym "Nil") = none := rfl

theorem mapM_decodeName (names : List String) :
    names.mapM (decodeName ∘ encodeName) = some names := by
  induction names with
  | nil => rfl
  | cons head tail ih => simp [List.mapM_cons, ih]

/-! ## Patterns -/

mutual
  /-- **A pattern, as a term of the engine.** -/
  def encodePattern : Pattern → Term
    | .bvar index => .expr [.sym "bvar", natural index]
    | .fvar name => .expr [.sym "fvar", encodeName name]
    | .apply label arguments => .expr [.sym "apply", encodeName label, encodePatterns arguments]
    | .lambda binder body =>
        .expr [.sym "lambda", encodeOption encodeName binder, encodePattern body]
    | .multiLambda arity binders body =>
        .expr [.sym "multi-lambda", natural arity, cells (binders.map encodeName),
          encodePattern body]
    | .subst body replacement => .expr [.sym "subst", encodePattern body, encodePattern replacement]
    | .collection kind elements rest =>
        .expr [.sym "collection", encodeKind kind, encodePatterns elements,
          encodeOption encodeName rest]

  /-- A list of patterns, as cells. -/
  def encodePatterns : List Pattern → Term
    | [] => .sym "Nil"
    | pattern :: patterns => .expr [.sym "Cons", encodePattern pattern, encodePatterns patterns]
end

theorem encodePatterns_eq_cells :
    ∀ patterns : List Pattern, encodePatterns patterns = cells (patterns.map encodePattern)
  | [] => rfl
  | pattern :: patterns => by
      rw [encodePatterns, List.map_cons, cells, encodePatterns_eq_cells patterns]

mutual
  /-- The pattern of a term. -/
  def decodePattern : Term → Option Pattern
    | .expr [.sym "bvar", index] => (natural? index).map .bvar
    | .expr [.sym "fvar", name] => (decodeName name).map .fvar
    | .expr [.sym "apply", label, arguments] =>
        (decodeName label).bind fun label =>
          (decodePatterns arguments).map fun arguments => .apply label arguments
    | .expr [.sym "lambda", binder, body] =>
        (decodeOptionalName binder).bind fun binder =>
          (decodePattern body).map fun body => .lambda binder body
    | .expr [.sym "multi-lambda", arity, binders, body] =>
        (natural? arity).bind fun arity =>
          (uncells binders).bind fun items =>
            (items.mapM decodeName).bind fun binders =>
              (decodePattern body).map fun body => .multiLambda arity binders body
    | .expr [.sym "subst", body, replacement] =>
        (decodePattern body).bind fun body =>
          (decodePattern replacement).map fun replacement => .subst body replacement
    | .expr [.sym "collection", kind, elements, rest] =>
        (decodeKind kind).bind fun kind =>
          (decodePatterns elements).bind fun elements =>
            (decodeOptionalName rest).map fun rest => .collection kind elements rest
    | _ => none

  /-- The patterns of a chain of cells. -/
  def decodePatterns : Term → Option (List Pattern)
    | .sym "Nil" => some []
    | .expr [.sym "Cons", head, tail] =>
        (decodePattern head).bind fun head => (decodePatterns tail).map fun tail => head :: tail
    | _ => none
end

mutual
  /-- **The reading of patterns has a left inverse.** -/
  theorem decodePattern_encodePattern :
      ∀ pattern : Pattern, decodePattern (encodePattern pattern) = some pattern
    | .bvar index => by simp [encodePattern, decodePattern]
    | .fvar name => by simp [encodePattern, decodePattern]
    | .apply label arguments => by
        simp [encodePattern, decodePattern, decodePatterns_encodePatterns arguments]
    | .lambda binder body => by
        simp [encodePattern, decodePattern, decodePattern_encodePattern body]
    | .multiLambda arity binders body => by
        simp [encodePattern, decodePattern, mapM_decodeName, decodePattern_encodePattern body]
    | .subst body replacement => by
        simp [encodePattern, decodePattern, decodePattern_encodePattern body,
          decodePattern_encodePattern replacement]
    | .collection kind elements rest => by
        simp [encodePattern, decodePattern, decodePatterns_encodePatterns elements]

  theorem decodePatterns_encodePatterns :
      ∀ patterns : List Pattern, decodePatterns (encodePatterns patterns) = some patterns
    | [] => by simp [encodePatterns, decodePatterns]
    | pattern :: patterns => by
        simp [encodePatterns, decodePatterns, decodePattern_encodePattern pattern,
          decodePatterns_encodePatterns patterns]
end

/-- **The reading of patterns is injective.** -/
theorem encodePattern_injective : Function.Injective encodePattern := fun first second same =>
  Option.some.inj
    (by rw [← decodePattern_encodePattern first, same, decodePattern_encodePattern second])

theorem encodePatterns_injective : Function.Injective encodePatterns := fun first second same =>
  Option.some.inj
    (by rw [← decodePatterns_encodePatterns first, same, decodePatterns_encodePatterns second])

/-- **Positive**: an application of a label to no argument. -/
theorem encodePattern_constant (label : String) :
    encodePattern (.apply label []) = .expr [.sym "apply", encodeName label, .sym "Nil"] := by
  simp [encodePattern, encodePatterns]

/-- **Negative**: a call of the engine is the term of no pattern. -/
theorem decodePattern_call (head : String) (argument : Term) (other : head ≠ "bvar")
    (another : head ≠ "fvar") : decodePattern (.expr [.sym head, argument]) = none := by
  simp [decodePattern, other, another]

/-- **Negative**: a call of two arguments whose head is no tag of cells is no
list of patterns. -/
theorem decodePatterns_call (head : String) (first second : Term) (other : head ≠ "Cons") :
    decodePatterns (.expr [.sym head, first, second]) = none := by
  simp [decodePatterns, other]

/-! ## Names are data for a program -/

/-- **The tags of cells are constructors** of a program and a host: no
equation defines them, and the host does not handle them. -/
structure KeepsCells (program : Program) (host : Host) : Prop where
  undefined : program.defines "Cons" = false
  unhandled : ∀ arguments, host.primitive "Cons" arguments = .unhandled

theorem cells_passive {program : Program} {host : Host} (keeps : KeepsCells program host) :
    ∀ {items : List Term}, (∀ item ∈ items, PassiveData program host item) →
      PassiveData program host (cells items)
  | [], _ => .sym _
  | head :: tail, passive =>
      .node (by simp [Special]) keeps.undefined (keeps.unhandled _) (by
        intro argument member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact passive _ (List.mem_cons_self ..)
        · exact cells_passive keeps fun item inTail => passive item (List.mem_cons_of_mem _ inTail))

/-- **The term of a name is data**: evaluation gives it back. -/
theorem encodeName_passive {program : Program} {host : Host} (keeps : KeepsCells program host)
    (name : String) : PassiveData program host (encodeName name) :=
  cells_passive keeps fun item member => by
    obtain ⟨character, -, rfl⟩ := List.mem_map.mp member
    exact natural_passive program host _

theorem encodeName_evaluates {program : Program} {host : Host} (keeps : KeepsCells program host)
    (name : String) (environment : Env) :
    Evaluates program host environment (encodeName name) (encodeName name) :=
  (encodeName_passive keeps name).evaluates environment

/-- **Positive**: the shared host keeps the cells of a program that does not
define `Cons`. -/
theorem keepsCells_dataEqualityHost {program : Program} (undefined : program.defines "Cons" = false) :
    KeepsCells program dataEqualityHost :=
  ⟨undefined, fun _ => rfl⟩

/-- **Negative**: a program with an equation for `Cons` does not keep them. -/
theorem not_keepsCells_of_defined (host : Host) :
    ¬ KeepsCells [⟨"cons", "Cons", [.var "head", .var "tail"], .var "tail"⟩] host :=
  fun keeps => by
    have defined := keeps.undefined
    revert defined
    decide

#print axioms uncells_cells
#print axioms decodeName_encodeName
#print axioms encodeName_injective
#print axioms decodePattern_encodePattern
#print axioms encodePattern_injective
#print axioms encodePatterns_injective
#print axioms encodeName_passive
#print axioms keepsCells_dataEqualityHost

end Mettapedia.Logic.HostingStyles.AuthoredEvaluators
