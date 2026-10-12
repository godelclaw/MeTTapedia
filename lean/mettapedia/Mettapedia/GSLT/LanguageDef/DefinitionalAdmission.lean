import Mettapedia.GSLT.LanguageDef.DefinitionalTyping
import Mettapedia.GSLT.LanguageDef.SortedFirstOrderAdmission

/-!
# Admitting the equations of a language as definitions

The definitions of a language are read off its authored equations: an
equation with no premises whose left side is a constructor applied to
metavariables states one definition. The check decides that every equation
has that shape, that the rows are well formed and acyclic in authored order,
that each defined constructor has exactly one declaration, with ordinary
parameters of declared sorts, at which the body is typed, and that the
language has no collection laws.

The check is exact. A language passes exactly when it is a definitional
language, and its rows are then the ones read off. An equation of another
shape, such as commutativity, fails the check; it remains an equation of the
language, with the equation theory it generates.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DefinitionalEquations

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.SortedFirstOrderRules

/-! ## Reading the rows -/

/-- The names of a list of metavariables, when every entry is one. -/
def metavariables? : List Pattern → Option (List String)
  | [] => some []
  | .fvar name :: patterns => (metavariables? patterns).map (name :: ·)
  | _ :: _ => none

theorem metavariables?_sound :
    ∀ {patterns : List Pattern} {names : List String},
      metavariables? patterns = some names → patterns = names.map Pattern.fvar
  | [], names, found => by
      simp only [metavariables?, Option.some.injEq] at found
      subst found
      rfl
  | .fvar name :: patterns, names, found => by
      cases rest : metavariables? patterns with
      | none => simp [metavariables?, rest] at found
      | some tail =>
        have same : name :: tail = names := by simpa [metavariables?, rest] using found
        subst same
        rw [List.map_cons, metavariables?_sound rest]
  | .bvar _ :: _, _, found => by simp [metavariables?] at found
  | .apply _ _ :: _, _, found => by simp [metavariables?] at found
  | .lambda _ _ :: _, _, found => by simp [metavariables?] at found
  | .multiLambda _ _ _ :: _, _, found => by simp [metavariables?] at found
  | .subst _ _ :: _, _, found => by simp [metavariables?] at found
  | .collection _ _ _ :: _, _, found => by simp [metavariables?] at found

theorem metavariables?_fvars :
    ∀ names : List String, metavariables? (names.map Pattern.fvar) = some names
  | [] => rfl
  | name :: names => by simp [metavariables?, metavariables?_fvars names]

/-- The definition an authored equation states, when it has that shape. -/
def rowOf? (equation : Equation) : Option Row :=
  match equation.premises, equation.left with
  | [], .apply head arguments =>
      (metavariables? arguments).map (fun formals => ⟨head, formals, equation.right⟩)
  | _, _ => none

theorem rowOf?_sound {equation : Equation} {row : Row} (found : rowOf? equation = some row) :
    Defines equation row := by
  unfold rowOf? at found
  split at found
  · rename_i head arguments noPremises shape
    cases names : metavariables? arguments with
    | none => simp [names] at found
    | some formals =>
      have same : (⟨head, formals, equation.right⟩ : Row) = row := by
        simpa [names] using found
      subst same
      exact ⟨noPremises, by rw [shape, metavariables?_sound names]; rfl, rfl⟩
  · cases found

theorem rowOf?_complete {equation : Equation} {row : Row} (defines : Defines equation row) :
    rowOf? equation = some row := by
  simp only [rowOf?, defines.noPremises, defines.left, Row.left, metavariables?_fvars,
    Option.map_some, defines.right]

theorem rowOf?_eq_some_iff {equation : Equation} {row : Row} :
    rowOf? equation = some row ↔ Defines equation row :=
  ⟨rowOf?_sound, rowOf?_complete⟩

/-- The definitions of an equation list, in authored order. -/
def rows? : List Equation → Option (List Row)
  | [] => some []
  | equation :: equations => do
      let row ← rowOf? equation
      let rest ← rows? equations
      some (row :: rest)

theorem rows?_sound :
    ∀ {equations : List Equation} {rows : List Row}, rows? equations = some rows →
      List.Forall₂ Defines equations rows
  | [], rows, found => by
      simp only [rows?, Option.some.injEq] at found
      subst found
      exact .nil
  | equation :: equations, rows, found => by
      cases first : rowOf? equation with
      | none => simp [rows?, first] at found
      | some row =>
        cases rest : rows? equations with
        | none => simp [rows?, first, rest] at found
        | some tail =>
          have same : row :: tail = rows := by simpa [rows?, first, rest] using found
          subst same
          exact .cons (rowOf?_sound first) (rows?_sound rest)

theorem rows?_complete {equations : List Equation} {rows : List Row}
    (pointwise : List.Forall₂ Defines equations rows) : rows? equations = some rows := by
  induction pointwise with
  | nil => rfl
  | cons defines _ inductionHypothesis =>
    simp [rows?, rowOf?_complete defines, inductionHypothesis]

/-- The rows read off an equation list are the ones its equations state, one
each and in order. -/
theorem rows?_eq_some_iff {equations : List Equation} {rows : List Row} :
    rows? equations = some rows ↔ List.Forall₂ Defines equations rows :=
  ⟨rows?_sound, rows?_complete⟩

/-! ## Acyclic order -/

/-- Distinct formals and a first-order body over them. -/
def Row.check (row : Row) : Bool :=
  decide row.formals.Nodup && checkSchema row.formals row.body

theorem Row.check_iff (row : Row) : row.check = true ↔ row.WellFormed := by
  simp only [Row.check, Bool.and_eq_true, decide_eq_true_iff, checkSchema_iff]
  exact ⟨fun ⟨distinct, schema⟩ => ⟨distinct, schema⟩, fun formed => ⟨formed.distinct, formed.schema⟩⟩

/-- Well formed rows, distinct heads, and no body mentioning its own head or
a later one. -/
def checkAcyclic (rows : List Row) : Bool :=
  rows.all Row.check &&
    decide (rows.Pairwise (fun earlier later => earlier.head ≠ later.head)) &&
    rows.all (fun row => checkAvoids row.head row.body) &&
    decide (rows.Pairwise (fun earlier later => checkAvoids later.head earlier.body = true))

theorem checkAcyclic_iff (rows : List Row) : checkAcyclic rows = true ↔ Acyclic rows := by
  simp only [checkAcyclic, Bool.and_eq_true, List.all_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨⟨⟨formed, heads⟩, own⟩, later⟩
    exact ⟨fun row member => (Row.check_iff row).mp (formed row member), heads,
      fun row member => (checkAvoids_iff _ _).mp (own row member),
      later.imp (fun avoided => (checkAvoids_iff _ _).mp avoided)⟩
  · intro acyclic
    exact ⟨⟨⟨fun row member => (Row.check_iff row).mpr (acyclic.wellFormed row member),
      acyclic.distinctHeads⟩,
      fun row member => (checkAvoids_iff _ _).mpr (acyclic.ownHead row member)⟩,
      acyclic.laterHeads.imp (fun avoided => (checkAvoids_iff _ _).mpr avoided)⟩

/-! ## Typed rows -/

/-- The types of a parameter list, when every parameter is an ordinary term
position. -/
def simpleTypes? : List TermParam → Option (List TypeExpr)
  | [] => some []
  | .simple _ type :: parameters => (simpleTypes? parameters).map (type :: ·)
  | _ :: _ => none

theorem simpleTypes?_sound :
    ∀ {parameters : List TermParam} {types : List TypeExpr},
      simpleTypes? parameters = some types → SimpleParameters parameters types
  | [], types, found => by
      simp only [simpleTypes?, Option.some.injEq] at found
      subst found
      exact .nil
  | .simple name type :: parameters, types, found => by
      cases rest : simpleTypes? parameters with
      | none => simp [simpleTypes?, rest] at found
      | some tail =>
        have same : type :: tail = types := by simpa [simpleTypes?, rest] using found
        subst same
        exact .cons ⟨name, rfl⟩ (simpleTypes?_sound rest)
  | .abstractionNamed _ _ _ :: _, _, found => by simp [simpleTypes?] at found
  | .multiAbstractionNamed _ _ _ :: _, _, found => by simp [simpleTypes?] at found

theorem simpleTypes?_complete {parameters : List TermParam} {types : List TypeExpr}
    (simple : SimpleParameters parameters types) : simpleTypes? parameters = some types := by
  induction simple with
  | nil => rfl
  | cons shape _ inductionHypothesis =>
    obtain ⟨name, rfl⟩ := shape
    simp [simpleTypes?, inductionHypothesis]

/-- One declaration carries the head, its parameters are the formals with
declared sorts, and the body is typed at it. -/
def Row.checkTyped (language : LanguageDef) (row : Row) : Bool :=
  match language.terms.filter (fun rule => rule.label == row.head) with
  | [declaration] =>
      match simpleTypes? declaration.params with
      | some types =>
          decide (types.length = row.formals.length) && types.all (checkBaseType language) &&
            checkHasType language FreeTypeContext.empty types (numbered row.formals row.body)
              (.base declaration.category)
      | none => false
  | _ => false

theorem Row.checkTyped_iff {language : LanguageDef} {row : Row} (formed : row.WellFormed) :
    row.checkTyped language = true ↔ row.Typed language := by
  constructor
  · intro checked
    unfold Row.checkTyped at checked
    split at checked
    · rename_i declaration only
      split at checked
      · rename_i types simple
        simp only [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true,
          checkBaseType_iff] at checked
        obtain ⟨⟨arity, sorts⟩, bodyChecked⟩ := checked
        exact ⟨declaration, types, only, simpleTypes?_sound simple, arity, sorts,
          checkHasType_sound bodyChecked⟩
      · cases checked
    · cases checked
  · rintro ⟨declaration, types, typedAt⟩
    have fragment : isMatchCorrectAux (numbered row.formals row.body) = true :=
      formed.schema.numbered_firstOrder formed.distinct
    simp only [Row.checkTyped, typedAt.declared, simpleTypes?_complete typedAt.simple,
      Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true, checkBaseType_iff]
    exact ⟨⟨typedAt.arity, typedAt.sorts⟩,
      checkHasType_complete_of_object typedAt.body (firstOrder_object fragment)⟩

/-! ## The language -/

/-- The definitions a language states, or none when an equation has another
shape. -/
def definitions (language : LanguageDef) : List Row :=
  (rows? language.equations).getD []

/-- The equations of the language are typed definitions in acyclic order,
and the language has no collection laws. -/
def checkDefinitional (language : LanguageDef) : Bool :=
  match rows? language.equations with
  | some rows =>
      checkAcyclic rows && rows.all (Row.checkTyped language) &&
        !language.usesCollection .hashBag && !language.usesCollection .hashSet &&
        !language.hasAlgebraDeclarations
  | none => false

/-- A language that passes the check is a definitional language. -/
theorem checkDefinitional_sound {language : LanguageDef}
    (checked : checkDefinitional language = true) :
    DefinitionalLanguage language (definitions language) := by
  unfold checkDefinitional at checked
  split at checked
  · rename_i rows found
    simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true'] at checked
    obtain ⟨⟨⟨⟨acyclicChecked, typed⟩, noBags⟩, noSets⟩, noAlgebra⟩ := checked
    have same : definitions language = rows := by simp [definitions, found]
    have acyclic := (checkAcyclic_iff rows).mp acyclicChecked
    rw [same]
    exact
      { authored := rows?_sound found
        acyclic := acyclic
        typed := fun row member =>
          (Row.checkTyped_iff (acyclic.wellFormed row member)).mp (typed row member)
        noBags := noBags
        noSets := noSets
        noAlgebra := noAlgebra }
  · cases checked

/-- A definitional language has one list of definitions: the rows read off
its equations. -/
theorem DefinitionalLanguage.rows_eq {language : LanguageDef} {rows : List Row}
    (definitional : DefinitionalLanguage language rows) : rows = definitions language := by
  simp [definitions, rows?_complete definitional.authored]

/-- **The check is exact.** A language passes exactly when it is a
definitional language. -/
theorem checkDefinitional_iff (language : LanguageDef) :
    checkDefinitional language = true ↔ ∃ rows, DefinitionalLanguage language rows := by
  constructor
  · intro checked
    exact ⟨definitions language, checkDefinitional_sound checked⟩
  · rintro ⟨rows, definitional⟩
    simp only [checkDefinitional, rows?_complete definitional.authored, Bool.and_eq_true,
      List.all_eq_true, Bool.not_eq_true']
    exact ⟨⟨⟨⟨(checkAcyclic_iff rows).mpr definitional.acyclic,
      fun row member =>
        (Row.checkTyped_iff (definitional.acyclic.wellFormed row member)).mpr
          (definitional.typed row member)⟩,
      definitional.noBags⟩, definitional.noSets⟩, definitional.noAlgebra⟩

/-- The check decides that the rows read off the language make it
definitional. -/
theorem checkDefinitional_iff_definitions (language : LanguageDef) :
    checkDefinitional language = true ↔ DefinitionalLanguage language (definitions language) :=
  ⟨checkDefinitional_sound,
    fun definitional => (checkDefinitional_iff language).mpr ⟨_, definitional⟩⟩

end Mettapedia.GSLT.LanguageDef.DefinitionalEquations
