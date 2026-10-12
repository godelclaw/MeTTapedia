import Mettapedia.OSLF.NativeTypes.Structural.SpatialDeclarations
import Mettapedia.OSLF.Syntax.BindingSignature

open Mettapedia.OSLF.Framework

/-!
# Executable structural and propositional generation

The elaborator checks the selected connective fragment and the authored
constructor signatures. Successful output retains the resolved declaration
positions. Refusing a connective is an elaboration result, never a statement
that its meaning is false. Structural splitting quantifies over typed
constructor introductions modulo equations, including binding arguments.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Structural

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted

inductive PropositionalStrength where
  | finiteLimits
  | bounded
  | distributive
  | heyting
  deriving DecidableEq, Repr

inductive Connective where
  | top | bottom | conjunction | disjunction | implication | negation
  | structural | modal
  deriving DecidableEq, Repr

/-- The existing finite-limit controls, together with explicitly requested
stronger operations and the declared interpretation strength. -/
structure ConnectiveFragment where
  core : Mettapedia.OSLF.Binding.ConnectiveFragment
  strength : PropositionalStrength := .finiteLimits
  bottom : Bool := false
  disjunction : Bool := false
  implication : Bool := false
  negation : Bool := false
  deriving DecidableEq, Repr

def ConnectiveFragment.admits (fragment : ConnectiveFragment) : Connective → Bool
  | .top => fragment.core.top
  | .conjunction => fragment.core.conj
  | .structural => fragment.core.structural
  | .modal => fragment.core.modal
  | .bottom => fragment.bottom && fragment.strength != .finiteLimits
  | .disjunction => fragment.disjunction &&
      (fragment.strength == .distributive || fragment.strength == .heyting)
  | .implication => fragment.implication && fragment.strength == .heyting
  | .negation => fragment.negation && fragment.strength == .heyting

def finiteLimitFragment : ConnectiveFragment :=
  { core := Mettapedia.OSLF.Binding.fullConnectives }

def heytingFragment : ConnectiveFragment :=
  { core := Mettapedia.OSLF.Binding.fullConnectives, strength := .heyting,
    bottom := true, disjunction := true, implication := true, negation := true }

/-- Constructor identifiers and modal atom identifiers are positions in the
generated catalogues, not a second authored vocabulary. -/
inductive Formula where
  | top
  | bottom
  | atom (index : Nat)
  | conj (left right : Formula)
  | disj (left right : Formula)
  | imp (left right : Formula)
  | neg (inner : Formula)
  | root (index : Nat)
  | split (index : Nat) (left right : Formula)
  | spatial (index : Nat) (left right : Formula)
  deriving DecidableEq, Repr

def Formula.connective : Formula → Connective
  | .top => .top
  | .bottom => .bottom
  | .atom _ => .modal
  | .conj _ _ => .conjunction
  | .disj _ _ => .disjunction
  | .imp _ _ => .implication
  | .neg _ => .negation
  | .root _ => .structural
  | .split _ _ _ => .structural
  | .spatial _ _ _ => .structural

/-- Find the first unsupported operation before considering its truth. -/
def denyUnless (fragment : ConnectiveFragment) (connective : Connective)
    (inner : Option Connective) : Option Connective :=
  if fragment.admits connective then inner else some connective

def firstDenied (fragment : ConnectiveFragment) : Formula → Option Connective
  | .top => denyUnless fragment .top none
  | .bottom => denyUnless fragment .bottom none
  | .atom _ => denyUnless fragment .modal none
  | .conj left right => denyUnless fragment .conjunction
      ((firstDenied fragment left).or (firstDenied fragment right))
  | .disj left right => denyUnless fragment .disjunction
      ((firstDenied fragment left).or (firstDenied fragment right))
  | .imp left right => denyUnless fragment .implication
      ((firstDenied fragment left).or (firstDenied fragment right))
  | .neg inner => denyUnless fragment .negation (firstDenied fragment inner)
  | .root _ => denyUnless fragment .structural none
  | .split _ left right => denyUnless fragment .structural
      ((firstDenied fragment left).or (firstDenied fragment right))
  | .spatial _ left right => denyUnless fragment .structural
      ((firstDenied fragment left).or (firstDenied fragment right))

/-- Formation is specified independently as inference rules. Constructor
arity and argument carriers are read from the original declaration. -/
inductive Formed (language : LanguageDef) (atomSort : Nat → Option TypeExpr)
    (fragment : ConnectiveFragment) : TypeExpr → Formula → Prop where
  | top (expected : TypeExpr) (enabled : fragment.admits .top = true) :
      Formed language atomSort fragment expected .top
  | bottom (expected : TypeExpr) (enabled : fragment.admits .bottom = true) :
      Formed language atomSort fragment expected .bottom
  | atom {expected : TypeExpr} (index : Nat) (enabled : fragment.admits .modal = true)
      (sort : atomSort index = some expected) :
      Formed language atomSort fragment expected (.atom index)
  | conj {expected : TypeExpr} {left right : Formula}
      (enabled : fragment.admits .conjunction = true)
      (first : Formed language atomSort fragment expected left)
      (second : Formed language atomSort fragment expected right) :
      Formed language atomSort fragment expected (.conj left right)
  | disj {expected : TypeExpr} {left right : Formula}
      (enabled : fragment.admits .disjunction = true)
      (first : Formed language atomSort fragment expected left)
      (second : Formed language atomSort fragment expected right) :
      Formed language atomSort fragment expected (.disj left right)
  | imp {expected : TypeExpr} {left right : Formula}
      (enabled : fragment.admits .implication = true)
      (first : Formed language atomSort fragment expected left)
      (second : Formed language atomSort fragment expected right) :
      Formed language atomSort fragment expected (.imp left right)
  | neg {expected : TypeExpr} {inner : Formula}
      (enabled : fragment.admits .negation = true)
      (formed : Formed language atomSort fragment expected inner) :
      Formed language atomSort fragment expected (.neg inner)
  | root {expected : TypeExpr} (index : Nat) (declaration : GrammarRule)
      (enabled : fragment.admits .structural = true)
      (lookup : language.terms[index]? = some declaration)
      (sort : expected = .base declaration.category) :
      Formed language atomSort fragment expected (.root index)
  | split {expected firstSort secondSort : TypeExpr} {left right : Formula}
      (index : Nat) (declaration : GrammarRule) (firstParam secondParam : TermParam)
      (enabled : fragment.admits .structural = true)
      (lookup : language.terms[index]? = some declaration)
      (sort : expected = .base declaration.category)
      (arity : declaration.params = [firstParam, secondParam])
      (firstType : parameterType? firstParam = some firstSort)
      (secondType : parameterType? secondParam = some secondSort)
      (first : Formed language atomSort fragment firstSort left)
      (second : Formed language atomSort fragment secondSort right) :
      Formed language atomSort fragment expected (.split index left right)
  | spatial {expected : TypeExpr} {left right : Formula}
      (index : Nat) (declaration : GrammarRule) (shape : SpatialShape)
      (enabled : fragment.admits .structural = true)
      (lookup : language.terms[index]? = some declaration)
      (sort : expected = .base declaration.category)
      (spatial : spatialShape? language declaration = some shape)
      (first : Formed language atomSort fragment expected left)
      (second : Formed language atomSort fragment expected right) :
      Formed language atomSort fragment expected (.spatial index left right)

/-- Actual recursive formation checking. There is no supplied admissibility
predicate or constructor table. -/
def checkFormation (language : LanguageDef) (atomSort : Nat → Option TypeExpr)
    (fragment : ConnectiveFragment) (expected : TypeExpr) : Formula → Bool
  | .top => fragment.admits .top
  | .bottom => fragment.admits .bottom
  | .atom index => fragment.admits .modal && atomSort index == some expected
  | .conj left right => fragment.admits .conjunction &&
      checkFormation language atomSort fragment expected left &&
      checkFormation language atomSort fragment expected right
  | .disj left right => fragment.admits .disjunction &&
      checkFormation language atomSort fragment expected left &&
      checkFormation language atomSort fragment expected right
  | .imp left right => fragment.admits .implication &&
      checkFormation language atomSort fragment expected left &&
      checkFormation language atomSort fragment expected right
  | .neg inner => fragment.admits .negation &&
      checkFormation language atomSort fragment expected inner
  | .root index => fragment.admits .structural &&
      match language.terms[index]? with
      | none => false
      | some declaration => expected == .base declaration.category
  | .split index left right => fragment.admits .structural &&
      match language.terms[index]? with
      | none => false
      | some declaration => expected == .base declaration.category &&
          match declaration.params with
          | [first, second] =>
              match parameterType? first, parameterType? second with
              | some firstSort, some secondSort =>
                  checkFormation language atomSort fragment firstSort left &&
                  checkFormation language atomSort fragment secondSort right
              | _, _ => false
          | _ => false
  | .spatial index left right => fragment.admits .structural &&
      match language.terms[index]? with
      | none => false
      | some declaration => expected == .base declaration.category &&
          (spatialShape? language declaration).isSome &&
          checkFormation language atomSort fragment expected left &&
          checkFormation language atomSort fragment expected right

theorem checkFormation_complete {language : LanguageDef} {atomSort : Nat → Option TypeExpr}
    {fragment : ConnectiveFragment} {expected : TypeExpr} {formula : Formula}
    (formed : Formed language atomSort fragment expected formula) :
    checkFormation language atomSort fragment expected formula = true := by
  induction formed with
  | top expected enabled => exact enabled
  | bottom expected enabled => exact enabled
  | atom index enabled sort => simp [checkFormation, enabled, sort]
  | conj enabled first second ihFirst ihSecond =>
      simp [checkFormation, enabled, ihFirst, ihSecond]
  | disj enabled first second ihFirst ihSecond =>
      simp [checkFormation, enabled, ihFirst, ihSecond]
  | imp enabled first second ihFirst ihSecond =>
      simp [checkFormation, enabled, ihFirst, ihSecond]
  | neg enabled formed ih => simp [checkFormation, enabled, ih]
  | root index declaration enabled lookup sort => simp [checkFormation, enabled, lookup, sort]
  | split index declaration firstParam secondParam enabled lookup sort arity firstType secondType
      first second ihFirst ihSecond =>
      simp [checkFormation, enabled, lookup, sort, arity, firstType, secondType, ihFirst, ihSecond]
  | spatial index declaration shape enabled lookup sort spatial first second ihFirst ihSecond =>
      simp_all [checkFormation]

theorem checkFormation_sound (language : LanguageDef) (atomSort : Nat → Option TypeExpr)
    (fragment : ConnectiveFragment) (formula : Formula) :
    ∀ expected, checkFormation language atomSort fragment expected formula = true →
      Formed language atomSort fragment expected formula := by
  induction formula with
  | top => intro expected checked; exact .top expected checked
  | bottom => intro expected checked; exact .bottom expected checked
  | atom index =>
      intro expected checked
      simp only [checkFormation, Bool.and_eq_true, beq_iff_eq] at checked
      exact .atom index checked.1 checked.2
  | conj left right ihLeft ihRight =>
      intro expected checked
      simp only [checkFormation, Bool.and_eq_true] at checked
      exact .conj checked.1.1 (ihLeft expected checked.1.2) (ihRight expected checked.2)
  | disj left right ihLeft ihRight =>
      intro expected checked
      simp only [checkFormation, Bool.and_eq_true] at checked
      exact .disj checked.1.1 (ihLeft expected checked.1.2) (ihRight expected checked.2)
  | imp left right ihLeft ihRight =>
      intro expected checked
      simp only [checkFormation, Bool.and_eq_true] at checked
      exact .imp checked.1.1 (ihLeft expected checked.1.2) (ihRight expected checked.2)
  | neg inner ih =>
      intro expected checked
      simp only [checkFormation, Bool.and_eq_true] at checked
      exact .neg checked.1 (ih expected checked.2)
  | root index =>
      intro expected checked
      simp only [checkFormation, Bool.and_eq_true] at checked
      cases lookup : language.terms[index]? with
      | none => simp [lookup] at checked
      | some declaration =>
          exact .root index declaration checked.1 lookup
            (by simpa [lookup] using checked.2)
  | split index left right ihLeft ihRight =>
      intro expected checked
      simp only [checkFormation, Bool.and_eq_true] at checked
      cases lookup : language.terms[index]? with
      | none => simp [lookup] at checked
      | some declaration =>
          simp only [lookup, Bool.and_eq_true, beq_iff_eq] at checked
          rcases checked with ⟨enabled, sort, checked⟩
          cases params : declaration.params with
          | nil => simp [params] at checked
          | cons first rest =>
              cases rest with
              | nil => simp [params] at checked
              | cons second rest =>
                  cases rest with
                  | cons third rest => simp [params] at checked
                  | nil =>
                      cases firstType : parameterType? first with
                      | none => simp [params, firstType] at checked
                      | some firstSort =>
                          cases secondType : parameterType? second with
                          | none => simp [params, firstType, secondType] at checked
                          | some secondSort =>
                              simp only [params, firstType, secondType, Bool.and_eq_true] at checked
                              exact .split index declaration first second enabled lookup sort params
                                firstType secondType (ihLeft firstSort checked.1)
                                (ihRight secondSort checked.2)
  | spatial index left right ihLeft ihRight =>
      intro expected checked
      simp only [checkFormation, Bool.and_eq_true] at checked
      cases lookup : language.terms[index]? with
      | none => simp [lookup] at checked
      | some declaration =>
          simp only [lookup, Bool.and_eq_true, beq_iff_eq] at checked
          rcases checked with ⟨enabled, ⟨⟨⟨sort, shaped⟩, first⟩, second⟩⟩
          cases spatial : spatialShape? language declaration with
          | none => simp [spatial] at shaped
          | some shape =>
              exact .spatial index declaration shape enabled lookup sort spatial
                (ihLeft expected first) (ihRight expected second)

theorem checkFormation_iff (language : LanguageDef) (atomSort : Nat → Option TypeExpr)
    (fragment : ConnectiveFragment) (expected : TypeExpr) (formula : Formula) :
    checkFormation language atomSort fragment expected formula = true ↔
      Formed language atomSort fragment expected formula :=
  ⟨checkFormation_sound language atomSort fragment formula expected, checkFormation_complete⟩

inductive Refusal where
  | unsupportedConnective (connective : Connective)
  | malformedJudgment (expected : TypeExpr)
  deriving DecidableEq, Repr

/-- A successfully elaborated judgment retains the constructor catalogue
computed from its language, in addition to the admitted query syntax. -/
structure Judgment where
  expected : TypeExpr
  formula : Formula
  structural : List Former
  deriving DecidableEq, Repr

def elaborate (language : LanguageDef) (atomSort : Nat → Option TypeExpr)
    (fragment : ConnectiveFragment) (expected : TypeExpr) (formula : Formula) :
    Except Refusal Judgment :=
  if checkFormation language atomSort fragment expected formula then
    .ok ⟨expected, formula, structuralFormers language⟩
  else
    match firstDenied fragment formula with
    | some denied => .error (.unsupportedConnective denied)
    | none => .error (.malformedJudgment expected)

theorem elaborate_success_iff (language : LanguageDef) (atomSort : Nat → Option TypeExpr)
    (fragment : ConnectiveFragment) (expected : TypeExpr) (formula : Formula) :
    (∃ judgment, elaborate language atomSort fragment expected formula = .ok judgment) ↔
      Formed language atomSort fragment expected formula := by
  rw [← checkFormation_iff]
  unfold elaborate
  cases checkFormation language atomSort fragment expected formula <;> simp
  case false => cases firstDenied fragment formula <;> simp

theorem elaborate_output {language : LanguageDef} {atomSort : Nat → Option TypeExpr}
    {fragment : ConnectiveFragment} {expected : TypeExpr} {formula : Formula} {judgment : Judgment}
    (success : elaborate language atomSort fragment expected formula = .ok judgment) :
    judgment = ⟨expected, formula, structuralFormers language⟩ ∧
      Formed language atomSort fragment expected formula := by
  have formed := (elaborate_success_iff language atomSort fragment expected formula).mp
    ⟨judgment, success⟩
  have checked := checkFormation_complete formed
  simp only [elaborate, checked, ↓reduceIte, Except.ok.injEq] at success
  exact ⟨success.symm, formed⟩

/-- The generator exposes every authored structural former through the same
elaborator. There is no separate per-language formation inventory. -/
theorem every_structural_former_elaborates {language : LanguageDef}
    {atomSort : Nat → Option TypeExpr} {fragment : ConnectiveFragment}
    (enabled : fragment.admits .structural = true) {former : Former}
    (member : former ∈ structuralFormers language) :
    ∃ judgment, elaborate language atomSort fragment (.base former.declaration.category)
      (.root former.index) = .ok judgment := by
  apply (elaborate_success_iff _ _ _ _ _).mpr
  exact .root former.index former.declaration enabled
    ((mem_structuralFormers_iff language former).mp member) rfl

theorem firstDenied_none_of_formed {language : LanguageDef} {atomSort : Nat → Option TypeExpr}
    {fragment : ConnectiveFragment} {expected : TypeExpr} {formula : Formula}
    (formed : Formed language atomSort fragment expected formula) :
    firstDenied fragment formula = none := by
  induction formed <;> simp_all [firstDenied, denyUnless]

/-- Unsupported syntax is refused even if its intended interpretation would
be true. Elaboration is independent of the observation's truth value. -/
theorem unsupported_connective_refused {language : LanguageDef}
    {atomSort : Nat → Option TypeExpr} {fragment : ConnectiveFragment}
    {expected : TypeExpr} {formula : Formula} {connective : Connective}
    (denied : firstDenied fragment formula = some connective) :
    elaborate language atomSort fragment expected formula =
      .error (.unsupportedConnective connective) := by
  have notChecked : checkFormation language atomSort fragment expected formula = false := by
    cases checked : checkFormation language atomSort fragment expected formula with
    | false => rfl
    | true =>
        have none := firstDenied_none_of_formed
          (checkFormation_sound language atomSort fragment formula expected checked)
        rw [denied] at none
        cases none
  simp [elaborate, notChecked, denied]

/-- Widening permitted operations never invalidates a previously formed
judgment. The operational language and its equations are fixed here. -/
theorem Formed.mono {language : LanguageDef} {atomSort : Nat → Option TypeExpr}
    {smaller larger : ConnectiveFragment}
    (inclusion : ∀ connective, smaller.admits connective = true →
      larger.admits connective = true)
    {expected : TypeExpr} {formula : Formula}
    (formed : Formed language atomSort smaller expected formula) :
    Formed language atomSort larger expected formula := by
  induction formed with
  | top expected enabled => exact .top expected (inclusion _ enabled)
  | bottom expected enabled => exact .bottom expected (inclusion _ enabled)
  | atom index enabled sort => exact .atom index (inclusion _ enabled) sort
  | conj enabled first second ihFirst ihSecond => exact .conj (inclusion _ enabled) ihFirst ihSecond
  | disj enabled first second ihFirst ihSecond => exact .disj (inclusion _ enabled) ihFirst ihSecond
  | imp enabled first second ihFirst ihSecond => exact .imp (inclusion _ enabled) ihFirst ihSecond
  | neg enabled formed ih => exact .neg (inclusion _ enabled) ih
  | root index declaration enabled lookup sort =>
      exact .root index declaration (inclusion _ enabled) lookup sort
  | split index declaration firstParam secondParam enabled lookup sort arity firstType secondType
      first second ihFirst ihSecond =>
      exact .split index declaration firstParam secondParam (inclusion _ enabled) lookup sort arity
        firstType secondType ihFirst ihSecond
  | spatial index declaration shape enabled lookup sort spatial first second ihFirst ihSecond =>
      exact .spatial index declaration shape (inclusion _ enabled) lookup sort spatial ihFirst ihSecond

end Mettapedia.OSLF.NativeTypes.Structural
