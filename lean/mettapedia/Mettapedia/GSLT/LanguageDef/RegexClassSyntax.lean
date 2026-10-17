import Mettapedia.GSLT.LanguageDef.RegexClassMaterialization

/-!
# Selected class syntax and its symbolic interpretation

Adjacency denotes union. The three doubled operators share a left-associative
tier below adjacency; brackets give explicit grouping. Case closure belongs
to positive atomic classes before Boolean operations and negation. The
independent syntax judgment retains that order rather than folding a final
subtraction or complement after the fact.

The atomic interpreter supplies scalar ranges, escapes and versioned Unicode
properties. This module handles the structural class language and proves
two-sided CST projection and set interpretation. It does not choose a tree
from a packed forest or verify a native C implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexClassSyntax

open RegexClassInterpretation (Expr Provider Scalar)
open RegexClassMaterialization (Catalog Ranges lower provider)
open RegexSourceProjection (cst fields? InRanges)
open CettaWire (Term)

inductive Binary where
  | union | intersection | difference | symmetricDifference
  deriving DecidableEq, Repr

inductive Syntax where
  | atomic (expression : Expr)
  | complement (body : Syntax)
  | binary (operation : Binary) (left right : Syntax)
  deriving DecidableEq, Repr

/-- Set meaning does not invoke the symbolic lowering or interval compiler. -/
def meaning (interpretation : Provider) : Syntax → Set Nat
  | .atomic expression => RegexClassInterpretation.meaning interpretation expression
  | .complement body => Scalar \ meaning interpretation body
  | .binary .union left right => meaning interpretation left ∪ meaning interpretation right
  | .binary .intersection left right => meaning interpretation left ∩ meaning interpretation right
  | .binary .difference left right => meaning interpretation left \ meaning interpretation right
  | .binary .symmetricDifference left right =>
      (meaning interpretation left \ meaning interpretation right) ∪
      (meaning interpretation right \ meaning interpretation left)

def elaborate : Syntax → Expr
  | .atomic expression => expression
  | .complement body => .complement (elaborate body)
  | .binary .union left right => .union (elaborate left) (elaborate right)
  | .binary .intersection left right => .intersection (elaborate left) (elaborate right)
  | .binary .difference left right => .difference (elaborate left) (elaborate right)
  | .binary .symmetricDifference left right =>
      .union (.difference (elaborate left) (elaborate right))
        (.difference (elaborate right) (elaborate left))

theorem elaborate_exact (interpretation : Provider) (parsed : Syntax) :
    RegexClassInterpretation.meaning interpretation (elaborate parsed) = meaning interpretation parsed := by
  induction parsed with
  | atomic expression => rfl
  | complement body ih => simp [elaborate, RegexClassInterpretation.meaning, meaning, ih]
  | binary operation left right ihLeft ihRight =>
      cases operation <;> simp [elaborate, RegexClassInterpretation.meaning, meaning, ihLeft, ihRight]

theorem intervals_exact (catalog : Catalog) (parsed : Syntax) (ranges : Ranges)
    (compiled : lower catalog (elaborate parsed) = some ranges) (scalar : Nat) :
    InRanges scalar ranges ↔ scalar ∈ meaning (provider catalog) parsed := by
  rw [← elaborate_exact]
  exact RegexClassMaterialization.lower_exact catalog (elaborate parsed) ranges compiled scalar

inductive Shell where
  | atomic
  | identity (body : Term)
  | complement (body : Term)
  | binary (operation : Binary) (left right : Term)
  | prefix (scalar : Nat) (body : Term)
  deriving DecidableEq, Repr

/-- Structural recognition only. Numeric and property interpretation remain
in the separately supplied atomic interpretation. -/
def shell? (tree : Term) : Option Shell := do
  let (name, children) ← fields? tree
  match name, children with
  | "re-src:class", [body] | "re-src:class-union", [body]
  | "re-src:first-nested", [body] | "re-src:class-nested", [body] => some (.identity body)
  | "re-src:class-not", [body] | "re-src:first-nested-not", [body]
  | "re-src:class-nested-not", [body] => some (.complement body)
  | "re-src:class-first", [left, right] | "re-src:class-tail", [left, right]
  | "re-src:class-amp-item", [left, right] | "re-src:class-tilde-item", [left, right] =>
      some (.binary .union left right)
  | "re-src:class-intersection", [left, right] => some (.binary .intersection left right)
  | "re-src:class-difference", [left, right] => some (.binary .difference left right)
  | "re-src:class-symmetric-difference", [left, right] => some (.binary .symmetricDifference left right)
  | "re-src:class-initial-dash", [body] => some (.prefix 45 body)
  | "re-src:class-first-amp", [body] | "re-src:class-tail-amp", [body]
  | "re-src:class-tilde-amp", [body] => some (.prefix 38 body)
  | "re-src:class-first-tilde", [body] | "re-src:class-tail-tilde", [body]
  | "re-src:class-amp-tilde", [body] => some (.prefix 126 body)
  | _, _ => some .atomic

def close (insensitive : Bool) (expression : Expr) : Expr :=
  if insensitive then .fold expression else expression

def prefixSyntax (insensitive : Bool) (scalar : Nat) (body : Syntax) : Syntax :=
  .binary .union (.atomic (close insensitive (.range scalar scalar))) body

/-- Local semantic rules are independent of the fuelled projection. -/
inductive Projects (atomic : Term → Option Expr) (insensitive : Bool) : Term → Syntax → Prop
  | atomic {tree expression} (shape : shell? tree = some .atomic)
      (value : atomic tree = some expression) : Projects atomic insensitive tree (.atomic expression)
  | identity {tree body result} (shape : shell? tree = some (.identity body))
      (inside : Projects atomic insensitive body result) : Projects atomic insensitive tree result
  | complement {tree body result} (shape : shell? tree = some (.complement body))
      (inside : Projects atomic insensitive body result) : Projects atomic insensitive tree (.complement result)
  | binary {tree operation left right a b} (shape : shell? tree = some (.binary operation left right))
      (before : Projects atomic insensitive left a) (after : Projects atomic insensitive right b) :
      Projects atomic insensitive tree (.binary operation a b)
  | prefix {tree scalar body result} (shape : shell? tree = some (.prefix scalar body))
      (inside : Projects atomic insensitive body result) :
      Projects atomic insensitive tree (prefixSyntax insensitive scalar result)

def project (atomic : Term → Option Expr) (insensitive : Bool) : Nat → Term → Option Syntax
  | 0, _ => none
  | fuel + 1, tree => do
      match ← shell? tree with
      | .atomic => Syntax.atomic <$> atomic tree
      | .identity body => project atomic insensitive fuel body
      | .complement body => Syntax.complement <$> project atomic insensitive fuel body
      | .binary operation left right => do
          some (.binary operation (← project atomic insensitive fuel left) (← project atomic insensitive fuel right))
      | .prefix scalar body => prefixSyntax insensitive scalar <$> project atomic insensitive fuel body

theorem project_sound (atomic : Term → Option Expr) (insensitive : Bool) (fuel : Nat)
    (tree : Term) (parsed : Syntax) (computed : project atomic insensitive fuel tree = some parsed) :
    Projects atomic insensitive tree parsed := by
  induction fuel generalizing tree parsed with
  | zero => simp [project] at computed
  | succ fuel ih =>
      cases shape : shell? tree with
      | none => simp [project, shape] at computed
      | some shell =>
          cases shell with
          | atomic =>
              cases value : atomic tree with
              | none => simp [project, shape, value] at computed
              | some expression =>
                  simp [project, shape, value] at computed
                  subst parsed
                  exact Projects.atomic shape value
          | identity body => exact Projects.identity shape (ih _ _ (by simpa [project, shape] using computed))
          | complement body =>
              cases inside : project atomic insensitive fuel body with
              | none => simp [project, shape, inside] at computed
              | some result =>
                  simp [project, shape, inside] at computed
                  subst parsed
                  exact Projects.complement shape (ih _ _ inside)
          | binary operation left right =>
              cases before : project atomic insensitive fuel left with
              | none => simp [project, shape, before] at computed
              | some a =>
                  cases after : project atomic insensitive fuel right with
                  | none => simp [project, shape, before, after] at computed
                  | some b =>
                      simp [project, shape, before, after] at computed
                      subst parsed
                      exact Projects.binary shape (ih _ _ before) (ih _ _ after)
          | «prefix» scalar body =>
              cases inside : project atomic insensitive fuel body with
              | none => simp [project, shape, inside] at computed
              | some result =>
                  simp [project, shape, inside] at computed
                  subst parsed
                  exact Projects.prefix shape (ih _ _ inside)

theorem project_mono (atomic : Term → Option Expr) (insensitive : Bool) {small large : Nat}
    (enough : small ≤ large) (tree : Term) (parsed : Syntax)
    (computed : project atomic insensitive small tree = some parsed) :
    project atomic insensitive large tree = some parsed := by
  induction small generalizing large tree parsed with
  | zero => simp [project] at computed
  | succ small ih =>
      cases large with
      | zero => omega
      | succ large =>
          have enough' : small ≤ large := by omega
          cases shape : shell? tree with
          | none => simp [project, shape] at computed
          | some shell =>
              cases shell with
              | atomic => simpa [project, shape] using computed
              | identity body =>
                  exact by simpa [project, shape] using ih enough' body parsed (by simpa [project, shape] using computed)
              | complement body =>
                  cases inside : project atomic insensitive small body with
                  | none => simp [project, shape, inside] at computed
                  | some result =>
                      simp [project, shape, inside] at computed
                      subst parsed
                      simp [project, shape, ih enough' body result inside]
              | binary operation left right =>
                  cases before : project atomic insensitive small left with
                  | none => simp [project, shape, before] at computed
                  | some a =>
                      cases after : project atomic insensitive small right with
                      | none => simp [project, shape, before, after] at computed
                      | some b =>
                          simp [project, shape, before, after] at computed
                          subst parsed
                          simp [project, shape, ih enough' left a before, ih enough' right b after]
              | «prefix» scalar body =>
                  cases inside : project atomic insensitive small body with
                  | none => simp [project, shape, inside] at computed
                  | some result =>
                      simp [project, shape, inside] at computed
                      subst parsed
                      simp [project, shape, ih enough' body result inside]

theorem project_complete (atomic : Term → Option Expr) (insensitive : Bool) {tree : Term} {parsed : Syntax}
    (derivation : Projects atomic insensitive tree parsed) :
    ∃ fuel, project atomic insensitive fuel tree = some parsed := by
  induction derivation with
  | atomic shape value => exact ⟨1, by simp [project, shape, value]⟩
  | identity shape _ ih => obtain ⟨fuel, computed⟩ := ih; exact ⟨fuel + 1, by simp [project, shape, computed]⟩
  | complement shape _ ih => obtain ⟨fuel, computed⟩ := ih; exact ⟨fuel + 1, by simp [project, shape, computed]⟩
  | @binary tree operation left right a b shape _ _ before after =>
      obtain ⟨fuelA, computedA⟩ := before
      obtain ⟨fuelB, computedB⟩ := after
      exact ⟨max fuelA fuelB + 1, by simp [project, shape,
        project_mono atomic insensitive (Nat.le_max_left fuelA fuelB) left a computedA,
        project_mono atomic insensitive (Nat.le_max_right fuelA fuelB) right b computedB]⟩
  | «prefix» shape _ ih => obtain ⟨fuel, computed⟩ := ih; exact ⟨fuel + 1, by simp [project, shape, computed]⟩

theorem project_iff (atomic : Term → Option Expr) (insensitive : Bool) (tree : Term) (parsed : Syntax) :
    (∃ fuel, project atomic insensitive fuel tree = some parsed) ↔ Projects atomic insensitive tree parsed :=
  ⟨fun ⟨fuel, computed⟩ => project_sound atomic insensitive fuel tree parsed computed,
    project_complete atomic insensitive⟩

theorem selected_intervals_exact (atomic : Term → Option Expr) (insensitive : Bool)
    (catalog : Catalog) (tree : Term) (parsed : Syntax) (ranges : Ranges)
    (selected : ∃ fuel, project atomic insensitive fuel tree = some parsed)
    (compiled : lower catalog (elaborate parsed) = some ranges) (scalar : Nat) :
    Projects atomic insensitive tree parsed ∧
      (InRanges scalar ranges ↔ scalar ∈ meaning (provider catalog) parsed) :=
  ⟨(project_iff atomic insensitive tree parsed).1 selected, intervals_exact catalog parsed ranges compiled scalar⟩

namespace Controls

private def atom (tree : Term) : Option Expr :=
  if tree = cst "a" [] then some (.range 97 97)
  else if tree = cst "A" [] then some (.range 65 65)
  else none

theorem nested_negation_is_structural :
    project atom false 4 (cst "re-src:class-intersection" [cst "a" [],
      cst "re-src:class-nested-not" [cst "A" []]]) =
      some (.binary .intersection (.atomic (.range 97 97)) (.complement (.atomic (.range 65 65)))) := by
  simp [project, shell?, atom, fields?, cst]

theorem unknown_atomic_source_does_not_invent_a_class :
    project atom false 4 (cst "unresolved" []) = none := by simp [project, shell?, atom, fields?, cst]

theorem negative_class_is_not_post_folded :
    project (fun tree => Expr.fold <$> atom tree) true 4 (cst "re-src:class-not" [cst "a" []]) =
      some (.complement (.atomic (.fold (.range 97 97)))) := by
  simp [project, shell?, atom, fields?, cst]

theorem symmetric_difference_is_not_union (interpretation : Provider) :
    meaning interpretation (.binary .symmetricDifference (.atomic (.range 97 97)) (.atomic (.range 97 97))) = ∅ := by
  simp [meaning]

end Controls

end Mettapedia.GSLT.LanguageDef.RegexClassSyntax
