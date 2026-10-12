import Mettapedia.OSLF.NativeTypes.Semantics.Structural

open Mettapedia.OSLF.Framework

/-!
# Executable constructor decomposition contracts

A decomposition backend returns actual typed constructor introductions. The
soundness and coverage obligations concern those introductions and primitive
equation classes, before any generated structural predicate is checked.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.Structural.ConstructorBackend

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.NativeTypes.Generation (Generated structuralDeclaration)

abbrev Constructor (generated : Generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) :=
  Mettapedia.OSLF.NativeTypes.Structural.ConstructorValue generated.snapshot.language generated.snapshot.free bound
    (structuralDeclaration generated index)

abbrev Related (generated : Generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length) (source : Pattern)
    (value : Constructor generated bound index) :=
  Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound
    (.base (structuralDeclaration generated index).category)) source value.pattern

def argument {generated : Generated} {bound : List TypeExpr}
    {index : Fin generated.snapshot.language.terms.length}
    (value : Constructor generated bound index)
    (position : Fin (structuralDeclaration generated index).params.length) : Pattern :=
  value.arguments[position.val]'(by rw [value.arguments_length]; exact position.isLt)

abbrev InputRelated (generated : Generated) (bound : List TypeExpr)
    (index : Fin generated.snapshot.language.terms.length)
    (position : Fin (structuralDeclaration generated index).params.length) (first second : Pattern) :=
  Relation.EqvGen (GeneralOccurrenceSemantics.Equation generated.plan bound
    (structuralDeclaration generated index).params[position].typeExpr) first second

structure Backend (generated : Generated) (bound : List TypeExpr) (admitted : Pattern → Prop) where
  values : Nat → (index : Fin generated.snapshot.language.terms.length) → Pattern →
    List (Constructor generated bound index)
  closed : Nat → Fin generated.snapshot.language.terms.length → Pattern → Bool
  sound : ∀ budget index source value,
    value ∈ values budget index source → Related generated bound index source value
  coverage : ∀ budget index source,
    closed budget index source = true →
    ∀ value : Constructor generated bound index, Related generated bound index source value →
      ∃ candidate, candidate ∈ values budget index source
  completionBudget : Fin generated.snapshot.language.terms.length → Pattern → Nat
  complete_at : ∀ index source, admitted source →
    closed (completionBudget index source) index source = true
  values_stable : ∀ index source budget, completionBudget index source ≤ budget →
    values budget index source = values (completionBudget index source) index source
  closed_stable : ∀ index source budget, completionBudget index source ≤ budget →
    closed budget index source = closed (completionBudget index source) index source

/-- Ordered coverage is primitive decomposition data: it preserves each
argument class, independently of any predicates later supplied for them. -/
structure OrderedBackend (generated : Generated) (bound : List TypeExpr)
    (admitted : Pattern → Prop) extends Backend generated bound admitted where
  ordered_coverage : ∀ budget index source,
    closed budget index source = true →
    ∀ value : Constructor generated bound index, Related generated bound index source value →
      ∃ candidate, candidate ∈ values budget index source ∧
        ∀ position, InputRelated generated bound index position
          (argument value position) (argument candidate position)

theorem completed_values_exact {generated : Generated} {bound : List TypeExpr} {admitted : Pattern → Prop}
    (backend : Backend generated bound admitted) (budget : Nat)
    (index : Fin generated.snapshot.language.terms.length) (source : Pattern)
    (closed : backend.closed budget index source = true) :
    (∃ candidate, candidate ∈ backend.values budget index source) ↔
      ∃ value : Constructor generated bound index, Related generated bound index source value := by
  constructor
  · rintro ⟨candidate, listed⟩
    exact ⟨candidate, backend.sound budget index source candidate listed⟩
  · rintro ⟨value, related⟩
    exact backend.coverage budget index source closed value related

end Mettapedia.OSLF.NativeTypes.Decision.Structural.ConstructorBackend
