import Mettapedia.OSLF.Framework.RhoScopeBinaryDescription
import Mettapedia.OSLF.Syntax.RhoScopedScopeDecision
import Mathlib.Data.Nat.Lattice

/-!
# Sorted scope formulas, exact membership, and description upper bounds

The existing existential interpretation of quoted parallel formulas agrees
with the independent process-class composite scope. Canonical readback and
finite catalogue search therefore act on the formula semantics itself.

Minimum description length is measured over all expressions interpreted
in one declared atom language and environment, using the independently
decoded binary programs. Describable process scopes have a composite name
scope description with at most the sum of their minimum lengths plus six.
This construction does not assert an additive lower bound.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoScopeExpressionDecomposition

open Mettapedia.OSLF.Binding RhoSchema RhoQuotationClassFibres RhoScopedParallelInventory
open RhoScopedScopeDecomposition RhoScopedScopeDecision
open RhoScopeExpression RhoScopeBinaryDescription

universe u

variable {Atom : Type u} {context : Ctx sig}

def reading (atoms : Atom → Process context → Prop) (env : Environment context)
    {sort : Srt} (expression : Expression Atom sort) : TermQ rhoSourceE context sort → Prop :=
  denote atoms expression env

theorem reading_quote_parallel (atoms : Atom → Process context → Prop) (env : Environment context)
    (first second : Expression Atom Srt.pr) :
    reading atoms env (.quote (.par first second)) =
      Composite (reading atoms env first) (reading atoms env second) := by
  funext name
  apply propext
  change (∃ whole, (∃ a b, reading atoms env first a ∧ reading atoms env second b ∧
      join a b = whole) ∧ quote whole = name) ↔ _
  constructor
  · rintro ⟨whole, ⟨a, b, firstAdmitted, secondAdmitted, same⟩, readout⟩
    exact ⟨a, b, firstAdmitted, secondAdmitted, (congrArg quote same).trans readout⟩
  · rintro ⟨a, b, firstAdmitted, secondAdmitted, readout⟩
    exact ⟨join a b, ⟨a, b, firstAdmitted, secondAdmitted, rfl⟩, readout⟩

theorem formula_membership_iff_fast_verdict (atoms : Atom → Process context → Prop)
    (env : Environment context) (first second : Expression Atom Srt.pr)
    [DecidablePred (reading atoms env first)] [DecidablePred (reading atoms env second)]
    {classify : Prime context → Bool}
    (leftSupport : LeftSupported classify (reading atoms env first))
    (rightSupport : RightSupported classify (reading atoms env second))
    (exposed : ExposedComposites (reading atoms env first) (reading atoms env second))
    (name : Name context) :
    reading atoms env (.quote (.par first second)) name ↔
      verdict classify (reading atoms env first) (reading atoms env second) name = true := by
  rw [reading_quote_parallel]
  exact (verdict_iff_composite leftSupport rightSupport exposed name).symm

theorem formula_membership_iff_complete_search (atoms : Atom → Process context → Prop)
    (env : Environment context) (first second : Expression Atom Srt.pr)
    [DecidablePred (reading atoms env first)] [DecidablePred (reading atoms env second)]
    (name : Name context) :
    reading atoms env (.quote (.par first second)) name ↔
      (admittedCatalogue (reading atoms env first) (reading atoms env second) name).Nonempty := by
  rw [reading_quote_parallel]
  exact composite_iff_catalogue_nonempty name

def lengths (atoms : Atom → Process context → Prop) (env : Environment context)
    (code : AtomCode Atom) {sort : Srt} (scope : TermQ rhoSourceE context sort → Prop) : Set Nat :=
  {length | ∃ expression : Expression Atom sort,
    reading atoms env expression = scope ∧ (encodeBinary code expression).length = length}

def Describable (atoms : Atom → Process context → Prop) (env : Environment context)
    {sort : Srt} (scope : TermQ rhoSourceE context sort → Prop) : Prop :=
  ∃ expression : Expression Atom sort, reading atoms env expression = scope

noncomputable def minimum (atoms : Atom → Process context → Prop) (env : Environment context)
    (code : AtomCode Atom) {sort : Srt} (scope : TermQ rhoSourceE context sort → Prop) : Nat :=
  sInf (lengths atoms env code scope)

theorem minimum_realized (atoms : Atom → Process context → Prop) (env : Environment context)
    (code : AtomCode Atom) {sort : Srt} {scope : TermQ rhoSourceE context sort → Prop}
    (described : Describable atoms env scope) :
    ∃ expression : Expression Atom sort, reading atoms env expression = scope ∧
      (encodeBinary code expression).length = minimum atoms env code scope := by
  obtain ⟨expression, same⟩ := described
  have nonempty : (lengths atoms env code scope).Nonempty :=
    ⟨_, expression, same, rfl⟩
  exact Nat.sInf_mem nonempty

theorem minimum_le_supplied_description (atoms : Atom → Process context → Prop)
    (env : Environment context) (code : AtomCode Atom) {sort : Srt}
    (expression : Expression Atom sort) :
    minimum atoms env code (reading atoms env expression) ≤ (encodeBinary code expression).length :=
  Nat.sInf_le ⟨expression, rfl, rfl⟩

/-- The actual compiled descriptions yield a uniform semantic minimum upper bound. -/
theorem composite_minimum_upper_bound (atoms : Atom → Process context → Prop)
    (env : Environment context) (code : AtomCode Atom)
    {left right : Process context → Prop}
    (leftDescribed : Describable atoms env left) (rightDescribed : Describable atoms env right) :
    minimum atoms env code (Composite left right) ≤
      minimum atoms env code left + minimum atoms env code right + 6 := by
  obtain ⟨first, sameFirst, firstLength⟩ := minimum_realized atoms env code leftDescribed
  obtain ⟨second, sameSecond, secondLength⟩ := minimum_realized atoms env code rightDescribed
  have supplied := minimum_le_supplied_description atoms env code (.quote (.par first second))
  rw [reading_quote_parallel, sameFirst, sameSecond,
    quoted_parallel_description_length, firstLength, secondLength] at supplied
  exact supplied

theorem minimum_lower_bound (atoms : Atom → Process context → Prop) (env : Environment context)
    (code : AtomCode Atom) {sort : Srt} {scope : TermQ rhoSourceE context sort → Prop}
    (described : Describable atoms env scope) {bound : Nat}
    (allDescriptions : ∀ expression : Expression Atom sort,
      reading atoms env expression = scope → bound ≤ (encodeBinary code expression).length) :
    bound ≤ minimum atoms env code scope := by
  obtain ⟨expression, same, exactLength⟩ := minimum_realized atoms env code described
  rw [← exactLength]
  exact allDescriptions expression same

end Mettapedia.OSLF.Framework.RhoScopeExpressionDecomposition
