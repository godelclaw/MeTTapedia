import Mettapedia.OSLF.Framework.RhoScopeExpression
import Mettapedia.OSLF.Framework.RhoGeneratedScopeSubstitution

/-!
# The authored two-atom scope generator and its native reading

The sorted expression explicitly quotes a parallel composition whose two
parts are atomic or dropped recursive names. Its generic image-fibre
interpretation is compared with the independently constructed quotient
scope transformer. The resulting least fixed point is the existing
substitution-stable native scope when its atoms are native predicates.

The generator retains a finite syntactic description at every semantic
depth. Equivalent expressions can have different description costs, so the
cost belongs to the supplied expression rather than its erased denotation.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopeGeneratorInterpretation

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open BindingConstructorPredicates
open RhoEquationGeneratedScope RhoGeneratedScopeSubstitution RhoScopeExpression

universe u

def body {Atom : Type u} (left right : Atom) : Expression Atom Srt.nm :=
  .quote (.par (.or (.atom left) (.drop (.var 0))) (.or (.atom right) (.drop (.var 0))))

def generator {Atom : Type u} (left right : Atom) : Expression Atom Srt.nm :=
  .mu (body left right)

theorem part_readout {Atom : Type u} {context : Ctx sig}
    (atoms : Atom → Process context → Prop) (label : Atom)
    (env : RhoScopeExpression.Environment context) (names : NamePredicate context)
    (process : Process context) :
    denote atoms (.or (.atom label) (.drop (.var 0))) (push names env) process ↔
      Part (atoms label) names process := by
  change (atoms label process ∨ ∃ name, names name ∧ drop name = process) ↔
    (atoms label process ∨ ∃ name, names name ∧ process = drop name)
  constructor
  · rintro (atomic | ⟨name, member, readout⟩)
    · exact Or.inl atomic
    · exact Or.inr ⟨name, member, readout.symm⟩
  · rintro (atomic | ⟨name, member, readout⟩)
    · exact Or.inl atomic
    · exact Or.inr ⟨name, member, readout.symm⟩

theorem body_transformer {Atom : Type u} {context : Ctx sig}
    (atoms : Atom → Process context → Prop) (left right : Atom)
    (env : RhoScopeExpression.Environment context) :
    (denote atoms (body left right)).comp (pushNames env) = step (atoms left) (atoms right) := by
  apply OrderHom.ext
  funext names name
  apply propext
  change (∃ process,
    (∃ first second,
      denote atoms (.or (.atom left) (.drop (.var 0))) (push names env) first ∧
      denote atoms (.or (.atom right) (.drop (.var 0))) (push names env) second ∧
      join first second = process) ∧ quote process = name) ↔
    ∃ first second, quote (join first second) = name ∧
      Part (atoms left) names first ∧ Part (atoms right) names second
  constructor
  · rintro ⟨_, ⟨first, second, firstAdmitted, secondAdmitted, rfl⟩, readout⟩
    exact ⟨first, second, readout,
      (part_readout atoms left env names first).mp firstAdmitted,
      (part_readout atoms right env names second).mp secondAdmitted⟩
  · rintro ⟨first, second, readout, firstAdmitted, secondAdmitted⟩
    exact ⟨join first second, ⟨first, second,
      (part_readout atoms left env names first).mpr firstAdmitted,
      (part_readout atoms right env names second).mpr secondAdmitted, rfl⟩, readout⟩

theorem generator_denotation {Atom : Type u} {context : Ctx sig}
    (atoms : Atom → Process context → Prop) (left right : Atom)
    (env : RhoScopeExpression.Environment context) :
    denote atoms (generator left right) env = generated (atoms left) (atoms right) := by
  change ((denote atoms (body left right)).comp (pushNames env)).lfp = _
  rw [body_transformer]
  rfl

theorem generator_native_readout {Atom : Type u}
    (atoms : Atom → Predicate model Srt.pr) (left right : Atom)
    {context : Ctx sig} (env : RhoScopeExpression.Environment context) (name : Name context) :
    denote (fun label => (atoms label).holds) (generator left right) env name ↔
      (native (atoms left) (atoms right)).holds name := by
  rw [generator_denotation]
  rfl

theorem generator_description {Atom : Type u} (atomCost : Atom → Nat) (left right : Atom) :
    (generator left right).description atomCost = atomCost left + atomCost right + 9 := by
  simp only [generator, body, Expression.description]
  omega

theorem generator_closed {Atom : Type u} (left right : Atom) :
    (generator left right).closedAt 0 = true := by
  simp only [generator, body, Expression.closedAt]
  decide

theorem unbound_scope_variable_rejected {Atom : Type u} :
    (Expression.var (Atom := Atom) 0).closedAt 0 = false := rfl

theorem denotation_erases_duplicate_disjunction {Atom : Type u} {context : Ctx sig}
    (atoms : Atom → Process context → Prop) {sort : Srt} (expression : Expression Atom sort) :
    denote atoms (.or expression expression) = denote atoms expression := by
  apply OrderHom.ext
  funext env value
  change (denote atoms expression env value ∨ denote atoms expression env value) =
    denote atoms expression env value
  exact or_self _

theorem identical_readings_different_description {Atom : Type u} {context : Ctx sig}
    (atoms : Atom → Process context → Prop) (label : Atom) :
    denote atoms (.or (.atom label) (.atom label)) = denote atoms (.atom label) ∧
      (Expression.or (.atom label) (.atom label)).description (fun _ => 1) ≠
        (Expression.atom label).description (fun _ => 1) := by
  refine ⟨denotation_erases_duplicate_disjunction atoms _, ?_⟩
  change (3 : Nat) ≠ 1
  decide

end Mettapedia.OSLF.Framework.RhoScopeGeneratorInterpretation
