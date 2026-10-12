import Mettapedia.OSLF.Framework.ScopedBindingInstrumentLogic

/-!
# Equation-compatible structural tests as actual binding instrument interactions

Every admitted constructor test is one actual ask transition followed by its
actual get transitions. Each projection returns the selected argument at its
original extended binder context. Arbitrary postconditions respect the
authored equations through the earned base action and observation laws.

The theorem concerns the explicit instrument extension. It does not convert
an inspection transition beneath a binder into an original reduction step.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.ScopedInstruments.Admission

open ScopedEncoding
open Mettapedia.OSLF.Framework

universe uAtom uLabel
variable {S : Signature} {E : EquationTheory S}

theorem holds_equation (base : BaseSystem.{uAtom,uLabel} E)
    {scope : Scope S} (formula : Formula S base.Atom base.Label scope)
    {before after : Term S scope.1 scope.2} (related : E.relation before after) :
    Holds base formula before ↔ Holds base formula after :=
  (holds_encode_iff base formula before).symm.trans
    ((SortedInstrumentCongruence.holds_resp (sortedBase base) formula
      ((sorted_relation_encode E before after).mpr related)).trans
        (holds_encode_iff base formula after))

theorem ask_readout (base : BaseSystem.{uAtom,uLabel} E)
    {opened : Constructor S → Prop} (constructor : Constructor S)
    (value : Term S ((signature S).output constructor).1 ((signature S).output constructor).2)
    (arguments : Arguments constructor)
    (step : Act base opened (.ask constructor) (.term value) (.bundle constructor arguments)) :
    E.relation value (buildTerm constructor arguments) := by
  cases step with
  | ask _ _ related => exact related

theorem structural_iff_interactions (base : BaseSystem.{uAtom,uLabel} E)
    {opened : Constructor S → Prop} (constructor : Constructor S) (allowed : opened constructor)
    (clauses : (position : Fin ((signature S).arity constructor)) →
      Formula S base.Atom base.Label ((signature S).input constructor position))
    (value : Term S ((signature S).output constructor).1 ((signature S).output constructor).2) :
    Holds base (.node constructor clauses) value ↔
      ∃ arguments : Arguments constructor,
        Act base opened (.ask constructor) (.term value) (.bundle constructor arguments) ∧
        ∀ position, ∃ projected : Term S ((signature S).input constructor position).1
            ((signature S).input constructor position).2,
          Act base opened (.get constructor position) (.bundle constructor arguments) (.term projected) ∧
          Holds base (clauses position) projected := by
  constructor
  · rintro ⟨arguments, related, postconditions⟩
    refine ⟨arguments, .ask constructor allowed related, ?_⟩
    intro position
    exact ⟨readArguments constructor arguments position,
      .get constructor allowed position (E.reflexive _), postconditions position⟩
  · rintro ⟨arguments, asked, projections⟩
    refine ⟨arguments, ask_readout base constructor value arguments asked, ?_⟩
    intro position
    obtain ⟨projected, got, postcondition⟩ := projections position
    exact (holds_equation base (clauses position)
      (Act.get_readout constructor arguments position projected got)).mpr postcondition

end Mettapedia.OSLF.Binding.ScopedInstruments.Admission
