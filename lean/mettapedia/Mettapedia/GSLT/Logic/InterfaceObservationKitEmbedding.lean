import Mettapedia.GSLT.Logic.InterfaceObservationKitRounds

/-!
# Admission into the existing interface modal language

Every selected context formula translates to the independently defined
interface grammar using its actual arrow. The satisfaction comparison is
earned by structural induction. Unrestricted interface bisimilarity thus
implies agreement on all admitted bounded tests, without a finiteness premise.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.InterfaceObservationKit

open _root_.CategoryTheory RedexRelativeCongruence

universe u v uIndex uLabel

variable {C : Type u} [Category.{v} C] {Index : Type uIndex}
  (K : Kit.{u, v, uIndex, uLabel} C Index) (origin : C)
  (rules : ReactionRule origin → Prop)

def Formula.toInterface : {interface : Index} → Formula K interface →
    InterfaceModalLogic.Formula C (K.object interface)
  | _, .top => .top
  | _, .conj first second => .conj first.toInterface second.toInterface
  | _, .neg inner => .neg inner.toInterface
  | _, .diamond label inner => .diamond (K.context label) inner.toInterface

theorem interface_satisfaction {interface : Index} (formula : Formula K interface) :
    ∀ agent : origin ⟶ K.object interface,
      InterfaceModalLogic.Holds rules formula.toInterface agent ↔ Holds K origin rules formula agent := by
  induction formula with
  | top => intro agent; exact Iff.rfl
  | conj first second firstRead secondRead =>
      intro agent
      exact and_congr (firstRead agent) (secondRead agent)
  | neg inner inductionHypothesis => intro agent; exact not_congr (inductionHypothesis agent)
  | diamond label inner inductionHypothesis =>
      intro agent
      exact exists_congr fun target => and_congr Iff.rfl (inductionHypothesis target)

theorem all_context_bisimilarity_implies_kit_agreement {interface : Index}
    {first second : origin ⟶ K.object interface} (related : IPOBisimilar rules first second)
    (depth : Nat) : LogicallyEquivalent K origin rules depth first second := by
  intro formula _bounded
  exact (interface_satisfaction K origin rules formula first).symm.trans
    ((InterfaceModalLogic.logicallyEquivalent_of_ipoBisimilar rules related formula.toInterface).trans
      (interface_satisfaction K origin rules formula second))

end Mettapedia.GSLT.InterfaceObservationKit
