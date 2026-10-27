import Mettapedia.GSLT.Logic.SemiSaturatedBisimilarity
import Mettapedia.GSLT.Logic.BagRelativePushout

/-!
# Saturated bisimilarity of a parallel calculus, by its least labels

In a calculus whose composition is parallel, a context is the bag beside the hole (`BagRelativePushout`). There:

- **every span has relative pushouts** (`hasRedexRPOs`), so least labels characterize saturated bisimilarity
  semi-saturated (`semiSaturated_iff_saturated`): no environment tells two bags apart exactly when every least-labelled
  step of one is answered by a reaction of the other in the label's context;
- **the least label of a rule is what the agent lacks of the redex** (`actIPO_iff`): an agent `a` steps under the label
  `p` by the rule `l ⟶ k` exactly when `p = l - a`, the reaction context is `a - l`, and the result is `k + (a - l)`.
  So an agent has one least label per rule, computed by bag subtraction; a rule that the agent already contains has
  the empty label;
- the semi-saturated game is therefore finitary per rule: the challenger's labels are `l - a`, the answerer reacts in
  the context `l - a` (`semiSaturated_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.BagSaturated

open CategoryTheory
open Mettapedia.GSLT.RelativePushout
open Mettapedia.GSLT.RedexRelativeCongruence
open Mettapedia.GSLT.BagRelativePushout
open Mettapedia.GSLT.SemiSaturated

universe u

variable {α : Type u} [DecidableEq α] {rules : ReactionRule (Obj α) → Prop}

/-- The bag an arrow of the context category is. -/
def coordinates (arrow : Obj α ⟶ Obj α) : Multiset α := Multiplicative.toAdd arrow

theorem bag_coordinates (arrow : Obj α ⟶ Obj α) : bag (coordinates arrow) = arrow := rfl

/-- **Every span of a parallel calculus has relative pushouts.** -/
theorem hasRedexRPOs (rules : ReactionRule (Obj α) → Prop) : HasRedexRPOs rules := by
  intro interface agent rule _
  obtain ⟨agentBag, agentEq⟩ := bag_surjective agent
  obtain ⟨redexBag, redexEq⟩ := bag_surjective rule.redex
  rw [agentEq, redexEq]
  exact hasRelativePushouts agentBag redexBag

/-- **No environment tells two bags apart exactly when they are semi-saturated bisimilar.** -/
theorem semiSaturated_iff_saturated {left right : Obj α ⟶ Obj α} :
    SemiSaturatedBisimilar rules left right ↔ SaturatedBisimilar rules left right :=
  SemiSaturated.semiSaturated_iff_saturated (hasRedexRPOs rules)

/-- **A least bound shares nothing**: the label is what the agent lacks of the redex, the reaction context what the
redex lacks of the agent. -/
theorem least_iff (a l p r : Multiset α) :
    (a + p = l + r ∧ p ∩ r = 0) ↔ (p = l - a ∧ r = a - l) := by
  constructor
  · rintro ⟨sum, disjoint⟩
    have counts : ∀ x, a.count x + p.count x = l.count x + r.count x := fun x => by
      rw [← Multiset.count_add, ← Multiset.count_add, sum]
    have shares : ∀ x, min (p.count x) (r.count x) = 0 := fun x => by
      rw [← Multiset.count_inter, disjoint, Multiset.count_zero]
    constructor
    · ext x
      rw [Multiset.count_sub]
      have := counts x
      have := shares x
      omega
    · ext x
      rw [Multiset.count_sub]
      have := counts x
      have := shares x
      omega
  · rintro ⟨rfl, rfl⟩
    constructor
    · ext x
      rw [Multiset.count_add, Multiset.count_add, Multiset.count_sub, Multiset.count_sub]
      omega
    · ext x
      rw [Multiset.count_inter, Multiset.count_sub, Multiset.count_sub, Multiset.count_zero]
      omega

/-- **The least labels of a bag agent are what it lacks of the rules' redexes**: an agent `a` steps under `p` to `t`
exactly when, for some rule `l ⟶ k`, the label is `l - a` and the result is `k + (a - l)`. -/
theorem actIPO_iff {a p t : Multiset α} :
    ActIPO rules (bag p) (bag a) (bag t) ↔
      ∃ rule : ReactionRule (Obj α), rules rule ∧ ∃ l k : Multiset α, rule.redex = bag l ∧ rule.reactum = bag k ∧
        p = l - a ∧ t = k + (a - l) := by
  constructor
  · rintro ⟨rule, member, reaction, square, ipo, targetEq⟩
    have squareBags : bag a ≫ bag p =
        bag (coordinates rule.redex) ≫ bag (coordinates reaction) := square
    have disjoint : p ∩ coordinates reaction = 0 :=
      (isIdemPushout_bag_iff a (coordinates rule.redex) p (coordinates reaction) squareBags).mp ipo
    have sumEq : a + p = coordinates rule.redex + coordinates reaction := by
      rw [bag_comp, bag_comp] at squareBags
      exact bag_injective squareBags
    obtain ⟨labelEq, reactionEq⟩ := (least_iff a _ p _).mp ⟨sumEq, disjoint⟩
    refine ⟨rule, member, coordinates rule.redex, coordinates rule.reactum, rfl, rfl, labelEq, ?_⟩
    have targetBags : bag t = bag (coordinates rule.reactum) ≫ bag (coordinates reaction) := targetEq
    rw [bag_comp] at targetBags
    rw [← reactionEq]
    exact bag_injective targetBags
  · rintro ⟨rule, member, l, k, redexEq, reactumEq, rfl, rfl⟩
    obtain ⟨sumEq, disjoint⟩ := (least_iff a l (l - a) (a - l)).mpr ⟨rfl, rfl⟩
    have squareBags : bag a ≫ bag (l - a) = bag l ≫ bag (a - l) := by
      rw [bag_comp, bag_comp, sumEq]
    have square : bag a ≫ bag (l - a) = rule.redex ≫ bag (a - l) := by rw [redexEq]; exact squareBags
    refine ⟨rule, member, bag (a - l), square, ?_, ?_⟩
    · exact (isIdemPushout_bag_iff a (coordinates rule.redex) (l - a) (a - l) square).mpr disjoint
    · rw [reactumEq, bag_comp]

/-- **A reaction of a bag**: it contains a rule's redex, and becomes the reactum with the rest. -/
theorem reacts_iff {a t : Multiset α} :
    Reacts rules (bag a) (bag t) ↔
      ∃ rule : ReactionRule (Obj α), rules rule ∧ ∃ l k : Multiset α, rule.redex = bag l ∧ rule.reactum = bag k ∧
        l ≤ a ∧ t = k + (a - l) := by
  constructor
  · rintro ⟨rule, member, reaction, agentEq, targetEq⟩
    have agentBags : bag a = bag (coordinates rule.redex) ≫ bag (coordinates reaction) := agentEq
    have targetBags : bag t = bag (coordinates rule.reactum) ≫ bag (coordinates reaction) := targetEq
    rw [bag_comp] at agentBags targetBags
    have sum := bag_injective agentBags
    have target := bag_injective targetBags
    refine ⟨rule, member, coordinates rule.redex, coordinates rule.reactum, rfl, rfl, ?_, ?_⟩
    · rw [sum]
      exact Multiset.le_add_right _ _
    · rw [target, sum, add_tsub_cancel_left]
  · rintro ⟨rule, member, l, k, redexEq, reactumEq, contained, rfl⟩
    refine ⟨rule, member, bag (a - l), ?_, ?_⟩
    · rw [redexEq, bag_comp, add_tsub_cancel_of_le contained]
    · rw [reactumEq, bag_comp]

end Mettapedia.GSLT.BagSaturated
