import Mettapedia.GSLT.Logic.HigherOrderContextClosure
import Mettapedia.Order.PredicateFixedPointEncodings

/-!
# Quantified predicates for the existing higher-order progression operator

The predicate formulas are formed on complete interface-indexed state pairs.
Their interpretation uses the original progression operator, including actual
successors, observations and process-bearing label payloads. Induction and
coinduction compare these independently formed formulas with the existing
lattice construction. Literal IPO labels recover the original reactive
system's bisimilarity without a branching assumption.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HigherOrderBisimulation

open Mettapedia.Order

universe uInterface uState uSkeleton uAtom

variable {Interface : Type uInterface} {State : Interface → Type uState}
  {vocabulary : Vocabulary.{uInterface, uSkeleton} Interface}

namespace System

variable (system : System vocabulary State)

def leastRelation : RelationFamily State :=
  unpack (PredicateFixedPointEncodings.least system.progressOnJudgments)

def greatestRelation : RelationFamily State :=
  unpack (PredicateFixedPointEncodings.greatest system.progressOnJudgments)

theorem leastRelation_induction (relation : RelationFamily State)
    (closed : system.progress relation ≤ relation) : system.leastRelation ≤ relation := by
  intro interface first second related
  exact related (pack relation) (fun pair => closed pair.1 pair.2.1 pair.2.2)

theorem greatestRelation_coinduction (relation : RelationFamily State)
    (invariant : relation ≤ system.progress relation) : relation ≤ system.greatestRelation := by
  intro interface first second related
  exact ⟨pack relation, (fun pair => invariant pair.1 pair.2.1 pair.2.2), related⟩

theorem leastRelation_unfold : system.progress system.leastRelation = system.leastRelation := by
  have fixed := PredicateFixedPointEncodings.least_unfold system.progressOnJudgments
  exact congrArg unpack fixed

theorem greatestRelation_unfold : system.progress system.greatestRelation = system.greatestRelation := by
  have fixed := PredicateFixedPointEncodings.greatest_unfold system.progressOnJudgments
  exact congrArg unpack fixed

theorem greatestRelation_iff_bisimilar {interface : Interface} (first second : State interface) :
    system.greatestRelation interface first second ↔ system.Bisimilar interface first second := by
  constructor
  · exact system.coinduction system.greatestRelation_unfold.symm.le interface first second
  · exact system.greatestRelation_coinduction system.Bisimilar
      (fun _ _ _ related => system.bisimilar_unfold.mp related) interface first second

theorem leastRelation_le_greatestRelation : system.leastRelation ≤ system.greatestRelation :=
  system.leastRelation_induction system.greatestRelation system.greatestRelation_unfold.le

end System

section IPO

open CategoryTheory Mettapedia.GSLT.RedexRelativeCongruence

universe v u

variable {C : Type u} [Category.{v} C] {origin : C}

theorem ipo_coinductive_iff (rules : ReactionRule origin → Prop) {interface : C}
    (first second : origin ⟶ interface) :
    (ipoSystem rules).greatestRelation interface first second ↔ IPOBisimilar rules first second :=
  ((ipoSystem rules).greatestRelation_iff_bisimilar first second).trans
    (ipo_bisimilar_iff rules first second)

end IPO

end Mettapedia.GSLT.HigherOrderBisimulation
