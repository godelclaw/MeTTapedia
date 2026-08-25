import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactor

/-!
# Total interface reachability after bounded deletion

The mask-stable interface contraction is naturally stated on surviving
coordinates.  A cumulative transition, however, may retain names for ports
whose represented graph vertex has just been deleted.  Graph reachability is
still reflexive at such an isolated vertex, so simply requiring both named
ports to survive would lose the equality case.

This file gives the exact total extension.  Two arbitrary interface slots are
reachable after a mask precisely when they denote the same ambient vertex, or
when both survive and the existing finite interface closure connects them.
It is graph-generic and does not assert a corridor transition or a reachable
state count.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceDeletionComponentFactorTotal

open GoertzelV24DeletionSensitivePortResidualFactorContraction
open GoertzelV24InterfaceDeletionComponentFactor
open SimpleGraph

/-- Total finite interpretation of an interface code after one deletion mask.
The explicit equality branch retains reflexive reachability for aliases and
for coordinates whose represented vertex was deleted. -/
def InterfaceExteriorTotalFactoredReachability
    {N Interface : Type*}
    (code : BoundedInterfaceExteriorCode Interface)
    (interfaceVertex : Interface → N) (removed : Interface → Bool)
    (left right : Interface) : Prop :=
  interfaceVertex left = interfaceVertex right ∨
    ∃ (hleft : survivesMask interfaceVertex removed
        (interfaceVertex left))
      (hright : survivesMask interfaceVertex removed
        (interfaceVertex right)),
      Relation.ReflTransGen
        (fun first second :
            SurvivingInterfaceSlot interfaceVertex removed =>
          InterfaceExteriorFactoredStep code first.1 second.1)
        ⟨left, hleft⟩ ⟨right, hright⟩

/-- Reachability in a masked graph, including deleted or aliased named slots,
is exactly equality or the surviving-interface closure. -/
theorem restrictedByMask_reachable_iff_totalInterfaceExteriorClosure
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (removed : Interface → Bool)
    (left right : Interface) :
    (restrictedByMask graph interfaceVertex removed).Reachable
        (interfaceVertex left) (interfaceVertex right) ↔
      interfaceVertex left = interfaceVertex right ∨
        ∃ (hleft : survivesMask interfaceVertex removed
            (interfaceVertex left))
          (hright : survivesMask interfaceVertex removed
            (interfaceVertex right)),
          Relation.ReflTransGen
            (SurvivingInterfaceExteriorStep graph interfaceVertex removed)
            ⟨left, hleft⟩ ⟨right, hright⟩ := by
  constructor
  · intro hreachable
    by_cases heq : interfaceVertex left = interfaceVertex right
    · exact Or.inl heq
    · have hleftSupport : interfaceVertex left ∈
          (restrictedByMask graph interfaceVertex removed).support :=
        SimpleGraph.mem_support_of_reachable heq hreachable
      have hrightSupport : interfaceVertex right ∈
          (restrictedByMask graph interfaceVertex removed).support :=
        SimpleGraph.mem_support_of_reachable (fun h => heq h.symm)
          hreachable.symm
      rcases hleftSupport with ⟨leftNeighbor, hleftAdj⟩
      rcases hrightSupport with ⟨rightNeighbor, hrightAdj⟩
      have hleftSurvives : survivesMask interfaceVertex removed
          (interfaceVertex left) :=
        ((supportRestriction_adj graph
          (survivesMask interfaceVertex removed) _ _).1 hleftAdj).2.1
      have hrightSurvives : survivesMask interfaceVertex removed
          (interfaceVertex right) :=
        ((supportRestriction_adj graph
          (survivesMask interfaceVertex removed) _ _).1 hrightAdj).2.1
      exact Or.inr ⟨hleftSurvives, hrightSurvives,
        (restrictedByMask_reachable_iff_interfaceExteriorClosure graph
          interfaceVertex removed ⟨left, hleftSurvives⟩
            ⟨right, hrightSurvives⟩).1 hreachable⟩
  · rintro (heq | ⟨hleft, hright, hclosure⟩)
    · rw [heq]
    · exact (restrictedByMask_reachable_iff_interfaceExteriorClosure graph
        interfaceVertex removed ⟨left, hleft⟩ ⟨right, hright⟩).2
          hclosure

/-- The mask-independent exact code computes the total masked relation on all
named interface slots, not only on a subtype of surviving ones. -/
theorem exactInterfaceExteriorCode_totalFactoredReachability_iff
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (removed : Interface → Bool)
    (left right : Interface) :
    InterfaceExteriorTotalFactoredReachability
        (exactInterfaceExteriorCode graph interfaceVertex)
        interfaceVertex removed left right ↔
      (restrictedByMask graph interfaceVertex removed).Reachable
        (interfaceVertex left) (interfaceVertex right) := by
  rw [restrictedByMask_reachable_iff_totalInterfaceExteriorClosure]
  unfold InterfaceExteriorTotalFactoredReachability
  apply or_congr Iff.rfl
  constructor
  · rintro ⟨hleft, hright, hclosure⟩
    exact ⟨hleft, hright, hclosure.mono fun first second hstep =>
      (exactInterfaceExteriorCode_step_iff graph interfaceVertex
        first.1 second.1).1 hstep⟩
  · rintro ⟨hleft, hright, hclosure⟩
    exact ⟨hleft, hright, hclosure.mono fun first second hstep =>
      (exactInterfaceExteriorCode_step_iff graph interfaceVertex
        first.1 second.1).2 hstep⟩

end GoertzelV24InterfaceDeletionComponentFactorTotal

end Mettapedia.GraphTheory.FourColor
