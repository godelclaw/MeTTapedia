import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceDeletionComponentFactorTotal

/-!
# A finite graph presentation of total interface reachability

`InterfaceExteriorTotalFactoredReachability` is the exact finite relation on
named interface coordinates after a deletion mask.  Downstream component
factorizations are phrased for `SimpleGraph`, so this file turns that relation
into a graph: distinct related coordinates are joined directly.

When the interface code is exact, connected components of the finite graph
are exactly the connected components of the masked ambient graph, including
aliases and isolated deleted coordinates.  This is a representation lemma;
it does not introduce a corridor letter or a reachable-state count.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InterfaceDeletionComponentFactorTotalGraph

open GoertzelV24InterfaceDeletionComponentFactor
open GoertzelV24InterfaceDeletionComponentFactorTotal
open GoertzelV24DeletionSensitivePortResidualFactorContraction
open SimpleGraph

/-- Make the total finite reachability relation into a simple graph.  The
constructor removes loops and symmetrizes the supplied relation; neither
operation changes its connected components when the relation represents
graph reachability. -/
def totalFactoredComponentGraph
    {N Interface : Type*}
    (code : BoundedInterfaceExteriorCode Interface)
    (interfaceVertex : Interface → N) (removed : Interface → Bool) :
    SimpleGraph Interface :=
  SimpleGraph.fromRel fun left right =>
    InterfaceExteriorTotalFactoredReachability code interfaceVertex removed
      left right

/-- A relation which exactly presents reachability in another graph has the
same reflexive-transitive closure after `totalFactoredComponentGraph` turns it
into an undirected loopless graph. -/
theorem totalFactoredComponentGraph_reachable_iff_of_exact
    {N Interface : Type*}
    (code : BoundedInterfaceExteriorCode Interface)
    (interfaceVertex : Interface → N) (removed : Interface → Bool)
    (graph : SimpleGraph N)
    (hexact : ∀ left right,
      InterfaceExteriorTotalFactoredReachability code interfaceVertex removed
          left right ↔
        graph.Reachable (interfaceVertex left) (interfaceVertex right))
    (left right : Interface) :
    (totalFactoredComponentGraph code interfaceVertex removed).Reachable
        left right ↔
      graph.Reachable (interfaceVertex left) (interfaceVertex right) := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro hclosure
    induction hclosure with
    | refl => exact SimpleGraph.Reachable.rfl
    | @tail middle finish _ hadj ih =>
        have hstep : graph.Reachable
            (interfaceVertex middle) (interfaceVertex finish) := by
          rcases (SimpleGraph.fromRel_adj _ middle finish).1 hadj with
            ⟨_, hforward | hbackward⟩
          · exact (hexact middle finish).1 hforward
          · exact ((hexact finish middle).1 hbackward).symm
        exact ih.trans hstep
  · intro hreachable
    by_cases heq : left = right
    · subst right
      exact Relation.ReflTransGen.refl
    · apply Relation.ReflTransGen.single
      apply (SimpleGraph.fromRel_adj _ left right).2
      exact ⟨heq, Or.inl ((hexact left right).2 hreachable)⟩

/-- The canonical mask-independent interface code therefore has a literal
finite component graph which is exact for the masked ambient graph. -/
theorem exactInterfaceExteriorCode_totalFactoredComponentGraph_reachable_iff
    {N Interface : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (removed : Interface → Bool)
    (left right : Interface) :
    (totalFactoredComponentGraph
        (exactInterfaceExteriorCode graph interfaceVertex)
        interfaceVertex removed).Reachable left right ↔
      (restrictedByMask graph interfaceVertex removed).Reachable
        (interfaceVertex left) (interfaceVertex right) := by
  apply totalFactoredComponentGraph_reachable_iff_of_exact
  intro first second
  exact exactInterfaceExteriorCode_totalFactoredReachability_iff graph
    interfaceVertex removed first second

end GoertzelV24InterfaceDeletionComponentFactorTotalGraph

end Mettapedia.GraphTheory.FourColor
