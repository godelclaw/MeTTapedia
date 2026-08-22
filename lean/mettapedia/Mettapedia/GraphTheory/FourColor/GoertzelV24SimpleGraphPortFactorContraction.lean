import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Factoring graph reachability through named ports

A finite interface may contain local attachment positions that are not
themselves the persistent ports of a cumulative region.  This module isolates
the exact generic condition under which reachability between those positions
is nevertheless determined by two finite relations: attachment to a named
port, and connectivity between named ports.

The coverage premise is deliberately support-sensitive.  Reflexive
reachability of an isolated interface position requires no port; every
nontrivial component move does.  This distinction prevents a padded or
isolated coordinate from being silently treated as source geometry.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SimpleGraphPortFactorContraction

open SimpleGraph

/-- The graph-independent relation obtained by passing from each finite
interface position to a named port, moving between ports, and returning to
the interface.  Equality of the decoded ambient vertices is retained as the
reflexive case because two finite coordinates need not be injective. -/
def PortFactoredReachability
    {N Interface Port : Type*}
    (interfaceVertex : Interface → N)
    (attaches : Interface → Port → Prop)
    (portConnected : Port → Port → Prop)
    (left right : Interface) : Prop :=
  interfaceVertex left = interfaceVertex right ∨
    ∃ leftPort rightPort,
      attaches left leftPort ∧
        portConnected leftPort rightPort ∧
        attaches right rightPort

/-- If the finite attachment relation is sound and covers every supported
interface vertex, and the finite port relation is sound everywhere and
complete on supported ports, then it exactly records graph reachability on
the whole finite interface.  The support qualification matches guarded
boundary profiles, whose diagonal is false at an inactive port even though
graph reachability itself is reflexive there.

This theorem does not manufacture either finite relation.  In a source
application, `attaches` is local geometry and `portConnected` is read from the
incoming boundary profile. -/
theorem reachable_iff_portFactoredReachability
    {N Interface Port : Type*} (graph : SimpleGraph N)
    (interfaceVertex : Interface → N) (portVertex : Port → N)
    (attaches : Interface → Port → Prop)
    (portConnected : Port → Port → Prop)
    (hattachSound : ∀ interface port,
      attaches interface port →
        graph.Reachable (interfaceVertex interface) (portVertex port))
    (hattachCoverage : ∀ interface,
      interfaceVertex interface ∈ graph.support →
        ∃ port, attaches interface port)
    (hportSound : ∀ left right,
      portConnected left right →
        graph.Reachable (portVertex left) (portVertex right))
    (hportComplete : ∀ left right,
      portVertex left ∈ graph.support →
      portVertex right ∈ graph.support →
      graph.Reachable (portVertex left) (portVertex right) →
        portConnected left right)
    (left right : Interface) :
    graph.Reachable (interfaceVertex left) (interfaceVertex right) ↔
      PortFactoredReachability interfaceVertex attaches
        portConnected left right := by
  constructor
  · intro hreachable
    by_cases heq : interfaceVertex left = interfaceVertex right
    · exact Or.inl heq
    · have hleftSupport : interfaceVertex left ∈ graph.support :=
        SimpleGraph.mem_support_of_reachable heq hreachable
      have hrightSupport : interfaceVertex right ∈ graph.support :=
        SimpleGraph.mem_support_of_reachable (fun h => heq h.symm)
          hreachable.symm
      rcases hattachCoverage left hleftSupport with ⟨leftPort, hleft⟩
      rcases hattachCoverage right hrightSupport with ⟨rightPort, hright⟩
      have hleftPortSupport : portVertex leftPort ∈ graph.support := by
        by_cases hvertex : interfaceVertex left = portVertex leftPort
        · simpa [hvertex] using hleftSupport
        · exact SimpleGraph.mem_support_of_reachable
            (fun h => hvertex h.symm)
            (hattachSound left leftPort hleft).symm
      have hrightPortSupport : portVertex rightPort ∈ graph.support := by
        by_cases hvertex : interfaceVertex right = portVertex rightPort
        · simpa [hvertex] using hrightSupport
        · exact SimpleGraph.mem_support_of_reachable
            (fun h => hvertex h.symm)
            (hattachSound right rightPort hright).symm
      refine Or.inr ⟨leftPort, rightPort, hleft, ?_, hright⟩
      exact hportComplete leftPort rightPort hleftPortSupport
        hrightPortSupport ((hattachSound left leftPort hleft).symm.trans
          (hreachable.trans (hattachSound right rightPort hright)))
  · intro hfactored
    rcases hfactored with heq | ⟨leftPort, rightPort, hleft, hports, hright⟩
    · rw [heq]
    · exact (hattachSound left leftPort hleft).trans
        ((hportSound leftPort rightPort hports).trans
          (hattachSound right rightPort hright).symm)

end GoertzelV24SimpleGraphPortFactorContraction

end Mettapedia.GraphTheory.FourColor
