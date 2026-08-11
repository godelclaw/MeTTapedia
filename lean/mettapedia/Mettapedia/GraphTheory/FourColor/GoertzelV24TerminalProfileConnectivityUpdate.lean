import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileRestriction
import Mettapedia.GraphTheory.FourColor.GoertzelV24InterfaceSpliceConnectivity

/-!
# Relational connectivity update across one corridor Cell

The terminal-aware Cell-3 state records connectivity from the moving cut to
five fixed cap-foot terminals.  Extending the prefix by one literal Cell does
not in general determine a new profile as a function of the old one: the Cell
can have more than one compatible coloring.  The source transfer is therefore
kept relational.

This file isolates the connectivity part of that relation.  When every tracked
adjacency in the union of an old prefix and a new Cell belongs wholly to one of
the two regions, the regional tracked graph of the union is their graph
supremum.  Consequently, connectivity after the extension is precisely the
reflexive-transitive closure of old-prefix and Cell component moves through the
shared interface.

No capped-face update is asserted here.  Connectivity and face progress must
ultimately be packaged together in the terminal-aware transfer law.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TerminalProfileConnectivityUpdate

open GoertzelV24HexSlabConnectivityProfile
open GoertzelV24InterfaceSpliceConnectivity
open SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Every ambient tracked adjacency supported in the union of two regions is
already wholly supported in one of them.  For consecutive corridor pieces this
is the exact local coverage fact supplied by the literal seam geometry. -/
def RegionalTrackedAdjacencyCovered
    (RS : RotationSystem V E) (leftRegion rightRegion : Finset E)
    (C : E → Color) (a b : Color) : Prop :=
  ∀ {x y : E},
    (RS.trackedEdgeGraph C a b).Adj x y →
    x ∈ leftRegion ∪ rightRegion →
    y ∈ leftRegion ∪ rightRegion →
    (x ∈ leftRegion ∧ y ∈ leftRegion) ∨
      (x ∈ rightRegion ∧ y ∈ rightRegion)

/-- Under literal adjacency coverage, restricting the tracked graph to a union
of regions is exactly the supremum of the two regional restrictions. -/
theorem regionalTrackedEdgeGraph_union_eq_sup_of_adjacencyCovered
    (RS : RotationSystem V E) (leftRegion rightRegion : Finset E)
    (C : E → Color) (a b : Color)
    (hcovered : RegionalTrackedAdjacencyCovered RS leftRegion rightRegion C a b) :
    regionalTrackedEdgeGraph RS (leftRegion ∪ rightRegion) C a b =
      regionalTrackedEdgeGraph RS leftRegion C a b ⊔
        regionalTrackedEdgeGraph RS rightRegion C a b := by
  ext x y
  change
    ((RS.trackedEdgeGraph C a b).Adj x y ∧
        x ∈ leftRegion ∪ rightRegion ∧
        y ∈ leftRegion ∪ rightRegion) ↔
      (((RS.trackedEdgeGraph C a b).Adj x y ∧
          x ∈ leftRegion ∧ y ∈ leftRegion) ∨
        ((RS.trackedEdgeGraph C a b).Adj x y ∧
          x ∈ rightRegion ∧ y ∈ rightRegion))
  constructor
  · rintro ⟨hadj, hx, hy⟩
    rcases hcovered hadj hx hy with hleft | hright
    · exact Or.inl ⟨hadj, hleft⟩
    · exact Or.inr ⟨hadj, hright⟩
  · rintro (hleft | hright)
    · exact ⟨hleft.1, Finset.mem_union_left _ hleft.2.1,
        Finset.mem_union_left _ hleft.2.2⟩
    · exact ⟨hright.1, Finset.mem_union_right _ hright.2.1,
        Finset.mem_union_right _ hright.2.2⟩

/-- Connectivity after adjoining one Cell is the closure of whole-component
moves in the old prefix and in the Cell, with switches confined to their
literal shared interface.  This is the relational connectivity update used by
the terminal-aware transfer state. -/
theorem regionalTrackedEdgeGraph_union_reachable_iff_componentClosure
    (RS : RotationSystem V E) (leftRegion rightRegion : Finset E)
    (C : E → Color) (a b : Color)
    (hcovered : RegionalTrackedAdjacencyCovered RS leftRegion rightRegion C a b)
    {start finish : E}
    (hstart : start ∈ leftRegion ∩ rightRegion)
    (hfinish : finish ∈ leftRegion ∩ rightRegion) :
    (regionalTrackedEdgeGraph RS (leftRegion ∪ rightRegion) C a b).Reachable
        start finish ↔
      Relation.ReflTransGen
        (fun x y : Subtype (fun edge => edge ∈ leftRegion ∩ rightRegion) =>
          (regionalTrackedEdgeGraph RS leftRegion C a b).Reachable x y ∨
          (regionalTrackedEdgeGraph RS rightRegion C a b).Reachable x y)
        ⟨start, hstart⟩ ⟨finish, hfinish⟩ := by
  rw [regionalTrackedEdgeGraph_union_eq_sup_of_adjacencyCovered
    RS leftRegion rightRegion C a b hcovered]
  exact reachable_sup_iff_subtype_componentClosure
    (regionalTrackedEdgeGraph RS leftRegion C a b)
    (regionalTrackedEdgeGraph RS rightRegion C a b)
    (fun edge => edge ∈ leftRegion ∩ rightRegion)
    start finish hstart hfinish
    (regionalTrackedEdgeGraph_switch_mem_inter
      RS leftRegion rightRegion C a b)

end

end GoertzelV24TerminalProfileConnectivityUpdate

end Mettapedia.GraphTheory.FourColor
