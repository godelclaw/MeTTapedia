import Mettapedia.GraphTheory.FourColor.GoertzelV24MajorityShoreStateDescent
import Mettapedia.GraphTheory.FourColor.GoertzelV24RawWidthSupplyScope

/-!
# The obligation that replaces fixed-mesh exclusion

Fixed ordered-mesh exclusion is not a workable formulation of the high-width
branch of this route.  Every descent mechanism here consumes a decomposition
whose cuts have bounded *complete ambient* interfaces, and
`no_rootedConnectedBranchDecomposition_of_orderedMesh` shows no such
decomposition exists precisely when the mesh is present.  So the exclusion
cannot be obtained from the descent it is meant to enable.

What the route actually needs is an interface statement, and this file states
it exactly and proves that it suffices.

`LongNestedShoreSupply k w N` says: every graph-backed vertex-minimal Tait
counterexample on more than `N` vertices carries a strictly nested chain of
certified shores, all at boundary width `k` and middle width `w`, longer than
the number of phased states available at those widths.  Each node is a
`LiteralShoreNode`, so the interface data is the literal one the physical
splice consumes -- connected shore, connected complement, bounded complete
middle set, cyclic boundary data -- not an abstract width parameter.

`vertexBound_of_longNestedShoreSupply` proves such a supply forces the vertex
bound `N`, because a chain that long contradicts `length_le_of_literalShoreChain`.
Composing with `rawBranchDecompositionSupply_of_vertexBound` reaches the
existing consumer.

The obligation is therefore non-vacuous in the only sense that matters: prove
it and the high-width branch closes.  It is also strictly more accurate than
mesh exclusion, since it names the bounded interface rather than a carrier
whose presence destroys the bound.  Nothing here proves the supply; that is
the open problem, and the bounded interface is the part nothing currently
supplies -- not the mesh, not sphere-cut decompositions, whose width is the
branchwidth itself, and not the Excess Identity.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24BoundedInterfaceObligation

open GoertzelV24MajorityShoreStateDescent
open GoertzelV24RawWidthSupplyScope
open GoertzelV24SphericalReductiveAssembly
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation

noncomputable section

universe u

/-- The number of phased states available at boundary width `k` and middle
width `w`; the length bound of any strictly nested certified chain. -/
def phasedStateBound (k w : Nat) : Nat :=
  (6 * w + 1) *
    (∑ j : Fin (k + 1), Nat.factorial (j : Nat) * 2 ^ (3 ^ (j : Nat)))

/-- **The replacement obligation.**  Above `N` vertices, every graph-backed
vertex-minimal Tait counterexample supplies a strictly nested chain of
certified shores at fixed boundary and middle width, longer than the phased
state count at those widths. -/
def LongNestedShoreSupply (k w N : Nat) : Prop :=
  ∀ {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (rotation : Data G),
    GraphBackedVertexMinimalTaitCounterexample rotation →
      N < Fintype.card V →
        ∃ length : Nat, ∃ nodes : Fin length → LiteralShoreNode rotation k w,
          (∀ i j : Fin length, i < j → (nodes j).shore ⊂ (nodes i).shore) ∧
          phasedStateBound k w < length

/-- The obligation suffices: a chain longer than the phased state count
contradicts the checked length bound, so no counterexample exceeds `N`. -/
theorem vertexBound_of_longNestedShoreSupply (k w N : Nat)
    (supply : LongNestedShoreSupply.{u} k w N)
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (rotation : Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation) :
    Fintype.card V ≤ N := by
  by_contra hlarge
  push_neg at hlarge
  obtain ⟨length, nodes, hstrict, hlong⟩ := supply rotation minimal hlarge
  have hle := length_le_of_literalShoreChain rotation minimal k w length nodes hstrict
  exact absurd hle (by simpa [phasedStateBound] using Nat.not_le_of_lt hlong)

/-- Composed with the existing width supplier, the obligation reaches the
consumer the assembly already uses. -/
theorem rawBranchDecompositionSupply_of_longNestedShoreSupply (k w N : Nat)
    (supply : LongNestedShoreSupply.{u} k w N) :
    RawBranchDecompositionSupply.{u} N :=
  rawBranchDecompositionSupply_of_vertexBound N
    (fun rotation minimal => vertexBound_of_longNestedShoreSupply k w N supply rotation minimal)

end

end GoertzelV24BoundedInterfaceObligation

end Mettapedia.GraphTheory.FourColor
