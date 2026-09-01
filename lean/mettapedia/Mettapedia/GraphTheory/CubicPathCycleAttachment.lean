import Mettapedia.GraphTheory.CubicPathAttachment
import Mettapedia.GraphTheory.PathChord

/-!
# Third-edge attachments relative to a path-cycle closure

A cubic path position has one incident edge outside the two path edges.  If
the path is one arc of a simple cycle, an attachment leaving the path has two
geometrically different destinations: it can meet the complementary arc of
the same cycle, or it can leave the entire cycle.

This file records that intrinsic trichotomy.  It is graph-theoretic and does
not depend on a planar embedding, a colouring, or the four-colour route.
-/

namespace Mettapedia.GraphTheory.CubicPathAttachment

open SimpleGraph

universe u

variable {V : Type u} {G : SimpleGraph V} {start finish : V}
  [G.LocallyFinite]

/-- A third edge leaves the distinguished path and reaches the complementary
arc of its simple-cycle closure. -/
def IsComplementAttachment
    {path : G.Walk start finish} (closure : PathCycleClosure path)
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) : Prop :=
  IsExternalAttachment hpath hregular position ∧
    attachmentNeighbor hpath hregular position ∈ closure.complement.support

/-- A third edge leaves the whole simple cycle containing the distinguished
path arc. -/
def IsCycleExteriorAttachment
    {path : G.Walk start finish} (closure : PathCycleClosure path)
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) : Prop :=
  attachmentNeighbor hpath hregular position ∉
    (path.append closure.complement).support

/-- An attachment exterior to the whole cycle is exterior to the selected
path in particular. -/
theorem IsCycleExteriorAttachment.isExternalAttachment
    {path : G.Walk start finish} (closure : PathCycleClosure path)
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (hexterior : IsCycleExteriorAttachment closure hpath hregular position) :
    IsExternalAttachment hpath hregular position := by
  intro hpathSupport
  apply hexterior
  rw [SimpleGraph.Walk.mem_support_append_iff]
  exact Or.inl hpathSupport

/-- **External-attachment partition.**  Relative to a simple-cycle closure,
leaving the distinguished path means exactly reaching only the complementary
arc or leaving the complete cycle. -/
theorem isExternalAttachment_iff_complement_or_cycleExterior
    {path : G.Walk start finish} (closure : PathCycleClosure path)
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    IsExternalAttachment hpath hregular position ↔
      IsComplementAttachment closure hpath hregular position ∨
        IsCycleExteriorAttachment closure hpath hregular position := by
  constructor
  · intro hexternal
    by_cases hcomplement : attachmentNeighbor hpath hregular position ∈
        closure.complement.support
    · exact Or.inl ⟨hexternal, hcomplement⟩
    · right
      rw [IsCycleExteriorAttachment,
        SimpleGraph.Walk.mem_support_append_iff]
      push Not
      exact ⟨hexternal, hcomplement⟩
  · rintro (hcomplement | hexterior)
    · exact hcomplement.1
    · exact hexterior.isExternalAttachment closure hpath hregular position

/-- The third edge at a cubic path position either returns to the selected
path, reaches only the complementary cycle arc, or exits the complete cycle.
-/
theorem chordAttachment_or_complementAttachment_or_cycleExterior
    {path : G.Walk start finish} (closure : PathCycleClosure path)
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    Nonempty (ChordAttachment hpath hregular position) ∨
      IsComplementAttachment closure hpath hregular position ∨
        IsCycleExteriorAttachment closure hpath hregular position := by
  rcases chordAttachment_or_externalAttachment hpath hregular position with
    hchord | hexternal
  · exact Or.inl hchord
  · exact Or.inr <|
      (isExternalAttachment_iff_complement_or_cycleExterior
        closure hpath hregular position).mp hexternal

/-- A genuinely exterior attachment edge is not an edge of the closing
cycle. -/
theorem attachmentEdge_not_mem_cycle_edges_of_cycleExterior
    {path : G.Walk start finish} (closure : PathCycleClosure path)
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (hexterior : IsCycleExteriorAttachment closure hpath hregular position) :
    (attachmentEdge hpath hregular position).1 ∉
      (path.append closure.complement).edges := by
  intro hedge
  apply hexterior
  exact (path.append closure.complement).snd_mem_support_of_mem_edges hedge

end Mettapedia.GraphTheory.CubicPathAttachment
