import Mettapedia.GraphTheory.CubicPathAttachment
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

/-!
# Rotation sides of attachments to a cubic path

At an internal vertex of a simple path in a cubic graph there are three
outgoing darts: backward along the path, forward along the path, and along the
unique attachment edge.  A cyclic vertex rotation has exactly two possible
orders on these darts.  This file records those two orders as a semantic turn
label.

No planarity or noncrossing conclusion is made here.  The turn label is the
local syntax consumed by later separation theorems.
-/

namespace Mettapedia.GraphTheory.FourColor.CubicPathRotation

open SimpleGraph
open Mettapedia.GraphTheory.CubicPathAttachment
open SimpleGraphDartRotation

universe u

variable {V : Type u} {G : SimpleGraph V} {start finish : V}
  [Fintype V] [DecidableEq V] [DecidableRel G.Adj] [G.LocallyFinite]

/-- The dart directed from an internal path vertex to its predecessor. -/
def backwardDart {path : G.Walk start finish}
    (position : InternalPosition path) : G.Dart := by
  have hpositive : 0 < position.index :=
    Nat.pos_of_ne_zero position.index_ne_zero
  have hlt : position.index < path.length := position.index_lt_length
  have hadj := path.adj_getVert_succ
    (i := position.index - 1) (by omega)
  have hindex : position.index - 1 + 1 = position.index := by omega
  exact ⟨(position.vertex, position.previousVertex), by
    simpa only [InternalPosition.vertex, InternalPosition.previousVertex,
      hindex] using hadj.symm⟩

/-- The dart directed from an internal path vertex to its successor. -/
def forwardDart {path : G.Walk start finish}
    (position : InternalPosition path) : G.Dart :=
  ⟨(position.vertex, position.nextVertex), by
    simpa only [InternalPosition.vertex, InternalPosition.nextVertex] using
      path.adj_getVert_succ position.index_lt_length⟩

/-- The dart directed along the unique third edge at an internal path vertex. -/
noncomputable def attachmentDart {path : G.Walk start finish}
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) : G.Dart :=
  ⟨(position.vertex, attachmentNeighbor hpath hregular position),
    attachmentNeighbor_adj hpath hregular position⟩

@[simp] theorem backwardDart_fst {path : G.Walk start finish}
    (position : InternalPosition path) :
    (backwardDart position).fst = position.vertex :=
  rfl

@[simp] theorem backwardDart_snd {path : G.Walk start finish}
    (position : InternalPosition path) :
    (backwardDart position).snd = position.previousVertex :=
  rfl

@[simp] theorem forwardDart_fst {path : G.Walk start finish}
    (position : InternalPosition path) :
    (forwardDart position).fst = position.vertex :=
  rfl

@[simp] theorem forwardDart_snd {path : G.Walk start finish}
    (position : InternalPosition path) :
    (forwardDart position).snd = position.nextVertex :=
  rfl

@[simp] theorem attachmentDart_fst {path : G.Walk start finish}
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    (attachmentDart hpath hregular position).fst = position.vertex :=
  rfl

@[simp] theorem attachmentDart_snd {path : G.Walk start finish}
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    (attachmentDart hpath hregular position).snd =
      attachmentNeighbor hpath hregular position :=
  rfl

/-- The predecessor and successor of an internal position on a simple path are
distinct. -/
theorem previousVertex_ne_nextVertex {path : G.Walk start finish}
    (hpath : path.IsPath) (position : InternalPosition path) :
    position.previousVertex ≠ position.nextVertex := by
  intro heq
  have hpositive : 0 < position.index :=
    Nat.pos_of_ne_zero position.index_ne_zero
  have hlt : position.index < path.length := position.index_lt_length
  change path.getVert (position.index - 1) =
    path.getVert (position.index + 1) at heq
  have hindices := hpath.getVert_injOn
    (by simp only [Set.mem_setOf_eq]; omega)
    (by simp only [Set.mem_setOf_eq]; omega) heq
  omega

theorem backwardDart_ne_forwardDart {path : G.Walk start finish}
    (hpath : path.IsPath) (position : InternalPosition path) :
    backwardDart position ≠ forwardDart position := by
  intro heq
  exact previousVertex_ne_nextVertex hpath position
    (congrArg (fun dart : G.Dart => dart.snd) heq)

theorem backwardDart_ne_attachmentDart {path : G.Walk start finish}
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    backwardDart position ≠ attachmentDart hpath hregular position := by
  intro heq
  exact attachmentNeighbor_ne_previousVertex hpath hregular position
    (congrArg (fun dart : G.Dart => dart.snd) heq).symm

theorem forwardDart_ne_attachmentDart {path : G.Walk start finish}
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    forwardDart position ≠ attachmentDart hpath hregular position := by
  intro heq
  exact attachmentNeighbor_ne_nextVertex hpath hregular position
    (congrArg (fun dart : G.Dart => dart.snd) heq).symm

/-- The two possible cyclic positions of the attachment dart relative to the
oriented path.  The constructor name states which path dart is immediately
followed by the attachment dart. -/
inductive AttachmentTurn where
  | backwardToAttachment
  | forwardToAttachment
  deriving DecidableEq, Repr

/-- The rotation turn of the unique attachment edge at an internal path
position. -/
noncomputable def attachmentTurn (data : Data G)
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) : AttachmentTurn :=
  if data.vertexRotation (backwardDart position) =
      attachmentDart hpath hregular position then
    .backwardToAttachment
  else
    .forwardToAttachment

/-- The rotation of the backward path dart is one of the other two local
darts. -/
theorem vertexRotation_backward_eq_forward_or_attachment
    (data : Data G) (hcyclic : data.IsVertexwiseCyclic)
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    data.vertexRotation (backwardDart position) = forwardDart position ∨
      data.vertexRotation (backwardDart position) =
        attachmentDart hpath hregular position := by
  exact SimpleGraphDartRotation.Data.vertexRotation_apply_eq_second_or_third_of_regularThree
    (G := G) data hregular hcyclic
    (by simp) (by simp)
    (backwardDart_ne_forwardDart hpath position)
    (backwardDart_ne_attachmentDart hpath hregular position)
    (forwardDart_ne_attachmentDart hpath hregular position)

/-- If the attachment follows the backward dart, the complete local rotation
cycle is backward, attachment, forward. -/
theorem rotationCycle_of_attachmentTurn_eq_backwardToAttachment
    (data : Data G) (hcyclic : data.IsVertexwiseCyclic)
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (hturn : attachmentTurn data hpath hregular position =
      .backwardToAttachment) :
    data.vertexRotation (backwardDart position) =
        attachmentDart hpath hregular position ∧
      data.vertexRotation (attachmentDart hpath hregular position) =
        forwardDart position ∧
      data.vertexRotation (forwardDart position) = backwardDart position := by
  have hfirst : data.vertexRotation (backwardDart position) =
      attachmentDart hpath hregular position := by
    by_contra hne
    simp [attachmentTurn, hne] at hturn
  have hcycle := SimpleGraphDartRotation.Data.vertexRotation_three_cycle_of_eq_second
    (G := G) data hregular hcyclic
    (first := backwardDart position)
    (second := attachmentDart hpath hregular position)
    (third := forwardDart position)
    (by simp) (by simp)
    (backwardDart_ne_attachmentDart hpath hregular position)
    (backwardDart_ne_forwardDart hpath position)
    (forwardDart_ne_attachmentDart hpath hregular position).symm
    hfirst
  exact ⟨hfirst, hcycle⟩

/-- If the attachment follows the forward dart, the complete local rotation
cycle is backward, forward, attachment. -/
theorem rotationCycle_of_attachmentTurn_eq_forwardToAttachment
    (data : Data G) (hcyclic : data.IsVertexwiseCyclic)
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path)
    (hturn : attachmentTurn data hpath hregular position =
      .forwardToAttachment) :
    data.vertexRotation (backwardDart position) = forwardDart position ∧
      data.vertexRotation (forwardDart position) =
        attachmentDart hpath hregular position ∧
      data.vertexRotation (attachmentDart hpath hregular position) =
        backwardDart position := by
  have hnotAttachment : data.vertexRotation (backwardDart position) ≠
      attachmentDart hpath hregular position := by
    intro heq
    simp [attachmentTurn, heq] at hturn
  have hfirst : data.vertexRotation (backwardDart position) =
      forwardDart position :=
    (vertexRotation_backward_eq_forward_or_attachment
      data hcyclic hpath hregular position).resolve_right hnotAttachment
  have hcycle := SimpleGraphDartRotation.Data.vertexRotation_three_cycle_of_eq_second
    (G := G) data hregular hcyclic
    (first := backwardDart position)
    (second := forwardDart position)
    (third := attachmentDart hpath hregular position)
    (by simp) (by simp)
    (backwardDart_ne_forwardDart hpath position)
    (backwardDart_ne_attachmentDart hpath hregular position)
    (forwardDart_ne_attachmentDart hpath hregular position)
    hfirst
  exact ⟨hfirst, hcycle⟩

/-- The two turn labels are exhaustive. -/
theorem attachmentTurn_cases (data : Data G)
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (position : InternalPosition path) :
    attachmentTurn data hpath hregular position = .backwardToAttachment ∨
      attachmentTurn data hpath hregular position = .forwardToAttachment := by
  cases attachmentTurn data hpath hregular position <;> simp

end Mettapedia.GraphTheory.FourColor.CubicPathRotation
