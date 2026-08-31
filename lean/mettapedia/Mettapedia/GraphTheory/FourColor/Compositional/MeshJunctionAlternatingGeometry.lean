import Mettapedia.GraphTheory.FourColor.Compositional.ResidualSiteProvenance

/-!
# Alternating geometry at internal mesh junctions

At an internal branch position of a simple mesh row, the incoming and
outgoing path steps have distinct outer endpoints and share the branch
vertex.  A perfect matching can use at most one of those two steps.  Hence a
single residual-defect minimizer is noncentral on at least one arm, where the
globally selected deletion colouring supplies a proper alternating component.

This is the first use of the two-sided local geometry of a mesh path in the
residual-defect route.  It requires neither a transverse row--column crossing
nor compatibility between the deletion colourings at different steps.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.MeshJunctionAlternatingGeometry

open Compositional.ResidualSiteProvenance
open GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24ResidualDefectDescent
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open MatchingParity
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a b : Nat}

variable
  (rotation : Data G)
  (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
  (ordered : OrderedInjectiveMesh
    (toMultigraph rotation.toRotationSystem) a (b + 2))

/-- The non-boundary column indexed by `column`, shifted past the first
column of the ordered mesh. -/
def internalColumn (column : Fin b) : Fin (b + 2) :=
  ⟨column.val + 1, by omega⟩

/-- The position of an internal branch vertex on its ordered row. -/
def internalRowPosition (row : Fin a) (column : Fin b) :
    Fin ((ordered.toMesh.row row).len + 1) :=
  ordered.rowBranchPosition row (internalColumn column)

/-- An internal branch position has a preceding row step. -/
theorem internalRowPosition_pos (row : Fin a) (column : Fin b) :
    0 < (internalRowPosition rotation ordered row column).val := by
  let previous : Fin (b + 2) := ⟨column.val, by omega⟩
  have hprevious : previous < internalColumn column := by
    simp [previous, internalColumn]
  have hstrict := ordered.rowBranchPosition_strictMono row hprevious
  change
    (ordered.rowBranchPosition row previous).val <
      (internalRowPosition rotation ordered row column).val at hstrict
  exact lt_of_le_of_lt (Nat.zero_le _) hstrict

/-- An internal branch position has a following row step. -/
theorem internalRowPosition_lt_len (row : Fin a) (column : Fin b) :
    (internalRowPosition rotation ordered row column).val <
      (ordered.toMesh.row row).len := by
  let following : Fin (b + 2) := ⟨column.val + 2, by omega⟩
  have hfollowing : internalColumn column < following := by
    simp [internalColumn, following]
  have hstrict := ordered.rowBranchPosition_strictMono row hfollowing
  have hbound := (ordered.rowBranchPosition row following).isLt
  change
    (internalRowPosition rotation ordered row column).val <
      (ordered.rowBranchPosition row following).val at hstrict
  change
    (ordered.rowBranchPosition row following).val <
      (ordered.toMesh.row row).len + 1 at hbound
  omega

/-- The row step immediately before an internal branch vertex. -/
def incomingRowStep (row : Fin a) (column : Fin b) :
    Fin ((ordered.toMesh.row row).len) := by
  let position := internalRowPosition rotation ordered row column
  exact ⟨position.val - 1, by
    have hposition := position.isLt
    have hpositive := internalRowPosition_pos rotation ordered row column
    omega⟩

/-- The row step immediately after an internal branch vertex. -/
def outgoingRowStep (row : Fin a) (column : Fin b) :
    Fin ((ordered.toMesh.row row).len) := by
  let position := internalRowPosition rotation ordered row column
  exact ⟨position.val,
    internalRowPosition_lt_len rotation ordered row column⟩

/-- The incoming globally indexed row site at an internal branch. -/
def incomingGlobalStep (row : Fin a) (column : Fin b) :
    GlobalMeshStep rotation ordered :=
  .inl ⟨row, incomingRowStep rotation ordered row column⟩

/-- The outgoing globally indexed row site at an internal branch. -/
def outgoingGlobalStep (row : Fin a) (column : Fin b) :
    GlobalMeshStep rotation ordered :=
  .inl ⟨row, outgoingRowStep rotation ordered row column⟩

/-- The incoming step ends at the designated branch vertex. -/
theorem incomingGlobalStep_second_eq_branch
    (row : Fin a) (column : Fin b) :
    globalSecondVertex rotation ordered
        (incomingGlobalStep rotation ordered row column) =
      ordered.toMesh.branch row (internalColumn column) := by
  rw [← ordered.rowBranchPosition_spec row (internalColumn column)]
  apply congrArg (ordered.toMesh.row row).vert
  apply Fin.ext
  change
    (internalRowPosition rotation ordered row column).val - 1 + 1 =
      (internalRowPosition rotation ordered row column).val
  have hpositive := internalRowPosition_pos rotation ordered row column
  omega

/-- The outgoing step begins at the designated branch vertex. -/
theorem outgoingGlobalStep_first_eq_branch
    (row : Fin a) (column : Fin b) :
    globalFirstVertex rotation ordered
        (outgoingGlobalStep rotation ordered row column) =
      ordered.toMesh.branch row (internalColumn column) := by
  rw [← ordered.rowBranchPosition_spec row (internalColumn column)]
  apply congrArg (ordered.toMesh.row row).vert
  apply Fin.ext
  change
    (internalRowPosition rotation ordered row column).val =
      (ordered.rowBranchPosition row (internalColumn column)).val
  rfl

/-- The outer endpoints of the incoming and outgoing row steps are distinct.
This is the exact simple-path fact needed to rule out centrality on both
arms. -/
theorem incoming_first_ne_outgoing_second
    (row : Fin a) (column : Fin b) :
    globalFirstVertex rotation ordered
        (incomingGlobalStep rotation ordered row column) ≠
      globalSecondVertex rotation ordered
        (outgoingGlobalStep rotation ordered row column) := by
  intro heq
  have hindex := ordered.rowVertexInjective row heq
  have hval := congrArg Fin.val hindex
  change
    (internalRowPosition rotation ordered row column).val - 1 =
      (internalRowPosition rotation ordered row column).val + 1 at hval
  have hpositive := internalRowPosition_pos rotation ordered row column
  omega

/-- One common residual-defect minimizer has a provenanced proper
alternating component on at least one arm of every internal row junction.

The conclusion is deliberately disjunctive: no compatibility between the
two independently selected deletion colourings is assumed. -/
theorem exists_minimizer_with_proper_site_at_every_internal_row_junction :
    ∃ sigma : Pairing V,
      sigma.SupportedBy G ∧
      2 ≤ residualDefect G sigma ∧
      ∀ (row : Fin a) (column : Fin b),
        Nonempty (ProvenancedAlternatingSiteReceipt
          rotation minimal ordered sigma
          (incomingGlobalStep rotation ordered row column)) ∨
        Nonempty (ProvenancedAlternatingSiteReceipt
          rotation minimal ordered sigma
          (outgoingGlobalStep rotation ordered row column)) := by
  obtain ⟨sigma, hSigma, hdefect, hsite⟩ :=
    exists_exchangeRigid_with_provenanced_alternatingSite_at_every_globalMeshStep
      rotation minimal ordered
  refine ⟨sigma, hSigma, hdefect, ?_⟩
  intro row column
  rcases hsite (incomingGlobalStep rotation ordered row column) with
      hIncomingCentral | hIncomingProper
  · rcases hsite (outgoingGlobalStep rotation ordered row column) with
        hOutgoingCentral | hOutgoingProper
    · exfalso
      have hAtBranchFromIncoming :
          sigma.partner (ordered.toMesh.branch row (internalColumn column)) =
            globalFirstVertex rotation ordered
              (incomingGlobalStep rotation ordered row column) := by
        rw [← incomingGlobalStep_second_eq_branch
          rotation ordered row column, ← hIncomingCentral,
          sigma.partner_partner]
      have hAtBranchFromOutgoing :
          sigma.partner (ordered.toMesh.branch row (internalColumn column)) =
            globalSecondVertex rotation ordered
              (outgoingGlobalStep rotation ordered row column) := by
        rw [← outgoingGlobalStep_first_eq_branch
          rotation ordered row column]
        exact hOutgoingCentral
      exact incoming_first_ne_outgoing_second rotation ordered row column
        (hAtBranchFromIncoming.symm.trans hAtBranchFromOutgoing)
    · exact Or.inr hOutgoingProper
  · exact Or.inl hIncomingProper

end

end Mettapedia.GraphTheory.FourColor.Compositional.MeshJunctionAlternatingGeometry
