import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshBoundaryWalk

/-!
# Globally shared adjacent-pair sites on an ordered mesh

A cell-local boundary tag is not a global composition key: two neighbouring
coordinate rectangles traverse their common side with opposite orientations.
This file indexes every row and column path step of one ordered mesh once,
then chooses its adjacent-pair Kempe site once.

Every complete cell-boundary step maps to this carrier.  The mapped global
site deletes exactly the same unordered pair of ambient vertices as the
clockwise local site, including the reversed south and west sides.  Thus later
two-dimensional transport can share a physical deletion object across cells
without making unrelated local choices.  No embedded-cell, flatness, or
wall-exclusion conclusion is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedMeshGlobalSites

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshAdjacentPairSites
open GoertzelV24OrderedMeshBoundaryWalk
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
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
    (toMultigraph rotation.toRotationSystem) a b)

/-- Every literal path-step occurrence of the ordered mesh, tagged by its row
or column family.  The tags remain distinct even when a row and a column use
the same ambient multigraph edge. -/
abbrev GlobalMeshStep :=
  (Σ row : Fin a, Fin ((ordered.toMesh.row row).len)) ⊕
    (Σ col : Fin b, Fin ((ordered.toMesh.col col).len))

/-- The forward first endpoint of a globally indexed mesh step. -/
def globalFirstVertex : GlobalMeshStep rotation ordered → V
  | .inl rowStep =>
      (ordered.toMesh.row rowStep.1).vert rowStep.2.castSucc
  | .inr colStep =>
      (ordered.toMesh.col colStep.1).vert colStep.2.castSucc

/-- The forward second endpoint of a globally indexed mesh step. -/
def globalSecondVertex : GlobalMeshStep rotation ordered → V
  | .inl rowStep =>
      (ordered.toMesh.row rowStep.1).vert rowStep.2.succ
  | .inr colStep =>
      (ordered.toMesh.col colStep.1).vert colStep.2.succ

/-- The ambient graph edge represented by a global mesh step. -/
def globalEdge : GlobalMeshStep rotation ordered →
    G.edgeSet
  | .inl rowStep => (ordered.toMesh.row rowStep.1).edge rowStep.2
  | .inr colStep => (ordered.toMesh.col colStep.1).edge colStep.2

/-- Canonical forward adjacent-pair data at a global path step. -/
def globalAdjacentPairData :
    GlobalMeshStep rotation ordered → AdjacentPairData G
  | .inl rowStep =>
      adjacentPairDataAtStep rotation minimal
        (ordered.toMesh.row rowStep.1) rowStep.2
  | .inr colStep =>
      adjacentPairDataAtStep rotation minimal
        (ordered.toMesh.col colStep.1) colStep.2

@[simp] theorem globalAdjacentPairData_firstVertex (step) :
    (globalAdjacentPairData rotation minimal ordered step).firstVertex =
      globalFirstVertex rotation ordered step := by
  cases step <;> rfl

@[simp] theorem globalAdjacentPairData_secondVertex (step) :
    (globalAdjacentPairData rotation minimal ordered step).secondVertex =
      globalSecondVertex rotation ordered step := by
  cases step <;> rfl

/-- The physical unordered pair deleted at a global mesh step. -/
def globalEndpointPair (step : GlobalMeshStep rotation ordered) : Finset V :=
  {globalFirstVertex rotation ordered step,
    globalSecondVertex rotation ordered step}

variable (cell : CellIndex a b)

/-- Forget a cell-local side tag and orientation, retaining the literal
global row/column path-step occurrence. -/
def boundaryToGlobalStep :
    CellBoundaryStep rotation ordered cell → GlobalMeshStep rotation ordered
  | .north position =>
      .inl ⟨cell.topRow, northPathStep rotation ordered cell position⟩
  | .east position =>
      .inr ⟨cell.rightCol, eastPathStep rotation ordered cell position⟩
  | .south position =>
      .inl ⟨cell.bottomRow, southPathStep rotation ordered cell position⟩
  | .west position =>
      .inr ⟨cell.leftCol, westPathStep rotation ordered cell position⟩

/-- Mapping a boundary step to the global mesh carrier forgets only
orientation: the unordered deleted endpoint pair is unchanged. -/
theorem globalEndpointPair_boundaryToGlobalStep
    (step : CellBoundaryStep rotation ordered cell) :
    globalEndpointPair rotation ordered
        (boundaryToGlobalStep rotation ordered cell step) =
      { (boundaryData rotation minimal ordered cell step).firstVertex,
        (boundaryData rotation minimal ordered cell step).secondVertex } := by
  cases step <;>
    simp [globalEndpointPair, boundaryToGlobalStep, globalFirstVertex,
      globalSecondVertex, boundaryData,
      adjacentPairDataAtStep, adjacentPairDataAtStepReverse,
      GoertzelV24RecoveredAdjacentPairData.adjacentPairData,
      Finset.pair_comm]

/-- Distinct boundary occurrences of one coordinate rectangle remain
distinct in the global row/column step carrier. -/
theorem boundaryToGlobalStep_injective :
    Function.Injective (boundaryToGlobalStep rotation ordered cell) := by
  intro source target heq
  cases source with
  | north source =>
      cases target with
      | north target =>
          have hsigma := Sum.inl.inj heq
          have hval := congrArg
            (fun step : Σ row : Fin a,
              Fin ((ordered.toMesh.row row).len) => step.2.val) hsigma
          apply congrArg CellBoundaryStep.north
          apply Fin.ext
          simp [northPathStep] at hval ⊢
          omega
      | east target => simp [boundaryToGlobalStep] at heq
      | south target =>
          have hsigma := Sum.inl.inj heq
          have hrow := congrArg
            (fun step : Σ row : Fin a,
              Fin ((ordered.toMesh.row row).len) => step.1) hsigma
          exact (cell.topRow_lt_bottomRow.ne hrow).elim
      | west target => simp [boundaryToGlobalStep] at heq
  | east source =>
      cases target with
      | north target => simp [boundaryToGlobalStep] at heq
      | east target =>
          have hsigma := Sum.inr.inj heq
          have hval := congrArg
            (fun step : Σ col : Fin b,
              Fin ((ordered.toMesh.col col).len) => step.2.val) hsigma
          apply congrArg CellBoundaryStep.east
          apply Fin.ext
          simp [eastPathStep] at hval ⊢
          omega
      | south target => simp [boundaryToGlobalStep] at heq
      | west target =>
          have hsigma := Sum.inr.inj heq
          have hcol := congrArg
            (fun step : Σ col : Fin b,
              Fin ((ordered.toMesh.col col).len) => step.1) hsigma
          exact (cell.leftCol_lt_rightCol.ne hcol.symm).elim
  | south source =>
      cases target with
      | north target =>
          have hsigma := Sum.inl.inj heq
          have hrow := congrArg
            (fun step : Σ row : Fin a,
              Fin ((ordered.toMesh.row row).len) => step.1) hsigma
          exact (cell.topRow_lt_bottomRow.ne hrow.symm).elim
      | east target => simp [boundaryToGlobalStep] at heq
      | south target =>
          have hsigma := Sum.inl.inj heq
          have hval := congrArg
            (fun step : Σ row : Fin a,
              Fin ((ordered.toMesh.row row).len) => step.2.val) hsigma
          have hsource_lt : source.val <
              (ordered.rowBranchPosition cell.bottomRow cell.rightCol).val := by
            have hsource := source.isLt
            dsimp [southLength] at hsource
            omega
          have htarget_lt : target.val <
              (ordered.rowBranchPosition cell.bottomRow cell.rightCol).val := by
            have htarget := target.isLt
            dsimp [southLength] at htarget
            omega
          apply congrArg CellBoundaryStep.south
          apply Fin.ext
          simp only [southPathStep] at hval
          omega
      | west target => simp [boundaryToGlobalStep] at heq
  | west source =>
      cases target with
      | north target => simp [boundaryToGlobalStep] at heq
      | east target =>
          have hsigma := Sum.inr.inj heq
          have hcol := congrArg
            (fun step : Σ col : Fin b,
              Fin ((ordered.toMesh.col col).len) => step.1) hsigma
          exact (cell.leftCol_lt_rightCol.ne hcol).elim
      | south target => simp [boundaryToGlobalStep] at heq
      | west target =>
          have hsigma := Sum.inr.inj heq
          have hval := congrArg
            (fun step : Σ col : Fin b,
              Fin ((ordered.toMesh.col col).len) => step.2.val) hsigma
          have hsource_lt : source.val <
              (ordered.colBranchPosition cell.bottomRow cell.leftCol).val := by
            have hsource := source.isLt
            dsimp [westLength] at hsource
            omega
          have htarget_lt : target.val <
              (ordered.colBranchPosition cell.bottomRow cell.leftCol).val := by
            have htarget := target.isLt
            dsimp [westLength] at htarget
            omega
          apply congrArg CellBoundaryStep.west
          apply Fin.ext
          simp only [westPathStep] at hval
          omega

/-! ## One globally coherent orbit choice per mesh step -/

/-- One adjacent-pair Kempe orbit selected at a globally indexed mesh step. -/
structure GlobalKempeSite
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (step : GlobalMeshStep rotation ordered) where
  data : AdjacentPairData G
  first_eq : data.firstVertex = globalFirstVertex rotation ordered step
  second_eq : data.secondVertex = globalSecondVertex rotation ordered step
  base : (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).EdgeColoring Color
  baseTait :
    IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) base

/-- Minimality supplies a site at every global row/column step. -/
theorem nonempty_globalKempeSite
    (step : GlobalMeshStep rotation ordered) :
    Nonempty (GlobalKempeSite rotation ordered minimal step) := by
  rcases (globalAdjacentPairData rotation minimal ordered step).exists_rotationOrdered_commonKempeOrbit_with_all_constantWords_of_minimal
      rotation minimal with
    ⟨data, hfirst, hsecond, base, hbase, _⟩
  exact ⟨{
    data := data
    first_eq := hfirst.trans
      (globalAdjacentPairData_firstVertex rotation minimal ordered step)
    second_eq := hsecond.trans
      (globalAdjacentPairData_secondVertex rotation minimal ordered step)
    base := base
    baseTait := hbase }⟩

/-- The choice is made once on the global mesh-step carrier, so every cell
using that occurrence receives definitionally the same data and base. -/
noncomputable def selectedGlobalKempeSite
    (step : GlobalMeshStep rotation ordered) :
    GlobalKempeSite rotation ordered minimal step :=
  Classical.choice (nonempty_globalKempeSite
    rotation minimal ordered step)

/-- The globally selected site used by a cell boundary deletes the same
physical unordered pair as the cell-local clockwise data. -/
theorem selectedGlobalKempeSite_boundary_endpointPair
    (step : CellBoundaryStep rotation ordered cell) :
    ({ (selectedGlobalKempeSite rotation minimal ordered
          (boundaryToGlobalStep rotation ordered cell step)).data.firstVertex,
        (selectedGlobalKempeSite rotation minimal ordered
          (boundaryToGlobalStep rotation ordered cell step)).data.secondVertex } :
        Finset V) =
      { (boundaryData rotation minimal ordered cell step).firstVertex,
        (boundaryData rotation minimal ordered cell step).secondVertex } := by
  rw [(selectedGlobalKempeSite rotation minimal ordered
      (boundaryToGlobalStep rotation ordered cell step)).first_eq,
    (selectedGlobalKempeSite rotation minimal ordered
      (boundaryToGlobalStep rotation ordered cell step)).second_eq]
  exact globalEndpointPair_boundaryToGlobalStep
    rotation minimal ordered cell step

end

end GoertzelV24OrderedMeshGlobalSites

end Mettapedia.GraphTheory.FourColor
