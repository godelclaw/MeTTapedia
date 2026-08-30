import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshAdjacentPairSites

/-!
# The complete adjacent-pair boundary walk of an ordered mesh rectangle

The four-corner mesh adapter selects only one path step at each branch
vertex.  A subdivided wall may have arbitrarily many path steps between two
successive branch vertices.  This file records every such step, oriented
clockwise around one coordinate rectangle.

No topological-cell assertion is made.  Rows and columns may have additional
intersections or shared segments, exactly as permitted by `OrderedInjectiveMesh`.
The result is purely an incidence carrier: a finite cyclic successor system
of adjacent-pair deletions.  Consecutive sites share their boundary vertex,
and hence compare on the canonical common induced graph obtained by deleting
their (at most) three endpoint vertices.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedMeshBoundaryWalk

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshAdjacentPairSites
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
  (cell : CellIndex a b)

/-! ## The four subdivided side lengths -/

def northLength : Nat :=
  (ordered.rowBranchPosition cell.topRow cell.rightCol).val -
    (ordered.rowBranchPosition cell.topRow cell.leftCol).val

def eastLength : Nat :=
  (ordered.colBranchPosition cell.bottomRow cell.rightCol).val -
    (ordered.colBranchPosition cell.topRow cell.rightCol).val

def southLength : Nat :=
  (ordered.rowBranchPosition cell.bottomRow cell.rightCol).val -
    (ordered.rowBranchPosition cell.bottomRow cell.leftCol).val

def westLength : Nat :=
  (ordered.colBranchPosition cell.bottomRow cell.leftCol).val -
    (ordered.colBranchPosition cell.topRow cell.leftCol).val

theorem northLength_pos : 0 < northLength rotation ordered cell := by
  dsimp [northLength]
  exact Nat.sub_pos_of_lt
    (ordered.rowBranchPosition_strictMono cell.topRow
      cell.leftCol_lt_rightCol)

theorem eastLength_pos : 0 < eastLength rotation ordered cell := by
  dsimp [eastLength]
  exact Nat.sub_pos_of_lt
    (ordered.colBranchPosition_strictMono cell.rightCol
      cell.topRow_lt_bottomRow)

theorem southLength_pos : 0 < southLength rotation ordered cell := by
  dsimp [southLength]
  exact Nat.sub_pos_of_lt
    (ordered.rowBranchPosition_strictMono cell.bottomRow
      cell.leftCol_lt_rightCol)

theorem westLength_pos : 0 < westLength rotation ordered cell := by
  dsimp [westLength]
  exact Nat.sub_pos_of_lt
    (ordered.colBranchPosition_strictMono cell.leftCol
      cell.topRow_lt_bottomRow)

/-! ## Every oriented path step -/

/-- A north-side position, read from west to east, as a step of its row. -/
def northPathStep (position : Fin (northLength rotation ordered cell)) :
    Fin ((ordered.toMesh.row cell.topRow).len) :=
  ⟨(ordered.rowBranchPosition cell.topRow cell.leftCol).val + position.val, by
    have hposition := position.isLt
    have hright :=
      (ordered.rowBranchPosition cell.topRow cell.rightCol).isLt
    dsimp [northLength] at hposition
    omega⟩

/-- An east-side position, read from north to south, as a step of its column. -/
def eastPathStep (position : Fin (eastLength rotation ordered cell)) :
    Fin ((ordered.toMesh.col cell.rightCol).len) :=
  ⟨(ordered.colBranchPosition cell.topRow cell.rightCol).val + position.val, by
    have hposition := position.isLt
    have hbottom :=
      (ordered.colBranchPosition cell.bottomRow cell.rightCol).isLt
    dsimp [eastLength] at hposition
    omega⟩

/-- A south-side position, read from east to west, as a step of its row. -/
def southPathStep (position : Fin (southLength rotation ordered cell)) :
    Fin ((ordered.toMesh.row cell.bottomRow).len) :=
  ⟨(ordered.rowBranchPosition cell.bottomRow cell.rightCol).val - 1 -
      position.val, by
    have hposition := position.isLt
    have hright :=
      (ordered.rowBranchPosition cell.bottomRow cell.rightCol).isLt
    have hstrict := ordered.rowBranchPosition_strictMono cell.bottomRow
      cell.leftCol_lt_rightCol
    dsimp [southLength] at hposition
    omega⟩

/-- A west-side position, read from south to north, as a step of its column. -/
def westPathStep (position : Fin (westLength rotation ordered cell)) :
    Fin ((ordered.toMesh.col cell.leftCol).len) :=
  ⟨(ordered.colBranchPosition cell.bottomRow cell.leftCol).val - 1 -
      position.val, by
    have hposition := position.isLt
    have hbottom :=
      (ordered.colBranchPosition cell.bottomRow cell.leftCol).isLt
    have hstrict := ordered.colBranchPosition_strictMono cell.leftCol
      cell.topRow_lt_bottomRow
    dsimp [westLength] at hposition
    omega⟩

/-- Every path step encountered clockwise around the coordinate rectangle.
The four constructors are disjoint even when different ambient mesh paths
share an edge. -/
inductive CellBoundaryStep : Type
  | north : Fin (northLength rotation ordered cell) → CellBoundaryStep
  | east : Fin (eastLength rotation ordered cell) → CellBoundaryStep
  | south : Fin (southLength rotation ordered cell) → CellBoundaryStep
  | west : Fin (westLength rotation ordered cell) → CellBoundaryStep

noncomputable instance cellBoundaryStepDecidableEq :
    DecidableEq (CellBoundaryStep rotation ordered cell) :=
  Classical.decEq _

/-- The complete clockwise enumeration, including every subdivision step. -/
def boundaryWalk : List (CellBoundaryStep rotation ordered cell) :=
  List.ofFn (fun position => CellBoundaryStep.north position) ++
    List.ofFn (fun position => CellBoundaryStep.east position) ++
    List.ofFn (fun position => CellBoundaryStep.south position) ++
    List.ofFn (fun position => CellBoundaryStep.west position)

theorem boundaryWalk_length :
    (boundaryWalk rotation ordered cell).length =
      northLength rotation ordered cell + eastLength rotation ordered cell +
        southLength rotation ordered cell + westLength rotation ordered cell := by
  simp [boundaryWalk, Nat.add_assoc]

theorem mem_boundaryWalk (step : CellBoundaryStep rotation ordered cell) :
    step ∈ boundaryWalk rotation ordered cell := by
  cases step <;> simp [boundaryWalk]

theorem boundaryWalk_nodup :
    (boundaryWalk rotation ordered cell).Nodup := by
  simp [boundaryWalk, List.nodup_append', List.nodup_ofFn,
    List.disjoint_left, Function.Injective]

noncomputable instance cellBoundaryStepFintype :
    Fintype (CellBoundaryStep rotation ordered cell) :=
  Fintype.ofList (boundaryWalk rotation ordered cell)
    (mem_boundaryWalk rotation ordered cell)

theorem boundaryWalk_toFinset_eq_univ :
    (boundaryWalk rotation ordered cell).toFinset = Finset.univ := by
  ext step
  simp [mem_boundaryWalk]

/-- The canonical adjacent-pair deletion at every oriented boundary step. -/
def boundaryData : CellBoundaryStep rotation ordered cell → AdjacentPairData G
  | .north position =>
      adjacentPairDataAtStep rotation minimal
        (ordered.toMesh.row cell.topRow)
        (northPathStep rotation ordered cell position)
  | .east position =>
      adjacentPairDataAtStep rotation minimal
        (ordered.toMesh.col cell.rightCol)
        (eastPathStep rotation ordered cell position)
  | .south position =>
      adjacentPairDataAtStepReverse rotation minimal
        (ordered.toMesh.row cell.bottomRow)
        (southPathStep rotation ordered cell position)
  | .west position =>
      adjacentPairDataAtStepReverse rotation minimal
        (ordered.toMesh.col cell.leftCol)
        (westPathStep rotation ordered cell position)

@[simp] theorem boundaryData_north_first (position) :
    (boundaryData rotation minimal ordered cell (.north position)).firstVertex =
      (ordered.toMesh.row cell.topRow).vert
        (northPathStep rotation ordered cell position).castSucc := rfl

@[simp] theorem boundaryData_north_second (position) :
    (boundaryData rotation minimal ordered cell (.north position)).secondVertex =
      (ordered.toMesh.row cell.topRow).vert
        (northPathStep rotation ordered cell position).succ := rfl

@[simp] theorem boundaryData_east_first (position) :
    (boundaryData rotation minimal ordered cell (.east position)).firstVertex =
      (ordered.toMesh.col cell.rightCol).vert
        (eastPathStep rotation ordered cell position).castSucc := rfl

@[simp] theorem boundaryData_east_second (position) :
    (boundaryData rotation minimal ordered cell (.east position)).secondVertex =
      (ordered.toMesh.col cell.rightCol).vert
        (eastPathStep rotation ordered cell position).succ := rfl

@[simp] theorem boundaryData_south_first (position) :
    (boundaryData rotation minimal ordered cell (.south position)).firstVertex =
      (ordered.toMesh.row cell.bottomRow).vert
        (southPathStep rotation ordered cell position).succ := rfl

@[simp] theorem boundaryData_south_second (position) :
    (boundaryData rotation minimal ordered cell (.south position)).secondVertex =
      (ordered.toMesh.row cell.bottomRow).vert
        (southPathStep rotation ordered cell position).castSucc := rfl

@[simp] theorem boundaryData_west_first (position) :
    (boundaryData rotation minimal ordered cell (.west position)).firstVertex =
      (ordered.toMesh.col cell.leftCol).vert
        (westPathStep rotation ordered cell position).succ := rfl

@[simp] theorem boundaryData_west_second (position) :
    (boundaryData rotation minimal ordered cell (.west position)).secondVertex =
      (ordered.toMesh.col cell.leftCol).vert
        (westPathStep rotation ordered cell position).castSucc := rfl

/-! ## The exact cyclic incidence relation -/

/-- The next clockwise boundary step.  At the end of a side this turns onto
the first step of the next side. -/
def boundarySuccessor :
    CellBoundaryStep rotation ordered cell → CellBoundaryStep rotation ordered cell
  | .north position =>
      if h : position.val + 1 < northLength rotation ordered cell then
        .north ⟨position.val + 1, h⟩
      else
        .east ⟨0, eastLength_pos rotation ordered cell⟩
  | .east position =>
      if h : position.val + 1 < eastLength rotation ordered cell then
        .east ⟨position.val + 1, h⟩
      else
        .south ⟨0, southLength_pos rotation ordered cell⟩
  | .south position =>
      if h : position.val + 1 < southLength rotation ordered cell then
        .south ⟨position.val + 1, h⟩
      else
        .west ⟨0, westLength_pos rotation ordered cell⟩
  | .west position =>
      if h : position.val + 1 < westLength rotation ordered cell then
        .west ⟨position.val + 1, h⟩
      else
        .north ⟨0, northLength_pos rotation ordered cell⟩

/-- Exact consecutive-site incidence is the graph of the clockwise
successor. -/
def AreBoundaryConsecutive
    (source target : CellBoundaryStep rotation ordered cell) : Prop :=
  boundarySuccessor rotation ordered cell source = target

/-- The clockwise successor is a genuine permutation of the complete step
carrier, rather than merely a partial next-step operation. -/
theorem boundarySuccessor_injective :
    Function.Injective (boundarySuccessor rotation ordered cell) := by
  intro source target heq
  cases source <;> cases target <;>
    simp only [boundarySuccessor] at heq ⊢ <;>
    split_ifs at heq <;> simp_all
  all_goals (apply Fin.ext; omega)

/-- The cyclic successor packaged as an equivalence for later relational
transport and monodromy consumers. -/
noncomputable def boundarySuccessorEquiv :
    CellBoundaryStep rotation ordered cell ≃
      CellBoundaryStep rotation ordered cell :=
  Equiv.ofBijective (boundarySuccessor rotation ordered cell)
    ⟨boundarySuccessor_injective rotation ordered cell,
      Finite.surjective_of_injective
        (boundarySuccessor_injective rotation ordered cell)⟩

theorem boundarySuccessor_unique
    (source target first : CellBoundaryStep rotation ordered cell)
    (htarget : AreBoundaryConsecutive rotation ordered cell source target)
    (hfirst : AreBoundaryConsecutive rotation ordered cell source first) :
    target = first := by
  exact htarget.symm.trans hfirst

/-- Consecutive oriented sites share literally the terminal vertex of the
first site as the initial vertex of the second.  The four turn cases use only
the recorded branch-position equations; no embedded-cell claim enters. -/
theorem boundaryData_second_eq_successor_first
    (step : CellBoundaryStep rotation ordered cell) :
    (boundaryData rotation minimal ordered cell step).secondVertex =
      (boundaryData rotation minimal ordered cell
        (boundarySuccessor rotation ordered cell step)).firstVertex := by
  cases step with
  | north position =>
      simp only [boundarySuccessor]
      split_ifs with h
      · simp only [boundaryData_north_second, boundaryData_north_first]
        apply congrArg (ordered.toMesh.row cell.topRow).vert
        apply Fin.ext
        simp [northPathStep, Nat.add_assoc]
      · simp only [boundaryData_north_second, boundaryData_east_first]
        have hlast : position.val + 1 = northLength rotation ordered cell := by
          have hle := position.isLt
          omega
        have hstrict := ordered.rowBranchPosition_strictMono cell.topRow
          cell.leftCol_lt_rightCol
        dsimp [northLength] at hlast
        calc
          (ordered.toMesh.row cell.topRow).vert
              (northPathStep rotation ordered cell position).succ =
              ordered.toMesh.branch cell.topRow cell.rightCol := by
            rw [← ordered.rowBranchPosition_spec cell.topRow cell.rightCol]
            apply congrArg (ordered.toMesh.row cell.topRow).vert
            apply Fin.ext
            dsimp [northPathStep]
            omega
          _ = (ordered.toMesh.col cell.rightCol).vert
              (eastPathStep rotation ordered cell
                ⟨0, eastLength_pos rotation ordered cell⟩).castSucc := by
            rw [← ordered.colBranchPosition_spec cell.topRow cell.rightCol]
            apply congrArg (ordered.toMesh.col cell.rightCol).vert
            apply Fin.ext
            simp [eastPathStep]
  | east position =>
      simp only [boundarySuccessor]
      split_ifs with h
      · simp only [boundaryData_east_second, boundaryData_east_first]
        apply congrArg (ordered.toMesh.col cell.rightCol).vert
        apply Fin.ext
        simp [eastPathStep, Nat.add_assoc]
      · simp only [boundaryData_east_second, boundaryData_south_first]
        have hlast : position.val + 1 = eastLength rotation ordered cell := by
          have hle := position.isLt
          omega
        have hstrict := ordered.colBranchPosition_strictMono cell.rightCol
          cell.topRow_lt_bottomRow
        dsimp [eastLength] at hlast
        calc
          (ordered.toMesh.col cell.rightCol).vert
              (eastPathStep rotation ordered cell position).succ =
              ordered.toMesh.branch cell.bottomRow cell.rightCol := by
            rw [← ordered.colBranchPosition_spec cell.bottomRow cell.rightCol]
            apply congrArg (ordered.toMesh.col cell.rightCol).vert
            apply Fin.ext
            dsimp [eastPathStep]
            omega
          _ = (ordered.toMesh.row cell.bottomRow).vert
              (southPathStep rotation ordered cell
                ⟨0, southLength_pos rotation ordered cell⟩).succ := by
            rw [← ordered.rowBranchPosition_spec cell.bottomRow cell.rightCol]
            apply congrArg (ordered.toMesh.row cell.bottomRow).vert
            apply Fin.ext
            have hsouth :
                (ordered.rowBranchPosition cell.bottomRow cell.leftCol).val <
                  (ordered.rowBranchPosition cell.bottomRow cell.rightCol).val :=
              ordered.rowBranchPosition_strictMono cell.bottomRow
                cell.leftCol_lt_rightCol
            have hpositive : 1 ≤
                (ordered.rowBranchPosition cell.bottomRow cell.rightCol).val := by
              omega
            dsimp [southPathStep]
            exact (Nat.sub_add_cancel hpositive).symm
  | south position =>
      simp only [boundarySuccessor]
      split_ifs with h
      · simp only [boundaryData_south_second, boundaryData_south_first]
        apply congrArg (ordered.toMesh.row cell.bottomRow).vert
        apply Fin.ext
        have hstrict := ordered.rowBranchPosition_strictMono cell.bottomRow
          cell.leftCol_lt_rightCol
        dsimp [southPathStep, southLength] at h ⊢
        omega
      · simp only [boundaryData_south_second, boundaryData_west_first]
        have hlast : position.val + 1 = southLength rotation ordered cell := by
          have hle := position.isLt
          omega
        have hstrict := ordered.rowBranchPosition_strictMono cell.bottomRow
          cell.leftCol_lt_rightCol
        dsimp [southLength] at hlast
        calc
          (ordered.toMesh.row cell.bottomRow).vert
              (southPathStep rotation ordered cell position).castSucc =
              ordered.toMesh.branch cell.bottomRow cell.leftCol := by
            rw [← ordered.rowBranchPosition_spec cell.bottomRow cell.leftCol]
            apply congrArg (ordered.toMesh.row cell.bottomRow).vert
            apply Fin.ext
            dsimp [southPathStep]
            omega
          _ = (ordered.toMesh.col cell.leftCol).vert
              (westPathStep rotation ordered cell
                ⟨0, westLength_pos rotation ordered cell⟩).succ := by
            rw [← ordered.colBranchPosition_spec cell.bottomRow cell.leftCol]
            apply congrArg (ordered.toMesh.col cell.leftCol).vert
            apply Fin.ext
            have hwest :
                (ordered.colBranchPosition cell.topRow cell.leftCol).val <
                  (ordered.colBranchPosition cell.bottomRow cell.leftCol).val :=
              ordered.colBranchPosition_strictMono cell.leftCol
                cell.topRow_lt_bottomRow
            have hpositive : 1 ≤
                (ordered.colBranchPosition cell.bottomRow cell.leftCol).val := by
              omega
            dsimp [westPathStep]
            exact (Nat.sub_add_cancel hpositive).symm
  | west position =>
      simp only [boundarySuccessor]
      split_ifs with h
      · simp only [boundaryData_west_second, boundaryData_west_first]
        apply congrArg (ordered.toMesh.col cell.leftCol).vert
        apply Fin.ext
        have hstrict := ordered.colBranchPosition_strictMono cell.leftCol
          cell.topRow_lt_bottomRow
        dsimp [westPathStep, westLength] at h ⊢
        omega
      · simp only [boundaryData_west_second, boundaryData_north_first]
        have hlast : position.val + 1 = westLength rotation ordered cell := by
          have hle := position.isLt
          omega
        have hstrict := ordered.colBranchPosition_strictMono cell.leftCol
          cell.topRow_lt_bottomRow
        dsimp [westLength] at hlast
        calc
          (ordered.toMesh.col cell.leftCol).vert
              (westPathStep rotation ordered cell position).castSucc =
              ordered.toMesh.branch cell.topRow cell.leftCol := by
            rw [← ordered.colBranchPosition_spec cell.topRow cell.leftCol]
            apply congrArg (ordered.toMesh.col cell.leftCol).vert
            apply Fin.ext
            dsimp [westPathStep]
            omega
          _ = (ordered.toMesh.row cell.topRow).vert
              (northPathStep rotation ordered cell
                ⟨0, northLength_pos rotation ordered cell⟩).castSucc := by
            rw [← ordered.rowBranchPosition_spec cell.topRow cell.leftCol]
            apply congrArg (ordered.toMesh.row cell.topRow).vert
            apply Fin.ext
            simp [northPathStep]

theorem boundaryData_sharedVertex_of_consecutive
    {source target : CellBoundaryStep rotation ordered cell}
    (hconsecutive : AreBoundaryConsecutive rotation ordered cell source target) :
    (boundaryData rotation minimal ordered cell source).secondVertex =
      (boundaryData rotation minimal ordered cell target).firstVertex := by
  subst target
  exact boundaryData_second_eq_successor_first
    rotation minimal ordered cell source

/-! ## The exact common comparison carrier -/

/-- The common induced graph on which colourings of two consecutive
adjacent-pair deletions can be compared. -/
abbrev boundaryCommonCarrier
    (source target : CellBoundaryStep rotation ordered cell) :=
  AdjacentPairData.DeletedTwoPairsGraph G
    (boundaryData rotation minimal ordered cell source).firstVertex
    (boundaryData rotation minimal ordered cell source).secondVertex
    (boundaryData rotation minimal ordered cell target).firstVertex
    (boundaryData rotation minimal ordered cell target).secondVertex

/-- Canonical inclusion of the common carrier into the source deletion. -/
def boundaryCommonToSourceDeletion
    (source target : CellBoundaryStep rotation ordered cell) :
    boundaryCommonCarrier rotation minimal ordered cell source target ↪g
      DeletedAdjacentPairGraph G
        (boundaryData rotation minimal ordered cell source).firstVertex
        (boundaryData rotation minimal ordered cell source).secondVertex :=
  AdjacentPairData.deletedTwoPairsToFirstDeletionEmbedding G _ _ _ _

/-- Canonical inclusion of the common carrier into the target deletion. -/
def boundaryCommonToTargetDeletion
    (source target : CellBoundaryStep rotation ordered cell) :
    boundaryCommonCarrier rotation minimal ordered cell source target ↪g
      DeletedAdjacentPairGraph G
        (boundaryData rotation minimal ordered cell target).firstVertex
        (boundaryData rotation minimal ordered cell target).secondVertex :=
  AdjacentPairData.deletedTwoPairsToSecondDeletionEmbedding G _ _ _ _

/-- Because consecutive sites share one endpoint, their generic four-name
common carrier has exactly the three endpoint inequalities shown here.
Additional mesh intersections are allowed, so no assertion that the three
vertices are pairwise distinct is smuggled into the statement. -/
theorem boundaryCommonCarrier_property_iff_three_endpoints
    {source target : CellBoundaryStep rotation ordered cell}
    (hconsecutive : AreBoundaryConsecutive rotation ordered cell source target)
    (vertex : V) :
    (vertex ≠ (boundaryData rotation minimal ordered cell source).firstVertex ∧
      vertex ≠ (boundaryData rotation minimal ordered cell source).secondVertex ∧
      vertex ≠ (boundaryData rotation minimal ordered cell target).firstVertex ∧
      vertex ≠ (boundaryData rotation minimal ordered cell target).secondVertex) ↔
    (vertex ≠ (boundaryData rotation minimal ordered cell source).firstVertex ∧
      vertex ≠ (boundaryData rotation minimal ordered cell source).secondVertex ∧
      vertex ≠ (boundaryData rotation minimal ordered cell target).secondVertex) := by
  have hshared := boundaryData_sharedVertex_of_consecutive
    rotation minimal ordered cell hconsecutive
  rw [← hshared]
  tauto

/-! ## One globally coherent Kempe-orbit choice at every site -/

/-- A single adjacent-pair Kempe orbit selected at one boundary step.  The
endpoint equations connect the selected rotation order back to the literal
oriented mesh edge. -/
structure BoundaryKempeSite (step : CellBoundaryStep rotation ordered cell) where
  data : AdjacentPairData G
  first_eq :
    data.firstVertex =
      (boundaryData rotation minimal ordered cell step).firstVertex
  second_eq :
    data.secondVertex =
      (boundaryData rotation minimal ordered cell step).secondVertex
  base :
    (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex).EdgeColoring Color
  baseTait :
    IsTaitEdgeColoring
      (DeletedAdjacentPairGraph G data.firstVertex data.secondVertex) base

/-- Minimality supplies one such orbit at every literal boundary site. -/
theorem nonempty_boundaryKempeSite
    (step : CellBoundaryStep rotation ordered cell) :
    Nonempty (BoundaryKempeSite rotation minimal ordered cell step) := by
  rcases (boundaryData rotation minimal ordered cell step).exists_rotationOrdered_commonKempeOrbit_with_all_constantWords_of_minimal
      rotation minimal with
    ⟨data, hfirst, hsecond, base, hbase, _⟩
  exact ⟨{
    data := data
    first_eq := hfirst
    second_eq := hsecond
    base := base
    baseTait := hbase }⟩

/-- The choice is made once as a function of the boundary site.  Thus its
two incident overlap relations use definitionally the same deletion object
and base colouring. -/
noncomputable def selectedBoundaryKempeSite
    (step : CellBoundaryStep rotation ordered cell) :
    BoundaryKempeSite rotation minimal ordered cell step :=
  Classical.choice
    (nonempty_boundaryKempeSite rotation minimal ordered cell step)

/-- The globally selected sites at consecutive positions still share their
literal endpoint. -/
theorem selectedBoundaryKempeSite_sharedVertex
    (step : CellBoundaryStep rotation ordered cell) :
    (selectedBoundaryKempeSite rotation minimal ordered cell step).data.secondVertex =
      (selectedBoundaryKempeSite rotation minimal ordered cell
        (boundarySuccessor rotation ordered cell step)).data.firstVertex := by
  calc
    (selectedBoundaryKempeSite rotation minimal ordered cell step).data.secondVertex =
        (boundaryData rotation minimal ordered cell step).secondVertex :=
      (selectedBoundaryKempeSite rotation minimal ordered cell step).second_eq
    _ = (boundaryData rotation minimal ordered cell
          (boundarySuccessor rotation ordered cell step)).firstVertex :=
      boundaryData_second_eq_successor_first rotation minimal ordered cell step
    _ = (selectedBoundaryKempeSite rotation minimal ordered cell
          (boundarySuccessor rotation ordered cell step)).data.firstVertex :=
      (selectedBoundaryKempeSite rotation minimal ordered cell
        (boundarySuccessor rotation ordered cell step)).first_eq.symm

/-- The exact finite overlap relation from one selected boundary site to its
clockwise successor. -/
def successorOverlapKempeStateSupport
    (step : CellBoundaryStep rotation ordered cell) : Set OverlapKempeState :=
  let source := selectedBoundaryKempeSite rotation minimal ordered cell step
  let target := selectedBoundaryKempeSite rotation minimal ordered cell
    (boundarySuccessor rotation ordered cell step)
  overlapKempeStateSupport source.data target.data source.base target.base

/-- Every step-to-successor relation is inhabited by the two globally
selected proper base colourings. -/
theorem successorOverlapKempeStateSupport_nonempty
    (step : CellBoundaryStep rotation ordered cell) :
    (successorOverlapKempeStateSupport
      rotation minimal ordered cell step).Nonempty := by
  exact overlapKempeStateSupport_nonempty
    (selectedBoundaryKempeSite rotation minimal ordered cell step).data
    (selectedBoundaryKempeSite rotation minimal ordered cell
      (boundarySuccessor rotation ordered cell step)).data
    (selectedBoundaryKempeSite rotation minimal ordered cell step).base
    (selectedBoundaryKempeSite rotation minimal ordered cell
      (boundarySuccessor rotation ordered cell step)).base
    (selectedBoundaryKempeSite rotation minimal ordered cell step).baseTait
    (selectedBoundaryKempeSite rotation minimal ordered cell
      (boundarySuccessor rotation ordered cell step)).baseTait

end

end GoertzelV24OrderedMeshBoundaryWalk

end Mettapedia.GraphTheory.FourColor
