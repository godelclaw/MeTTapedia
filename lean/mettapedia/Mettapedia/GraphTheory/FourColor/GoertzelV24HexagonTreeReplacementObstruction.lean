import Mettapedia.GraphTheory.FourColor.GoertzelV24HexagonPlanarPairingObstruction

/-!
# No smaller connected cubic tree is a monotone hexagon replacement

A connected cubic tangle with six boundary ports and fewer than the six
internal vertices of a hexagonal cell must have four internal vertices and
three internal edges.  Its internal graph is therefore a tree.  Up to
dihedral boundary order there are three plane boundary-support types: two
orders for the path-shaped internal tree and one for the tripod.

This file gives those three exact support relations and, in every case, an
explicit proper tree colouring whose boundary word does not extend across a
hexagon.  The accompanying ordinary proof classifies an arbitrary smaller
connected plane cubic six-port tangle into these three cases.

This is a local monotone-support obstruction.  It does not rule out a
replacement of a larger two-dimensional patch or a replacement justified by
the restricted language of one actual exterior.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexagonTreeReplacementObstruction

/-- The three plane support types of a cubic tree with six cyclic ports.  In
the two path cases the singleton port blocks are respectively separated or
adjacent around the outer face; in the tripod case all three blocks are
pairs. -/
inductive PlaneSixPortTreeShape where
  | pathSeparated
  | pathAdjacent
  | tripod
  deriving DecidableEq

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Colours of the three internal tree edges. -/
abbrev TreeInternalColoring := Fin 3 → Color

/-- Exact local properness relation for the three canonical plane trees.

For both path cases, the internal edges are `01`, `02`, and `13`.  For the
tripod they are the three edges from the centre to its leaves. -/
def IsTreeExtension (shape : PlaneSixPortTreeShape)
    (word : HexagonBoundaryWord) (internal : TreeInternalColoring) : Prop :=
  match shape with
  | .pathSeparated =>
      ProperColorTriple (word 0) (internal 0) (internal 1) ∧
      ProperColorTriple (word 3) (internal 0) (internal 2) ∧
      ProperColorTriple (word 4) (word 5) (internal 1) ∧
      ProperColorTriple (word 1) (word 2) (internal 2)
  | .pathAdjacent =>
      ProperColorTriple (word 2) (internal 0) (internal 1) ∧
      ProperColorTriple (word 3) (internal 0) (internal 2) ∧
      ProperColorTriple (word 0) (word 1) (internal 1) ∧
      ProperColorTriple (word 4) (word 5) (internal 2)
  | .tripod =>
      ProperColorTriple (internal 0) (internal 1) (internal 2) ∧
      ProperColorTriple (word 0) (word 1) (internal 0) ∧
      ProperColorTriple (word 2) (word 3) (internal 1) ∧
      ProperColorTriple (word 4) (word 5) (internal 2)

instance (shape : PlaneSixPortTreeShape) (word : HexagonBoundaryWord)
    (internal : TreeInternalColoring) :
    Decidable (IsTreeExtension shape word internal) := by
  unfold IsTreeExtension
  cases shape <;> infer_instance

/-- Boundary language of one canonical smaller cubic tree. -/
def treeSupport (shape : PlaneSixPortTreeShape) : Set HexagonBoundaryWord :=
  {word | ∃ internal, IsTreeExtension shape word internal}

/-- The literal support of the hexagonal cell, without packaging nonzero
boundary colours as subtypes. -/
def hexagonRawSupport : Set HexagonBoundaryWord :=
  {word | ∃ internal, IsHexagonExtension word internal}

/-- A concrete word accepted by each tree shape but rejected by the
hexagon. -/
def obstructionWord (shape : PlaneSixPortTreeShape) : HexagonBoundaryWord :=
  match shape with
  | .pathSeparated => hexagonColorWord red red blue red red blue
  | .pathAdjacent => hexagonColorWord red blue red red red blue
  | .tripod => hexagonColorWord red blue red purple blue purple

/-- Internal edge colours witnessing the corresponding tree extension. -/
def obstructionInternal
    (shape : PlaneSixPortTreeShape) : TreeInternalColoring :=
  match shape with
  | .pathSeparated => fun i =>
      if i = 0 then blue else purple
  | .pathAdjacent => fun i =>
      if i = 0 then blue else purple
  | .tripod => fun i =>
      if i = 0 then purple else if i = 1 then blue else red

/-- Each displayed boundary word has a proper colouring on its canonical
four-vertex cubic tree. -/
theorem obstructionWord_isTreeExtension
    (shape : PlaneSixPortTreeShape) :
    IsTreeExtension shape (obstructionWord shape)
      (obstructionInternal shape) := by
  cases shape <;> decide

/-- None of the three displayed words extends across the six-cycle. -/
theorem obstructionWord_not_hexagon
    (shape : PlaneSixPortTreeShape) :
    ¬ ∃ internal, IsHexagonExtension (obstructionWord shape) internal := by
  cases shape <;> decide

/-- No one of the three plane cubic-tree boundary languages is contained in
the literal hexagon language. -/
theorem no_treeSupport_subset_hexagonRawSupport
    (shape : PlaneSixPortTreeShape) :
    ¬ treeSupport shape ⊆ hexagonRawSupport := by
  intro hsubset
  exact obstructionWord_not_hexagon shape
    (hsubset ⟨obstructionInternal shape,
      obstructionWord_isTreeExtension shape⟩)

/-- Simultaneous finite form of the three support-inclusion obstructions. -/
theorem every_planeTreeShape_has_nonextension :
    ∀ shape : PlaneSixPortTreeShape,
      ∃ word : HexagonBoundaryWord,
        word ∈ treeSupport shape ∧ word ∉ hexagonRawSupport := by
  intro shape
  exact ⟨obstructionWord shape,
    ⟨obstructionInternal shape, obstructionWord_isTreeExtension shape⟩,
    obstructionWord_not_hexagon shape⟩

end GoertzelV24HexagonTreeReplacementObstruction

end Mettapedia.GraphTheory.FourColor
