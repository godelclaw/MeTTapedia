import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularCrosscutOpenInterface
import Mettapedia.GraphTheory.FourColor.RotationSystemEdgeColoring

/-!
# Tait-coloring semantics of a cut-open annular interface

The compositional source counts colorings of *open* planar cubic pieces.  A
paired crosscut already has a literal slit rotation system in this tree: every
crossed primal edge is split into two boundary stubs.  This file makes the
corresponding finite coloring semantics explicit.

An `OpenTaitColoring` is a proper nonzero edge coloring of that slit rotation
system.  The fresh degree-one stubs impose no artificial three-edge condition;
their colors are precisely the free boundary data of the open piece.  Thus the
matrix below counts partial Tait colorings by their two exposed boundary words,
rather than extracting a state only from a coloring of the original closed
graph.

This is the concrete boundary-color component of the source's `Count`
semantics.  The connectivity and capped-face components of the full profile
are intentionally not claimed here; they must be coupled to this literal open
coloring layer before the full corridor transfer is called complete.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24AnnularCrosscutSlitRotation
open GoertzelV24FaceOrbitIncidence
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance openTaitGraphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

namespace AlignedSimpleDualCrosscuts

/-- Proper edge colorings of the literal simultaneous slit.  Boundary stubs
are degree one, so this is a coloring of an open tangle rather than a coloring
of the old closed graph. -/
abbrev OpenTaitColoring
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique) :=
  pair.slitRotationSystem.EdgeColoring Color

/-- Nonzero-color condition for an open Tait coloring.  Properness is already
carried by `OpenTaitColoring`; unlike the closed cubic predicate, this does not
try to make a boundary stub have three incident edges. -/
def IsOpenTaitColoring
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (coloring : pair.OpenTaitColoring) : Prop :=
  pair.slitRotationSystem.IsTaitEdgeColoring coloring

/-- Color carried by one literal left boundary stub of the simultaneous slit. -/
def leftBoundaryColor
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (coloring : pair.OpenTaitColoring) (endpoint : pair.LeftInterfaceEnd) :
    Color :=
  coloring (pair.slitRotationSystem.edgeOf (pair.leftInterfaceStub endpoint))

/-- Color carried by one literal right boundary stub of the simultaneous slit. -/
def rightBoundaryColor
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (coloring : pair.OpenTaitColoring) (endpoint : pair.RightInterfaceEnd) :
    Color :=
  coloring (pair.slitRotationSystem.edgeOf (pair.rightInterfaceStub endpoint))

/-- The input boundary word of an open coloring, read from the actual left
stubs rather than from an ambient closed coloring. -/
def leftBoundaryWord
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (coloring : pair.OpenTaitColoring) : pair.LeftInterfaceEnd → Color :=
  fun endpoint => pair.leftBoundaryColor coloring endpoint

/-- The output boundary word of an open coloring, read from the actual right
stubs rather than from an ambient closed coloring. -/
def rightBoundaryWord
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (coloring : pair.OpenTaitColoring) : pair.RightInterfaceEnd → Color :=
  fun endpoint => pair.rightBoundaryColor coloring endpoint

theorem leftBoundaryColor_ne_zero
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (coloring : pair.OpenTaitColoring) (hcoloring : pair.IsOpenTaitColoring coloring)
    (endpoint : pair.LeftInterfaceEnd) :
    pair.leftBoundaryColor coloring endpoint ≠ 0 := by
  exact hcoloring _

theorem rightBoundaryColor_ne_zero
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (coloring : pair.OpenTaitColoring) (hcoloring : pair.IsOpenTaitColoring coloring)
    (endpoint : pair.RightInterfaceEnd) :
    pair.rightBoundaryColor coloring endpoint ≠ 0 := by
  exact hcoloring _

/-- The finite fiber of open Tait colorings realizing two literal boundary
words.  Keeping the fiber as a `Finset` makes the later generated checker
route explicit: this is a finite enumeration over colorings of one open
piece, not an imported configuration catalogue. -/
noncomputable def openTaitColoringFiber
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (left : pair.LeftInterfaceEnd → Color)
    (right : pair.RightInterfaceEnd → Color) : Finset pair.OpenTaitColoring := by
  classical
  exact Finset.univ.filter fun coloring =>
    pair.IsOpenTaitColoring coloring ∧
      pair.leftBoundaryWord coloring = left ∧
      pair.rightBoundaryWord coloring = right

/-- Boundary-color component of the source's counting semantics: its
`(left,right)` entry is the number of partial Tait colorings of the
*cut-open* map whose exposed boundary words are exactly `left` and `right`.
The richer connectivity and capped-face coordinates remain to be joined to
this concrete finite matrix. -/
noncomputable def openTaitBoundaryColorCount
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique) :
    Matrix (pair.LeftInterfaceEnd → Color) (pair.RightInterfaceEnd → Color) Nat :=
  fun left right => (pair.openTaitColoringFiber left right).card

theorem openTaitBoundaryColorCount_apply
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (left : pair.LeftInterfaceEnd → Color)
    (right : pair.RightInterfaceEnd → Color) :
    pair.openTaitBoundaryColorCount left right =
      (pair.openTaitColoringFiber left right).card :=
  rfl

theorem mem_openTaitColoringFiber_iff
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    {hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))}
    (pair : AlignedSimpleDualCrosscuts (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish hunique)
    (left : pair.LeftInterfaceEnd → Color)
    (right : pair.RightInterfaceEnd → Color)
    (coloring : pair.OpenTaitColoring) :
    coloring ∈ pair.openTaitColoringFiber left right ↔
      pair.IsOpenTaitColoring coloring ∧
        pair.leftBoundaryWord coloring = left ∧
        pair.rightBoundaryWord coloring = right := by
  classical
  simp [openTaitColoringFiber]

end AlignedSimpleDualCrosscuts

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
