import Mathlib.Data.Fin.Rev
import Mathlib.Data.Finset.Basic

/-!
# Proof-relevant interfaces for the physical corridor splice

The compositional route glues open cubic pieces and deletes repeated corridor
slabs.  Equality of a finite semantic payload is not, by itself, a physical
gluing theorem.  The physical construction must also retain three kinds of
data which occur explicitly in the source splice checklist:

* a complete colored star at every seam vertex;
* accumulated edge, internal-vertex, and face support for both rails; and
* an ordered boundary object, together with a side-reversing identification.

This file supplies conservative interfaces for those data and proves the
generic preservation facts they are meant to expose.  It does not assert that
the current corridor construction already inhabits the interfaces, nor does it
construct the final quotient rotation system.  Those remain source-specific
realization theorems.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PhysicalSpliceInterfaces

universe uVertex uHalfEdge uColor uPath uEdge uFace uAnchor uPort

section SeamStar

variable {Vertex : Type uVertex} {HalfEdge : Type uHalfEdge}
  {Color : Type uColor}

/-- Properness at one vertex, stated on incident half-edges. -/
def ProperAt (incident : Vertex → HalfEdge → Prop)
    (color : HalfEdge → Color) (vertex : Vertex) : Prop :=
  ∀ ⦃left right : HalfEdge⦄,
    incident vertex left → incident vertex right → left ≠ right →
      color left ≠ color right

/-- Properness restricted to one piece of a prospective gluing. -/
def ProperOn (belongs : HalfEdge → Prop)
    (incident : Vertex → HalfEdge → Prop) (color : HalfEdge → Color) : Prop :=
  ∀ ⦃vertex left right⦄,
    belongs left → belongs right → incident vertex left → incident vertex right →
      left ≠ right → color left ≠ color right

/-- A complete seam-star receipt.

`useToken` and `used_once` retain the single-use bookkeeping of the pushout.
The equivalence `star` says that a seam vertex receives exactly three final
half-edges, rather than merely some matching subset. -/
structure CompleteSeamStarInterface where
  interfaceVertex : Vertex → Prop
  incident : Vertex → HalfEdge → Prop
  color : HalfEdge → Color
  UseToken : Type
  uses : UseToken → HalfEdge → Prop
  used_once : ∀ halfEdge, ∃! token, uses token halfEdge
  star : (vertex : {vertex // interfaceVertex vertex}) →
    Fin 3 ≃ {halfEdge // incident vertex.1 halfEdge}
  star_colors_distinct : ∀ vertex (left right : Fin 3), left ≠ right →
    color ((star vertex left).1) ≠ color ((star vertex right).1)

/-- Completeness and the certified three-color star imply properness at every
interface vertex. -/
theorem CompleteSeamStarInterface.properAt_interface
    (data : CompleteSeamStarInterface (Vertex := Vertex)
      (HalfEdge := HalfEdge) (Color := Color))
    {vertex : Vertex} (hvertex : data.interfaceVertex vertex) :
    ProperAt data.incident data.color vertex := by
  intro left right hleft hright hne
  let seamVertex : {vertex // data.interfaceVertex vertex} := ⟨vertex, hvertex⟩
  obtain ⟨leftIndex, hleftIndex⟩ :=
    (data.star seamVertex).surjective ⟨left, hleft⟩
  obtain ⟨rightIndex, hrightIndex⟩ :=
    (data.star seamVertex).surjective ⟨right, hright⟩
  have hindex : leftIndex ≠ rightIndex := by
    intro heq
    apply hne
    have := congrArg Subtype.val (hleftIndex.symm.trans
      (heq ▸ hrightIndex))
    exact this
  have hcolors := data.star_colors_distinct seamVertex leftIndex rightIndex hindex
  rw [hleftIndex, hrightIndex] at hcolors
  exact hcolors

/-- A complete seam receipt plus inherited properness away from the interface
gives properness at every final vertex. -/
structure GluedPropernessReceipt extends
    CompleteSeamStarInterface (Vertex := Vertex) (HalfEdge := HalfEdge)
      (Color := Color) where
  noninterface_proper : ∀ vertex, ¬interfaceVertex vertex →
    ProperAt incident color vertex

theorem GluedPropernessReceipt.proper_everywhere
    (data : GluedPropernessReceipt (Vertex := Vertex)
      (HalfEdge := HalfEdge) (Color := Color)) :
    ∀ vertex, ProperAt data.incident data.color vertex := by
  intro vertex
  by_cases hvertex : data.interfaceVertex vertex
  · exact data.toCompleteSeamStarInterface.properAt_interface hvertex
  · exact data.noninterface_proper vertex hvertex

/-! The following two one-edge pieces are the minimal counterexample to the
weak rule "proper on each piece plus agreement on shared edges implies proper
after gluing".  Their overlap is empty, while the final seam star has two red
half-edges. -/

def weakLeftPiece (halfEdge : Bool) : Prop := halfEdge = false

def weakRightPiece (halfEdge : Bool) : Prop := halfEdge = true

def weakIncident (_vertex : Unit) (_halfEdge : Bool) : Prop := True

def weakRedColor (_halfEdge : Bool) : Unit := ()

theorem weak_shared_edge_agreement_does_not_glue :
    ProperOn weakLeftPiece weakIncident weakRedColor ∧
    ProperOn weakRightPiece weakIncident weakRedColor ∧
    (∀ halfEdge, weakLeftPiece halfEdge ∧ weakRightPiece halfEdge →
      weakRedColor halfEdge = weakRedColor halfEdge) ∧
    ¬ ProperAt weakIncident weakRedColor () := by
  constructor
  · intro vertex left right hleft hright _ _ hne
    simp only [weakLeftPiece] at hleft hright
    subst left
    subst right
    exact (hne rfl).elim
  constructor
  · intro vertex left right hleft hright _ _ hne
    simp only [weakRightPiece] at hleft hright
    subst left
    subst right
    exact (hne rfl).elim
  constructor
  · intro halfEdge _
    rfl
  · intro hproper
    have hcolors := hproper (left := false) (right := true)
      trivial trivial (by decide)
    exact hcolors rfl

end SeamStar

section Rails

variable {Path : Type uPath} {Edge : Type uEdge} {Vertex : Type uVertex}
  {Face : Type uFace} {Anchor : Type uAnchor}
  [DecidableEq Edge] [DecidableEq Vertex] [DecidableEq Face]

/-- The support functions associated with the concrete path representation.
Keeping them in one model makes every support field exact by construction. -/
structure RailSupportModel where
  IsSimple : Path → Prop
  edgeSupport : Path → Finset Edge
  internalVertexSupport : Path → Finset Vertex
  faceSupport : Path → Finset Face

/-- One ordered rail with its two boundary anchors and exact accumulated
supports. -/
structure EmbeddedRail (model : RailSupportModel (Path := Path)
    (Edge := Edge) (Vertex := Vertex) (Face := Face)) where
  path : Path
  entryAnchor : Anchor
  exitAnchor : Anchor
  simple : model.IsSimple path

namespace EmbeddedRail

variable {model : RailSupportModel (Path := Path) (Edge := Edge)
  (Vertex := Vertex) (Face := Face)}

def edgeSupport (rail : EmbeddedRail model (Anchor := Anchor)) : Finset Edge :=
  model.edgeSupport rail.path

def internalVertexSupport (rail : EmbeddedRail model (Anchor := Anchor)) :
    Finset Vertex :=
  model.internalVertexSupport rail.path

def faceSupport (rail : EmbeddedRail model (Anchor := Anchor)) : Finset Face :=
  model.faceSupport rail.path

end EmbeddedRail

/-- A globally separated rail pair.  Boundary order is a proof-relevant
predicate supplied by the source carrier; it is not reconstructed from the
three support sets. -/
structure SeparatedRailPair
    (model : RailSupportModel (Path := Path) (Edge := Edge)
      (Vertex := Vertex) (Face := Face))
    (BoundaryOrder : Anchor → Anchor → Anchor → Anchor → Prop) where
  left : EmbeddedRail model (Anchor := Anchor)
  right : EmbeddedRail model (Anchor := Anchor)
  edge_disjoint : Disjoint left.edgeSupport right.edgeSupport
  internalVertex_disjoint :
    Disjoint left.internalVertexSupport right.internalVertexSupport
  face_disjoint : Disjoint left.faceSupport right.faceSupport
  boundary_order : BoundaryOrder left.entryAnchor left.exitAnchor
    right.entryAnchor right.exitAnchor

private theorem disjoint_union_union {α : Type*} [DecidableEq α]
    {firstLeft secondLeft firstRight secondRight : Finset α}
    (hFirst : Disjoint firstLeft firstRight)
    (hCrossLeft : Disjoint firstLeft secondRight)
    (hCrossRight : Disjoint secondLeft firstRight)
    (hSecond : Disjoint secondLeft secondRight) :
    Disjoint (firstLeft ∪ secondLeft) (firstRight ∪ secondRight) := by
  rw [Finset.disjoint_union_left, Finset.disjoint_union_right,
    Finset.disjoint_union_right]
  exact ⟨⟨hFirst, hCrossLeft⟩, hCrossRight, hSecond⟩

/-- The global append rule.  Local separation of each pair is insufficient:
the two cross-freshness conditions are required in all three support
coordinates. -/
noncomputable def SeparatedRailPair.of_support_unions
    {model : RailSupportModel (Path := Path) (Edge := Edge)
      (Vertex := Vertex) (Face := Face)}
    {BoundaryOrder : Anchor → Anchor → Anchor → Anchor → Prop}
    (old next : SeparatedRailPair model BoundaryOrder)
    (resultLeft resultRight : EmbeddedRail model (Anchor := Anchor))
    (hleftEdge : resultLeft.edgeSupport =
      old.left.edgeSupport ∪ next.left.edgeSupport)
    (hrightEdge : resultRight.edgeSupport =
      old.right.edgeSupport ∪ next.right.edgeSupport)
    (hleftVertex : resultLeft.internalVertexSupport =
      old.left.internalVertexSupport ∪ next.left.internalVertexSupport)
    (hrightVertex : resultRight.internalVertexSupport =
      old.right.internalVertexSupport ∪ next.right.internalVertexSupport)
    (hleftFace : resultLeft.faceSupport =
      old.left.faceSupport ∪ next.left.faceSupport)
    (hrightFace : resultRight.faceSupport =
      old.right.faceSupport ∪ next.right.faceSupport)
    (hEdgeOldNew : Disjoint old.left.edgeSupport next.right.edgeSupport)
    (hEdgeNewOld : Disjoint next.left.edgeSupport old.right.edgeSupport)
    (hVertexOldNew : Disjoint old.left.internalVertexSupport
      next.right.internalVertexSupport)
    (hVertexNewOld : Disjoint next.left.internalVertexSupport
      old.right.internalVertexSupport)
    (hFaceOldNew : Disjoint old.left.faceSupport next.right.faceSupport)
    (hFaceNewOld : Disjoint next.left.faceSupport old.right.faceSupport)
    (hboundary : BoundaryOrder resultLeft.entryAnchor resultLeft.exitAnchor
      resultRight.entryAnchor resultRight.exitAnchor) :
    SeparatedRailPair model BoundaryOrder where
  left := resultLeft
  right := resultRight
  edge_disjoint := by
    rw [hleftEdge, hrightEdge]
    exact disjoint_union_union old.edge_disjoint hEdgeOldNew hEdgeNewOld
      next.edge_disjoint
  internalVertex_disjoint := by
    rw [hleftVertex, hrightVertex]
    exact disjoint_union_union old.internalVertex_disjoint hVertexOldNew
      hVertexNewOld next.internalVertex_disjoint
  face_disjoint := by
    rw [hleftFace, hrightFace]
    exact disjoint_union_union old.face_disjoint hFaceOldNew hFaceNewOld
      next.face_disjoint
  boundary_order := hboundary

/-! Three locally simple one-edge steps can still close a triangle. -/

def triangleRailWord : List (Fin 3) := [0, 1, 2, 0]

theorem triangleRailWord_not_simple : ¬triangleRailWord.Nodup := by
  decide

theorem triangleRailWord_local_steps_distinct :
    triangleRailWord.IsChain (· ≠ ·) := by
  decide

end Rails

section OrderedBoundary

variable {Port : Type uPort}

/-- A boundary is an indexed cyclic list of literal ports, not merely its
underlying finite set. -/
structure OrderedBoundary (portCount : Nat) where
  port : Fin portCount ≃ Port

/-- An orientation-compatible identification reverses the boundary-side
order when the two oriented surfaces are sewn together. -/
structure SideReversingBoundaryIso {LeftPort RightPort : Type*}
    {portCount : Nat}
    (left : OrderedBoundary (Port := LeftPort) portCount)
    (right : OrderedBoundary (Port := RightPort) portCount) where
  portEquiv : LeftPort ≃ RightPort
  index_compatibility : ∀ index,
    portEquiv (left.port index) = right.port (Fin.rev index)

/-- The finite semantic payload carried at an ordered boundary. -/
structure FiveFieldPayload (ColorData ConnectivityData FaceData IncidenceData
    CapData : Type*) where
  color : ColorData
  connectivity : ConnectivityData
  face : FaceData
  incidence : IncidenceData
  cap : CapData

/-- The physical splice interface keeps geometry and semantics separate but
simultaneously load-bearing.  Equality of `leftProfile` and `rightProfile`
cannot erase the ordered boundary or the seam and rail receipts. -/
structure OrderedBoundarySpliceData
    (LeftPort RightPort : Type*) (portCount : Nat)
    (RailPair SeamReceipt Profile : Type*) where
  leftBoundary : OrderedBoundary (Port := LeftPort) portCount
  rightBoundary : OrderedBoundary (Port := RightPort) portCount
  boundaryIso : SideReversingBoundaryIso leftBoundary rightBoundary
  rails : RailPair
  seam : SeamReceipt
  leftProfile : Profile
  rightProfile : Profile
  profileAgreement : leftProfile = rightProfile

end OrderedBoundary

end GoertzelV24PhysicalSpliceInterfaces

end Mettapedia.GraphTheory.FourColor
