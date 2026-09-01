import Mettapedia.GraphTheory.Embedding.PathChord
import Mettapedia.GraphTheory.FourColor.CubicPathRotation
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceCutVertexAvoidingTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24LocalFaceCutCycleWalkTransport

/-!
# Rotation sides of chords on a cycle arc

This file separates the local rotation algebra of two interleaving chords
from the global Jordan-separation argument.  The local theorem says that an
exact face cut carried by one chord cycle forces opposite attachment turns,
provided the complementary outer arc identifies the two exterior face
labels.  A subsequent theorem supplies that anchor from a `PathCycleClosure`.
-/

namespace Mettapedia.GraphTheory.Embedding

open Mettapedia.GraphTheory
open Mettapedia.GraphTheory.CubicPathAttachment
open Mettapedia.GraphTheory.FourColor
open Mettapedia.GraphTheory.FourColor.CubicPathRotation
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceCutTransport
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceCutVertexAvoidingTransport
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
open Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence
open Mettapedia.GraphTheory.FourColor.GoertzelV24InducedHexCorridorTypes
open Mettapedia.GraphTheory.FourColor.SimpleGraphDartRotation
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {start finish : V}

/-- Every edge at a based vertex of the complementary outer-cycle interval
avoids the selected chord cycle.  Path-suffix and path-prefix vertices are
outside the selected coordinate interval; vertices genuinely in the closing
arc are excluded by simplicity of the outer cycle. -/
theorem incidentEdge_not_mem_chordCycle_of_mem_exteriorInterval_darts
    {path : G.Walk start finish} (closure : PathCycleClosure path)
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (selectedPosition : InternalPosition path)
    (selected : ChordAttachment hpath hregular selectedPosition)
    (hselectedLeft : selected.IsLeftEndpoint hpath hregular selectedPosition)
    (outerRight : Fin (path.length + 1))
    (hright :
      (selected.orderedCoordinates hpath hregular selectedPosition).right <
        outerRight)
    (based : G.Dart)
    (hbased : based ∈
      (closure.exteriorInterval
        (selected.orderedCoordinates hpath hregular selectedPosition).left
        outerRight).darts)
    (incident : G.Dart) (hincident : incident.fst = based.fst) :
    incident.edge ∉
      (selected.boundary hpath hregular selectedPosition).cycleWalk.edges := by
  rcases closure.based_vertex_of_mem_exteriorInterval_darts
      (selected.orderedCoordinates hpath hregular selectedPosition).left
      outerRight based hbased with
    ⟨coordinate, houtside, hcoordinateBound, hbase⟩ | hcomplement
  · change (⟨incident.edge, incident.edge_mem⟩ : G.edgeSet).1 ∉
      (selected.boundary hpath hregular selectedPosition).cycleWalk.edges
    refine selected.incidentEdge_not_mem_boundary_cycleWalk_of_coordinate_outside
      hpath hregular selectedPosition coordinate hcoordinateBound ?_
        ⟨incident.edge, incident.edge_mem⟩ ?_
    · rcases houtside with hbefore | hafter
      · exact Or.inl hbefore
      · exact Or.inr (lt_of_lt_of_le hright hafter)
    · change path.getVert coordinate ∈ incident.edge
      rw [← hbase, ← hincident]
      simp [SimpleGraph.Dart.edge, Sym2.mem_iff]
  · intro hedge
    have hvertex : incident.fst ∈ (incident.edge : Sym2 V) := by
      simp [SimpleGraph.Dart.edge, Sym2.mem_iff]
    rcases selected.exists_coordinate_between_of_mem_boundary_cycleWalk_edges
        hpath hregular selectedPosition
        ⟨incident.edge, incident.edge_mem⟩ hedge hvertex with
      ⟨inside, hleft, _hrightInside, hinside⟩
    have hselectedCoordinate : selectedPosition.index =
        (selected.orderedCoordinates hpath hregular
          selectedPosition).left.val := by
      exact congrArg Fin.val hselectedLeft
    change selectedPosition.index =
      (selected.orderedCoordinates hpath hregular
        selectedPosition).left.val at hselectedCoordinate
    have hinsidePositive : inside ≠ 0 := by
      have hpositionPositive : 0 < selectedPosition.index :=
        Nat.pos_of_ne_zero selectedPosition.index_ne_zero
      omega
    have hpathNotNil : ¬path.Nil := by
      rw [SimpleGraph.Walk.not_nil_iff_lt_length]
      exact lt_of_le_of_lt (Nat.zero_le selectedPosition.index)
        selectedPosition.index_lt_length
    have hpathTail : path.getVert inside ∈ path.support.tail :=
      path.getVert_mem_tail_support hpathNotNil hinsidePositive
    have hbasedEq : based.fst = path.getVert inside :=
      hincident.symm.trans hinside.symm
    rw [hbasedEq] at hcomplement
    exact (List.disjoint_left.mp closure.tail_support_disjoint)
      hpathTail hcomplement

/-- The final dart of the complementary outer-cycle interval enters the
selected left endpoint along the ambient path, so reversing it gives the
selected position's backward dart. -/
theorem symm_lastDart_exteriorInterval_eq_backwardDart
    {path : G.Walk start finish} (closure : PathCycleClosure path)
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (selectedPosition : InternalPosition path)
    (selected : ChordAttachment hpath hregular selectedPosition)
    (hselectedLeft : selected.IsLeftEndpoint hpath hregular selectedPosition)
    (outerRight : Fin (path.length + 1))
    (hnil : ¬(closure.exteriorInterval
      (selected.orderedCoordinates hpath hregular selectedPosition).left
      outerRight).Nil) :
    ((closure.exteriorInterval
      (selected.orderedCoordinates hpath hregular selectedPosition).left
      outerRight).lastDart hnil).symm = backwardDart selectedPosition := by
  let left :=
    (selected.orderedCoordinates hpath hregular selectedPosition).left
  let exterior := closure.exteriorInterval left outerRight
  have hleftCoordinate : selectedPosition.index = left.val := by
    exact congrArg Fin.val hselectedLeft
  have hleftPositive : 0 < left.val := by
    rw [← hleftCoordinate]
    exact Nat.pos_of_ne_zero selectedPosition.index_ne_zero
  have hleftBound : left.val ≤ path.length := Nat.lt_succ_iff.mp left.isLt
  have hinitialNe : path.darts.take left.val ≠ [] := by
    intro hempty
    have hlength := congrArg List.length hempty
    simp [SimpleGraph.Walk.length_darts, Nat.min_eq_left hleftBound] at hlength
    exact (Nat.ne_of_gt hleftPositive) (by
      simpa using congrArg Fin.val hlength)
  have hdartsNe : exterior.darts ≠ [] :=
    SimpleGraph.Walk.darts_eq_nil.not.mpr hnil
  have hlastExterior : exterior.darts.getLast hdartsNe =
      (path.darts.take left.val).getLast hinitialNe := by
    have hrestNe :
        closure.complement.darts ++ path.darts.take left.val ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ hinitialNe
    have hpiecesNe :
        path.darts.drop outerRight ++
          (closure.complement.darts ++ path.darts.take left.val) ≠ [] :=
      List.append_ne_nil_of_right_ne_nil _ hrestNe
    calc
      exterior.darts.getLast hdartsNe =
          (path.darts.drop outerRight ++
            (closure.complement.darts ++ path.darts.take left.val)).getLast
              hpiecesNe :=
        List.getLast_congr hdartsNe hpiecesNe
          (closure.exteriorInterval_darts left outerRight)
      _ = (closure.complement.darts ++
            path.darts.take left.val).getLast hrestNe :=
        List.getLast_append_of_right_ne_nil _ _ hrestNe
      _ = (path.darts.take left.val).getLast hinitialNe :=
        List.getLast_append_of_right_ne_nil _ _ hinitialNe
  have hlastPrefix : (path.darts.take left.val).getLast hinitialNe =
      (backwardDart selectedPosition).symm := by
    rw [List.getLast_eq_getElem]
    simp only [List.length_take, SimpleGraph.Walk.length_darts,
      Nat.min_eq_left hleftBound]
    rw [List.getElem_take,
      SimpleGraph.Walk.darts_getElem_eq_getVert]
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · change path.getVert (left.val - 1) =
        path.getVert (selectedPosition.index - 1)
      rw [hleftCoordinate]
    · change path.getVert (left.val - 1 + 1) =
        path.getVert selectedPosition.index
      have hone : 1 ≤ left.val := Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hleftPositive)
      rw [Nat.sub_add_cancel hone, ← hleftCoordinate]
  have hlast : exterior.lastDart hnil =
      (backwardDart selectedPosition).symm := by
    rw [exterior.lastDart_eq_getLast_darts hnil]
    exact hlastExterior.trans hlastPrefix
  rw [hlast]
  exact SimpleGraph.Dart.symm_symm _

/-- The complementary arc of a simple outer cycle identifies the exterior
face sides of two interleaving chords.  Starting at the later chord, cross
its non-cut edge and follow the outer-cycle interval back to the selected
left endpoint.  Every vertex on that interval avoids the selected chord
cycle, so the exact-cut label is unchanged throughout. -/
theorem labels_chordDart_eq_backwardDart_of_exteriorInterval
    (rotation : Data G)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    {path : G.Walk start finish} (closure : PathCycleClosure path)
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (selectedPosition otherPosition : InternalPosition path)
    (selected : ChordAttachment hpath hregular selectedPosition)
    (other : ChordAttachment hpath hregular otherPosition)
    (hselectedLeft : selected.IsLeftEndpoint hpath hregular selectedPosition)
    {A : Type*} (labels : OrbitFace rotation.toRotationSystem → A)
    (hexact : ∀ dart : rotation.toRotationSystem.D,
      labels (dartOrbitFace rotation.toRotationSystem dart) ≠
          labels (dartOrbitFace rotation.toRotationSystem
            (rotation.toRotationSystem.alpha dart)) ↔
        (rotation.toRotationSystem.edgeOf dart).1 ∈
          (selected.boundary hpath hregular selectedPosition).cycleWalk.edges)
    (hright :
      (selected.orderedCoordinates hpath hregular selectedPosition).right <
        (other.orderedCoordinates hpath hregular otherPosition).right) :
    labels (dartOrbitFace rotation.toRotationSystem
        (other.chordDart hpath hregular otherPosition)) =
      labels (dartOrbitFace rotation.toRotationSystem
        (backwardDart selectedPosition)) := by
  let RS := rotation.toRotationSystem
  let selectedLeft :=
    (selected.orderedCoordinates hpath hregular selectedPosition).left
  let otherRight :=
    (other.orderedCoordinates hpath hregular otherPosition).right
  let exterior := closure.exteriorInterval selectedLeft otherRight
  have hleftRight : selectedLeft < otherRight :=
    lt_trans selected.orderedCoordinates.left_lt_right hright
  have hnil : ¬exterior.Nil := by
    exact closure.exteriorInterval_not_nil hpath selectedLeft otherRight
      hleftRight
  have hfirstMem : exterior.firstDart hnil ∈ exterior.darts :=
    exterior.firstDart_mem_darts hnil
  have hfirstBase :
      RS.vertOf (exterior.firstDart hnil) =
        RS.vertOf (RS.alpha
          (other.chordDart hpath hregular otherPosition)) := by
    change (exterior.firstDart hnil).fst =
      (other.chordDart hpath hregular otherPosition).snd
    change path.getVert otherRight = path.getVert
      (other.orderedCoordinates hpath hregular otherPosition).right
    rfl
  have halphaOtherNotCut :
      (RS.edgeOf (RS.alpha
        (other.chordDart hpath hregular otherPosition))).1 ∉
          (selected.boundary hpath hregular selectedPosition).cycleWalk.edges := by
    apply incidentEdge_not_mem_chordCycle_of_mem_exteriorInterval_darts
      closure hpath hregular selectedPosition selected hselectedLeft
        otherRight hright (exterior.firstDart hnil) hfirstMem
          (RS.alpha (other.chordDart hpath hregular otherPosition))
    exact hfirstBase.symm
  have hotherNotCut :
      (RS.edgeOf (other.chordDart hpath hregular otherPosition)).1 ∉
        (selected.boundary hpath hregular selectedPosition).cycleWalk.edges := by
    rw [RS.edge_alpha] at halphaOtherNotCut
    exact halphaOtherNotCut
  have hcrossOther := labels_eq_alpha_of_not_cut RS labels
    (fun edge : G.edgeSet ↦ edge.1 ∈
      (selected.boundary hpath hregular selectedPosition).cycleWalk.edges)
    hexact (other.chordDart hpath hregular otherPosition) hotherNotCut
  have hturn :
      labels (dartOrbitFace RS
          (RS.alpha (other.chordDart hpath hregular otherPosition))) =
        labels (dartOrbitFace RS (exterior.firstDart hnil)) := by
    apply labels_eq_of_same_vertex_of_all_edges_not_cut
      RS hrotation labels
        (fun edge : G.edgeSet ↦ edge.1 ∈
          (selected.boundary hpath hregular selectedPosition).cycleWalk.edges)
        hexact
    · exact hfirstBase
    · intro incident hincident
      apply incidentEdge_not_mem_chordCycle_of_mem_exteriorInterval_darts
        closure hpath hregular selectedPosition selected hselectedLeft
          otherRight hright (exterior.firstDart hnil) hfirstMem incident
      exact hincident.trans hfirstBase.symm
  have htransport :=
    walk_labels_eq_firstDart_alpha_lastDart_of_vertices_avoid_cut
      rotation hrotation labels
        (fun edge : G.edgeSet ↦ edge.1 ∈
          (selected.boundary hpath hregular selectedPosition).cycleWalk.edges)
        hexact exterior hnil (by
          intro based hbased incident hincident
          exact incidentEdge_not_mem_chordCycle_of_mem_exteriorInterval_darts
            closure hpath hregular selectedPosition selected hselectedLeft
              otherRight hright based hbased incident hincident)
  have hlastAlpha : RS.alpha (exterior.lastDart hnil) =
      backwardDart selectedPosition := by
    rw [SimpleGraphDartRotation.Data.toRotationSystem_alpha]
    exact symm_lastDart_exteriorInterval_eq_backwardDart closure hpath hregular
      selectedPosition selected hselectedLeft otherRight hnil
  calc
    labels (dartOrbitFace RS
        (other.chordDart hpath hregular otherPosition)) =
        labels (dartOrbitFace RS
          (RS.alpha (other.chordDart hpath hregular otherPosition))) :=
      hcrossOther
    _ = labels (dartOrbitFace RS (exterior.firstDart hnil)) := hturn
    _ = labels (dartOrbitFace RS
          (RS.alpha (exterior.lastDart hnil))) := htransport
    _ = labels (dartOrbitFace RS (backwardDart selectedPosition)) := by
      rw [hlastAlpha]

/-- If the earlier endpoint of another canonical chord lies strictly inside
the selected chord interval, its backward path dart occurs in the selected
oriented chord cycle. -/
theorem backwardDart_mem_chordCycle_of_left_inside
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (selectedPosition otherPosition : InternalPosition path)
    (selected : ChordAttachment hpath hregular selectedPosition)
    (other : ChordAttachment hpath hregular otherPosition)
    (hotherLeft : other.IsLeftEndpoint hpath hregular otherPosition)
    (hleft :
      (selected.orderedCoordinates hpath hregular selectedPosition).left <
        (other.orderedCoordinates hpath hregular otherPosition).left)
    (hright :
      (other.orderedCoordinates hpath hregular otherPosition).left <
        (selected.orderedCoordinates hpath hregular selectedPosition).right) :
    backwardDart otherPosition ∈
      (selected.boundary hpath hregular selectedPosition).cycleWalk.darts := by
  let selectedLeft :=
    (selected.orderedCoordinates hpath hregular selectedPosition).left.val
  let selectedRight :=
    (selected.orderedCoordinates hpath hregular selectedPosition).right.val
  let otherLeft :=
    (other.orderedCoordinates hpath hregular otherPosition).left.val
  let offset := otherLeft - 1 - selectedLeft
  have hotherIndex : otherPosition.index = otherLeft := by
    simpa [otherLeft] using congrArg Fin.val hotherLeft
  have hselectedRight : selectedRight ≤ path.length := by
    exact Nat.le_of_lt_succ
      (selected.orderedCoordinates hpath hregular selectedPosition).right.isLt
  have hsubarcLength :
      (selected.subarc hpath hregular selectedPosition).length =
        selectedRight - selectedLeft := by
    exact walkInterval_length path _ _
      selected.orderedCoordinates.left_lt_right.le hselectedRight
  have hoffset : offset <
      (selected.subarc hpath hregular selectedPosition).darts.length := by
    rw [SimpleGraph.Walk.length_darts, hsubarcLength]
    dsimp [offset, selectedLeft, selectedRight, otherLeft]
    omega
  have hdarts :
      (selected.subarc hpath hregular selectedPosition).darts =
        ((path.darts.drop selectedLeft).take
          (selectedRight - selectedLeft)) := by
    simpa only [selectedLeft, selectedRight] using
      selected.subarc_darts hpath hregular selectedPosition
  have hoffsetSlice : offset <
      ((path.darts.drop selectedLeft).take
        (selectedRight - selectedLeft)).length := by
    rw [← hdarts]
    exact hoffset
  have hdart :
      ((path.darts.drop selectedLeft).take
        (selectedRight - selectedLeft))[offset] =
          (backwardDart otherPosition).symm := by
    rw [List.getElem_take, List.getElem_drop,
      SimpleGraph.Walk.darts_getElem_eq_getVert]
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · change path.getVert (selectedLeft + offset) =
        path.getVert (otherPosition.index - 1)
      congr 1
      dsimp [offset]
      omega
    · change path.getVert (selectedLeft + offset + 1) =
        path.getVert otherPosition.index
      congr 1
      dsimp [offset]
      omega
  have hsymmMember : (backwardDart otherPosition).symm ∈
      (selected.subarc hpath hregular selectedPosition).darts := by
    rw [hdarts, ← hdart]
    exact List.getElem_mem hoffsetSlice
  have hreverseMember : backwardDart otherPosition ∈
      (selected.subarc hpath hregular selectedPosition).reverse.darts :=
    (SimpleGraph.Walk.mem_darts_reverse).2 (by simpa using hsymmMember)
  change backwardDart otherPosition ∈
    ((selected.subarc hpath hregular selectedPosition).reverse.cons
      (selected.chordDart hpath hregular selectedPosition).adj).darts
  simp only [SimpleGraph.Walk.darts_cons, List.mem_cons]
  exact Or.inr hreverseMember

/-- Along an exact cut carried by the selected chord cycle, its chord dart
and the backward path dart at every strictly interior coordinate receive the
same oriented-side label. -/
theorem labels_chordDart_eq_backwardDart_of_left_inside
    (rotation : Data G)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (selectedPosition otherPosition : InternalPosition path)
    (selected : ChordAttachment hpath hregular selectedPosition)
    (other : ChordAttachment hpath hregular otherPosition)
    (hotherLeft : other.IsLeftEndpoint hpath hregular otherPosition)
    {A : Type*} (labels : OrbitFace rotation.toRotationSystem → A)
    (hexact : ∀ dart : rotation.toRotationSystem.D,
      labels (dartOrbitFace rotation.toRotationSystem dart) ≠
          labels (dartOrbitFace rotation.toRotationSystem
            (rotation.toRotationSystem.alpha dart)) ↔
        (rotation.toRotationSystem.edgeOf dart).1 ∈
        (selected.boundary hpath hregular selectedPosition).cycleWalk.edges)
    (hleft :
      (selected.orderedCoordinates hpath hregular selectedPosition).left <
        (other.orderedCoordinates hpath hregular otherPosition).left)
    (hright :
      (other.orderedCoordinates hpath hregular otherPosition).left <
        (selected.orderedCoordinates hpath hregular selectedPosition).right) :
    labels (dartOrbitFace rotation.toRotationSystem
        (selected.chordDart hpath hregular selectedPosition)) =
      labels (dartOrbitFace rotation.toRotationSystem
        (backwardDart otherPosition)) := by
  let boundary := selected.boundary hpath hregular selectedPosition
  have hcubic : rotation.toRotationSystem.IsCubic :=
    rotation.toRotationSystem_isCubic_iff.mpr
      (SimpleGraph.isRegularOfDegree_instance_independent 3 _ _ hregular)
  have hcycle : boundary.cycleWalk.IsCycle := boundary.cycleWalk_isCycle
  have htransport := rotation.cycle_labels_eq_firstDart_dart_of_mem_darts_of_local_cubic
    hrotation labels boundary.cycleWalk hcycle hexact
      (fun dart _ ↦ hcubic (rotation.toRotationSystem.vertOf dart))
      (backwardDart otherPosition)
      (backwardDart_mem_chordCycle_of_left_inside hpath hregular
        selectedPosition otherPosition selected other hotherLeft hleft hright)
  rw [boundary.firstDart_cycleWalk] at htransport
  exact htransport

/-- For two canonically oriented chords with endpoints ordered
`selected.left < other.left < selected.right < other.right`, an exact face
cut along the selected chord cycle and the complementary outer-face anchor
force the two attachment turns to be different.  This is the local rotation
algebra in the chord-noncrossing argument; the outer-cycle separation theorem
is responsible for supplying `hanchor`. -/
theorem attachmentTurn_ne_of_right_interleaving_exactFaceCut
    (rotation : Data G)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    {path : G.Walk start finish} (hpath : path.IsPath)
    (hregular : G.IsRegularOfDegree 3)
    (selectedPosition otherPosition : InternalPosition path)
    (selected : ChordAttachment hpath hregular selectedPosition)
    (other : ChordAttachment hpath hregular otherPosition)
    (hselectedLeft : selected.IsLeftEndpoint hpath hregular selectedPosition)
    (hotherLeft : other.IsLeftEndpoint hpath hregular otherPosition)
    {A : Type*} (labels : OrbitFace rotation.toRotationSystem → A)
    (hexact : ∀ dart : rotation.toRotationSystem.D,
      labels (dartOrbitFace rotation.toRotationSystem dart) ≠
          labels (dartOrbitFace rotation.toRotationSystem
            (rotation.toRotationSystem.alpha dart)) ↔
        (rotation.toRotationSystem.edgeOf dart).1 ∈
          (selected.boundary hpath hregular selectedPosition).cycleWalk.edges)
    (hleft :
      (selected.orderedCoordinates hpath hregular selectedPosition).left <
        (other.orderedCoordinates hpath hregular otherPosition).left)
    (hmiddle :
      (other.orderedCoordinates hpath hregular otherPosition).left <
        (selected.orderedCoordinates hpath hregular selectedPosition).right)
    (hright :
      (selected.orderedCoordinates hpath hregular selectedPosition).right <
        (other.orderedCoordinates hpath hregular otherPosition).right)
    (hanchor :
      labels (dartOrbitFace rotation.toRotationSystem
          (other.chordDart hpath hregular otherPosition)) =
        labels (dartOrbitFace rotation.toRotationSystem
          (backwardDart selectedPosition))) :
    attachmentTurn rotation hpath hregular selectedPosition ≠
      attachmentTurn rotation hpath hregular otherPosition := by
  let RS := rotation.toRotationSystem
  let boundary := selected.boundary hpath hregular selectedPosition
  have hcyclic : rotation.IsVertexwiseCyclic := by
    intro vertex
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · intro dart hdart
      simpa using (rotation.vertexRotation_fst dart).trans hdart
    · intro left _hleft right _hright heq
      exact rotation.vertexRotation.injective heq
    · intro dart hdart
      refine ⟨rotation.vertexRotation.symm dart, ?_, by simp⟩
      calc
        (rotation.vertexRotation.symm dart).fst =
            (rotation.vertexRotation
              (rotation.vertexRotation.symm dart)).fst :=
          (rotation.vertexRotation_fst _).symm
        _ = dart.fst := congrArg (fun current : G.Dart ↦ current.fst)
          (rotation.vertexRotation.apply_symm_apply dart)
        _ = vertex := hdart
    · intro left hleft right hright
      apply hrotation left right
      simpa using hleft.trans hright.symm
  have hselectedAttachment :
      attachmentDart hpath hregular selectedPosition =
        selected.chordDart hpath hregular selectedPosition :=
    attachmentDart_eq_chordDart_of_isLeftEndpoint hpath hregular
      selectedPosition selected hselectedLeft
  have hotherAttachment :
      attachmentDart hpath hregular otherPosition =
        other.chordDart hpath hregular otherPosition :=
    attachmentDart_eq_chordDart_of_isLeftEndpoint hpath hregular
      otherPosition other hotherLeft
  have hselectedSide :
      labels (dartOrbitFace RS
          (selected.chordDart hpath hregular selectedPosition)) =
        labels (dartOrbitFace RS (backwardDart otherPosition)) :=
    labels_chordDart_eq_backwardDart_of_left_inside rotation hrotation
      hpath hregular selectedPosition otherPosition selected other hotherLeft
      labels hexact hleft hmiddle
  have hotherBackwardCut :
      (RS.edgeOf (backwardDart otherPosition)).1 ∈
        boundary.cycleWalk.edges := by
    change (backwardDart otherPosition).edge ∈ boundary.cycleWalk.edges
    exact (List.mem_map).2 ⟨backwardDart otherPosition,
      backwardDart_mem_chordCycle_of_left_inside hpath hregular
        selectedPosition otherPosition selected other hotherLeft hleft hmiddle,
      rfl⟩
  have hselectedChordCut :
      (RS.edgeOf (selected.chordDart hpath hregular selectedPosition)).1 ∈
        boundary.cycleWalk.edges := by
    have hwall := boundary.chordEdge_mem_wall
    rw [boundary.mem_wall_iff_mem_cycleWalk_edges] at hwall
    exact hwall
  have hselectedBackwardNotCut :
      (RS.edgeOf (backwardDart selectedPosition)).1 ∉
        boundary.cycleWalk.edges := by
    apply selected.incidentEdge_not_mem_boundary_cycleWalk_of_coordinate_outside
      hpath hregular selectedPosition (selectedPosition.index - 1)
    · exact Nat.le_trans (Nat.sub_le _ _)
        (Nat.le_of_lt selectedPosition.index_lt_length)
    · left
      have hcoordinate : selectedPosition.index =
          (selected.orderedCoordinates hpath hregular
            selectedPosition).left.val :=
        congrArg Fin.val hselectedLeft
      change selectedPosition.index =
        (selected.orderedCoordinates hpath hregular
          selectedPosition).left.val at hcoordinate
      rw [← hcoordinate]
      exact Nat.sub_lt (Nat.pos_of_ne_zero selectedPosition.index_ne_zero)
        Nat.zero_lt_one
    · change path.getVert (selectedPosition.index - 1) ∈
        s(selectedPosition.vertex, selectedPosition.previousVertex)
      rw [Sym2.mem_iff]
      exact Or.inr rfl
  have hotherChordNotCut :
      (RS.edgeOf (other.chordDart hpath hregular otherPosition)).1 ∉
        boundary.cycleWalk.edges := by
    apply selected.incidentEdge_not_mem_boundary_cycleWalk_of_coordinate_outside
      hpath hregular selectedPosition other.otherPosition.val
    · exact Nat.le_of_lt_succ other.otherPosition.isLt
    · right
      have hotherRight := congrArg Fin.val
        (other.otherPosition_eq_right_of_isLeftEndpoint
          hpath hregular otherPosition hotherLeft)
      change other.otherPosition.val =
        (other.orderedCoordinates hpath hregular otherPosition).right.val
          at hotherRight
      rw [hotherRight]
      exact hright
    · have hotherRight :=
        other.otherPosition_eq_right_of_isLeftEndpoint
          hpath hregular otherPosition hotherLeft
      change path.getVert other.otherPosition.val ∈
        s(path.getVert
            (other.orderedCoordinates hpath hregular otherPosition).left,
          path.getVert
            (other.orderedCoordinates hpath hregular otherPosition).right)
      rw [Sym2.mem_iff]
      exact Or.inr (congrArg (fun coordinate : Fin (path.length + 1) ↦
        path.getVert coordinate) hotherRight)
  intro hsame
  rcases attachmentTurn_cases rotation hpath hregular selectedPosition with
      hselectedTurn | hselectedTurn
  · have hotherTurn :
        attachmentTurn rotation hpath hregular otherPosition =
          .backwardToAttachment := hsame.symm ▸ hselectedTurn
    have hotherRotation :=
      rotationCycle_of_attachmentTurn_eq_backwardToAttachment rotation hcyclic
        hpath hregular otherPosition hotherTurn
    have hcutNe := (hexact (backwardDart otherPosition)).2 hotherBackwardCut
    rw [dartOrbitFace_alpha_eq_dartOrbitFace_rho
      rotation.toRotationSystem (backwardDart otherPosition)] at hcutNe
    change labels (dartOrbitFace rotation.toRotationSystem
        (backwardDart otherPosition)) ≠
      labels (dartOrbitFace rotation.toRotationSystem
        (rotation.vertexRotation (backwardDart otherPosition))) at hcutNe
    rw [hotherRotation.1, hotherAttachment] at hcutNe
    have hselectedTransport := labels_eq_rho_of_not_cut
      rotation.toRotationSystem labels
      (fun edge : G.edgeSet ↦ edge.1 ∈ boundary.cycleWalk.edges)
      hexact (backwardDart selectedPosition) hselectedBackwardNotCut
    change labels (dartOrbitFace rotation.toRotationSystem
        (backwardDart selectedPosition)) =
      labels (dartOrbitFace rotation.toRotationSystem
        (rotation.vertexRotation
          (backwardDart selectedPosition))) at hselectedTransport
    have hselectedRotation :=
      rotationCycle_of_attachmentTurn_eq_backwardToAttachment rotation hcyclic
        hpath hregular selectedPosition hselectedTurn
    rw [hselectedRotation.1, hselectedAttachment] at hselectedTransport
    dsimp [RS] at hselectedSide
    exact hcutNe (hselectedSide.symm.trans
      (hselectedTransport.symm.trans hanchor.symm))
  · have hotherTurn :
        attachmentTurn rotation hpath hregular otherPosition =
          .forwardToAttachment := hsame.symm ▸ hselectedTurn
    have hselectedRotation :=
      rotationCycle_of_attachmentTurn_eq_forwardToAttachment rotation hcyclic
        hpath hregular selectedPosition hselectedTurn
    have hotherRotation :=
      rotationCycle_of_attachmentTurn_eq_forwardToAttachment rotation hcyclic
        hpath hregular otherPosition hotherTurn
    have hselectedAttachmentCut :
        (rotation.toRotationSystem.edgeOf
          (attachmentDart hpath hregular selectedPosition)).1 ∈
            boundary.cycleWalk.edges := by
      rw [hselectedAttachment]
      exact hselectedChordCut
    have hselectedCutNe :=
      (hexact (attachmentDart hpath hregular selectedPosition)).2
        hselectedAttachmentCut
    rw [dartOrbitFace_alpha_eq_dartOrbitFace_rho
      rotation.toRotationSystem
        (attachmentDart hpath hregular selectedPosition)] at hselectedCutNe
    change labels (dartOrbitFace rotation.toRotationSystem
        (attachmentDart hpath hregular selectedPosition)) ≠
      labels (dartOrbitFace rotation.toRotationSystem
        (rotation.vertexRotation
          (attachmentDart hpath hregular selectedPosition))) at hselectedCutNe
    rw [hselectedRotation.2.2] at hselectedCutNe
    have hotherAttachmentNotCut :
        (rotation.toRotationSystem.edgeOf
          (attachmentDart hpath hregular otherPosition)).1 ∉
            boundary.cycleWalk.edges := by
      rw [hotherAttachment]
      exact hotherChordNotCut
    have hotherTransport := labels_eq_rho_of_not_cut
      rotation.toRotationSystem labels
      (fun edge : G.edgeSet ↦ edge.1 ∈ boundary.cycleWalk.edges)
      hexact (attachmentDart hpath hregular otherPosition)
      hotherAttachmentNotCut
    change labels (dartOrbitFace rotation.toRotationSystem
        (attachmentDart hpath hregular otherPosition)) =
      labels (dartOrbitFace rotation.toRotationSystem
        (rotation.vertexRotation
          (attachmentDart hpath hregular otherPosition))) at hotherTransport
    rw [hotherRotation.2.2] at hotherTransport
    dsimp [RS] at hselectedSide
    have hselectedSide' :
        labels (dartOrbitFace rotation.toRotationSystem
            (attachmentDart hpath hregular selectedPosition)) =
          labels (dartOrbitFace rotation.toRotationSystem
            (backwardDart otherPosition)) := by
      rw [hselectedAttachment]
      exact hselectedSide
    have hanchor' :
        labels (dartOrbitFace rotation.toRotationSystem
            (attachmentDart hpath hregular otherPosition)) =
          labels (dartOrbitFace rotation.toRotationSystem
            (backwardDart selectedPosition)) := by
      rw [hotherAttachment]
      exact hanchor
    exact hselectedCutNe
      (hselectedSide'.trans (hotherTransport.symm.trans hanchor'))

/-- Two canonical chords whose endpoints interleave on one arc of a simple
outer cycle have different cubic attachment turns.  This is the global
noncrossing theorem obtained by composing the local exact-cut rotation
algebra with transport along the complementary outer-cycle arc. -/
theorem attachmentTurn_ne_of_right_interleaving_exactFaceCut_of_pathCycleClosure
    (rotation : Data G)
    (hrotation : VertexRotationCyclic rotation.toRotationSystem)
    {path : G.Walk start finish} (closure : PathCycleClosure path)
    (hpath : path.IsPath) (hregular : G.IsRegularOfDegree 3)
    (selectedPosition otherPosition : InternalPosition path)
    (selected : ChordAttachment hpath hregular selectedPosition)
    (other : ChordAttachment hpath hregular otherPosition)
    (hselectedLeft : selected.IsLeftEndpoint hpath hregular selectedPosition)
    (hotherLeft : other.IsLeftEndpoint hpath hregular otherPosition)
    {A : Type*} (labels : OrbitFace rotation.toRotationSystem → A)
    (hexact : ∀ dart : rotation.toRotationSystem.D,
      labels (dartOrbitFace rotation.toRotationSystem dart) ≠
          labels (dartOrbitFace rotation.toRotationSystem
            (rotation.toRotationSystem.alpha dart)) ↔
        (rotation.toRotationSystem.edgeOf dart).1 ∈
          (selected.boundary hpath hregular selectedPosition).cycleWalk.edges)
    (hleft :
      (selected.orderedCoordinates hpath hregular selectedPosition).left <
        (other.orderedCoordinates hpath hregular otherPosition).left)
    (hmiddle :
      (other.orderedCoordinates hpath hregular otherPosition).left <
        (selected.orderedCoordinates hpath hregular selectedPosition).right)
    (hright :
      (selected.orderedCoordinates hpath hregular selectedPosition).right <
        (other.orderedCoordinates hpath hregular otherPosition).right) :
    attachmentTurn rotation hpath hregular selectedPosition ≠
      attachmentTurn rotation hpath hregular otherPosition := by
  apply attachmentTurn_ne_of_right_interleaving_exactFaceCut
    rotation hrotation hpath hregular selectedPosition otherPosition
      selected other hselectedLeft hotherLeft labels hexact hleft hmiddle
        hright
  exact labels_chordDart_eq_backwardDart_of_exteriorInterval rotation
    hrotation closure hpath hregular selectedPosition otherPosition selected
      other hselectedLeft labels hexact hright

end

end Mettapedia.GraphTheory.Embedding
