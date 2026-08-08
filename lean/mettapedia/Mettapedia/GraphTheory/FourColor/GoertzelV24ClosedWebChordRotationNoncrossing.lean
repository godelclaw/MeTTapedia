import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebChordRotationSector
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebInterleavingChordHoleDrainage
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebLaminarDepth

/-!
# Noncrossing of equal rotation sectors

The rotation bit of an actual same-path chord records the side of the radial
path on which it leaves.  This module connects that local coordinate to the
exact face cut of a selected chord cycle.  The connection turns strict
endpoint interleaving into unequal rotation bits, closing the geometric
interface required by the L6 laminar-depth argument.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebChordRotationNoncrossing

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebChordCycleFaceSideTransport
open GoertzelV24ClosedWebChordHoleSideCutWitness
open GoertzelV24ClosedWebChordRotationSector
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebInterleavingChordHoleDrainage
open GoertzelV24ClosedWebLaminarDepth
open GoertzelV24ClosedWebLengthDepthDichotomy
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChordDiagram
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebRadialPathSectorAnchors
open GoertzelV24FaceCutTransport
open GoertzelV24FaceCutVertexAvoidingTransport
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24SimpleGraphFaceDualConnectedness
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

local instance chordRotationNoncrossingEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- At a position strictly inside a selected chord interval, the dart which
points backward along the radial path is one of the selected cycle darts. -/
theorem leftBackwardDart_mem_cycleWalk_of_inside
    {data : AnnularBoundaryData G outerCount}
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (selected other :
      MajorityChordOnRadialPath C majority first second radial)
    (hdata : data.WellFormed)
    (htriple : IsTaitColorTriple majority first second)
    (hleft : selected.left.val < other.left.val)
    (hright : other.left.val < selected.right.val) :
    MajorityChordOnRadialPath.leftBackwardDart other hdata htriple ∈
      selected.cycleWalk.darts := by
  let offset := other.left.val - 1 - selected.left.val
  have hselectedRight : selected.right.val ≤
      (ambientRadialPath radial).length := by
    rw [ambientRadialPath_length]
    omega
  have hsubarcLength : selected.subarc.length =
      selected.right.val - selected.left.val := by
    exact walkInterval_length (ambientRadialPath radial)
      selected.left selected.right
        (Nat.le_of_lt selected.left_lt_right) hselectedRight
  have hoffset : offset < selected.subarc.darts.length := by
    rw [SimpleGraph.Walk.length_darts, hsubarcLength]
    dsimp [offset]
    omega
  have hdarts : selected.subarc.darts =
      (((ambientRadialPath radial).darts.drop selected.left.val).take
        (selected.right.val - selected.left.val)) := by
    simp only [MajorityChordOnRadialPath.subarc,
      MajorityChordOnRadialPath.chordDart, walkInterval,
      SimpleGraph.Walk.darts_copy]
    rw [SimpleGraph.Walk.darts_take, SimpleGraph.Walk.darts_drop]
  have hoffsetSlice : offset <
      ((((ambientRadialPath radial).darts.drop selected.left.val).take
        (selected.right.val - selected.left.val))).length := by
    rw [← hdarts]
    exact hoffset
  have hdart :
      ((((ambientRadialPath radial).darts.drop selected.left.val).take
        (selected.right.val - selected.left.val)))[offset] =
      (MajorityChordOnRadialPath.leftBackwardDart
        other hdata htriple).symm := by
    rw [List.getElem_take, List.getElem_drop,
      SimpleGraph.Walk.darts_getElem_eq_getVert]
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · change (ambientRadialPath radial).getVert
          (selected.left.val + offset) =
        (ambientRadialPath radial).getVert (other.left.val - 1)
      congr 1
      dsimp [offset]
      omega
    · change (ambientRadialPath radial).getVert
          (selected.left.val + offset + 1) =
        (ambientRadialPath radial).getVert other.left.val
      congr 1
      dsimp [offset]
      omega
  have hsymmMember :
      (MajorityChordOnRadialPath.leftBackwardDart
        other hdata htriple).symm ∈ selected.subarc.darts := by
    rw [hdarts, ← hdart]
    exact List.getElem_mem hoffsetSlice
  have hreverseMember :
      MajorityChordOnRadialPath.leftBackwardDart other hdata htriple ∈
        selected.subarc.reverse.darts :=
    (SimpleGraph.Walk.mem_darts_reverse).2 (by simpa using hsymmMember)
  rw [MajorityChordOnRadialPath.cycleWalk,
    SimpleGraph.Walk.darts_cons]
  simpa only [List.mem_cons] using (Or.inr hreverseMember)

/-- At the interior left endpoint of an interleaving chord, its chord-face
label is the selected cycle-side label indexed by its own rotation bit. -/
theorem labels_chordDart_eq_selectedSide_rotationSector_of_right_interleaving
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (selected other :
      MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (labels : OrbitFace embedded.RS → F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ selected.cycleWalk.edges)
    (hleft : selected.left.val < other.left.val)
    (hmiddle : other.left.val < selected.right.val)
    (hright : selected.right.val < other.right.val) :
    labels (dartOrbitFace embedded.RS other.chordDart) =
      labels (chordSideFace embedded.cellulation
        (selected.boundary htriple)
        (MajorityChordOnRadialPath.rotationSector
          embedded other hdata htriple)) := by
  let backward := MajorityChordOnRadialPath.leftBackwardDart
    other hdata htriple
  let forward := MajorityChordOnRadialPath.leftForwardDart
    other hdata htriple
  have hbackwardMem : backward ∈ selected.cycleWalk.darts :=
    leftBackwardDart_mem_cycleWalk_of_inside selected other hdata htriple
      hleft hmiddle
  have hsideTransport :=
    labels_eq_chordSideFace_dartSide_of_mem_exact_chordCycle_cut
      embedded hdata selected htriple labels hexact
        (MajorityChordOnRadialPath.rotationSector
          embedded other hdata htriple) backward hbackwardMem
  by_cases hsector : MajorityChordOnRadialPath.rotationSector
      embedded other hdata htriple = true
  · have hrotation : VertexRotationCyclic embedded.RS :=
      hasCyclicVertexRotations_implies_vertexRotationCyclic
        G embedded.cellulation.rotation
          embedded.cellulation.vertexRotation_cyclic
    have hotherChordMem : other.chordDart ∈ other.cycleWalk.darts := by
      simp [MajorityChordOnRadialPath.cycleWalk]
    have hcard := cycleWalk_dartsAt_card_eq_three
      embedded hdata other htriple other.chordDart hotherChordMem
    have hrotForward : embedded.RS.rho other.chordDart = forward := by
      simpa [forward] using
        (MajorityChordOnRadialPath.rotationSector_eq_true_iff
          embedded other hdata htriple).1 hsector
    have hrotBackward : embedded.RS.rho backward = other.chordDart :=
      (embedded.RS.rho_three_cycle_of_eq_second_of_card_dartsAt_eq_three
        hrotation (first := other.chordDart) (second := forward)
          (third := backward) hcard
          (by simp [forward]) (by simp [backward])
          (MajorityChordOnRadialPath.chordDart_ne_leftForwardDart
            other hdata htriple)
          (MajorityChordOnRadialPath.chordDart_ne_leftBackwardDart
            other hdata htriple)
          (MajorityChordOnRadialPath.leftBackwardDart_ne_leftForwardDart
            other hdata htriple).symm hrotForward).2
    have hface : dartOrbitFace embedded.RS
          (embedded.RS.alpha backward) =
        dartOrbitFace embedded.RS other.chordDart := by
      calc
        dartOrbitFace embedded.RS (embedded.RS.alpha backward) =
            dartOrbitFace embedded.RS
              (embedded.RS.phi (embedded.RS.alpha backward)) :=
          (dartOrbitFace_phi_eq embedded.RS
            (embedded.RS.alpha backward)).symm
        _ = dartOrbitFace embedded.RS other.chordDart := by
          simp [RotationSystem.phi_apply, hrotBackward]
    have htransport :
        labels (chordSideFace embedded.cellulation
            (selected.boundary htriple) true) =
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha backward)) := by
      simpa [hsector] using hsideTransport
    simpa [hsector] using
      ((congrArg labels hface).symm.trans htransport.symm)
  · have hsectorFalse : MajorityChordOnRadialPath.rotationSector
        embedded other hdata htriple = false := by
      exact Bool.eq_false_of_not_eq_true hsector
    have hrotBackward : embedded.RS.rho other.chordDart = backward := by
      simpa [backward] using
        (MajorityChordOnRadialPath.rotationSector_eq_false_iff
          embedded other hdata htriple).1 hsectorFalse
    have hface : dartOrbitFace embedded.RS
          (embedded.RS.alpha other.chordDart) =
        dartOrbitFace embedded.RS backward := by
      calc
        dartOrbitFace embedded.RS (embedded.RS.alpha other.chordDart) =
            dartOrbitFace embedded.RS
              (embedded.RS.phi (embedded.RS.alpha other.chordDart)) :=
          (dartOrbitFace_phi_eq embedded.RS
            (embedded.RS.alpha other.chordDart)).symm
        _ = dartOrbitFace embedded.RS backward := by
          simp [RotationSystem.phi_apply, hrotBackward]
    have hotherNotCut :
        (embedded.RS.edgeOf other.chordDart).1 ∉
          selected.cycleWalk.edges := by
      apply incidentEdge_not_mem_cycleWalk_of_position_outside selected
        htriple other.right.val
          (Nat.le_of_lt (other.right_lt_length hdata htriple))
          (Or.inr hright) (embedded.RS.edgeOf other.chordDart)
      change (ambientRadialPath radial).getVert other.right.val ∈
        other.chordDart.edge
      simp [MajorityChordOnRadialPath.chordDart,
        SimpleGraph.Dart.edge]
    have hcross := labels_eq_alpha_of_not_cut embedded.RS labels
      (fun edge => edge.1 ∈ selected.cycleWalk.edges)
        hexact other.chordDart hotherNotCut
    have htransport :
        labels (chordSideFace embedded.cellulation
            (selected.boundary htriple) false) =
          labels (dartOrbitFace embedded.RS backward) := by
      simpa [hsectorFalse] using hsideTransport
    simpa [hsectorFalse] using
      (hcross.trans ((congrArg labels hface).trans htransport.symm))

/-- The side opposite the rotation bit opens toward the radial prefix and
therefore carries the inner-hole label.  Equivalently, the rotation bit is
the side cut off from both holes. -/
theorem labels_chordSideFace_not_rotationSector_eq_innerHole
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath
      C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (labels : OrbitFace embedded.RS → F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges) :
    labels (chordSideFace embedded.cellulation
        (chord.boundary htriple)
        (!(MajorityChordOnRadialPath.rotationSector
          embedded chord hdata htriple))) =
      labels embedded.cellulation.innerHole := by
  let ambient := ambientRadialPath radial
  let initialSegment := ambient.take chord.left.val
  let backward := MajorityChordOnRadialPath.leftBackwardDart
    chord hdata htriple
  let forward := MajorityChordOnRadialPath.leftForwardDart
    chord hdata htriple
  have hleftPos : 0 < chord.left.val := chord.left_pos hdata htriple
  have hleftBound : chord.left.val ≤ ambient.length := by
    simp [ambient, ambientRadialPath_length]
    omega
  have hleftPathBound : chord.left.val ≤ radial.path.length := by
    simpa [ambient, ambientRadialPath_length] using hleftBound
  have hprefixNonempty : ¬initialSegment.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    simp [initialSegment, SimpleGraph.Walk.take_length,
      Nat.min_eq_left hleftBound, hleftPos]
  have hambientNonempty : ¬ambient.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    exact lt_of_lt_of_le hleftPos hleftBound
  have hfirstDart : initialSegment.firstDart hprefixNonempty =
      ambient.firstDart hambientNonempty := by
    exact firstDart_take_eq_firstDart ambient chord.left.val
      hleftPos hleftBound
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  have hprefixAvoids :
      ∀ based ∈ initialSegment.darts, ∀ incident : G.Dart,
        incident.fst = based.fst →
          (embedded.RS.edgeOf incident).1 ∉ chord.cycleWalk.edges := by
    intro based hbased incident hincident
    rcases exists_position_lt_of_mem_darts_take
        ambient chord.left.val hleftBound based hbased with
      ⟨position, hposition, hbasedPosition⟩
    apply incidentEdge_not_mem_cycleWalk_of_position_outside chord
      htriple position
      (by
        rw [← ambientRadialPath_length radial]
        exact le_trans (Nat.le_of_lt hposition) hleftBound)
      (Or.inl hposition) (embedded.RS.edgeOf incident)
    change ambient.getVert position ∈ incident.edge
    rw [← hbasedPosition, ← hincident]
    simp [SimpleGraph.Dart.edge]
  have hprefixTransport :=
    walk_labels_eq_firstDart_alpha_lastDart_of_vertices_avoid_cut
      embedded.cellulation.rotation hrotation labels
        (fun edge => edge.1 ∈ chord.cycleWalk.edges)
        hexact initialSegment hprefixNonempty hprefixAvoids
  have hfirstFace : dartOrbitFace embedded.RS
        (initialSegment.firstDart hprefixNonempty) =
      embedded.cellulation.innerHole := by
    rw [hfirstDart]
    apply embedded.innerBoundaryEdgeDarts_on_innerHole radial.inner
    apply (embedded.RS.mem_dartsOn).2
    apply Subtype.ext
    exact ambientRadialPath_firstDart_edgeOf_eq_innerBoundaryEdge
      hdata radial hambientNonempty
  have hlastBackward : embedded.RS.alpha
        (initialSegment.lastDart hprefixNonempty) = backward := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · change (initialSegment.lastDart hprefixNonempty).snd =
        (ambientRadialPath radial).getVert chord.left.val
      simp [initialSegment, ambient, SimpleGraph.Walk.lastDart,
        Nat.min_eq_left hleftPathBound]
    · change (initialSegment.lastDart hprefixNonempty).fst =
        (ambientRadialPath radial).getVert (chord.left.val - 1)
      simp [initialSegment, ambient, SimpleGraph.Walk.lastDart,
        Nat.min_eq_left hleftPathBound]
  have hinnerBackward : labels embedded.cellulation.innerHole =
      labels (dartOrbitFace embedded.RS backward) := by
    calc
      labels embedded.cellulation.innerHole =
          labels (dartOrbitFace embedded.RS
            (initialSegment.firstDart hprefixNonempty)) :=
        (congrArg labels hfirstFace).symm
      _ = labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha
              (initialSegment.lastDart hprefixNonempty))) := hprefixTransport
      _ = labels (dartOrbitFace embedded.RS backward) := by
        rw [hlastBackward]
  by_cases hsector : MajorityChordOnRadialPath.rotationSector
      embedded chord hdata htriple = true
  · have hchordMem : chord.chordDart ∈ chord.cycleWalk.darts := by
      simp [MajorityChordOnRadialPath.cycleWalk]
    have hcard := cycleWalk_dartsAt_card_eq_three
      embedded hdata chord htriple chord.chordDart hchordMem
    have hrotForward : embedded.RS.rho chord.chordDart = forward := by
      simpa [forward] using
        (MajorityChordOnRadialPath.rotationSector_eq_true_iff
          embedded chord hdata htriple).1 hsector
    have hrotBackward : embedded.RS.rho backward = chord.chordDart :=
      (embedded.RS.rho_three_cycle_of_eq_second_of_card_dartsAt_eq_three
        hrotation (first := chord.chordDart) (second := forward)
          (third := backward) hcard
          (by simp [forward]) (by simp [backward])
          (MajorityChordOnRadialPath.chordDart_ne_leftForwardDart
            chord hdata htriple)
          (MajorityChordOnRadialPath.chordDart_ne_leftBackwardDart
            chord hdata htriple)
          (MajorityChordOnRadialPath.leftBackwardDart_ne_leftForwardDart
            chord hdata htriple).symm hrotForward).2
    have hface : dartOrbitFace embedded.RS
          (embedded.RS.alpha backward) =
        dartOrbitFace embedded.RS chord.chordDart := by
      calc
        dartOrbitFace embedded.RS (embedded.RS.alpha backward) =
            dartOrbitFace embedded.RS
              (embedded.RS.phi (embedded.RS.alpha backward)) :=
          (dartOrbitFace_phi_eq embedded.RS
            (embedded.RS.alpha backward)).symm
        _ = dartOrbitFace embedded.RS chord.chordDart := by
          simp [RotationSystem.phi_apply, hrotBackward]
    have hbackwardNotCut :
        (embedded.RS.edgeOf backward).1 ∉ chord.cycleWalk.edges := by
      apply incidentEdge_not_mem_cycleWalk_of_position_outside chord
        htriple (chord.left.val - 1)
          (by omega)
          (Or.inl (by omega)) (embedded.RS.edgeOf backward)
      change (ambientRadialPath radial).getVert (chord.left.val - 1) ∈
        backward.edge
      simp [backward, MajorityChordOnRadialPath.leftBackwardDart,
        SimpleGraph.Dart.edge]
    have hbackwardCross := labels_eq_alpha_of_not_cut
      embedded.RS labels (fun edge => edge.1 ∈ chord.cycleWalk.edges)
        hexact backward hbackwardNotCut
    have hresult : labels (dartOrbitFace embedded.RS chord.chordDart) =
        labels embedded.cellulation.innerHole :=
      (congrArg labels hface).symm.trans
        (hbackwardCross.symm.trans hinnerBackward.symm)
    simpa [hsector, chordSideFace,
      MajorityChordOnRadialPath.boundary] using hresult
  · have hsectorFalse : MajorityChordOnRadialPath.rotationSector
        embedded chord hdata htriple = false :=
      Bool.eq_false_of_not_eq_true hsector
    have hrotBackward : embedded.RS.rho chord.chordDart = backward := by
      simpa [backward] using
        (MajorityChordOnRadialPath.rotationSector_eq_false_iff
          embedded chord hdata htriple).1 hsectorFalse
    have hface : dartOrbitFace embedded.RS
          (embedded.RS.alpha chord.chordDart) =
        dartOrbitFace embedded.RS backward := by
      calc
        dartOrbitFace embedded.RS (embedded.RS.alpha chord.chordDart) =
            dartOrbitFace embedded.RS
              (embedded.RS.phi (embedded.RS.alpha chord.chordDart)) :=
          (dartOrbitFace_phi_eq embedded.RS
            (embedded.RS.alpha chord.chordDart)).symm
        _ = dartOrbitFace embedded.RS backward := by
          simp [RotationSystem.phi_apply, hrotBackward]
    have hresult :
        labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha chord.chordDart)) =
          labels embedded.cellulation.innerHole :=
      (congrArg labels hface).trans hinnerBackward.symm
    simpa [hsectorFalse, chordSideFace,
      MajorityChordOnRadialPath.boundary] using hresult

/-! The previous face-label theorem identifies the intrinsic sector.  The
next lemma supplies the corresponding primal-side transport for an actual
cyclic cut.  Its geometric input is deliberately only the support fact that
the listed cut edges lie on the chord cycle; the radial-prefix avoidance is
proved from the existing chord-cycle support lemmas.  In particular, this does
not confuse the primal crossing-port set with the whole facial wall. -/

theorem CyclicEdgeCutRealization.side_iff_of_radial_prefix_of_edgeCut_subset_cycle
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath
      C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (hcut : ∀ e : G.edgeSet, e ∈ edgeCut →
      e.1 ∈ chord.cycleWalk.edges) :
    realization.side radial.start.1 ↔
      realization.side ((ambientRadialPath radial).getVert chord.left.val) := by
  let ambient := ambientRadialPath radial
  let initialSegment := ambient.take chord.left.val
  have hleftPos : 0 < chord.left.val := chord.left_pos hdata htriple
  have hleftBound : chord.left.val ≤ ambient.length := by
    simp [ambient, ambientRadialPath_length]
    omega
  have hprefixNonempty : ¬initialSegment.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    simp [initialSegment, SimpleGraph.Walk.take_length,
      Nat.min_eq_left hleftBound, hleftPos]
  have hprefixAvoids :
      ∀ based ∈ initialSegment.darts, ∀ incident : G.Dart,
        incident.fst = based.fst →
          (⟨incident.edge, incident.edge_mem⟩ : G.edgeSet) ∉ edgeCut := by
    intro based hbased incident hincident
    rcases exists_position_lt_of_mem_darts_take
        ambient chord.left.val hleftBound based hbased with
      ⟨position, hposition, hbasedPosition⟩
    have hnotCycle :
        (embedded.RS.edgeOf incident).1 ∉ chord.cycleWalk.edges := by
      apply incidentEdge_not_mem_cycleWalk_of_position_outside chord
        htriple position
        (by
          rw [← ambientRadialPath_length radial]
          exact le_trans (Nat.le_of_lt hposition) hleftBound)
        (Or.inl hposition) (embedded.RS.edgeOf incident)
      change ambient.getVert position ∈ incident.edge
      rw [← hbasedPosition, ← hincident]
      simp [SimpleGraph.Dart.edge]
    intro hcutEdge
    exact hnotCycle <| hcut _ hcutEdge
  have hside := realization.side_iff_of_walk_darts_avoid_edgeCut
    initialSegment hprefixAvoids
  simpa [initialSegment, ambient] using hside

/-- Any selected side whose exact-cut label differs from the common hole
label is necessarily the intrinsic rotation sector of the chord. -/
theorem side_eq_rotationSector_of_label_ne_innerHole
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath
      C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (labels : OrbitFace embedded.RS → F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    (side : Bool)
    (hside : labels (chordSideFace embedded.cellulation
        (chord.boundary htriple) side) ≠
      labels embedded.cellulation.innerHole) :
    side = MajorityChordOnRadialPath.rotationSector
      embedded chord hdata htriple := by
  have hopposite :=
    labels_chordSideFace_not_rotationSector_eq_innerHole
      embedded hdata chord htriple labels hexact
  cases side <;>
    cases hsector : MajorityChordOnRadialPath.rotationSector
      embedded chord hdata htriple
  · rfl
  · exfalso
    apply hside
    simpa [hsector] using hopposite
  · exfalso
    apply hside
    simpa [hsector] using hopposite
  · rfl

/-- If the selected chord starts first and the two endpoint intervals
strictly interleave, their intrinsic rotation sectors are different. -/
theorem rotationSector_ne_of_right_interleaving
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (selected other : MajorityChordOnRadialPath
      C majority first second pair.firstPath)
    (htriple : IsTaitColorTriple majority first second)
    (hleft : selected.left.val < other.left.val)
    (hmiddle : other.left.val < selected.right.val)
    (hright : selected.right.val < other.right.val) :
    MajorityChordOnRadialPath.rotationSector
        embedded selected hdata htriple ≠
      MajorityChordOnRadialPath.rotationSector
        embedded other hdata htriple := by
  rcases exists_exact_chordCycle_faceCut_with_holeFreeSide
      embedded hdata pair selected htriple with
    ⟨labels, side, _hboundary, hexact, hholes, hside,
      _hholeFree⟩
  have hsideEq := side_eq_rotationSector_of_label_ne_innerHole
    embedded hdata selected htriple labels hexact side hside
  have hlocal :=
    labels_chordDart_eq_selectedSide_rotationSector_of_right_interleaving
      embedded hdata selected other htriple labels hexact
        hleft hmiddle hright
  have houter := labels_chordDart_eq_outerHole_of_right_after
    embedded hdata selected other htriple labels hexact hright
  have hinner : labels (dartOrbitFace embedded.RS other.chordDart) =
      labels embedded.cellulation.innerHole := houter.trans hholes.symm
  intro hequal
  apply hside
  rw [hsideEq, hequal]
  exact hlocal.symm.trans hinner

/-- Strictly interleaving actual chords always have opposite rotation
sectors, whichever chord starts first. -/
theorem rotationSector_ne_of_interleaving
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (firstChord secondChord : MajorityChordOnRadialPath
      C majority first second pair.firstPath)
    (htriple : IsTaitColorTriple majority first second)
    (hinterleave :
      (firstChord.left.val < secondChord.left.val ∧
        secondChord.left.val < firstChord.right.val ∧
        firstChord.right.val < secondChord.right.val) ∨
      (secondChord.left.val < firstChord.left.val ∧
        firstChord.left.val < secondChord.right.val ∧
        secondChord.right.val < firstChord.right.val)) :
    MajorityChordOnRadialPath.rotationSector
        embedded firstChord hdata htriple ≠
      MajorityChordOnRadialPath.rotationSector
        embedded secondChord hdata htriple := by
  rcases hinterleave with hright | hleft
  · exact rotationSector_ne_of_right_interleaving
      embedded hdata pair firstChord secondChord htriple
        hright.1 hright.2.1 hright.2.2
  · intro hequal
    exact rotationSector_ne_of_right_interleaving
      embedded hdata pair secondChord firstChord htriple
        hleft.1 hleft.2.1 hleft.2.2 hequal.symm

/-- The intrinsic position-level rotation coordinate supplies the exact
`SameSectorNoncrossing` interface required by the laminar-depth module. -/
theorem firstPath_positionRotationSector_sameSectorNoncrossing
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second) :
    SameSectorNoncrossing C majority first second pair.firstPath
      (positionRotationSector embedded hdata pair.firstPath htriple) := by
  intro firstPosition hfirst secondPosition hsecond _hne hsamesector
  intro hcrosses
  let hfirstData := (mem_majorityChordDiagram_iff).1 hfirst
  let hsecondData := (mem_majorityChordDiagram_iff).1 hsecond
  let firstChord := majorityChordOfPosition firstPosition hfirstData
  let secondChord := majorityChordOfPosition secondPosition hsecondData
  have hinterleave :
      (firstChord.left.val < secondChord.left.val ∧
        secondChord.left.val < firstChord.right.val ∧
        firstChord.right.val < secondChord.right.val) ∨
      (secondChord.left.val < firstChord.left.val ∧
        firstChord.left.val < secondChord.right.val ∧
        secondChord.right.val < firstChord.right.val) := by
    simpa [firstChord, secondChord, hfirstData, hsecondData,
      majorityChordOfPosition,
      OrderedPathChord.Crosses] using hcrosses
  have hneSectors := rotationSector_ne_of_interleaving
    embedded hdata pair firstChord secondChord htriple hinterleave
  have hfirstSector := positionRotationSector_eq_rotationSector
    embedded hdata pair.firstPath htriple firstPosition hfirst
  have hsecondSector := positionRotationSector_eq_rotationSector
    embedded hdata pair.firstPath htriple secondPosition hsecond
  apply hneSectors
  simpa [firstChord, secondChord, hfirstData, hsecondData,
    majorityChordOfPosition]
    using hfirstSector.symm.trans (hsamesector.trans hsecondSector)

/-- The high-load branch now yields a large laminar family with no external
sector or noncrossing premise. -/
theorem exists_large_laminar_rotationSector_of_hasDeepChordTransversal
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second)
    (depthBound : Nat)
    (hdeep : HasDeepChordTransversal C majority first second
      pair.firstPath (2 * depthBound)) :
    ∃ (cut : Fin pair.firstPath.path.length) (side : Bool),
      depthBound <
        (sectorSpanningChords C majority first second pair.firstPath
          (positionRotationSector embedded hdata pair.firstPath htriple)
          side cut).card ∧
      PairwiseLaminar
        (sectorSpanningChords C majority first second pair.firstPath
          (positionRotationSector embedded hdata pair.firstPath htriple)
          side cut) := by
  exact exists_large_laminar_sector_of_hasDeepChordTransversal
    C majority first second pair.firstPath
      (positionRotationSector embedded hdata pair.firstPath htriple)
      (firstPath_positionRotationSector_sameSectorNoncrossing
        embedded hdata pair htriple) depthBound hdeep

/-- Source-facing L6 dichotomy on the first radial path: a sufficiently long
path contains either a clean shallow block or an explicitly large laminar
rotation-sector family. -/
theorem hasShallowRadialCorridor_or_exists_large_laminar_rotationSector
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (htriple : IsTaitColorTriple majority first second)
    (badPositions : Finset (Fin pair.firstPath.path.length))
    (defectBudget depthBound blockLength : Nat)
    (hblockLength : 0 < blockLength)
    (hbad : badPositions.card ≤ defectBudget)
    (hprefix :
      (defectBudget + 1) * blockLength ≤ pair.firstPath.path.length) :
    HasShallowRadialCorridor C majority first second pair.firstPath
        badPositions defectBudget (2 * depthBound) blockLength ∨
      ∃ (cut : Fin pair.firstPath.path.length) (side : Bool),
        depthBound <
          (sectorSpanningChords C majority first second pair.firstPath
            (positionRotationSector embedded hdata pair.firstPath htriple)
            side cut).card ∧
        PairwiseLaminar
          (sectorSpanningChords C majority first second pair.firstPath
            (positionRotationSector embedded hdata pair.firstPath htriple)
            side cut) := by
  rcases hasShallowRadialCorridor_or_hasDeepChordTransversal
      C majority first second pair.firstPath badPositions defectBudget
        (2 * depthBound) blockLength hblockLength hbad hprefix with
    hshallow | hdeep
  · exact Or.inl hshallow
  · exact Or.inr <|
      exists_large_laminar_rotationSector_of_hasDeepChordTransversal
        embedded hdata pair htriple depthBound hdeep

end

end GoertzelV24ClosedWebChordRotationNoncrossing

end Mettapedia.GraphTheory.FourColor
