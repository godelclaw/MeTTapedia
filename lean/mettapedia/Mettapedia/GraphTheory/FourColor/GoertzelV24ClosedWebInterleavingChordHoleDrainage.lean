import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebChordHoleSideCutWitness

/-!
# Hole-side drainage for interleaving same-path chords

An endpoint lying strictly outside a selected chord interval can be joined to
the corresponding annular hole along a radial prefix or suffix whose based
vertices all avoid the selected chord cycle.  Exact-cut transport along that
actual walk, followed by the other chord edge, places the other endpoint on
the common hole side.

This module proves the two directed escape statements before joining them to
an innermost-chord selection or naming the resulting regions as sectors.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebInterleavingChordHoleDrainage

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebChordHoleSideCutWitness
open GoertzelV24ClosedWebChordCycleFaceSideTransport
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebRadialPathSectorAnchors
open GoertzelV24FaceCutTransport
open GoertzelV24FaceCutVertexAvoidingTransport
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceParityBoundary
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

local instance interleavingDrainageGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A dart based in the first `bound` edges of a walk has a unique based
position strictly below `bound`. -/
theorem exists_position_lt_of_mem_darts_take
    {start finish : V} (walk : G.Walk start finish)
    (bound : Nat) (hbound : bound ≤ walk.length)
    (dart : G.Dart) (hdart : dart ∈ (walk.take bound).darts) :
    ∃ position : Nat, position < bound ∧
      dart.fst = walk.getVert position := by
  rcases List.mem_iff_getElem.mp hdart with ⟨position, hposition, rfl⟩
  have hpositionBound : position < bound := by
    simpa [SimpleGraph.Walk.length_darts,
      SimpleGraph.Walk.take_length, Nat.min_eq_left hbound] using hposition
  refine ⟨position, hpositionBound, ?_⟩
  rw [SimpleGraph.Walk.darts_getElem_eq_getVert]
  simp [SimpleGraph.Walk.take_getVert,
    Nat.min_eq_right (Nat.le_of_lt hpositionBound)]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Taking a positive prefix preserves the first oriented dart. -/
theorem firstDart_take_eq_firstDart
    {start finish : V} (walk : G.Walk start finish)
    (bound : Nat) (hpositive : 0 < bound) (hbound : bound ≤ walk.length) :
    (walk.take bound).firstDart (by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length]
        simp [SimpleGraph.Walk.take_length, Nat.min_eq_left hbound,
          hpositive]) =
      walk.firstDart (by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length]
        exact lt_of_lt_of_le hpositive hbound) := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · simp [SimpleGraph.Walk.firstDart,
      SimpleGraph.Walk.take_getVert,
      Nat.min_eq_right (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt hpositive))]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- A dart based in a dropped suffix occurs at an original walk position at
or after the drop point and still strictly before the original finish. -/
theorem exists_position_ge_of_mem_darts_drop
    {start finish : V} (walk : G.Walk start finish)
    (bound : Nat) (hbound : bound ≤ walk.length)
    (dart : G.Dart) (hdart : dart ∈ (walk.drop bound).darts) :
    ∃ position : Nat, bound ≤ position ∧ position < walk.length ∧
      dart.fst = walk.getVert position := by
  rcases List.mem_iff_getElem.mp hdart with ⟨offset, hoffset, rfl⟩
  have hoffsetBound : offset < walk.length - bound := by
    simpa [SimpleGraph.Walk.length_darts,
      SimpleGraph.Walk.drop_length] using hoffset
  refine ⟨bound + offset, Nat.le_add_right _ _, by omega, ?_⟩
  rw [SimpleGraph.Walk.darts_getElem_eq_getVert]
  simp [SimpleGraph.Walk.drop_getVert]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Dropping a proper prefix preserves the final oriented dart. -/
theorem lastDart_drop_eq_lastDart
    {start finish : V} (walk : G.Walk start finish)
    (bound : Nat) (hbound : bound < walk.length) :
    (walk.drop bound).lastDart (by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length,
          SimpleGraph.Walk.drop_length]
        omega) =
      walk.lastDart (by
        rw [SimpleGraph.Walk.not_nil_iff_lt_length]
        omega) := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · change (walk.drop bound).penultimate = walk.penultimate
    simp only [SimpleGraph.Walk.penultimate,
      SimpleGraph.Walk.drop_length,
      SimpleGraph.Walk.drop_getVert]
    congr 1
    omega
  · rfl

/-- If another actual chord starts strictly before the selected chord
interval, the face on the far side of that oriented chord is on the inner
hole side of the selected exact cycle cut. -/
theorem labels_alpha_chordDart_eq_innerHole_of_left_before
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
    (hbefore : other.left.val < selected.left.val) :
    labels (dartOrbitFace embedded.RS
        (embedded.RS.alpha other.chordDart)) =
      labels embedded.cellulation.innerHole := by
  let ambient := ambientRadialPath radial
  let escapePrefix := ambient.take other.left.val
  have hotherLeftPos : 0 < other.left.val :=
    other.left_pos hdata htriple
  have hotherLeftBound : other.left.val ≤ radial.path.length := by
    have := other.left.isLt
    omega
  have hambientBound : other.left.val ≤ ambient.length := by
    simpa [ambient, ambientRadialPath_length] using hotherLeftBound
  have hprefixNonempty : ¬escapePrefix.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    simp [escapePrefix, SimpleGraph.Walk.take_length,
      Nat.min_eq_left hambientBound, hotherLeftPos]
  have hambientNonempty : ¬ambient.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    exact lt_of_lt_of_le hotherLeftPos hambientBound
  have hfirstDart : escapePrefix.firstDart hprefixNonempty =
      ambient.firstDart hambientNonempty := by
    exact firstDart_take_eq_firstDart ambient other.left.val
      hotherLeftPos hambientBound
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  have hprefixAvoids :
      ∀ based ∈ escapePrefix.darts, ∀ incident : G.Dart,
        incident.fst = based.fst →
          (embedded.RS.edgeOf incident).1 ∉
            selected.cycleWalk.edges := by
    intro based hbased incident hincident
    rcases exists_position_lt_of_mem_darts_take
        ambient other.left.val hambientBound based hbased with
      ⟨position, hposition, hbasedPosition⟩
    apply incidentEdge_not_mem_cycleWalk_of_position_outside selected
      htriple position
      (by
        rw [← ambientRadialPath_length radial]
        exact le_trans (Nat.le_of_lt hposition) hambientBound)
      (Or.inl (lt_trans hposition hbefore))
      (embedded.RS.edgeOf incident)
    change ambient.getVert position ∈ incident.edge
    rw [← hbasedPosition, ← hincident]
    simp [SimpleGraph.Dart.edge]
  have hprefixTransport :=
    walk_labels_eq_firstDart_alpha_lastDart_of_vertices_avoid_cut
      embedded.cellulation.rotation hrotation labels
        (fun edge => edge.1 ∈ selected.cycleWalk.edges)
        hexact escapePrefix hprefixNonempty hprefixAvoids
  have hfirstFace :
      dartOrbitFace embedded.RS (escapePrefix.firstDart hprefixNonempty) =
        embedded.cellulation.innerHole := by
    rw [hfirstDart]
    apply embedded.innerBoundaryEdgeDarts_on_innerHole radial.inner
    apply (embedded.RS.mem_dartsOn).2
    apply Subtype.ext
    exact ambientRadialPath_firstDart_edgeOf_eq_innerBoundaryEdge
      hdata radial hambientNonempty
  have houtsideAll : ∀ dart : embedded.RS.D,
      embedded.RS.vertOf dart =
          embedded.RS.vertOf
            (embedded.RS.alpha (escapePrefix.lastDart hprefixNonempty)) →
        (embedded.RS.edgeOf dart).1 ∉ selected.cycleWalk.edges := by
    intro dart hbase
    apply incidentEdge_not_mem_cycleWalk_of_position_outside selected
      htriple other.left.val hotherLeftBound (Or.inl hbefore)
      (embedded.RS.edgeOf dart)
    change ambient.getVert other.left.val ∈ dart.edge
    have hvertex : dart.fst = ambient.getVert other.left.val := by
      change dart.fst = (escapePrefix.lastDart hprefixNonempty).snd at hbase
      simpa [escapePrefix, ambient, SimpleGraph.Walk.lastDart] using hbase
    rw [← hvertex]
    simp [SimpleGraph.Dart.edge]
  have hturn :
      labels (dartOrbitFace embedded.RS
          (embedded.RS.alpha (escapePrefix.lastDart hprefixNonempty))) =
        labels (dartOrbitFace embedded.RS other.chordDart) := by
    apply labels_eq_of_same_vertex_of_all_edges_not_cut
      embedded.RS hrotation labels
        (fun edge => edge.1 ∈ selected.cycleWalk.edges) hexact
    · change other.chordDart.fst =
        (escapePrefix.lastDart hprefixNonempty).snd
      simp [MajorityChordOnRadialPath.chordDart, escapePrefix, ambient,
        SimpleGraph.Walk.lastDart]
    · exact houtsideAll
  have hotherNotCut :
      (embedded.RS.edgeOf other.chordDart).1 ∉
        selected.cycleWalk.edges := by
    apply incidentEdge_not_mem_cycleWalk_of_position_outside selected
      htriple other.left.val hotherLeftBound (Or.inl hbefore)
      (embedded.RS.edgeOf other.chordDart)
    change ambient.getVert other.left.val ∈ other.chordDart.edge
    simp [ambient, MajorityChordOnRadialPath.chordDart,
      SimpleGraph.Dart.edge]
  have hotherCross := labels_eq_alpha_of_not_cut embedded.RS labels
    (fun edge => edge.1 ∈ selected.cycleWalk.edges)
      hexact other.chordDart hotherNotCut
  calc
    labels (dartOrbitFace embedded.RS
        (embedded.RS.alpha other.chordDart)) =
        labels (dartOrbitFace embedded.RS other.chordDart) :=
      hotherCross.symm
    _ = labels (dartOrbitFace embedded.RS
          (embedded.RS.alpha (escapePrefix.lastDart hprefixNonempty))) :=
      hturn.symm
    _ = labels (dartOrbitFace embedded.RS
          (escapePrefix.firstDart hprefixNonempty)) :=
      hprefixTransport.symm
    _ = labels embedded.cellulation.innerHole := congrArg labels hfirstFace

/-- If another actual chord ends strictly after the selected chord interval,
the face on the near side of that oriented chord is on the outer-hole side of
the selected exact cycle cut. -/
theorem labels_chordDart_eq_outerHole_of_right_after
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
    (hafter : selected.right.val < other.right.val) :
    labels (dartOrbitFace embedded.RS other.chordDart) =
      labels embedded.cellulation.outerHole := by
  let ambient := ambientRadialPath radial
  let escapeSuffix := ambient.drop other.right.val
  have hotherRightBefore : other.right.val < radial.path.length :=
    other.right_lt_length hdata htriple
  have hotherRightBound : other.right.val ≤ ambient.length := by
    simpa [ambient, ambientRadialPath_length] using
      Nat.le_of_lt hotherRightBefore
  have hotherRightBeforeAmbient : other.right.val < ambient.length := by
    simpa [ambient, ambientRadialPath_length] using hotherRightBefore
  have hsuffixNonempty : ¬escapeSuffix.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    simp [escapeSuffix, SimpleGraph.Walk.drop_length]
    omega
  have hambientNonempty : ¬ambient.Nil := by
    rw [SimpleGraph.Walk.not_nil_iff_lt_length]
    omega
  have hlastDart : escapeSuffix.lastDart hsuffixNonempty =
      ambient.lastDart hambientNonempty := by
    exact lastDart_drop_eq_lastDart ambient other.right.val
      hotherRightBeforeAmbient
  have hrotation : VertexRotationCyclic embedded.RS :=
    hasCyclicVertexRotations_implies_vertexRotationCyclic
      G embedded.cellulation.rotation
        embedded.cellulation.vertexRotation_cyclic
  have hsuffixAvoids :
      ∀ based ∈ escapeSuffix.darts, ∀ incident : G.Dart,
        incident.fst = based.fst →
          (embedded.RS.edgeOf incident).1 ∉
            selected.cycleWalk.edges := by
    intro based hbased incident hincident
    rcases exists_position_ge_of_mem_darts_drop
        ambient other.right.val hotherRightBound based hbased with
      ⟨position, hposition, hpositionEnd, hbasedPosition⟩
    apply incidentEdge_not_mem_cycleWalk_of_position_outside selected
      htriple position
      (by
        rw [← ambientRadialPath_length radial]
        exact Nat.le_of_lt hpositionEnd)
      (Or.inr (lt_of_lt_of_le hafter hposition))
      (embedded.RS.edgeOf incident)
    change ambient.getVert position ∈ incident.edge
    rw [← hbasedPosition, ← hincident]
    simp [SimpleGraph.Dart.edge]
  have hsuffixTransport :=
    walk_labels_eq_firstDart_alpha_lastDart_of_vertices_avoid_cut
      embedded.cellulation.rotation hrotation labels
        (fun edge => edge.1 ∈ selected.cycleWalk.edges)
        hexact escapeSuffix hsuffixNonempty hsuffixAvoids
  have hlastFace :
      dartOrbitFace embedded.RS
          (embedded.RS.alpha
            (escapeSuffix.lastDart hsuffixNonempty)) =
        embedded.cellulation.outerHole := by
    rw [hlastDart]
    apply embedded.outerBoundaryEdgeDarts_on_outerHole radial.outer
    apply (embedded.RS.mem_dartsOn).2
    rw [embedded.RS.edge_alpha]
    apply Subtype.ext
    exact ambientRadialPath_lastDart_edgeOf_eq_outerBoundaryEdge
      hdata radial hambientNonempty
  have houtsideAll : ∀ dart : embedded.RS.D,
      embedded.RS.vertOf dart =
          embedded.RS.vertOf (embedded.RS.alpha other.chordDart) →
        (embedded.RS.edgeOf dart).1 ∉ selected.cycleWalk.edges := by
    intro dart hbase
    apply incidentEdge_not_mem_cycleWalk_of_position_outside selected
      htriple other.right.val (Nat.le_of_lt hotherRightBefore)
      (Or.inr hafter) (embedded.RS.edgeOf dart)
    change ambient.getVert other.right.val ∈ dart.edge
    have hvertex : dart.fst = ambient.getVert other.right.val := by
      change dart.fst = other.chordDart.snd at hbase
      simpa [ambient, MajorityChordOnRadialPath.chordDart] using hbase
    rw [← hvertex]
    simp [SimpleGraph.Dart.edge]
  have hturn :
      labels (dartOrbitFace embedded.RS
          (embedded.RS.alpha other.chordDart)) =
        labels (dartOrbitFace embedded.RS
          (escapeSuffix.firstDart hsuffixNonempty)) := by
    apply labels_eq_of_same_vertex_of_all_edges_not_cut
      embedded.RS hrotation labels
        (fun edge => edge.1 ∈ selected.cycleWalk.edges) hexact
    · change (escapeSuffix.firstDart hsuffixNonempty).fst =
        other.chordDart.snd
      simp [escapeSuffix, ambient,
        MajorityChordOnRadialPath.chordDart,
        SimpleGraph.Walk.firstDart]
    · exact houtsideAll
  have hotherNotCut :
      (embedded.RS.edgeOf other.chordDart).1 ∉
        selected.cycleWalk.edges := by
    apply incidentEdge_not_mem_cycleWalk_of_position_outside selected
      htriple other.right.val (Nat.le_of_lt hotherRightBefore)
      (Or.inr hafter) (embedded.RS.edgeOf other.chordDart)
    change ambient.getVert other.right.val ∈ other.chordDart.edge
    simp [ambient, MajorityChordOnRadialPath.chordDart,
      SimpleGraph.Dart.edge]
  have hotherCross := labels_eq_alpha_of_not_cut embedded.RS labels
    (fun edge => edge.1 ∈ selected.cycleWalk.edges)
      hexact other.chordDart hotherNotCut
  calc
    labels (dartOrbitFace embedded.RS other.chordDart) =
        labels (dartOrbitFace embedded.RS
          (embedded.RS.alpha other.chordDart)) := hotherCross
    _ = labels (dartOrbitFace embedded.RS
          (escapeSuffix.firstDart hsuffixNonempty)) := hturn
    _ = labels (dartOrbitFace embedded.RS
          (embedded.RS.alpha
            (escapeSuffix.lastDart hsuffixNonempty))) := hsuffixTransport
    _ = labels embedded.cellulation.outerHole := congrArg labels hlastFace

/-- For strictly interleaving endpoint intervals, the other chord face based
at the endpoint inside the selected interval has the common hole label and
therefore differs from the selected hole-free side label.  The disjunction
retains which endpoint is the interior one. -/
theorem interleaving_chord_innerFace_label_ne_holeFreeSide
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
    (hholes : labels embedded.cellulation.innerHole =
      labels embedded.cellulation.outerHole)
    (side : Bool)
    (hsideHole : labels (GoertzelV24ClosedWebFaceTracing.chordSideFace
        embedded.cellulation (selected.boundary htriple) side) ≠
      labels embedded.cellulation.innerHole)
    (hinterleave :
      (other.left.val < selected.left.val ∧
        selected.left.val < other.right.val ∧
        other.right.val < selected.right.val) ∨
      (selected.left.val < other.left.val ∧
        other.left.val < selected.right.val ∧
        selected.right.val < other.right.val)) :
    (other.left.val < selected.left.val ∧
        selected.left.val < other.right.val ∧
        other.right.val < selected.right.val ∧
        labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha other.chordDart)) ≠
          labels (GoertzelV24ClosedWebFaceTracing.chordSideFace
            embedded.cellulation (selected.boundary htriple) side)) ∨
      (selected.left.val < other.left.val ∧
        other.left.val < selected.right.val ∧
        selected.right.val < other.right.val ∧
        labels (dartOrbitFace embedded.RS other.chordDart) ≠
          labels (GoertzelV24ClosedWebFaceTracing.chordSideFace
            embedded.cellulation (selected.boundary htriple) side)) := by
  rcases hinterleave with hleft | hright
  · left
    refine ⟨hleft.1, hleft.2.1, hleft.2.2, ?_⟩
    have hface := labels_alpha_chordDart_eq_innerHole_of_left_before
      embedded hdata selected other htriple labels hexact hleft.1
    intro heq
    exact hsideHole (heq.symm.trans hface)
  · right
    refine ⟨hright.1, hright.2.1, hright.2.2, ?_⟩
    have hfaceOuter := labels_chordDart_eq_outerHole_of_right_after
      embedded hdata selected other htriple labels hexact hright.2.2
    have hfaceInner :
        labels (dartOrbitFace embedded.RS other.chordDart) =
          labels embedded.cellulation.innerHole :=
      hfaceOuter.trans hholes.symm
    intro heq
    exact hsideHole (heq.symm.trans hfaceInner)

/-- A pair of strictly interleaving actual chords admits one retained exact
cut and one genuinely hole-free selected side for which the other chord's
interior-end face is certified to have the opposite binary label. -/
theorem exists_exact_holeFreeSide_with_interleaving_chord_drainage
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (selected other : MajorityChordOnRadialPath
      C majority first second pair.firstPath)
    (htriple : IsTaitColorTriple majority first second)
    (hinterleave :
      (other.left.val < selected.left.val ∧
        selected.left.val < other.right.val ∧
        other.right.val < selected.right.val) ∨
      (selected.left.val < other.left.val ∧
        other.left.val < selected.right.val ∧
        selected.right.val < other.right.val)) :
    ∃ (labels : OrbitFace embedded.RS → F2) (side : Bool),
      orbitFaceParityBoundaryLinearMap embedded.RS labels =
          walkEdgeParity selected.cycleWalk ∧
        (∀ dart : embedded.RS.D,
          labels (dartOrbitFace embedded.RS dart) ≠
              labels (dartOrbitFace embedded.RS
                (embedded.RS.alpha dart)) ↔
            (embedded.RS.edgeOf dart).1 ∈ selected.cycleWalk.edges) ∧
        labels embedded.cellulation.innerHole =
          labels embedded.cellulation.outerHole ∧
        labels (chordSideFace embedded.cellulation
            (selected.boundary htriple) side) ≠
          labels embedded.cellulation.innerHole ∧
        HoleFreeChordSide embedded.cellulation
          (selected.boundary htriple) side ∧
        ((other.left.val < selected.left.val ∧
            selected.left.val < other.right.val ∧
            other.right.val < selected.right.val ∧
            labels (dartOrbitFace embedded.RS
                (embedded.RS.alpha other.chordDart)) ≠
              labels (chordSideFace embedded.cellulation
                (selected.boundary htriple) side)) ∨
          (selected.left.val < other.left.val ∧
            other.left.val < selected.right.val ∧
            selected.right.val < other.right.val ∧
            labels (dartOrbitFace embedded.RS other.chordDart) ≠
              labels (chordSideFace embedded.cellulation
                (selected.boundary htriple) side))) := by
  rcases exists_exact_chordCycle_faceCut_with_holeFreeSide
      embedded hdata pair selected htriple with
    ⟨labels, side, hboundary, hexact, hholes, hside, hholeFree⟩
  have hdrainage :=
    interleaving_chord_innerFace_label_ne_holeFreeSide
      embedded hdata selected other htriple labels hexact hholes
        side hside hinterleave
  exact ⟨labels, side, hboundary, hexact, hholes, hside,
    hholeFree, hdrainage⟩

end

end GoertzelV24ClosedWebInterleavingChordHoleDrainage

end Mettapedia.GraphTheory.FourColor
