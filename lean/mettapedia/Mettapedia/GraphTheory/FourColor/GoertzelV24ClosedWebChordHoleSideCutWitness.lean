import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebChordHoleSeparation
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebChordCycleFaceSideTransport

/-!
# Retaining the exact cut behind a hole-free chord side

The first hole-separation theorem deliberately exposed only the geometric
conclusion that one chord-cycle side contains neither annular hole.  The L8
drainage step also needs the binary exact-cut witness which selected that
side.  This module retains both pieces of data without adding a sector or
noncrossing assumption.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebChordHoleSideCutWitness

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebChordHoleSeparation
open GoertzelV24ClosedWebChordCycleFaceSideTransport
open GoertzelV24ClosedWebFaceTracing
open GoertzelV24ClosedWebRadialComponents
open GoertzelV24ClosedWebRadialPathChords
open GoertzelV24ClosedWebRadialPathSectorAnchors
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceParityBoundary
open GoertzelV24WalkCycleParity
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

local instance chordHoleSideCutGraphEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- In the two-element field, equality of one pair and inequality across
both corresponding cut edges determines equality of the opposite pair. -/
private theorem f2_opposite_eq_of_eq_of_ne_of_ne
    (first last firstOpposite lastOpposite : F2)
    (hsame : first = last)
    (hfirst : first ≠ firstOpposite)
    (hlast : last ≠ lastOpposite) :
    firstOpposite = lastOpposite := by
  fin_cases first <;> fin_cases last <;>
    fin_cases firstOpposite <;> fin_cases lastOpposite <;> simp_all

/-- Every same-path chord cycle admits one exact binary face cut together
with the actual side selected away from both annular holes.  Unlike
`exists_holeFreeChordSide`, this theorem retains the labels which certify the
selection, so later face transport can compare a second chord with the same
cut. -/
theorem exists_exact_chordCycle_faceCut_with_holeFreeSide
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    (pair : RadialPathPair data C first second)
    (chord : MajorityChordOnRadialPath C majority first second
      pair.firstPath)
    (htriple : IsTaitColorTriple majority first second) :
    ∃ (labels : OrbitFace embedded.RS → F2) (side : Bool),
      orbitFaceParityBoundaryLinearMap embedded.RS labels =
          walkEdgeParity chord.cycleWalk ∧
        (∀ dart : embedded.RS.D,
          labels (dartOrbitFace embedded.RS dart) ≠
              labels (dartOrbitFace embedded.RS
                (embedded.RS.alpha dart)) ↔
            (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges) ∧
        labels embedded.cellulation.innerHole =
          labels embedded.cellulation.outerHole ∧
        labels (chordSideFace embedded.cellulation
            (chord.boundary htriple) side) ≠
          labels embedded.cellulation.innerHole ∧
        HoleFreeChordSide embedded.cellulation
          (chord.boundary htriple) side := by
  rcases exists_exact_chordCycle_faceCut_with_holes_sameSide
      embedded hdata pair chord htriple with
    ⟨labels, hlabels, hexact, hholes⟩
  have hchordEdge :
      (embedded.RS.edgeOf chord.chordDart).1 ∈
        chord.cycleWalk.edges := by
    simp [MajorityChordOnRadialPath.cycleWalk]
    exact Or.inl rfl
  have hchordSides :
      labels (dartOrbitFace embedded.RS chord.chordDart) ≠
        labels (dartOrbitFace embedded.RS
          (embedded.RS.alpha chord.chordDart)) :=
    (hexact chord.chordDart).2 hchordEdge
  have hholeFree : ∀ side : Bool,
      labels (chordSideFace embedded.cellulation
          (chord.boundary htriple) side) ≠
        labels embedded.cellulation.innerHole →
      HoleFreeChordSide embedded.cellulation
        (chord.boundary htriple) side := by
    intro side hseedInner
    rw [holeFreeChordSide_iff]
    constructor
    · intro hreach
      exact hseedInner <|
        labels_eq_of_reachable_avoiding_chordCycle
          embedded chord htriple labels hexact hreach
    · intro hreach
      have hseedOuter := labels_eq_of_reachable_avoiding_chordCycle
        embedded chord htriple labels hexact hreach
      exact hseedInner (hseedOuter.trans hholes.symm)
  by_cases hfirstHole :
      labels (dartOrbitFace embedded.RS chord.chordDart) =
        labels embedded.cellulation.innerHole
  · have hseedInner :
        labels (chordSideFace embedded.cellulation
          (chord.boundary htriple) true) ≠
            labels embedded.cellulation.innerHole := by
      simp only [chordSideFace, if_true]
      change labels (dartOrbitFace embedded.RS
        (embedded.RS.alpha chord.chordDart)) ≠
          labels embedded.cellulation.innerHole
      intro heq
      exact hchordSides (hfirstHole.trans heq.symm)
    exact ⟨labels, true, hlabels, hexact, hholes, hseedInner,
      hholeFree true hseedInner⟩
  · have hseedInner :
        labels (chordSideFace embedded.cellulation
          (chord.boundary htriple) false) ≠
            labels embedded.cellulation.innerHole := by
      simpa [chordSideFace,
        MajorityChordOnRadialPath.boundary] using hfirstHole
    exact ⟨labels, false, hlabels, hexact, hholes, hseedInner,
      hholeFree false hseedInner⟩

/-- Exact-cut transport around the chord cycle is valid at every cycle dart
on either selected face side.  `false` follows the cycle darts themselves;
`true` follows the opposite face at each cycle edge.  Binary labels turn the
first-side transport into the corresponding opposite-side transport without
a second geometric argument. -/
theorem labels_eq_chordSideFace_dartSide_of_mem_exact_chordCycle_cut
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (labels : OrbitFace embedded.RS → F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    (side : Bool) (target : G.Dart)
    (htarget : target ∈ chord.cycleWalk.darts) :
    labels (chordSideFace embedded.cellulation
        (chord.boundary htriple) side) =
      labels (dartOrbitFace embedded.RS
        (if side then
          embedded.RS.alpha target
        else target)) := by
  have hcycle : chord.cycleWalk.IsCycle :=
    chord.cycleWalk_isCycle htriple
  have hfirstDart :
      chord.cycleWalk.firstDart hcycle.not_nil = chord.chordDart := by
    apply SimpleGraph.Dart.ext
    apply Prod.ext
    · rfl
    · simpa [MajorityChordOnRadialPath.cycleWalk] using
        SimpleGraph.Walk.snd_cons chord.subarc.reverse
          chord.chordDart.adj
  have hsame :
      labels (dartOrbitFace embedded.RS chord.chordDart) =
        labels (dartOrbitFace embedded.RS target) := by
    rw [← hfirstDart]
    exact labels_eq_firstDart_dart_of_mem_exact_chordCycle_cut
      embedded hdata chord htriple labels hexact target htarget
  have hchordEdge :
      (embedded.RS.edgeOf chord.chordDart).1 ∈
        chord.cycleWalk.edges := by
    simp [MajorityChordOnRadialPath.cycleWalk]
    exact Or.inl rfl
  have htargetEdge :
      (embedded.RS.edgeOf target).1 ∈ chord.cycleWalk.edges := by
    change target.edge ∈ chord.cycleWalk.edges
    exact List.mem_map_of_mem htarget
  have hfirstCross :
      labels (dartOrbitFace embedded.RS chord.chordDart) ≠
        labels (dartOrbitFace embedded.RS
          (embedded.RS.alpha chord.chordDart)) :=
    (hexact chord.chordDart).2 hchordEdge
  have htargetCross :
      labels (dartOrbitFace embedded.RS target) ≠
        labels (dartOrbitFace embedded.RS
          (embedded.RS.alpha target)) :=
    (hexact target).2 htargetEdge
  have hopposite :
      labels (dartOrbitFace embedded.RS
          (embedded.RS.alpha chord.chordDart)) =
        labels (dartOrbitFace embedded.RS
          (embedded.RS.alpha target)) :=
    f2_opposite_eq_of_eq_of_ne_of_ne _ _ _ _
      hsame hfirstCross htargetCross
  cases side
  · simpa [chordSideFace, MajorityChordOnRadialPath.boundary]
      using hsame
  · simpa [chordSideFace, MajorityChordOnRadialPath.boundary]
      using hopposite

/-- Final-dart specialization of the every-dart side transport theorem. -/
theorem labels_eq_chordSideFace_lastDartSide_of_exact_chordCycle_cut
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed)
    {C : G.EdgeColoring Color} {majority first second : Color}
    {component : (colorPairSupportGraph C first second).ConnectedComponent}
    {radial : ComponentRadialPath data C first second component}
    (chord : MajorityChordOnRadialPath C majority first second radial)
    (htriple : IsTaitColorTriple majority first second)
    (labels : OrbitFace embedded.RS → F2)
    (hexact : ∀ dart : embedded.RS.D,
      labels (dartOrbitFace embedded.RS dart) ≠
          labels (dartOrbitFace embedded.RS
            (embedded.RS.alpha dart)) ↔
        (embedded.RS.edgeOf dart).1 ∈ chord.cycleWalk.edges)
    (side : Bool) :
    labels (chordSideFace embedded.cellulation
        (chord.boundary htriple) side) =
      labels (dartOrbitFace embedded.RS
        (if side then
          embedded.RS.alpha (chord.cycleWalk.lastDart
            (chord.cycleWalk_isCycle htriple).not_nil)
        else chord.cycleWalk.lastDart
          (chord.cycleWalk_isCycle htriple).not_nil)) := by
  apply labels_eq_chordSideFace_dartSide_of_mem_exact_chordCycle_cut
    embedded hdata chord htriple labels hexact side
  exact chord.cycleWalk.lastDart_mem_darts
    (chord.cycleWalk_isCycle htriple).not_nil

end

end GoertzelV24ClosedWebChordHoleSideCutWitness

end Mettapedia.GraphTheory.FourColor
