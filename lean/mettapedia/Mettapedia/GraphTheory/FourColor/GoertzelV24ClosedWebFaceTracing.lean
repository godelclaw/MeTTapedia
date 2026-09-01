import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mettapedia.GraphTheory.PathChord
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedAnnularExcess
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceTwoSided

/-!
# Face tracing for the v24 closed-web sectors

The embedded part of the source's Sector-Alternation lemma is a finite
face-reachability statement.  A same-path chord together with the path
subarc between its endpoints is a primal wall.  Faces remain adjacent after
cutting along that wall exactly when they share some non-wall edge.  The
candidate disk on a chosen side of the chord is hole-free when its component
in this cut facial dual contains neither distinguished hole face.

This module formalizes that checkable obligation.  It deliberately does not
assert that every same-path chord passes the check, nor that hole-freeness by
itself excludes nested chords.  Those are the mathematical content of the
Sector-Alternation step, not cellulation data.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebFaceTracing

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V F E : Type*} [Fintype V] [DecidableEq V]
  [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E]

/-- The facial dual after crossings through the listed primal wall edges have
been removed.  The definition retains an adjacency whenever the two faces
share at least one non-wall edge; it therefore remains exact even before a
unique-shared-edge hypothesis is available. -/
def faceAdjacencyAvoiding
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (wall : Finset E) : SimpleGraph (AmbientFace allFaces) where
  Adj first second := first.1 ≠ second.1 ∧
    ∃ edge,
      edge ∈ interiorEdgeSupport faceBoundary allFaces ∧
      edge ∉ wall ∧
      edge ∈ faceBoundary first.1 ∧
      edge ∈ faceBoundary second.1
  symm := ⟨by
    rintro first second ⟨hne, edge, hinterior, haway, hfirst, hsecond⟩
    exact ⟨hne.symm, edge, hinterior, haway, hsecond, hfirst⟩⟩
  loopless := ⟨by
    intro face hface
    exact hface.1 rfl⟩

instance instDecidableRelFaceAdjacencyAvoiding
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (wall : Finset E) :
    DecidableRel (faceAdjacencyAvoiding faceBoundary allFaces wall).Adj := by
  intro first second
  change Decidable (first.1 ≠ second.1 ∧
    ∃ edge,
      edge ∈ interiorEdgeSupport faceBoundary allFaces ∧
      edge ∉ wall ∧
      edge ∈ faceBoundary first.1 ∧
      edge ∈ faceBoundary second.1)
  infer_instance

omit [Fintype F] [DecidableEq F] [Fintype E] in
@[simp] theorem faceAdjacencyAvoiding_adj_iff
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (wall : Finset E) {first second : AmbientFace allFaces} :
    (faceAdjacencyAvoiding faceBoundary allFaces wall).Adj first second ↔
      first.1 ≠ second.1 ∧
      ∃ edge,
        edge ∈ interiorEdgeSupport faceBoundary allFaces ∧
        edge ∉ wall ∧
        edge ∈ faceBoundary first.1 ∧
        edge ∈ faceBoundary second.1 :=
  Iff.rfl

omit [Fintype F] [DecidableEq F] [Fintype E] in
/-- Cutting primal edges only removes adjacencies from the ordinary facial
dual. -/
theorem faceAdjacencyAvoiding_le_interiorDualGraph
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (wall : Finset E) :
    faceAdjacencyAvoiding faceBoundary allFaces wall ≤
      interiorDualGraph faceBoundary allFaces := by
  intro first second hadj
  rcases hadj with ⟨hne, edge, hinterior, _haway, hfirst, hsecond⟩
  exact ⟨hne, edge, hinterior, hfirst, hsecond⟩

/-- A rotation step at an interior edge remains reachable after cutting that
edge out of the facial dual.  This is the local Jordan-side move: the two
dart-side faces are still joined by the vertex rotation whenever the rotated
edge is not part of the wall.  The two-sidedness premise is kept explicit
because a bare rotation system may let one edge occur twice on one quotient
face. -/
theorem faceAdjacencyAvoiding_reachable_of_rho
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (wall : Finset E) (dart : RS.D)
    (haway : RS.edgeOf dart ∉ wall) :
    (faceAdjacencyAvoiding
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
      (orbitFaceVertex RS dart) (orbitFaceVertex RS (RS.rho dart)) := by
  by_cases hsame : dartOrbitFace RS dart = dartOrbitFace RS (RS.rho dart)
  · have heq : orbitFaceVertex RS dart =
        orbitFaceVertex RS (RS.rho dart) := Subtype.ext hsame
    rw [heq]
  · apply SimpleGraph.Adj.reachable
    apply (faceAdjacencyAvoiding_adj_iff
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) wall).2
    refine ⟨hsame, RS.edgeOf dart, ?_, haway, ?_, ?_⟩
    · apply (mem_interiorEdgeSupport_iff
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).2
      refine ⟨Finset.mem_biUnion.2 ⟨dartOrbitFace RS dart, ?_, ?_⟩, ?_⟩
      · exact Finset.mem_univ _
      · exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS dart
      · exact orbitFace_totalIncidenceCount_eq_two_of_twoSided RS
          htwoSided (RS.edgeOf dart)
    · exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS dart
    · change RS.edgeOf dart ∈
        orbitFaceBoundary RS (dartOrbitFace RS (RS.rho dart))
      rw [← dartOrbitFace_alpha_eq_dartOrbitFace_rho RS dart]
      simpa [RS.edge_alpha] using
        edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha dart)

/-- A whole vertex-rotation cycle remains connected in the cut facial dual
when every edge incident with that vertex avoids the wall.  This is the
well-definedness step for deriving a primal side from a chosen face
component: the chosen incident dart does not matter away from the wall. -/
theorem faceAdjacencyAvoiding_reachable_of_rho_sameCycle_of_vertex_avoids
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (wall : Finset E) {left right : RS.D}
    (hsame : RS.rho.SameCycle left right)
    (havoid : ∀ dart : RS.D,
      RS.vertOf dart = RS.vertOf left → RS.edgeOf dart ∉ wall) :
    (faceAdjacencyAvoiding
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
      (orbitFaceVertex RS left) (orbitFaceVertex RS right) := by
  rcases hsame with ⟨power, hpower⟩
  have hpowers :
      RS.vertOf ((RS.rho ^ power) left) = RS.vertOf left ∧
        (faceAdjacencyAvoiding
          (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
          (orbitFaceVertex RS left)
          (orbitFaceVertex RS ((RS.rho ^ power) left)) := by
    exact zpow_induction_left (g := RS.rho)
      (P := fun permutation =>
        RS.vertOf (permutation left) = RS.vertOf left ∧
          (faceAdjacencyAvoiding
            (orbitFaceBoundary RS)
            (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
            (orbitFaceVertex RS left)
            (orbitFaceVertex RS (permutation left)))
      (by simp)
      (fun permutation hreach => by
        have hstep := faceAdjacencyAvoiding_reachable_of_rho RS htwoSided
          wall (permutation left) (havoid (permutation left) hreach.1)
        refine ⟨(RS.vert_rho (permutation left)).trans hreach.1, ?_⟩
        exact hreach.2.trans (by simpa using hstep))
      (fun permutation hreach => by
        have hvertex : RS.vertOf (RS.rho.symm (permutation left)) =
            RS.vertOf left := by
          calc
            RS.vertOf (RS.rho.symm (permutation left)) =
                RS.vertOf (RS.rho (RS.rho.symm (permutation left))) :=
              (RS.vert_rho (RS.rho.symm (permutation left))).symm
            _ = RS.vertOf (permutation left) := by simp
            _ = RS.vertOf left := hreach.1
        have hstep := faceAdjacencyAvoiding_reachable_of_rho RS htwoSided
          wall (RS.rho.symm (permutation left)) (havoid _ hvertex)
        have hstep' :
            (faceAdjacencyAvoiding
              (orbitFaceBoundary RS)
              (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
              (orbitFaceVertex RS (RS.rho.symm (permutation left)))
              (orbitFaceVertex RS (permutation left)) := by
          simpa using hstep
        refine ⟨by
          calc
            RS.vertOf (RS.rho.symm (permutation left)) =
                RS.vertOf (RS.rho (RS.rho.symm (permutation left))) :=
              (RS.vert_rho (RS.rho.symm (permutation left))).symm
            _ = RS.vertOf (permutation left) := by simp
            _ = RS.vertOf left := hreach.1, ?_⟩
        exact hreach.2.trans hstep'.symm)
      power
  rw [hpower] at hpowers
  exact hpowers.2

/-- Crossing one non-wall edge remains a reachable move in the cut facial dual.
The two-sidedness premise again rules out the degenerate case in which both
dart sides of the edge belong to one quotient face. -/
theorem faceAdjacencyAvoiding_reachable_of_alpha
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (wall : Finset E) (dart : RS.D)
    (haway : RS.edgeOf dart ∉ wall) :
    (faceAdjacencyAvoiding
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
      (orbitFaceVertex RS dart) (orbitFaceVertex RS (RS.alpha dart)) := by
  by_cases hsame : dartOrbitFace RS dart = dartOrbitFace RS (RS.alpha dart)
  · have heq : orbitFaceVertex RS dart =
        orbitFaceVertex RS (RS.alpha dart) := Subtype.ext hsame
    rw [heq]
  · apply SimpleGraph.Adj.reachable
    apply (faceAdjacencyAvoiding_adj_iff
      (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) wall).2
    refine ⟨hsame, RS.edgeOf dart, ?_, haway, ?_, ?_⟩
    · apply (mem_interiorEdgeSupport_iff
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS))).2
      refine ⟨Finset.mem_biUnion.2 ⟨dartOrbitFace RS dart, ?_, ?_⟩, ?_⟩
      · exact Finset.mem_univ _
      · exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS dart
      · exact orbitFace_totalIncidenceCount_eq_two_of_twoSided RS
          htwoSided (RS.edgeOf dart)
    · exact edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS dart
    · change RS.edgeOf dart ∈
        orbitFaceBoundary RS (dartOrbitFace RS (RS.alpha dart))
      simpa [RS.edge_alpha] using
        edgeOf_mem_orbitFaceBoundary_dartOrbitFace RS (RS.alpha dart)

/-- The primal side induced by one component of the facial dual after a wall
is removed.  It is deliberately existential over incident darts; the next
lemma proves that this existential is a genuine vertex predicate away from
wall-incident vertices. -/
def faceComponentSide
    (RS : RotationSystem V E) (wall : Finset E)
    (seed : AmbientFace (Finset.univ : Finset (OrbitFace RS)))
    (vertex : V) : Prop :=
  ∃ dart : RS.D,
    RS.vertOf dart = vertex ∧
      (faceAdjacencyAvoiding
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
        seed (orbitFaceVertex RS dart)

/-- At a vertex whose whole rotation fiber avoids the wall, the facial
component side is independent of the chosen incident dart. -/
theorem faceComponentSide_iff_of_anchor_of_vertex_avoids
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (hrotation : VertexRotationCyclic RS)
    (wall : Finset E)
    (seed : AmbientFace (Finset.univ : Finset (OrbitFace RS)))
    (vertex : V) (anchor : RS.D)
    (hanchor : RS.vertOf anchor = vertex)
    (havoid : ∀ dart : RS.D,
      RS.vertOf dart = vertex → RS.edgeOf dart ∉ wall) :
    faceComponentSide RS wall seed vertex ↔
      (faceAdjacencyAvoiding
        (orbitFaceBoundary RS)
        (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
        seed (orbitFaceVertex RS anchor) := by
  constructor
  · rintro ⟨dart, hdart, hreach⟩
    have hsame : RS.rho.SameCycle dart anchor :=
      hrotation dart anchor (hdart.trans hanchor.symm)
    have hconnect :=
      faceAdjacencyAvoiding_reachable_of_rho_sameCycle_of_vertex_avoids
        RS htwoSided wall hsame (by
          intro incident hincident
          exact havoid incident (hincident.trans hdart))
    exact hreach.trans hconnect
  · intro hreach
    exact ⟨anchor, hanchor, hreach⟩

/-- A non-wall edge whose two endpoint rotation fibers avoid the wall preserves
the face-component side.  This is the exact local non-crossing statement that
the eventual primal Jordan separator must extend over the wall vertices. -/
theorem faceComponentSide_iff_of_nonwall_edge
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (hrotation : VertexRotationCyclic RS)
    (wall : Finset E)
    (seed : AmbientFace (Finset.univ : Finset (OrbitFace RS)))
    (dart : RS.D)
    (haway : RS.edgeOf dart ∉ wall)
    (havoidLeft : ∀ incident : RS.D,
      RS.vertOf incident = RS.vertOf dart → RS.edgeOf incident ∉ wall)
    (havoidRight : ∀ incident : RS.D,
      RS.vertOf incident = RS.vertOf (RS.alpha dart) →
        RS.edgeOf incident ∉ wall) :
    faceComponentSide RS wall seed (RS.vertOf dart) ↔
      faceComponentSide RS wall seed (RS.vertOf (RS.alpha dart)) := by
  have hleft := faceComponentSide_iff_of_anchor_of_vertex_avoids
    RS htwoSided hrotation wall seed (RS.vertOf dart) dart rfl havoidLeft
  have hright := faceComponentSide_iff_of_anchor_of_vertex_avoids
    RS htwoSided hrotation wall seed (RS.vertOf (RS.alpha dart))
      (RS.alpha dart) rfl havoidRight
  have hcross := faceAdjacencyAvoiding_reachable_of_alpha
    RS htwoSided wall dart haway
  constructor
  · intro hside
    apply hright.mpr
    exact (hleft.mp hside).trans hcross
  · intro hside
    apply hleft.mpr
    exact (hright.mp hside).trans hcross.symm

/-!
The off-wall theorem above obtains the vertex-side seam by rotating through a
wall-free vertex fiber.  At a wall vertex that rotation is unavailable.  The
following form isolates exactly the replacement needed there: if every
incident dart at each endpoint can be routed, in the cut facial dual, to the
chosen dart of the non-wall edge, then the existential face-component side is
still constant across that edge.  This is the local Jordan/seam interface;
the theorem itself is purely combinatorial face tracing.
-/

theorem faceComponentSide_iff_of_nonwall_edge_of_local_vertex_routes
    (RS : RotationSystem V E) (htwoSided : OrbitFacesTwoSided RS)
    (wall : Finset E)
    (seed : AmbientFace (Finset.univ : Finset (OrbitFace RS)))
    (dart : RS.D)
    (haway : RS.edgeOf dart ∉ wall)
    (hleftRoute : ∀ incident : RS.D,
      RS.vertOf incident = RS.vertOf dart →
        (faceAdjacencyAvoiding
          (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
          (orbitFaceVertex RS incident) (orbitFaceVertex RS dart))
    (hrightRoute : ∀ incident : RS.D,
      RS.vertOf incident = RS.vertOf (RS.alpha dart) →
        (faceAdjacencyAvoiding
          (orbitFaceBoundary RS)
          (Finset.univ : Finset (OrbitFace RS)) wall).Reachable
          (orbitFaceVertex RS incident)
            (orbitFaceVertex RS (RS.alpha dart))) :
    faceComponentSide RS wall seed (RS.vertOf dart) ↔
      faceComponentSide RS wall seed (RS.vertOf (RS.alpha dart)) := by
  have hedge := faceAdjacencyAvoiding_reachable_of_alpha
    RS htwoSided wall dart haway
  constructor
  · rintro ⟨incident, hincident, hreach⟩
    refine ⟨RS.alpha dart, rfl, ?_⟩
    exact hreach.trans ((hleftRoute incident hincident).trans hedge)
  · rintro ⟨incident, hincident, hreach⟩
    refine ⟨dart, rfl, ?_⟩
    exact hreach.trans ((hrightRoute incident hincident).trans hedge.symm)

omit [Fintype F] [DecidableEq F] [Fintype E] in
/-- Enlarging the primal wall can only shrink the cut facial dual. -/
theorem faceAdjacencyAvoiding_anti
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    {smallWall largeWall : Finset E} (hwall : smallWall ⊆ largeWall) :
    faceAdjacencyAvoiding faceBoundary allFaces largeWall ≤
      faceAdjacencyAvoiding faceBoundary allFaces smallWall := by
  intro first second hadj
  rcases hadj with ⟨hne, edge, hinterior, hlarge, hfirst, hsecond⟩
  exact ⟨hne, edge, hinterior, fun hsmall => hlarge (hwall hsmall),
    hfirst, hsecond⟩

/-- A selected cut-dual component contains no face from `holes`.  This is the
finite face-tracing formulation of "the bounded region contains no hole
face" used by playbook flag L8. -/
def HoleFreeFaceRegion
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (wall : Finset E) (seed : AmbientFace allFaces)
    (holes : Finset (AmbientFace allFaces)) : Prop :=
  ∀ hole ∈ holes,
    ¬ (faceAdjacencyAvoiding faceBoundary allFaces wall).Reachable seed hole

instance instDecidableHoleFreeFaceRegion
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (wall : Finset E) (seed : AmbientFace allFaces)
    (holes : Finset (AmbientFace allFaces)) :
    Decidable (HoleFreeFaceRegion faceBoundary allFaces wall seed holes) := by
  unfold HoleFreeFaceRegion
  infer_instance

omit [Fintype F] [Fintype E] in
/-- A successful finite decision is a kernel-checkable hole-free-region
certificate.  Concrete rotation tables may use this theorem after reducing
the decision, without introducing a separate trusted search procedure. -/
theorem holeFreeFaceRegion_of_decide_eq_true
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (wall : Finset E) (seed : AmbientFace allFaces)
    (holes : Finset (AmbientFace allFaces))
    (hcheck : decide
      (HoleFreeFaceRegion faceBoundary allFaces wall seed holes) = true) :
    HoleFreeFaceRegion faceBoundary allFaces wall seed holes := by
  exact of_decide_eq_true hcheck

section WalkWall

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

section AnnularCellulation

noncomputable section

variable (cell : FramedAnnularCellulation G)

abbrev CellRS := cell.rotation.toRotationSystem

/-- All orbit faces as vertices of the full facial dual. -/
abbrev FullFace := AmbientFace
  (Finset.univ : Finset (OrbitFace (CellRS cell)))

/-- A distinguished orbit face as a vertex of the full facial dual. -/
noncomputable def fullFace (face : OrbitFace (CellRS cell)) : FullFace cell :=
  ⟨face, Finset.mem_univ face⟩

/-- The two source hole faces in the full facial dual. -/
noncomputable def holeFullFaces : Finset (FullFace cell) :=
  {fullFace cell cell.innerHole, fullFace cell cell.outerHole}

/-- The two facial sides of the chord edge, selected by its orientation.
`false` chooses the face containing the chord dart and `true` the face
containing its flipped dart. -/
noncomputable def chordSideFace
    (boundary : SamePathChordBoundary G) (side : Bool) :
    OrbitFace (CellRS cell) :=
  if side then
    dartOrbitFace (CellRS cell) ((CellRS cell).alpha boundary.chord)
  else dartOrbitFace (CellRS cell) boundary.chord

/-- The exact L8 face-tracing obligation for one chosen side of a
chord-plus-subarc wall. -/
noncomputable def HoleFreeChordSide
    (boundary : SamePathChordBoundary G) (side : Bool) : Prop :=
  HoleFreeFaceRegion
    (orbitFaceBoundary (CellRS cell))
    (Finset.univ : Finset (OrbitFace (CellRS cell)))
    boundary.wall
    (fullFace cell (chordSideFace cell boundary side))
    (holeFullFaces cell)

/-- Unfold the annular L8 obligation into the two explicit non-reachability
checks. -/
theorem holeFreeChordSide_iff
    (boundary : SamePathChordBoundary G) (side : Bool) :
    HoleFreeChordSide cell boundary side ↔
      ¬ (faceAdjacencyAvoiding
        (orbitFaceBoundary (CellRS cell))
        (Finset.univ : Finset (OrbitFace (CellRS cell)))
        boundary.wall).Reachable
          (fullFace cell (chordSideFace cell boundary side))
          (fullFace cell cell.innerHole) ∧
      ¬ (faceAdjacencyAvoiding
        (orbitFaceBoundary (CellRS cell))
        (Finset.univ : Finset (OrbitFace (CellRS cell)))
        boundary.wall).Reachable
          (fullFace cell (chordSideFace cell boundary side))
          (fullFace cell cell.outerHole) := by
  classical
  simp [HoleFreeChordSide, HoleFreeFaceRegion, holeFullFaces]

end

end AnnularCellulation

end WalkWall

end GoertzelV24ClosedWebFaceTracing

end Mettapedia.GraphTheory.FourColor
