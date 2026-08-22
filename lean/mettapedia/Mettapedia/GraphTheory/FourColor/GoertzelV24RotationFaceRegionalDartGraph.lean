import Mettapedia.GraphTheory.FourColor.GoertzelV24TerminalProfileFaceUpdate
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationBoundaryFaceCutProfile

/-!
# Regional face connectivity on literal dart occurrences

The existing facial update graph uses bounded cyclic positions relative to a
chosen root.  A serial recurrence also needs a root-independent carrier so
that occurrences coming from different boundary fragments can be compared
without projecting them to primal edges.

This file defines the regional face graph directly on darts.  Its edges are
the nontrivial successor/predecessor steps of the face permutation whose two
underlying primal edges lie in the region.  For every root, the bounded cyclic
position graph is graph-isomorphic to the induced dart graph on that root's
face orbit.

This is generic rotation-system infrastructure.  It makes no corridor or
profile completeness claim.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationFaceRegionalDartGraph

open GoertzelV24FaceOrbitIncidence
open GoertzelV24HexFaceRungType
open GoertzelV24InducedHexCorridorTypes
open GoertzelV24RotationFaceFragments
open GoertzelV24RotationBoundaryFaceCutProfile
open GoertzelV24RotationAllFaceCutProfile
open GoertzelV24TerminalProfileFaceUpdate
open SimpleGraph

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The face-cycle graph restricted to a regional edge set, directly on the
literal dart carrier.  A one-dart face contributes no loop. -/
def faceRegionalDartGraph
    (RS : RotationSystem V E) (region : Finset E) : SimpleGraph RS.D where
  Adj left right :=
    left ≠ right ∧
      (right = RS.phi left ∨ left = RS.phi right) ∧
      RS.edgeOf left ∈ region ∧ RS.edgeOf right ∈ region
  symm := ⟨by
    rintro left right ⟨hne, hstep, hleft, hright⟩
    exact ⟨hne.symm, hstep.symm, hright, hleft⟩⟩
  loopless := ⟨by
    intro dart hadj
    exact hadj.1 rfl⟩

@[simp]
theorem faceRegionalDartGraph_adj
    (RS : RotationSystem V E) (region : Finset E) (left right : RS.D) :
    (faceRegionalDartGraph RS region).Adj left right ↔
      left ≠ right ∧
        (right = RS.phi left ∨ left = RS.phi right) ∧
        RS.edgeOf left ∈ region ∧ RS.edgeOf right ∈ region :=
  Iff.rfl

/-- Bounded powers of the face permutation enumerate exactly the literal dart
fiber of one face orbit. -/
noncomputable def faceCycleDartOrbitEquiv
    (RS : RotationSystem V E) (root : RS.D) :
    Fin (RS.faceOrbit root).card ≃ ↑(RS.faceOrbit root) :=
  Equiv.ofBijective
    (fun position => ⟨faceCycleDart RS root position,
      faceCycleDart_mem RS root position⟩)
    ⟨by
      intro left right heq
      apply faceCycleDart_injective RS root
      exact congrArg Subtype.val heq,
    by
      intro dart
      rcases existsUnique_faceCycleDart_eq RS root dart.1 dart.2 with
        ⟨position, hposition, _hunique⟩
      refine ⟨position, ?_⟩
      apply Subtype.ext
      exact hposition⟩

@[simp]
theorem faceCycleDartOrbitEquiv_apply_val
    (RS : RotationSystem V E) (root : RS.D)
    (position : Fin (RS.faceOrbit root).card) :
    (faceCycleDartOrbitEquiv RS root position).1 =
      faceCycleDart RS root position :=
  rfl

/-- Root-relative cyclic positions and literal darts in that root's orbit
carry exactly the same regional face graph. -/
noncomputable def faceRegionalAmbientPositionGraphIsoDartOrbit
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E) :
    faceRegionalAmbientPositionGraph RS root region ≃g
      (faceRegionalDartGraph RS region).induce
        (fun dart => dart ∈ RS.faceOrbit root) where
  toEquiv := faceCycleDartOrbitEquiv RS root
  map_rel_iff' := by
    intro left right
    change
      (faceCycleDart RS root left ≠ faceCycleDart RS root right ∧
          (faceCycleDart RS root right =
              RS.phi (faceCycleDart RS root left) ∨
            faceCycleDart RS root left =
              RS.phi (faceCycleDart RS root right)) ∧
          RS.edgeOf (faceCycleDart RS root left) ∈ region ∧
          RS.edgeOf (faceCycleDart RS root right) ∈ region) ↔
      (left ≠ right ∧
          (faceCycleDart RS root right =
              RS.phi (faceCycleDart RS root left) ∨
            faceCycleDart RS root left =
              RS.phi (faceCycleDart RS root right))) ∧
          RS.edgeOf (faceCycleDart RS root left) ∈ region ∧
          RS.edgeOf (faceCycleDart RS root right) ∈ region
    constructor
    · rintro ⟨hne, hstep, hleft, hright⟩
      refine ⟨⟨?_, hstep⟩, hleft, hright⟩
      intro hposition
      exact hne (congrArg (faceCycleDart RS root) hposition)
    · rintro ⟨⟨hne, hstep⟩, hleft, hright⟩
      refine ⟨?_, hstep, hleft, hright⟩
      intro hdart
      exact hne (faceCycleDart_injective RS root hdart)

/-- Regional reachability on bounded positions is exactly reachability on the
corresponding literal dart-orbit fiber. -/
theorem faceRegionalAmbientPositionGraph_reachable_iff_dartOrbit
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E)
    (left right : Fin (RS.faceOrbit root).card) :
    (faceRegionalAmbientPositionGraph RS root region).Reachable left right ↔
      ((faceRegionalDartGraph RS region).induce
        (fun dart => dart ∈ RS.faceOrbit root)).Reachable
          (faceCycleDartOrbitEquiv RS root left)
          (faceCycleDartOrbitEquiv RS root right) := by
  exact (faceRegionalAmbientPositionGraphIsoDartOrbit RS root region).reachable_iff.symm

/-- A regional face-dart edge never changes the ambient orbit face. -/
theorem faceRegionalDartGraph_adj_dartOrbitFace_eq
    (RS : RotationSystem V E) (region : Finset E) {left right : RS.D}
    (hadj : (faceRegionalDartGraph RS region).Adj left right) :
    dartOrbitFace RS left = dartOrbitFace RS right := by
  rcases (faceRegionalDartGraph_adj RS region left right).1 hadj with
    ⟨_hne, hstep, _hleft, _hright⟩
  rcases hstep with hforward | hbackward
  · subst right
    exact (dartOrbitFace_phi_eq RS left).symm
  · subst left
    exact dartOrbitFace_phi_eq RS right

/-- Regional face-dart reachability stays on one literal orbit face. -/
theorem faceRegionalDartGraph_reachable_dartOrbitFace_eq
    (RS : RotationSystem V E) (region : Finset E) {left right : RS.D}
    (hreachable : (faceRegionalDartGraph RS region).Reachable left right) :
    dartOrbitFace RS left = dartOrbitFace RS right := by
  apply hreachable.elim
  intro walk
  induction walk with
  | nil => rfl
  | cons hadj tail ih =>
      exact (faceRegionalDartGraph_adj_dartOrbitFace_eq RS region hadj).trans
        (ih tail.reachable)

/-- Restricting the regional dart graph to one orbit face neither loses nor
creates reachability between darts already on that face. -/
theorem faceRegionalDartGraph_reachable_iff_induce_faceOrbit
    (RS : RotationSystem V E) (root : RS.D) (region : Finset E)
    (left right : ↑(RS.faceOrbit root)) :
    (faceRegionalDartGraph RS region).Reachable left.1 right.1 ↔
      ((faceRegionalDartGraph RS region).induce
        (fun dart => dart ∈ RS.faceOrbit root)).Reachable left right := by
  constructor
  · intro hreachable
    apply hreachable.elim
    intro walk
    have hleftFace : dartOrbitFace RS left.1 = dartOrbitFace RS root := by
      exact (Quotient.sound ((RS.mem_faceOrbit).1 left.2)).symm
    have hsupport : ∀ dart ∈ walk.support, dart ∈ RS.faceOrbit root := by
      intro dart hdart
      rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit RS root,
        mem_orbitFaceDarts_iff]
      have hface := faceRegionalDartGraph_reachable_dartOrbitFace_eq RS region
        (walk.takeUntil dart hdart).reachable
      exact hface.symm.trans hleftFace
    exact ⟨walk.induce (fun dart => dart ∈ RS.faceOrbit root) hsupport⟩
  · intro hreachable
    exact hreachable.map (Embedding.induce _).toHom

/-- The canonical dart representatives of boundary fragments are connected
in the regional face graph exactly when they represent the same fragment.
This is occurrence-sensitive: two sides of one bridge remain distinct. -/
theorem boundaryRegionalFragmentDartOccurrence_reachable_iff_eq
    (RS : RotationSystem V E) (cut region : Finset E)
    (left right : BoundaryRegionalFragment RS cut region) :
    (faceRegionalDartGraph RS region).Reachable
        (boundaryRegionalFragmentDartOccurrence RS cut region left).1
        (boundaryRegionalFragmentDartOccurrence RS cut region right).1 ↔
      left = right := by
  constructor
  · intro hreachable
    have hface : left.1.1 = right.1.1 := by
      calc
        left.1.1 = dartOrbitFace RS (orbitFaceRoot RS left.1.1) :=
          (dartOrbitFace_orbitFaceRoot RS left.1.1).symm
        _ = dartOrbitFace RS
            (boundaryRegionalFragmentDartOccurrence RS cut region left).1 := by
          exact (dartOrbitFace_faceCycleDart RS (orbitFaceRoot RS left.1.1)
            (boundaryRegionalFragmentCutPosition RS cut region left)).symm
        _ = dartOrbitFace RS
            (boundaryRegionalFragmentDartOccurrence RS cut region right).1 :=
          faceRegionalDartGraph_reachable_dartOrbitFace_eq RS region hreachable
        _ = dartOrbitFace RS (orbitFaceRoot RS right.1.1) := by
          exact dartOrbitFace_faceCycleDart RS (orbitFaceRoot RS right.1.1)
            (boundaryRegionalFragmentCutPosition RS cut region right)
        _ = right.1.1 := dartOrbitFace_orbitFaceRoot RS right.1.1
    rcases left with ⟨leftFace, ⟨leftFragment, leftTouches⟩⟩
    rcases right with ⟨rightFace, ⟨rightFragment, rightTouches⟩⟩
    dsimp only at hface
    have hfaceSubtype : leftFace = rightFace := Subtype.ext hface
    subst rightFace
    let root := orbitFaceRoot RS leftFace.1
    let leftBoundary : BoundaryRegionalFragment RS cut region :=
      ⟨leftFace, ⟨leftFragment, leftTouches⟩⟩
    let rightBoundary : BoundaryRegionalFragment RS cut region :=
      ⟨leftFace, ⟨rightFragment, rightTouches⟩⟩
    let leftPosition :=
      boundaryRegionalFragmentCutPosition RS cut region leftBoundary
    let rightPosition :=
      boundaryRegionalFragmentCutPosition RS cut region rightBoundary
    rcases (mem_faceRegionalFragmentPositions_iff RS root region leftFragment
      leftPosition).1 (by
        simpa [root, leftPosition, leftBoundary] using
          boundaryRegionalFragmentCutPosition_mem RS cut region leftBoundary) with
      ⟨leftRegional, hleftSupp, hleftPosition⟩
    rcases (mem_faceRegionalFragmentPositions_iff RS root region rightFragment
      rightPosition).1 (by
        simpa [root, rightPosition, rightBoundary] using
          boundaryRegionalFragmentCutPosition_mem RS cut region rightBoundary) with
      ⟨rightRegional, hrightSupp, hrightPosition⟩
    have hInduced :
        ((faceRegionalDartGraph RS region).induce
          (fun dart => dart ∈ RS.faceOrbit root)).Reachable
            (faceCycleDartOrbitEquiv RS root leftPosition)
            (faceCycleDartOrbitEquiv RS root rightPosition) := by
      apply (faceRegionalDartGraph_reachable_iff_induce_faceOrbit RS root region
        (faceCycleDartOrbitEquiv RS root leftPosition)
        (faceCycleDartOrbitEquiv RS root rightPosition)).1
      simpa [root, leftPosition, rightPosition, leftBoundary, rightBoundary,
        boundaryRegionalFragmentDartOccurrence] using hreachable
    have hambient :
        (faceRegionalAmbientPositionGraph RS root region).Reachable
          leftPosition rightPosition :=
      (faceRegionalAmbientPositionGraph_reachable_iff_dartOrbit RS root region
        leftPosition rightPosition).2 hInduced
    have hregional :
        (faceRegionalPositionGraph RS root region).Reachable
          leftRegional rightRegional :=
      (faceRegionalPositionGraph_reachable_iff_ambient RS root region
        leftRegional rightRegional).2 (by
          simpa [hleftPosition, hrightPosition] using hambient)
    have hfragment : leftFragment = rightFragment :=
      ((SimpleGraph.ConnectedComponent.mem_supp_iff leftFragment
        leftRegional).1 hleftSupp).symm.trans
        ((SimpleGraph.ConnectedComponent.sound hregional).trans
          ((SimpleGraph.ConnectedComponent.mem_supp_iff rightFragment
            rightRegional).1 hrightSupp))
    cases hfragment
    rfl
  · rintro rfl
    exact SimpleGraph.Reachable.refl _

end

end GoertzelV24RotationFaceRegionalDartGraph

end Mettapedia.GraphTheory.FourColor
