import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedCountReplacement
import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSeamMultigraph
import Mettapedia.GraphTheory.FourColor.GoertzelV24RawNooseCountPumping
import Mettapedia.GraphTheory.FourColor.GoertzelV24RewiredTaitColoring

/-!
# The abstract closed Count is the physical sewn map

`PortTangle.series` is the coloring-level composition used by the Count law,
whereas `OpenTangleData.composeRotationSystem` is the literal dart splice used
by the structural descent.  This file proves that, after explicitly reindexing
the right boundary through the seam matching, the two constructions have the
same proper nonzero Tait colorings.

The proof is deliberately independent of the vertex rotation.  The two dart
carriers differ only by reassociation, deletion of empty external ports, and
the displayed equivalence between the two seam carriers.  That equivalence
preserves the vertex map and conjugates the edge flip.  Proper dart colorings
therefore transport in both directions, and the generic descent from invariant
dart colors to computed edge orbits identifies the result with ordinary Tait
colorability of the physical composite rotation system.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PhysicalClosedCountBridge

open GoertzelV24OpenTangleComposition
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24ClosedCountReplacement
open GoertzelV24CompositeSeamMultigraph
open GoertzelV24RotationSpliceConstructor
open GoertzelV24RawNooseCountPumping

universe u

abbrev EmptyPort := PEmpty.{u + 1}

section

variable {V W I J L R : Type u}

/-- The left side with no external input ports and seam carrier `L`. -/
def leftClosedPortTangle (left : OpenTangleData V I L) :
    PortTangle V I (EmptyPort.{u} ⊕ L) where
  vert
    | Sum.inl dart => left.interiorVert dart
    | Sum.inr (Sum.inl empty) => PEmpty.elim empty
    | Sum.inr (Sum.inr port) => left.boundaryVert port
  alpha := left.interiorAlpha
  alpha_involutive := left.interiorAlpha_involutive
  alpha_fixfree := left.interiorAlpha_fixfree
  no_self_loops := left.interior_no_self_loops

/-- The right side, with its input seam explicitly relabelled from `R` to `L`
through `matching`, and with no external output ports. -/
def rightClosedPortTangle (right : OpenTangleData W J R) (matching : L ≃ R) :
    PortTangle W J (L ⊕ EmptyPort.{u}) where
  vert
    | Sum.inl dart => right.interiorVert dart
    | Sum.inr (Sum.inl port) => right.boundaryVert (matching port)
    | Sum.inr (Sum.inr empty) => PEmpty.elim empty
  alpha := right.interiorAlpha
  alpha_involutive := right.interiorAlpha_involutive
  alpha_fixfree := right.interiorAlpha_fixfree
  no_self_loops := right.interior_no_self_loops

/-! ## The finite cut-word support is the full realizable support -/

/-- Forget the nonzero proof carried by a genuine Tait cut word. -/
def cutWordColor (word : CutWord L) : L → Color :=
  fun port => (word port).1

/-- The finite support stored in a decomposition state: genuine Tait cut
words realized by an inner piece. -/
def taitInnerSupport (tangle : PortTangle W J (L ⊕ EmptyPort.{u})) :
    Set (CutWord L) :=
  {word | cutWordColor word ∈ innerSupport tangle}

/-- Every word in the raw inner support is automatically a genuine Tait cut
word, because proper port colourings are nonzero at every boundary dart. -/
theorem exists_cutWord_of_mem_innerSupport
    (tangle : PortTangle W J (L ⊕ EmptyPort.{u}))
    {word : L → Color} (hword : word ∈ innerSupport tangle) :
    ∃ taitWord : CutWord L,
      taitWord ∈ taitInnerSupport tangle ∧
        cutWordColor taitWord = word := by
  have hrealized := hword
  obtain ⟨coloring⟩ := hrealized
  have hnonzero : ∀ port : L, word port ≠ 0 := by
    intro port
    have hboundary := congrFun coloring.2.2 (Sum.inl port)
    change coloring.1.color (Sum.inr (Sum.inl port)) = word port at hboundary
    rw [← hboundary]
    exact coloring.2.1.1 (Sum.inr (Sum.inl port))
  let taitWord : CutWord L := fun port => ⟨word port, hnonzero port⟩
  have hforget : cutWordColor taitWord = word := by
    funext port
    rfl
  refine ⟨taitWord, ?_, hforget⟩
  · change cutWordColor taitWord ∈ innerSupport tangle
    rw [hforget]
    exact hword

/-- Equality of the finite genuine-word supports is exactly equality of the
raw supports consumed by the closed Count replacement; no stronger state is
needed. -/
theorem innerSupport_eq_of_taitInnerSupport_eq
    (first : PortTangle W J (L ⊕ EmptyPort.{u}))
    {W' J' : Type u}
    (second : PortTangle W' J' (L ⊕ EmptyPort.{u}))
    (hsupport : taitInnerSupport first = taitInnerSupport second) :
    innerSupport first = innerSupport second := by
  ext word
  constructor
  · intro hword
    obtain ⟨taitWord, htait, hforget⟩ :=
      exists_cutWord_of_mem_innerSupport first hword
    rw [hsupport] at htait
    change cutWordColor taitWord ∈ innerSupport second at htait
    simpa [hforget] using htait
  · intro hword
    obtain ⟨taitWord, htait, hforget⟩ :=
      exists_cutWord_of_mem_innerSupport second hword
    rw [← hsupport] at htait
    change cutWordColor taitWord ∈ innerSupport first at htait
    simpa [hforget] using htait

/-- Reassociation and seam relabelling from the interior dart carrier of the
closed `PortTangle.series` to the dart carrier of the literal splice. -/
def seriesCompositeDartEquiv (matching : L ≃ R) :
    ((I ⊕ J) ⊕ (L ⊕ L)) ≃ MatchedSeam.Dart (I ⊕ J) L R where
  toFun
    | Sum.inl dart => Sum.inl dart
    | Sum.inr (Sum.inl port) => Sum.inr (Sum.inl port)
    | Sum.inr (Sum.inr port) => Sum.inr (Sum.inr (matching port))
  invFun
    | Sum.inl dart => Sum.inl dart
    | Sum.inr (Sum.inl port) => Sum.inr (Sum.inl port)
    | Sum.inr (Sum.inr port) => Sum.inr (Sum.inr (matching.symm port))
  left_inv := by
    rintro (dart | (port | port)) <;> simp
  right_inv := by
    rintro (dart | (port | port)) <;> simp

@[simp]
theorem seriesCompositeDartEquiv_leftInterior (matching : L ≃ R) (dart : I) :
    seriesCompositeDartEquiv (I := I) (J := J) matching
        (Sum.inl (Sum.inl dart)) =
      Sum.inl (Sum.inl dart) :=
  rfl

@[simp]
theorem seriesCompositeDartEquiv_rightInterior (matching : L ≃ R) (dart : J) :
    seriesCompositeDartEquiv (I := I) (J := J) matching
        (Sum.inl (Sum.inr dart)) =
      Sum.inl (Sum.inr dart) :=
  rfl

@[simp]
theorem seriesCompositeDartEquiv_leftSeam (matching : L ≃ R) (port : L) :
    seriesCompositeDartEquiv (I := I) (J := J) matching
        (Sum.inr (Sum.inl port)) =
      Sum.inr (Sum.inl port) :=
  rfl

@[simp]
theorem seriesCompositeDartEquiv_rightSeam (matching : L ≃ R) (port : L) :
    seriesCompositeDartEquiv (I := I) (J := J) matching
        (Sum.inr (Sum.inr port)) =
      Sum.inr (Sum.inr (matching port)) :=
  rfl

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

/-- The carrier equivalence preserves the displayed endpoint vertex. -/
theorem seriesCompositeDartEquiv_vert
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (dart : (I ⊕ J) ⊕ (L ⊕ L)) :
    (compositeDarts left right matching).vertOf
        (seriesCompositeDartEquiv matching dart) =
      (series (leftClosedPortTangle left)
        (rightClosedPortTangle right matching)).vert (Sum.inl dart) := by
  rcases dart with (dart | dart) | (port | port) <;>
    rfl

/-- The carrier equivalence conjugates the abstract series flip to the literal
matched-seam flip. -/
theorem seriesCompositeDartEquiv_alpha
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (dart : (I ⊕ J) ⊕ (L ⊕ L)) :
    seriesCompositeDartEquiv matching
        ((series (leftClosedPortTangle left)
          (rightClosedPortTangle right matching)).alpha dart) =
      (compositeDarts left right matching).alpha
        (seriesCompositeDartEquiv matching dart) := by
  rcases dart with (dart | dart) | (port | port) <;>
    simp [series, seriesAlpha, leftClosedPortTangle, rightClosedPortTangle,
      compositeDarts, MatchedSeam.Data.toRewiredDartSystem,
      OpenTangleData.composeData,
      seriesCompositeDartEquiv]

/-! ## From the Count composite to the physical composite -/

/-- Read a closed series colouring on the literal composite dart carrier. -/
def physicalDartColor
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R)
    (coloring : Col
      (series (leftClosedPortTangle left)
        (rightClosedPortTangle right matching))
      (Sum.elim PEmpty.elim PEmpty.elim)) :
    MatchedSeam.Dart (I ⊕ J) L R → Color :=
  fun dart => coloring.1.color
    (Sum.inl ((seriesCompositeDartEquiv matching).symm dart))

/-- The transported dart colouring is constant on the literal edge flip. -/
theorem physicalDartColor_alpha
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R)
    (coloring : Col
      (series (leftClosedPortTangle left)
        (rightClosedPortTangle right matching))
      (Sum.elim PEmpty.elim PEmpty.elim))
    (dart : MatchedSeam.Dart (I ⊕ J) L R) :
    physicalDartColor left right matching coloring
        ((compositeDarts left right matching).alpha dart) =
      physicalDartColor left right matching coloring dart := by
  let equiv := seriesCompositeDartEquiv (I := I) (J := J) matching
  have hconj := seriesCompositeDartEquiv_alpha left right matching (equiv.symm dart)
  have hsymm :
      equiv.symm ((compositeDarts left right matching).alpha dart) =
        (series (leftClosedPortTangle left)
          (rightClosedPortTangle right matching)).alpha (equiv.symm dart) := by
    apply equiv.injective
    rw [equiv.apply_symm_apply]
    simpa [equiv] using hconj.symm
  simp only [physicalDartColor]
  rw [hsymm]
  exact coloring.1.invariant (equiv.symm dart)

/-- Properness transports along the same dart equivalence. -/
theorem physicalDartColor_proper
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R)
    (coloring : Col
      (series (leftClosedPortTangle left)
        (rightClosedPortTangle right matching))
      (Sum.elim PEmpty.elim PEmpty.elim))
    {first second : MatchedSeam.Dart (I ⊕ J) L R}
    (hvert : (compositeDarts left right matching).vertOf first =
      (compositeDarts left right matching).vertOf second)
    (hne : first ≠ second) :
    physicalDartColor left right matching coloring first ≠
      physicalDartColor left right matching coloring second := by
  let equiv := seriesCompositeDartEquiv (I := I) (J := J) matching
  apply coloring.2.1.2
  · calc
      (series (leftClosedPortTangle left)
          (rightClosedPortTangle right matching)).vert
          (Sum.inl (equiv.symm first)) =
          (compositeDarts left right matching).vertOf first := by
            simpa [equiv] using
              (seriesCompositeDartEquiv_vert left right matching
                (equiv.symm first)).symm
      _ = (compositeDarts left right matching).vertOf second := hvert
      _ = (series (leftClosedPortTangle left)
          (rightClosedPortTangle right matching)).vert
          (Sum.inl (equiv.symm second)) := by
            simpa [equiv] using
              seriesCompositeDartEquiv_vert left right matching
                (equiv.symm second)
  · intro heq
    apply hne
    apply equiv.symm.injective
    exact Sum.inl.inj heq

omit [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R] in
/-- Nonzero colours transport pointwise. -/
theorem physicalDartColor_nonzero
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R)
    (coloring : Col
      (series (leftClosedPortTangle left)
        (rightClosedPortTangle right matching))
      (Sum.elim PEmpty.elim PEmpty.elim))
    (dart : MatchedSeam.Dart (I ⊕ J) L R) :
    physicalDartColor left right matching coloring dart ≠ 0 :=
  coloring.2.1.1
    (Sum.inl ((seriesCompositeDartEquiv matching).symm dart))

/-- A proper Count-side colouring descends to an ordinary edge colouring of
the computed edge orbits of the physical splice. -/
noncomputable def physicalEdgeColoring
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R)
    (coloring : Col
      (series (leftClosedPortTangle left)
        (rightClosedPortTangle right matching))
      (Sum.elim PEmpty.elim PEmpty.elim)) :
    (compositeRS left right matching).EdgeColoring Color :=
  (compositeDarts left right matching).descendedColoring
    (physicalDartColor left right matching coloring)
    (physicalDartColor_alpha left right matching coloring)
    (physicalDartColor_proper left right matching coloring)

theorem physicalEdgeColoring_isTait
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R)
    (coloring : Col
      (series (leftClosedPortTangle left)
        (rightClosedPortTangle right matching))
      (Sum.elim PEmpty.elim PEmpty.elim)) :
    (compositeRS left right matching).IsTaitEdgeColoring
      (physicalEdgeColoring left right matching coloring) := by
  exact (compositeDarts left right matching).descendedColoring_isTait
    (physicalDartColor left right matching coloring)
    (physicalDartColor_alpha left right matching coloring)
    (physicalDartColor_proper left right matching coloring)
    (physicalDartColor_nonzero left right matching coloring)

/-! ## From the physical composite back to the Count composite -/

/-- Pull an edge colouring of the physical splice back to the abstract closed
series by reading the computed edge containing each dart. -/
noncomputable def seriesColoringOfPhysical
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R)
    (coloring : (compositeRS left right matching).EdgeColoring Color) :
    Coloring (series (leftClosedPortTangle left)
      (rightClosedPortTangle right matching)) where
  color
    | Sum.inl dart => coloring
        ((compositeDarts left right matching).edgeOf
          (seriesCompositeDartEquiv matching dart))
    | Sum.inr (Sum.inl empty) => PEmpty.elim empty
    | Sum.inr (Sum.inr empty) => PEmpty.elim empty
  invariant := by
    intro dart
    change coloring ((compositeDarts left right matching).edgeOf
        (seriesCompositeDartEquiv matching
          ((series (leftClosedPortTangle left)
            (rightClosedPortTangle right matching)).alpha dart))) =
      coloring ((compositeDarts left right matching).edgeOf
        (seriesCompositeDartEquiv matching dart))
    rw [seriesCompositeDartEquiv_alpha]
    rw [(compositeDarts left right matching).edgeOf_alpha]

/-- The pulled-back physical colouring is proper at every series vertex. -/
theorem seriesColoringOfPhysical_isProper
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R)
    (coloring : (compositeRS left right matching).EdgeColoring Color)
    (hcoloring : (compositeRS left right matching).IsTaitEdgeColoring coloring) :
    IsProper (seriesColoringOfPhysical left right matching coloring) := by
  constructor
  · rintro (dart | (empty | empty))
    · exact hcoloring
        ((compositeDarts left right matching).edgeOf
          (seriesCompositeDartEquiv matching dart))
    · exact PEmpty.elim empty
    · exact PEmpty.elim empty
  · rintro (first | (emptyFirst | emptyFirst))
      (second | (emptySecond | emptySecond)) hvert hne
    · let equiv := seriesCompositeDartEquiv (I := I) (J := J) matching
      have hphysicalVert :
          (compositeDarts left right matching).vertOf (equiv first) =
            (compositeDarts left right matching).vertOf (equiv second) := by
        calc
          (compositeDarts left right matching).vertOf (equiv first) =
              (series (leftClosedPortTangle left)
                (rightClosedPortTangle right matching)).vert
                (Sum.inl first) :=
            seriesCompositeDartEquiv_vert left right matching first
          _ = (series (leftClosedPortTangle left)
                (rightClosedPortTangle right matching)).vert
                (Sum.inl second) := hvert
          _ = (compositeDarts left right matching).vertOf (equiv second) :=
            (seriesCompositeDartEquiv_vert left right matching second).symm
      have hedgeNe :
          (compositeDarts left right matching).edgeOf (equiv first) ≠
            (compositeDarts left right matching).edgeOf (equiv second) := by
        intro hedge
        have hdart : equiv first = equiv second := by
          apply (compositeRS left right matching).edgeOf_injOn_dartsAt
            ((compositeDarts left right matching).vertOf (equiv first))
          · simp [RotationSystem.dartsAt]
          · simp [RotationSystem.dartsAt, hphysicalVert]
          · exact hedge
        apply hne
        exact congrArg Sum.inl (equiv.injective hdart)
      apply coloring.valid
      rw [RotationSystem.edgeAdjacencyGraph_adj_iff]
      refine ⟨hedgeNe,
        (compositeDarts left right matching).vertOf (equiv first), ?_, ?_⟩
      · apply (compositeRS left right matching).mem_endpoints_iff.2
        exact ⟨equiv first,
          (compositeRS left right matching).mem_dartsOn.2 rfl, rfl⟩
      · apply (compositeRS left right matching).mem_endpoints_iff.2
        exact ⟨equiv second,
          (compositeRS left right matching).mem_dartsOn.2 rfl,
          hphysicalVert.symm⟩
    · exact PEmpty.elim emptySecond
    · exact PEmpty.elim emptySecond
    · exact PEmpty.elim emptyFirst
    · exact PEmpty.elim emptyFirst
    · exact PEmpty.elim emptyFirst
    · exact PEmpty.elim emptyFirst
    · exact PEmpty.elim emptyFirst
    · exact PEmpty.elim emptyFirst

/-- The physical Tait colouring, viewed as a closed Count-side colouring. -/
noncomputable def closedColOfPhysical
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R)
    (coloring : (compositeRS left right matching).EdgeColoring Color)
    (hcoloring : (compositeRS left right matching).IsTaitEdgeColoring coloring) :
    Col (series (leftClosedPortTangle left)
      (rightClosedPortTangle right matching))
      (Sum.elim PEmpty.elim PEmpty.elim) :=
  ⟨seriesColoringOfPhysical left right matching coloring,
    seriesColoringOfPhysical_isProper left right matching coloring hcoloring,
    by
      funext port
      rcases port with empty | empty <;> exact PEmpty.elim empty⟩

/-- **Exact physical/semantic bridge.**  The abstract closed object consumed by
the Count replacement theorem is colourable exactly when the literal sewn
rotation system is Tait-colourable.  In particular this is a biconditional, not
a one-way source simulation. -/
theorem closedColorable_iff_composeRotationSystem_taitColorable
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) :
    ClosedColorable (leftClosedPortTangle left)
        (rightClosedPortTangle right matching) ↔
      ∃ coloring : (left.composeRotationSystem right matching).EdgeColoring Color,
        (left.composeRotationSystem right matching).IsTaitEdgeColoring coloring := by
  constructor
  · rintro ⟨coloring⟩
    exact ⟨physicalEdgeColoring left right matching coloring,
      physicalEdgeColoring_isTait left right matching coloring⟩
  · rintro ⟨coloring, hcoloring⟩
    exact ⟨closedColOfPhysical left right matching coloring hcoloring⟩

variable {W' J' R' : Type u}
  [Fintype W'] [DecidableEq W'] [Fintype J'] [DecidableEq J']
  [Fintype R'] [DecidableEq R']

/-- **Physical zero-Count replacement.**  Equality of the inner seam support
preserves non-colourability of the literal sewn rotation system, not merely of
an abstract semantic surrogate. -/
theorem not_composeRotationSystem_taitColorable_of_innerSupport_eq
    (left : OpenTangleData V I L)
    (right : OpenTangleData W J R) (matching : L ≃ R)
    (right' : OpenTangleData W' J' R') (matching' : L ≃ R')
    (hsupport :
      innerSupport (rightClosedPortTangle right matching) =
        innerSupport (rightClosedPortTangle right' matching'))
    (hzero : ¬ ∃ coloring :
        (left.composeRotationSystem right matching).EdgeColoring Color,
      (left.composeRotationSystem right matching).IsTaitEdgeColoring coloring) :
    ¬ ∃ coloring :
        (left.composeRotationSystem right' matching').EdgeColoring Color,
      (left.composeRotationSystem right' matching').IsTaitEdgeColoring coloring := by
  have habstractZero :
      ¬ ClosedColorable (leftClosedPortTangle left)
        (rightClosedPortTangle right matching) := by
    intro hcolorable
    exact hzero
      ((closedColorable_iff_composeRotationSystem_taitColorable
        left right matching).1 hcolorable)
  have habstractZero' :
      ¬ ClosedColorable (leftClosedPortTangle left)
        (rightClosedPortTangle right' matching') :=
    not_closedColorable_of_innerSupport_eq
      (leftClosedPortTangle left)
      (rightClosedPortTangle right matching)
      (rightClosedPortTangle right' matching')
      hsupport habstractZero
  intro hcolorable
  exact habstractZero'
    ((closedColorable_iff_composeRotationSystem_taitColorable
      left right' matching').2 hcolorable)

/-- The exact form consumed by the finite typed state: equality of the sets of
genuine Tait cut words already preserves physical non-colourability. -/
theorem not_composeRotationSystem_taitColorable_of_taitInnerSupport_eq
    (left : OpenTangleData V I L)
    (right : OpenTangleData W J R) (matching : L ≃ R)
    (right' : OpenTangleData W' J' R') (matching' : L ≃ R')
    (hsupport :
      taitInnerSupport (rightClosedPortTangle right matching) =
        taitInnerSupport (rightClosedPortTangle right' matching'))
    (hzero : ¬ ∃ coloring :
        (left.composeRotationSystem right matching).EdgeColoring Color,
      (left.composeRotationSystem right matching).IsTaitEdgeColoring coloring) :
    ¬ ∃ coloring :
        (left.composeRotationSystem right' matching').EdgeColoring Color,
      (left.composeRotationSystem right' matching').IsTaitEdgeColoring coloring :=
  not_composeRotationSystem_taitColorable_of_innerSupport_eq
    left right matching right' matching'
    (innerSupport_eq_of_taitInnerSupport_eq
      (rightClosedPortTangle right matching)
      (rightClosedPortTangle right' matching') hsupport)
    hzero

end

end GoertzelV24PhysicalClosedCountBridge

end Mettapedia.GraphTheory.FourColor
