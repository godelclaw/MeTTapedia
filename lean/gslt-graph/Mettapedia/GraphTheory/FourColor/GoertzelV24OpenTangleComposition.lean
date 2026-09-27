import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationCutDartDecomposition

/-!
# Composition of literal open tangles

The compositional source treats a corridor slab as an open planar instance:
its intact darts retain their old edge involution, while its boundary darts
are unpaired half-edges.  Two such *disjoint* instances compose by matching
their boundary half-edges.  This file supplies that combinatorial-map
operation directly.

The construction is deliberately below coloring and profile semantics.  Its
only job is to turn a pair of open pieces into a loop-free rewired rotation
system.  The source-specific layer construction will later provide the two
pieces and prove that their boundary words agree.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenTangleComposition

open GoertzelV24RotationSpliceConstructor
open GoertzelV24RotationCutDartDecomposition

noncomputable section

/-- Vertex map on a literal open-tangle carrier. -/
def openTangleVertOf {V I B : Type*}
    (interiorVert : I → V) (boundaryVert : B → V) : I ⊕ B → V
  | Sum.inl dart => interiorVert dart
  | Sum.inr dart => boundaryVert dart

/-- A finite open tangle with a distinguished collection of unpaired boundary
half-edges.  `interior` is closed under the old edge involution; `boundary`
is deliberately not.  The vertex rotation still acts on all darts, so the
data retains the literal cyclic order at every old vertex. -/
structure OpenTangleData (V I B : Type*) where
  interiorVert : I → V
  boundaryVert : B → V
  interiorAlpha : Equiv.Perm I
  interiorAlpha_involutive : ∀ dart,
    interiorAlpha (interiorAlpha dart) = dart
  interiorAlpha_fixfree : ∀ dart, interiorAlpha dart ≠ dart
  rho : Equiv.Perm (I ⊕ B)
  vert_rho : ∀ dart,
    openTangleVertOf interiorVert boundaryVert (rho dart) =
      openTangleVertOf interiorVert boundaryVert dart
  interior_no_self_loops : ∀ dart,
    interiorVert dart ≠ interiorVert (interiorAlpha dart)
  outer : I ⊕ B

namespace OpenTangleData

variable {V I B : Type*}

/-- Vertex map of the literal open tangle. -/
def vertOf (data : OpenTangleData V I B) : I ⊕ B → V :=
  openTangleVertOf data.interiorVert data.boundaryVert

/-- The two summands in an open tangle retain their displayed vertex maps. -/
@[simp]
theorem vertOf_interior (data : OpenTangleData V I B) (dart : I) :
    data.vertOf (Sum.inl dart) = data.interiorVert dart :=
  rfl

@[simp]
theorem vertOf_boundary (data : OpenTangleData V I B) (dart : B) :
    data.vertOf (Sum.inr dart) = data.boundaryVert dart :=
  rfl

/-- The retained vertex named by a dart on one side of a vertex cut. -/
def vertexSideVertex {E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (keep : V → Prop)
    (dart : RetainedDart RS keep) : { vertex : V // keep vertex } :=
  ⟨RS.vertOf dart.1, dart.2⟩

/-- The retained-dart partition preserves the displayed vertex when an
interior or boundary dart is viewed as an open-tangle dart. -/
@[simp]
theorem openTangleVertOf_vertexSide_partition_symm {E : Type*}
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (keep : V → Prop)
    (dart : InternalDart RS keep ⊕ BoundaryDart RS keep) :
    openTangleVertOf
        (fun internal : InternalDart RS keep => vertexSideVertex RS keep internal.1)
        (fun boundary : BoundaryDart RS keep => vertexSideVertex RS keep boundary.1)
        dart =
      vertexSideVertex RS keep
        ((retainedDartEquivInternalSumBoundary RS keep).symm dart) := by
  rcases dart with internal | boundary <;> rfl

/-- A literal vertex-side open tangle: all retained internal darts keep their
old involution, while every retained boundary dart is a genuine unpaired
half-edge.  This is the concrete bridge from a planar deletion component to
the source's category of open instances. -/
noncomputable def ofVertexSide {E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep) :
    OpenTangleData { vertex : V // keep vertex }
      (InternalDart RS keep) (BoundaryDart RS keep) where
  interiorVert := fun dart => vertexSideVertex RS keep dart.1
  boundaryVert := fun dart => vertexSideVertex RS keep dart.1
  interiorAlpha := internalAlpha RS keep
  interiorAlpha_involutive := internalAlpha_involutive RS keep
  interiorAlpha_fixfree := internalAlpha_fixfree RS keep
  rho :=
    (((retainedDartEquivInternalSumBoundary RS keep).symm.trans
      (retainedRho RS keep)).trans
        (retainedDartEquivInternalSumBoundary RS keep))
  vert_rho := by
    intro dart
    change openTangleVertOf
        (fun internal : InternalDart RS keep => vertexSideVertex RS keep internal.1)
        (fun boundary : BoundaryDart RS keep => vertexSideVertex RS keep boundary.1)
        ((retainedDartEquivInternalSumBoundary RS keep)
          (retainedRho RS keep
            ((retainedDartEquivInternalSumBoundary RS keep).symm dart))) =
      openTangleVertOf
        (fun internal : InternalDart RS keep => vertexSideVertex RS keep internal.1)
        (fun boundary : BoundaryDart RS keep => vertexSideVertex RS keep boundary.1)
        dart
    simp only [openTangleVertOf_vertexSide_partition_symm,
      Equiv.symm_apply_apply]
    apply Subtype.ext
    exact RS.vert_rho
      ((retainedDartEquivInternalSumBoundary RS keep).symm dart).1
  interior_no_self_loops := by
    intro dart hloop
    apply RS.no_self_loops dart.1.1
    exact congrArg Subtype.val hloop
  outer := retainedDartEquivInternalSumBoundary RS keep outer

/-- The old vertex rotation acts literally on the underlying retained dart of
the corresponding open tangle. -/
theorem ofVertexSide_rho_underlying {E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : RetainedDart RS keep)
    (dart : InternalDart RS keep ⊕ BoundaryDart RS keep) :
    (retainedDartEquivInternalSumBoundary RS keep).symm
      ((ofVertexSide RS keep outer).rho dart) =
      retainedRho RS keep
        ((retainedDartEquivInternalSumBoundary RS keep).symm dart) := by
  change (retainedDartEquivInternalSumBoundary RS keep).symm
      ((retainedDartEquivInternalSumBoundary RS keep)
        (retainedRho RS keep
          ((retainedDartEquivInternalSumBoundary RS keep).symm dart))) =
    retainedRho RS keep
      ((retainedDartEquivInternalSumBoundary RS keep).symm dart)
  simp

end OpenTangleData

/-- Reassociate the disjoint union of two open-tangle dart carriers into the
three-part carrier consumed by `MatchedSeam.Data`: intact darts first, then
the left and right boundary interfaces. -/
def composeDartEquiv {I L J R : Type*} :
    ((I ⊕ L) ⊕ (J ⊕ R)) ≃ MatchedSeam.Dart (I ⊕ J) L R where
  toFun
    | Sum.inl (Sum.inl interior) => Sum.inl (Sum.inl interior)
    | Sum.inl (Sum.inr left) => Sum.inr (Sum.inl left)
    | Sum.inr (Sum.inl interior) => Sum.inl (Sum.inr interior)
    | Sum.inr (Sum.inr right) => Sum.inr (Sum.inr right)
  invFun
    | Sum.inl (Sum.inl interior) => Sum.inl (Sum.inl interior)
    | Sum.inl (Sum.inr interior) => Sum.inr (Sum.inl interior)
    | Sum.inr (Sum.inl left) => Sum.inl (Sum.inr left)
    | Sum.inr (Sum.inr right) => Sum.inr (Sum.inr right)
  left_inv := by
    intro dart
    rcases dart with (interior | left) | (interior | right) <;> rfl
  right_inv := by
    intro dart
    rcases dart with (interior | interior) | (left | right) <;> rfl

@[simp]
theorem composeDartEquiv_left_interior {I L J R : Type*} (dart : I) :
    composeDartEquiv (I := I) (L := L) (J := J) (R := R)
        (Sum.inl (Sum.inl dart)) =
      Sum.inl (Sum.inl dart) :=
  rfl

@[simp]
theorem composeDartEquiv_left_boundary {I L J R : Type*} (dart : L) :
    composeDartEquiv (I := I) (L := L) (J := J) (R := R)
        (Sum.inl (Sum.inr dart)) =
      Sum.inr (Sum.inl dart) :=
  rfl

@[simp]
theorem composeDartEquiv_right_interior {I L J R : Type*} (dart : J) :
    composeDartEquiv (I := I) (L := L) (J := J) (R := R)
        (Sum.inr (Sum.inl dart)) =
      Sum.inl (Sum.inr dart) :=
  rfl

@[simp]
theorem composeDartEquiv_right_boundary {I L J R : Type*} (dart : R) :
    composeDartEquiv (I := I) (L := L) (J := J) (R := R)
        (Sum.inr (Sum.inr dart)) =
      Sum.inr (Sum.inr dart) :=
  rfl

namespace OpenTangleData

variable {V W I L J R : Type*}

/-- The vertex map on the disjoint union of two open-tangle carriers. -/
def disjointVertOf
    (left : OpenTangleData V I L) (right : OpenTangleData W J R) :
    ((I ⊕ L) ⊕ (J ⊕ R)) → V ⊕ W
  | Sum.inl dart => Sum.inl (left.vertOf dart)
  | Sum.inr dart => Sum.inr (right.vertOf dart)

/-- The dart data obtained by composing two disjoint open tangles along a
matching of their boundary interfaces.  The vertex carrier is a sum on
purpose: a newly sewn edge joins a vertex of the left piece to a vertex of
the right piece, so it cannot become a self-loop merely because the two
pieces happened to use extensionally equal source labels. -/
noncomputable def composeData
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) :
    MatchedSeam.Data (V ⊕ W) (I ⊕ J) L R where
  interiorVert
    | Sum.inl dart => Sum.inl (left.interiorVert dart)
    | Sum.inr dart => Sum.inr (right.interiorVert dart)
  leftVert := fun dart => Sum.inl (left.boundaryVert dart)
  rightVert := fun dart => Sum.inr (right.boundaryVert dart)
  interiorAlpha := Equiv.sumCongr left.interiorAlpha right.interiorAlpha
  matching := matching
  rho :=
    ((composeDartEquiv (I := I) (L := L) (J := J) (R := R)).symm.trans
      (Equiv.sumCongr left.rho right.rho)).trans
        (composeDartEquiv (I := I) (L := L) (J := J) (R := R))
  outer := composeDartEquiv (I := I) (L := L) (J := J) (R := R)
    (Sum.inl left.outer)

/-- The composed dart data uses exactly the disjoint vertex map before the
carrier reassociation. -/
@[simp]
theorem composeData_vertOf_composeDartEquiv
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (dart : (I ⊕ L) ⊕ (J ⊕ R)) :
    (left.composeData right matching).vertOf
        (composeDartEquiv (I := I) (L := L) (J := J) (R := R) dart) =
      disjointVertOf left right dart := by
  rcases dart with (dart | dart) | (dart | dart) <;> rfl

/-- Each source tangle's rotation preserves the disjoint tagged vertex map. -/
theorem disjointVertOf_sumRho
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (dart : (I ⊕ L) ⊕ (J ⊕ R)) :
    disjointVertOf left right
        ((Equiv.sumCongr left.rho right.rho) dart) =
      disjointVertOf left right dart := by
  rcases dart with dart | dart
  · simpa [disjointVertOf, vertOf] using left.vert_rho dart
  · simpa [disjointVertOf, vertOf] using right.vert_rho dart

/-- The composed rotation is conjugate to the disjoint sum of the two input
rotations through `composeDartEquiv`. -/
@[simp]
theorem composeData_rho_apply
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (dart : MatchedSeam.Dart (I ⊕ J) L R) :
    (left.composeData right matching).rho dart =
      composeDartEquiv (I := I) (L := L) (J := J) (R := R)
        ((Equiv.sumCongr left.rho right.rho)
          ((composeDartEquiv (I := I) (L := L) (J := J) (R := R)).symm dart)) :=
  rfl

/-- The assembled rotation still preserves the displayed vertex map.  This
is inherited componentwise from the two source tangles; the reassociation of
the dart carrier does not identify any vertices. -/
theorem composeData_vert_rho
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (dart : MatchedSeam.Dart (I ⊕ J) L R) :
    (left.composeData right matching).vertOf
        ((left.composeData right matching).rho dart) =
      (left.composeData right matching).vertOf dart := by
  let equiv := composeDartEquiv (I := I) (L := L) (J := J) (R := R)
  calc
    (left.composeData right matching).vertOf
        ((left.composeData right matching).rho dart) =
      disjointVertOf left right
        ((Equiv.sumCongr left.rho right.rho) (equiv.symm dart)) := by
          rw [composeData_rho_apply]
          exact composeData_vertOf_composeDartEquiv left right matching _
    _ = disjointVertOf left right (equiv.symm dart) :=
      disjointVertOf_sumRho left right (equiv.symm dart)
    _ = (left.composeData right matching).vertOf dart := by
      simpa [equiv] using
        (composeData_vertOf_composeDartEquiv left right matching
          (equiv.symm dart)).symm

/-- The intact edge involution remains involutive after taking the disjoint
sum of the two open pieces. -/
theorem composeData_interiorAlpha_involutive
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (dart : I ⊕ J) :
    (left.composeData right matching).interiorAlpha
        ((left.composeData right matching).interiorAlpha dart) = dart := by
  rcases dart with dart | dart
  · simpa [composeData] using congrArg (fun value : I =>
      (Sum.inl value : I ⊕ J))
      (left.interiorAlpha_involutive dart)
  · simpa [composeData] using congrArg (fun value : J =>
      (Sum.inr value : I ⊕ J))
      (right.interiorAlpha_involutive dart)

/-- The intact edge involution remains fixed-point-free after taking the
disjoint sum of the two open pieces. -/
theorem composeData_interiorAlpha_fixfree
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (dart : I ⊕ J) :
    (left.composeData right matching).interiorAlpha dart ≠ dart := by
  rcases dart with dart | dart
  · intro h
    apply left.interiorAlpha_fixfree dart
    exact Sum.inl.inj h
  · intro h
    apply right.interiorAlpha_fixfree dart
    exact Sum.inr.inj h

/-- Intact edges remain loop-free under disjoint open-tangle composition. -/
theorem composeData_interior_no_self_loops
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (dart : I ⊕ J) :
    (left.composeData right matching).interiorVert dart ≠
      (left.composeData right matching).interiorVert
        ((left.composeData right matching).interiorAlpha dart) := by
  rcases dart with dart | dart
  · simpa [composeData] using left.interior_no_self_loops dart
  · simpa [composeData] using right.interior_no_self_loops dart

/-- A newly sewn edge joins separate tagged copies of the two input tangles,
so no boundary matching can create a self-loop.  This is the point at which
the source's open-instance formulation avoids the false old-vertex condition
encountered by a local Cell-3 tile. -/
theorem composeData_seam_no_self_loops
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (dart : L) :
    (left.composeData right matching).leftVert dart ≠
      (left.composeData right matching).rightVert (matching dart) := by
  simp [composeData]

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype L] [DecidableEq L]
  [Fintype J] [DecidableEq J] [Fintype R] [DecidableEq R]

/-- The closed combinatorial-map output of gluing two literal open tangles
along a matching boundary interface.  All rotation-system edge laws are
computed by the generic matched-seam constructor. -/
noncomputable def composeRotationSystem
    (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) :
    RotationSystem (V ⊕ W) ((left.composeData right matching).toRewiredDartSystem
      (left.composeData_interiorAlpha_involutive right matching)
      (left.composeData_interiorAlpha_fixfree right matching)
      (left.composeData_vert_rho right matching)
      (left.composeData_interior_no_self_loops right matching)
      (left.composeData_seam_no_self_loops right matching)).Edge :=
  ((left.composeData right matching).toRewiredDartSystem
    (left.composeData_interiorAlpha_involutive right matching)
    (left.composeData_interiorAlpha_fixfree right matching)
    (left.composeData_vert_rho right matching)
    (left.composeData_interior_no_self_loops right matching)
    (left.composeData_seam_no_self_loops right matching)).toRotationSystem

end OpenTangleData

end

end GoertzelV24OpenTangleComposition

end Mettapedia.GraphTheory.FourColor
