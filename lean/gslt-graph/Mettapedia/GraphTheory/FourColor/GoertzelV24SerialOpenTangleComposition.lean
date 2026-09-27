import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenTangleComposition

/-!
# Serial composition of open tangles

The compositional source treats a corridor window as a tangle with an input
and an output interface.  Gluing the output of one window to the input of
the next leaves the outside interfaces open; it is therefore not the closed
matched-seam construction.  This file implements that serial operation on
literal dart data.  Newly glued darts become internal, while the two external
interfaces remain genuine unpaired half-edges.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenTangleComposition

open GoertzelV24RotationSpliceConstructor

noncomputable section

/-- The vertex map on a tangle with separately displayed input and output
boundary interfaces. -/
def twoSidedOpenTangleVertOf {V I L R : Type*}
    (interiorVert : I → V) (leftVert : L → V) (rightVert : R → V) :
    I ⊕ (L ⊕ R) → V
  | Sum.inl dart => interiorVert dart
  | Sum.inr (Sum.inl dart) => leftVert dart
  | Sum.inr (Sum.inr dart) => rightVert dart

/-- A literal open tangle with distinguished input and output boundary
interfaces.  Its boundary darts are deliberately unpaired; only `interior`
is closed under the edge involution. -/
structure TwoSidedOpenTangleData (V I L R : Type*) where
  interiorVert : I → V
  leftVert : L → V
  rightVert : R → V
  interiorAlpha : Equiv.Perm I
  interiorAlpha_involutive : ∀ dart,
    interiorAlpha (interiorAlpha dart) = dart
  interiorAlpha_fixfree : ∀ dart, interiorAlpha dart ≠ dart
  rho : Equiv.Perm (I ⊕ (L ⊕ R))
  vert_rho : ∀ dart,
    twoSidedOpenTangleVertOf interiorVert leftVert rightVert (rho dart) =
      twoSidedOpenTangleVertOf interiorVert leftVert rightVert dart
  interior_no_self_loops : ∀ dart,
    interiorVert dart ≠ interiorVert (interiorAlpha dart)
  outer : I ⊕ (L ⊕ R)

namespace TwoSidedOpenTangleData

variable {V W I L R J M S : Type*}

/-- Vertex map of a two-sided literal open tangle. -/
def vertOf (data : TwoSidedOpenTangleData V I L R) : I ⊕ (L ⊕ R) → V :=
  twoSidedOpenTangleVertOf data.interiorVert data.leftVert data.rightVert

/-- Reassociate the dart carriers of two tangles into the carrier of their
serial composite.  The output darts of the left tangle and input darts of the
right tangle become the middle internal seam. -/
def serialDartEquiv :
    ((I ⊕ (L ⊕ R)) ⊕ (J ⊕ (M ⊕ S))) ≃
      (((I ⊕ J) ⊕ (R ⊕ M)) ⊕ (L ⊕ S)) where
  toFun
    | Sum.inl (Sum.inl interior) => Sum.inl (Sum.inl (Sum.inl interior))
    | Sum.inl (Sum.inr (Sum.inl left)) => Sum.inr (Sum.inl left)
    | Sum.inl (Sum.inr (Sum.inr right)) => Sum.inl (Sum.inr (Sum.inl right))
    | Sum.inr (Sum.inl interior) => Sum.inl (Sum.inl (Sum.inr interior))
    | Sum.inr (Sum.inr (Sum.inl left)) => Sum.inl (Sum.inr (Sum.inr left))
    | Sum.inr (Sum.inr (Sum.inr right)) => Sum.inr (Sum.inr right)
  invFun
    | Sum.inl (Sum.inl (Sum.inl interior)) => Sum.inl (Sum.inl interior)
    | Sum.inl (Sum.inl (Sum.inr interior)) => Sum.inr (Sum.inl interior)
    | Sum.inl (Sum.inr (Sum.inl right)) => Sum.inl (Sum.inr (Sum.inr right))
    | Sum.inl (Sum.inr (Sum.inr left)) => Sum.inr (Sum.inr (Sum.inl left))
    | Sum.inr (Sum.inl left) => Sum.inl (Sum.inr (Sum.inl left))
    | Sum.inr (Sum.inr right) => Sum.inr (Sum.inr (Sum.inr right))
  left_inv := by
    intro dart
    rcases dart with (interior | (left | right)) | (interior | (left | right)) <;> rfl
  right_inv := by
    intro dart
    rcases dart with ((interior | interior) | (right | left)) | (left | right) <;> rfl

/-- The tagged vertex map before serial carrier reassociation. -/
def serialSourceVertOf
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S) :
    ((I ⊕ (L ⊕ R)) ⊕ (J ⊕ (M ⊕ S))) → V ⊕ W
  | Sum.inl dart => Sum.inl (left.vertOf dart)
  | Sum.inr dart => Sum.inr (right.vertOf dart)

/-- The tagged vertex map after serial composition. -/
def serialOutputVertOf
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S) :
    (((I ⊕ J) ⊕ (R ⊕ M)) ⊕ (L ⊕ S)) → V ⊕ W
  | Sum.inl (Sum.inl (Sum.inl interior)) => Sum.inl (left.interiorVert interior)
  | Sum.inl (Sum.inl (Sum.inr interior)) => Sum.inr (right.interiorVert interior)
  | Sum.inl (Sum.inr (Sum.inl rightBoundary)) => Sum.inl (left.rightVert rightBoundary)
  | Sum.inl (Sum.inr (Sum.inr leftBoundary)) => Sum.inr (right.leftVert leftBoundary)
  | Sum.inr (Sum.inl leftBoundary) => Sum.inl (left.leftVert leftBoundary)
  | Sum.inr (Sum.inr rightBoundary) => Sum.inr (right.rightVert rightBoundary)

/-- Carrier reassociation preserves the displayed tagged vertex map. -/
@[simp]
theorem serialOutputVertOf_serialDartEquiv
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (dart : (I ⊕ (L ⊕ R)) ⊕ (J ⊕ (M ⊕ S))) :
    serialOutputVertOf left right (serialDartEquiv dart) =
      serialSourceVertOf left right dart := by
  rcases dart with (interior | (leftBoundary | rightBoundary)) |
      (interior | (leftBoundary | rightBoundary)) <;> rfl

/-- `serialOutputVertOf` is exactly the two-sided vertex map obtained from
its three displayed output components. -/
theorem twoSidedOpenTangleVertOf_serialOutput
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (dart : (((I ⊕ J) ⊕ (R ⊕ M)) ⊕ (L ⊕ S))) :
    twoSidedOpenTangleVertOf
        (fun interior => serialOutputVertOf left right (Sum.inl interior))
        (fun leftBoundary => serialOutputVertOf left right
          (Sum.inr (Sum.inl leftBoundary)))
        (fun rightBoundary => serialOutputVertOf left right
          (Sum.inr (Sum.inr rightBoundary))) dart =
      serialOutputVertOf left right dart := by
  rcases dart with ((interior | interior) | (rightBoundary | leftBoundary)) |
      (leftBoundary | rightBoundary) <;> rfl

/-- Componentwise vertex preservation of the two source rotations. -/
theorem serialSourceVertOf_sumRho
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (dart : (I ⊕ (L ⊕ R)) ⊕ (J ⊕ (M ⊕ S))) :
    serialSourceVertOf left right
        ((Equiv.sumCongr left.rho right.rho) dart) =
      serialSourceVertOf left right dart := by
  rcases dart with dart | dart
  · simpa [serialSourceVertOf, vertOf] using
      congrArg (fun vertex : V => (Sum.inl vertex : V ⊕ W)) (left.vert_rho dart)
  · simpa [serialSourceVertOf, vertOf] using
      congrArg (fun vertex : W => (Sum.inr vertex : V ⊕ W)) (right.vert_rho dart)

/-- The edge flip on the internal darts of a serial composition: old internal
edges remain internal, while the joined output/input interfaces become a
matched seam. -/
def serialInteriorAlpha
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M) :
    Equiv.Perm ((I ⊕ J) ⊕ (R ⊕ M)) :=
  Equiv.sumCongr (Equiv.sumCongr left.interiorAlpha right.interiorAlpha)
    (MatchedSeam.seamSwap matching)

theorem serialInteriorAlpha_involutive
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M) (dart : (I ⊕ J) ⊕ (R ⊕ M)) :
    serialInteriorAlpha left right matching
      (serialInteriorAlpha left right matching dart) = dart := by
  rcases dart with (interior | interior) | (rightBoundary | leftBoundary)
  · simpa [serialInteriorAlpha] using left.interiorAlpha_involutive interior
  · simpa [serialInteriorAlpha] using right.interiorAlpha_involutive interior
  · simp [serialInteriorAlpha]
  · simp [serialInteriorAlpha]

theorem serialInteriorAlpha_fixfree
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M) (dart : (I ⊕ J) ⊕ (R ⊕ M)) :
    serialInteriorAlpha left right matching dart ≠ dart := by
  rcases dart with (interior | interior) | (rightBoundary | leftBoundary)
  · simpa [serialInteriorAlpha] using left.interiorAlpha_fixfree interior
  · simpa [serialInteriorAlpha] using right.interiorAlpha_fixfree interior
  · simp [serialInteriorAlpha]
  · simp [serialInteriorAlpha]

theorem serialInterior_no_self_loops
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M) (dart : (I ⊕ J) ⊕ (R ⊕ M)) :
    serialOutputVertOf left right (Sum.inl dart) ≠
      serialOutputVertOf left right
        (Sum.inl (serialInteriorAlpha left right matching dart)) := by
  rcases dart with (interior | interior) | (rightBoundary | leftBoundary)
  · intro hloop
    have hloop' : (Sum.inl (left.interiorVert interior) : V ⊕ W) =
        Sum.inl (left.interiorVert (left.interiorAlpha interior)) := by
      simpa [serialOutputVertOf, serialInteriorAlpha] using hloop
    exact left.interior_no_self_loops interior (Sum.inl.inj hloop')
  · intro hloop
    have hloop' : (Sum.inr (right.interiorVert interior) : V ⊕ W) =
        Sum.inr (right.interiorVert (right.interiorAlpha interior)) := by
      simpa [serialOutputVertOf, serialInteriorAlpha] using hloop
    exact right.interior_no_self_loops interior (Sum.inr.inj hloop')
  · simp [serialOutputVertOf, serialInteriorAlpha]
  · simp [serialOutputVertOf, serialInteriorAlpha]

/-- Serially glue the output interface of `left` to the input interface of
`right`.  The source vertex carriers are tagged separately, so a seam formed
from two boundary ends with extensionally equal old labels remains loop-free.
The exterior input of `left` and exterior output of `right` remain open. -/
noncomputable def serialCompose
    (left : TwoSidedOpenTangleData V I L R)
    (right : TwoSidedOpenTangleData W J M S)
    (matching : R ≃ M) :
    TwoSidedOpenTangleData (V ⊕ W) ((I ⊕ J) ⊕ (R ⊕ M)) L S where
  interiorVert := fun dart => serialOutputVertOf left right (Sum.inl dart)
  leftVert := fun dart => serialOutputVertOf left right (Sum.inr (Sum.inl dart))
  rightVert := fun dart => serialOutputVertOf left right (Sum.inr (Sum.inr dart))
  interiorAlpha := serialInteriorAlpha left right matching
  interiorAlpha_involutive := serialInteriorAlpha_involutive left right matching
  interiorAlpha_fixfree := serialInteriorAlpha_fixfree left right matching
  rho :=
    (((serialDartEquiv (I := I) (L := L) (R := R) (J := J) (M := M) (S := S)).symm.trans
      (Equiv.sumCongr left.rho right.rho)).trans
        (serialDartEquiv (I := I) (L := L) (R := R) (J := J) (M := M) (S := S)))
  vert_rho := by
    intro dart
    simp only [twoSidedOpenTangleVertOf_serialOutput]
    let equiv := serialDartEquiv (I := I) (L := L) (R := R) (J := J) (M := M) (S := S)
    change serialOutputVertOf left right
        (((equiv.symm.trans (Equiv.sumCongr left.rho right.rho)).trans equiv) dart) =
      serialOutputVertOf left right dart
    simp only [Equiv.trans_apply]
    calc
      serialOutputVertOf left right
          (equiv ((Equiv.sumCongr left.rho right.rho) (equiv.symm dart))) =
        serialSourceVertOf left right
          ((Equiv.sumCongr left.rho right.rho) (equiv.symm dart)) := by
            simp [equiv, serialOutputVertOf_serialDartEquiv]
      _ = serialSourceVertOf left right (equiv.symm dart) :=
        serialSourceVertOf_sumRho left right (equiv.symm dart)
      _ = serialOutputVertOf left right dart := by
        simpa [equiv] using
          (serialOutputVertOf_serialDartEquiv left right (equiv.symm dart)).symm
  interior_no_self_loops := serialInterior_no_self_loops left right matching
  outer := serialDartEquiv (I := I) (L := L) (R := R) (J := J) (M := M) (S := S)
    (Sum.inl left.outer)

end TwoSidedOpenTangleData

namespace OpenTangleData

variable {V I B L R : Type*}

/-- Reindex an ordinary open-tangle boundary as separately displayed left and
right interfaces. -/
def boundarySplitDartEquiv (split : B ≃ L ⊕ R) :
    I ⊕ B ≃ I ⊕ (L ⊕ R) :=
  Equiv.sumCongr (Equiv.refl I) split

/-- The displayed vertex map is unchanged when an ordinary boundary is
reindexed by a left/right split. -/
theorem twoSidedVertOf_boundarySplitDartEquiv
    (data : OpenTangleData V I B) (split : B ≃ L ⊕ R)
    (dart : I ⊕ B) :
    twoSidedOpenTangleVertOf data.interiorVert
        (fun left => data.boundaryVert (split.symm (Sum.inl left)))
        (fun right => data.boundaryVert (split.symm (Sum.inr right)))
        (boundarySplitDartEquiv split dart) = data.vertOf dart := by
  rcases dart with interior | boundary
  · rfl
  · cases hsplit : split boundary with
    | inl left =>
      rw [show boundarySplitDartEquiv (I := I) split (Sum.inr boundary) =
        Sum.inr (split boundary) by rfl, hsplit]
      change data.boundaryVert (split.symm (Sum.inl left)) =
        data.boundaryVert boundary
      apply congrArg data.boundaryVert
      apply split.injective
      simp [hsplit]
    | inr right =>
      rw [show boundarySplitDartEquiv (I := I) split (Sum.inr boundary) =
        Sum.inr (split boundary) by rfl, hsplit]
      change data.boundaryVert (split.symm (Sum.inr right)) =
        data.boundaryVert boundary
      apply congrArg data.boundaryVert
      apply split.injective
      simp [hsplit]

/-- Split the boundary of a literal open tangle into input and output
interfaces.  This changes only the displayed boundary carrier; it preserves
the old internal involution and transports the vertex rotation by the boundary
equivalence. -/
noncomputable def splitBoundary
    (data : OpenTangleData V I B) (split : B ≃ L ⊕ R) :
    TwoSidedOpenTangleData V I L R where
  interiorVert := data.interiorVert
  leftVert := fun left => data.boundaryVert (split.symm (Sum.inl left))
  rightVert := fun right => data.boundaryVert (split.symm (Sum.inr right))
  interiorAlpha := data.interiorAlpha
  interiorAlpha_involutive := data.interiorAlpha_involutive
  interiorAlpha_fixfree := data.interiorAlpha_fixfree
  rho :=
    (((boundarySplitDartEquiv split).symm.trans data.rho).trans
      (boundarySplitDartEquiv split))
  vert_rho := by
    intro dart
    let equiv := boundarySplitDartEquiv (I := I) split
    change twoSidedOpenTangleVertOf data.interiorVert
        (fun left => data.boundaryVert (split.symm (Sum.inl left)))
        (fun right => data.boundaryVert (split.symm (Sum.inr right)))
        (((equiv.symm.trans data.rho).trans equiv) dart) =
      twoSidedOpenTangleVertOf data.interiorVert
        (fun left => data.boundaryVert (split.symm (Sum.inl left)))
        (fun right => data.boundaryVert (split.symm (Sum.inr right))) dart
    simp only [Equiv.trans_apply]
    calc
      twoSidedOpenTangleVertOf data.interiorVert
          (fun left => data.boundaryVert (split.symm (Sum.inl left)))
          (fun right => data.boundaryVert (split.symm (Sum.inr right)))
          (equiv (data.rho (equiv.symm dart))) =
        data.vertOf (data.rho (equiv.symm dart)) :=
          twoSidedVertOf_boundarySplitDartEquiv data split _
      _ = data.vertOf (equiv.symm dart) := data.vert_rho _
      _ = twoSidedOpenTangleVertOf data.interiorVert
          (fun left => data.boundaryVert (split.symm (Sum.inl left)))
          (fun right => data.boundaryVert (split.symm (Sum.inr right))) dart := by
          simpa [equiv] using
            (twoSidedVertOf_boundarySplitDartEquiv data split (equiv.symm dart)).symm
  interior_no_self_loops := data.interior_no_self_loops
  outer := boundarySplitDartEquiv split data.outer

end OpenTangleData

end

end GoertzelV24OpenTangleComposition

end Mettapedia.GraphTheory.FourColor
