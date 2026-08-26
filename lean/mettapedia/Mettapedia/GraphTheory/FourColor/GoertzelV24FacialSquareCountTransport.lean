import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareGraphComposition
import Mettapedia.GraphTheory.FourColor.GoertzelV24SquareLadder

/-!
# Graph-level square count transport, at the facial square itself

The profile-resolved additive identity is available in its rotation-system
form: for a facial square, a Tait colouring of the ambient map, and a tracked
colour pair, the count of a given exterior connectivity profile among the
square's proper local extensions is the sum of the counts from the two planar
reduction sides.

Nothing here is supplied by a caller.  The exterior profiles are the ambient
map's own, produced by composing the graph colouring with each local
extension, and the identity consumed below is the graph-level one rather than
its finite-interface ancestor.  What this module adds is the step the square
rung actually uses: summing that identity over a finite set of target profiles
and reading off that a vanishing total upstairs is a vanishing total on each
side.

Consequently a least zero-target instance descends through both reductions,
since a facial-square reduction removes four vertices.  No migration statement
occurs, and no all-equal overlap is used.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

namespace FacialSquareData

/-- The ambient extension count of one exterior connectivity profile. -/
noncomputable def facialSquareExtensionCount
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : RS.EdgeColoring Color) (a b : Color)
    (target : Q.ExteriorEdge → Q.ExteriorEdge → Bool) : ℕ :=
  (Q.facialSquareComposedExtensionProfileMultiset RS hdist C
    (Q.boundaryWord C) a b).count target

/-- The count contributed by one named planar reduction side. -/
noncomputable def facialSquareReductionSideCount
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : RS.EdgeColoring Color) (side : SquareReductionSide) (a b : Color)
    (target : Q.ExteriorEdge → Q.ExteriorEdge → Bool) : ℕ :=
  (Q.facialSquareComposedReductionSideProfileMultiset RS hdist C side
    (Q.boundaryWord C) a b).count target

/-- **The concrete profilewise identity.**  This is the graph-level additive
identity, restated in the count vocabulary the descent uses.  Its exterior
profiles are the ambient map's own. -/
theorem facialSquareExtensionCount_eq_add
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (target : Q.ExteriorEdge → Q.ExteriorEdge → Bool) :
    Q.facialSquareExtensionCount RS hdist C a b target =
      Q.facialSquareReductionSideCount RS hdist C .join01_23 a b target +
        Q.facialSquareReductionSideCount RS hdist C .join12_30 a b target :=
  Q.taitColoring_facialSquareComposedAdditiveProfileCountIdentity RS hdist C hC
    target a b ha hb hab

/-- **The target total is additive.** -/
theorem sum_facialSquareExtensionCount_eq_add
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (targets : Finset (Q.ExteriorEdge → Q.ExteriorEdge → Bool)) :
    (∑ target ∈ targets, Q.facialSquareExtensionCount RS hdist C a b target) =
      (∑ target ∈ targets,
          Q.facialSquareReductionSideCount RS hdist C .join01_23 a b target) +
        (∑ target ∈ targets,
          Q.facialSquareReductionSideCount RS hdist C .join12_30 a b target) :=
  GoertzelV24SquareLadder.sum_eq_add_of_profilewise targets
    (fun target =>
      Q.facialSquareExtensionCount_eq_add RS hdist C hC a b ha hb hab target)

/-- **A least zero-target instance descends through both reductions.**  The
ambient target total vanishes exactly when both reduction totals vanish. -/
theorem sum_facialSquareExtensionCount_eq_zero_iff
    (Q : @FacialSquareData V E) (hdist : Q.LocalEdgesDistinct)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (targets : Finset (Q.ExteriorEdge → Q.ExteriorEdge → Bool)) :
    (∑ target ∈ targets, Q.facialSquareExtensionCount RS hdist C a b target)
        = 0 ↔
      (∑ target ∈ targets,
          Q.facialSquareReductionSideCount RS hdist C .join01_23 a b target) = 0 ∧
        (∑ target ∈ targets,
          Q.facialSquareReductionSideCount RS hdist C .join12_30 a b target)
          = 0 :=
  GoertzelV24SquareLadder.sum_eq_zero_iff_of_profilewise targets
    (fun target =>
      Q.facialSquareExtensionCount_eq_add RS hdist C hC a b ha hb hab target)

/-- The ambient profile of a proper facial-square colouring is one of the
profiles the extension side counts, so the ambient instance really is
represented in the total. -/
theorem ambientProfile_counted
    (Q : @FacialSquareData V E) (hQ : Q.WellFormed RS)
    (hdist : Q.LocalEdgesDistinct)
    (C : RS.EdgeColoring Color)
    (hx : Q.internalColoring C ∈ squareExtensions (Q.boundaryWord C))
    (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    0 < Q.facialSquareExtensionCount RS hdist C a b
      (Q.ambientTrackedExteriorProfile RS C a b) := by
  have hmem := Q.ambientTrackedExteriorProfile_mem_composedExtensionProfiles
    RS hQ hdist C a b hx ha hb hab
  simpa [facialSquareExtensionCount] using Multiset.count_pos.mpr hmem

end FacialSquareData

end RotationSystem

end Mettapedia.GraphTheory.FourColor
