import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Finset.Sym
import Mettapedia.GraphTheory.FourColor.RotationSystem

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationSpliceConstructor

open Sym2

noncomputable section

/-- Rotation data before naming edges. This is the natural output of a dart
splice: the vertex rotation is retained, while the fixed-point-free dart
involution is rewired across the new seam. -/
structure RewiredDartSystem (V D : Type*)
    [Fintype V] [DecidableEq V] [Fintype D] [DecidableEq D] where
  vertOf : D → V
  alpha : Equiv.Perm D
  rho : Equiv.Perm D
  alpha_involutive : ∀ dart, alpha (alpha dart) = dart
  alpha_fixfree : ∀ dart, alpha dart ≠ dart
  vert_rho : ∀ dart, vertOf (rho dart) = vertOf dart
  outer : D
  no_self_loops : ∀ dart, vertOf dart ≠ vertOf (alpha dart)

namespace RewiredDartSystem

variable {V D : Type*} [Fintype V] [DecidableEq V]
  [Fintype D] [DecidableEq D]

/-- An edge is a two-dart orbit of the rewired involution, represented by its
unordered dart pair. The existential predicate is decidable on the finite
dart carrier. -/
def Edge (data : RewiredDartSystem V D) :=
  {pair : Sym2 D // ∃ dart, pair = s(dart, data.alpha dart)}

noncomputable instance instFintypeEdge (data : RewiredDartSystem V D) :
    Fintype data.Edge := by
  classical
  apply Fintype.ofFinset
    (Finset.univ.filter fun pair : Sym2 D =>
      ∃ dart, pair = s(dart, data.alpha dart))
  intro pair
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> intro h <;> exact h

instance instDecidableEqEdge (data : RewiredDartSystem V D) :
    DecidableEq data.Edge := Classical.decEq data.Edge

/-- The computed involution orbit containing a dart. -/
def edgeOf (data : RewiredDartSystem V D) (dart : D) : data.Edge :=
  ⟨s(dart, data.alpha dart), ⟨dart, rfl⟩⟩

@[simp]
theorem edgeOf_val (data : RewiredDartSystem V D) (dart : D) :
    (data.edgeOf dart).val = s(dart, data.alpha dart) :=
  rfl

/-- Two darts name the same computed edge exactly when they are equal or
opposite under the rewired involution. -/
theorem edgeOf_eq_edgeOf_iff (data : RewiredDartSystem V D) (left right : D) :
    data.edgeOf left = data.edgeOf right ↔
      left = right ∨ left = data.alpha right := by
  constructor
  · intro hedges
    have hpairs :
        s(left, data.alpha left) = s(right, data.alpha right) :=
      congrArg Subtype.val hedges
    rcases Sym2.eq_iff.1 hpairs with hsame | hswapped
    · exact Or.inl hsame.1
    · exact Or.inr hswapped.1
  · rintro (rfl | hswap)
    · rfl
    · subst left
      apply Subtype.ext
      change s(data.alpha right, data.alpha (data.alpha right)) =
        s(right, data.alpha right)
      rw [data.alpha_involutive]
      exact Sym2.eq_swap

/-- Applying the rewired involution preserves the computed edge. -/
@[simp]
theorem edgeOf_alpha (data : RewiredDartSystem V D) (dart : D) :
    data.edgeOf (data.alpha dart) = data.edgeOf dart := by
  exact (data.edgeOf_eq_edgeOf_iff (data.alpha dart) dart).2 (Or.inr rfl)

/-- The complete fiber over a computed edge is its defining two-dart orbit. -/
theorem edgeFiber_eq_pair (data : RewiredDartSystem V D) (dart : D) :
    Finset.univ.filter (fun other => data.edgeOf other = data.edgeOf dart) =
      {dart, data.alpha dart} := by
  ext other
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  exact data.edgeOf_eq_edgeOf_iff other dart

/-- Every computed edge has exactly two darts. -/
theorem edge_fiber_two (data : RewiredDartSystem V D) (edge : data.Edge) :
    (Finset.univ.filter (fun dart => data.edgeOf dart = edge)).card = 2 := by
  rcases edge.property with ⟨dart, hdart⟩
  have hedge : edge = data.edgeOf dart := Subtype.ext hdart
  subst edge
  rw [data.edgeFiber_eq_pair]
  have hne : dart ≠ data.alpha dart := (data.alpha_fixfree dart).symm
  simp [hne]

/-- Complete rotation system generated from rewired dart data. No edge-fiber
or planarity fact is assumed: edge names and two-dart fibers are computed
from the involution. -/
def toRotationSystem (data : RewiredDartSystem V D) :
    RotationSystem V data.Edge where
  D := D
  edgeOf := data.edgeOf
  vertOf := data.vertOf
  alpha := data.alpha
  rho := data.rho
  alpha_involutive := data.alpha_involutive
  alpha_fixfree := data.alpha_fixfree
  edge_alpha := data.edgeOf_alpha
  edge_fiber_two := data.edge_fiber_two
  vert_rho := data.vert_rho
  outer := data.outer
  no_self_loops := data.no_self_loops

@[simp]
theorem toRotationSystem_edgeOf (data : RewiredDartSystem V D) (dart : D) :
    data.toRotationSystem.edgeOf dart = data.edgeOf dart :=
  rfl

@[simp]
theorem toRotationSystem_vertOf (data : RewiredDartSystem V D) (dart : D) :
    data.toRotationSystem.vertOf dart = data.vertOf dart :=
  rfl

@[simp]
theorem toRotationSystem_alpha (data : RewiredDartSystem V D) (dart : D) :
    data.toRotationSystem.alpha dart = data.alpha dart :=
  rfl

@[simp]
theorem toRotationSystem_rho (data : RewiredDartSystem V D) (dart : D) :
    data.toRotationSystem.rho dart = data.rho dart :=
  rfl

end RewiredDartSystem

namespace MatchedSeam

variable {V I L R : Type*}

/-- The dart carrier after removing an open corridor segment: intact darts,
followed by the two exposed sides of the new seam. -/
abbrev Dart (I L R : Type*) := I ⊕ (L ⊕ R)

/-- A matching between the two exposed sides induces the seam edge flip. -/
def seamSwap (matching : L ≃ R) : Equiv.Perm (L ⊕ R) where
  toFun
    | Sum.inl left => Sum.inr (matching left)
    | Sum.inr right => Sum.inl (matching.symm right)
  invFun
    | Sum.inl left => Sum.inr (matching left)
    | Sum.inr right => Sum.inl (matching.symm right)
  left_inv := by
    intro side
    cases side <;> simp
  right_inv := by
    intro side
    cases side <;> simp

@[simp]
theorem seamSwap_left (matching : L ≃ R) (left : L) :
    seamSwap matching (Sum.inl left) = Sum.inr (matching left) :=
  rfl

@[simp]
theorem seamSwap_right (matching : L ≃ R) (right : R) :
    seamSwap matching (Sum.inr right) = Sum.inl (matching.symm right) :=
  rfl

/-- The seam flip is involutive by construction. -/
theorem seamSwap_involutive (matching : L ≃ R) (side : L ⊕ R) :
    seamSwap matching (seamSwap matching side) = side := by
  cases side <;> simp

/-- The seam flip has no fixed dart because it exchanges the two summands. -/
theorem seamSwap_fixfree (matching : L ≃ R) (side : L ⊕ R) :
    seamSwap matching side ≠ side := by
  cases side <;> simp

/-- Data used by the matched-seam constructor. In particular, this record does
not contain involutivity, fixed-point freedom, edge fibers, or a rotation-system
conclusion: those facts are derived below. -/
structure Data (V I L R : Type*) where
  interiorVert : I → V
  leftVert : L → V
  rightVert : R → V
  interiorAlpha : Equiv.Perm I
  matching : L ≃ R
  rho : Equiv.Perm (Dart I L R)
  outer : Dart I L R

namespace Data

/-- Vertex projection on the decomposed retained-dart carrier. -/
def vertOf (data : Data V I L R) : Dart I L R → V
  | Sum.inl interior => data.interiorVert interior
  | Sum.inr (Sum.inl left) => data.leftVert left
  | Sum.inr (Sum.inr right) => data.rightVert right

/-- The global edge flip retains the old flip on intact darts and uses the
specified side matching on exposed seam darts. -/
def alpha (data : Data V I L R) : Equiv.Perm (Dart I L R) :=
  Equiv.sumCongr data.interiorAlpha (seamSwap data.matching)

@[simp]
theorem alpha_interior (data : Data V I L R) (interior : I) :
    data.alpha (Sum.inl interior) = Sum.inl (data.interiorAlpha interior) :=
  rfl

@[simp]
theorem alpha_left (data : Data V I L R) (left : L) :
    data.alpha (Sum.inr (Sum.inl left)) =
      Sum.inr (Sum.inr (data.matching left)) :=
  rfl

@[simp]
theorem alpha_right (data : Data V I L R) (right : R) :
    data.alpha (Sum.inr (Sum.inr right)) =
      Sum.inr (Sum.inl (data.matching.symm right)) :=
  rfl

/-- Involutivity of the global flip is derived from the intact flip law and the
two-sided seam matching. -/
theorem alpha_involutive (data : Data V I L R)
    (hInterior : ∀ interior,
      data.interiorAlpha (data.interiorAlpha interior) = interior)
    (dart : Dart I L R) :
    data.alpha (data.alpha dart) = dart := by
  rcases dart with interior | side
  · simp [hInterior]
  · rcases side with left | right <;> simp

/-- Fixed-point freedom of the global flip is derived from fixed-point freedom
on intact darts; seam darts cannot be fixed because their side changes. -/
theorem alpha_fixfree (data : Data V I L R)
    (hInterior : ∀ interior, data.interiorAlpha interior ≠ interior)
    (dart : Dart I L R) :
    data.alpha dart ≠ dart := by
  rcases dart with interior | side
  · simp [hInterior]
  · rcases side with left | right <;> simp

/-- Matching-oriented endpoint separation implies absence of self-loops on
both orientations of every newly created seam edge. -/
theorem no_self_loops (data : Data V I L R)
    (hInterior : ∀ interior,
      data.interiorVert interior ≠
        data.interiorVert (data.interiorAlpha interior))
    (hSeam : ∀ left,
      data.leftVert left ≠ data.rightVert (data.matching left))
    (dart : Dart I L R) :
    data.vertOf dart ≠ data.vertOf (data.alpha dart) := by
  rcases dart with interior | side
  · exact hInterior interior
  · rcases side with left | right
    · exact hSeam left
    · simpa [vertOf] using (hSeam (data.matching.symm right)).symm

variable [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I]
  [Fintype L] [DecidableEq L]
  [Fintype R] [DecidableEq R]

/-- Build the complete rewired-dart system from an explicit seam matching.
Only the retained vertex rotation and its vertex-preservation law remain input;
all edge-orbit laws are computed by the constructor. -/
def toRewiredDartSystem (data : Data V I L R)
    (hInteriorInvolutive : ∀ interior,
      data.interiorAlpha (data.interiorAlpha interior) = interior)
    (hInteriorFixfree : ∀ interior,
      data.interiorAlpha interior ≠ interior)
    (hRho : ∀ dart, data.vertOf (data.rho dart) = data.vertOf dart)
    (hInteriorNoLoops : ∀ interior,
      data.interiorVert interior ≠
        data.interiorVert (data.interiorAlpha interior))
    (hSeamNoLoops : ∀ left,
      data.leftVert left ≠ data.rightVert (data.matching left)) :
    RewiredDartSystem V (Dart I L R) where
  vertOf := data.vertOf
  alpha := data.alpha
  rho := data.rho
  alpha_involutive := data.alpha_involutive hInteriorInvolutive
  alpha_fixfree := data.alpha_fixfree hInteriorFixfree
  vert_rho := hRho
  outer := data.outer
  no_self_loops := data.no_self_loops hInteriorNoLoops hSeamNoLoops

end Data

end MatchedSeam

end


end GoertzelV24RotationSpliceConstructor

end Mettapedia.GraphTheory.FourColor
