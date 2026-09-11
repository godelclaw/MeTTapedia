import Mettapedia.GraphTheory.FourColor.VertexTransfer
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# Colour Count does not determine the boundary gluing orientation

The same loopless cubic incidence and edge flip carry two cyclic vertex
rotations. Their open-side Count functions agree literally, but only one
rotation satisfies spherical Euler equality. Reversing the second vertex
rotation repairs the example. This is a generic gluing diagnostic, not a
counterexample to the source reduction with its geometric hypotheses.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexSpliceOrientation

open TubeSlab TubeSlab.NestedSideWire GoertzelV24RotationCutDartDecomposition
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24FaceOrbitPartitionBridge
open GoertzelV24TwoEdgeCutMinimality

abbrev Dart := Bool × Fin 3

def flip : Equiv.Perm Dart where
  toFun d := (!d.1, d.2)
  invFun d := (!d.1, d.2)
  left_inv d := by cases d with | mk b i => cases b <;> rfl
  right_inv d := by cases d with | mk b i => cases b <;> rfl

def turn (twist : Bool) (d : Dart) : Dart :=
  (d.1, d.2 + if d.1 && !twist then 2 else 1)

def rotation (twist : Bool) : Equiv.Perm Dart where
  toFun := turn twist
  invFun d := (d.1, d.2 - if d.1 && !twist then 2 else 1)
  left_inv := by cases twist <;> decide
  right_inv := by cases twist <;> decide

/-- The two-vertex, three-edge map. False gives opposite cyclic orders;
True gives equal cyclic orders and one face instead of three. -/
def theta (twist : Bool) : RotationSystem Bool (Fin 3) where
  D := Dart
  edgeOf := Prod.snd
  vertOf := Prod.fst
  alpha := flip
  rho := rotation twist
  alpha_involutive := by decide
  alpha_fixfree := by decide
  edge_alpha := by decide
  edge_fiber_two := by decide
  vert_rho := by intro d; rfl
  outer := (false, 0)
  no_self_loops := by decide

theorem cubic (twist : Bool) : (theta twist).IsCubic := by
  unfold RotationSystem.IsCubic
  cases twist <;> decide

theorem cyclic (twist : Bool) :
    GoertzelV24FaceDualConnectedness.VertexRotationCyclic (theta twist) := by
  unfold GoertzelV24FaceDualConnectedness.VertexRotationCyclic
  cases twist <;> decide

theorem faces_flat : (theta false).phi.partition.parts.card = 3 := by decide
theorem faces_twisted : (theta true).phi.partition.parts.card = 1 := by decide

/-- Copy the same dart colours; cyclic order does not occur in properness. -/
def sideEquiv (keep : Bool → Prop) :
    SideColoring (theta false) keep ≃ SideColoring (theta true) keep where
  toFun c := ⟨c.color, c.alpha_internal, c.ne_zero, c.proper⟩
  invFun c := ⟨c.color, c.alpha_internal, c.ne_zero, c.proper⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equality of actual open-side supports, not merely their cardinalities. -/
theorem same_side_support (keep : Bool → Prop) : sideSupport (theta false) keep =
    sideSupport (theta true) keep := by
  ext w
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨sideEquiv keep c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨(sideEquiv keep).symm c, hc⟩

def wordEquiv {keep : Bool → Prop} (w : BoundaryDart (theta false) keep → Color) :
    WordColoring (RS := theta false) w ≃ WordColoring (RS := theta true) w where
  toFun c := ⟨sideEquiv keep c.1, c.2⟩
  invFun c := ⟨(sideEquiv keep).symm c.1, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Even exact multiplicities, for every boundary word, do not see this
change of cyclic vertex order. -/
theorem same_side_count {keep : Bool → Prop} (w : BoundaryDart (theta false) keep → Color) :
    sideCount (RS := theta false) w = sideCount (RS := theta true) w :=
  Nat.card_congr (wordEquiv w)

theorem colorable (twist : Bool) : RotationSystemTaitColorable (theta twist) := by
  let colors : Fin 3 → Color := ![(1, 0), (0, 1), (1, 1)]
  refine ⟨⟨colors, ?_⟩, ?_⟩
  · intro e f h
    change colors e ≠ colors f
    have hne : e ≠ f := h.1
    have hinj : Function.Injective colors := by decide
    exact fun he => hne (hinj he)
  · change ∀ e, colors e ≠ 0
    decide

def flat_spherical : OrbitSphericalCubicMapData (theta false) where
  cubic := cubic false
  euler := by
    rw [card_orbitFace_eq_faceCycleLengths_card]
    change (2 : Int) - 3 + ((theta false).phi.partition.parts.card : Int) = 2
    rw [faces_flat]
    norm_num

/-- The corresponding wrong-orientation splice is outside the spherical
minimality class, despite unchanged colour Count. -/
theorem twisted_not_spherical : ¬ Nonempty (OrbitSphericalCubicMapData (theta true)) := by
  rintro ⟨h⟩
  have he := h.euler
  rw [card_orbitFace_eq_faceCycleLengths_card] at he
  change (2 : Int) - 3 + ((theta true).phi.partition.parts.card : Int) = 2 at he
  rw [faces_twisted] at he
  norm_num at he

/-- Even the complete Count function of the varying half cannot classify
sphericity after gluing to the fixed other half in the stored coordinates. -/
theorem no_count_only_sphericity :
    ¬ ∃ classify : ((BoundaryDart (theta false) (fun b => b = true) → Color) → ℕ) → Prop,
      ∀ twist : Bool,
        classify (fun w => sideCount (RS := theta twist) (keep := fun b => b = true) w) ↔
        Nonempty (OrbitSphericalCubicMapData (theta twist)) := by
  rintro ⟨classify, h⟩
  have hc := (h false).2 ⟨flat_spherical⟩
  have heq : (fun w : BoundaryDart (theta false) (fun b => b = true) → Color =>
      sideCount (RS := theta false) (keep := fun b => b = true) w) =
      (fun w => sideCount (RS := theta true) (keep := fun b => b = true) w) :=
    funext same_side_count
  rw [heq] at hc
  exact twisted_not_spherical ((h true).1 hc)

end Mettapedia.GraphTheory.FourColor.VertexSpliceOrientation
