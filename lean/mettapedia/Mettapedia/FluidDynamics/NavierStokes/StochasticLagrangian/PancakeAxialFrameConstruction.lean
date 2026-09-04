import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeSquareDyadicSectorProjector

/-!
# An explicit oriented frame aligned with a unit axial direction

The pancake multiplier needs an oriented Euclidean frame whose axial
coordinate is the compressive strain direction.  A whole eigenbasis is more
than is required.  This module constructs the frame directly from one unit
vector.

For a non-axial unit vector `n`, reflection across the plane normal to
`n - e_z` sends `n` to `e_z`.  Composing it with reflection of the first
coordinate gives an orientation-preserving orthogonal map which still fixes
`e_z`.  At `n = e_z` we use the identity.  All algebraic fields of
`OrientedFrameEquiv`, including cross-product preservation and bijectivity,
are proved from the explicit formulas.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeAxialFrameConstruction

open PancakeRealCoherentPairEstimate
open PancakeFrameCovariance

/-- Coordinatewise subtraction in the algebraic three-vector model. -/
def sub (u v : RealVec3) : RealVec3 :=
  (u.1 - v.1, u.2.1 - v.2.1, u.2.2 - v.2.2)

/-- Reflection of the first coordinate. -/
def flipFirst (v : RealVec3) : RealVec3 :=
  (-v.1, v.2.1, v.2.2)

/-- Orthogonal reflection across the plane with nonzero normal `a`. -/
def reflectNormal (a v : RealVec3) : RealVec3 :=
  add v (smul (-2 * dot a v / normSq a) a)

theorem normSq_eq_zero_iff (v : RealVec3) :
    normSq v = 0 ↔ v = (0, 0, 0) := by
  obtain ⟨x, y, z⟩ := v
  simp only [normSq, dot]
  constructor
  · intro h
    have hx : x = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hy : y = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    have hz : z = 0 := by nlinarith [sq_nonneg x, sq_nonneg y, sq_nonneg z]
    simp [hx, hy, hz]
  · intro h
    injection h with hx hyz
    injection hyz with hy hz
    simp [hx, hy, hz]

theorem sub_eq_zero_iff (u v : RealVec3) :
    sub u v = (0, 0, 0) ↔ u = v := by
  obtain ⟨ux, uy, uz⟩ := u
  obtain ⟨vx, vy, vz⟩ := v
  constructor
  · intro h
    injection h with hx hyz
    injection hyz with hy hz
    apply Prod.ext
    · dsimp at hx ⊢
      linarith
    · apply Prod.ext <;> dsimp at hy hz ⊢ <;> linarith
  · intro h
    injection h with hx hyz
    injection hyz with hy hz
    simp [sub, hx, hy, hz]

theorem normSq_sub_ne_zero {u v : RealVec3} (h : u ≠ v) :
    normSq (sub u v) ≠ 0 := by
  intro hz
  exact h ((sub_eq_zero_iff u v).mp ((normSq_eq_zero_iff _).mp hz))

theorem flipFirst_involutive : Function.Involutive flipFirst := by
  rintro ⟨x, y, z⟩
  simp [flipFirst]

theorem flipFirst_map_add (u v : RealVec3) :
    flipFirst (add u v) = add (flipFirst u) (flipFirst v) := by
  obtain ⟨ux, uy, uz⟩ := u
  obtain ⟨vx, vy, vz⟩ := v
  simp only [flipFirst, add]
  apply Prod.ext
  · dsimp
    ring
  · apply Prod.ext
    · rfl
    · rfl

theorem flipFirst_map_smul (c : ℝ) (v : RealVec3) :
    flipFirst (smul c v) = smul c (flipFirst v) := by
  obtain ⟨x, y, z⟩ := v
  simp [flipFirst, smul]

theorem flipFirst_map_dot (u v : RealVec3) :
    dot (flipFirst u) (flipFirst v) = dot u v := by
  obtain ⟨ux, uy, uz⟩ := u
  obtain ⟨vx, vy, vz⟩ := v
  simp only [flipFirst, dot]
  ring

/-- A single coordinate reflection reverses the cross product. -/
theorem flipFirst_map_cross (u v : RealVec3) :
    flipFirst (cross u v) =
      smul (-1) (cross (flipFirst u) (flipFirst v)) := by
  obtain ⟨ux, uy, uz⟩ := u
  obtain ⟨vx, vy, vz⟩ := v
  simp only [flipFirst, cross, smul]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp <;> ring

theorem reflectNormal_involutive (a : RealVec3) (ha : normSq a ≠ 0) :
    Function.Involutive (reflectNormal a) := by
  intro v
  obtain ⟨ax, ay, az⟩ := a
  obtain ⟨x, y, z⟩ := v
  simp only [reflectNormal, add, smul, dot, normSq] at ha ⊢
  have ha' : ax ^ 2 + ay ^ 2 + az ^ 2 ≠ 0 := by
    simpa [pow_two] using ha
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp <;>
    field_simp [ha'] <;> ring

theorem reflectNormal_map_add (a u v : RealVec3) :
    reflectNormal a (add u v) =
      add (reflectNormal a u) (reflectNormal a v) := by
  obtain ⟨ax, ay, az⟩ := a
  obtain ⟨ux, uy, uz⟩ := u
  obtain ⟨vx, vy, vz⟩ := v
  simp only [reflectNormal, add, smul, dot, normSq]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp <;> ring

theorem reflectNormal_map_smul (a : RealVec3) (c : ℝ) (v : RealVec3) :
    reflectNormal a (smul c v) = smul c (reflectNormal a v) := by
  obtain ⟨ax, ay, az⟩ := a
  obtain ⟨x, y, z⟩ := v
  simp only [reflectNormal, add, smul, dot, normSq]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp <;> ring

theorem reflectNormal_map_dot (a u v : RealVec3)
    (ha : normSq a ≠ 0) :
    dot (reflectNormal a u) (reflectNormal a v) = dot u v := by
  obtain ⟨ax, ay, az⟩ := a
  obtain ⟨ux, uy, uz⟩ := u
  obtain ⟨vx, vy, vz⟩ := v
  simp only [reflectNormal, add, smul, dot, normSq] at ha ⊢
  have ha' : ax ^ 2 + ay ^ 2 + az ^ 2 ≠ 0 := by
    simpa [pow_two] using ha
  field_simp [ha']
  ring

/-- A reflection with nonzero normal reverses the cross product. -/
theorem reflectNormal_map_cross (a u v : RealVec3)
    (ha : normSq a ≠ 0) :
    reflectNormal a (cross u v) =
      smul (-1) (cross (reflectNormal a u) (reflectNormal a v)) := by
  obtain ⟨ax, ay, az⟩ := a
  obtain ⟨ux, uy, uz⟩ := u
  obtain ⟨vx, vy, vz⟩ := v
  simp only [reflectNormal, add, smul, dot, normSq, cross] at ha ⊢
  have ha' : ax ^ 2 + ay ^ 2 + az ^ 2 ≠ 0 := by
    simpa [pow_two] using ha
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp <;>
    field_simp [ha'] <;> ring

/-- The orientation-preserving composition of the two reflections. -/
def doubleReflectionMap (a v : RealVec3) : RealVec3 :=
  flipFirst (reflectNormal a v)

theorem doubleReflectionMap_bijective (a : RealVec3)
    (ha : normSq a ≠ 0) : Function.Bijective (doubleReflectionMap a) := by
  exact flipFirst_involutive.bijective.comp
    (reflectNormal_involutive a ha).bijective

theorem doubleReflectionMap_map_add (a u v : RealVec3) :
    doubleReflectionMap a (add u v) =
      add (doubleReflectionMap a u) (doubleReflectionMap a v) := by
  unfold doubleReflectionMap
  rw [reflectNormal_map_add, flipFirst_map_add]

theorem doubleReflectionMap_map_smul (a : RealVec3) (c : ℝ) (v : RealVec3) :
    doubleReflectionMap a (smul c v) =
      smul c (doubleReflectionMap a v) := by
  unfold doubleReflectionMap
  rw [reflectNormal_map_smul, flipFirst_map_smul]

theorem doubleReflectionMap_map_dot (a u v : RealVec3)
    (ha : normSq a ≠ 0) :
    dot (doubleReflectionMap a u) (doubleReflectionMap a v) = dot u v := by
  unfold doubleReflectionMap
  rw [flipFirst_map_dot, reflectNormal_map_dot a u v ha]

/-- Two reflections preserve orientation, hence preserve the cross product. -/
theorem doubleReflectionMap_map_cross (a u v : RealVec3)
    (ha : normSq a ≠ 0) :
    doubleReflectionMap a (cross u v) =
      cross (doubleReflectionMap a u) (doubleReflectionMap a v) := by
  unfold doubleReflectionMap
  rw [reflectNormal_map_cross a u v ha,
    flipFirst_map_smul, flipFirst_map_cross]
  obtain ⟨x, y, z⟩ := cross (flipFirst (reflectNormal a u))
    (flipFirst (reflectNormal a v))
  simp [smul]

/-- The two-reflection map packaged as the algebraic oriented frame consumed
by the pancake multiplier. -/
def doubleReflectionFrame (a : RealVec3) (ha : normSq a ≠ 0) :
    OrientedFrameEquiv where
  toFun := doubleReflectionMap a
  bijective := doubleReflectionMap_bijective a ha
  map_add := doubleReflectionMap_map_add a
  map_smul := doubleReflectionMap_map_smul a
  map_dot := fun u v ↦ doubleReflectionMap_map_dot a u v ha
  map_cross := fun u v ↦ doubleReflectionMap_map_cross a u v ha

/-- Reflection in the plane normal to `n - e_z` maps a unit `n` to `e_z`. -/
theorem doubleReflectionMap_unit_to_ez
    (n : RealVec3) (hn : normSq n = 1) (hne : n ≠ ez) :
    doubleReflectionMap (sub n ez) n = ez := by
  have ha : normSq (sub n ez) ≠ 0 := normSq_sub_ne_zero hne
  obtain ⟨x, y, z⟩ := n
  simp only [normSq, dot] at hn
  simp only [doubleReflectionMap, reflectNormal, sub, ez, add, smul,
    dot, normSq, flipFirst] at ha ⊢
  have ha' : (x - 0) ^ 2 + (y - 0) ^ 2 + (z - 1) ^ 2 ≠ 0 := by
    simpa [pow_two] using ha
  apply Prod.ext
  · dsimp
    field_simp [ha']
    linear_combination x * hn
  · apply Prod.ext
    · dsimp
      field_simp [ha']
      linear_combination -y * hn
    · dsimp
      field_simp [ha']
      linear_combination (1 - z) * hn

/-- A deterministic orientation-preserving frame which sends a given unit
direction to the axial coordinate vector `e_z`. -/
def axialFrameOfUnit (n : RealVec3) (_hn : normSq n = 1) :
    OrientedFrameEquiv :=
  if h : n = ez then identityFrame
  else doubleReflectionFrame (sub n ez) (normSq_sub_ne_zero h)

theorem axialFrameOfUnit_toFun_self
    (n : RealVec3) (hn : normSq n = 1) :
    (axialFrameOfUnit n hn).toFun n = ez := by
  by_cases h : n = ez
  · subst n
    simp [axialFrameOfUnit, identityFrame]
  · simp only [axialFrameOfUnit, dif_neg h, doubleReflectionFrame]
    exact doubleReflectionMap_unit_to_ez n hn h

/-- Pointwise frame field obtained from a field of unit axial directions.
No continuity or differentiability of the direction field is required by the
pointwise annular kernel endpoint. -/
def axialFrameFieldOfUnit {X : Type*} (n : X → RealVec3)
    (hn : ∀ x, normSq (n x) = 1) : X → OrientedFrameEquiv :=
  fun x ↦ axialFrameOfUnit (n x) (hn x)

theorem axialFrameFieldOfUnit_toFun_self {X : Type*} (n : X → RealVec3)
    (hn : ∀ x, normSq (n x) = 1) (x : X) :
    (axialFrameFieldOfUnit n hn x).toFun (n x) = ez :=
  axialFrameOfUnit_toFun_self (n x) (hn x)

end PancakeAxialFrameConstruction
end NavierStokes
end FluidDynamics
end Mettapedia
