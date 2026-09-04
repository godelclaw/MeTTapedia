import Mathlib

/-
# Pancake-cone pairwise stretching: the direction dichotomy

The dyadic pancake closure's open pin (`ScaleLocalPancakeStrainBudget`)
was proposed with a Biot-Savart self-depletion mechanism gated on the
*wavevector* cone of aperture `delta_q = lambda_q^{-1/2}`.  The
pre-registered kinematic lab
(`scripts/validation_lab/ns_pancake_kinematic_depletion_lab.py`) found:
aggregate cone gain is exactly the cone measure (`delta^2`), while the
worst *pair* coefficient saturates the generic maximum `1/2` at every
aperture.  This module distills the lab's finding into two exact
identities on a single wavevector pair, entirely inside the cone:

* **Saturation.**  The axial vorticity mode `k1 = (0,0,m)`, `w1 = e_x`
  stretches the vorticity direction `w2 = e_y` of the receiving cone
  mode `k2 = (1,0,M)` with normalized coefficient exactly `1/2` — the
  generic maximum — for every `m, M`.  Wavevector-cone confinement
  alone provides NO pairwise depletion.

* **Aligned depletion.**  The same source acting on the same receiver's
  *in-plane-aligned* polarization `w2 = (-M,0,1)` (the one parallel to
  `w1` up to the divergence-free tilt) has squared coefficient exactly
  `1/(4 (1 + M^2))` — a full inverse-square power of the receiver
  frequency, far stronger than any aperture power.

Consequently the self-depletion envelope of the pancake budget cannot be
proved from wavevector-cone geometry: the operative small parameter is
the *vorticity-direction misalignment* inside the pancake (the
Constantin–Fefferman coherence quantity), and the correct refinement of
the pin constrains direction coherence, not only the wavevector cone.

The stretching coefficient is the amplitude-level Fourier symbol of
`S(u) omega`: for a source vorticity mode `(k1, w1)` with Biot-Savart
velocity amplitude `u = k1 x w1 / |k1|^2`, the strain amplitude applied
to a vorticity vector `w2` is `(1/2) (k1 (u . w2) + u (k1 . w2))` (the
two `i` factors combine to a real matrix).  Everything below is exact
rational arithmetic on integer lattice data.

This is a route fence, not a proof of any part of Navier-Stokes
regularity.
-/

set_option autoImplicit false

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeConeDirectionDichotomy

/-- Rational 3-vectors as triples. -/
abbrev Vec3 := ℚ × ℚ × ℚ

def dot (a b : Vec3) : ℚ :=
  a.1 * b.1 + a.2.1 * b.2.1 + a.2.2 * b.2.2

def cross (a b : Vec3) : Vec3 :=
  (a.2.1 * b.2.2 - a.2.2 * b.2.1,
   a.2.2 * b.1 - a.1 * b.2.2,
   a.1 * b.2.1 - a.2.1 * b.1)

def smul (c : ℚ) (a : Vec3) : Vec3 :=
  (c * a.1, c * a.2.1, c * a.2.2)

def add (a b : Vec3) : Vec3 :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2 + b.2.2)

def normSq (a : Vec3) : ℚ :=
  dot a a

/-- Biot-Savart velocity amplitude of the vorticity mode `(k, w)`
(real representative; the `i` is carried by the strain symbol). -/
def biotSavartAmp (k w : Vec3) : Vec3 :=
  smul (1 / normSq k) (cross k w)

/-- Amplitude-level stretching vector: the strain of the source mode
`(k1, w1)` applied to the vorticity vector `w2`. -/
def stretchAmp (k1 w1 w2 : Vec3) : Vec3 :=
  let u := biotSavartAmp k1 w1
  smul (1 / 2) (add (smul (dot u w2) k1) (smul (dot k1 w2) u))

/-- Squared normalized stretching coefficient. -/
def sigmaSq (k1 w1 w2 : Vec3) : ℚ :=
  normSq (stretchAmp k1 w1 w2) / (normSq w1 * normSq w2)

/-- The axial source mode: wavevector along the pancake normal. -/
def axialK (m : ℚ) : Vec3 := (0, 0, m)

def ex : Vec3 := (1, 0, 0)
def ey : Vec3 := (0, 1, 0)

/-- The receiving cone mode at scale `M`, one lattice step off axis. -/
def coneK (M : ℚ) : Vec3 := (1, 0, M)

/-- The receiver's in-plane-aligned divergence-free polarization. -/
def alignedW (M : ℚ) : Vec3 := (-M, 0, 1)

/-- Both polarizations are legitimate vorticity directions:
divergence-free (perpendicular to the receiving wavevector). -/
theorem ey_perp_coneK (M : ℚ) : dot (coneK M) ey = 0 := by
  simp [dot, coneK, ey]

theorem alignedW_perp_coneK (M : ℚ) : dot (coneK M) (alignedW M) = 0 := by
  simp [dot, coneK, alignedW]

/-- The receiver lies in every pancake cone eventually: the squared sine
of its angle to the axis is `1 / (1 + M^2)`. -/
theorem coneK_sinSq (M : ℚ) :
    (coneK M).1 ^ 2 + (coneK M).2.1 ^ 2 = 1 ∧
      normSq (coneK M) = 1 + M ^ 2 := by
  constructor
  · simp [coneK]
  · simp [normSq, dot, coneK]
    ring

/-- **Saturation.**  Wavevector-cone confinement alone does not deplete
pairwise stretching: the axial pancake source at any frequency `m ≠ 0`
stretches the perpendicular in-plane vorticity direction of the cone
receiver at the exact generic maximum, `sigma^2 = 1/4`. -/
theorem sigmaSq_saturates (m : ℚ) (hm : m ≠ 0) :
    sigmaSq (axialK m) ex ey = 1 / 4 := by
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  simp only [sigmaSq, stretchAmp, biotSavartAmp, axialK, ex, ey,
    cross, dot, smul, add, normSq]
  field_simp
  ring

/-- **Aligned depletion.**  The same source acting on the same
receiver's aligned polarization is depleted by a full inverse-square
power of the receiver frequency: `sigma^2 = 1 / (4 (1 + M^2))`. -/
theorem sigmaSq_aligned_depleted (m M : ℚ) (hm : m ≠ 0) :
    sigmaSq (axialK m) ex (alignedW M) = 1 / (4 * (1 + M ^ 2)) := by
  have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
  have hM : (1 : ℚ) + M ^ 2 ≠ 0 := by positivity
  simp only [sigmaSq, stretchAmp, biotSavartAmp, axialK, ex, alignedW,
    cross, dot, smul, add, normSq]
  field_simp
  ring

/-- The dichotomy in one statement: on a single wavevector pair inside
every pancake cone, the stretching coefficient is the generic maximum
for the perpendicular vorticity direction and vanishes like the inverse
receiver frequency for the aligned one.  The pancake budget's
self-depletion mechanism therefore lives in vorticity-direction
coherence, not wavevector confinement. -/
theorem pancake_direction_dichotomy (m M : ℚ) (hm : m ≠ 0) :
    sigmaSq (axialK m) ex ey = 1 / 4 ∧
      sigmaSq (axialK m) ex (alignedW M) = 1 / (4 * (1 + M ^ 2)) :=
  ⟨sigmaSq_saturates m hm, sigmaSq_aligned_depleted m M hm⟩

end PancakeConeDirectionDichotomy
end NavierStokes
end FluidDynamics
end Mettapedia
