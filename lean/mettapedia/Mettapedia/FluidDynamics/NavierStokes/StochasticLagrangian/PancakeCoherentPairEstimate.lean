import Mettapedia.FluidDynamics.NavierStokes.StochasticLagrangian.PancakeConeDirectionDichotomy

/-
# The coherent pair estimate: direction-coherent cone modes deplete

The kinematic dichotomy showed wavevector-cone confinement alone gives
no pairwise depletion, and the coherent-aggregate lab measured that
direction-coherent polarizations restore a per-pair aperture gain
governed by the *wider* cone of the pair.  This module proves that law
exactly: for two modes inside pancake cones of squared apertures
`d1, d2 <= 1/4`, both carrying the direction-coherent polarization
(the fixed in-plane reference `e_x` projected off the wavevector), the
squared normalized stretching coefficient obeys

    sigmaSq  <=  6 * (d1 + d2).

The mechanism is the exact identity `k x (|k|^2 e_x - (k.e_x) k) =
|k|^2 (0, k_z, -k_y)`: the Biot-Savart velocity of a coherently
polarized mode is perpendicular to the reference direction, so the
strain it applies to another coherent polarization is controlled by the
two tilts alone.  Together with `PancakeConeDirectionDichotomy` this
isolates the provable content of the Biot-Savart self-depletion
envelope: depletion is bought by direction coherence, at the rate of
the summed tilts, and by nothing else.

This is an exact kinematic estimate, not a proof of any part of
Navier-Stokes regularity.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes
namespace PancakeCoherentPairEstimate

open PancakeConeDirectionDichotomy

/-- The unnormalized direction-coherent polarization: the reference
`e_x` projected off the wavevector, scaled by `|k|^2` to stay
polynomial. -/
def coherentW (k : Vec3) : Vec3 :=
  add (smul (normSq k) ex) (smul (-(dot k ex)) k)

/-- The coherent polarization is a legitimate vorticity direction. -/
theorem coherentW_perp (k : Vec3) : dot k (coherentW k) = 0 := by
  simp only [coherentW, dot, add, smul, ex, normSq]
  ring

/-- Its squared norm in closed form. -/
theorem normSq_coherentW (k : Vec3) :
    normSq (coherentW k) = normSq k * (normSq k - k.1 ^ 2) := by
  simp only [coherentW, normSq, dot, add, smul, ex]
  ring

/-- The exact Biot-Savart numerator of a coherent mode: perpendicular
to the reference direction. -/
theorem cross_coherentW (k : Vec3) :
    cross k (coherentW k) = smul (normSq k) (0, k.2.2, -k.2.1) := by
  simp only [coherentW, cross, add, smul, normSq, dot, ex]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp <;> ring

/-- The polynomial core of the estimate, stated on raw components.
`N1, N2` are the squared wavevector norms; the numerator is the exact
squared norm of the stretching vector of one coherent mode on the
other, times `4`. -/
theorem core_inequality (a1 b1 c1 a2 b2 c2 d1 d2 : ℚ)
    (hn1 : 0 < a1 ^ 2 + b1 ^ 2 + c1 ^ 2)
    (hn2 : 0 < a2 ^ 2 + b2 ^ 2 + c2 ^ 2)
    (hcone1 : a1 ^ 2 + b1 ^ 2 ≤ d1 * (a1 ^ 2 + b1 ^ 2 + c1 ^ 2))
    (hcone2 : a2 ^ 2 + b2 ^ 2 ≤ d2 * (a2 ^ 2 + b2 ^ 2 + c2 ^ 2))
    (hd1 : d1 ≤ 1 / 4) (hd2 : d2 ≤ 1 / 4) :
    let N1 := a1 ^ 2 + b1 ^ 2 + c1 ^ 2
    let N2 := a2 ^ 2 + b2 ^ 2 + c2 ^ 2
    let P := -a2 * (c1 * b2 - b1 * c2)
    let Q := N2 * a1 - a2 * (a1 * a2 + b1 * b2 + c1 * c2)
    P ^ 2 * N1 + Q ^ 2 * (b1 ^ 2 + c1 ^ 2) ≤
      24 * (d1 + d2) * ((3 / 4) * (N1 * N1) * ((3 / 4) * (N2 * N2))) := by
  intro N1 N2 P Q
  have hd1nn : 0 ≤ d1 := by nlinarith [sq_nonneg a1, sq_nonneg b1]
  have hd2nn : 0 ≤ d2 := by nlinarith [sq_nonneg a2, sq_nonneg b2]
  have ha1sq : a1 ^ 2 ≤ d1 * N1 := by nlinarith [sq_nonneg b1]
  have hb1sq : b1 ^ 2 ≤ d1 * N1 := by nlinarith [sq_nonneg a1]
  have ha2sq : a2 ^ 2 ≤ d2 * N2 := by nlinarith [sq_nonneg b2]
  have hb2sq : b2 ^ 2 ≤ d2 * N2 := by nlinarith [sq_nonneg a2]
  have hc1sq : c1 ^ 2 ≤ N1 := by nlinarith [sq_nonneg a1, sq_nonneg b1]
  have hc2sq : c2 ^ 2 ≤ N2 := by nlinarith [sq_nonneg a2, sq_nonneg b2]
  have hddnn : 0 ≤ d1 + d2 := by linarith
  -- P^2 ≤ 2 d2 (d1+d2) N1 N2^2
  have hPsq : P ^ 2 ≤ 2 * d2 * (d1 + d2) * N1 * (N2 * N2) := by
    have hinner : (c1 * b2 - b1 * c2) ^ 2 ≤
        2 * (c1 ^ 2 * b2 ^ 2 + b1 ^ 2 * c2 ^ 2) := by
      nlinarith [sq_nonneg (c1 * b2 + b1 * c2)]
    have hcb : c1 ^ 2 * b2 ^ 2 ≤ N1 * (d2 * N2) :=
      mul_le_mul hc1sq hb2sq (sq_nonneg b2) (le_of_lt hn1)
    have hbc : b1 ^ 2 * c2 ^ 2 ≤ d1 * N1 * N2 := by
      have := mul_le_mul hb1sq hc2sq (sq_nonneg c2)
        (by nlinarith : (0:ℚ) ≤ d1 * N1)
      linarith [this]
    have hsum : (c1 * b2 - b1 * c2) ^ 2 ≤ 2 * (d1 + d2) * (N1 * N2) := by
      nlinarith [hinner, hcb, hbc]
    have hPform : P ^ 2 = a2 ^ 2 * (c1 * b2 - b1 * c2) ^ 2 := by
      simp only [P]
      ring
    rw [hPform]
    calc a2 ^ 2 * (c1 * b2 - b1 * c2) ^ 2
        ≤ (d2 * N2) * (2 * (d1 + d2) * (N1 * N2)) := by
          exact mul_le_mul ha2sq hsum (sq_nonneg _)
            (by nlinarith : (0:ℚ) ≤ d2 * N2)
      _ = 2 * d2 * (d1 + d2) * N1 * (N2 * N2) := by ring
  -- Q^2 ≤ 2 (d1+d2) N1 N2^2
  have hQsq : Q ^ 2 ≤ 2 * (d1 + d2) * N1 * (N2 * N2) := by
    have hcs : (a1 * a2 + b1 * b2 + c1 * c2) ^ 2 ≤ N1 * N2 := by
      nlinarith [sq_nonneg (a1 * b2 - b1 * a2), sq_nonneg (a1 * c2 - c1 * a2),
        sq_nonneg (b1 * c2 - c1 * b2)]
    have hsplit : Q ^ 2 ≤ 2 * ((N2 * a1) ^ 2 +
        (a2 * (a1 * a2 + b1 * b2 + c1 * c2)) ^ 2) := by
      have := sq_nonneg (N2 * a1 + a2 * (a1 * a2 + b1 * b2 + c1 * c2))
      simp only [Q]
      nlinarith [this]
    have ht1 : (N2 * a1) ^ 2 ≤ d1 * N1 * (N2 * N2) := by
      have : (N2 * a1) ^ 2 = a1 ^ 2 * (N2 * N2) := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_right ha1sq
        (by positivity : (0:ℚ) ≤ N2 * N2)
    have ht2 : (a2 * (a1 * a2 + b1 * b2 + c1 * c2)) ^ 2 ≤
        d2 * N2 * (N1 * N2) := by
      have hexp : (a2 * (a1 * a2 + b1 * b2 + c1 * c2)) ^ 2 =
          a2 ^ 2 * (a1 * a2 + b1 * b2 + c1 * c2) ^ 2 := by ring
      rw [hexp]
      exact mul_le_mul ha2sq hcs (sq_nonneg _)
        (by nlinarith : (0:ℚ) ≤ d2 * N2)
    nlinarith [hsplit, ht1, ht2, hd2, mul_pos hn1 hn2,
      mul_nonneg hd2nn (le_of_lt (mul_pos hn1 (mul_pos hn2 hn2)))]
  -- b1^2 + c1^2 ≤ (1 + d1) N1 ≤ (5/4) N1
  have hbc1 : b1 ^ 2 + c1 ^ 2 ≤ (5 / 4) * N1 := by
    nlinarith [sq_nonneg a1]
  -- assemble
  have hterm1 : P ^ 2 * N1 ≤ 2 * d2 * (d1 + d2) * (N1 * N1) * (N2 * N2) := by
    have := mul_le_mul_of_nonneg_right hPsq (le_of_lt hn1)
    nlinarith [this]
  have hterm2 : Q ^ 2 * (b1 ^ 2 + c1 ^ 2) ≤
      2 * (d1 + d2) * (5 / 4) * (N1 * N1) * (N2 * N2) := by
    have hbcnn : (0 : ℚ) ≤ b1 ^ 2 + c1 ^ 2 := by positivity
    have := mul_le_mul hQsq hbc1 hbcnn
      (by nlinarith [mul_pos hn1 (mul_pos hn2 hn2)] :
        (0:ℚ) ≤ 2 * (d1 + d2) * N1 * (N2 * N2))
    nlinarith [this]
  nlinarith [hterm1, hterm2, hd2,
    mul_nonneg hddnn (le_of_lt (mul_pos (mul_pos hn1 hn1) (mul_pos hn2 hn2))),
    mul_nonneg (mul_nonneg hd2nn hddnn)
      (le_of_lt (mul_pos (mul_pos hn1 hn1) (mul_pos hn2 hn2)))]

/-- **The coherent pair estimate.**  For wavevectors inside pancake
cones of squared apertures `d1, d2 ≤ 1/4`, the squared normalized
stretching coefficient of one direction-coherent mode on the other is
at most `6 (d1 + d2)`. -/
theorem sigmaSq_coherent_le
    (k1 k2 : Vec3) (d1 d2 : ℚ)
    (hk1 : normSq k1 ≠ 0) (hk2 : normSq k2 ≠ 0)
    (hcone1 : k1.1 ^ 2 + k1.2.1 ^ 2 ≤ d1 * normSq k1)
    (hcone2 : k2.1 ^ 2 + k2.2.1 ^ 2 ≤ d2 * normSq k2)
    (hd1 : d1 ≤ 1 / 4) (hd2 : d2 ≤ 1 / 4) :
    sigmaSq k1 (coherentW k1) (coherentW k2) ≤ 6 * (d1 + d2) := by
  obtain ⟨a1, b1, c1⟩ := k1
  obtain ⟨a2, b2, c2⟩ := k2
  simp only [normSq, dot] at hk1 hk2 hcone1 hcone2
  have hn1 : 0 < a1 ^ 2 + b1 ^ 2 + c1 ^ 2 := by
    by_contra h
    push_neg at h
    apply hk1
    nlinarith [sq_nonneg a1, sq_nonneg b1, sq_nonneg c1]
  have hn2 : 0 < a2 ^ 2 + b2 ^ 2 + c2 ^ 2 := by
    by_contra h
    push_neg at h
    apply hk2
    nlinarith [sq_nonneg a2, sq_nonneg b2, sq_nonneg c2]
  have hcone1' : a1 ^ 2 + b1 ^ 2 ≤ d1 * (a1 ^ 2 + b1 ^ 2 + c1 ^ 2) := by
    nlinarith [hcone1]
  have hcone2' : a2 ^ 2 + b2 ^ 2 ≤ d2 * (a2 ^ 2 + b2 ^ 2 + c2 ^ 2) := by
    nlinarith [hcone2]
  have hcore := core_inequality a1 b1 c1 a2 b2 c2 d1 d2 hn1 hn2
    hcone1' hcone2' hd1 hd2
  simp only at hcore
  have hddnn : 0 ≤ d1 + d2 := by
    have hd1nn : 0 ≤ d1 := by nlinarith [sq_nonneg a1, sq_nonneg b1]
    have hd2nn : 0 ≤ d2 := by nlinarith [sq_nonneg a2, sq_nonneg b2]
    linarith
  -- exact Biot-Savart amplitude of the coherent source
  have hNval : normSq (a1, b1, c1) = a1 ^ 2 + b1 ^ 2 + c1 ^ 2 := by
    simp only [normSq, dot]
    ring
  have hbiot : biotSavartAmp (a1, b1, c1) (coherentW (a1, b1, c1)) =
      ((0 : ℚ), c1, -b1) := by
    simp only [biotSavartAmp]
    rw [cross_coherentW, hNval]
    simp only [smul]
    have hne : a1 ^ 2 + b1 ^ 2 + c1 ^ 2 ≠ 0 := ne_of_gt hn1
    refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> dsimp <;> field_simp
  -- the two scalar couplings
  have hPval : dot ((0 : ℚ), c1, -b1) (coherentW (a2, b2, c2)) =
      -a2 * (c1 * b2 - b1 * c2) := by
    simp only [coherentW, dot, add, smul, ex, normSq]
    ring
  have hQval : dot ((a1 : ℚ), b1, c1) (coherentW (a2, b2, c2)) =
      (a2 ^ 2 + b2 ^ 2 + c2 ^ 2) * a1 -
        a2 * (a1 * a2 + b1 * b2 + c1 * c2) := by
    simp only [coherentW, dot, add, smul, ex, normSq]
    ring
  -- squared norm of the stretching vector, cross term cancelled
  have hstretch : normSq (stretchAmp (a1, b1, c1) (coherentW (a1, b1, c1))
      (coherentW (a2, b2, c2))) =
      (1 / 4) * ((-a2 * (c1 * b2 - b1 * c2)) ^ 2 *
          (a1 ^ 2 + b1 ^ 2 + c1 ^ 2) +
        ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) * a1 -
          a2 * (a1 * a2 + b1 * b2 + c1 * c2)) ^ 2 *
          (b1 ^ 2 + c1 ^ 2)) := by
    simp only [stretchAmp]
    rw [hbiot, hPval, hQval]
    simp only [normSq, dot, smul, add]
    ring
  -- denominators
  have hD1 : normSq (coherentW (a1, b1, c1)) =
      (a1 ^ 2 + b1 ^ 2 + c1 ^ 2) * ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) - a1 ^ 2) := by
    rw [normSq_coherentW, hNval]
  have hD2 : normSq (coherentW (a2, b2, c2)) =
      (a2 ^ 2 + b2 ^ 2 + c2 ^ 2) * ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) - a2 ^ 2) := by
    rw [normSq_coherentW]
    simp only [normSq, dot]
    ring_nf
  have hden1 : (3 / 4) * ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) *
      (a1 ^ 2 + b1 ^ 2 + c1 ^ 2)) ≤
      (a1 ^ 2 + b1 ^ 2 + c1 ^ 2) * ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) - a1 ^ 2) := by
    have ha1 : a1 ^ 2 ≤ (1 / 4) * (a1 ^ 2 + b1 ^ 2 + c1 ^ 2) := by
      nlinarith [sq_nonneg b1, hcone1', hd1, hn1]
    nlinarith [hn1]
  have hden2 : (3 / 4) * ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) *
      (a2 ^ 2 + b2 ^ 2 + c2 ^ 2)) ≤
      (a2 ^ 2 + b2 ^ 2 + c2 ^ 2) * ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) - a2 ^ 2) := by
    have ha2 : a2 ^ 2 ≤ (1 / 4) * (a2 ^ 2 + b2 ^ 2 + c2 ^ 2) := by
      nlinarith [sq_nonneg b2, hcone2', hd2, hn2]
    nlinarith [hn2]
  have hD1pos : 0 < (a1 ^ 2 + b1 ^ 2 + c1 ^ 2) *
      ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) - a1 ^ 2) := by
    nlinarith [hden1, mul_pos hn1 hn1]
  have hD2pos : 0 < (a2 ^ 2 + b2 ^ 2 + c2 ^ 2) *
      ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) - a2 ^ 2) := by
    nlinarith [hden2, mul_pos hn2 hn2]
  -- reduce the division and close with the core
  rw [sigmaSq, hstretch, hD1, hD2, div_le_iff₀ (by positivity)]
  calc (1 / 4) * ((-a2 * (c1 * b2 - b1 * c2)) ^ 2 *
        (a1 ^ 2 + b1 ^ 2 + c1 ^ 2) +
      ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) * a1 -
        a2 * (a1 * a2 + b1 * b2 + c1 * c2)) ^ 2 * (b1 ^ 2 + c1 ^ 2))
      ≤ (1 / 4) * (24 * (d1 + d2) *
          ((3 / 4) * ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) * (a1 ^ 2 + b1 ^ 2 + c1 ^ 2)) *
            ((3 / 4) * ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) * (a2 ^ 2 + b2 ^ 2 + c2 ^ 2))))) := by
        linarith [hcore]
    _ = 6 * (d1 + d2) *
          ((3 / 4) * ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) * (a1 ^ 2 + b1 ^ 2 + c1 ^ 2))) *
          ((3 / 4) * ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) * (a2 ^ 2 + b2 ^ 2 + c2 ^ 2))) := by
        ring
    _ ≤ 6 * (d1 + d2) *
          ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) * ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) - a1 ^ 2)) *
          ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) * ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) - a2 ^ 2)) := by
        have h6 : (0 : ℚ) ≤ 6 * (d1 + d2) := by linarith
        have hstep1 : 6 * (d1 + d2) *
            ((3 / 4) * ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) * (a1 ^ 2 + b1 ^ 2 + c1 ^ 2))) ≤
            6 * (d1 + d2) *
            ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) * ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) - a1 ^ 2)) :=
          mul_le_mul_of_nonneg_left hden1 h6
        have hlast : (0 : ℚ) ≤
            (3 / 4) * ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) * (a2 ^ 2 + b2 ^ 2 + c2 ^ 2)) := by
          positivity
        calc 6 * (d1 + d2) *
              ((3 / 4) * ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) * (a1 ^ 2 + b1 ^ 2 + c1 ^ 2))) *
              ((3 / 4) * ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) * (a2 ^ 2 + b2 ^ 2 + c2 ^ 2)))
            ≤ 6 * (d1 + d2) *
              ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) * ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) - a1 ^ 2)) *
              ((3 / 4) * ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) * (a2 ^ 2 + b2 ^ 2 + c2 ^ 2))) :=
              mul_le_mul_of_nonneg_right hstep1 hlast
          _ ≤ 6 * (d1 + d2) *
              ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) * ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) - a1 ^ 2)) *
              ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) * ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) - a2 ^ 2)) := by
              apply mul_le_mul_of_nonneg_left hden2
              nlinarith [h6, hD1pos]
    _ = 6 * (d1 + d2) *
          ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) * ((a1 ^ 2 + b1 ^ 2 + c1 ^ 2) - a1 ^ 2) *
            ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) * ((a2 ^ 2 + b2 ^ 2 + c2 ^ 2) - a2 ^ 2))) := by
        ring

end PancakeCoherentPairEstimate
end NavierStokes
end FluidDynamics
end Mettapedia
