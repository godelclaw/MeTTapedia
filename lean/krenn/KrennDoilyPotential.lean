import Mathlib

/-!
The finite K6 doily potential criterion.

A `lineSum` is the sum of the three perfect-matching products through
an edge.  A vertex potential assigns `s u + s v` to edge `{u,v}`.
Double-counting a matching's three edges gives the identity below.
It turns P-kills supported on a nonzero-mean potential into a direct
contradiction with monochromatic normalization.
-/

namespace Krenn.DoilyPotential

open BigOperators

/-- The fifteen edge coefficients induced by six vertex potentials. -/
def edgePotential {R : Type*} [AddCommMonoid R]
    (s : Fin 6 → R) : Fin 15 → R := ![
  s 0 + s 1,
  s 0 + s 2,
  s 0 + s 3,
  s 0 + s 4,
  s 0 + s 5,
  s 1 + s 2,
  s 1 + s 3,
  s 1 + s 4,
  s 1 + s 5,
  s 2 + s 3,
  s 2 + s 4,
  s 2 + s 5,
  s 3 + s 4,
  s 3 + s 5,
  s 4 + s 5
]

/-- The three matching products through each of the fifteen K6 edges. -/
def lineSum {R : Type*} [AddCommMonoid R]
    (m : Fin 15 → R) : Fin 15 → R := ![
  m 0 + m 1 + m 2,
  m 3 + m 4 + m 5,
  m 6 + m 7 + m 8,
  m 9 + m 10 + m 11,
  m 12 + m 13 + m 14,
  m 6 + m 9 + m 12,
  m 3 + m 10 + m 13,
  m 4 + m 7 + m 14,
  m 5 + m 8 + m 11,
  m 0 + m 11 + m 14,
  m 1 + m 8 + m 13,
  m 2 + m 7 + m 10,
  m 2 + m 5 + m 12,
  m 1 + m 4 + m 9,
  m 0 + m 3 + m 6
]

/-- The product of the three diagonal edge weights in each matching. -/
def matchingProduct {R : Type*} [CommMonoid R]
    (d : Fin 15 → R) : Fin 15 → R := ![
  d 0 * d 9 * d 14,
  d 0 * d 10 * d 13,
  d 0 * d 11 * d 12,
  d 1 * d 6 * d 14,
  d 1 * d 7 * d 13,
  d 1 * d 8 * d 12,
  d 2 * d 5 * d 14,
  d 2 * d 7 * d 11,
  d 2 * d 8 * d 10,
  d 3 * d 5 * d 13,
  d 3 * d 6 * d 11,
  d 3 * d 8 * d 9,
  d 4 * d 5 * d 12,
  d 4 * d 6 * d 10,
  d 4 * d 7 * d 9
]

/-- The K4 diagonal co-sum `P^(e)` at every K6 edge. -/
def coSum {R : Type*} [CommSemiring R]
    (d : Fin 15 → R) : Fin 15 → R := ![
  d 9 * d 14 + d 10 * d 13 + d 11 * d 12,
  d 6 * d 14 + d 7 * d 13 + d 8 * d 12,
  d 5 * d 14 + d 7 * d 11 + d 8 * d 10,
  d 5 * d 13 + d 6 * d 11 + d 8 * d 9,
  d 5 * d 12 + d 6 * d 10 + d 7 * d 9,
  d 2 * d 14 + d 3 * d 13 + d 4 * d 12,
  d 1 * d 14 + d 3 * d 11 + d 4 * d 10,
  d 1 * d 13 + d 2 * d 11 + d 4 * d 9,
  d 1 * d 12 + d 2 * d 10 + d 3 * d 9,
  d 0 * d 14 + d 3 * d 8 + d 4 * d 7,
  d 0 * d 13 + d 2 * d 8 + d 4 * d 6,
  d 0 * d 12 + d 2 * d 7 + d 3 * d 6,
  d 0 * d 11 + d 1 * d 8 + d 4 * d 5,
  d 0 * d 10 + d 1 * d 7 + d 3 * d 5,
  d 0 * d 9 + d 1 * d 6 + d 2 * d 5
]

def totalPotential {R : Type*} [AddCommMonoid R] (s : Fin 6 → R) : R :=
  s 0 + s 1 + s 2 + s 3 + s 4 + s 5

def totalMatching {R : Type*} [AddCommMonoid R] (m : Fin 15 → R) : R :=
  m 0 + m 1 + m 2 + m 3 + m 4 + m 5 + m 6 + m 7 + m 8 + m 9 + m 10 + m 11 + m 12 + m 13 + m 14

def potentialLineTotal {R : Type*} [CommRing R]
    (s : Fin 6 → R) (m : Fin 15 → R) : R :=
  ∑ edge, edgePotential s edge * lineSum m edge

set_option maxRecDepth 100000 in
/-- Exact K6 perfect-matching/edge double count. -/
theorem potential_line_identity {R : Type*} [CommRing R]
    (s : Fin 6 → R) (m : Fin 15 → R) :
    potentialLineTotal s m = totalPotential s * totalMatching m := by
  simp [potentialLineTotal, edgePotential, lineSum, totalPotential,
    totalMatching, Fin.sum_univ_succ]
  ring

/-- The exact diagonal deflation identity `D_e * P^(e) =
sum_{M contains e} m_M`, checked for all fifteen K6 edges. -/
theorem lineSum_factor {R : Type*} [CommRing R]
    (d : Fin 15 → R) (edge : Fin 15) :
    lineSum (matchingProduct d) edge = d edge * coSum d edge := by
  fin_cases edge <;> simp [lineSum, matchingProduct, coSum] <;> ring

/-- If every edge carrying a nonzero vertex potential has a dead P-line,
then the total matching product is annihilated by the potential sum. -/
theorem potential_kills_force_total_zero {R : Type*} [CommRing R]
    (s : Fin 6 → R) (diagonal p m : Fin 15 → R)
    (hfactor : ∀ edge, lineSum m edge = diagonal edge * p edge)
    (hdead : ∀ edge, edgePotential s edge ≠ 0 → p edge = 0) :
    totalPotential s * totalMatching m = 0 := by
  rw [← potential_line_identity]
  unfold potentialLineTotal
  apply Finset.sum_eq_zero
  intro edge _
  rw [hfactor edge]
  by_cases hpotential : edgePotential s edge = 0
  · simp [hpotential]
  · rw [hdead edge hpotential]
    ring

/-- The usable contradiction form: a mean-one potential supported on
P-kills is incompatible with monochromatic normalization. -/
theorem no_normalized_witness_of_potential_kills
    {R : Type*} [CommRing R] [Nontrivial R]
    (s : Fin 6 → R) (diagonal p m : Fin 15 → R)
    (hfactor : ∀ edge, lineSum m edge = diagonal edge * p edge)
    (hdead : ∀ edge, edgePotential s edge ≠ 0 → p edge = 0)
    (hpotential : totalPotential s = 1)
    (hmono : totalMatching m = 1) : False := by
  have hzero := potential_kills_force_total_zero s diagonal p m hfactor hdead
  rw [hpotential, hmono] at hzero
  have honezero : (1 : R) = 0 := by simpa only [one_mul] using hzero
  exact one_ne_zero honezero

/-- Fully diagonal-specialized form of the potential criterion. -/
theorem no_normalized_diagonal_witness_of_potential_kills
    {R : Type*} [CommRing R] [Nontrivial R]
    (s : Fin 6 → R) (d : Fin 15 → R)
    (hdead : ∀ edge, edgePotential s edge ≠ 0 → coSum d edge = 0)
    (hpotential : totalPotential s = 1)
    (hmono : totalMatching (matchingProduct d) = 1) : False := by
  exact no_normalized_witness_of_potential_kills
    s d (coSum d) (matchingProduct d) (lineSum_factor d) hdead
    hpotential hmono

#print axioms Krenn.DoilyPotential.potential_line_identity
#print axioms Krenn.DoilyPotential.lineSum_factor
#print axioms Krenn.DoilyPotential.no_normalized_witness_of_potential_kills
#print axioms Krenn.DoilyPotential.no_normalized_diagonal_witness_of_potential_kills

end Krenn.DoilyPotential
