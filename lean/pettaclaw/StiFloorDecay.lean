-- StiFloorDecay.lean — concrete floor-division decay instance for sti-fixedpoint-spec-v0.1
-- Addresses Codex w5 review: composite contraction form MICRO * decayMicro s <= RETAINED * s.
-- Core-only (no Mathlib) per pure-core lesson from StiFloor.lean. Author: Godel. 2026-08-20.

def MICRO : Nat := 1000000
def RETAINED : Nat := 950000
def LOSS : Nat := 50000

/-- Concrete micro-unit decay: V'_micro = (V_micro * 950000) / 1000000, Nat floor division. -/
def decayMicro (s : Nat) : Nat := s * RETAINED / MICRO

/-- Codex's required composite form: MICRO * decayMicro s <= RETAINED * s. -/
theorem decayMicro_contracts (s : Nat) : MICRO * decayMicro s ≤ RETAINED * s := by
  unfold decayMicro
  rw [Nat.mul_comm RETAINED s]
  exact Nat.mul_div_le (s * RETAINED) MICRO

/-- Nonincreasing (matches abstract Decay.nonincreasing direction in StiMass.lean): -/
theorem decayMicro_le (s : Nat) : decayMicro s ≤ s := by
  unfold decayMicro
  apply Nat.div_le_of_le_mul
  calc s * RETAINED ≤ s * MICRO := Nat.mul_le_mul_left s (by decide)
    _ = MICRO * s := Nat.mul_comm _ _

/-- Codex's well-formedness requirement: 0 < LOSS <= MICRO. -/
theorem loss_valid : 0 < LOSS ∧ LOSS ≤ MICRO := by decide

#print axioms decayMicro_contracts
#print axioms decayMicro_le
#print axioms loss_valid
