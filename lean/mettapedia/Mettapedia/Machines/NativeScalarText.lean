import Std

/-!
# Integer foundations of retained binary64 text conversion

The compatibility program performs its decimal arithmetic in MeTTa. Native
operations expose the original binary64 parts and exact integer divmod.
These results establish the required power range, the normalization step and
the two rounding laws. The finite power certificate is kernel-checked and its
values are replayed through the actual MeTTa helper.

Binary64 decomposition, decimal parsing/round-trip equality, native arithmetic
and execution of the complete formatter remain separate refinement obligations.
These theorems are not a verification of SQLite or the C implementation.
-/

namespace Mettapedia.Machines.NativeScalarText

def requiredPower (exponent : Int) : Int := 17 - ((exponent + 63) * 78913) / 262144

theorem required_power_bounds (exponent : Int)
    (lower : -1137 ≤ exponent) (upper : exponent ≤ 960) :
    -290 ≤ requiredPower exponent ∧ requiredPower exponent ≤ 341 := by
  unfold requiredPower
  omega

def scalingShift (exponent : Int) : Int :=
  -(exponent + (requiredPower exponent * 108853) / 32768 + 2)

theorem scaling_shift_bounds (exponent : Int)
    (lower : -1137 ≤ exponent) (upper : exponent ≤ 960) :
    2 ≤ scalingShift exponent ∧ scalingShift exponent ≤ 5 := by
  unfold scalingShift requiredPower
  omega

theorem normalization_preserves_scaled_value (mantissa exponent : Nat) :
    (mantissa * 2) * 2 ^ exponent = mantissa * 2 ^ (exponent + 1) := by
  simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]

def ceilHalf (value : Nat) : Nat := (value + 1) / 2
def sourceHalf (value : Nat) : Nat := (value + 2 * (value % 2)) / 2

theorem conversion_half_step (value : Nat) : sourceHalf value = ceilHalf value := by
  unfold sourceHalf ceilHalf
  by_cases even : value % 2 = 0
  · simp only [even, Nat.mul_zero, Nat.add_zero]
    omega
  · have odd : value % 2 = 1 := by omega
    simp only [odd, Nat.mul_one]
    omega

def decimalRound (leading digit : Nat) : Nat := leading + if 5 ≤ digit then 1 else 0

theorem decimal_lookahead_rounds_half_up (leading digit : Nat) (valid : digit < 10) :
    (10 * leading + digit + 5) / 10 = decimalRound leading digit := by
  unfold decimalRound
  split <;> omega

def powerHigh (power : Int) : Nat :=
  let binary := (power * 108853) / 32768
  let shift := 63 - binary
  if 0 ≤ power then
    if 0 ≤ shift then 10 ^ power.toNat * 2 ^ shift.toNat
    else 10 ^ power.toNat / 2 ^ (-shift).toNat
  else
    if 0 ≤ shift then 2 ^ shift.toNat / 10 ^ (-power).toNat
    else 1 / (10 ^ (-power).toNat * 2 ^ (-shift).toNat)

def powerRangeCheck : Bool :=
  (List.range 696).all fun index =>
    let value := powerHigh (Int.ofNat index - 348)
    decide (9223372036854775808 ≤ value ∧ value < 18446744073709551616)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 2000000 in
set_option exponentiation.threshold 2048 in
theorem required_power_values_are_normalized : powerRangeCheck = true := by decide

theorem power_high_normalized (power : Int) (lower : -348 ≤ power) (upper : power < 348) :
    9223372036854775808 ≤ powerHigh power ∧ powerHigh power < 18446744073709551616 := by
  have indexBound : (power + 348).toNat < 696 := by omega
  have castValue : Int.ofNat (power + 348).toNat = power + 348 :=
    Int.toNat_of_nonneg (by omega)
  have indexValue : Int.ofNat (power + 348).toNat - 348 = power := by omega
  have checked := List.all_eq_true.mp required_power_values_are_normalized
    (power + 348).toNat (List.mem_range.mpr indexBound)
  simpa only [indexValue, decide_eq_true_eq] using checked

theorem conversion_power_normalized (exponent : Int)
    (lower : -1137 ≤ exponent) (upper : exponent ≤ 960) :
    9223372036854775808 ≤ powerHigh (requiredPower exponent) ∧
    powerHigh (requiredPower exponent) < 18446744073709551616 := by
  have bounds := required_power_bounds exponent lower upper
  exact power_high_normalized _ (by omega) (by omega)

def powerTrace : IO Unit := do
  for index in List.range 696 do
    let power := Int.ofNat index - 348
    IO.println s!"NUMERIC_POWER {power} {powerHigh power}"

end Mettapedia.Machines.NativeScalarText

#eval Mettapedia.Machines.NativeScalarText.powerTrace
