import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankModularCertificateP1000000007Group0
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankModularCertificateP1000000007Group1
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankModularCertificateP1000000007Group2
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankModularCertificateP1000000007Group3
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankModularCertificateP1000000009Group0
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankModularCertificateP1000000009Group1
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankModularCertificateP1000000009Group2
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceRankModularCertificateP1000000009Group3
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16TraceFiniteQuotient

/-!
# Uniform two-prime replay for the eight-field trace certificate

Every selected integer relation row is reduced against independently computed
sparse echelon data modulo each of the two certified primes.  The exact
rational rank theorem remains the semantic rank result; these replays are
independent arithmetic audits of the sparse elimination data.
-/

set_option autoImplicit false

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceRankModularCertificate

open HypercubicDimension16TraceRankCertificateData

theorem modularReplayP1000000007_of_range {start count offset : Nat}
    (hcheck : modularReplayRangeCheckP1000000007 start count = true)
    (hoffset : offset < count) :
    modularReplaySelectedRowP1000000007 (start + offset) = true := by
  apply List.all_eq_true.mp hcheck
  exact List.mem_range.mpr hoffset

theorem modularReplayP1000000007_certificate {rowIndex : Nat}
    (hrowIndex : rowIndex < selectedRowCount) :
    modularReplaySelectedRowP1000000007 rowIndex = true := by
  norm_num [selectedRowCount] at hrowIndex
  let chunk := rowIndex / 256
  have hchunk : chunk ≤ 45 := by
    dsimp [chunk]
    omega
  have hdecomposition :
      256 * chunk + rowIndex % 256 = rowIndex := by
    simpa [chunk] using Nat.div_add_mod rowIndex 256
  interval_cases chunk
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_000 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_001 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_002 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_003 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_004 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_005 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_006 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_007 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_008 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_009 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_010 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_011 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_012 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_013 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_014 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_015 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_016 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_017 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_018 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_019 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_020 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_021 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_022 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_023 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_024 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_025 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_026 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_027 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_028 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_029 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_030 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_031 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_032 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_033 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_034 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_035 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_036 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_037 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_038 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_039 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_040 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_041 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_042 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_043 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_044 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000007_of_range
      modularReplayP1000000007Range_045 (by omega)

theorem modularReplayP1000000009_of_range {start count offset : Nat}
    (hcheck : modularReplayRangeCheckP1000000009 start count = true)
    (hoffset : offset < count) :
    modularReplaySelectedRowP1000000009 (start + offset) = true := by
  apply List.all_eq_true.mp hcheck
  exact List.mem_range.mpr hoffset

theorem modularReplayP1000000009_certificate {rowIndex : Nat}
    (hrowIndex : rowIndex < selectedRowCount) :
    modularReplaySelectedRowP1000000009 rowIndex = true := by
  norm_num [selectedRowCount] at hrowIndex
  let chunk := rowIndex / 256
  have hchunk : chunk ≤ 45 := by
    dsimp [chunk]
    omega
  have hdecomposition :
      256 * chunk + rowIndex % 256 = rowIndex := by
    simpa [chunk] using Nat.div_add_mod rowIndex 256
  interval_cases chunk
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_000 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_001 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_002 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_003 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_004 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_005 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_006 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_007 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_008 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_009 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_010 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_011 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_012 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_013 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_014 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_015 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_016 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_017 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_018 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_019 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_020 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_021 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_022 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_023 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_024 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_025 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_026 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_027 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_028 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_029 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_030 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_031 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_032 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_033 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_034 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_035 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_036 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_037 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_038 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_039 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_040 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_041 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_042 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_043 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_044 (by omega)
  · rw [← hdecomposition]
    exact modularReplayP1000000009_of_range
      modularReplayP1000000009Range_045 (by omega)

theorem p1000000007_prime : Nat.Prime 1000000007 := by
  norm_num

theorem p1000000009_prime : Nat.Prime 1000000009 := by
  norm_num

theorem auditPrimes_distinct :
    (1000000007 : Nat) ≠ 1000000009 := by
  norm_num

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem modularP1000000007_shape :
    HypercubicDimension16TraceRankModularDataP1000000007.modularBasisSizeCheck = true ∧
    HypercubicDimension16TraceRankModularDataP1000000007.modularReplayStepsSizeCheck = true := by
  decide

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem modularP1000000009_shape :
    HypercubicDimension16TraceRankModularDataP1000000009.modularBasisSizeCheck = true ∧
    HypercubicDimension16TraceRankModularDataP1000000009.modularReplayStepsSizeCheck = true := by
  decide

end HypercubicDimension16TraceRankModularCertificate
end YangMills
end QuantumTheory
end Mettapedia
