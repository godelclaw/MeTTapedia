import MettapediaFourColor.ExactFanResidual
import MettapediaFourColor.CyclicChargeExample

/-! The exact identity specializes to two retained finite receivers.
Their remaining matcher counts are independently computed by the program
audit; the Lean conclusions retain those counts explicitly. -/

namespace FourColor.ExactChargeExample

open ChainBoundaryExample CyclicChargeExample CyclicCharge ExactCyclicCharge

theorem eight_charge : NearLinearCharge.finalCharge rotation 69 =
    2 + extraCount rotation 69 := by
  have h := exact_charge rotation triangular 69 (by rw [eight_degree]; decide) eight_low
  rw [eight_degree, eight_counts.1, eight_counts.2] at h
  norm_num at h
  exact h

theorem seven_charge : NearLinearCharge.finalCharge rotation 150 =
    8 + extraCount rotation 150 := by
  have h := exact_charge rotation triangular 150 (by rw [seven_degree]) seven_low
  rw [seven_degree, seven_counts.1, seven_counts.2] at h
  norm_num at h
  exact h

end FourColor.ExactChargeExample
