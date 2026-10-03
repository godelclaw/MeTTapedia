import MettapediaFourColor.WheelRepairCertificate

namespace FourColor.WheelRepairCertificate

set_option maxRecDepth 65536

theorem sampleInput0 : ∀ k : Fin 16, inputCheck (0 + k.val) = true := by decide +kernel

theorem sampleInput265712 : ∀ k : Fin 16, inputCheck (265712 + k.val) = true := by decide +kernel

theorem sampleInput531425 : ∀ k : Fin 16, inputCheck (531425 + k.val) = true := by decide +kernel

end FourColor.WheelRepairCertificate
