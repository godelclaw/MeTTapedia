import MettapediaFourColor.WheelRepairCertificate

/-! # Finite block indices for complete wheel repair checks -/
namespace FourColor.WheelRepairCertificate

def checkAt (n : ℕ) : Bool :=
  check ⟨n % WheelRepairData.count, Nat.mod_lt _ (by decide)⟩
def inputAt (n : ℕ) : Bool := inputCheck (n % (3 ^ 12))

end FourColor.WheelRepairCertificate
