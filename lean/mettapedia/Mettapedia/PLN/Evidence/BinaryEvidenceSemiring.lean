import Mettapedia.PLN.Evidence.BinaryEvidence

/-!
# The existing binary tensor operations form a commutative semiring

This optional algebra interface uses the existing count addition, tensor
product, zero, and tensor unit. It supplies their distributive laws for
standard semiring homomorphisms. It does not identify tensor fusion with
paired-sample conjunction or license revisions of shared observations.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Evidence

noncomputable instance binaryTensorCommSemiring : CommSemiring BinaryEvidence where
  __ := (inferInstance : AddCommMonoid BinaryEvidence)
  __ := (inferInstance : CommMonoid BinaryEvidence)
  left_distrib first second third := by
    apply BinaryEvidence.ext' <;>
      simp [BinaryEvidence.tensor_def, BinaryEvidence.hplus_def, mul_add]
  right_distrib first second third := by
    apply BinaryEvidence.ext' <;>
      simp [BinaryEvidence.tensor_def, BinaryEvidence.hplus_def, add_mul]
  zero_mul value := by
    apply BinaryEvidence.ext' <;> simp [BinaryEvidence.tensor_def]
  mul_zero value := by
    apply BinaryEvidence.ext' <;> simp [BinaryEvidence.tensor_def]

end Mettapedia.PLN.Evidence
