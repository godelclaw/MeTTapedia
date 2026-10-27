import Algebra.SplitComplex

/-! The quadratic algebra construction and its preservation laws live in the
standalone inference foundation. This module exposes that canonical API. -/
namespace Mettapedia.Algebra
export _root_.Algebra
  (SplitComplex SplitComplex.conj SplitComplex.conj.eq_1 SplitComplex.conj_eq_star
   SplitComplex.equivRealProd SplitComplex.equivRealProd.eq_1 SplitComplex.has_zero_divisors SplitComplex.idempotentNeg
   SplitComplex.idempotentNeg.eq_1 SplitComplex.idempotentNeg_sq SplitComplex.idempotentPos SplitComplex.idempotentPos.eq_1
   SplitComplex.idempotentPos_sq SplitComplex.idempotent_coordinates SplitComplex.idempotent_orthogonal SplitComplex.idempotent_sum
   SplitComplex.instCoeReal SplitComplex.isUnit_iff_norm_ne_zero SplitComplex.j SplitComplex.j.eq_1
   SplitComplex.j_ne_neg_one SplitComplex.j_ne_one SplitComplex.j_sq SplitComplex.mul_conj
   SplitComplex.norm SplitComplex.norm.eq_1 SplitComplex.norm_eq_quadratic_norm SplitComplex.norm_j_negative
   SplitComplex.norm_mul SplitComplex.ofReal SplitComplex.ofRealProd SplitComplex.toRealProd
   SplitComplex.toRealProd.eq_1 SplitComplex.zero_divisor_example)
end Mettapedia.Algebra
