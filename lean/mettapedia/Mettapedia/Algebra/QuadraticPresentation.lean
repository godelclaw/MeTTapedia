import Algebra.QuadraticPresentation

/-! The quadratic algebra construction and its preservation laws live in the
standalone inference foundation. This module exposes that canonical API. -/
namespace Mettapedia.Algebra.QuadraticPresentation
export _root_.Algebra.QuadraticPresentation
  (Controls.field_not_quadratic Controls.productUnitBasis Controls.product_basis_relation Controls.product_has_quadratic_presentation
   Controls.product_idempotent_nonscalar affineEquiv basisOfNonscalar basisOfNonscalar.eq_1
   basisOfNonscalar_one basisOfNonscalar_zero basis_coordinates changeGenerator
   changeGenerator_im changeGenerator_observations changeGenerator_re dimension_of_equiv
   exists_basis_one exists_equiv_quadratic exists_equiv_quadratic_iff exists_nonscalar
   mul_comm_of_finrank_two ofBasis ofBasis_apply ofBasis_symm_apply
   realize realize.congr_simp realize_apply realize_injective
   realize_repr_one realize_repr_zero realize_surjective scalar_generator_not_independent
   shiftedConstant shiftedLinear shifted_discriminant squareConstant
   squareConstant.eq_1 squareLinear squareLinear.eq_1 square_relation)
end Mettapedia.Algebra.QuadraticPresentation
