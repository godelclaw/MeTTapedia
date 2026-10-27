import InformationTheory.Basic

/-! The canonical probability and valuation infrastructure is provided by the
standalone inference foundation. This namespace exposes the same declarations
to MeTTapedia consumers, without defining a second carrier or proof suite. -/

namespace Mettapedia.InformationTheory

/-- The canonical carrier, retaining this namespace for local observation methods. -/
abbrev Prob (α : Type*) [Fintype α] := _root_.InformationTheory.Prob α
abbrev ProbVec (n : ℕ) := Prob (Fin n)

namespace ProbVec
variable {n : ℕ}
theorem nonneg (p : ProbVec n) (i : Fin n) : 0 ≤ p.1 i := _root_.InformationTheory.ProbVec.nonneg p i
theorem sum_eq_one (p : ProbVec n) : ∑ i, p.1 i = 1 := _root_.InformationTheory.ProbVec.sum_eq_one p
theorem le_one (p : ProbVec n) (i : Fin n) : p.1 i ≤ 1 := _root_.InformationTheory.ProbVec.le_one p i
theorem mem_Icc (p : ProbVec n) (i : Fin n) : p.1 i ∈ Set.Icc 0 1 := _root_.InformationTheory.ProbVec.mem_Icc p i
end ProbVec

export _root_.InformationTheory
  (binaryDist binaryDist.eq_1 binaryUniform binaryUniform.eq_1
   binaryUniform_apply_one binaryUniform_apply_zero expandZero groupFirstTwo normalizeBinary
   permute permute_apply pointMass pointMass.eq_1 pointMass_apply_eq
   pointMass_apply_ne shannonEntropy shannonEntropy.eq_1 shannonEntropy_eq_neg_sum ternaryDist
   uniformDist uniformDist_apply)
end Mettapedia.InformationTheory
