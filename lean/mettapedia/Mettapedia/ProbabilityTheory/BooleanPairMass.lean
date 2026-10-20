import Mettapedia.ProbabilityTheory.FiniteConditionalStability

/-!
# Event masses and conditional readouts on a Boolean pair

These identities concern the independently defined finite sums. They make no
normalization or independence assumption about the supplied table.
-/

set_option autoImplicit false

namespace Mettapedia.ProbabilityTheory.BooleanPairMass

open scoped BigOperators
open Mettapedia.ProbabilityTheory.FiniteEventMass
open Mettapedia.ProbabilityTheory.FiniteConditionalStability

theorem mass_fst (weight : Bool × Bool → ℝ) :
    mass weight Prod.fst = ∑ second, weight (true, second) := by
  simp [mass, Fintype.sum_prod_type]

theorem mass_snd (weight : Bool × Bool → ℝ) :
    mass weight Prod.snd = ∑ first, weight (first, true) := by
  simp [mass, Fintype.sum_prod_type]

theorem mass_snd_and_fst (weight : Bool × Bool → ℝ) :
    mass weight (fun world => world.2 && world.1) = weight (true, true) := by
  simp [mass, Fintype.sum_prod_type]

theorem conditional_snd_fst (weight : Bool × Bool → ℝ) :
    conditional weight Prod.snd Prod.fst = weight (true, true) / ∑ second, weight (true, second) := by
  rw [conditional, mass_snd_and_fst, mass_fst]

end Mettapedia.ProbabilityTheory.BooleanPairMass
