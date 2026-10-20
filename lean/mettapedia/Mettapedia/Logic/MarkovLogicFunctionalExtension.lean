import Mettapedia.Logic.MarkovLogicFiniteTable
import Mettapedia.ProbabilityTheory.FiniteFunctionalExtension

/-!
# Deterministic Boolean extensions through grounded clauses

Source and derived atoms remain distinct. A valuation of their sum is in
bijection with a source-output pair. Blocking clauses encode the deterministic
extension table, and summing their actual product preserves all joint output
queries and the total mass. Table size can be exponential in the atom count.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.MarkovLogicFunctionalExtension

open scoped ENNReal NNReal BigOperators
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicCountable
open Mettapedia.Logic.MarkovLogicFiniteTable
open Mettapedia.ProbabilityTheory.FiniteFunctionalExtension

variable {SourceAtom OutputAtom : Type*} [Fintype SourceAtom] [Fintype OutputAtom]
  [DecidableEq SourceAtom] [DecidableEq OutputAtom]

/-- Disjoint atom namespaces retain both source and auxiliary valuations. -/
def valuationEquiv : ((SourceAtom → Bool) × (OutputAtom → Bool)) ≃
    ((SourceAtom ⊕ OutputAtom) → Bool) where
  toFun pair := Sum.elim pair.1 pair.2
  invFun world := (world ∘ Sum.inl, world ∘ Sum.inr)
  left_inv _ := rfl
  right_inv world := by funext atom; cases atom <;> rfl

omit [Fintype SourceAtom] [Fintype OutputAtom] [DecidableEq SourceAtom] [DecidableEq OutputAtom] in
@[simp] theorem valuationEquiv_output (pair : (SourceAtom → Bool) × (OutputAtom → Bool)) :
    valuationEquiv pair ∘ Sum.inr = pair.2 := rfl

noncomputable def extensionWeight (realize : (SourceAtom → Bool) → OutputAtom → Bool)
    (weight : (SourceAtom → Bool) → ℝ≥0) (world : (SourceAtom ⊕ OutputAtom) → Bool) : ℝ≥0 :=
  extend realize weight (valuationEquiv.symm world)

/-- An explicit grounded-clause representation, including its hard zeros. -/
noncomputable def clauseModel (realize : (SourceAtom → Bool) → OutputAtom → Bool)
    (weight : (SourceAtom → Bool) → ℝ≥0) :
    GroundMLN (SourceAtom ⊕ OutputAtom) ((SourceAtom ⊕ OutputAtom) → Bool) :=
  tableMLN (fun world => (extensionWeight realize weight world : ℝ≥0∞))
    (fun _ => ENNReal.coe_ne_top)

/-- The observed values come from the actual clause-product semantics. -/
noncomputable def massSemantics (realize : (SourceAtom → Bool) → OutputAtom → Bool)
    (weight : (SourceAtom → Bool) → ℝ≥0) :
    Mettapedia.ProbabilityTheory.MassSemantics ((OutputAtom → Bool) → Bool) := by
  letI : Encodable ((SourceAtom ⊕ OutputAtom) → Bool) := GroundMLN.atomValuationEncodable
  exact ((clauseModel realize weight).toCountableMLNSemantics Finset.univ
    (fun event world => event (world ∘ Sum.inr) = true)).toMassSemantics

/-- Clause-product summation agrees with deterministic source observation,
including the unnormalized masses and the zero-total case. -/
theorem clause_mass_eq_source (realize : (SourceAtom → Bool) → OutputAtom → Bool)
    (weight : (SourceAtom → Bool) → ℝ≥0) :
    massSemantics realize weight = observationMass weight realize := by
  classical
  rw [← extended_mass_eq realize weight]
  apply Mettapedia.ProbabilityTheory.MassSemantics.ext
  · funext event
    dsimp only [massSemantics, CountableMLNSemantics.toMassSemantics,
      CountableMLNSemantics.queryMass, GroundMLN.toCountableMLNSemantics]
    rw [tsum_fintype, ← valuationEquiv.sum_comp]
    simp only [clauseModel, tableMLN_worldWeight, extensionWeight, Equiv.symm_apply_apply]
    simp only [valuationEquiv_output]
    simp only [observationMass]
    rw [ENNReal.ofNNReal_finsetSum]
    apply Finset.sum_congr rfl
    intro pair _
    by_cases observed : event pair.2 = true <;> simp [observed]
  · change (∑' world : (SourceAtom ⊕ OutputAtom) → Bool,
      (clauseModel realize weight).worldWeight Finset.univ world) = _
    rw [tsum_fintype, ← valuationEquiv.sum_comp]
    simp only [clauseModel, tableMLN_worldWeight, extensionWeight, Equiv.symm_apply_apply]
    exact (ENNReal.ofNNReal_finsetSum Finset.univ (extend realize weight)).symm

end Mettapedia.Logic.MarkovLogicFunctionalExtension
