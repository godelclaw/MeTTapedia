import Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraphPolynomialReadout
import Mettapedia.PLN.Bridges.Languages.ProbLog.ClauseExtension

/-!
# ProbLog finite factor observations in polynomial module readouts

The reference evaluator executes the existing finite least-model factor
presentation. Its complete mass semantics agrees with both that presentation
and the grounded-clause interpretation. Bounded fact probabilities license the
original normalized distribution-semantics answer.

The selected least-model observation can be noncomputable. This is a verified
finite-table execution boundary, not a new executable saturation algorithm for
arbitrary source programs.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.Languages.ProbLog.FactorReadouts

open scoped ENNReal NNReal
open Mettapedia.Logic.LP
open Mettapedia.PLN.Bridges.Languages.ProbLog.Compilation
open Mettapedia.PLN.Bridges.Languages.ProbLog.FunctionalExtension
open Mettapedia.PLN.Bridges.Languages.ProbLog.ClauseExtension
open Mettapedia.ProbabilityTheory
open Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraphPolynomialReadout

variable {σ : LPSignature} {n m : ℕ}

local instance (program : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ) (flag : Bool) :
    Fintype ((factorGraph program queries).stateSpace flag) := by
  change Fintype (Mettapedia.ProbabilityTheory.BayesianNetworks.FunctionalExtension.stateSpace
    (Source := Fin (2^n)) (Output := Fin m → Bool) flag)
  cases flag <;> dsimp [Mettapedia.ProbabilityTheory.BayesianNetworks.FunctionalExtension.stateSpace] <;>
    infer_instance

local instance (program : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ) :
    Fintype (factorGraph program queries).factors := inferInstanceAs (Fintype Bool)

/-- Execute the finite factor presentation of the selected least-model observations. -/
noncomputable def mass (program : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ) :
    MassSemantics ((Fin m → Bool) → Bool) :=
  compiledMass (factorGraph program queries) (fun configuration => configuration true)

/-- The evaluator realizes the independent finite factor semantics. -/
theorem mass_eq_factor_mass (program : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ) :
    mass program queries = factorMass program queries := by
  have observation := compiled_mass_eq_observation (Output := Fin m → Bool)
    (factorGraph program queries) (fun configuration => configuration true)
  exact observation

/-- The same executed mass object agrees with the grounded-clause presentation. -/
theorem mass_eq_clause_mass (program : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ) :
    mass program queries = clauseMass program queries := by
  rw [mass_eq_factor_mass, clause_mass_eq_factor_mass]

/-- With bounded fact probabilities, execution retains the original distribution-semantics query. -/
theorem normalized_query (program : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ)
    (normalized : ∀ index, program.probs index ≤ 1) (event : (Fin m → Bool) → Bool) :
    (mass program queries).query event =
      some (Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics.queryProb
        program.probs (fun world => event (realize program queries world))) := by
  rw [mass_eq_factor_mass, factor_query program queries normalized]

end Mettapedia.PLN.Bridges.Languages.ProbLog.FactorReadouts
