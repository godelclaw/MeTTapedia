import Mettapedia.PLN.Bridges.Languages.ProbLog.FunctionalExtension
import Mettapedia.Logic.MarkovLogicFunctionalExtension

/-!
# ProbLog least-model queries through grounded clauses

The source fact bits and the selected derived atoms have disjoint names.
An explicit Boolean-world equivalence connects total choices to source
valuations. The grounded clauses then represent exactly the deterministic
least-model extension. Their complete output mass semantics agrees with the
independently defined two-factor graph, before normalization.

The clause presentation is generally exponential and uses hard zeros. This
establishes semantic representability, not an efficient program compiler or an
encoding using only finite real log-weights.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.Languages.ProbLog.ClauseExtension

open scoped NNReal ENNReal
open Mettapedia.Logic.LP
open Mettapedia.Logic.BDDCore.WMPLNBDDWMCExact
open Mettapedia.PLN.Bridges.Languages.ProbLog.Compilation
open Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics
open Mettapedia.PLN.Bridges.Languages.ProbLog.FunctionalExtension
open Mettapedia.ProbabilityTheory.FiniteFunctionalExtension

variable {σ : LPSignature} {n m : ℕ}

noncomputable def choiceWeight (prog : ProbLogProgram σ n) (world : Fin n → Bool) : ℝ≥0 :=
  sourceWeight prog ((worldAssignmentEquiv n).symm world)

noncomputable def choiceRealize (prog : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ)
    (world : Fin n → Bool) : Fin m → Bool :=
  realize prog queries ((worldAssignmentEquiv n).symm world)

/-- Actual grounded clauses over both source and derived atom namespaces. -/
noncomputable def clauses (prog : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ) :=
  Mettapedia.Logic.MarkovLogicFunctionalExtension.clauseModel
    (choiceRealize prog queries) (choiceWeight prog)

noncomputable def clauseMass (prog : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ) :=
  Mettapedia.Logic.MarkovLogicFunctionalExtension.massSemantics
    (choiceRealize prog queries) (choiceWeight prog)

/-- The clause and factor presentations agree as complete mass objects.
The equality includes every Boolean joint query on the selected atoms. -/
theorem clause_mass_eq_factor_mass (prog : ProbLogProgram σ n)
    (queries : Fin m → GroundAtom σ) :
    clauseMass prog queries = factorMass prog queries := by
  rw [clauseMass, Mettapedia.Logic.MarkovLogicFunctionalExtension.clause_mass_eq_source,
    factorMass,
    Mettapedia.ProbabilityTheory.BayesianNetworks.FunctionalExtension.graph_mass_eq_source]
  have reindex := observationMass_equiv (worldAssignmentEquiv n)
    (choiceWeight prog) (choiceRealize prog queries)
  simpa only [choiceWeight, choiceRealize, Function.comp_def, Equiv.symm_apply_apply] using
    reindex.symm

theorem clause_query (prog : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ)
    (normalized : ∀ index, prog.probs index ≤ 1) (event : (Fin m → Bool) → Bool) :
    (clauseMass prog queries).query event =
      some (queryProb prog.probs (fun world => event (realize prog queries world))) := by
  rw [clause_mass_eq_factor_mass, factor_query prog queries normalized]

end Mettapedia.PLN.Bridges.Languages.ProbLog.ClauseExtension
