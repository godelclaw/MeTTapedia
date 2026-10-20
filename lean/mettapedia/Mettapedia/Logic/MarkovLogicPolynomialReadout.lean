import Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraphPolynomialReadout
import Mettapedia.Logic.MarkovLogicClauseFactorGraph

/-!
# Clause-scope MLN queries in polynomial module readouts

The bridge reuses the actual clause-scope factor graph. Each active weighted
clause retains its own potential and scope. Reference tree execution recovers
the native sum of clause-product world weights for every finite Boolean query.
The general grounded-clause potentials include hard zeros.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.MarkovLogicPolynomialReadout

open scoped ENNReal
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.ProbabilityTheory.BayesianNetworks.FactorGraphPolynomialReadout
open Mettapedia.GSLT.LanguageDef.FiniteFactorReadouts
open Mettapedia.GSLT.LanguageDef.PolynomialReadoutEvaluation
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.Logic.MarkovLogicClauseFactorGraph.GroundMLN

variable {Atom ClauseId : Type*} [Fintype Atom] [DecidableEq Atom] [DecidableEq ClauseId]

/-- Compile the existing clause-scope factor graph while retaining its individual potentials. -/
noncomputable def queryReadout (model : GroundMLN Atom ClauseId) (support : Finset ClauseId)
    (query : AtomValuation Atom → Bool) : Pattern :=
  readout (compiledClauseFactorGraph model support) (fun configuration => query (fun atom => configuration atom))

omit [DecidableEq ClauseId] in
/-- Executed polynomial query mass equals the actual product-of-clauses world mass. -/
theorem run_query_readout (model : GroundMLN Atom ClauseId) (support : Finset ClauseId)
    (query : AtomValuation Atom → Bool) :
    (run (values (table (compiledClauseFactorGraph model support)))
      (queryReadout model support query)).value =
        ∑ world, if query world then model.worldWeight support world else 0 := by
  have law := run_readout (compiledClauseFactorGraph model support)
    (fun configuration => query (fun atom => configuration atom))
  change (run (values (table (compiledClauseFactorGraph model support)))
    (queryReadout model support query)).value = _ at law
  rw [law]
  change (∑ world : AtomValuation Atom, if query world then
    (compiledClauseFactorGraph model support).unnormalizedJoint world else 0) = _
  simp only [compiledClauseFactorGraph_unnormalizedJoint_eq_worldWeight]

omit [DecidableEq ClauseId] in
/-- The polynomial module evaluator and the existing variable-elimination
algorithm compute the same native clause-scope query mass. -/
theorem run_constraint_readout_eq_variable_elimination
    (model : GroundMLN Atom ClauseId) (support : Finset ClauseId) (constraints : Mettapedia.Logic.MarkovLogicClauseFactorGraph.ConstraintQuery Atom) :
    (run (values (table (compiledClauseFactorGraph model support)))
      (queryReadout model support (fun world => decide (Mettapedia.Logic.MarkovLogicClauseFactorGraph.satisfiesConstraints world constraints)))).value =
      Mettapedia.ProbabilityTheory.BayesianNetworks.VariableElimination.veQueryWeight (fg := compiledClauseFactorGraph model support) constraints := by
  rw [run_query_readout, veQueryWeight_eq_worldWeight_sum]
  simp only [decide_eq_true_eq]


end Mettapedia.Logic.MarkovLogicPolynomialReadout
