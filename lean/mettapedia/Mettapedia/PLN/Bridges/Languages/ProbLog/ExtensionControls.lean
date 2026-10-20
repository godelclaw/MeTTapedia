import Mettapedia.PLN.Bridges.Languages.ProbLog.ClauseExtension

/-!
# Least-model extension controls

The recursive program `q :- q` has no support for `q`, so its least model makes
`q` false. Treating the rule as a hard material implication admits both Boolean
valuations and gives probability one half instead. The deterministic clause
extension agrees with the least-model interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.Languages.ProbLog.ExtensionControls

open scoped ENNReal BigOperators
open Mettapedia.Logic.LP
open Mettapedia.Logic.MarkovLogicClauseSemantics
open Mettapedia.PLN.Bridges.Languages.ProbLog.Compilation
open Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics
open Mettapedia.PLN.Bridges.Languages.ProbLog.FunctionalExtension
open Mettapedia.PLN.Bridges.Languages.ProbLog.ClauseExtension

private def signature : LPSignature where
  constants := Unit
  vars := Empty
  relationSymbols := Unit
  relationArity _ := 0
  functionSymbols := Empty
  functionArity := Empty.elim

private def queryAtom : GroundAtom signature := ⟨(), Fin.elim0⟩

private def recursiveProgram : ProbLogProgram signature 0 where
  probFacts := Fin.elim0
  probs := Fin.elim0
  rules := [⟨queryAtom.toAtom, [queryAtom.toAtom]⟩]
  facts_injective := by intro first; exact Fin.elim0 first

/-- A recursive rule cannot manufacture support for its own body. -/
theorem recursive_query_absent (world : Fin (2 ^ 0)) :
    ¬ queryHolds recursiveProgram queryAtom world := by
  intro present
  have emptyModel : T_P_LP (residualKB recursiveProgram world) ∅ ⊆ ∅ := by
    rw [T_P_LP_le_iff]
    constructor
    · intro atom member
      obtain ⟨index, _, _⟩ := member
      exact Fin.elim0 index
    · intro clause grounding member body
      have same : clause = ⟨queryAtom.toAtom, [queryAtom.toAtom]⟩ := by
        simpa [residualKB, recursiveProgram] using member
      subst clause
      exact body queryAtom.toAtom (List.mem_cons_self ..)
  exact leastHerbrandModel_least (residualKB recursiveProgram world) ∅ emptyModel present

/-- The selected observation preserves the recursive program's least model. -/
theorem recursive_factor_query :
    (factorMass recursiveProgram (fun _ : Fin 1 => queryAtom)).query (fun values => values 0) =
      some (0 : ℝ≥0∞) := by
  rw [factor_query recursiveProgram (fun _ : Fin 1 => queryAtom) (fun index => Fin.elim0 index)]
  have falseQuery : (fun world => realize recursiveProgram (fun _ : Fin 1 => queryAtom) world 0) =
      fun _ => false := by
    funext world
    apply Bool.eq_false_iff.mpr
    intro yes
    exact recursive_query_absent world ((realize_eq_true _ _ _ _).mp yes)
  rw [falseQuery]
  simp [queryProb, queryMass, Mettapedia.PLN.Evidence.PLNJointEvidence.JointEvidence.countWorld]

theorem recursive_clause_query :
    (clauseMass recursiveProgram (fun _ : Fin 1 => queryAtom)).query (fun values => values 0) =
      some (0 : ℝ≥0∞) := by
  rw [clause_mass_eq_factor_mass, recursive_factor_query]

private noncomputable def materialRule : GroundMLN Unit Unit where
  clauseData _ := {
    clause := {Literal.neg (), Literal.pos ()}
    satisfiedPotential := 1
    unsatisfiedPotential := 0
    satisfied_ne_top := ENNReal.one_ne_top
    unsatisfied_ne_top := ENNReal.zero_ne_top }

private theorem materialRule_weight (world : Unit → Bool) :
    materialRule.worldWeight Finset.univ world = 1 := by
  rw [GroundMLN.worldWeight_eq_prod]
  rw [Fintype.prod_unique]
  cases value : world () <;>
    simp [materialRule, WeightedGroundClause.eval, GroundClause.holds, Literal.holds, value]

private noncomputable def materialMass : Mettapedia.ProbabilityTheory.MassSemantics
    ((Unit → Bool) → Bool) :=
  Mettapedia.ProbabilityTheory.MassSemantics.ofFiniteWeights
    (materialRule.worldWeight Finset.univ) (fun world => materialRule.worldWeight_ne_top _ world)

private theorem sum_single_atom (value : (Unit → Bool) → ℝ≥0∞) :
    (∑ world, value world) = value (fun _ => true) + value (fun _ => false) := by
  rw [← (Equiv.funUnique Unit Bool).symm.sum_comp]
  rw [Fintype.sum_bool]
  rfl

/-- Material implication admits both valuations; normalization cannot recover
least-model selection from this weaker constraint. -/
theorem material_implication_changes_query :
    materialMass.totalMass = 2 ∧
      materialMass.query (fun world => world ()) = some (1/2 : ℝ≥0∞) := by
  simp only [materialMass, Mettapedia.ProbabilityTheory.MassSemantics.query,
    Mettapedia.ProbabilityTheory.MassSemantics.queryProb,
    Mettapedia.ProbabilityTheory.MassSemantics.ofFiniteWeights,
    materialRule_weight, sum_single_atom]
  norm_num

end Mettapedia.PLN.Bridges.Languages.ProbLog.ExtensionControls
