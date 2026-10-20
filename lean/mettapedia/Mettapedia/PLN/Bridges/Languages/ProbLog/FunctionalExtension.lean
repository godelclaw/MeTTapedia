import Mettapedia.PLN.Bridges.Languages.ProbLog.Compilation
import Mettapedia.PLN.Bridges.Languages.ProbLog.MassSemantics
import Mettapedia.ProbabilityTheory.BayesianNetworks.FunctionalExtension

/-!
# Least-model observations as deterministic factor extensions

A total choice determines a residual definite program and hence a unique least
Herbrand model. Selecting finitely many atoms gives a finite Boolean observation
of that model. A factor graph extends each total choice by exactly that output,
preserving all joint query masses and the partition mass.

The program may be recursive; its interpretation uses the existing least-model
semantics. This is a semantic construction, not an executable saturation or
knowledge-compilation algorithm. The auxiliary consistency factor can have an
arbitrarily large table. It does not assert independence among derived atoms.
-/

set_option autoImplicit false

namespace Mettapedia.PLN.Bridges.Languages.ProbLog.FunctionalExtension

open scoped ENNReal NNReal BigOperators
open Mettapedia.Logic.LP
open Mettapedia.PLN.Core.CompletePLN
open Mettapedia.PLN.Evidence.PLNJointEvidence.JointEvidence
open Mettapedia.PLN.Bridges.Languages.ProbLog.Compilation
open Mettapedia.PLN.Bridges.Languages.ProbLog.DistributionSemantics
open Mettapedia.Logic.BDDCore.WMPLNBDDWMCExact
open Mettapedia.ProbabilityTheory.FiniteFunctionalExtension

variable {σ : LPSignature} {n m : ℕ}

/-- A finite joint observation of the residual program's least model. -/
noncomputable def realize (prog : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ)
    (world : Fin (2 ^ n)) : Fin m → Bool := by
  classical
  exact fun index => decide (queryHolds prog (queries index) world)

@[simp] theorem realize_eq_true (prog : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ)
    (world : Fin (2 ^ n)) (index : Fin m) :
    realize prog queries world index = true ↔ queryHolds prog (queries index) world := by
  classical
  simp [realize]

theorem worldWeight_le_one (p : ProbAssignment n) (normalized : ∀ index, p index ≤ 1)
    (world : Fin (2 ^ n)) : worldWeight p world ≤ 1 := by
  apply Finset.prod_le_one'
  intro index _
  unfold factWeight
  split_ifs
  · exact normalized index
  · exact tsub_le_self

/-- Finite nonnegative weights retain the original total-choice masses. -/
noncomputable def sourceWeight (prog : ProbLogProgram σ n) : Fin (2 ^ n) → ℝ≥0 :=
  fun world => (worldWeight prog.probs world).toNNReal

@[simp] theorem coe_sourceWeight (prog : ProbLogProgram σ n)
    (normalized : ∀ index, prog.probs index ≤ 1) (world : Fin (2 ^ n)) :
    (sourceWeight prog world : ℝ≥0∞) = worldWeight prog.probs world := by
  apply ENNReal.coe_toNNReal
  exact ne_top_of_le_ne_top ENNReal.one_ne_top (worldWeight_le_one prog.probs normalized world)

/-- The actual two-variable factor graph, with source-weight and consistency
factors. Its output variable carries all selected atoms jointly. -/
noncomputable def factorGraph (prog : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ) :=
  Mettapedia.ProbabilityTheory.BayesianNetworks.FunctionalExtension.graph
    (realize prog queries) (sourceWeight prog)

/-- Joint mass semantics obtained by summing the factor graph's configurations. -/
noncomputable def factorMass (prog : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ) :=
  Mettapedia.ProbabilityTheory.BayesianNetworks.FunctionalExtension.massSemantics
    (realize prog queries) (sourceWeight prog)

/-- Every Boolean predicate on the selected atoms is preserved. This includes
conjunction, disjunction, and overlapping explanations without derivation counts. -/
theorem factor_queryMass (prog : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ)
    (normalized : ∀ index, prog.probs index ≤ 1) (event : (Fin m → Bool) → Bool) :
    (factorMass prog queries).queryMass event =
      queryMass prog.probs (fun world => event (realize prog queries world)) := by
  rw [factorMass,
    Mettapedia.ProbabilityTheory.BayesianNetworks.FunctionalExtension.graph_mass_eq_source]
  change ((∑ world, if event (realize prog queries world) then sourceWeight prog world else 0 :
    ℝ≥0) : ℝ≥0∞) = _
  rw [ENNReal.ofNNReal_finsetSum]
  unfold queryMass countWorld probLogToJointEvidence
  apply Finset.sum_congr rfl
  intro world _
  split_ifs <;> simp [coe_sourceWeight prog normalized]

/-- The deterministic auxiliary does not alter the normalizing constant. -/
theorem factor_totalMass (prog : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ)
    (normalized : ∀ index, prog.probs index ≤ 1) :
    (factorMass prog queries).totalMass = 1 := by
  rw [factorMass,
    Mettapedia.ProbabilityTheory.BayesianNetworks.FunctionalExtension.graph_mass_eq_source]
  change ((∑ world, sourceWeight prog world : ℝ≥0) : ℝ≥0∞) = 1
  rw [ENNReal.ofNNReal_finsetSum]
  simp only [coe_sourceWeight prog normalized]
  exact totalMass_eq_one prog.probs normalized

theorem factor_query (prog : ProbLogProgram σ n) (queries : Fin m → GroundAtom σ)
    (normalized : ∀ index, prog.probs index ≤ 1) (event : (Fin m → Bool) → Bool) :
    (factorMass prog queries).query event =
      some (queryProb prog.probs (fun world => event (realize prog queries world))) := by
  simp [Mettapedia.ProbabilityTheory.MassSemantics.query,
    Mettapedia.ProbabilityTheory.MassSemantics.queryProb, factor_totalMass prog queries normalized,
    factor_queryMass prog queries normalized, queryProb, totalMass_eq_one prog.probs normalized]

/-- An OR-pattern's actual selected least-model query has the noisy-OR value.
Overlapping derivations are counted through worlds, rather than added. -/
theorem factor_or_query (prog : ProbLogProgram σ n) (atom : GroundAtom σ)
    (pattern : IsORPattern prog atom) [IsEmpty σ.functionSymbols] [Nonempty (GroundTerm σ)]
    (normalized : ∀ index, prog.probs index ≤ 1) :
    (factorMass prog (fun _ : Fin 1 => atom)).query (fun values => values 0) =
      some (1 - ∏ index, (1 - prog.probs index)) := by
  rw [factor_query prog (fun _ : Fin 1 => atom) normalized]
  have observation : (fun world => realize prog (fun _ : Fin 1 => atom) world 0) =
      anyTrue (List.finRange n) := by
    funext world
    apply Bool.eq_iff_iff.mpr
    rw [realize_eq_true]
    exact queryHolds_iff_anyTrue prog atom pattern world
  rw [observation, compilation_or_noisyOr prog atom pattern normalized (by positivity)]

end Mettapedia.PLN.Bridges.Languages.ProbLog.FunctionalExtension
