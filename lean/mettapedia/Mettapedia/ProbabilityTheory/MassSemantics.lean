import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mettapedia.Logic.WorldModel.Basic

/-!
# Query masses, normalization and mixture revision

This representation-neutral interface describes finite unnormalized query
masses. It does not interpret total mass as an observation count. Mixture
revision adds masses; factor composition and program union are different
operations. Normalization is a readout and is not additive.
-/

namespace Mettapedia.ProbabilityTheory

open scoped ENNReal BigOperators

structure MassSemantics (Query : Type*) where
  queryMass : Query → ℝ≥0∞
  totalMass : ℝ≥0∞
  queryMass_le_total : ∀ query, queryMass query ≤ totalMass
  totalMass_ne_top : totalMass ≠ ⊤

namespace MassSemantics

variable {Query : Type*}

@[ext] theorem ext {first second : MassSemantics Query}
    (queries : first.queryMass = second.queryMass) (total : first.totalMass = second.totalMass) :
    first = second := by
  cases first
  cases second
  cases queries
  cases total
  rfl

/-- The legacy zero-mass numerical convention. `query` retains its absence. -/
noncomputable def queryProb (source : MassSemantics Query) (query : Query) : ℝ≥0∞ :=
  if source.totalMass = 0 then 0 else source.queryMass query / source.totalMass

/-- Normalized observation with an explicit impossible/empty-source outcome. -/
noncomputable def query (source : MassSemantics Query) (request : Query) : Option ℝ≥0∞ :=
  if source.totalMass = 0 then none else some (source.queryProb request)

def empty : MassSemantics Query where
  queryMass _ := 0
  totalMass := 0
  queryMass_le_total _ := le_rfl
  totalMass_ne_top := ENNReal.zero_ne_top

noncomputable def mix (first second : MassSemantics Query) : MassSemantics Query where
  queryMass request := first.queryMass request + second.queryMass request
  totalMass := first.totalMass + second.totalMass
  queryMass_le_total request := add_le_add (first.queryMass_le_total request) (second.queryMass_le_total request)
  totalMass_ne_top := ENNReal.add_ne_top.mpr ⟨first.totalMass_ne_top, second.totalMass_ne_top⟩

/-- General WM semantics is the default. Its normalized query is not an
additive evidence extraction. -/
noncomputable instance : MonoidalWorldModel (MassSemantics Query) Query (Option ℝ≥0∞) where
  revise := mix
  empty := empty
  extract := query
  revise_assoc first second third := by ext request <;> simp [mix, add_assoc]
  revise_empty_left source := by ext request <;> simp [mix, empty]
  revise_empty_right source := by ext request <;> simp [mix, empty]

theorem queryProb_le_one (source : MassSemantics Query) (request : Query) :
    source.queryProb request ≤ 1 := by
  unfold queryProb
  split_ifs
  · exact zero_le_one
  · apply ENNReal.div_le_of_le_mul
    simpa using source.queryMass_le_total request

@[simp] theorem query_empty (request : Query) : (empty : MassSemantics Query).query request = none := by
  simp [query, empty]

/-- A finite world-weight table is an instance without requiring any PLN,
MLN, or logic-program interpretation of its worlds. -/
noncomputable def ofFiniteWeights {Ω : Type*} [Fintype Ω]
    (weight : Ω → ℝ≥0∞) (finite : ∀ world, weight world ≠ ⊤) :
    MassSemantics (Ω → Bool) where
  queryMass event := ∑ world, if event world then weight world else 0
  totalMass := ∑ world, weight world
  queryMass_le_total event := Finset.sum_le_sum fun world _ => by split_ifs <;> simp
  totalMass_ne_top := ENNReal.sum_ne_top.mpr (fun world _ => finite world)

namespace Controls

def unitSource : MassSemantics Unit where
  queryMass _ := 1
  totalMass := 1
  queryMass_le_total _ := le_rfl
  totalMass_ne_top := ENNReal.one_ne_top

/-- Adding masses changes the source but may preserve every probability. -/
theorem mixture_changes_mass_not_probability :
    (mix unitSource unitSource).totalMass ≠ unitSource.totalMass ∧
      (mix unitSource unitSource).queryProb () = unitSource.queryProb () := by
  norm_num [mix, unitSource, queryProb, ENNReal.div_self]

/-- Normalization cannot be used as the additive observation law. -/
theorem normalization_not_additive :
    (mix unitSource unitSource).queryProb () ≠ unitSource.queryProb () + unitSource.queryProb () := by
  norm_num [mix, unitSource, queryProb, ENNReal.div_self]

end Controls

end MassSemantics
end Mettapedia.ProbabilityTheory
