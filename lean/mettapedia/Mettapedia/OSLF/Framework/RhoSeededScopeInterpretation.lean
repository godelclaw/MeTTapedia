import Mettapedia.OSLF.Framework.RhoSeededScopeStages

/-!
# The finite rho strata are exactly the authored seeded scope

The independently interpreted positive scope expression is compared with the
actual seed-and-pair transformer. Its least fixed point consists exactly of
names in some constructed finite stratum. Thus the finite-set counts concern
the scope expression's real source equation classes, not merely a recurrence
or a separately selected tree carrier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoSeededScopeInterpretation

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoCanonicalNamePairs
open RhoScopeExpression RhoScopeSeedReadings RhoSeededScopeStages

def step : (Name [] → Prop) →o (Name [] → Prop) where
  toFun := fun names name => name = quote (zero []) ∨ name = quote visible ∨
    ∃ first second, names first ∧ names second ∧ combine first second = name
  monotone' := by
    intro firstNames secondNames included name member
    rcases member with seed | seed | ⟨first, second, firstMember, secondMember, readout⟩
    · exact Or.inl seed
    · exact Or.inr (Or.inl seed)
    · exact Or.inr (Or.inr ⟨first, second, included _ firstMember, included _ secondMember, readout⟩)

theorem body_reading (names : Name [] → Prop) (env : RhoScopeExpression.Environment []) :
    denote atoms seededBody (push names env) = step names := by
  funext name
  apply propext
  change (((∃ process, process = zero [] ∧ quote process = name) ∨
      (∃ process, process = visible ∧ quote process = name)) ∨
      (∃ result, (∃ firstProcess secondProcess,
        (∃ first, names first ∧ drop first = firstProcess) ∧
        (∃ second, names second ∧ drop second = secondProcess) ∧
        join firstProcess secondProcess = result) ∧ quote result = name)) ↔
    (name = quote (zero []) ∨ name = quote visible ∨
      ∃ first second, names first ∧ names second ∧ combine first second = name)
  constructor
  · rintro ((left | right) | compound)
    · obtain ⟨_, rfl, readout⟩ := left
      exact Or.inl readout.symm
    · obtain ⟨_, rfl, readout⟩ := right
      exact Or.inr (Or.inl readout.symm)
    · obtain ⟨_, ⟨_, _, ⟨first, firstMember, rfl⟩, ⟨second, secondMember, rfl⟩, rfl⟩,
        readout⟩ := compound
      exact Or.inr (Or.inr ⟨first, second, firstMember, secondMember, readout⟩)
  · rintro (rfl | rfl | ⟨first, second, firstMember, secondMember, readout⟩)
    · exact Or.inl (Or.inl ⟨zero [], rfl, rfl⟩)
    · exact Or.inl (Or.inr ⟨visible, rfl, rfl⟩)
    · exact Or.inr ⟨join (drop first) (drop second),
        ⟨drop first, drop second, ⟨first, firstMember, rfl⟩,
          ⟨second, secondMember, rfl⟩, rfl⟩, readout⟩

theorem seeded_denotation (env : RhoScopeExpression.Environment []) :
    denote atoms seeded env = step.lfp := by
  change ((denote atoms seededBody).comp (pushNames env)).lfp = step.lfp
  have same : (denote atoms seededBody).comp (pushNames env) = step := by
    apply OrderHom.ext
    funext names
    exact body_reading names env
  exact congrArg OrderHom.lfp same

def finiteScope (name : Name []) : Prop := ∃ depth, name ∈ stage depth

theorem finiteScope_closed : step finiteScope ≤ finiteScope := by
  intro name member
  rcases member with rfl | rfl | ⟨first, second, ⟨firstDepth, firstMember⟩,
    ⟨secondDepth, secondMember⟩, readout⟩
  · exact ⟨0, (mem_seeds _).mpr (Or.inl rfl)⟩
  · exact ⟨0, (mem_seeds _).mpr (Or.inr rfl)⟩
  · refine ⟨max firstDepth secondDepth + 1, (mem_stage_succ _ _).mpr (Or.inr (Or.inr ?_))⟩
    exact ⟨first, second, stage_monotone (Nat.le_max_left _ _) firstMember,
      stage_monotone (Nat.le_max_right _ _) secondMember, readout⟩

theorem step_into_lfp {name : Name []} (member : step step.lfp name) : step.lfp name := by
  rw [← OrderHom.map_lfp step]
  exact member

theorem stage_into_lfp (depth : Nat) : ∀ name, name ∈ stage depth → step.lfp name := by
  induction depth with
  | zero =>
    intro name member
    rcases (mem_seeds _).mp member with left | right
    · exact step_into_lfp (Or.inl left)
    · exact step_into_lfp (Or.inr (Or.inl right))
  | succ depth ih =>
    intro name member
    rcases (mem_stage_succ _ _).mp member with left | right |
      ⟨first, second, firstMember, secondMember, readout⟩
    · exact step_into_lfp (Or.inl left)
    · exact step_into_lfp (Or.inr (Or.inl right))
    · exact step_into_lfp (Or.inr (Or.inr ⟨first, second,
        ih first firstMember, ih second secondMember, readout⟩))

theorem seeded_membership_iff (env : RhoScopeExpression.Environment []) (name : Name []) :
    denote atoms seeded env name ↔ ∃ depth, name ∈ stage depth := by
  rw [seeded_denotation]
  exact ⟨step.lfp_le finiteScope_closed name,
    fun ⟨depth, member⟩ => stage_into_lfp depth name member⟩

theorem stage_members_are_actual_scope (env : RhoScopeExpression.Environment [])
    (depth : Nat) {name : Name []} (member : name ∈ stage depth) :
    denote atoms seeded env name := (seeded_membership_iff env name).mpr ⟨depth, member⟩

end Mettapedia.OSLF.Framework.RhoSeededScopeInterpretation
