import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Boundaries

open Mettapedia.OSLF.Framework

/-!
# Stable typed profiles for equation-invariant generated judgments

A law has a coherent shared context and preserves formation at every context
valuation. The finite checker compares partial sort results, including failed
formation, so agreement at one context does not certify a stable profile.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence

open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

variable {S : Signature.{0}}

/-- Both sides form together somewhere and have exactly the same formation
judgments everywhere. This is independent of the Boolean checker. -/
def StableEquation (profile : Profile S) (equation : Equation S) : Prop :=
  CoherentEquation profile equation ∧
    ∀ valuation sort, Formed profile valuation equation.1 sort ↔ Formed profile valuation equation.2 sort

private theorem option_eq_iff (first second : Option HSort) :
    first = second ↔ ∀ sort, (first = some sort ↔ second = some sort) := by
  constructor
  · intro equal
    rw [equal]
    exact fun _ => Iff.rfl
  · intro readout
    cases first with
    | none =>
        cases second with
        | none => rfl
        | some sort =>
            have contradiction := (readout sort).mpr rfl
            cases contradiction
    | some sort => exact ((readout sort).mp rfl).symm

theorem formation_stable_iff_uniform (profile : Profile S) (equation : Equation S) :
    (∀ valuation sort, Formed profile valuation equation.1 sort ↔ Formed profile valuation equation.2 sort) ↔
      UniformSortInvariant profile equation := by
  constructor
  · intro formed valuation
    apply (option_eq_iff _ _).mpr
    intro sort
    rw [evaluate_iff_formed, evaluate_iff_formed]
    exact formed valuation sort
  · intro uniform valuation sort
    rw [← evaluate_iff_formed, ← evaluate_iff_formed, uniform valuation]

def checkUniform (profile : Profile S) (equation : Equation S) : Bool :=
  decide (∀ valuation : Fin (contextBound equation) → HSort,
    equation.1.evaluateBelow (partialModel profile) (fun index => some (valuation index))
      (Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.left_bounded equation) =
    equation.2.evaluateBelow (partialModel profile) (fun index => some (valuation index))
      (Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.right_bounded equation))

theorem checkUniform_iff (profile : Profile S) (equation : Equation S) :
    checkUniform profile equation = true ↔ UniformSortInvariant profile equation := by
  constructor
  · intro checked valuation
    have equal := of_decide_eq_true checked (fun index : Fin (contextBound equation) => valuation index.val)
    rw [Term.evaluateBelow_eq_evaluate (totalValuation := fun index => some (valuation index))
        (agrees := fun _ _ => rfl),
      Term.evaluateBelow_eq_evaluate (totalValuation := fun index => some (valuation index))
        (agrees := fun _ _ => rfl)] at equal
    exact equal
  · intro invariant
    apply decide_eq_true
    intro valuation
    rw [Term.evaluateBelow_eq_evaluate (totalValuation := fun index => some (extend valuation index))
        (agrees := fun index below => by simp [extend, below]),
      Term.evaluateBelow_eq_evaluate (totalValuation := fun index => some (extend valuation index))
        (agrees := fun index below => by simp [extend, below])]
    exact invariant (extend valuation)

def checkStableEquation (profile : Profile S) (equation : Equation S) : Bool :=
  checkEquation profile equation && checkUniform profile equation

theorem checkStableEquation_iff (profile : Profile S) (equation : Equation S) :
    checkStableEquation profile equation = true ↔ StableEquation profile equation := by
  simp only [checkStableEquation, Bool.and_eq_true, checkEquation_iff, checkUniform_iff, StableEquation,
    formation_stable_iff_uniform]

def Stable (system : EquationSystem S) (profile : Profile S) : Prop :=
  ∀ equation ∈ system.equations, StableEquation profile equation

def checkStable (system : EquationSystem S) (profile : Profile S) : Bool :=
  system.equations.all (checkStableEquation profile)

theorem checkStable_iff (system : EquationSystem S) (profile : Profile S) :
    checkStable system profile = true ↔ Stable system profile := by
  simp only [checkStable, List.all_eq_true, Stable, checkStableEquation_iff]

variable [Fintype S.Operation] [DecidableEq S.Operation]

def stableCenter (system : EquationSystem S) : Finset (Profile S) :=
  Finset.univ.filter fun profile => checkStable system profile = true

theorem mem_stableCenter_iff (system : EquationSystem S) (profile : Profile S) :
    profile ∈ stableCenter system ↔ Stable system profile := by
  simp [stableCenter, checkStable_iff]

theorem no_equations_stable_whole_cube (system : EquationSystem S) (empty : system.equations = []) :
    stableCenter system = Finset.univ := by
  simp [stableCenter, checkStable, empty]

omit [Fintype S.Operation] [DecidableEq S.Operation] in
theorem uniform_rename (profile : Profile S) (permutation : Nat ≃ Nat) (equation : Equation S) :
    UniformSortInvariant profile
      (equation.1.subst (fun index => .var (permutation index)),
       equation.2.subst (fun index => .var (permutation index))) ↔
      UniformSortInvariant profile equation := by
  constructor
  · intro invariant valuation
    have equal := invariant (fun index => valuation (permutation.symm index))
    simpa only [Term.evaluate_subst, Term.evaluate, Equiv.symm_apply_apply] using equal
  · intro invariant valuation
    simpa only [Term.evaluate_subst, Term.evaluate] using
      invariant (fun index => valuation (permutation index))

omit [Fintype S.Operation] [DecidableEq S.Operation] in
theorem stable_equation_rename (profile : Profile S) (permutation : Nat ≃ Nat) (equation : Equation S) :
    StableEquation profile
      (equation.1.subst (fun index => .var (permutation index)),
       equation.2.subst (fun index => .var (permutation index))) ↔
      StableEquation profile equation := by
  exact and_congr (coherent_rename profile permutation equation)
    (((formation_stable_iff_uniform profile _).trans (uniform_rename profile permutation equation)).trans
      (formation_stable_iff_uniform profile equation).symm)

theorem stableCenter_rename (system : EquationSystem S) (permutation : Nat ≃ Nat) :
    stableCenter (Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.rename permutation system) = stableCenter system := by
  ext profile
  rw [mem_stableCenter_iff, mem_stableCenter_iff]
  unfold Stable Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.rename
  simp only [List.mem_map]
  constructor
  · intro stable equation member
    exact (stable_equation_rename profile permutation equation).mp
      (stable _ ⟨equation, member, rfl⟩)
  · intro stable equation member
    obtain ⟨original, member, rfl⟩ := member
    exact (stable_equation_rename profile permutation original).mpr (stable original member)

omit [Fintype S.Operation] [DecidableEq S.Operation] in
/-- The strengthened check excludes the variable equation for every profile;
its previously coherent context cannot justify arbitrary-context stability. -/
theorem variable_equation_never_stable (profile : Profile S) :
    ¬ StableEquation profile (.var 0, .var 1) := by
  intro stable
  exact (shared_context_is_not_uniform_stability profile).2
    ((formation_stable_iff_uniform profile _).mp stable.2)

end Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence
