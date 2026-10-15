import Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter

open Mettapedia.OSLF.Framework

/-!
# Typed operation profiles and simultaneous equation formation

A profile has exactly one slot per argument and one result slot. It supplies
formation rules, rather than a complete truth table. A displayed equation is
coherent when one shared variable valuation makes both sides well formed at
the same result sort. The executable test enumerates the finite valuation
space and agrees with the independent inductive formation judgment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence

open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

variable (S : Signature.{0})

abbrev ProfileSlot := Σ operation : S.Operation, Fin (S.arity operation + 1)
abbrev Profile := ProfileSlot S → HSort

variable {S}

def input (profile : Profile S) (operation : S.Operation) (position : Fin (S.arity operation)) : HSort :=
  profile ⟨operation, ⟨position.val, Nat.lt_trans position.isLt (Nat.lt_succ_self _)⟩⟩

def output (profile : Profile S) (operation : S.Operation) : HSort :=
  profile ⟨operation, ⟨S.arity operation, Nat.lt_succ_self _⟩⟩

/-- Formation is an independent inference system. A failed premise is not an
alternative result sort. The context valuation is shared across occurrences. -/
inductive Formed (profile : Profile S) (valuation : Nat → HSort) : Term S → HSort → Prop where
  | variableTerm (index : Nat) : Formed profile valuation (.var index) (valuation index)
  | operation (operation : S.Operation) (arguments : Fin (S.arity operation) → Term S)
      (children : ∀ position, Formed profile valuation (arguments position) (input profile operation position)) :
      Formed profile valuation (.op operation arguments) (output profile operation)

def partialModel (profile : Profile S) : Model S (Option HSort) where
  interpret operation arguments :=
    if ∀ position, arguments position = some (input profile operation position)
      then some (output profile operation) else none

theorem formed_evaluate {profile : Profile S} {valuation : Nat → HSort}
    {term : Term S} {sort : HSort} (formed : Formed profile valuation term sort) :
    term.evaluate (partialModel profile) (fun index => some (valuation index)) = some sort := by
  induction formed with
  | variableTerm index => rfl
  | operation operation arguments children ih =>
      change (if ∀ position, (arguments position).evaluate (partialModel profile)
        (fun index => some (valuation index)) = some (input profile operation position)
      then some (output profile operation) else none) = some (output profile operation)
      exact if_pos ih

theorem evaluate_formed (profile : Profile S) (valuation : Nat → HSort) (term : Term S) :
    ∀ sort, term.evaluate (partialModel profile) (fun index => some (valuation index)) = some sort →
      Formed profile valuation term sort := by
  induction term with
  | var index =>
      intro sort equal
      simp only [Term.evaluate, Option.some.injEq] at equal
      exact equal ▸ .variableTerm index
  | op operation arguments ih =>
      intro sort equal
      simp only [Term.evaluate, partialModel] at equal
      split at equal
      · rename_i checked
        simp only [Option.some.injEq] at equal
        subst sort
        exact .operation operation arguments (fun position => ih position _ (checked position))
      · cases equal

theorem evaluate_iff_formed (profile : Profile S) (valuation : Nat → HSort) (term : Term S) (sort : HSort) :
    term.evaluate (partialModel profile) (fun index => some (valuation index)) = some sort ↔
      Formed profile valuation term sort :=
  ⟨evaluate_formed profile valuation term sort, formed_evaluate⟩


/-- A substitution preserves profile formation when each replacement satisfies
its declared shared-context sort. -/
theorem Formed.substitute {profile : Profile S} {valuation target : Nat → HSort}
    {term : Term S} {sort : HSort} (formed : Formed profile valuation term sort)
    (substitution : Nat → Term S)
    (typed : ∀ index, Formed profile target (substitution index) (valuation index)) :
    Formed profile target (term.subst substitution) sort := by
  induction formed with
  | variableTerm index => exact typed index
  | operation operation arguments children ih =>
      exact .operation operation (fun position => (arguments position).subst substitution) ih

/-- One consistent context makes both equation sides inhabit the same sort. -/
def CoherentEquation (profile : Profile S) (equation : Equation S) : Prop :=
  ∃ valuation sort, Formed profile valuation equation.1 sort ∧ Formed profile valuation equation.2 sort

abbrev contextBound (equation : Equation S) : Nat :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.contextBound equation

def checkEquation (profile : Profile S) (equation : Equation S) : Bool :=
  decide (∃ valuation : Fin (contextBound equation) → HSort, ∃ sort : HSort,
    equation.1.evaluateBelow (partialModel profile) (fun index => some (valuation index))
      (Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.left_bounded equation) = some sort ∧
    equation.2.evaluateBelow (partialModel profile) (fun index => some (valuation index))
      (Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.right_bounded equation) = some sort)

def extend {bound : Nat} (valuation : Fin bound → HSort) : Nat → HSort :=
  fun index => if below : index < bound then valuation ⟨index, below⟩ else .star

/-- The finite checker earns simultaneous formation for all terms of the
signature, with every repeated variable interpreted by the same valuation. -/
theorem checkEquation_iff (profile : Profile S) (equation : Equation S) :
    checkEquation profile equation = true ↔ CoherentEquation profile equation := by
  constructor
  · intro checked
    obtain ⟨valuation, sort, left, right⟩ := of_decide_eq_true checked
    refine ⟨extend valuation, sort, ?_, ?_⟩
    · apply (evaluate_iff_formed profile (extend valuation) _ sort).mp
      rw [← Term.evaluateBelow_eq_evaluate (finiteValuation := fun index => some (valuation index))
        (agrees := fun index below => by simp [extend, below])]
      exact left
    · apply (evaluate_iff_formed profile (extend valuation) _ sort).mp
      rw [← Term.evaluateBelow_eq_evaluate (finiteValuation := fun index => some (valuation index))
        (agrees := fun index below => by simp [extend, below])]
      exact right
  · rintro ⟨valuation, sort, left, right⟩
    apply decide_eq_true
    refine ⟨fun position => valuation position.val, sort, ?_, ?_⟩
    · rw [Term.evaluateBelow_eq_evaluate (totalValuation := fun index => some (valuation index))
        (agrees := fun _ _ => rfl)]
      exact formed_evaluate left
    · rw [Term.evaluateBelow_eq_evaluate (totalValuation := fun index => some (valuation index))
        (agrees := fun _ _ => rfl)]
      exact formed_evaluate right

def check (system : EquationSystem S) (profile : Profile S) : Bool :=
  system.equations.all (checkEquation profile)

def Coherent (system : EquationSystem S) (profile : Profile S) : Prop :=
  ∀ equation ∈ system.equations, CoherentEquation profile equation

theorem check_iff_coherent (system : EquationSystem S) (profile : Profile S) :
    check system profile = true ↔ Coherent system profile := by
  simp only [check, List.all_eq_true, Coherent, checkEquation_iff]

variable [Fintype S.Operation] [DecidableEq S.Operation]

def center (system : EquationSystem S) : Finset (Profile S) :=
  Finset.univ.filter fun profile => check system profile = true

theorem mem_center_iff (system : EquationSystem S) (profile : Profile S) :
    profile ∈ center system ↔ Coherent system profile := by
  simp [center, check_iff_coherent]

theorem no_equations_whole_cube (system : EquationSystem S) (empty : system.equations = []) :
    center system = Finset.univ := by
  simp [center, check, empty]

omit [Fintype S.Operation] [DecidableEq S.Operation] in
/-- Injectively renaming variables preserves repeated-variable consistency. -/
theorem coherent_rename (profile : Profile S) (permutation : Nat ≃ Nat) (equation : Equation S) :
    CoherentEquation profile
      (equation.1.subst (fun index => .var (permutation index)),
       equation.2.subst (fun index => .var (permutation index))) ↔
      CoherentEquation profile equation := by
  constructor
  · rintro ⟨valuation, sort, left, right⟩
    refine ⟨fun index => valuation (permutation index), sort, ?_, ?_⟩
    · apply (evaluate_iff_formed profile _ _ sort).mp
      have equal := formed_evaluate left
      simpa only [Term.evaluate_subst, Term.evaluate] using equal
    · apply (evaluate_iff_formed profile _ _ sort).mp
      have equal := formed_evaluate right
      simpa only [Term.evaluate_subst, Term.evaluate] using equal
  · rintro ⟨valuation, sort, left, right⟩
    refine ⟨fun index => valuation (permutation.symm index), sort, ?_, ?_⟩
    · apply (evaluate_iff_formed profile _ _ sort).mp
      simpa only [Term.evaluate_subst, Term.evaluate, Equiv.symm_apply_apply] using formed_evaluate left
    · apply (evaluate_iff_formed profile _ _ sort).mp
      simpa only [Term.evaluate_subst, Term.evaluate, Equiv.symm_apply_apply] using formed_evaluate right

theorem center_rename (system : EquationSystem S) (permutation : Nat ≃ Nat) :
    center (Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.rename permutation system) = center system := by
  ext profile
  rw [mem_center_iff, mem_center_iff]
  unfold Coherent Mettapedia.OSLF.NativeTypes.SortProfiles.EquationalCenter.rename
  simp only [List.mem_map]
  constructor
  · intro coherent equation member
    exact (coherent_rename profile permutation equation).mp
      (coherent _ ⟨equation, member, rfl⟩)
  · intro coherent equation member
    obtain ⟨original, member, rfl⟩ := member
    exact (coherent_rename profile permutation original).mpr (coherent original member)

end Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence
