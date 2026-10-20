import Mettapedia.Logic.ModalQuantaleSemantics
import Mettapedia.GSLT.LanguageDef.CertificateGSLTMuCalculusBoundary
import Mettapedia.OSLF.NativeTypes.Decision.FiniteFixedPoints

/-!
# Finite execution of the existing modal mu-calculus

This strategy consumes `ModalMuCalculus.Formula` and its existing recursive
positivity gate. Its finite adjacency is certified against an independently
given transition system. Formula variables are represented by finite sets;
nested fixed points use the finite-carrier iteration theorem. The ordinary
box here quantifies over outgoing transitions of the supplied labelled system.
An incoming modality requires a separately justified reversed relation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Decision.FiniteMuCalculus

open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.Logic.ModalQuantaleSemantics.Boolean
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary
open Reference.Core

universe u v
variable {State : Type u} {Action : Type v}

/-- Exact finite successors, including the absence of omitted transitions. -/
structure Model (lts : LTS State Action) where
  successors : State → Action → Finset State
  successors_exact : ∀ source action target,
    target ∈ successors source action ↔ lts.trans source action target

abbrev Environment (State : Type u) (n : Nat) := Fin n → Finset State

def Environment.meaning {n : Nat} (environment : Environment State n) : Env State n :=
  fun index => ↑(environment index)

def Environment.extend {n : Nat} (environment : Environment State n) (states : Finset State) :
    Environment State (n + 1) :=
  fun index => if zero : index.val = 0 then states else environment ⟨index.val - 1, by omega⟩

theorem Environment.meaning_extend {n : Nat} (environment : Environment State n)
    (states : Finset State) :
    (environment.extend states).meaning = environment.meaning.extend (↑states : Set State) := by
  funext index
  unfold meaning extend Env.extend
  split <;> rfl

variable [Fintype State] [DecidableEq State]
variable {lts : LTS State Action} (model : Model lts)

/-- Structural evaluation on the finite carrier. No semantic proposition is
decided by classical choice. Positivity is checked by the entry point below. -/
def evaluate : {n : Nat} → Formula Action n → Environment State n → Finset State
  | _, .tt, _ => Finset.univ
  | _, .ff, _ => ∅
  | _, .var index, environment => environment index
  | _, .neg formula, environment => Finset.univ \ evaluate formula environment
  | _, .conj left right, environment => evaluate left environment ∩ evaluate right environment
  | _, .disj left right, environment => evaluate left environment ∪ evaluate right environment
  | _, .diamond action formula, environment =>
      let targets := evaluate formula environment
      Finset.univ.filter fun source => ∃ target ∈ model.successors source action, target ∈ targets
  | _, .box action formula, environment =>
      let targets := evaluate formula environment
      Finset.univ.filter fun source => ∀ target ∈ model.successors source action, target ∈ targets
  | _, .mu body, environment =>
      (fun states => evaluate body (environment.extend states))^[Fintype.card State] ∅
  | _, .nu body, environment =>
      (fun states => evaluate body (environment.extend states))^[Fintype.card State] Finset.univ

theorem evaluate_correct {n : Nat} (formula : Formula Action n)
    (admitted : fixedPointsPositive formula = true)
    (environment : Environment State n) (state : State) :
    state ∈ evaluate model formula environment ↔ satisfies lts environment.meaning formula state := by
  induction formula generalizing state with
  | tt => simp [evaluate, satisfies]
  | ff => simp [evaluate, satisfies]
  | var index => rfl
  | neg formula ih =>
      simp only [fixedPointsPositive] at admitted
      simpa only [evaluate, Finset.mem_sdiff, Finset.mem_univ, true_and, satisfies] using
        not_congr (ih admitted environment state)
  | conj left right leftIH rightIH =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at admitted
      simpa only [evaluate, Finset.mem_inter, satisfies] using
        and_congr (leftIH admitted.1 environment state) (rightIH admitted.2 environment state)
  | disj left right leftIH rightIH =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at admitted
      simpa only [evaluate, Finset.mem_union, satisfies] using
        or_congr (leftIH admitted.1 environment state) (rightIH admitted.2 environment state)
  | diamond action formula ih =>
      simp only [fixedPointsPositive] at admitted
      simp only [evaluate, Finset.mem_filter, Finset.mem_univ, true_and, satisfies,
        LTS.successors, Set.mem_ofPred_eq, model.successors_exact, ih admitted environment]
  | box action formula ih =>
      simp only [fixedPointsPositive] at admitted
      simp only [evaluate, Finset.mem_filter, Finset.mem_univ, true_and, satisfies,
        LTS.successors, Set.mem_ofPred_eq, model.successors_exact, ih admitted environment]
  | mu body ih =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at admitted
      let strategy : FiniteFixedPoints.Strategy (bodyOrderHom lts environment.meaning body admitted.1) :=
        { step := fun states => evaluate model body (environment.extend states)
          step_correct := by
            intro states
            ext target
            simpa only [Finset.mem_coe, bodyOrderHom, OrderHom.coe_mk, sat, Set.mem_ofPred_eq,
              Environment.meaning_extend] using ih admitted.2 (environment.extend states) target }
      change state ∈ strategy.lower (Fintype.card State) ↔ _
      change state ∈ (↑(strategy.lower (Fintype.card State)) : Set State) ↔ _
      rw [strategy.lower_at_card]
      exact (satisfies_mu_iff_mem_lfp lts environment.meaning body admitted.1 state).symm
  | nu body ih =>
      simp only [fixedPointsPositive, Bool.and_eq_true] at admitted
      let strategy : FiniteFixedPoints.Strategy (bodyOrderHom lts environment.meaning body admitted.1) :=
        { step := fun states => evaluate model body (environment.extend states)
          step_correct := by
            intro states
            ext target
            simpa only [Finset.mem_coe, bodyOrderHom, OrderHom.coe_mk, sat, Set.mem_ofPred_eq,
              Environment.meaning_extend] using ih admitted.2 (environment.extend states) target }
      change state ∈ strategy.upper (Fintype.card State) ↔ _
      change state ∈ (↑(strategy.upper (Fintype.card State)) : Set State) ↔ _
      rw [strategy.upper_at_card]
      exact (satisfies_nu_iff_mem_gfp lts environment.meaning body admitted.1 state).symm

theorem evaluate_eq_sat {n : Nat} (formula : Formula Action n)
    (admitted : fixedPointsPositive formula = true) (environment : Environment State n) :
    (↑(evaluate model formula environment) : Set State) = sat lts environment.meaning formula := by
  ext state
  exact evaluate_correct model formula admitted environment state

/-- A structural allowance counting recursive formula evaluations and each
fixed-point iteration. It does not price finite-set operations or adjacency
enumeration, and is not a bound on host instructions. This quantity selects the
complete strategy; no general runtime-cost theorem is asserted here. -/
def requiredBudget : {n : Nat} → Formula Action n → Nat
  | _, .tt | _, .ff | _, .var _ => 1
  | _, .neg formula | _, .diamond _ formula | _, .box _ formula =>
      1 + requiredBudget formula
  | _, .conj left right | _, .disj left right =>
      1 + requiredBudget left + requiredBudget right
  | _, .mu body | _, .nu body =>
      1 + Fintype.card State * requiredBudget body

/-- This entry point provides a coarse budget gate. It does not retain an
in-progress formula cursor or claim the finer resumption of a single operator. -/
def check {n : Nat} (formula : Formula Action n) (admitted : fixedPointsPositive formula = true)
    (environment : Environment State n) (budget : Nat) (state : State) :
    Outcome (satisfies lts environment.meaning formula state) :=
  if requiredBudget (State := State) formula ≤ budget then
    if member : state ∈ evaluate model formula environment then
      .proved ((evaluate_correct model formula admitted environment state).mp member)
    else .refuted (fun proof => member ((evaluate_correct model formula admitted environment state).mpr proof))
  else .unknown

/-- Refusal of a nonpositive binder is distinct from a negative verdict or
an incomplete computation. -/
def check? {n : Nat} (formula : Formula Action n) (environment : Environment State n)
    (budget : Nat) (state : State) :
    Option (Outcome (satisfies lts environment.meaning formula state)) :=
  if admitted : fixedPointsPositive formula = true then
    some (check model formula admitted environment budget state)
  else none

theorem check_unknown_of_budget {n : Nat} (formula : Formula Action n)
    (admitted : fixedPointsPositive formula = true) (environment : Environment State n)
    (budget : Nat) (state : State) (short : budget < requiredBudget (State := State) formula) :
    (check model formula admitted environment budget state).answer = none := by
  simp [check, Nat.not_le.mpr short, Outcome.answer]

theorem check_decided {n : Nat} (formula : Formula Action n)
    (admitted : fixedPointsPositive formula = true) (environment : Environment State n)
    (budget : Nat) (state : State) (enough : requiredBudget (State := State) formula ≤ budget) :
    (check model formula admitted environment budget state).Decided := by
  simp only [check, if_pos enough]
  split <;> simp [Outcome.Decided, Outcome.answer]

theorem check_positive_iff {n : Nat} (formula : Formula Action n)
    (admitted : fixedPointsPositive formula = true) (environment : Environment State n)
    (budget : Nat) (state : State) (enough : requiredBudget (State := State) formula ≤ budget) :
    (check model formula admitted environment budget state).answer = some true ↔
      satisfies lts environment.meaning formula state := by
  constructor
  · exact Outcome.positive _
  · intro satisfied
    have member := (evaluate_correct model formula admitted environment state).mpr satisfied
    simp [check, enough, member, Outcome.answer]

theorem check_negative_iff {n : Nat} (formula : Formula Action n)
    (admitted : fixedPointsPositive formula = true) (environment : Environment State n)
    (budget : Nat) (state : State) (enough : requiredBudget (State := State) formula ≤ budget) :
    (check model formula admitted environment budget state).answer = some false ↔
      ¬ satisfies lts environment.meaning formula state := by
  constructor
  · exact Outcome.negative _
  · intro absent
    have missing : state ∉ evaluate model formula environment :=
      fun member => absent ((evaluate_correct model formula admitted environment state).mp member)
    simp [check, enough, missing, Outcome.answer]

theorem check?_refused_iff {n : Nat} (formula : Formula Action n)
    (environment : Environment State n) (budget : Nat) (state : State) :
    check? model formula environment budget state = none ↔ fixedPointsPositive formula = false := by
  unfold check?
  split <;> simp_all

end Mettapedia.OSLF.NativeTypes.Decision.FiniteMuCalculus
