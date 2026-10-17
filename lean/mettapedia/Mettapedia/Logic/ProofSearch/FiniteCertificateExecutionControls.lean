import Mettapedia.Logic.ProofSearch.FiniteCertificateExecution

/-!
# Executed finite certificate search controls

The independent source checker proves exactly the positive Boolean claim. Its
certificate must start with the letter `1`. The finite implementation reads
that letter and drains every remaining input symbol before halting. Empty and
zero-headed candidates are genuinely refused, while the bounded enumeration
still checks later candidates in its original order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.ProofSearch.FiniteCertificateExecution.Controls

open Turing StateTransition Turing.TM2.Stmt
open Mettapedia.Computability
open Mettapedia.Computability.StackMachineComposition (oneStep)
open Mettapedia.GSLT.LanguageDef.KernelAuthority

def checker : Checker Bool (List (Fin 2)) :=
  ⟨fun claim certificate => claim && ((certificate.head?).map finTwoEquiv).getD false⟩

theorem checker_authority : checker.Authority (fun claim => claim = true) := by
  constructor
  · intro claim certificate accepted
    cases claim <;> simp_all [checker]
  · intro claim valid
    subst claim
    exact ⟨[1], rfl⟩

/-- The implementation consumes the complete candidate, including data
after an already invalid first letter, before returning the checked verdict. -/
def candidateMachine (claim : Bool) : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Bool
  main := false
  σ := Bool × Option Bool
  initialState := (false, none)
  m phase := if phase then
    pop false (fun state symbol => (state.1, symbol))
      (branch (fun state => state.2.isSome)
        (goto fun _ => true)
        (push true Prod.fst (load (fun _ => (false, none)) halt)))
    else pop false (fun _ symbol => (claim && symbol.getD false, none)) (goto fun _ => true)

attribute [local implicit_reducible] candidateMachine

def config (claim : Bool) (phase : Option Bool) (verdict : Bool) (last : Option Bool)
    (input output : List Bool) : (candidateMachine claim).Cfg where
  l := phase
  var := (verdict, last)
  stk key := if (show Bool from key) then output else input

theorem first_step (claim : Bool) (input : List Bool) :
    (candidateMachine claim).step (config claim (some false) false none input []) =
      some (config claim (some true) (claim && input.head?.getD false) none input.tail []) := by
  simp [FinTM2.step, candidateMachine, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem drain_cons (claim verdict : Bool) (last : Option Bool) (head : Bool) (tail : List Bool) :
    (candidateMachine claim).step (config claim (some true) verdict last (head :: tail) []) =
      some (config claim (some true) verdict (some head) tail []) := by
  simp [FinTM2.step, candidateMachine, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem drain_nil (claim verdict : Bool) (last : Option Bool) :
    (candidateMachine claim).step (config claim (some true) verdict last [] []) =
      some (config claim none false none [] [verdict]) := by
  simp [FinTM2.step, candidateMachine, config, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

def drain_run (claim verdict : Bool) (last : Option Bool) (input : List Bool) :
    EvalsToInTime (candidateMachine claim).step (config claim (some true) verdict last input [])
      (some (config claim none false none [] [verdict])) (input.length + 1) := by
  induction input generalizing last with
  | nil => exact oneStep (drain_nil claim verdict last)
  | cons head tail ih =>
      have first := oneStep (drain_cons claim verdict last head tail)
      have rest := ih (some head)
      have joined := EvalsToInTime.trans _ 1 (tail.length + 1) _ _ _ first rest
      simpa using joined

theorem init_eq (claim : Bool) (word : List Bool) : initList (candidateMachine claim) word =
    config claim (some false) false none word [] := by
  simp only [initList, candidateMachine, config]
  congr 1
  funext key
  cases key <;> simp

theorem halt_eq (claim : Bool) (verdict : Bool) : haltList (candidateMachine claim) [verdict] =
    config claim none false none [] [verdict] := by
  simp only [haltList, candidateMachine, config]
  congr 1

def outputs (claim : Bool) (word : List Bool) :
    TM2OutputsInTime (candidateMachine claim) word (some [claim && word.head?.getD false])
      (word.length + 2) := by
  have first := oneStep (first_step claim word)
  have rest := drain_run claim (claim && word.head?.getD false) none word.tail
  have joined := EvalsToInTime.trans _ 1 (word.tail.length + 1) _ _ _ first rest
  have relaxed : word.tail.length + 1 + 1 ≤ word.length + 2 := by
    cases word <;> simp
  change EvalsToInTime _ (initList (candidateMachine claim) _) (some (haltList (candidateMachine claim) _)) _
  rw [init_eq, halt_eq]
  exact ⟨joined.toEvalsTo, joined.steps_le_m.trans relaxed⟩

def candidateClock (certificate : List (Fin 2)) : Nat := certificate.length + 2

def candidateRun (claim : Bool) (certificate : List (Fin 2)) :
    TM2OutputsInTime (candidateMachine claim)
      (Checking.encodeCertificate (candidateMachine claim) (Equiv.refl Bool) certificate)
      (some [(Equiv.refl Bool).symm (checker.check claim certificate)]) (candidateClock certificate) := by
  have ran := outputs claim (certificate.map finTwoEquiv)
  change TM2OutputsInTime (candidateMachine claim) ((certificate.map finTwoEquiv).map id)
    (some [claim && ((certificate.head?).map finTwoEquiv).getD false]) (certificate.length + 2)
  simp only [List.map_id]
  simpa only [List.length_map, List.head?_map] using ran

noncomputable def searchRun (claim : Bool) (bound : Nat) :=
  letI : Inhabited ((candidateMachine claim).Γ (candidateMachine claim).k₀) :=
    inferInstanceAs (Inhabited Bool)
  letI : Fintype ((candidateMachine claim).Γ (candidateMachine claim).k₁) :=
    inferInstanceAs (Fintype Bool)
  Checking.search_outputs (candidateMachine claim) (Equiv.refl Bool) (Equiv.refl Bool)
    checker claim candidateClock (candidateRun claim) bound

theorem depth_zero_refused : (CertificateBounds.boundedSearch checker true 0).isSome = false := rfl

theorem depth_one_accepts : (CertificateBounds.boundedSearch checker true 1).isSome = true := rfl

theorem negative_claim_refused (bound : Nat) :
    (CertificateBounds.boundedSearch checker false bound).isSome = false := by
  have none := (CertificateBounds.boundedSearch_eq_none_iff checker false bound).mpr
    (fun _ _ => rfl)
  rw [none]
  rfl

end Mettapedia.Logic.ProofSearch.FiniteCertificateExecution.Controls
