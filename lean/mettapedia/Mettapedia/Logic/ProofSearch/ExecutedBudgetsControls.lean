import Mettapedia.Logic.ProofSearch.ExecutedBudgets
import Mettapedia.Logic.ProofSearch.SearchTransportControls

/-!
# Executed budget, refusal and unfinished-search controls

The nonidentity route executes a candidate producer, Boolean claim relocation
and an independently implemented checker, including both word handoffs.
A second authority admits the same positive claim with one certificate and
refuses another; this distinguishes certificate refusal from refutation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ProofSearch.ExecutedBudgets.Controls

open Mettapedia.GSLT.LanguageDef
open SemanticEvidence ResourceTranslation ProofSystems
open Mettapedia.Computability
open Turing Polynomial

set_option backward.isDefEq.respectTransparency false in
/-- The target control theory proves `false`; its checker really negates the
complete one-symbol encoded target claim. -/
noncomputable def flippedChecker : CheckerExecution SearchTransport.Controls.flippedAuthority
    SearchTransport.Controls.flippedEncoding where
  tm := SymbolMapMachine.machine (! · : Bool → Bool)
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time _ := 4
  outputs := by
    rintro ⟨⟨⟩, b, ⟨⟩⟩
    convert SymbolMapMachine.outputs (! · : Bool → Bool) [b] using 1 <;> rfl
  finiteAlphabet _ := inferInstanceAs (Finite Bool)

noncomputable def compiler := ExecutedTranslation.ofPolynomial SearchTransport.Controls.flipCompiler

noncomputable def whole : FinTM2 := pipeline SearchTransport.Controls.candidateProducer
  (Equiv.refl Bool) compiler SearchTransport.Controls.flipTranslation_exact flippedChecker

set_option backward.isDefEq.respectTransparency false in
noncomputable def wholeRun (b : Bool) : TM2OutputsInTime whole [b] (some [b]) 17 := by
  have run := pipeline_run SearchTransport.Controls.candidateProducer (Equiv.refl Bool)
    compiler SearchTransport.Controls.flipTranslation_exact flippedChecker [b]
    (ExecutionControls.packet b) 1 (SearchTransport.Controls.candidateRun b)
  have outputSame : ([checkPacket ExecutionControls.authority (ExecutionControls.packet b)].map
      flippedChecker.outputAlphabet.symm) = [b] := rfl
  rw [outputSame] at run
  convert run using 1 <;> first | rfl | simp [compiler, ExecutedTranslation.ofPolynomial,
    SearchTransport.Controls.flipCompiler, SearchTransport.Controls.flipRealization,
    ExecutionControls.encoding, ExecutionControls.packet,
    SearchTransport.Controls.flippedEncoding, Translation.packet,
    SearchTransport.Controls.flipTranslation, flippedChecker]

set_option maxRecDepth 4096 in
theorem wholeRun_steps (b : Bool) : (wholeRun b).steps = 17 := by
  have counted : (probe whole.step (initList whole [b]) 17).spent = 17 := by
    cases b <;> rfl
  have finished := probe_complete whole.step (initList whole [b]) (haltList whole [b])
    17 (wholeRun b) (by rfl)
  rw [finished] at counted
  exact counted

theorem whole_budget (b : Bool) (budget : Nat) :
    observe whole flippedChecker.outputAlphabet [b] budget =
      if 17 ≤ budget then some b else none := by
  have observed := observation_of_run whole flippedChecker.outputAlphabet [b] b
    (wholeRun b).toTM2Outputs budget
  simpa only [TM2OutputsInTime.toTM2Outputs, wholeRun_steps] using observed

theorem timeout_is_not_refutation :
    ExecutionControls.theory.Scope () true ∧
      observe whole flippedChecker.outputAlphabet [true] 16 = none ∧
      observe whole flippedChecker.outputAlphabet [true] 17 = some true := by
  refine ⟨rfl, ?_, ?_⟩ <;> simp [whole_budget]

theorem completed_refusal :
    observe whole flippedChecker.outputAlphabet [false] 17 = some false ∧
      (probe whole.step (initList whole [false]) 17).spent = 17 := by
  constructor
  · simp [whole_budget]
  · have finished := probe_complete whole.step (initList whole [false]) (haltList whole [false])
      17 (wholeRun false) (by rfl)
    rw [finished, wholeRun_steps]

/-- Same source claim, with independently checked certificate data. -/
def certificateAuthority : AuthorityContract ExecutionControls.theory where
  Certificate _ := Bool
  checker _ := ⟨fun claim certificate => claim && certificate⟩
  scopeAuthority _ :=
    { sound := by
        intro claim certificate accepted
        cases claim <;> cases certificate <;> simp_all [ExecutionControls.theory]
      complete := by
        intro claim accepted
        change claim = true at accepted
        subst claim
        exact ⟨true, rfl⟩ }

def certificatePacket (claim certificate : Bool) : Packet certificateAuthority :=
  ⟨(), claim, certificate⟩

def certificateEncoding : Computability.Encoding (Packet certificateAuthority) Bool where
  encode packet := [packet.2.1, packet.2.2]
  decode
    | [claim, certificate] => some (certificatePacket claim certificate)
    | _ => none
  decode_encode := by rintro ⟨⟨⟩, claim, certificate⟩; rfl

/-- Two actual transitions read both input fields and emit the original
checker result. The halt leaves all other stacks and registers empty. -/
def certificateMachine : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := true
  Γ _ := Bool
  Λ := Bool
  main := false
  σ := Option Bool
  initialState := none
  m
    | false => .pop false (fun _ value => value) (.goto (fun _ => true))
    | true => .pop false (fun claim certificate => some (claim.getD false && certificate.getD false))
        (.push true (fun result => result.getD false) (.load (fun _ => none) .halt))

set_option backward.isDefEq.respectTransparency false in
def certificateChecker : CheckerExecution certificateAuthority certificateEncoding where
  tm := certificateMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time _ := 2
  outputs := by
    rintro ⟨⟨⟩, claim, certificate⟩
    refine ⟨⟨2, ?_⟩, le_rfl⟩
    cases claim <;> cases certificate
    all_goals
      apply congrArg some
      change (⟨none, none, _⟩ : TM2.Cfg (fun _ : Bool => Bool) Bool (Option Bool)) =
        ⟨none, none, _⟩
      congr 1
      funext key
      cases key <;> rfl
  finiteAlphabet _ := inferInstanceAs (Finite Bool)

/-- Refusing a completed candidate can coexist with an accepted certificate
and a positive independently authored scope at exactly the same claim. -/
theorem refused_certificate_not_refutation :
    ExecutionControls.theory.Scope () true ∧
      observe certificateMachine certificateChecker.outputAlphabet [true, false] 2 = some false ∧
      observe certificateMachine certificateChecker.outputAlphabet [true, true] 2 = some true := by
  exact ⟨rfl, rfl, rfl⟩

theorem unfinished_certificate_is_not_refusal :
    observe certificateMachine certificateChecker.outputAlphabet [true, false] 1 = none := rfl

end Mettapedia.Logic.ProofSearch.ExecutedBudgets.Controls
