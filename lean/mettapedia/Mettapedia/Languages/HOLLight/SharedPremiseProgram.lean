import Mettapedia.Languages.HOLLight.SharedPremiseExecution
import Mettapedia.Languages.HOLLight.CachedClaimCheckingProgram
import Mettapedia.Computability.RetainedWordProgram
import Mettapedia.Computability.StackMachineDispatchProgram

/-!
# Executable instructions for the original saved-premise compiler branch

The computed instruction table, input initialization and transition agree
with the unchanged saved-premise machine. The original cached claim checker
is reused as an instruction subroutine; the caller adds only physical input
retention, status projection and original root resolution.

The counted evaluator takes fuel and snapshot period as parameters. Its
complete, duplicate-free stack enumeration earns configuration-preserving
snapshots and an exact original transition-count theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option allowUnsafeReducibility true

namespace Mettapedia.Languages.HOLLight.SharedPremiseProgram
open Turing Mettapedia.Computability
open Mettapedia.Computability.WordTemplateMachine
open Mettapedia.OSLF.Binding.WireCodec.Binary
open SharedPremiseExecution
abbrev Alphabet := SharedPremiseExecution.Alphabet
abbrev target := SharedPremiseExecution.machine

attribute [local reducible] FinTM2.Cfg SharedPremiseExecution.machine rootMachine savedMachine testedMachine guardedMachine
  CachedClaimChecking.machine CachedClaimChecking.lookupMachine CachedClaimChecking.retainedMachine
  CachedClaimChecking.checkMachine CachedClaimChecking.successMachine CachedClaimChecking.guardedMachine
  StackMachineComposition.machine StackMachineComposition.Dispatch.machine
  StackMachineComposition.leftKey StackMachineComposition.rightKey
  RetainedWordExecution.machine RetainedWordExecution.statement
  Indexed.machine Indexed.Alphabet WordHomomorphismMachine.machine
  Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.machine

attribute [local reducible]
  RetainedWordExecution.WithOutput.Framed.machine RetainedWordExecution.WithOutput.Framed.taggedMachine
  RetainedWordExecution.WithOutput.Framed.retainedMachine RetainedWordExecution.WithOutput.Framed.untag
  RetainedWordExecution.WithOutput.machine
  FramedFieldSelection.machine WordTemplateMachine.machine WordEqualityMachine.machine
  Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.ChainedCache.machine
  Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.ChainedCache.firstMachine
  Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.ChainedCache.secondMachine
  Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.ChainedCache.guardedMachine
  Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.ChainedCache.preparedMachine
  Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.ChainedCache.taggedMachine
  Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.ChainedCache.retainedMachine
  Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.EncodedTable.decodedMachine
  Mettapedia.OSLF.Binding.WireCodec.Binary.Triples.Recovery.machine

attribute [local reducible]
  ClaimCheckingMachine.machine ClaimCheckingMachine.guardedMachine ClaimCheckingMachine.successMachine
  ClaimCheckingMachine.preparedMachine ClaimCheckingMachine.claimedMachine ClaimCheckingMachine.selectedClaimMachine
  ClaimCheckingMachine.claimMachine ClaimCheckingMachine.sequentMachine ClaimCheckingMachine.selectedSequentMachine
  ClaimCheckingMachine.projectedMachine ClaimCheckingMachine.Comparison.machine ClaimCheckingMachine.Comparison.compareMachine
  SourceQuantifierEmission.renderMachine SourceQuantifierEmission.rawMachine SourceQuantifierEmission.stripStatus
  SourceQuantifierEmission.rawIdentity SourceQuantifierEmission.selectedScopeMachine SourceQuantifierEmission.savedScopeMachine
  SourceQuantifierEmission.admissionMachine
  Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.machine
  Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.PrefixField.machine
  Mettapedia.GSLT.LanguageDef.PatternScopeExecution.OriginalAdmission.machine
  Mettapedia.GSLT.LanguageDef.PatternScopeExecution.OriginalAdmission.projectedMachine
  Mettapedia.GSLT.LanguageDef.PatternScopeExecution.VisitorAdapter.machine
  Mettapedia.GSLT.LanguageDef.PatternScopeExecution.Binary.machine
  Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.machine
  ArgumentRenderingMachine.Full.machine ArgumentRenderingMachine.Routing.Pipeline.machine
  ArgumentRenderingMachine.Routing.Traversal.machine ArgumentRenderingMachine.Routing.machine
  Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Hooks.Execution.machine ArgumentRenderingMachine.Execution.machine

local instance : Fintype (CachedClaimChecking.machine.Γ CachedClaimChecking.machine.k₁) := inferInstanceAs (Fintype Bool)
local instance : Inhabited (CachedClaimChecking.machine.Γ CachedClaimChecking.machine.k₁) := inferInstanceAs (Inhabited Bool)
local instance : Inhabited (CachedClaimChecking.machine.Γ CachedClaimChecking.machine.k₀) := inferInstanceAs (Inhabited (Option Alphabet))
local instance : Fintype (savedMachine.Γ savedMachine.k₁) := inferInstanceAs (Fintype (Option Alphabet ⊕ Bool))
local instance : Inhabited (savedMachine.Γ savedMachine.k₁) := inferInstanceAs (Inhabited (Option Alphabet ⊕ Bool))

local instance : Fintype Alphabet := ClaimCheckingProgram.alphabet0Finite
local instance : Inhabited Alphabet := ClaimCheckingProgram.alphabet0Default
local instance : Fintype (Option Alphabet) := ClaimCheckingProgram.alphabet1Finite
local instance : Inhabited (Option Alphabet) := ClaimCheckingProgram.alphabet1Default
local instance : Fintype (Option Alphabet ⊕ Bool) := ClaimCheckingProgram.alphabet4Finite
local instance : Inhabited (Option Alphabet ⊕ Bool) := ClaimCheckingProgram.alphabet4Default

private theorem sequence_exact (first second : FinTM2)
    [Fintype (first.Γ first.k₁)] [Inhabited (first.Γ first.k₁)]
    (bridge : first.Γ first.k₁ ≃ second.Γ second.k₀)
    {firstBody : first.Λ → first.Stmt} {secondBody : second.Λ → second.Stmt}
    (firstSame : firstBody = first.m) (secondSame : secondBody = second.m) :
    StackMachineComposition.Programs.body first.k₁ second.k₀ second.main default bridge firstBody secondBody =
      (StackMachineComposition.machine first second bridge).m := by
  cases firstSame
  cases secondSame
  exact StackMachineComposition.body_eq first second bridge

def rootSelectorTable : {body : (Indexed.machine rootSelector).Λ → (Indexed.machine rootSelector).Stmt //
    body = (Indexed.machine rootSelector).m} := by extract_rule_program (Indexed.machine rootSelector).m
def rootSelectorBody := rootSelectorTable.val
theorem rootSelectorBody_exact : rootSelectorBody = (Indexed.machine rootSelector).m := rootSelectorTable.property
def rootBody : rootMachine.Λ → rootMachine.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body
    (Indexed.machine rootSelector).k₁ Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.machine.k₀
    Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.machine.main (0 : Alphabet) (Equiv.refl Alphabet)
    rootSelectorBody Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.machine.m)
theorem rootBody_exact : rootBody = rootMachine.m :=
  sequence_exact (Indexed.machine rootSelector) Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.machine
    (Equiv.refl Alphabet) rootSelectorBody_exact rfl

def savedBody : savedMachine.Λ → savedMachine.Stmt :=
  RetainedWordExecution.Programs.body CachedClaimCheckingProgram.inputKey CachedClaimCheckingProgram.resultKey
    CachedClaimCheckingProgram.registers CachedClaimCheckingProgram.mainLabel (none : Option Alphabet) false
    (fun accepted => accepted) CachedClaimCheckingProgram.body
theorem savedBody_exact : savedBody = savedMachine.m := by
  unfold savedBody
  rw [CachedClaimCheckingProgram.body_exact]
  exact RetainedWordExecution.Programs.body_eq CachedClaimChecking.machine (fun accepted => accepted)

def projectionTable : {body : (WordHomomorphismMachine.machine SourceQuantifierEmission.project).Λ →
    (WordHomomorphismMachine.machine SourceQuantifierEmission.project).Stmt //
    body = (WordHomomorphismMachine.machine SourceQuantifierEmission.project).m} := by
  extract_rule_program (WordHomomorphismMachine.machine SourceQuantifierEmission.project).m
def projectionBody := projectionTable.val
theorem projectionBody_exact : projectionBody = (WordHomomorphismMachine.machine SourceQuantifierEmission.project).m := projectionTable.property
def testedBody : testedMachine.Λ → testedMachine.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body savedMachine.k₁
    (WordHomomorphismMachine.machine SourceQuantifierEmission.project).k₀
    (WordHomomorphismMachine.machine SourceQuantifierEmission.project).main (default : savedMachine.Γ savedMachine.k₁)
    (Equiv.refl (Option Alphabet ⊕ Bool)) savedBody projectionBody)
theorem testedBody_exact : testedBody = testedMachine.m :=
  sequence_exact savedMachine (WordHomomorphismMachine.machine SourceQuantifierEmission.project)
    (Equiv.refl (Option Alphabet ⊕ Bool)) savedBody_exact projectionBody_exact

def guardedBody : guardedMachine.Λ → guardedMachine.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Dispatch.Programs.body rootMachine.k₀ rootMachine.k₁
    rootMachine.initialState rootMachine.main SourceQuantifierEmission.accept [(0 : Alphabet)] rootBody)
theorem guardedBody_exact : guardedBody = guardedMachine.m := by
  unfold guardedBody
  rw [rootBody_exact]
  exact (StackMachineComposition.Dispatch.Programs.body_eq rootMachine SourceQuantifierEmission.accept [(0 : Alphabet)]).symm

def body : target.Λ → target.Stmt := by
  claim_program_literal_endpoints (StackMachineComposition.Programs.body testedMachine.k₁ guardedMachine.k₀
    guardedMachine.main (none : Option Alphabet) (Equiv.refl (Option Alphabet)) testedBody guardedBody)
theorem body_exact : body = target.m := sequence_exact testedMachine guardedMachine (Equiv.refl (Option Alphabet)) testedBody_exact guardedBody_exact

def keyEquality : DecidableEq target.K := by claim_program_key_equality
local instance : DecidableEq target.K := keyEquality
def registerEquality : DecidableEq target.σ := by claim_program_key_equality
def step := @TM2.step target.K target.Γ target.Λ target.σ keyEquality body
theorem step_exact : step = target.step := by
  unfold step
  rw [show keyEquality = target.kDecidableEq from Subsingleton.elim _ _, body_exact]
  rfl
def inputKey : target.K := by normalize_rule_program target.k₀
def resultKey : target.K := by normalize_rule_program target.k₁
def registers : target.σ := by normalize_rule_program target.initialState
def mainLabel : target.Λ := by normalize_rule_program target.main
def initial (word : List (Option Alphabet)) : target.Cfg where
  l := some mainLabel
  var := registers
  stk := Function.update (fun _ => []) inputKey word
theorem initial_exact (word : List (Option Alphabet)) : initial word = initList target word := by
  simp only [initial, initList]
  congr 1
  funext key
  have address : inputKey = target.k₀ := rfl
  simp only [Function.update, address]
  by_cases same : key = target.k₀
  · subst key; simp
  · simp [same]

private def added {Key : Type} (keys : List Key) := none :: keys.map some
private def joined {Left Right : Type} (left : List Left) (right : List Right) :=
  none :: (left.map (some ∘ Sum.inl) ++ right.map (some ∘ Sum.inr))
private theorem added_all {Key : Type} (keys : List Key) (complete : ∀ key, key ∈ keys) :
    ∀ key : Option Key, key ∈ added keys := by
  intro key
  cases key <;> simp [added, complete]
private theorem joined_all {Left Right : Type} (left : List Left) (right : List Right)
    (leftComplete : ∀ key, key ∈ left) (rightComplete : ∀ key, key ∈ right) :
    ∀ key : Option (Left ⊕ Right), key ∈ joined left right := by
  intro key
  cases key with
  | none => simp [joined]
  | some key => cases key <;> simp [joined, leftComplete, rightComplete]
private theorem added_nodup {Key : Type} {keys : List Key} (unique : keys.Nodup) : (added keys).Nodup := by
  rw [added, List.nodup_cons]
  exact ⟨by simp, unique.map (Option.some_injective Key)⟩
private theorem joined_nodup {Left Right : Type} {left : List Left} {right : List Right}
    (leftUnique : left.Nodup) (rightUnique : right.Nodup) : (joined left right).Nodup := by
  rw [joined, List.nodup_cons]
  refine ⟨by simp, List.Nodup.append ?_ ?_ ?_⟩
  · exact leftUnique.map ((Option.some_injective (Left ⊕ Right)).comp Sum.inl_injective)
  · exact rightUnique.map ((Option.some_injective (Left ⊕ Right)).comp Sum.inr_injective)
  · rw [List.disjoint_left]
    intro key leftMember rightMember
    obtain ⟨first, _, firstSame⟩ := List.mem_map.mp leftMember
    obtain ⟨second, _, secondSame⟩ := List.mem_map.mp rightMember
    simp at firstSame secondSame
    rw [← firstSame] at secondSame
    cases secondSame
private def homKeys : List WordHomomorphismMachine.Stack := [.input, .output, .result]
private def indexedKeys : List Indexed.Stack := [.input, .temporary, .output, .result]
private def referenceKeys : List Mettapedia.GSLT.LanguageDef.SharedReferenceExecution.Stack := [.input, .query, .temporary, .result]
def keys : List target.K := joined (joined (added (added (added CachedClaimCheckingProgram.keys))) homKeys)
  (joined indexedKeys referenceKeys)
local instance : BEq target.K := ⟨fun a b => decide (a = b)⟩
local instance : LawfulBEq target.K where
  eq_of_beq h := of_decide_eq_true h
  rfl := by intro a; exact decide_eq_true rfl
noncomputable local instance : Fintype target.K := target.kFin
theorem all_keys : ∀ key : target.K, key ∈ keys := by
  apply joined_all
  · apply joined_all
    · exact added_all _ (added_all _ (added_all _ CachedClaimCheckingProgram.all_keys))
    · intro key; cases key <;> simp [homKeys]
  · apply joined_all
    · intro key; cases key <;> simp [indexedKeys]
    · intro key; cases key <;> simp [referenceKeys]
theorem keys_nodup : keys.Nodup := by
  apply joined_nodup
  · apply joined_nodup
    · exact added_nodup (added_nodup (added_nodup CachedClaimCheckingProgram.keys_nodup))
    · decide +kernel
  · apply joined_nodup <;> decide +kernel
open StackMachineRegisters.StackSnapshot
def refresh (state : target.Cfg) : target.Cfg :=
  {state with stk := lookup target.Γ (snapshot target.Γ state.stk keys)}
theorem refresh_exact (state : target.Cfg) : refresh state = state := by
  cases state with
  | mk label registers contents =>
    dsimp only [refresh]
    congr 1
    funext key
    exact lookup_snapshot target.Γ contents keys key (all_keys key)

def periodicRefresh (period used : Nat) (state : target.Cfg) := if used % period = 0 then refresh state else state
theorem periodicRefresh_exact (period used : Nat) (state : target.Cfg) : periodicRefresh period used state = state := by
  unfold periodicRefresh
  split
  · exact refresh_exact state
  · rfl

def run (period : Nat) : Nat → Nat → target.Cfg → Option (Nat × target.Cfg)
  | 0, _, _ => none
  | fuel + 1, used, state =>
    if state.l.isNone then some (used, state)
    else match step state with
      | none => none
      | some next => run period fuel (used + 1) (periodicRefresh period (used + 1) next)

theorem run_actual (period fuel used : Nat) (before : target.Cfg)
    {count : Nat} {after : target.Cfg} (finished : run period fuel used before = some (count, after)) :
    used ≤ count ∧
      (∃ path : StateTransition.EvalsToInTime target.step before (some after) (count-used),
        path.steps = count-used) ∧ after.l = none := by
  induction fuel generalizing used before with
  | zero => cases finished
  | succ fuel ih =>
    simp only [run] at finished
    split at finished
    · rename_i halted
      have pair := Option.some.inj finished
      have countSame := congrArg Prod.fst pair
      have stateSame := congrArg Prod.snd pair
      change used = count at countSame
      change before = after at stateSame
      subst count
      subst after
      refine ⟨le_rfl, ?_, Option.isNone_iff_eq_none.mp halted⟩
      rw [Nat.sub_self]
      exact ⟨StateTransition.EvalsToInTime.refl target.step before, rfl⟩
    · cases advanced : step before with
      | none => simp only [advanced, reduceCtorEq] at finished
      | some next =>
        simp only [advanced] at finished
        rw [periodicRefresh_exact] at finished
        obtain ⟨countBound, ⟨tail, tailCount⟩, stopped⟩ := ih (used + 1) next finished
        have original : target.step before = some next := by rw [← step_exact]; exact advanced
        let first : StateTransition.EvalsToInTime target.step before (some next) 1 :=
          ⟨⟨1, by change (some before).bind target.step = some next; exact original⟩, le_rfl⟩
        have relative : count-used = (count-(used+1))+1 := by omega
        refine ⟨by omega, ?_, stopped⟩
        rw [relative]
        refine ⟨StateTransition.EvalsToInTime.trans target.step 1 (count-(used+1)) before next (some after) first tail, ?_⟩
        change tail.steps+first.steps = (count-(used+1))+1
        rw [tailCount]

end Mettapedia.Languages.HOLLight.SharedPremiseProgram
