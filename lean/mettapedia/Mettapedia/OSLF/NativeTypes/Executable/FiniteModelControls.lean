import Mettapedia.OSLF.Framework.FiniteModelSearch
import Mettapedia.OSLF.NativeTypes.Executable.CounterAbstractions

/-!
# Controls: finite-model certificates for a counter

Verdicts are about runs through object states (`ObjectState`: no explicit substitution, closed
collections, every bound variable in scope), the states of a language; for the compiled plan,
well-sorted states are object states and stay well-sorted. The binder languages (λ, name passing,
rho) are in `FiniteModelBinderControls`.

**A counter counting down by two** (`countdown`: `counter (succ (succ n)) ~> counter n`,
`counter zero ~> halted`). The states that halt are the counters of even numerals, infinitely many
patterns: backward search over patterns never saturates and stays `unknown` at `counter 1`. Five
parity classes form a tree automaton that every rule goes down, so no odd counter halts
(`odd_cannot_halt`), and the compiled plan agrees (`compiled_one_cannot_halt`). Removing the abstract
step from even counters to `halted` makes the certificate invalid. A search over the models of the
counter's constructors on three values finds a certificate with no hand-written part
(`one_cannot_halt_by_search`); one value is too few, and no model proves that `counter 2` cannot halt.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction (rootReducts)
open Mettapedia.OSLF.Framework.FiniteModels
open Mettapedia.OSLF.Framework.BackwardSearch
open Mettapedia.OSLF.Framework.HerbrandBridge (languageSpan Goal compiled compiled_reaches_iff
  language_sorted_closed)
open Mettapedia.OSLF.Framework.GeneralCanonicalAgreement (checkRootProfile RootProfile)
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (gsltSpan)
open Mettapedia.GSLT.Core.BranchingTemporal (Scheduler)
open Mettapedia.OSLF.NativeTypes.Executable.Explored.CounterAbstractions (natSort stateSort numeral counter
  halted sorted_of_check)

/-! ## A counter counting down by two -/

def downTwo : RewriteRule :=
  { name := "DownTwo", typeContext := [("n", natSort)], premises := [],
    left := .apply "Counter" [.apply "Succ" [.apply "Succ" [.fvar "n"]]], right := .apply "Counter" [.fvar "n"] }

def crashAtZero : RewriteRule :=
  { name := "CrashAtZero", typeContext := [], premises := [], left := counter 0, right := halted }

def countdown : LanguageDef :=
  Mettapedia.OSLF.NativeTypes.Executable.Explored.CounterAbstractions.language [downTwo, crashAtZero]

inductive Parity where
  | even
  | odd
  | evenCounter
  | oddCounter
  | stopped
  | junk
  deriving DecidableEq, Repr

/-- Numerals by parity, counters by the parity of their count: a tree automaton. -/
def parityModel : FiniteModel Parity where
  junk := .junk
  lam _ := .junk
  operation
    | "Zero", [] => .even
    | "Succ", [.even] => .odd
    | "Succ", [.odd] => .even
    | "Counter", [.even] => .evenCounter
    | "Counter", [.odd] => .oddCounter
    | "Halted", [] => .stopped
    | _, _ => .junk

def parityElements : List Parity := [.even, .odd, .evenCounter, .oddCounter, .stopped, .junk]

theorem parity_complete (entry : Parity) : entry ∈ parityElements := by cases entry <;> simp [parityElements]

/-- Only an even counter may stop. -/
def parityCertificate : Certificate Parity where
  elements := parityElements
  complete := parity_complete
  model := parityModel
  below first second := first == second || (first == .evenCounter && second == .stopped)

def isStopped (entry : Parity) : Bool := entry == .stopped

theorem parity_valid : parityCertificate.valid countdown = true := by decide +kernel

theorem halted_accepted : [halted].all (parityCertificate.goalCheck isStopped) = true := by decide +kernel

theorem value_numeral : ∀ count, value parityModel (numeral count) = if count % 2 = 0 then .even else .odd
  | 0 => rfl
  | count + 1 => by
    have earlier := value_numeral count
    unfold value at earlier ⊢
    simp only [numeral, eval, evalList] at earlier ⊢
    rw [earlier]
    rcases Nat.mod_two_eq_zero_or_one count with even | odd
    · rw [if_pos even, if_neg (by omega)]
      rfl
    · rw [if_neg (by omega), if_pos (by omega)]
      rfl

/-- **No odd counter halts**, for every count. -/
theorem odd_cannot_halt (count : ℕ) :
    ¬ Reaches (between (languageSpan countdown) ObjectState) (Goal [halted]) (counter (2 * count + 1)) := by
  apply parityCertificate.cannotReach_of_valid parity_valid halted_accepted
  have counterValue : value parityModel (counter (2 * count + 1)) = .oddCounter := by
    have inner := value_numeral (2 * count + 1)
    rw [if_neg (by omega)] at inner
    unfold value at inner ⊢
    simp only [counter, eval, evalList] at inner ⊢
    rw [inner]
    rfl
  show parityCertificate.apart isStopped (value parityModel _) = true
  rw [counterValue]
  decide

theorem countdown_profile : checkRootProfile countdown stateSort = true := by cbv

/-- **The compiled plan agrees**: `counter 1` never halts under GSLT → MeTTa's root plan. -/
theorem compiled_one_cannot_halt :
    ¬ Reaches (gsltSpan (compiled countdown stateSort)) (Goal [halted]) (counter 1) := fun reaches =>
  have profile := RootProfile.of_check countdown_profile
  have start : Mettapedia.OSLF.Framework.HerbrandBridge.Sorted countdown stateSort (counter 1) :=
    sorted_of_check (by cbv)
  odd_cannot_halt 0 (reaches_between_mono (fun _ sorted => ⟨sorted.2.2.2, sorted.2.2.1⟩)
    (reaches_between_of_closed (language_sorted_closed profile) start
      ((compiled_reaches_iff profile start).mp reaches)))

-- Backward search over patterns finds `counter 0`, `counter 2`, `counter 4`, … and never saturates.
#guard Mettapedia.OSLF.Framework.HerbrandBridge.answer countdown [halted] Scheduler.breadthFirst 4 (counter 1) ==
  .unknown
#guard Mettapedia.OSLF.Framework.HerbrandBridge.answer countdown [halted] Scheduler.breadthFirst 12 (counter 1) ==
  .unknown
#guard Mettapedia.OSLF.Framework.HerbrandBridge.answer countdown [halted] Scheduler.breadthFirst 6 (counter 4) ==
  .reaches
-- The certificate says nothing about even counters, which do halt.
#guard !parityCertificate.cannotReach countdown [halted] isStopped (counter 4)

/-- Without the abstract step from even counters to `halted`, the crash rule does not go down. -/
def strictCertificate : Certificate Parity := { parityCertificate with below := fun first second => first == second }

theorem strict_invalid : strictCertificate.valid countdown = false := by decide +kernel

/-! ### The certificate found by search -/

def counterSignature : Signature :=
  [.operation "Zero" 0, .operation "Succ" 1, .operation "Counter" 1, .operation "Halted" 0]

def threeValues : List (Fin 3) := [0, 1, 2]
theorem threeValues_complete (entry : Fin 3) : entry ∈ threeValues := by fin_cases entry <;> simp [threeValues]

def oneValue : List (Fin 1) := [0]
theorem oneValue_complete (entry : Fin 1) : entry ∈ oneValue := by fin_cases entry; simp [oneValue]

/-- **No certificate written by hand**: the kernel enumerates the models of the counter's constructors
over three values, computes each one's preorder from the rules, and stops at the first that proves the
verdict. -/
theorem one_cannot_halt_by_search :
    ¬ Reaches (between (languageSpan countdown) ObjectState) (Goal [halted]) (counter 1) :=
  cannotReachBySearch_of_check (elements := threeValues) (complete := threeValues_complete) (junk := 2)
    (signature := counterSignature) (by decide +kernel)

-- One value cannot separate a counter from `halted`.
theorem one_value_too_few :
    cannotReachBySearch oneValue oneValue_complete 0 counterSignature countdown [halted] (counter 1) = false := by
  decide +kernel

-- No model proves a false verdict: `counter 2` does halt, and every one of the 6561 models fails.
#guard !cannotReachBySearch threeValues threeValues_complete 2 counterSignature countdown [halted] (counter 2)

end Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls
