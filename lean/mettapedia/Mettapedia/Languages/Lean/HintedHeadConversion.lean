import Mettapedia.Languages.Lean.Lean4LeanRungOneDeltaDecision
import Mettapedia.Machines.ExecutionHints
import Mettapedia.GSLT.LanguageDef.KernelAuthority
import Mettapedia.Machines.ProductiveCoreAdapters
import Mettapedia.GSLT.Distinction.SimulationComposition

/-!
# Reproducible hints for the Lean4Lean head-reduction profile

The strategy is the existing executable beta/delta/head algorithm over a
finite definition catalog. A tick either performs that step or records that
no head step remains. Checkpoints contain the expression and terminal flag;
they never install a replacement environment or residual state.

Acceptance proves a path in the independent catalog event relation and a
head-normal endpoint. Completeness is relative to normalization by this
specified strategy. Full Lean typing, reduction under binders, recursors,
and the entire Lean definitional-equality procedure are outside this profile.
The counters are strategy ticks, not implementation heartbeats.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Lean.HintedHeadConversion

open Lean4Lean
open Lean4LeanRungOneDeltaDecision Lean4LeanRungZeroDecision
open Mettapedia.GSLT.LanguageDef KernelAuthority
open Mettapedia.Machines Mettapedia.Machines.ProductiveCoreAdapters
open Mettapedia.GSLT.Distinction.ProductiveBlocks

local instance : DecidableEq VExpr := fun left right =>
  if accepted : vExprStructEq left right = true then
    isTrue ((vExprStructEq_eq_true_iff left right).mp accepted)
  else isFalse (fun same => accepted ((vExprStructEq_eq_true_iff left right).mpr same))

structure State where
  expression : VExpr
  halted : Bool

def start (expression : VExpr) : State := ⟨expression, false⟩

def view (state : State) : VExpr × Bool := (state.expression, state.halted)

def tick (definitions : List VDefVal) (universes : Nat) (state : State) : State :=
  if state.halted then state else
    match catalogHeadStepWithReceipt? definitions universes state.expression with
    | none => ⟨state.expression, true⟩
    | some (target, _) => ⟨target, false⟩

def Step (definitions : List VDefVal) (universes : Nat) (source target : VExpr) : Prop :=
  ∃ receipt, CatalogHeadEvent definitions universes receipt source target

abbrev Steps (definitions : List VDefVal) (universes : Nat) :=
  Relation.ReflTransGen (Step definitions universes)

def HeadNormal (definitions : List VDefVal) (universes : Nat) (expression : VExpr) : Prop :=
  ∀ target, ¬ Step definitions universes expression target

variable {environment : VEnv} (catalog : DefinitionCatalog environment) (universes : Nat)

def Invariant (source : VExpr) (state : State) : Prop :=
  Steps catalog.entries universes source state.expression ∧
    (state.halted = true → HeadNormal catalog.entries universes state.expression)

theorem start_invariant (source : VExpr) : Invariant catalog universes source (start source) :=
  ⟨.refl, by simp [start]⟩

theorem tick_invariant (source : VExpr) (state : State)
    (valid : Invariant catalog universes source state) :
    Invariant catalog universes source (tick catalog.entries universes state) := by
  rcases valid with ⟨path, normal⟩
  cases halted : state.halted with
  | true => simpa [Invariant, tick, halted] using And.intro path normal
  | false =>
      cases stepped : catalogHeadStepWithReceipt? catalog.entries universes state.expression with
      | none =>
          simp only [tick, halted, Bool.false_eq_true, ↓reduceIte, stepped]
          refine ⟨path, fun _ target impossible => ?_⟩
          obtain ⟨receipt, event⟩ := impossible
          have computed := catalogHeadStepWithReceipt_complete catalog universes event
          rw [stepped] at computed
          cases computed
      | some next =>
          rcases next with ⟨target, receipt⟩
          have event := catalogHeadStepWithReceipt_sound_exact catalog universes stepped
          refine ⟨?_, ?_⟩
          · simpa [tick, halted, stepped] using path.tail (show Step catalog.entries universes state.expression target from ⟨receipt, event⟩)
          · simp [tick, halted, stepped]

theorem iterate_invariant (source : VExpr) (budget : Nat) :
    Invariant catalog universes source ((tick catalog.entries universes)^[budget] (start source)) := by
  induction budget with
  | zero => exact start_invariant catalog universes source
  | succ budget ih =>
      rw [Function.iterate_succ_apply']
      exact tick_invariant catalog universes source _ ih

def checker (definitions : List VDefVal) (universes : Nat) :
    Checker (VExpr × VExpr) (List (ExecutionHints.Checkpoint (VExpr × Bool))) where
  check claim hints := ExecutionHints.check (tick definitions universes) view
    (start claim.1, (claim.2, true)) hints

/-- Refusing a certificate does not assert that its source and target are
inequivalent. Acceptance establishes both the source path and terminal flag. -/
theorem check_sound (source target : VExpr)
    (hints : List (ExecutionHints.Checkpoint (VExpr × Bool)))
    (accepted : (checker catalog.entries universes).check (source, target) hints = true) :
    Steps catalog.entries universes source target ∧ HeadNormal catalog.entries universes target := by
  have reached := ExecutionHints.check_sound (tick catalog.entries universes) view
    (start source, (target, true)) hints accepted
  have expression := congrArg Prod.fst reached
  have halted := congrArg Prod.snd reached
  change ((tick catalog.entries universes)^[ExecutionHints.fuel hints] (start source)).expression = target at expression
  change ((tick catalog.entries universes)^[ExecutionHints.fuel hints] (start source)).halted = true at halted
  obtain ⟨path, normal⟩ := iterate_invariant catalog universes source (ExecutionHints.fuel hints)
  rw [expression] at path normal
  exact ⟨path, normal halted⟩

/-- Successful normalization by the original strategy, independently of the
checkpoint producer. It is a partial operational property. -/
def Normalizes (definitions : List VDefVal) (universes : Nat) (source target : VExpr) : Prop :=
  ∃ budget, view ((tick definitions universes)^[budget] (start source)) = (target, true)

theorem check_coverage (source target : VExpr) :
    (∃ hints, (checker catalog.entries universes).check (source, target) hints = true) ↔
      Normalizes catalog.entries universes source target := by
  constructor
  · rintro ⟨hints, accepted⟩
    exact ⟨ExecutionHints.fuel hints, ExecutionHints.check_sound _ _ _ _ accepted⟩
  · rintro ⟨budget, finished⟩
    obtain ⟨hints, _, checked⟩ :=
      (ExecutionHints.exists_check_iff (tick catalog.entries universes) view
        (start source) (target, true) budget).mpr finished
    exact ⟨hints, checked⟩

structure ConversionCertificate where
  normalForm : VExpr
  left : List (ExecutionHints.Checkpoint (VExpr × Bool))
  right : List (ExecutionHints.Checkpoint (VExpr × Bool))

def conversionCheck (definitions : List VDefVal) (universes : Nat)
    (claim : VExpr × VExpr) (certificate : ConversionCertificate) : Bool :=
  (checker definitions universes).check (claim.1, certificate.normalForm) certificate.left &&
    (checker definitions universes).check (claim.2, certificate.normalForm) certificate.right

theorem conversion_sound (claim : VExpr × VExpr) (certificate : ConversionCertificate)
    (accepted : conversionCheck catalog.entries universes claim certificate = true) :
    Steps catalog.entries universes claim.1 certificate.normalForm ∧
      Steps catalog.entries universes claim.2 certificate.normalForm ∧
      HeadNormal catalog.entries universes certificate.normalForm := by
  have both := Bool.and_eq_true_iff.mp accepted
  have left := check_sound catalog universes _ _ certificate.left both.1
  have right := check_sound catalog universes _ _ certificate.right both.2
  exact ⟨left.1, right.1, left.2⟩

theorem conversion_coverage (claim : VExpr × VExpr) :
    (∃ certificate, conversionCheck catalog.entries universes claim certificate = true) ↔
      ∃ common, Normalizes catalog.entries universes claim.1 common ∧
        Normalizes catalog.entries universes claim.2 common := by
  constructor
  · rintro ⟨certificate, accepted⟩
    have both := Bool.and_eq_true_iff.mp accepted
    exact ⟨certificate.normalForm,
      (check_coverage catalog universes _ _).mp ⟨certificate.left, both.1⟩,
      (check_coverage catalog universes _ _).mp ⟨certificate.right, both.2⟩⟩
  · rintro ⟨common, left, right⟩
    obtain ⟨leftHints, leftChecked⟩ := (check_coverage catalog universes _ _).mpr left
    obtain ⟨rightHints, rightChecked⟩ := (check_coverage catalog universes _ _).mpr right
    exact ⟨⟨common, leftHints, rightHints⟩, Bool.and_eq_true_iff.mpr ⟨leftChecked, rightChecked⟩⟩

def core (definitions : List VDefVal) (universes : Nat) : AnswerMachineCore VExpr State where
  State := State
  load := start
  step state := if state.halted then none else some (tick definitions universes state)
  answer state := if state.halted then some state else none
  answer_final := by intro state result; split <;> simp_all

def object (definitions : List VDefVal) (universes : Nat) :
    ObservedMachine (Occurrence State) State Empty :=
  ObservedMachine.of (answerMachine (core definitions universes))

theorem retainedTick_eq (definitions : List VDefVal) (universes : Nat) :
    retainedTick (core definitions universes).toMachineCore = tick definitions universes := by
  funext state
  cases halted : state.halted with
  | false => simp [retainedTick, core, halted]; rfl
  | true => simp [retainedTick, core, halted, tick]; rfl

/-- Accepted checkpoint evidence corresponds to an actual finished run of
the original head strategy, within its tick budget plus one observation. -/
theorem machine_of_checked (definitions : List VDefVal) (universes : Nat)
    (source target : VExpr) (hints : List (ExecutionHints.Checkpoint (VExpr × Bool)))
    (accepted : (checker definitions universes).check (source, target) hints = true) :
    ∃ fuel events report, fuel ≤ ExecutionHints.fuel hints + 1 ∧
      (object definitions universes).machine.run fuel (start source) = (events, .finished report) ∧
      report.expression = target ∧ report.halted = true := by
  let final := (tick definitions universes)^[ExecutionHints.fuel hints] (start source)
  have reached := ExecutionHints.check_sound (tick definitions universes) view
    (start source, (target, true)) hints accepted
  have expression : final.expression = target := congrArg Prod.fst reached
  have halted : final.halted = true := congrArg Prod.snd reached
  have observed : (core definitions universes).answer final = some final := by simp [core, halted]
  have ticks : (retainedTick (core definitions universes).toMachineCore)^[ExecutionHints.fuel hints]
      (start source) = final := by
    rw [retainedTick_eq]
    rfl
  have completed : (core definitions universes).answer
      ((retainedTick (core definitions universes).toMachineCore)^[ExecutionHints.fuel hints]
        (start source)) = some final := by
    rw [ticks]
    exact observed
  obtain ⟨fuel, events, bounded, finished⟩ := retainedTick_finished (core definitions universes)
    (ExecutionHints.fuel hints) (start source) final completed
  exact ⟨fuel, events, final, bounded, finished, expression, halted⟩

/-- Trace length is the strategy budget. The observation payloads have
additional size, and replay still executes every intervening strategy tick. -/
theorem trace_materialization (definitions : List VDefVal) (universes : Nat)
    (source target : VExpr) (budget : Nat) :
    let trace := ExecutionHints.fullTrace (tick definitions universes) view (start source) budget
    trace.length = budget ∧
      (checker definitions universes).check (source, target) trace =
        decide (view ((tick definitions universes)^[budget] (start source)) = (target, true)) := by
  exact ⟨ExecutionHints.fullTrace_length _ _ _ _, ExecutionHints.check_fullTrace _ _ _ _⟩

namespace Controls

def identity : VExpr := .lam (.sort .zero) (.bvar 0)
def betaSource : VExpr := .app identity (.sort .zero)

theorem beta_normalizes : Normalizes [] 0 betaSource (.sort .zero) := ⟨2, rfl⟩

theorem missing_terminal_inspection :
    (checker [] 0).check (betaSource, .sort .zero) [⟨1, (.sort .zero, false)⟩] = false := by decide

theorem beta_hint_accepted :
    (checker [] 0).check (betaSource, .sort .zero) [⟨2, (.sort .zero, true)⟩] = true := by decide

def selfApply : VExpr := .lam (.sort .zero) (.app (.bvar 0) (.bvar 0))
def omega : VExpr := .app selfApply selfApply

theorem omega_tick_fixed : tick [] 0 (start omega) = start omega := rfl

theorem omega_never_normalizes (target : VExpr) : ¬ Normalizes [] 0 omega target := by
  rintro ⟨budget, finished⟩
  rw [Function.iterate_fixed omega_tick_fixed] at finished
  have impossible := congrArg Prod.snd finished
  cases impossible

theorem omega_certificate_refused (target : VExpr)
    (hints : List (ExecutionHints.Checkpoint (VExpr × Bool))) :
    (checker [] 0).check (omega, target) hints = false := by
  cases accepted : (checker [] 0).check (omega, target) hints with
  | false => rfl
  | true =>
      have finished := ExecutionHints.check_sound (tick [] 0) view (start omega, (target, true)) hints accepted
      exact (omega_never_normalizes target ⟨ExecutionHints.fuel hints, finished⟩).elim

end Controls
end Mettapedia.Languages.Lean.HintedHeadConversion
