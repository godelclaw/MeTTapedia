import Mettapedia.OSLF.NativeTypes.Executable.FiniteModelKripke
import Mettapedia.OSLF.NativeTypes.Executable.ContextualControls

/-!
# Controls: certificates refute native formulas

A certificate is a finite Kripke model: its preorder is a finite span, and the value map is a
simulation into it. The finite model checker then refutes formulas without negation and boxes, and
proves formulas without negation and diamonds.

- **Order.** A level that only rises (`Low ~> Mid ~> High`) reaches `Mid` and reaches `High`
  (`low_reaches_mid`, `low_reaches_high`), so neither reachability verdict applies. Reaching `High`
  and afterwards `Mid` is refuted (`low_never_high_then_mid`).
- **The past.** No ancestor of `Mid` is `High` (`mid_has_no_high_ancestor`), and every ancestor of
  `Mid` is below `High` (`mid_ancestors_below_high`).
- **Invariants.** Every state reached from the λ term `twice` is clean, with β at the root
  (`twice_always_clean`) and with β anywhere (`always_clean_under_full_beta`).
- **One direction each.** `High` cannot step (`high_stuck`, `high_no_step`), yet its value can, since the
  preorder is reflexive. So the certificate neither refutes "some step" there (`high_step_not_refuted`)
  nor proves "no step" (`high_no_step_not_proved`).
- **Reachability is an instance.** At `μ X. dirty ∨ ◇ X`, the formula verdicts agree with the
  reachability verdicts of the λ controls, with β at the root and with β anywhere
  (`clean_never_errs_as_formula`, `clean_stays_clean_as_formula`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction (rootReducts)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.OSLF.Framework.FiniteModels
open Mettapedia.OSLF.Framework.BackwardSearch
open Mettapedia.OSLF.Framework.HerbrandBridge (languageSpan)
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.OSLF.NativeTypes.Semantics.ModalFormula
open Mettapedia.OSLF.NativeTypes.Decision

/-! ## A level that only rises -/

def levelTerms : List GrammarRule :=
  ["Low", "Mid", "High"].map fun label =>
    { label := label, category := "Phase", params := [], syntaxPattern := [.terminal label] }

/-- A rule that rewrites one constant to another. -/
def rise (source target : String) : RewriteRule :=
  { name := source ++ target, typeContext := [], premises := [], left := .apply source [],
    right := .apply target [] }

def levels : LanguageDef :=
  { name := "Levels", types := ["Phase"], terms := levelTerms, equations := [],
    rewrites := [rise "Low" "Mid", rise "Mid" "High"] }

def low : Pattern := .apply "Low" []
def mid : Pattern := .apply "Mid" []
def high : Pattern := .apply "High" []

#guard rootReducts levels low == [mid]
#guard rootReducts levels mid == [high]
#guard rootReducts levels high == []

inductive Level where
  | low
  | mid
  | high
  deriving DecidableEq, Repr

instance : Fintype Level where
  elems := {.low, .mid, .high}
  complete entry := by cases entry <;> decide

def Level.rank : Level → ℕ
  | .low => 0
  | .mid => 1
  | .high => 2

def levelModel : FiniteModel Level where
  junk := .low
  lam _ := .low
  operation
    | "Mid", [] => .mid
    | "High", [] => .high
    | _, _ => .low

/-- A level never falls. -/
def levelCertificate : Certificate Level where
  elements := [.low, .mid, .high]
  complete entry := by cases entry <;> simp
  model := levelModel
  below first second := decide (first.rank ≤ second.rank)

theorem levels_valid : levelCertificate.valid levels = true := by decide +kernel

/-- The runs of the levels through object states. -/
abbrev levelRuns : Mettapedia.OSLF.Framework.DerivedModalities.ReductionSpan Pattern :=
  between (languageSpan levels) ObjectState

/-- One root step of the levels between object states. -/
def levelStep (source target : Pattern) (member : target ∈ rootReducts levels source)
    (sourceObject : ObjectState source) (targetObject : ObjectState target) : levelRuns.Edge :=
  ⟨⟨(source, target), member⟩, sourceObject, targetObject⟩

theorem low_reaches_mid : Reaches levelRuns (· = mid) low :=
  Reaches.step (levelStep low mid (by decide +kernel) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩) (Reaches.goal rfl)

theorem low_reaches_high : Reaches levelRuns (· = high) low :=
  Reaches.step (levelStep low mid (by decide +kernel) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩)
    (Reaches.step (levelStep mid high (by decide +kernel) ⟨rfl, rfl⟩ ⟨rfl, rfl⟩) (Reaches.goal rfl))

-- Neither reachability verdict applies at `Low`.
#guard !levelCertificate.cannotReachAccepted levels (· == .high) low
#guard !levelCertificate.cannotReachAccepted levels (· == .mid) low

/-- Atom 0 is `High`, atom 1 is `Mid`. -/
def highMid : Fin 2 → List Pattern := ![[high], [mid]]

def highMidValues : FiniteMuCalculus.Environment Level 2 := ![{.high}, {.mid}]

/-- `μ X. (high ∧ μ Y. (mid ∨ ◇ Y)) ∨ ◇ X`: reach `High`, and from there reach `Mid`. -/
def highThenMid : Formula Traversal 2 :=
  .mu (.disj (.conj (.var 1) (.mu (.disj (.var 3) (.diamond .future (.var 0))))) (.diamond .future (.var 0)))

/-- **`Low` never reaches `High` and afterwards `Mid`.** -/
theorem low_never_high_then_mid :
    ¬ satisfies (transitionSystem levelRuns) (Certificate.goalEnv highMid) highThenMid low :=
  levelCertificate.refutesGoals_of_check (environment := highMidValues) (by decide +kernel)

/-- `μ X. high ∨ ◇⁻ X`: some ancestor is `High`. -/
def highAncestor : Formula Traversal 1 := .mu (.disj (.var 1) (.diamond .past (.var 0)))

/-- **No ancestor of `Mid` is `High`.** -/
theorem mid_has_no_high_ancestor : ¬ satisfies (transitionSystem levelRuns) (fun _ => {high}) highAncestor mid :=
  levelCertificate.not_satisfies_of_value (Certificate.rootGoesDown levels_valid) rfl
    (environment := fun _ => {.high})
    (fun _ state member => by
      obtain rfl : state = high := member
      decide)
    (by decide +kernel)

/-- `◇ ⊤`: some step. -/
def canStep : Formula Traversal 0 := .diamond .future .tt

theorem high_stuck : ¬ satisfies (transitionSystem levelRuns) Env.empty canStep high := by
  rintro ⟨_, ⟨⟨⟨⟨source, _⟩, member⟩, _⟩, starts, _⟩, _⟩
  change source = high at starts
  subst starts
  have empty : rootReducts levels high = [] := by decide +kernel
  simp [empty] at member

/-- **The certificate is silent at `High`**: its value can step, by reflexivity. -/
theorem high_step_not_refuted : levelCertificate.refutes levels canStep Fin.elim0 high = false := by
  decide +kernel

/-- `□ ⊥`: no step. -/
def noStep : Formula Traversal 0 := .box .future .ff

theorem high_no_step : satisfies (transitionSystem levelRuns) Env.empty noStep high :=
  fun next step => high_stuck ⟨next, step, trivial⟩

/-- **The certificate does not prove it either.** -/
theorem high_no_step_not_proved : levelCertificate.proves levels noStep Fin.elim0 high = false := by
  decide +kernel

/-- `ν X. atom ∧ □⁻ X`: every ancestor satisfies the atom. -/
def alwaysBefore : Formula Traversal 1 := .nu (.conj (.var 1) (.box .past (.var 0)))

/-- The levels below `High`. -/
def belowHigh : FiniteMuCalculus.Environment Level 1 := fun _ => {.low, .mid}

/-- **Every ancestor of `Mid` has a level below `High`.** -/
theorem mid_ancestors_below_high :
    satisfies (transitionSystem levelRuns) (pullEnvironment (value levelModel) belowHigh.meaning) alwaysBefore mid :=
  levelCertificate.proves_of_check (by decide +kernel)

/-! ## Reachability is an instance -/

instance : Fintype Cleanness where
  elems := {.clean, .dirty}
  complete entry := by cases entry <;> decide

/-- **`twice` never reaches a dirty value**, as the refutation of `μ X. dirty ∨ ◇ X`. -/
theorem clean_never_errs_as_formula :
    ¬ satisfies (transitionSystem (between (languageSpan lambdaCalculus) ObjectState))
      (pullEnvironment (value cleanModel) (Certificate.accepted isDirty).meaning) reachFormula twice :=
  cleanCertificate.refutes_of_check (by decide +kernel)

/-- **Under β anywhere, a clean term never reaches a dirty value**, as the refutation of
`μ X. dirty ∨ ◇ X`, for every evaluator of the other premises that only adds bindings. -/
theorem clean_stays_clean_as_formula (base : BasePremiseEvaluator) :
    ¬ satisfies (transitionSystem (between (contextualSpan base fullLambda) ObjectState))
      (pullEnvironment (value cleanModel) (Certificate.accepted isDirty).meaning) reachFormula
      (app underBinder ok) :=
  cleanCertificate.refutesContextual_of_check (by decide +kernel) base
    (baseExtends_of_congruencesOnly (by decide +kernel) base)

/-! ## Invariants -/

/-- `ν X. atom ∧ □ X`: every state reached satisfies the atom. -/
def alwaysAfter : Formula Traversal 1 := .nu (.conj (.var 1) (.box .future (.var 0)))

/-- The clean value. -/
def cleanValues : FiniteMuCalculus.Environment Cleanness 1 := fun _ => {.clean}

/-- **Every state reached from `twice` is clean.** -/
theorem twice_always_clean :
    satisfies (transitionSystem (between (languageSpan lambdaCalculus) ObjectState))
      (pullEnvironment (value cleanModel) cleanValues.meaning) alwaysAfter twice :=
  cleanCertificate.proves_of_check (by decide +kernel)

/-- **Under β anywhere, every state reached from `(λx. (λy. y) x) ok` is clean**, for every evaluator of
the other premises that only adds bindings. -/
theorem always_clean_under_full_beta (base : BasePremiseEvaluator) :
    satisfies (transitionSystem (between (contextualSpan base fullLambda) ObjectState))
      (pullEnvironment (value cleanModel) cleanValues.meaning) alwaysAfter (app underBinder ok) :=
  cleanCertificate.provesContextual_of_check (by decide +kernel) base
    (baseExtends_of_congruencesOnly (by decide +kernel) base)

end Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls
