import Mettapedia.OSLF.Framework.BackwardBinders
import Mettapedia.OSLF.NativeTypes.Executable.FiniteModelBinderControls

/-!
# Controls: predecessors under β, name passing and a two-variable let

- **β** (`App (Lam (λ. body)) arg ~> body[arg]`). The states that step to `Ok` in one step are exactly
  `(λx. x) Ok` and `(λx. Ok) a` for every `a` (`steps_to_ok_iff`): the argument occurs in the result,
  or the body ignores it. At `App Ok Ok` the argument `Ok` occurs twice, so the body abstracts any
  nonempty set of its occurrences, or the whole result is the argument.
- **Name passing** (`Out x y | In x (λ. P) ~> P[y]`). The leak `Out Pub Sec` comes from four
  symbolic predecessors: the received name is the channel, the payload, the whole process, or unused.
  Every one mentions the secret, so a one-step leak needs the secret (`leak_needs_secret`, the past
  box of a finite model's native type); sending `Pub` on `Pub` does not.
- **Two variables at once** (`Let2 a b (λλ. body) ~> body[a, b]`). Nested substitutions invert one
  argument at a time; a candidate that would leave a bound variable dangling is dropped.
- **Rho** (`{x!(Q) | for (y <- x) P | rest} ~> {P[@Q/y] | rest}`). The source bag is matched modulo
  permutation and the rest is read off the result. A bag holding `Err` after one communication comes
  from a dirty bag (`err_bag_needs_dirt`); a clean result can come from a dirty bag that sends `Err`
  and drops it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction (rootReducts)
open Mettapedia.OSLF.Framework.BackwardBinders
open Mettapedia.OSLF.Framework.FiniteModels (FiniteModel value ObjectState)
open Mettapedia.OSLF.Framework.PredFiniteSufficient (lookupOrFvar)

/-! ## β -/

#guard (predecessors lambdaCalculus ok).map Family.pattern == [app (lam (.bvar 0)) ok, app (lam ok) (.fvar "argument")]

-- At `App Ok Ok`: the argument is the whole result, or `Ok` with one or both occurrences abstracted, or
-- unused.
#guard (predecessors lambdaCalculus (app ok ok)).map Family.pattern ==
  [app (lam (.bvar 0)) (app ok ok), app (lam (app (.bvar 0) (.bvar 0))) ok, app (lam (app (.bvar 0) ok)) ok,
    app (lam (app ok (.bvar 0))) ok, app (lam (app ok ok)) (.fvar "argument")]

-- Every instance does step back: `Err` as the unused argument.
#guard rootReducts lambdaCalculus (app (lam ok) err) == [ok]

theorem beta_backward : ∀ rule ∈ lambdaCalculus.rewrites, ruleBackward rule = true := by
  intro rule member
  simp only [lambdaCalculus, List.mem_singleton] at member
  subst member
  decide +kernel

theorem beta_matches_ok :
    matchBack beta.right ok = [[("body", .bvar 0), ("argument", ok)], [("body", ok)]] := by decide +kernel

theorem beta_literal : literalRule beta = true := by decide +kernel

/-- **The states that step to `Ok` in one β step**: `(λx. x) Ok`, and `(λx. Ok) a` for every `a`. -/
theorem steps_to_ok_iff {state : Pattern} (object : ObjectState state) (stateNameless : nameless state = true) :
    ok ∈ rootReducts lambdaCalculus state ↔ state = app (lam (.bvar 0)) ok ∨ ∃ argument, state = app (lam ok) argument := by
  constructor
  · intro step
    obtain ⟨⟨rule, fixed⟩, member, matches_⟩ := predecessors_complete beta_backward object step
    obtain ⟨ruleMember, _, fixedMember, _⟩ := mem_predecessors.mp member
    simp only [lambdaCalculus, List.mem_singleton] at ruleMember
    subst ruleMember
    obtain ⟨bindings, agrees, rfl⟩ := instance_of_matches beta_literal stateNameless matches_
    rw [beta_matches_ok] at fixedMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at fixedMember
    rcases fixedMember with rfl | rfl
    · left
      have body := agrees "body" (.bvar 0) (by decide)
      have argument := agrees "argument" ok (by decide)
      simp only [lookupOrFvar] at body argument
      simp [beta, applyBindings, body, argument, app, lam]
    · right
      have body := agrees "body" ok (by decide)
      simp only [lookupOrFvar] at body
      exact ⟨applyBindings bindings (.fvar "argument"), by simp [beta, applyBindings, body, app, lam]⟩
  · rintro (rfl | ⟨argument, rfl⟩)
    · decide +kernel
    · have member : (⟨beta, [("body", ok)]⟩ : Family) ∈ predecessors lambdaCalculus ok :=
        mem_predecessors.mpr ⟨by simp [lambdaCalculus], beta_backward beta (by simp [lambdaCalculus]),
          by rw [beta_matches_ok]; simp, by decide +kernel⟩
      refine predecessors_sound member (matches_of_instance member beta_literal
        ⟨[("body", ok), ("argument", argument)], fun name value found => ?_, by simp [beta, applyBindings, app, lam, ok]⟩)
      by_cases same : name = "body"
      · subst same
        simp at found
        simp [lookupOrFvar, applyBindings, ← found]
      · have different : ("body" == name) = false := beq_false_of_ne (Ne.symm same)
        simp [List.find?, different] at found

/-! ## Name passing -/

#guard namePassing.rewrites.all ruleBackward

#guard (predecessors namePassing (send pub sec)).map Family.pattern ==
  [par (send (.fvar "x") (send pub sec)) (receive (.fvar "x") (.bvar 0)),
    par (send (.fvar "x") pub) (receive (.fvar "x") (send (.bvar 0) sec)),
    par (send (.fvar "x") sec) (receive (.fvar "x") (send pub (.bvar 0))),
    par (send (.fvar "x") (.fvar "y")) (receive (.fvar "x") (send pub sec))]

-- The leaky forwarder is an instance of the third.
#guard rootReducts namePassing leakyForwarder == [send pub sec]

/-- Whether a process mentions the secret name; an input mentions it when its body does under a name
that is not the secret. -/
inductive Taint where
  | clean
  | secret
  deriving DecidableEq, Repr

def taintModel : FiniteModel Taint where
  junk := .clean
  lam body := body .clean
  operation
    | "Sec", [] => .secret
    | _, arguments => if arguments.contains .secret then .secret else .clean

def isSecret (entry : Taint) : Bool := entry == .secret

theorem comm_backward : ∀ rule ∈ namePassing.rewrites, ruleBackward rule = true := by
  intro rule member
  simp only [namePassing, List.mem_singleton] at member
  subst member
  decide +kernel

/-- **A one-step leak needs the secret**: every state that sends the secret on the public channel in
one step already mentions the secret name. -/
theorem leak_needs_secret {state : Pattern} (object : ObjectState state)
    (step : send pub sec ∈ rootReducts namePassing state) : value taintModel state = .secret := by
  have accepted := pastBox_of_check (model := taintModel) (elements := [.clean, .secret]) (fun entry => by cases entry <;> simp)
    comm_backward (accept := isSecret) (by decide +kernel) object step
  simpa [isSecret] using accepted

-- Sending the public name on the public channel needs no secret: a forwarder of `Pub` produces it.
#guard !pastBoxCheck taintModel [.clean, .secret] namePassing isSecret (send pub pub)
#guard rootReducts namePassing (par (send pub pub) (receive pub (send pub (.bvar 0)))) == [send pub pub]

/-! ## Two variables at once -/

#guard letCalculus.rewrites.all ruleBackward

-- No predecessor leaves a bound variable dangling.
#guard (predecessors letCalculus (app ok err)).all fun family => family.pattern.isWellScopedAt 0

#guard (predecessors letCalculus (app ok err)).map Family.pattern ==
  [letTwoOf (app ok err) (.fvar "second") (.bvar 1), letTwoOf ok err (app (.bvar 1) (.bvar 0)),
    letTwoOf ok (.fvar "second") (app (.bvar 1) err), letTwoOf err ok (app (.bvar 0) (.bvar 1)),
    letTwoOf err (.fvar "second") (app ok (.bvar 1)), letTwoOf (.fvar "first") (app ok err) (.bvar 0),
    letTwoOf (.fvar "first") ok (app (.bvar 0) err), letTwoOf (.fvar "first") err (app ok (.bvar 0)),
    letTwoOf (.fvar "first") (.fvar "second") (app ok err)]

/-! ## Rho -/

theorem rho_backward : ∀ rule ∈ rhoCalculus.rewrites, ruleBackward rule = true := by
  intro rule member
  simp only [rhoCalculus, List.mem_singleton] at member
  subst member
  decide +kernel

-- A bag holding only `Err` comes from an input whose continuation is already `Err`.
#guard (predecessors rhoCalculus (bag [errRho])).map Family.pattern ==
  [bag [output (.fvar "x") (.fvar "Q"), input (.fvar "x") errRho]]

-- `{*@Err | 0}`: the payload was `Err`, or the continuation already held `@Err`.
#guard (predecessors rhoCalculus (bag [drop (quote errRho), nilRho])).map Family.pattern ==
  [bag [output (.fvar "x") errRho, input (.fvar "x") (drop (.bvar 0)), nilRho],
    bag [output (.fvar "x") (.fvar "Q"), input (.fvar "x") (drop (quote errRho)), nilRho]]

/-- **One communication cannot create `Err` from a clean bag**: every object state that steps to the bag
holding `Err` is already dirty. Bags in the source are matched modulo permutation. -/
theorem err_bag_needs_dirt {state : Pattern} (object : ObjectState state)
    (step : bag [errRho] ∈ rootReducts rhoCalculus state) : value rhoModel state = .dirty := by
  have accepted := pastBox_of_check (model := rhoModel) (elements := [.clean, .dirty])
    (fun entry => by cases entry <;> simp) rho_backward (accept := isDirty) (by decide +kernel) object step
  simpa [isDirty] using accepted

-- A clean result can come from a dirty bag: send `Err`, receive it and drop it unused.
#guard !pastBoxCheck rhoModel [.clean, .dirty] rhoCalculus isDirty (bag [nilRho])
#guard rootReducts rhoCalculus (bag [output (quote nilRho) errRho, input (quote nilRho) nilRho]) == [bag [nilRho]]
#guard value rhoModel (bag [output (quote nilRho) errRho, input (quote nilRho) nilRho]) == .dirty

end Mettapedia.OSLF.NativeTypes.Executable.FiniteModelControls
