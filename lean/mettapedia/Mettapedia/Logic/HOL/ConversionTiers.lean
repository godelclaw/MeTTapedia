import Mettapedia.Logic.HOL.ContextualTrinity
import Mettapedia.Logic.HOL.BetaNormalization
import Mettapedia.GSLT.LanguageDef.TierLattice
import Mettapedia.Logic.HOL.Syntax.DecidableEq

/-!
# Beta-conversion tiers of the HOL kernel

Two checkers for HOL derivations modulo beta-joinability sit on the existing
tier lattice. They share the axiom checker and differ in the conversion
evidence they read.

* **Explicit tier.** Conversion evidence lists the redex positions contracted
  on each side (`explicitTier`). The checker replays every listed contraction
  and compares the two results. Replaying a position computes the step itself
  (`stepAt?`); a list of positions replays to an execution of the operational
  face, and every execution is recovered from its own positions
  (`replay?_positions`, `positions_of_replay?`). Positions are invariant under
  substitution and replay commutes with it (`stepAt?_subst`,
  `Execution.positions_subst`), so the explicit evidence is the operational
  face itself, read through a substitution-stable code.
* **Fuelled tier.** Conversion evidence is a pair of step budgets
  (`fuelledTier`). The checker runs leftmost-outermost reduction for the
  given number of steps on each side (`normalize`) and compares.

The fuelled tier lies above the explicit tier (`fuelledAboveExplicit`): its
elaboration records the positions that leftmost-outermost reduction contracts,
and these replay to exactly the normalized terms (`replay?_normalOrder`).
Soundness passes upward along the edge (`fuelled_locallySound`) without
trusting the elaborator. The elaboration writes at most one position per step
of the budgets it was given (`fuelledAboveExplicit_writes`), so the fuelled
checker pays at least the explicit certificate (`Above.work`).

The explicit tier also lies above the fuelled tier (`explicitAboveFuelled`).
This direction rests on strong normalization and confluence of beta
(`BetaNormalization`): leftmost-outermost reduction reaches the unique normal
form of every term, so two terms are joinable exactly when their normal forms
agree (`joinable_iff_normalForm`). The elaboration checks the explicit
evidence and writes the least sufficient budgets. The two tiers therefore
accept the same judgments (`fuelled_iff_explicit`).

The price of retaining explicit evidence is exponential and no more. A budget
is a binary numeral; the explicit certificate elaborated from a fuelled one is
smaller than two to the fuelled bit size plus one (`fuelledElaboration_size`),
and for the chain of `n` identity redexes every accepted explicit certificate
has at least `n` positions while the fuelled certificate has `Nat.size n` bits
(`Controls.compression_gap`). In the other direction the least budgets can
exceed the explicit checking time (`Controls.explicitAboveFuelled_not_writes`).

Both tiers are sound for the extensional face of the computational trinity:
every judgment derivable from axioms by beta-joinability holds in every Henkin
model of the axioms whose functions respect extensional equality
(`derivable_models`).

Controls: a two-step conversion is accepted by both tiers and refused for a
wrong target; whether an execution starts at the root is a substitution-stable
constraint that no extensional requirement selects
(`Controls.executionOrder_not_extensional`); a checker that charges no time for a conversion that needs a
step has no trace-bounded elaboration into the explicit tier
(`Controls.trusted_not_traceBounded`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ContextualTrinity

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Redex positions -/

/-- One move from a term to an immediate subterm: the function or the argument
of an application, the only immediate subterm of an abstraction, a quantifier
or a negation, and the left or right operand of a binary connective or an
equation. -/
inductive Direction where
  | function
  | argument
  | body
  | left
  | right
  deriving DecidableEq, Repr

/-- A path from the root of a term to a redex. -/
abbrev Position := List Direction

/-- The position at which a step contracts its redex. -/
def BetaStep.position : {Γ : Ctx Base} → {τ : Ty Base} →
    {source target : Term Const Γ τ} → BetaStep source target → Position
  | _, _, _, _, .beta _ _ => []
  | _, _, _, _, .appFun _ step => .function :: BetaStep.position step
  | _, _, _, _, .appArg _ step => .argument :: BetaStep.position step
  | _, _, _, _, .lam step => .body :: BetaStep.position step
  | _, _, _, _, .andLeft _ step => .left :: BetaStep.position step
  | _, _, _, _, .andRight _ step => .right :: BetaStep.position step
  | _, _, _, _, .orLeft _ step => .left :: BetaStep.position step
  | _, _, _, _, .orRight _ step => .right :: BetaStep.position step
  | _, _, _, _, .impLeft _ step => .left :: BetaStep.position step
  | _, _, _, _, .impRight _ step => .right :: BetaStep.position step
  | _, _, _, _, .not step => .body :: BetaStep.position step
  | _, _, _, _, .eqLeft _ step => .left :: BetaStep.position step
  | _, _, _, _, .eqRight _ step => .right :: BetaStep.position step
  | _, _, _, _, .all step => .body :: BetaStep.position step
  | _, _, _, _, .ex step => .body :: BetaStep.position step

/-- The root step of an application, when its function is an abstraction. -/
def lamStep? {Γ : Ctx Base} {σ τ : Ty Base} :
    (function : Term Const Γ (σ ⇒ τ)) → (argument : Term Const Γ σ) →
      Option (Σ target : Term Const Γ τ, BetaStep (.app function argument) target)
  | .lam body, argument => some ⟨_, .beta body argument⟩
  | _, _ => none

/-- The step contracting the root redex, if the term is one. -/
def rootStep? {Γ : Ctx Base} {τ : Ty Base} :
    (source : Term Const Γ τ) → Option (Σ target : Term Const Γ τ, BetaStep source target)
  | .app function argument => lamStep? function argument
  | _ => none

/-- Compute the step contracting the redex at a position, if there is one. -/
def stepAt? : {Γ : Ctx Base} → {τ : Ty Base} → (source : Term Const Γ τ) → Position →
    Option (Σ target : Term Const Γ τ, BetaStep source target)
  | _, _, source, [] => rootStep? source
  | _, _, .app function argument, .function :: rest =>
      (stepAt? function rest).map fun found => ⟨_, .appFun argument found.2⟩
  | _, _, .app function argument, .argument :: rest =>
      (stepAt? argument rest).map fun found => ⟨_, .appArg function found.2⟩
  | _, _, .lam body, .body :: rest =>
      (stepAt? body rest).map fun found => ⟨_, .lam found.2⟩
  | _, _, .and left right, .left :: rest =>
      (stepAt? left rest).map fun found => ⟨_, .andLeft right found.2⟩
  | _, _, .and left right, .right :: rest =>
      (stepAt? right rest).map fun found => ⟨_, .andRight left found.2⟩
  | _, _, .or left right, .left :: rest =>
      (stepAt? left rest).map fun found => ⟨_, .orLeft right found.2⟩
  | _, _, .or left right, .right :: rest =>
      (stepAt? right rest).map fun found => ⟨_, .orRight left found.2⟩
  | _, _, .imp left right, .left :: rest =>
      (stepAt? left rest).map fun found => ⟨_, .impLeft right found.2⟩
  | _, _, .imp left right, .right :: rest =>
      (stepAt? right rest).map fun found => ⟨_, .impRight left found.2⟩
  | _, _, .eq left right, .left :: rest =>
      (stepAt? left rest).map fun found => ⟨_, .eqLeft right found.2⟩
  | _, _, .eq left right, .right :: rest =>
      (stepAt? right rest).map fun found => ⟨_, .eqRight left found.2⟩
  | _, _, .not body, .body :: rest =>
      (stepAt? body rest).map fun found => ⟨_, .not found.2⟩
  | _, _, .all body, .body :: rest =>
      (stepAt? body rest).map fun found => ⟨_, .all found.2⟩
  | _, _, .ex body, .body :: rest =>
      (stepAt? body rest).map fun found => ⟨_, .ex found.2⟩
  | _, _, _, _ :: _ => none

@[simp] theorem stepAt?_position {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (step : BetaStep source target) : stepAt? source step.position = some ⟨target, step⟩ := by
  induction step with
  | beta body argument => rfl
  | _ => simp_all [BetaStep.position, stepAt?]

theorem position_of_stepAt? {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    {position : Position} {step : BetaStep source target}
    (found : stepAt? source position = some ⟨target, step⟩) : step.position = position := by
  induction position generalizing Γ τ with
  | nil =>
      cases source with
      | app function argument =>
          cases function with
          | lam body =>
              simp only [stepAt?, rootStep?, lamStep?, Option.some.injEq, Sigma.mk.inj_iff] at found
              obtain ⟨rfl, same⟩ := found
              cases same
              rfl
          | _ => simp [stepAt?, rootStep?, lamStep?] at found
      | _ => simp [stepAt?, rootStep?] at found
  | cons direction rest ih =>
      cases direction <;> cases source <;>
        simp only [stepAt?, Option.map_eq_some_iff, Sigma.mk.inj_iff, reduceCtorEq] at found
      all_goals
        obtain ⟨found', inner, rfl, same⟩ := found
        cases same
        simp [BetaStep.position, ih inner]

/-- A step is determined by its source and its position. -/
theorem BetaStep.eq_of_position {Γ : Ctx Base} {τ : Ty Base} {source target₁ target₂ : Term Const Γ τ}
    (first : BetaStep source target₁) (second : BetaStep source target₂)
    (same : first.position = second.position) : target₁ = target₂ ∧ HEq first second := by
  have found := stepAt?_position second
  rw [← same, stepAt?_position first] at found
  obtain ⟨targets, steps⟩ := Sigma.mk.inj_iff.mp (Option.some.inj found)
  exact ⟨targets, steps⟩

theorem BetaStep.position_of_heq {Γ : Ctx Base} {τ : Ty Base}
    {source₁ source₂ target₁ target₂ : Term Const Γ τ}
    (sources : source₁ = source₂) (targets : target₁ = target₂)
    {first : BetaStep source₁ target₁} {second : BetaStep source₂ target₂}
    (same : HEq first second) : first.position = second.position := by
  subst sources targets
  cases same
  rfl

/-- Substitution does not move a redex. -/
@[simp] theorem BetaStep.position_subst {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ') {τ : Ty Base}
    {source target : Term Const Γ τ} (step : BetaStep source target) :
    (step.subst θ).position = step.position := by
  induction step generalizing Γ' with
  | beta body argument =>
      exact BetaStep.position_of_heq rfl (ProofSyntax.subst_instantiate θ argument body)
        (ProofSyntax.mpr_heq _ _)
  | _ => simp_all [BetaStep.subst, BetaStep.position]

/-- Replay commutes with substitution: a position that contracts a redex
contracts its substituted image at the substituted term. -/
theorem stepAt?_subst {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ') {τ : Ty Base}
    {source target : Term Const Γ τ} {position : Position} {step : BetaStep source target}
    (found : stepAt? source position = some ⟨target, step⟩) :
    stepAt? (HOL.subst θ source) position = some ⟨HOL.subst θ target, step.subst θ⟩ := by
  rw [← position_of_stepAt? found, ← BetaStep.position_subst θ step, stepAt?_position]

/-! ## Executions as position lists -/

/-- The positions contracted by an execution, in order. -/
def Execution.positions {Γ : Ctx Base} {τ : Ty Base} :
    {source target : Term Const Γ τ} → Execution source target → List Position
  | _, _, .done _ => []
  | _, _, .step first rest => first.position :: rest.positions

/-- Replay a list of positions from a source term, constructing the
execution. -/
def replay? {Γ : Ctx Base} {τ : Ty Base} :
    (source : Term Const Γ τ) → List Position →
      Option (Σ target : Term Const Γ τ, Execution source target)
  | source, [] => some ⟨source, .done source⟩
  | source, position :: rest =>
      match stepAt? source position with
      | none => none
      | some found => (replay? found.1 rest).map fun run => ⟨run.1, .step found.2 run.2⟩

/-- Every execution is recovered from its own positions. -/
@[simp] theorem replay?_positions {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (execution : Execution source target) :
    replay? source execution.positions = some ⟨target, execution⟩ := by
  induction execution with
  | done term => rfl
  | step first rest ih => simp [Execution.positions, replay?, ih]

/-- A successful replay of a position list is an execution with exactly those
positions. -/
theorem positions_of_replay? {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    {positions : List Position} {execution : Execution source target}
    (replayed : replay? source positions = some ⟨target, execution⟩) :
    execution.positions = positions := by
  induction positions generalizing source with
  | nil =>
      simp only [replay?, Option.some.injEq, Sigma.mk.inj_iff] at replayed
      obtain ⟨rfl, same⟩ := replayed
      cases same
      rfl
  | cons position rest ih =>
      simp only [replay?] at replayed
      split at replayed
      · simp at replayed
      · rename_i found foundEq
        simp only [Option.map_eq_some_iff, Sigma.mk.inj_iff] at replayed
        obtain ⟨run, runEq, rfl, same⟩ := replayed
        cases same
        simp [Execution.positions, ih runEq, position_of_stepAt? foundEq]

/-- An execution is determined by its source and its positions. -/
theorem Execution.eq_of_positions {Γ : Ctx Base} {τ : Ty Base}
    {source target₁ target₂ : Term Const Γ τ}
    (first : Execution source target₁) (second : Execution source target₂)
    (same : first.positions = second.positions) : target₁ = target₂ ∧ HEq first second := by
  have replayed := replay?_positions second
  rw [← same, replay?_positions first] at replayed
  exact Sigma.mk.inj_iff.mp (Option.some.inj replayed)

@[simp] theorem Execution.positions_subst {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ') {τ : Ty Base}
    {source target : Term Const Γ τ} (execution : Execution source target) :
    (execution.subst θ).positions = execution.positions := by
  induction execution with
  | done => rfl
  | step first rest ih => simp [Execution.subst, Execution.positions, ih]

theorem Execution.length_positions {Γ : Ctx Base} {τ : Ty Base}
    {source target : Term Const Γ τ} (execution : Execution source target) :
    execution.positions.length = execution.length := by
  induction execution with
  | done => rfl
  | step first rest ih => simp [Execution.positions, Execution.length, ih]

theorem replay?_subst {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ') {τ : Ty Base}
    {source target : Term Const Γ τ} {positions : List Position}
    {execution : Execution source target}
    (replayed : replay? source positions = some ⟨target, execution⟩) :
    replay? (HOL.subst θ source) positions =
      some ⟨HOL.subst θ target, execution.subst θ⟩ := by
  rw [← positions_of_replay? replayed, ← Execution.positions_subst θ execution,
    replay?_positions]

/-! ## Leftmost-outermost reduction -/

/-- The leftmost-outermost redex of a term, searched through applications and
abstractions. -/
def leftmostRedex? : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Option Position
  | _, _, .app function argument =>
      match rootStep? (.app function argument) with
      | some _ => some []
      | none =>
          match leftmostRedex? function with
          | some position => some (.function :: position)
          | none => (leftmostRedex? argument).map (.argument :: ·)
  | _, _, .lam body => (leftmostRedex? body).map (.body :: ·)
  | _, _, .and left right =>
      match leftmostRedex? left with
      | some position => some (.left :: position)
      | none => (leftmostRedex? right).map (.right :: ·)
  | _, _, .or left right =>
      match leftmostRedex? left with
      | some position => some (.left :: position)
      | none => (leftmostRedex? right).map (.right :: ·)
  | _, _, .imp left right =>
      match leftmostRedex? left with
      | some position => some (.left :: position)
      | none => (leftmostRedex? right).map (.right :: ·)
  | _, _, .eq left right =>
      match leftmostRedex? left with
      | some position => some (.left :: position)
      | none => (leftmostRedex? right).map (.right :: ·)
  | _, _, .not body => (leftmostRedex? body).map (.body :: ·)
  | _, _, .all body => (leftmostRedex? body).map (.body :: ·)
  | _, _, .ex body => (leftmostRedex? body).map (.body :: ·)
  | _, _, _ => none

/-- One leftmost-outermost reduction step, computed directly on the term. -/
def reduceLeftmost? : {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Option (Term Const Γ τ)
  | _, _, .app function argument =>
      match rootStep? (.app function argument) with
      | some found => some found.1
      | none =>
          match reduceLeftmost? function with
          | some function' => some (.app function' argument)
          | none => (reduceLeftmost? argument).map (.app function ·)
  | _, _, .lam body => (reduceLeftmost? body).map .lam
  | _, _, .and left right =>
      match reduceLeftmost? left with
      | some left' => some (.and left' right)
      | none => (reduceLeftmost? right).map (.and left ·)
  | _, _, .or left right =>
      match reduceLeftmost? left with
      | some left' => some (.or left' right)
      | none => (reduceLeftmost? right).map (.or left ·)
  | _, _, .imp left right =>
      match reduceLeftmost? left with
      | some left' => some (.imp left' right)
      | none => (reduceLeftmost? right).map (.imp left ·)
  | _, _, .eq left right =>
      match reduceLeftmost? left with
      | some left' => some (.eq left' right)
      | none => (reduceLeftmost? right).map (.eq left ·)
  | _, _, .not body => (reduceLeftmost? body).map .not
  | _, _, .all body => (reduceLeftmost? body).map .all
  | _, _, .ex body => (reduceLeftmost? body).map .ex
  | _, _, _ => none

/-- The redex the search finds is contractible. -/
theorem stepAt?_leftmostRedex? {Γ : Ctx Base} {τ : Ty Base} {term : Term Const Γ τ}
    {position : Position} (found : leftmostRedex? term = some position) :
    ∃ contracted, stepAt? term position = some contracted := by
  induction term generalizing position with
  | app function argument functionIh argumentIh =>
      cases root : rootStep? (.app function argument) with
      | some contracted =>
          simp only [leftmostRedex?, root, Option.some.injEq] at found
          subst found
          exact ⟨contracted, root⟩
      | none =>
          cases leftmost : leftmostRedex? function with
          | some inner =>
              simp only [leftmostRedex?, root, leftmost, Option.some.injEq] at found
              subst found
              obtain ⟨contracted, stepped⟩ := functionIh leftmost
              exact ⟨⟨_, .appFun argument contracted.2⟩, by simp [stepAt?, stepped]⟩
          | none =>
              simp only [leftmostRedex?, root, leftmost, Option.map_eq_some_iff] at found
              obtain ⟨inner, innerFound, rfl⟩ := found
              obtain ⟨contracted, stepped⟩ := argumentIh innerFound
              exact ⟨⟨_, .appArg function contracted.2⟩, by simp [stepAt?, stepped]⟩
  | lam body ih =>
      simp only [leftmostRedex?, Option.map_eq_some_iff] at found
      obtain ⟨inner, innerFound, rfl⟩ := found
      obtain ⟨contracted, stepped⟩ := ih innerFound
      exact ⟨⟨_, .lam contracted.2⟩, by simp [stepAt?, stepped]⟩
  | and left right leftIh rightIh =>
      cases leftmost : leftmostRedex? left with
      | some inner =>
          simp only [leftmostRedex?, leftmost, Option.some.injEq] at found
          subst found
          obtain ⟨contracted, stepped⟩ := leftIh leftmost
          exact ⟨⟨_, .andLeft right contracted.2⟩, by simp [stepAt?, stepped]⟩
      | none =>
          simp only [leftmostRedex?, leftmost, Option.map_eq_some_iff] at found
          obtain ⟨inner, innerFound, rfl⟩ := found
          obtain ⟨contracted, stepped⟩ := rightIh innerFound
          exact ⟨⟨_, .andRight left contracted.2⟩, by simp [stepAt?, stepped]⟩
  | or left right leftIh rightIh =>
      cases leftmost : leftmostRedex? left with
      | some inner =>
          simp only [leftmostRedex?, leftmost, Option.some.injEq] at found
          subst found
          obtain ⟨contracted, stepped⟩ := leftIh leftmost
          exact ⟨⟨_, .orLeft right contracted.2⟩, by simp [stepAt?, stepped]⟩
      | none =>
          simp only [leftmostRedex?, leftmost, Option.map_eq_some_iff] at found
          obtain ⟨inner, innerFound, rfl⟩ := found
          obtain ⟨contracted, stepped⟩ := rightIh innerFound
          exact ⟨⟨_, .orRight left contracted.2⟩, by simp [stepAt?, stepped]⟩
  | imp left right leftIh rightIh =>
      cases leftmost : leftmostRedex? left with
      | some inner =>
          simp only [leftmostRedex?, leftmost, Option.some.injEq] at found
          subst found
          obtain ⟨contracted, stepped⟩ := leftIh leftmost
          exact ⟨⟨_, .impLeft right contracted.2⟩, by simp [stepAt?, stepped]⟩
      | none =>
          simp only [leftmostRedex?, leftmost, Option.map_eq_some_iff] at found
          obtain ⟨inner, innerFound, rfl⟩ := found
          obtain ⟨contracted, stepped⟩ := rightIh innerFound
          exact ⟨⟨_, .impRight left contracted.2⟩, by simp [stepAt?, stepped]⟩
  | eq left right leftIh rightIh =>
      cases leftmost : leftmostRedex? left with
      | some inner =>
          simp only [leftmostRedex?, leftmost, Option.some.injEq] at found
          subst found
          obtain ⟨contracted, stepped⟩ := leftIh leftmost
          exact ⟨⟨_, .eqLeft right contracted.2⟩, by simp [stepAt?, stepped]⟩
      | none =>
          simp only [leftmostRedex?, leftmost, Option.map_eq_some_iff] at found
          obtain ⟨inner, innerFound, rfl⟩ := found
          obtain ⟨contracted, stepped⟩ := rightIh innerFound
          exact ⟨⟨_, .eqRight left contracted.2⟩, by simp [stepAt?, stepped]⟩
  | not body ih =>
      simp only [leftmostRedex?, Option.map_eq_some_iff] at found
      obtain ⟨inner, innerFound, rfl⟩ := found
      obtain ⟨contracted, stepped⟩ := ih innerFound
      exact ⟨⟨_, .not contracted.2⟩, by simp [stepAt?, stepped]⟩
  | all body ih =>
      simp only [leftmostRedex?, Option.map_eq_some_iff] at found
      obtain ⟨inner, innerFound, rfl⟩ := found
      obtain ⟨contracted, stepped⟩ := ih innerFound
      exact ⟨⟨_, .all contracted.2⟩, by simp [stepAt?, stepped]⟩
  | ex body ih =>
      simp only [leftmostRedex?, Option.map_eq_some_iff] at found
      obtain ⟨inner, innerFound, rfl⟩ := found
      obtain ⟨contracted, stepped⟩ := ih innerFound
      exact ⟨⟨_, .ex contracted.2⟩, by simp [stepAt?, stepped]⟩
  | _ => simp [leftmostRedex?] at found

/-- The direct reducer contracts exactly the redex the search finds. -/
theorem reduceLeftmost?_eq {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) :
    reduceLeftmost? term =
      (leftmostRedex? term).bind fun position => (stepAt? term position).map (·.1) := by
  induction term with
  | app function argument functionIh argumentIh =>
      cases root : rootStep? (.app function argument) with
      | some found => simp [reduceLeftmost?, leftmostRedex?, root, stepAt?]
      | none =>
          cases leftmost : leftmostRedex? function with
          | some position =>
              obtain ⟨found, stepped⟩ := stepAt?_leftmostRedex? leftmost
              simp_all [reduceLeftmost?, leftmostRedex?, stepAt?]
          | none =>
              cases leftmostArgument : leftmostRedex? argument with
              | none => simp_all [reduceLeftmost?, leftmostRedex?]
              | some position =>
                  obtain ⟨found, stepped⟩ := stepAt?_leftmostRedex? leftmostArgument
                  simp_all [reduceLeftmost?, leftmostRedex?, stepAt?]
  | lam body ih =>
      cases leftmost : leftmostRedex? body with
      | none => simp_all [reduceLeftmost?, leftmostRedex?]
      | some position =>
          obtain ⟨found, stepped⟩ := stepAt?_leftmostRedex? leftmost
          simp_all [reduceLeftmost?, leftmostRedex?, stepAt?]
  | and left right leftIh rightIh =>
      cases leftmost : leftmostRedex? left with
      | some position =>
          obtain ⟨found, stepped⟩ := stepAt?_leftmostRedex? leftmost
          simp_all [reduceLeftmost?, leftmostRedex?, stepAt?]
      | none =>
          cases leftmostRight : leftmostRedex? right with
          | none => simp_all [reduceLeftmost?, leftmostRedex?]
          | some position =>
              obtain ⟨found, stepped⟩ := stepAt?_leftmostRedex? leftmostRight
              simp_all [reduceLeftmost?, leftmostRedex?, stepAt?]
  | or left right leftIh rightIh =>
      cases leftmost : leftmostRedex? left with
      | some position =>
          obtain ⟨found, stepped⟩ := stepAt?_leftmostRedex? leftmost
          simp_all [reduceLeftmost?, leftmostRedex?, stepAt?]
      | none =>
          cases leftmostRight : leftmostRedex? right with
          | none => simp_all [reduceLeftmost?, leftmostRedex?]
          | some position =>
              obtain ⟨found, stepped⟩ := stepAt?_leftmostRedex? leftmostRight
              simp_all [reduceLeftmost?, leftmostRedex?, stepAt?]
  | imp left right leftIh rightIh =>
      cases leftmost : leftmostRedex? left with
      | some position =>
          obtain ⟨found, stepped⟩ := stepAt?_leftmostRedex? leftmost
          simp_all [reduceLeftmost?, leftmostRedex?, stepAt?]
      | none =>
          cases leftmostRight : leftmostRedex? right with
          | none => simp_all [reduceLeftmost?, leftmostRedex?]
          | some position =>
              obtain ⟨found, stepped⟩ := stepAt?_leftmostRedex? leftmostRight
              simp_all [reduceLeftmost?, leftmostRedex?, stepAt?]
  | eq left right leftIh rightIh =>
      cases leftmost : leftmostRedex? left with
      | some position =>
          obtain ⟨found, stepped⟩ := stepAt?_leftmostRedex? leftmost
          simp_all [reduceLeftmost?, leftmostRedex?, stepAt?]
      | none =>
          cases leftmostRight : leftmostRedex? right with
          | none => simp_all [reduceLeftmost?, leftmostRedex?]
          | some position =>
              obtain ⟨found, stepped⟩ := stepAt?_leftmostRedex? leftmostRight
              simp_all [reduceLeftmost?, leftmostRedex?, stepAt?]
  | not body ih =>
      cases leftmost : leftmostRedex? body with
      | none => simp_all [reduceLeftmost?, leftmostRedex?]
      | some position =>
          obtain ⟨found, stepped⟩ := stepAt?_leftmostRedex? leftmost
          simp_all [reduceLeftmost?, leftmostRedex?, stepAt?]
  | all body ih =>
      cases leftmost : leftmostRedex? body with
      | none => simp_all [reduceLeftmost?, leftmostRedex?]
      | some position =>
          obtain ⟨found, stepped⟩ := stepAt?_leftmostRedex? leftmost
          simp_all [reduceLeftmost?, leftmostRedex?, stepAt?]
  | ex body ih =>
      cases leftmost : leftmostRedex? body with
      | none => simp_all [reduceLeftmost?, leftmostRedex?]
      | some position =>
          obtain ⟨found, stepped⟩ := stepAt?_leftmostRedex? leftmost
          simp_all [reduceLeftmost?, leftmostRedex?, stepAt?]
  | _ => rfl

/-- Run leftmost-outermost reduction for at most the given number of steps. -/
def normalize {Γ : Ctx Base} {τ : Ty Base} : Nat → Term Const Γ τ → Term Const Γ τ
  | 0, term => term
  | budget + 1, term =>
      match reduceLeftmost? term with
      | none => term
      | some reduced => normalize budget reduced

/-- The positions that leftmost-outermost reduction contracts within a
budget. -/
def normalOrderPositions {Γ : Ctx Base} {τ : Ty Base} : Nat → Term Const Γ τ → List Position
  | 0, _ => []
  | budget + 1, term =>
      match leftmostRedex? term with
      | none => []
      | some position =>
          match stepAt? term position with
          | none => []
          | some found => position :: normalOrderPositions budget found.1

/-- The recorded positions replay to exactly the normalized term. -/
theorem replay?_normalOrder {Γ : Ctx Base} {τ : Ty Base} (budget : Nat)
    (term : Term Const Γ τ) :
    (replay? term (normalOrderPositions budget term)).map Sigma.fst =
      some (normalize budget term) := by
  induction budget generalizing term with
  | zero => rfl
  | succ budget ih =>
      cases leftmost : leftmostRedex? term with
      | none =>
          have reduced : reduceLeftmost? term = none := by
            rw [reduceLeftmost?_eq, leftmost]
            rfl
          simp [normalOrderPositions, leftmost, normalize, reduced, replay?]
      | some position =>
          obtain ⟨found, stepped⟩ := stepAt?_leftmostRedex? leftmost
          have reduced : reduceLeftmost? term = some found.1 := by
            rw [reduceLeftmost?_eq, leftmost]
            simp [stepped]
          have restReplayed := ih found.1
          simp only [normalOrderPositions, leftmost, stepped, replay?, normalize, reduced]
          rw [← restReplayed]
          cases replay? found.fst (normalOrderPositions budget found.fst) <;> rfl

theorem length_normalOrderPositions {Γ : Ctx Base} {τ : Ty Base} (budget : Nat)
    (term : Term Const Γ τ) : (normalOrderPositions budget term).length ≤ budget := by
  induction budget generalizing term with
  | zero => simp [normalOrderPositions]
  | succ budget ih =>
      simp only [normalOrderPositions]
      split
      · simp
      · split
        · simp
        · simpa using ih _

end Mettapedia.Logic.HOL.ContextualTrinity

namespace Mettapedia.Logic.HOL.ConversionTiers

open Mettapedia.Logic.HOL.ContextualTrinity
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.ProofSystems
open Mettapedia.GSLT.LanguageDef.TierLattice

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}
variable [DecidableEq Base] [∀ τ, DecidableEq (Const τ)]

/-! ## The theory: axioms closed under beta-joinability -/

/-- Two terms are joinable when executions take both to one term. -/
def Joinable {Γ : Ctx Base} {τ : Ty Base} (left right : Term Const Γ τ) : Prop :=
  ∃ meet, Nonempty (Execution left meet) ∧ Nonempty (Execution right meet)

/-- A list of axioms at one context, closed under beta-joinability. -/
def joinTheory {Γ : Ctx Base} (axioms : List (Formula Const Γ)) : Theory (Formula Const Γ) where
  axioms formula := formula ∈ axioms
  conversion := Joinable

/-! ## Checkers and tiers -/

/-- Axiom evidence is an index into the list. Sizes and times are declared
accounts of a list walk, not machine clocks. -/
def axiomChecker {Γ : Ctx Base} (axioms : List (Formula Const Γ)) :
    TimedChecker (Formula Const Γ) Nat where
  check formula index := decide (axioms[index]? = some formula)
  claimSize _ := 1
  certificateSize index := index + 1
  time _ index := index + 1

/-- Replay both position lists and compare the results. -/
def explicitCheck {Γ : Ctx Base} (claim : ConversionClaim (Formula Const Γ))
    (evidence : List Position × List Position) : Bool :=
  match replay? claim.source evidence.1, replay? claim.target evidence.2 with
  | some left, some right => decide (left.1 = right.1)
  | _, _ => false

/-- Explicit conversion evidence: the contracted positions of both sides. Its
size counts contracted steps. -/
def explicitConversion {Γ : Ctx Base} :
    TimedChecker (ConversionClaim (Formula Const Γ)) (List Position × List Position) where
  check := explicitCheck
  claimSize _ := 1
  certificateSize evidence := evidence.1.length + evidence.2.length
  time _ evidence := evidence.1.length + evidence.2.length + 1

/-- Fuelled conversion evidence: step budgets for both sides. The checker
normalizes and compares; it reads no positions. A budget is a binary numeral,
so its size is its bit length. -/
def fuelledConversion {Γ : Ctx Base} :
    TimedChecker (ConversionClaim (Formula Const Γ)) (Nat × Nat) where
  check claim budgets :=
    decide (normalize budgets.1 claim.source = normalize budgets.2 claim.target)
  claimSize _ := 1
  certificateSize budgets := Nat.size budgets.1 + Nat.size budgets.2
  time _ budgets := budgets.1 + budgets.2 + 1

/-- The explicit tier: positions for every conversion. -/
def explicitTier {Γ : Ctx Base} (axioms : List (Formula Const Γ)) :
    Tier (Formula Const Γ) Nat (List Position × List Position) :=
  ⟨axiomChecker axioms, explicitConversion⟩

/-- The fuelled tier: budgets for every conversion. -/
def fuelledTier {Γ : Ctx Base} (axioms : List (Formula Const Γ)) :
    Tier (Formula Const Γ) Nat (Nat × Nat) :=
  ⟨axiomChecker axioms, fuelledConversion⟩

theorem explicitCheck_eq_true_iff {Γ : Ctx Base} (claim : ConversionClaim (Formula Const Γ))
    (evidence : List Position × List Position) :
    explicitCheck claim evidence = true ↔
      ∃ meet, (replay? claim.source evidence.1).map Sigma.fst = some meet ∧
        (replay? claim.target evidence.2).map Sigma.fst = some meet := by
  unfold explicitCheck
  cases left : replay? claim.source evidence.1 <;>
    cases right : replay? claim.target evidence.2 <;> simp [eq_comm]

/-- Leftmost-outermost positions elaborate fuelled evidence into explicit
evidence. -/
def fuelledElaboration {Γ : Ctx Base} :
    Elaboration (fuelledConversion (Const := Const) (Γ := Γ)).toChecker
      (explicitConversion (Const := Const) (Γ := Γ)).toChecker where
  elaborate claim budgets :=
    some (normalOrderPositions budgets.1 claim.source, normalOrderPositions budgets.2 claim.target)
  exact claim budgets := by
    change decide (normalize budgets.1 claim.source = normalize budgets.2 claim.target) = true ↔ _
    simp only [decide_eq_true_eq, Option.some.injEq, exists_eq_left']
    change _ ↔ explicitCheck claim _ = true
    rw [explicitCheck_eq_true_iff, replay?_normalOrder, replay?_normalOrder]
    simp [eq_comm]

/-- **The fuelled tier lies above the explicit tier.** -/
def fuelledAboveExplicit {Γ : Ctx Base} (axioms : List (Formula Const Γ)) :
    Above (fuelledTier axioms) (explicitTier axioms) where
  axiomElaboration := Elaboration.identity _
  conversionElaboration := fuelledElaboration

theorem explicit_locallySound {Γ : Ctx Base} (axioms : List (Formula Const Γ)) :
    (explicitTier axioms).LocallySound (joinTheory axioms) := by
  constructor
  · intro formula index accepted
    have found : axioms[index]? = some formula := of_decide_eq_true accepted
    exact List.mem_of_getElem? found
  · rintro claim ⟨left, right⟩ accepted
    change explicitCheck claim (left, right) = true at accepted
    rw [explicitCheck_eq_true_iff] at accepted
    obtain ⟨meet, leftMeet, rightMeet⟩ := accepted
    obtain ⟨⟨leftEnd, leftRun⟩, leftReplayed, leftSame⟩ := Option.map_eq_some_iff.mp leftMeet
    obtain ⟨⟨rightEnd, rightRun⟩, rightReplayed, rightSame⟩ := Option.map_eq_some_iff.mp rightMeet
    simp only at leftSame rightSame
    subst leftSame rightSame
    exact ⟨_, ⟨leftRun⟩, ⟨rightRun⟩⟩

/-- Soundness passes up the edge, with no trust in the elaborator. -/
theorem fuelled_locallySound {Γ : Ctx Base} (axioms : List (Formula Const Γ)) :
    (fuelledTier axioms).LocallySound (joinTheory axioms) :=
  (fuelledAboveExplicit axioms).sound (explicit_locallySound axioms)

/-- The elaboration writes at most one position per budgeted step. -/
theorem fuelledAboveExplicit_writes {Γ : Ctx Base} (axioms : List (Formula Const Γ)) :
    (fuelledAboveExplicit axioms).Writes := by
  constructor
  · intro formula index lowered produced
    cases produced
    exact le_rfl
  · rintro claim ⟨first, second⟩ lowered produced
    cases produced
    change (normalOrderPositions first claim.source).length +
        (normalOrderPositions second claim.target).length ≤ first + second + 1
    have := length_normalOrderPositions first claim.source
    have := length_normalOrderPositions second claim.target
    omega

/-! ## Explicit evidence elaborates into fuelled evidence

Strong normalization and confluence of beta (`BetaNormalization`) make
leftmost-outermost reduction a complete conversion test: it reaches the unique
normal form of every term, and two terms are joinable exactly when their normal
forms agree. So the explicit tier also lies above the fuelled tier, and the two
tiers accept the same articles. -/

section NormalOrder

open BetaNormalization

omit [DecidableEq Base] [∀ τ, DecidableEq (Const τ)] in
theorem reduceLeftmost?_reduces {Γ : Ctx Base} {τ : Ty Base} {term term' : Term Const Γ τ}
    (reduced : reduceLeftmost? term = some term') : Reduces term term' := by
  rw [reduceLeftmost?_eq] at reduced
  simp only [Option.bind_eq_some_iff, Option.map_eq_some_iff] at reduced
  obtain ⟨position, _, ⟨target, step⟩, _, rfl⟩ := reduced
  exact ⟨step⟩

omit [DecidableEq Base] [∀ τ, DecidableEq (Const τ)] in
theorem leftmostRedex?_isSome {Γ : Ctx Base} {τ : Ty Base} {term target : Term Const Γ τ}
    (step : BetaStep term target) : (leftmostRedex? term).isSome := by
  induction step with
  | beta body argument => simp [leftmostRedex?, rootStep?, lamStep?]
  | lam _ ih => simp_all [leftmostRedex?]
  | not _ ih => simp_all [leftmostRedex?]
  | all _ ih => simp_all [leftmostRedex?]
  | ex _ ih => simp_all [leftmostRedex?]
  | _ =>
      simp only [leftmostRedex?]
      repeat' split
      all_goals simp_all

omit [DecidableEq Base] [∀ τ, DecidableEq (Const τ)] in
/-- Leftmost-outermost reduction stops exactly at normal forms. -/
theorem reduceLeftmost?_eq_none_iff {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) :
    reduceLeftmost? term = none ↔ Normal term := by
  constructor
  · intro stopped target ⟨step⟩
    obtain ⟨position, found⟩ := Option.isSome_iff_exists.mp (leftmostRedex?_isSome step)
    obtain ⟨contracted, stepped⟩ := stepAt?_leftmostRedex? found
    rw [reduceLeftmost?_eq, found] at stopped
    simp [stepped] at stopped
  · intro normal
    cases reduced : reduceLeftmost? term with
    | none => rfl
    | some term' => exact absurd (reduceLeftmost?_reduces reduced) (normal term')

omit [DecidableEq Base] [∀ τ, DecidableEq (Const τ)] in
theorem normalize_star {Γ : Ctx Base} {τ : Ty Base} (budget : Nat) (term : Term Const Γ τ) :
    ReducesStar term (normalize budget term) := by
  induction budget generalizing term with
  | zero => exact .refl
  | succ budget ih =>
      cases reduced : reduceLeftmost? term with
      | none =>
          simp only [normalize, reduced]
          exact .refl
      | some term' =>
          simp only [normalize, reduced]
          exact .head (reduceLeftmost?_reduces reduced) (ih _)

omit [DecidableEq Base] [∀ τ, DecidableEq (Const τ)] in
/-- **Normal order terminates.** Some budget brings every term to a normal form. -/
theorem normalizes {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) :
    ∃ budget, (reduceLeftmost? (normalize budget term)).isNone = true := by
  induction stronglyNormalizing term with
  | intro term _ ih =>
      cases reduced : reduceLeftmost? term with
      | none => exact ⟨0, by simp [normalize, reduced]⟩
      | some term' =>
          obtain ⟨budget, stopped⟩ := ih term' (reduceLeftmost?_reduces reduced)
          exact ⟨budget + 1, by simpa [normalize, reduced] using stopped⟩

/-- The least budget at which leftmost-outermost reduction stops. -/
def normalSteps {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) : Nat :=
  Nat.find (normalizes term)

/-- The normal form, computed by leftmost-outermost reduction. -/
def normalForm {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) : Term Const Γ τ :=
  normalize (normalSteps term) term

omit [DecidableEq Base] [∀ τ, DecidableEq (Const τ)] in
theorem normalForm_normal {Γ : Ctx Base} {τ : Ty Base} (term : Term Const Γ τ) :
    Normal (normalForm term) := by
  have stopped := Nat.find_spec (normalizes term)
  rw [Option.isNone_iff_eq_none] at stopped
  exact (reduceLeftmost?_eq_none_iff _).mp stopped

omit [DecidableEq Base] [∀ τ, DecidableEq (Const τ)] in
theorem execution_star {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (execution : Execution source target) : ReducesStar source target := by
  induction execution with
  | done => exact .refl
  | step first _ ih => exact .head ⟨first⟩ ih

omit [DecidableEq Base] [∀ τ, DecidableEq (Const τ)] in
theorem star_execution {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (many : ReducesStar source target) : Nonempty (Execution source target) := by
  induction many using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨.done _⟩
  | head step _ ih =>
      obtain ⟨first⟩ := step
      obtain ⟨rest⟩ := ih
      exact ⟨.step first rest⟩

omit [DecidableEq Base] [∀ τ, DecidableEq (Const τ)] in
/-- **Joinability is equality of normal forms.** -/
theorem joinable_iff_normalForm {Γ : Ctx Base} {τ : Ty Base} {left right : Term Const Γ τ} :
    Joinable left right ↔ normalForm left = normalForm right := by
  constructor
  · rintro ⟨meet, ⟨leftRun⟩, ⟨rightRun⟩⟩
    exact normal_eq_of_joinable (execution_star leftRun) (execution_star rightRun)
      (normalize_star _ left) (normalForm_normal left) (normalize_star _ right)
      (normalForm_normal right)
  · intro same
    refine ⟨normalForm left, star_execution (normalize_star _ left), ?_⟩
    rw [same]
    exact star_execution (normalize_star _ right)

end NormalOrder

/-- Explicit evidence elaborates into the least sufficient budgets, after the
explicit evidence itself is checked. -/
def explicitElaboration {Γ : Ctx Base} :
    Elaboration (explicitConversion (Const := Const) (Γ := Γ)).toChecker
      (fuelledConversion (Const := Const) (Γ := Γ)).toChecker where
  elaborate claim evidence :=
    if explicitCheck claim evidence then
      some (normalSteps claim.source, normalSteps claim.target)
    else none
  exact claim evidence := by
    constructor
    · intro accepted
      have checked : explicitCheck claim evidence = true := accepted
      refine ⟨_, if_pos checked, ?_⟩
      have joinable := (explicit_locallySound (Const := Const) (Γ := Γ) []).2 claim evidence accepted
      exact decide_eq_true (joinable_iff_normalForm.mp joinable)
    · rintro ⟨lowered, produced, _⟩
      by_contra rejected
      have unchecked : explicitCheck claim evidence = false := Bool.eq_false_iff.mpr rejected
      simp [unchecked] at produced

/-- **The explicit tier lies above the fuelled tier.** With `fuelledAboveExplicit`,
the two tiers are equivalent in the lattice. -/
def explicitAboveFuelled {Γ : Ctx Base} (axioms : List (Formula Const Γ)) :
    Above (explicitTier axioms) (fuelledTier axioms) where
  axiomElaboration := Elaboration.identity _
  conversionElaboration := explicitElaboration

/-- The fuelled tier accepts exactly the joinable conversions, with the
least budgets as witnesses. -/
theorem fuelled_check_iff_joinable {Γ : Ctx Base} (claim : ConversionClaim (Formula Const Γ)) :
    (∃ budgets, fuelledConversion.check claim budgets = true) ↔
      Joinable claim.source claim.target := by
  constructor
  · rintro ⟨budgets, accepted⟩
    exact (fuelled_locallySound (Const := Const) (Γ := Γ) []).2 claim budgets accepted
  · intro joinable
    exact ⟨(normalSteps claim.source, normalSteps claim.target),
      decide_eq_true (joinable_iff_normalForm.mp joinable)⟩

/-- **The two tiers accept the same judgments.** -/
theorem fuelled_iff_explicit {Γ : Ctx Base} (axioms : List (Formula Const Γ))
    (judgmentSize : Formula Const Γ → Nat) (formula : Formula Const Γ) :
    (∃ article, ((fuelledTier axioms).checker judgmentSize).check formula article = true) ↔
      ∃ article, ((explicitTier axioms).checker judgmentSize).check formula article = true := by
  constructor
  · rintro ⟨article, accepted⟩
    obtain ⟨lowered, _, loweredAccepted⟩ :=
      (((fuelledAboveExplicit axioms).elaboration judgmentSize).exact formula article).mp accepted
    exact ⟨lowered, loweredAccepted⟩
  · rintro ⟨article, accepted⟩
    obtain ⟨lowered, _, loweredAccepted⟩ :=
      (((explicitAboveFuelled axioms).elaboration judgmentSize).exact formula article).mp accepted
    exact ⟨lowered, loweredAccepted⟩

/-! ## The price of explicit evidence -/

/-- **Elaboration size bound.** The explicit certificate that the fuelled tier
elaborates into is smaller than an exponential of the fuelled certificate's
bit size. -/
theorem fuelledElaboration_size {Γ : Ctx Base} (claim : ConversionClaim (Formula Const Γ))
    (budgets : Nat × Nat) {lowered : List Position × List Position}
    (produced : (fuelledElaboration (Const := Const) (Γ := Γ)).elaborate claim budgets = some lowered) :
    (explicitConversion (Const := Const) (Γ := Γ)).certificateSize lowered <
      2 ^ ((fuelledConversion (Const := Const) (Γ := Γ)).certificateSize budgets + 1) := by
  simp only [fuelledElaboration, Option.some.injEq] at produced
  subst produced
  change (normalOrderPositions budgets.1 claim.source).length +
      (normalOrderPositions budgets.2 claim.target).length <
    2 ^ (Nat.size budgets.1 + Nat.size budgets.2 + 1)
  have first := length_normalOrderPositions budgets.1 claim.source
  have second := length_normalOrderPositions budgets.2 claim.target
  have firstBits := Nat.lt_size_self budgets.1
  have secondBits := Nat.lt_size_self budgets.2
  have firstPow : 2 ^ Nat.size budgets.1 ≤ 2 ^ (Nat.size budgets.1 + Nat.size budgets.2) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right _ _)
  have secondPow : 2 ^ Nat.size budgets.2 ≤ 2 ^ (Nat.size budgets.1 + Nat.size budgets.2) :=
    Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left _ _)
  rw [pow_succ]
  omega

/-! ## Both tiers are sound for the extensional face -/

omit [DecidableEq Base] [∀ τ, DecidableEq (Const τ)] in
/-- Joinable formulas have the same truth value at every admissible
valuation of a Henkin model whose functions respect extensional equality. -/
theorem joinable_denote (M : HenkinModel.{u, v, w} Base Const) (respects : M.FunctionsRespectEqv)
    {Γ : Ctx Base} {valuation : HenkinModel.Valuation M Γ}
    (admissible : HenkinModel.ValuationAdmissible M valuation)
    {left right : Formula Const Γ} (joinable : Joinable left right) :
    (HenkinModel.denote M left valuation).down ↔ (HenkinModel.denote M right valuation).down := by
  obtain ⟨meet, ⟨leftRun⟩, ⟨rightRun⟩⟩ := joinable
  have leftMeet := Soundness.extDerivation_sound (leftRun.proof []).erase respects admissible
    (fun _ member => nomatch member)
  have rightMeet := Soundness.extDerivation_sound (rightRun.proof []).erase respects admissible
    (fun _ member => nomatch member)
  exact (show _ ↔ _ from leftMeet).trans (show _ ↔ _ from rightMeet).symm

omit [DecidableEq Base] [∀ τ, DecidableEq (Const τ)] in
/-- Every judgment derivable from the axioms by beta-joinability holds in
every model of the axioms. -/
theorem derivable_models {Γ : Ctx Base} (axioms : List (Formula Const Γ))
    (M : HenkinModel.{u, v, w} Base Const) (respects : M.FunctionsRespectEqv)
    {valuation : HenkinModel.Valuation M Γ}
    (admissible : HenkinModel.ValuationAdmissible M valuation)
    (axiomsHold : ∀ formula ∈ axioms, (HenkinModel.denote M formula valuation).down)
    {formula : Formula Const Γ} (derivable : Derivable (joinTheory axioms) formula) :
    (HenkinModel.denote M formula valuation).down := by
  induction derivable with
  | axiom' member => exact axiomsHold _ member
  | convert _ joinable ih => exact (joinable_denote M respects admissible joinable).mp ih

/-- An article accepted by the fuelled tier proves a judgment true in every
model of the axioms. Trust passes through the explicit tier. -/
theorem fuelled_accepted_models {Γ : Ctx Base} (axioms : List (Formula Const Γ))
    (judgmentSize : Formula Const Γ → Nat) {formula : Formula Const Γ}
    {article : ExplicitCertificate (Formula Const Γ) Nat (Nat × Nat)}
    (accepted : ((fuelledTier axioms).checker judgmentSize).check formula article = true)
    (M : HenkinModel.{u, v, w} Base Const) (respects : M.FunctionsRespectEqv)
    {valuation : HenkinModel.Valuation M Γ}
    (admissible : HenkinModel.ValuationAdmissible M valuation)
    (axiomsHold : ∀ formula ∈ axioms, (HenkinModel.denote M formula valuation).down) :
    (HenkinModel.denote M formula valuation).down :=
  derivable_models axioms M respects admissible axiomsHold
    (Tier.checker_sound judgmentSize (fuelled_locallySound axioms) formula article accepted)

/-! ## Explicit evidence is the operational face -/

/-- Checked position lists at a context: a source term and positions that
replay from it. -/
abbrev CheckedPositions (Γ : Ctx Base) : Type (max u v) :=
  {certificate : (Σ τ : Ty Base, Term Const Γ τ) × List Position //
    (replay? certificate.1.2 certificate.2).isSome}

namespace CheckedPositions

def subst {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ')
    (certificate : CheckedPositions (Const := Const) Γ) : CheckedPositions (Const := Const) Γ' :=
  ⟨(⟨certificate.1.1.1, HOL.subst θ certificate.1.1.2⟩, certificate.1.2), by
    obtain ⟨⟨⟨τ, source⟩, positions⟩, checked⟩ := certificate
    obtain ⟨⟨target, run⟩, replayed⟩ := Option.isSome_iff_exists.mp checked
    simp [replay?_subst θ replayed]⟩

/-- Decode checked positions into the execution they replay to. -/
def decode {Γ : Ctx Base} (certificate : CheckedPositions (Const := Const) Γ) :
    ExecutionAt (Const := Const) Γ :=
  let replayed := (replay? certificate.1.1.2 certificate.1.2).get certificate.2
  ⟨certificate.1.1.1, certificate.1.1.2, replayed.1, replayed.2⟩

/-- Encode an execution by its source and its positions. -/
def encode {Γ : Ctx Base} (execution : ExecutionAt (Const := Const) Γ) :
    CheckedPositions (Const := Const) Γ :=
  ⟨(⟨execution.1, execution.2.1⟩, execution.2.2.2.positions), by simp⟩

omit [DecidableEq Base] [∀ τ, DecidableEq (Const τ)] in
theorem decode_encode {Γ : Ctx Base} (execution : ExecutionAt (Const := Const) Γ) :
    decode (encode execution) = execution := by
  obtain ⟨τ, source, target, run⟩ := execution
  simp [decode, encode]

omit [DecidableEq Base] [∀ τ, DecidableEq (Const τ)] in
theorem encode_decode {Γ : Ctx Base} (certificate : CheckedPositions (Const := Const) Γ) :
    encode (decode certificate) = certificate := by
  obtain ⟨⟨⟨τ, source⟩, positions⟩, checked⟩ := certificate
  apply Subtype.ext
  simp only [encode, decode]
  congr 1
  exact positions_of_replay? (Option.some_get checked).symm

omit [DecidableEq Base] [∀ τ, DecidableEq (Const τ)] in
theorem encode_subst {Γ Γ' : Ctx Base} (θ : Subst Const Γ Γ')
    (execution : ExecutionAt (Const := Const) Γ) :
    encode (execution.subst θ) = (encode execution).subst θ := by
  apply Subtype.ext
  simp [encode, subst, ExecutionAt.subst]

end CheckedPositions

variable (Base Const) in
/-- The explicit conversion evidence as a presheaf: substitution acts on the
source and leaves the positions unchanged. -/
def positionFace :
    Mettapedia.Computability.ComputationalTrinity.Face.{u, max u v, max (u + 1) v w}
      (SubstContext Base Const) where
  obj context := ULift.{max (u + 1) v w} (CheckedPositions (Const := Const) context.unop.ctx)
  map θ := TypeCat.ofHom (fun certificate => ⟨certificate.down.subst θ.unop⟩)
  map_id _ := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    rintro ⟨⟨⟨⟨τ, source⟩, positions⟩, checked⟩⟩
    apply congrArg ULift.up
    apply Subtype.ext
    change ((⟨τ, HOL.subst Subst.id source⟩, positions) :
      (Σ τ : Ty Base, Term Const _ τ) × List Position) = (⟨τ, source⟩, positions)
    rw [HOL.subst_id]
  map_comp f g := by
    apply CategoryTheory.ConcreteCategory.hom_ext
    rintro ⟨certificate⟩
    apply congrArg ULift.up
    apply Subtype.ext
    simp only [CheckedPositions.subst]
    congr 2
    exact (HOL.subst_comp g.unop f.unop _).symm

variable (Base Const) in
/-- **Tier-0 evidence is the operational face.** Checked position lists and
executions are naturally isomorphic presheaves on the substitution category. -/
def programIsoPositions : programFace.{u, v, w} Base Const ≅ positionFace.{u, v, w} Base Const where
  hom :=
    { app := fun _ => TypeCat.ofHom fun execution => ⟨CheckedPositions.encode execution.down⟩
      naturality := by
        intro source target θ
        apply CategoryTheory.ConcreteCategory.hom_ext
        rintro ⟨execution⟩
        exact congrArg ULift.up (CheckedPositions.encode_subst θ.unop execution) }
  inv :=
    { app := fun _ => TypeCat.ofHom fun certificate => ⟨CheckedPositions.decode certificate.down⟩
      naturality := by
        intro source target θ
        apply CategoryTheory.ConcreteCategory.hom_ext
        rintro ⟨certificate⟩
        apply congrArg ULift.up
        conv_lhs => rw [← CheckedPositions.encode_decode certificate]
        change CheckedPositions.decode ((CheckedPositions.encode _).subst θ.unop) = _
        rw [← CheckedPositions.encode_subst, CheckedPositions.decode_encode]
        rfl }
  hom_inv_id := by
    ext context ⟨execution⟩
    exact congrArg ULift.up (CheckedPositions.decode_encode execution)
  inv_hom_id := by
    ext context ⟨certificate⟩
    exact congrArg ULift.up (CheckedPositions.encode_decode certificate)

/-! ## Controls -/

namespace Controls

open ContextualTrinity.Controls (NoConstant model model_respects)

abbrev identityOnProp : Term NoConstant [] (.prop ⇒ .prop) := .lam (.var .vz)

/-- `(λp. p) ⊤`. -/
abbrev redex : Formula NoConstant [] := .app identityOnProp .top

abbrev reduces : ConversionClaim (Formula NoConstant []) := ⟨redex, .top⟩

abbrev wrong : ConversionClaim (Formula NoConstant []) := ⟨redex, .bot⟩

theorem explicit_accepts : explicitConversion.check reduces ([[]], []) = true := by decide

theorem explicit_refuses_bad_position :
    explicitConversion.check reduces ([[.function]], []) = false := by decide

theorem fuelled_accepts : fuelledConversion.check reduces (1, 0) = true := by decide

theorem fuelled_refuses_short_budget : fuelledConversion.check reduces (0, 0) = false := by
  decide

/-- One fuelled article: from the axiom `(λp. p) ⊤`, conclude `⊤`. -/
theorem fuelled_article_accepted :
    ((fuelledTier [redex]).checker (fun _ => 1)).check .top
      (.convert redex (.base 0) (1, 0)) = true := by decide +kernel

/-- No explicit evidence joins `(λp. p) ⊤` with `⊥`: the standard model
separates them. -/
theorem explicit_refuses_wrong (evidence : List Position × List Position) :
    explicitConversion.check wrong evidence = false := by
  cases accepted : explicitConversion.check wrong evidence with
  | false => rfl
  | true =>
      exfalso
      have joinable := (explicit_locallySound (Const := NoConstant) []).2 wrong evidence accepted
      have same := joinable_denote model model_respects (Γ := [])
        (valuation := fun index => nomatch index) (fun index => nomatch index) joinable
      exact same.mp trivial

/-- A checker that charges no time for a conversion that needs a step. -/
def trustedConversion : TimedChecker (ConversionClaim (Formula NoConstant [])) (Nat × Nat) :=
  { fuelledConversion with time := fun _ _ => 0 }

/-- No elaboration of the free checker into the explicit tier writes within
its time: the explicit tier needs at least one position. -/
theorem trusted_not_traceBounded
    (elaboration : Elaboration trustedConversion.toChecker
      (explicitConversion (Const := NoConstant) (Γ := [])).toChecker) :
    ¬ elaboration.TraceBounded := by
  apply not_traceBounded_of_fast elaboration (claim := reduces) (certificate := (1, 0))
  · decide
  · rintro ⟨left, right⟩ accepted
    change 0 < left.length + right.length
    rcases left with _ | ⟨_, _⟩
    · rcases right with _ | ⟨_, _⟩
      · exact absurd accepted (by decide)
      · simp
    · simp

open Mettapedia.Computability.FragmentwiseComputationalTrinity in
/-- Executions whose first step contracts a root redex. Positions are
substitution-invariant, so this is a contextual constraint. -/
def rootFirst : Constraint (programFace.{0, 0, 0} Unit NoConstant) where
  holds _ execution := execution.down.2.2.2.positions.head? = some []
  map_closed θ := by
    rintro ⟨⟨τ, before, after, run⟩⟩ holds
    change (run.subst θ.unop).positions.head? = some []
    rw [Execution.positions_subst]
    exact holds

open Mettapedia.Computability.FragmentwiseComputationalTrinity in
/-- **Execution order stays on the presentation.** No requirement on the
extensional face, pulled back to executions, selects the executions that start
at the root. -/
theorem executionOrder_not_extensional
    (requirement : Constraint ContextualTrinity.Controls.trinity.space) :
    ¬ rootFirst.Equivalent
      (requirement.pullback ContextualTrinity.Controls.trinity.programToSpace) :=
  Constraint.not_equivalent_pullback_of_separates_fibre _ _ _
    ContextualTrinity.Controls.same_meaning rfl (by
      change ¬ (ContextualTrinity.Controls.innerFirst.positions.head? = some [])
      simp [ContextualTrinity.Controls.innerFirst, Execution.positions, BetaStep.position])

/-! ### The compression gap -/

open BetaNormalization

/-- `(λp. p) ((λp. p) (… ⊤))` with `n` redexes. -/
def chain : Nat → Formula NoConstant []
  | 0 => .top
  | n + 1 => .app identityOnProp (chain n)

/-- Every step of a chain removes exactly one redex. -/
theorem chain_step (n : Nat) : ∀ {target : Formula NoConstant []},
    Reduces (chain (n + 1)) target → target = chain n := by
  induction n with
  | zero =>
      intro target reduces
      rcases app_cases reduces with ⟨body, isLam, rfl⟩ | ⟨function', inner, rfl⟩ |
          ⟨argument', inner, rfl⟩
      · cases isLam
        rfl
      · obtain ⟨body', bodyStep, rfl⟩ := lam_cases inner
        exact absurd bodyStep (var_irreducible _ _)
      · exact absurd inner (top_irreducible _)
  | succ n ih =>
      intro target reduces
      rcases app_cases reduces with ⟨body, isLam, rfl⟩ | ⟨function', inner, rfl⟩ |
          ⟨argument', inner, rfl⟩
      · cases isLam
        rfl
      · obtain ⟨body', bodyStep, rfl⟩ := lam_cases inner
        exact absurd bodyStep (var_irreducible _ _)
      · rw [ih inner]
        rfl

/-- Every execution from a chain of `n` redexes to `⊤` has exactly `n` steps,
whatever order it contracts them in. -/
theorem chain_execution_length {source target : Formula NoConstant []}
    (execution : Execution source target) :
    ∀ n, source = chain n → target = .top → execution.length = n := by
  induction execution with
  | done term =>
      intro n sources targets
      subst targets
      cases n with
      | zero => rfl
      | succ n => simp [chain] at sources
  | step first rest ih =>
      intro n sources targets
      subst sources
      cases n with
      | zero => exact absurd ⟨first⟩ (top_irreducible _)
      | succ n =>
          have middle := chain_step n ⟨first⟩
          simp only [Execution.length, ih n middle targets]

theorem normalize_chain (budget extra : Nat) :
    normalize budget (chain (budget + extra)) = chain extra := by
  induction budget with
  | zero => simp [normalize]
  | succ budget ih =>
      rw [show budget + 1 + extra = (budget + extra) + 1 by omega]
      simp only [normalize, chain, reduceLeftmost?, rootStep?, lamStep?]
      exact ih

abbrev chainClaim (n : Nat) : ConversionClaim (Formula NoConstant []) := ⟨chain n, .top⟩

theorem fuelled_accepts_chain (n : Nat) : fuelledConversion.check (chainClaim n) (n, 0) = true := by
  have reduced := normalize_chain n 0
  simp only [Nat.add_zero] at reduced
  exact decide_eq_true (by simp [reduced, normalize, chain])

/-- Every explicit certificate for a chain lists at least one position per
redex. -/
theorem explicit_chain_size (n : Nat) (evidence : List Position × List Position)
    (accepted : (explicitConversion (Const := NoConstant) (Γ := [])).check (chainClaim n) evidence = true) :
    n ≤ (explicitConversion (Const := NoConstant) (Γ := [])).certificateSize evidence := by
  change explicitCheck (Const := NoConstant) (Γ := []) (chainClaim n) evidence = true at accepted
  rw [explicitCheck_eq_true_iff (Const := NoConstant)] at accepted
  obtain ⟨meet, leftMeet, rightMeet⟩ := accepted
  obtain ⟨⟨leftEnd, leftRun⟩, leftReplayed, leftSame⟩ := Option.map_eq_some_iff.mp leftMeet
  obtain ⟨⟨rightEnd, rightRun⟩, _, rightSame⟩ := Option.map_eq_some_iff.mp rightMeet
  simp only at leftSame rightSame
  subst leftSame rightSame
  have topNormal : Normal (Const := NoConstant) (Γ := []) Term.top :=
    fun target => top_irreducible target
  have rightIsTop := eq_of_normal_star topNormal (execution_star rightRun)
  have length := chain_execution_length leftRun n rfl rightIsTop
  have positions := positions_of_replay? leftReplayed
  have counted := Execution.length_positions leftRun
  rw [positions, length] at counted
  change n ≤ evidence.1.length + evidence.2.length
  omega

/-- **The compression gap.** A fuelled certificate of `b` bits for the chain of
`n` redexes is accepted, and every accepted explicit certificate has at least
`n ≥ (2^b - 1)/2` positions: explicit evidence is exponentially larger than the
fuelled proof, and `fuelledElaboration_size` shows this is the worst case. -/
theorem compression_gap (n : Nat) :
    fuelledConversion.check (chainClaim n) (n, 0) = true ∧
      (fuelledConversion (Const := NoConstant) (Γ := [])).certificateSize (n, 0) = Nat.size n ∧
      ∀ evidence, (explicitConversion (Const := NoConstant) (Γ := [])).check (chainClaim n) evidence = true →
        2 ^ ((fuelledConversion (Const := NoConstant) (Γ := [])).certificateSize (n, 0)) ≤
          2 * (explicitConversion (Const := NoConstant) (Γ := [])).certificateSize evidence + 1 := by
  refine ⟨fuelled_accepts_chain n, by simp [fuelledConversion], fun evidence accepted => ?_⟩
  have lower := explicit_chain_size n evidence accepted
  change 2 ^ (Nat.size n + Nat.size 0) ≤ _
  rw [Nat.size_zero, Nat.add_zero]
  rcases Nat.eq_zero_or_pos n with zero | positive
  · subst zero
    simp
  · have half : 2 ^ (Nat.size n - 1) ≤ n :=
      Nat.lt_size.mp (Nat.sub_lt (Nat.size_pos.mpr positive) Nat.one_pos)
    have sized : Nat.size n = (Nat.size n - 1) + 1 := (Nat.sub_add_cancel (Nat.size_pos.mpr positive)).symm
    rw [sized, pow_succ]
    omega

theorem normalSteps_chain (n : Nat) : normalSteps (chain n) = n := by
  unfold normalSteps
  rw [Nat.find_eq_iff]
  constructor
  · have reduced := normalize_chain n 0
    simp only [Nat.add_zero] at reduced
    simp [reduced, chain, reduceLeftmost?]
  · intro m smaller
    obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_lt smaller
    rw [show m + extra + 1 = m + (extra + 1) by omega, normalize_chain]
    simp [chain, reduceLeftmost?, rootStep?, lamStep?]

/-- **Elaborating explicit evidence into budgets is not trace-bounded.** The
empty explicit certificate of `chain 2 = chain 2` is checked in one unit, while
the least budgets for each side are `2`. -/
theorem explicitAboveFuelled_not_writes : ¬ (explicitAboveFuelled (Const := NoConstant) (Γ := []) []).Writes := by
  intro writes
  have produced : (explicitAboveFuelled (Const := NoConstant) (Γ := []) []).conversionElaboration.elaborate
      ⟨chain 2, chain 2⟩ ([], []) = some (normalSteps (chain 2), normalSteps (chain 2)) := by
    simp only [explicitAboveFuelled, explicitElaboration]
    rw [if_pos (by decide)]
  have bounded := writes.2 _ _ _ produced
  rw [normalSteps_chain] at bounded
  change Nat.size 2 + Nat.size 2 ≤ 0 + 0 + 1 at bounded
  exact absurd bounded (by decide)

end Controls

#print axioms fuelledAboveExplicit
#print axioms fuelled_locallySound
#print axioms fuelledAboveExplicit_writes
#print axioms derivable_models
#print axioms fuelled_accepted_models
#print axioms programIsoPositions
#print axioms ContextualTrinity.replay?_normalOrder
#print axioms ContextualTrinity.stepAt?_subst
#print axioms Controls.explicit_refuses_wrong
#print axioms Controls.trusted_not_traceBounded
#print axioms Controls.fuelled_article_accepted
#print axioms Controls.executionOrder_not_extensional
#print axioms explicitAboveFuelled
#print axioms joinable_iff_normalForm
#print axioms fuelled_iff_explicit
#print axioms fuelledElaboration_size
#print axioms Controls.compression_gap
#print axioms Controls.explicitAboveFuelled_not_writes

end Mettapedia.Logic.HOL.ConversionTiers
