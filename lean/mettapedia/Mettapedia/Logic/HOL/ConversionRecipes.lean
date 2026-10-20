import Mettapedia.Logic.EqualityRecipe
import Mettapedia.Logic.HOL.ConversionElaboration
import Mettapedia.Logic.HOL.ConversionTiers
import Mettapedia.GSLT.Core.IndexedOperational
import Mettapedia.GSLT.LanguageDef.HeuristicEvidence

/-!
# Checked conversion recipes with explicit HOL proof elaboration

The submitted recipe retains its composition tree and local evidence. Beta
leaves cite redex positions, eta leaves cite an arrow term, and equation
leaves cite a licensed declaration and a substitution at its telescope.
Policies independently enable beta, eta and individual declarations. The
checker verifies the actual endpoints, including every transitivity join.

The independent local judgment includes beta, eta and substitution instances
of the declared equations, with explicit typed substitution contexts and binder
congruence. A substitution context may use its argument repeatedly; its
logical step is not necessarily one evaluator contraction. Its equivalence closure is exactly the accepted recipe judgment.
This is not a normalization algorithm, and no total conversion decision for
arbitrary admitted equations is assumed.

Successful replay reconstructs the original evidence tree through the common
free-conversion interface, then computes an ordinary retained HOL proof. The
same proof can justify logical retyping. All syntax here is already scoped
and typed; a byte decoder and native capability implementation are separate
boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ConversionRecipes

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open ContextualTrinity

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Conversion options select computation, independently of which equations
already have ordinary HOL proofs. -/
structure Policy (Base : Type u) (declarations : Nat) where
  beta : Ty Base → Bool
  eta : Ty Base → Ty Base → Bool
  equation : Fin declarations → Bool

def Policy.betaOnly (declarations : Nat) : Policy Base declarations :=
  ⟨fun _ => true, fun _ _ => false, fun _ => false⟩

def Policy.betaEta (declarations : Nat) : Policy Base declarations :=
  ⟨fun _ => true, fun _ _ => true, fun _ => false⟩

def Policy.all (declarations : Nat) : Policy Base declarations :=
  ⟨fun _ => true, fun _ _ => true, fun _ => true⟩

/-- Recover the arrow's domain and codomain from the typed eta witness. -/
def Policy.etaAt {declarations : Nat} (policy : Policy Base declarations)
    {Γ : Ctx Base} {σ τ : Ty Base} (_function : Term Const Γ (σ ⇒ τ)) : Bool :=
  policy.eta σ τ

/-- A graph edge admits every local computation admitted at its source.
Theory axioms and implementation costs are not fields of this relation. -/
structure Policy.Extends {declarations : Nat} (small large : Policy Base declarations) : Prop where
  beta : ∀ τ, small.beta τ = true → large.beta τ = true
  eta : ∀ σ τ, small.eta σ τ = true → large.eta σ τ = true
  equation : ∀ index, small.equation index = true → large.equation index = true

theorem Policy.Extends.refl {declarations : Nat} (policy : Policy Base declarations) :
    policy.Extends policy := ⟨fun _ h => h, fun _ _ h => h, fun _ h => h⟩

theorem Policy.Extends.trans {declarations : Nat} {first middle last : Policy Base declarations}
    (earlier : first.Extends middle) (later : middle.Extends last) : first.Extends last :=
  ⟨fun τ h => later.beta τ (earlier.beta τ h),
   fun σ τ h => later.eta σ τ (earlier.eta σ τ h),
   fun index h => later.equation index (earlier.equation index h)⟩

/-- Joining policies enables the union of their generators. Decidability of
the resulting conversion relation is a separate obligation. -/
def Policy.join {declarations : Nat} (first second : Policy Base declarations) :
    Policy Base declarations where
  beta τ := first.beta τ || second.beta τ
  eta σ τ := first.eta σ τ || second.eta σ τ
  equation index := first.equation index || second.equation index

theorem Policy.extends_join_left {declarations : Nat} (first second : Policy Base declarations) :
    first.Extends (first.join second) := by
  constructor
  · intro τ enabled; simp [join, enabled]
  · intro σ τ enabled; simp [join, enabled]
  · intro index enabled; simp [join, enabled]

theorem Policy.extends_join_right {declarations : Nat} (first second : Policy Base declarations) :
    second.Extends (first.join second) := by
  constructor
  · intro τ enabled; simp [join, enabled]
  · intro σ τ enabled; simp [join, enabled]
  · intro index enabled; simp [join, enabled]

/-- The union is the least policy admitting both generator families. This
does not identify its conversion with the union of their conversion classes. -/
theorem Policy.join_extends_iff {declarations : Nat} (first second upper : Policy Base declarations) :
    (first.join second).Extends upper ↔ first.Extends upper ∧ second.Extends upper := by
  constructor
  · intro combined
    exact ⟨(extends_join_left first second).trans combined,
      (extends_join_right first second).trans combined⟩
  · rintro ⟨fromFirst, fromSecond⟩
    constructor
    · intro τ enabled
      simp only [join, Bool.or_eq_true] at enabled
      exact enabled.elim (fromFirst.beta τ) (fromSecond.beta τ)
    · intro σ τ enabled
      simp only [join, Bool.or_eq_true] at enabled
      exact enabled.elim (fromFirst.eta σ τ) (fromSecond.eta σ τ)
    · intro index enabled
      simp only [join, Bool.or_eq_true] at enabled
      exact enabled.elim (fromFirst.equation index) (fromSecond.equation index)

/-- Permission is checked at the contracted redex's result type, including
when the redex sits inside a term with a different outer type. -/
def Policy.betaAllowed {declarations : Nat} (policy : Policy Base declarations) :
    {Γ : Ctx Base} → {τ : Ty Base} → {source target : Term Const Γ τ} →
      BetaStep source target → Bool
  | _, τ, _, _, .beta _ _ => policy.beta τ
  | _, _, _, _, .appFun _ inner | _, _, _, _, .appArg _ inner
  | _, _, _, _, .lam inner | _, _, _, _, .andLeft _ inner
  | _, _, _, _, .andRight _ inner | _, _, _, _, .orLeft _ inner
  | _, _, _, _, .orRight _ inner | _, _, _, _, .impLeft _ inner
  | _, _, _, _, .impRight _ inner | _, _, _, _, .not inner
  | _, _, _, _, .eqLeft _ inner | _, _, _, _, .eqRight _ inner
  | _, _, _, _, .all inner | _, _, _, _, .ex inner => policy.betaAllowed inner

theorem Policy.betaAllowed_mono {declarations : Nat} {small large : Policy Base declarations}
    (extension : small.Extends large) {Γ : Ctx Base} {τ : Ty Base}
    {source target : Term Const Γ τ} (step : BetaStep source target) :
    small.betaAllowed step = true → large.betaAllowed step = true := by
  induction step with
  | beta _ _ => exact extension.beta _
  | _ => assumption

theorem Policy.betaAllowed_betaOnly {declarations : Nat} {Γ : Ctx Base} {τ : Ty Base}
    {source target : Term Const Γ τ} (step : BetaStep source target) :
    (Policy.betaOnly (Base := Base) declarations).betaAllowed step = true := by
  induction step <;> simp_all [betaAllowed, betaOnly]

/-- Local evidence carries the original declaration occurrence and its
capture-safe substitution, rather than silently replacing a declaration by
another proof of the same endpoint equation. -/
inductive Evidence (equations : List (DefiningEquation Const)) :
    Ctx Base → Ty Base → Type (max u v) where
  | beta {Γ : Ctx Base} {τ : Ty Base} (position : Position) : Evidence equations Γ τ
  | eta {Γ : Ctx Base} {σ τ : Ty Base} (function : Term Const Γ (σ ⇒ τ)) :
      Evidence equations Γ (σ ⇒ τ)
  | equation {Γ : Ctx Base} {τ : Ty Base} (index : Fin equations.length)
      (substitution : Subst Const (equations.get index).context Γ)
      (type_eq : (equations.get index).type = τ) : Evidence equations Γ τ
  | congr {Γ : Ctx Base} {σ τ : Ty Base} (body : Term Const (σ :: Γ) τ)
      (hole : Term Const Γ σ) (inner : Evidence equations Γ σ) : Evidence equations Γ τ
  | lam {Γ : Ctx Base} {σ τ : Ty Base} (body : Term Const (σ :: Γ) τ)
      (inner : Evidence equations (σ :: Γ) τ) : Evidence equations Γ (σ ⇒ τ)
  | all {Γ : Ctx Base} {σ : Ty Base} (body : Formula Const (σ :: Γ))
      (inner : Evidence equations (σ :: Γ) .prop) : Evidence equations Γ .prop
  | ex {Γ : Ctx Base} {σ : Ty Base} (body : Formula Const (σ :: Γ))
      (inner : Evidence equations (σ :: Γ) .prop) : Evidence equations Γ .prop

/-- The independently specified primitive judgments selected by a policy.
They make no reference to the replay function. -/
inductive LocalStep (equations : List (DefiningEquation Const))
    (policy : Policy Base equations.length) :
    (Γ : Ctx Base) → {τ : Ty Base} → Term Const Γ τ → Term Const Γ τ → Prop where
  | beta {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
      (step : BetaStep source target) (enabled : policy.betaAllowed step = true) :
      LocalStep equations policy Γ source target
  | eta {Γ : Ctx Base} {σ τ : Ty Base} (enabled : policy.eta σ τ = true)
      (function : Term Const Γ (σ ⇒ τ)) :
      LocalStep equations policy Γ
        (.lam (.app (weaken function) (.var .vz))) function
  | equation {Γ : Ctx Base} (index : Fin equations.length) (enabled : policy.equation index = true)
      (substitution : Subst Const (equations.get index).context Γ) :
      LocalStep equations policy Γ
        (subst substitution (equations.get index).left)
        (subst substitution (equations.get index).right)
  | congr {Γ : Ctx Base} {σ τ : Ty Base} (body : Term Const (σ :: Γ) τ)
      {source target : Term Const Γ σ} (inner : LocalStep equations policy Γ source target) :
      LocalStep equations policy Γ (instantiate source body) (instantiate target body)
  | lam {Γ : Ctx Base} {σ τ : Ty Base} {source target : Term Const (σ :: Γ) τ}
      (inner : LocalStep equations policy (σ :: Γ) source target) :
      LocalStep equations policy Γ (.lam source) (.lam target)
  | all {Γ : Ctx Base} {σ : Ty Base} {source target : Formula Const (σ :: Γ)}
      (inner : LocalStep equations policy (σ :: Γ) source target) :
      LocalStep equations policy Γ (.all source) (.all target)
  | ex {Γ : Ctx Base} {σ : Ty Base} {source target : Formula Const (σ :: Γ)}
      (inner : LocalStep equations policy (σ :: Γ) source target) :
      LocalStep equations policy Γ (.ex source) (.ex target)

/-- An extension acts on the independently stated local judgments, including
the type selected by each inner computation and every binder change. -/
theorem LocalStep.mono {equations : List (DefiningEquation Const)}
    {small large : Policy Base equations.length} (extension : small.Extends large)
    {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (step : LocalStep equations small Γ source target) : LocalStep equations large Γ source target := by
  induction step with
  | beta step enabled => exact .beta step (Policy.betaAllowed_mono extension step enabled)
  | eta enabled function => exact .eta (extension.eta _ _ enabled) function
  | equation index enabled substitution =>
      exact .equation index (extension.equation index enabled) substitution
  | congr body _ ih => exact .congr body ih
  | lam _ ih => exact .lam ih
  | all _ ih => exact .all ih
  | ex _ ih => exact .ex ih

theorem LocalStep.conversion_mono {equations : List (DefiningEquation Const)}
    {small large : Policy Base equations.length} (extension : small.Extends large)
    {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (conversion : Relation.EqvGen (LocalStep equations small Γ) source target) :
    Relation.EqvGen (LocalStep equations large Γ) source target := by
  induction conversion with
  | rel _ _ step => exact .rel _ _ (step.mono extension)
  | refl term => exact .refl term
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-- A replay result retains both the independently licensed step and its
ordinary HOL equality evidence. -/
structure Result (equations : List (DefiningEquation Const))
    (policy : Policy Base equations.length) {Γ : Ctx Base} {τ : Ty Base}
    (source : Term Const Γ τ) where
  target : Term Const Γ τ
  licensed : LocalStep equations policy Γ source target
  proof : ProofSyntax Const [] (.eq source target)

variable [DecidableEq Base] [∀ τ, DecidableEq (Const τ)]

/-- Checked local elaboration. Failed policies, positions or source matches
refuse before yielding any equality evidence. -/
def replayLeaf {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) (policy : Policy Base equations.length) :
    {Γ : Ctx Base} → {τ : Ty Base} → (source : Term Const Γ τ) →
      Evidence equations Γ τ → Option (Result equations policy source)
  | _, _, source, .beta position =>
      match stepAt? source position with
      | none => none
      | some found =>
          if enabled : policy.betaAllowed found.2 = true then
            some
              { target := found.1
                licensed := .beta found.2 enabled
                proof := found.2.proof [] }
          else none
  | _, _, source, .eta function =>
      if enabled : policy.etaAt function = true then
        if same : source = .lam (.app (weaken function) (.var .vz)) then
          some
            { target := function
              licensed := same.symm ▸ LocalStep.eta enabled function
              proof := same.symm ▸ ProofSyntax.eta function }
        else none
      else none
  | _, _, source, .equation index substitution typeEq => by
      cases typeEq
      exact if enabled : policy.equation index = true then
        if same : source = subst substitution (equations.get index).left then
          some
            { target := subst substitution (equations.get index).right
              licensed := same.symm ▸ LocalStep.equation index enabled substitution
              proof := same.symm ▸ licensed.instantiate (equations.get index)
                (List.get_mem _ _) substitution [] }
        else none
      else none
  | _, _, source, .congr body hole inner =>
      if same : source = instantiate hole body then
        match replayLeaf licensed policy hole inner with
        | none => none
        | some result => some
            { target := instantiate result.target body
              licensed := same.symm ▸ LocalStep.congr body result.licensed
              proof := same.symm ▸ holeCongr body result.proof }
      else none
  | _, _, source, .lam body inner =>
      if same : source = .lam body then
        match replayLeaf licensed policy body inner with
        | none => none
        | some result => some
            { target := .lam result.target
              licensed := same.symm ▸ LocalStep.lam result.licensed
              proof := same.symm ▸ ProofSyntax.eqLam result.proof }
      else none
  | _, _, source, .all body inner =>
      if same : source = .all body then
        match replayLeaf licensed policy body inner with
        | none => none
        | some result => some
            { target := .all result.target
              licensed := same.symm ▸ LocalStep.all result.licensed
              proof := same.symm ▸ allCongr (Δ := []) result.proof }
      else none
  | _, _, source, .ex body inner =>
      if same : source = .ex body then
        match replayLeaf licensed policy body inner with
        | none => none
        | some result => some
            { target := .ex result.target
              licensed := same.symm ▸ LocalStep.ex result.licensed
              proof := same.symm ▸ exCongr (Δ := []) result.proof }
      else none

def leafChecker {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) (policy : Policy Base equations.length)
    (Γ : Ctx Base) (τ : Ty Base) :
    Checker (Term Const Γ τ × Term Const Γ τ) (Evidence equations Γ τ) where
  check claim evidence :=
    match replayLeaf licensed policy claim.1 evidence with
    | none => false
    | some result => decide (result.target = claim.2)

/-- Recover the checked local result at exactly the requested target. -/
def leafResult {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) (policy : Policy Base equations.length)
    {Γ : Ctx Base} {τ : Ty Base} (source target : Term Const Γ τ)
    (evidence : Evidence equations Γ τ)
    (accepted : (leafChecker licensed policy Γ τ).check (source, target) evidence = true) :
    { result : Result equations policy source // result.target = target } := by
  cases found : replayLeaf licensed policy source evidence with
  | none => simp [leafChecker, found] at accepted
  | some result =>
      exact ⟨result, by simpa [leafChecker, found] using accepted⟩

private theorem leafCheck_iff {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) (policy : Policy Base equations.length)
    {Γ : Ctx Base} {τ : Ty Base} (source target : Term Const Γ τ)
    (evidence : Evidence equations Γ τ) :
    (leafChecker licensed policy Γ τ).check (source, target) evidence = true ↔
      ∃ result, replayLeaf licensed policy source evidence = some result ∧ result.target = target := by
  cases found : replayLeaf licensed policy source evidence <;> simp [leafChecker, found]

theorem localStep_complete {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) (policy : Policy Base equations.length)
    {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (step : LocalStep equations policy Γ source target) :
    ∃ evidence, (leafChecker licensed policy Γ τ).check (source, target) evidence = true := by
  induction step with
  | beta step enabled =>
      exact ⟨.beta step.position, by
        simp [leafChecker, replayLeaf, enabled, stepAt?_position]⟩
  | eta enabled function =>
      exact ⟨.eta function, by simp [leafChecker, replayLeaf, Policy.etaAt, enabled]⟩
  | equation index enabled substitution =>
      exact ⟨.equation index substitution rfl, by simp [leafChecker, replayLeaf, enabled]⟩
  | @congr Γ σ τ body source target inner ih =>
      obtain ⟨evidence, accepted⟩ := ih
      obtain ⟨result, found, equal⟩ := (leafCheck_iff licensed policy source target evidence).1 accepted
      exact ⟨.congr body source evidence, by simp [leafChecker, replayLeaf, found, equal]⟩
  | @lam Γ σ τ source target inner ih =>
      obtain ⟨evidence, accepted⟩ := ih
      obtain ⟨result, found, equal⟩ := (leafCheck_iff licensed policy source target evidence).1 accepted
      exact ⟨.lam source evidence, by simp [leafChecker, replayLeaf, found, equal]⟩
  | @all Γ σ source target inner ih =>
      obtain ⟨evidence, accepted⟩ := ih
      obtain ⟨result, found, equal⟩ := (leafCheck_iff licensed policy source target evidence).1 accepted
      exact ⟨.all source evidence, by simp [leafChecker, replayLeaf, found, equal]⟩
  | @ex Γ σ source target inner ih =>
      obtain ⟨evidence, accepted⟩ := ih
      obtain ⟨result, found, equal⟩ := (leafCheck_iff licensed policy source target evidence).1 accepted
      exact ⟨.ex source evidence, by simp [leafChecker, replayLeaf, found, equal]⟩

theorem leaf_authority {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) (policy : Policy Base equations.length)
    (Γ : Ctx Base) (τ : Ty Base) :
    (leafChecker licensed policy Γ τ).Authority
      (fun claim => LocalStep equations policy Γ claim.1 claim.2) where
  sound claim evidence accepted := by
    let result := leafResult licensed policy claim.1 claim.2 evidence accepted
    change LocalStep equations policy Γ claim.1 claim.2
    rw [← result.2]
    exact result.1.licensed
  complete _ step := localStep_complete licensed policy step

abbrev Recipe (equations : List (DefiningEquation Const)) (Γ : Ctx Base) (τ : Ty Base) :=
  EqualityRecipe.Recipe (Term Const Γ τ) (Evidence equations Γ τ)

def checker {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) (policy : Policy Base equations.length)
    (Γ : Ctx Base) (τ : Ty Base) :=
  EqualityRecipe.checker (leafChecker licensed policy Γ τ)

/-- The recipe checker has exact authority for the equivalence closure of
the selected primitive judgments, including their actual equation policy. -/
theorem authority {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) (policy : Policy Base equations.length)
    (Γ : Ctx Base) (τ : Ty Base) :
    (checker licensed policy Γ τ).Authority
      (fun claim => Relation.EqvGen (LocalStep equations policy Γ) claim.1 claim.2) :=
  EqualityRecipe.authority _ (leaf_authority licensed policy Γ τ)

/-- Existing typed executions become recipes by retaining every actual
contracted position. No new reduction engine is introduced. -/
def betaStepRecipe (equations : List (DefiningEquation Const))
    {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (step : BetaStep source target) : Recipe equations Γ τ :=
  .leaf source target (.beta step.position)

def executionRecipe (equations : List (DefiningEquation Const)) :
    {Γ : Ctx Base} → {τ : Ty Base} → {source target : Term Const Γ τ} →
      Execution source target → Recipe equations Γ τ
  | _, _, _, _, .done term => .refl term
  | _, _, _, _, .step head tail =>
      .trans (betaStepRecipe equations head) (executionRecipe equations tail)

/-- The maintained operational execution is accepted by the beta-only
profile, including reductions under logical constructors and binders. -/
theorem executionRecipe_checked {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) {Γ : Ctx Base} {τ : Ty Base}
    {source target : Term Const Γ τ} (execution : Execution source target) :
    (checker licensed (.betaOnly _) Γ τ).check (source, target)
      (executionRecipe equations execution) = true := by
  induction execution with
  | done term => simp [executionRecipe, checker, EqualityRecipe.checker, EqualityRecipe.evaluate]
  | @step source middle target head rest ih =>
      simp only [executionRecipe, betaStepRecipe, checker]
      apply EqualityRecipe.trans_checked (leafChecker licensed (.betaOnly _) Γ τ)
        (.leaf source middle (.beta head.position)) (executionRecipe equations rest)
        source middle target
      · simp [EqualityRecipe.checker, EqualityRecipe.evaluate, leafChecker, replayLeaf,
          stepAt?_position, Policy.betaAllowed_betaOnly]
      · exact ih

/-- Every equality accepted by the previous beta-execution observation has
an article at this checking boundary. Reverse reflection needs its own law. -/
theorem joinable_has_betaRecipe {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) {Γ : Ctx Base} {τ : Ty Base}
    {source target : Term Const Γ τ} (joinable : ConversionTiers.Joinable source target) :
    ∃ recipe, (checker licensed (.betaOnly _) Γ τ).check (source, target) recipe = true := by
  obtain ⟨meet, ⟨first⟩, ⟨second⟩⟩ := joinable
  refine ⟨.trans (executionRecipe equations first) (.symm (executionRecipe equations second)), ?_⟩
  exact EqualityRecipe.trans_checked _ _ _ source meet target
    (executionRecipe_checked licensed first)
    (EqualityRecipe.symm_checked _ _ _ _ (executionRecipe_checked licensed second))

private def proofAlgebra {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) (policy : Policy Base equations.length)
    (Γ : Ctx Base) (τ : Ty Base) (assumptions : List (Formula Const Γ)) :
    Mettapedia.TypeTheory.FreeConversion.Algebra (fun _ : Unit => Term Const Γ τ)
      (fun {_index : Unit} (source target : Term Const Γ τ) =>
        EqualityRecipe.AcceptedLeaf (leafChecker licensed policy Γ τ) source target)
      (fun {_index : Unit} (source target : Term Const Γ τ) =>
        ProofSyntax Const assumptions (.eq source target)) where
  onStep {_index} {source target} evidence := by
    let result := leafResult licensed policy source target evidence.1 evidence.2
    have proof := result.1.proof
    rw [result.2] at proof
    exact ProofSyntax.mono (Δ := [])
      { index := fun i => Fin.elim0 i
        get_eq := fun i => Fin.elim0 i } proof
  onRefl term := .eqRefl term
  onSymm proof := .eqSymm proof
  onTrans first second := .eqTrans first second

/-- Reconstruct actual retained HOL evidence from the accepted submitted
recipe. The generic decoder preserves the entire recipe before this fold. -/
def elaborate {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) (policy : Policy Base equations.length)
    {Γ : Ctx Base} {τ : Ty Base} (source target : Term Const Γ τ)
    (recipe : Recipe equations Γ τ)
    (accepted : (checker licensed policy Γ τ).check (source, target) recipe = true)
    (assumptions : List (Formula Const Γ)) :
    ProofSyntax Const assumptions (.eq source target) :=
  (proofAlgebra licensed policy Γ τ assumptions).fold
    (EqualityRecipe.checkedPath _ recipe source target
      ((EqualityRecipe.check_iff _ _ _).mp accepted))

/-- Replacing a conversion cast with the generated equality evidence gives a
retained proof of the original logical conclusion. -/
def convertProof {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) (policy : Policy Base equations.length)
    {Γ : Ctx Base} {assumptions : List (Formula Const Γ)}
    {source target : Formula Const Γ} (recipe : Recipe equations Γ .prop)
    (accepted : (checker licensed policy Γ .prop).check (source, target) recipe = true)
    (proof : ProofSyntax Const assumptions source) : ProofSyntax Const assumptions target :=
  .impE (.eqPropEL (elaborate licensed policy source target recipe accepted assumptions)) proof

/-- A proof-producing entry point returns evidence only for a successfully
checked submission. Producer failure is separate from logical refutation. -/
def elaborate? {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) (policy : Policy Base equations.length)
    {Γ : Ctx Base} {τ : Ty Base} (source target : Term Const Γ τ)
    (recipe : Recipe equations Γ τ) (assumptions : List (Formula Const Γ)) :
    Option (ProofSyntax Const assumptions (.eq source target)) :=
  if accepted : (checker licensed policy Γ τ).check (source, target) recipe = true then
    some (elaborate licensed policy source target recipe accepted assumptions)
  else none

theorem elaborate?_isSome {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) (policy : Policy Base equations.length)
    {Γ : Ctx Base} {τ : Ty Base} (source target : Term Const Γ τ)
    (recipe : Recipe equations Γ τ) (assumptions : List (Formula Const Γ)) :
    (elaborate? licensed policy source target recipe assumptions).isSome =
      (checker licensed policy Γ τ).check (source, target) recipe := by
  unfold elaborate?
  split <;> simp_all

open Mettapedia.GSLT Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-- Each context, simple result type and conversion policy determines one
operational observation fibre, on the original intrinsic HOL terms. -/
abbrev theory (equations : List (DefiningEquation Const))
    (policy : Policy Base equations.length) (Γ : Ctx Base) (τ : Ty Base) : GSLT :=
  conversionTheory (LocalStep equations policy Γ (τ := τ))

def nativeType (equations : List (DefiningEquation Const))
    (policy : Policy Base equations.length) {Γ : Ctx Base} {τ : Ty Base}
    (target : Term Const Γ τ) : GSLTNativeType (theory equations policy Γ τ) :=
  conversionNativeType (LocalStep equations policy Γ) target

/-- The native reachability observation is exactly certificate existence for
the selected policy. It does not identify the retained certificates. -/
theorem observed_iff_accepted {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) (policy : Policy Base equations.length)
    {Γ : Ctx Base} {τ : Ty Base} (source target : Term Const Γ τ) :
    (gsltOSLF (theory equations policy Γ τ)).satisfies (S := ()) source
      (nativeType equations policy target).pred ↔
    ∃ recipe, (checker licensed policy Γ τ).check (source, target) recipe = true :=
  (satisfies_conversionNativeType_iff (LocalStep equations policy Γ) source target).trans
    ((authority licensed policy Γ τ).meaning_iff_exists_certificate (source, target))

omit [DecidableEq Base] [∀ τ, DecidableEq (Const τ)] in
/-- Policy edges preserve the selected observation. They do not claim
reflection, identical execution histories or bounded compilation expense. -/
theorem observed_mono {equations : List (DefiningEquation Const)}
    {small large : Policy Base equations.length} (extension : small.Extends large)
    {Γ : Ctx Base} {τ : Ty Base} {source target : Term Const Γ τ}
    (observed : (gsltOSLF (theory equations small Γ τ)).satisfies (S := ()) source
      (nativeType equations small target).pred) :
    (gsltOSLF (theory equations large Γ τ)).satisfies (S := ()) source
      (nativeType equations large target).pred :=
  (satisfies_conversionNativeType_iff (LocalStep equations large Γ) source target).2
    (LocalStep.conversion_mono extension
      ((satisfies_conversionNativeType_iff (LocalStep equations small Γ) source target).1 observed))

/-- Tactics, instance search or implicit-argument producers may propose any
finite list. A selected submission still passes the original policy checker
before its equality proof can be returned. -/
def elaborateSubmission {equations : List (DefiningEquation Const)}
    (licensed : EquationProofs equations) (policy : Policy Base equations.length)
    {Γ : Ctx Base} {τ : Ty Base}
    (producer : (Term Const Γ τ × Term Const Γ τ) → List (Recipe equations Γ τ))
    (source target : Term Const Γ τ) (recipe : Recipe equations Γ τ)
    (selected : recipe ∈ Mettapedia.GSLT.LanguageDef.HeuristicEvidence.screen
      (checker licensed policy Γ τ) (source, target) (producer (source, target)))
    (assumptions : List (Formula Const Γ)) :
    ProofSyntax Const assumptions (.eq source target) :=
  elaborate licensed policy source target recipe
    ((Mettapedia.GSLT.LanguageDef.HeuristicEvidence.mem_screen _ _ _ _).1 selected).2 assumptions

end Mettapedia.Logic.HOL.ConversionRecipes
