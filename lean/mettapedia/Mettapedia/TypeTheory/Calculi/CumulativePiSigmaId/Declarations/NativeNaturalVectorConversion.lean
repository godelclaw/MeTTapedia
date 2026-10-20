import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorAnnotated
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstructorSystemDevelopment
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveTelescopeSpine
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativePreservation

/-!
# Structural conversion in the natural-only checking policy

The selected two original rows form a constructor system. Its confluence and
conversion boundaries concern the raw structural judgment used by the
formation-sensitive checker. They do not supply typed eta equality, annotated
former facts or subject preservation merely by erasure. The independently
selected operational iota roots preserve this smaller checking judgment;
their unrestricted dependent contextual closure is a separate obligation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
namespace Programs.ComputationProfiles.NaturalConversion

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open ConstructorSystem AlgebraicSchema ConversionCoherence

inductive Schema : {arity : Nat} → Tower.Tm arity → Tower.Tm arity → Prop where
  | zero : Schema natZeroIotaLeft natZeroIotaRight
  | successor : Schema natSuccIotaLeft natSuccIotaRight

/-- The support comes from the original permitted ordinals, with no new row. -/
theorem schema_iff {arity : Nat} {left right : Tower.Tm arity} :
    Schema left right ↔ Annotated.family naturalOnly left right := by
  constructor
  · intro rule
    cases rule with
    | zero => exact ⟨⟨0, by decide⟩, rfl, rfl⟩
    | successor => exact ⟨⟨1, by decide⟩, rfl, rfl⟩
  · rintro ⟨index, permitted, row⟩
    fin_cases index
    · change (⟨3, natZeroIotaLeft, natZeroIotaRight⟩ :
        Σ k, Tower.Tm k × Tower.Tm k) = ⟨arity, left, right⟩ at row
      cases row
      exact .zero
    · change (⟨4, natSuccIotaLeft, natSuccIotaRight⟩ :
        Σ k, Tower.Tm k × Tower.Tm k) = ⟨arity, left, right⟩ at row
      cases row
      exact .successor
    · cases permitted
    · cases permitted

theorem roots_exact {n : Nat} {left right : Tower.Tm n} :
    (rules naturalOnly).computation.step left right ↔ SchemaStep Schema left right := by
  constructor
  · intro step
    cases (Annotated.presentation naturalOnly).mp step with
    | instantiate rule substitution => exact .instantiate (schema_iff.mpr rule) substitution
  · intro step
    apply (Annotated.presentation naturalOnly).mpr
    cases step with
    | instantiate rule substitution => exact .instantiate (schema_iff.mp rule) substitution

def defined (name : DeclName) : Prop := name = natEliminateName

theorem schema_left {arity : Nat} {left right : Tower.Tm arity} (rule : Schema left right) :
    ∃ name, defined name ∧ 0 < (4 : Nat) ∧ LeftSide defined left name 4 := by
  cases rule with
  | zero =>
      exact ⟨natEliminateName, rfl, by decide,
        .app (.app (.app (.app (.const _) (.var 2)) (.var 1)) (.var 0))
          (.const (by change zeroName ≠ natEliminateName; decide))⟩
  | successor =>
      exact ⟨natEliminateName, rfl, by decide,
        .app (.app (.app (.app (.const _) (.var 3)) (.var 2)) (.var 1))
          (.app (.const (by change succName ≠ natEliminateName; decide)) (.var 0))⟩

theorem covered {arity : Nat} {left right : Tower.Tm arity} (rule : Schema left right) :
    ∀ index, 0 < variableMultiplicity index right → 0 < variableMultiplicity index left := by
  cases rule <;> intro index _ <;> fin_cases index <;> decide

theorem disjoint {arity other : Nat} {left right : Tower.Tm arity}
    {left' right' : Tower.Tm other} (first : Schema left right) (second : Schema left' right')
    (matching : unifiable left left' = true) :
    (⟨arity, left, right⟩ : Σ k, Tower.Tm k × Tower.Tm k) = ⟨other, left', right'⟩ := by
  cases first <;> cases second
  · rfl
  · cases matching
  · cases matching
  · rfl

def system : System Tower.Head where
  schema := Schema
  defined := defined
  arity := fun _ => 4
  left := schema_left
  linear := by
    intro arity left right rule index
    cases rule <;> fin_cases index <;> decide
  covered := covered
  determined := determined_of_disjoint
    (fun rule => let ⟨name, _, _, side⟩ := schema_left rule; ⟨name, 4, side⟩) covered disjoint

def presentation : ConstructorPresentation (rules naturalOnly) where
  presentation := AlgebraicParallel.SchemaFamily.presentation Schema (rules naturalOnly) roots_exact
  system := system
  same := fun _ _ => Iff.rfl
  symmetric := LevelTower.headEq_symmetric

theorem churchRosser : ChurchRosser (rules naturalOnly) := presentation.churchRosser

theorem pi_boundary : PiConversionBoundary (rules naturalOnly) := presentation.piConversionBoundary

theorem sigma_boundary : SigmaConversionBoundary (rules naturalOnly) := presentation.sigmaConversionBoundary

theorem root_head {n : Nat} {left right : Tower.Tm n}
    (step : (rules naturalOnly).computation.step left right) :
    spineHead left = some (natEliminateName, 4) := by
  cases roots_exact.mp step with
  | instantiate rule substitution => cases rule <;> rfl

/-- No bare constant takes a step: the only roots need four arguments. -/
theorem constant_normal {n : Nat} (name : DeclName) :
    Normal (rules naturalOnly) (.const name : Tower.Tm n) := by
  intro target step
  cases step with
  | root root =>
      have impossible := root_head root
      change some (name, 0) = some (natEliminateName, 4) at impossible
      cases impossible

/-- A nonempty declaration does not collapse into a function type through
an excursion outside its constructor image. -/
theorem natural_not_pi {n : Nat} (domain : Tower.Tm n) (codomain : Tower.Tm (n + 1)) :
    ¬ Conv (rules naturalOnly).headEq natTm (.pi domain codomain)
      (rules naturalOnly).computation := by
  intro conversion
  obtain ⟨common, naturalPath, functionPath⟩ := churchRosser conversion
  have same := Normal.stepStar (constant_normal natName) naturalPath
  obtain ⟨_, _, shape⟩ := presentation.stepStar_pi functionPath
  rw [same] at shape
  cases shape

/-- An actual permitted constructor computation witnesses the selected
policy's positive conversion behavior. -/
theorem addition_zero {n : Nat} (second : Tower.Tm n) :
    Conv (rules naturalOnly).headEq (add zeroTm second) second (rules naturalOnly).computation := by
  apply Relation.EqvGen.rel
  apply StepCore.root
  apply roots_exact.mpr
  exact SchemaStep.instantiate Schema.zero
    (fun index => Fin.cases (.lam (.lam (succApp (.var 0))))
      (Fin.cases second (fun _ => .lam natTm)) index)

namespace Preservation

open FormationSensitive TelescopeAbstraction

abbrev selectedRules := rules naturalOnly

theorem universes : UniverseRegularity selectedRules :=
  towerUniverseRegularity.includeSignature (signature naturalOnly)

def recursorTelescope : Tower.Ctx 4 :=
  RussellTarski.substLevelsCtx levels natContextPZSN

def recursorResult : Tower.Tm 4 := .app (.var 3) (.var 0)

theorem recursor_declared : selectedRules.constantType natEliminateName =
    some (closeType recursorTelescope recursorResult) := by decide +kernel

def arguments {n : Nat} (motive zeroCase succCase number : Tower.Tm n) : Sub Tower.Head 4 n :=
  fun index => Fin.cases number (Fin.cases succCase (Fin.cases zeroCase (fun _ => motive))) index

/-- The telescope follows the existing declaration, not a fresh recursor. -/
theorem application_shape {n : Nat} (motive zeroCase succCase number : Tower.Tm n) :
    applyClosed recursorTelescope (arguments motive zeroCase succCase number)
      (.const natEliminateName) = natEliminateApp motive zeroCase succCase number := rfl

theorem principal_result {n : Nat} (motive zeroCase succCase number : Tower.Tm n) :
    subst (arguments motive zeroCase succCase number) recursorResult = .app motive number := rfl

theorem recursor_spine {n : Nat} {Γ : Tower.Ctx n}
    {motive zeroCase succCase number displayed : Tower.Tm n}
    (observed : Typing selectedRules Γ (natEliminateApp motive zeroCase succCase number) displayed) :
    DeclarationSpine selectedRules Γ (.const natEliminateName)
      (liftClosed (closeType recursorTelescope recursorResult)) := by
  exact DeclarationSpine.ofObservedTelescope recursorTelescope recursorResult
    (arguments motive zeroCase succCase number) recursor_declared observed

/-- Observed typing retains the real closed formation certificate at its
declaration head. The common telescope theorem then recovers every argument
and the original displayed-type adjustment. -/
theorem recover {n : Nat} {Γ : Tower.Ctx n} {motive zeroCase succCase number displayed : Tower.Tm n}
    (context : ContextFormation selectedRules Γ)
    (observed : Typing selectedRules Γ (natEliminateApp motive zeroCase succCase number) displayed) :
    FormationSensitive.CtxMor selectedRules recursorTelescope Γ (arguments motive zeroCase succCase number) ∧
      DeclarationSpine selectedRules Γ (natEliminateApp motive zeroCase succCase number)
        (.app motive number) ∧
      TypeAdjustment selectedRules (.app motive number) displayed ∧
      (∀ {replacement}, Typing selectedRules Γ replacement (.app motive number) →
        Typing selectedRules Γ replacement displayed) := by
  have recovered := (recursor_spine observed).recoverTelescope universes pi_boundary context recursorTelescope
    recursorResult (arguments motive zeroCase succCase number) observed
  simpa only [application_shape, principal_result] using recovered

/-- Uniform zero-rule preservation keeps every original conversion and
cumulativity tail; the result type need not be the syntactic principal type. -/
theorem zero_preserves {n : Nat} {Γ : Tower.Ctx n} {motive zeroCase succCase displayed : Tower.Tm n}
    (context : ContextFormation selectedRules Γ)
    (observed : Typing selectedRules Γ (natEliminateApp motive zeroCase succCase zeroTm) displayed) :
    Typing selectedRules Γ zeroCase displayed := by
  have recovered := recover context observed
  apply recovered.2.2.2
  exact recovered.1 (2 : Fin 4)

theorem successor_declared : selectedRules.constantType succName = some succType := by decide +kernel

/-- A constructor's observed typing recovers the predecessor at the genuine
declared domain, rather than assuming constructor injectivity of typing. -/
theorem successor_argument {n : Nat} {Γ : Tower.Ctx n} {number : Tower.Tm n}
    (context : ContextFormation selectedRules Γ)
    (observed : Typing selectedRules Γ (succApp number) natTm) :
    Typing selectedRules Γ number natTm := by
  obtain ⟨_, _, head, _, _, _⟩ := observed.appGeneration
  obtain ⟨declared, level, known, formed, universeWitness⟩ := head.constFormation
  have same : declared = succType := Option.some.inj (known.symm.trans successor_declared)
  subst declared
  have spine := DeclarationSpine.constant (Γ := Γ) known formed universeWitness
  exact (spine.recoverApplication universes pi_boundary context observed).1

/-- Uniform successor-rule preservation follows from recovered method,
predecessor and recursive-call typing in the same formed context. -/
theorem successor_preserves {n : Nat} {Γ : Tower.Ctx n}
    {motive zeroCase succCase number displayed : Tower.Tm n}
    (context : ContextFormation selectedRules Γ)
    (observed : Typing selectedRules Γ
      (natEliminateApp motive zeroCase succCase (succApp number)) displayed) :
    Typing selectedRules Γ
      (.app (.app succCase number) (natEliminateApp motive zeroCase succCase number)) displayed := by
  have recovered := recover context observed
  have methodTyped := recovered.1 (1 : Fin 4)
  have numberTyped := successor_argument context (recovered.1 (0 : Fin 4))
  have parameterTyped : FormationSensitive.CtxMor selectedRules
      (RussellTarski.substLevelsCtx levels natContextPZS) Γ
      (fun index => arguments motive zeroCase succCase (succApp number) index.succ) :=
    recovered.1.dropNewest
  have renewed := parameterTyped.extend (type := natTm) numberTyped
  have same : consSub number
      (fun index => arguments motive zeroCase succCase (succApp number) index.succ) =
      arguments motive zeroCase succCase number := by
    funext index
    fin_cases index <;> rfl
  rw [same] at renewed
  have recursiveTyped := ((recursor_spine observed).applyTelescope recursorTelescope recursorResult
    (arguments motive zeroCase succCase number) renewed).typing
  have methodFirst := Typing.appElim methodTyped numberTyped
  change Typing selectedRules Γ (.app succCase number)
    (inst0 number (.pi (.app (rename wk motive) (.var 0))
      (.app (rename wk (rename wk motive)) (succApp (.var 1))))) at methodFirst
  dsimp only [inst0, subst] at methodFirst
  simp only [subst_liftSub_wk] at methodFirst
  rw [show subst (subst0 number) (rename wk motive) = motive from
    inst0_rename_wk number motive] at methodFirst
  change Typing selectedRules Γ (.app succCase number)
    (.pi (.app motive number) (rename wk (.app motive (succApp number)))) at methodFirst
  have recursiveReady : Typing selectedRules Γ (natEliminateApp motive zeroCase succCase number)
      (.app motive number) := by
    simpa only [application_shape, principal_result] using recursiveTyped
  have result := Typing.appElim methodFirst recursiveReady
  apply recovered.2.2.2
  simpa only [inst0_rename_wk] using result

theorem roots : RootPreservation selectedRules := by
  intro n Γ source target type context observed step
  cases roots_exact.mp step with
  | instantiate rule substitution =>
      cases rule with
      | zero => exact zero_preserves context observed
      | successor => exact successor_preserves context observed

theorem heads : HeadPreservation selectedRules :=
  towerHeadPreservation.includeSignature (signature naturalOnly)

/-- Every existing contextual beta/iota/projection step preserves the formed
judgment, including computation inside dependent binder types. -/
theorem steps_preserve {n : Nat} {Γ : Tower.Ctx n} {source target type : Tower.Tm n}
    (judgment : Judgment selectedRules Γ source type)
    (steps : StepStar selectedRules source target) : Judgment selectedRules Γ target type :=
  judgment.steps_preserve universes pi_boundary sigma_boundary heads roots steps

namespace Vector

def recursorTelescope : Tower.Ctx 6 :=
  .snoc (.snoc (RussellTarski.substLevelsCtx levels vecContextAPZS) natTm)
    (vecApp (.var 4) (.var 0))

def recursorResult : Tower.Tm 6 := .app (.app (.var 4) (.var 1)) (.var 0)

theorem recursor_declared : selectedRules.constantType vecEliminateName =
    some (closeType recursorTelescope recursorResult) := by decide +kernel

def arguments {n : Nat} (element motive nilCase consCase length vector : Tower.Tm n) :
    Sub Tower.Head 6 n :=
  fun index => Fin.cases vector (Fin.cases length (Fin.cases consCase
    (Fin.cases nilCase (Fin.cases motive (fun _ => element))))) index

theorem application_shape {n : Nat} (element motive nilCase consCase length vector : Tower.Tm n) :
    applyClosed recursorTelescope (arguments element motive nilCase consCase length vector)
      (.const vecEliminateName) =
      vecEliminateApp element motive nilCase consCase length vector := rfl

theorem principal_result {n : Nat} (element motive nilCase consCase length vector : Tower.Tm n) :
    subst (arguments element motive nilCase consCase length vector) recursorResult =
      .app (.app motive length) vector := rfl

theorem recursor_spine {n : Nat} {Γ : Tower.Ctx n}
    {element motive nilCase consCase length vector displayed : Tower.Tm n}
    (observed : Typing selectedRules Γ
      (vecEliminateApp element motive nilCase consCase length vector) displayed) :
    DeclarationSpine selectedRules Γ (.const vecEliminateName)
      (liftClosed (closeType recursorTelescope recursorResult)) :=
  .ofObservedTelescope recursorTelescope recursorResult
    (arguments element motive nilCase consCase length vector) recursor_declared observed

/-- All six arguments come from the original declaration and observed
derivation; the final replay retains its exact displayed type. -/
theorem recover {n : Nat} {Γ : Tower.Ctx n}
    {element motive nilCase consCase length vector displayed : Tower.Tm n}
    (context : ContextFormation selectedRules Γ)
    (observed : Typing selectedRules Γ
      (vecEliminateApp element motive nilCase consCase length vector) displayed) :
    FormationSensitive.CtxMor selectedRules recursorTelescope Γ
        (arguments element motive nilCase consCase length vector) ∧
      DeclarationSpine selectedRules Γ
        (vecEliminateApp element motive nilCase consCase length vector)
        (.app (.app motive length) vector) ∧
      TypeAdjustment selectedRules (.app (.app motive length) vector) displayed ∧
      (∀ {replacement}, Typing selectedRules Γ replacement (.app (.app motive length) vector) →
        Typing selectedRules Γ replacement displayed) := by
  have recovered := (recursor_spine observed).recoverTelescope universes pi_boundary context
    recursorTelescope recursorResult (arguments element motive nilCase consCase length vector) observed
  simpa only [application_shape, principal_result] using recovered

theorem nil_preserves {n : Nat} {Γ : Tower.Ctx n}
    {element motive nilCase consCase displayed : Tower.Tm n}
    (context : ContextFormation selectedRules Γ)
    (observed : Typing selectedRules Γ
      (vecEliminateApp element motive nilCase consCase zeroTm (vnilApp element)) displayed) :
    Typing selectedRules Γ nilCase displayed := by
  have recovered := recover context observed
  apply recovered.2.2.2
  exact recovered.1 (3 : Fin 6)

def constructorTelescope : Tower.Ctx 4 :=
  .snoc (.snoc (.snoc (.snoc .nil (sortTm elementLevel)) natTm) (.var 1))
    (vecApp (.var 2) (.var 1))

def constructorResult : Tower.Tm 4 := vecApp (.var 3) (succApp (.var 2))

def constructorArguments {n : Nat} (element length head tail : Tower.Tm n) : Sub Tower.Head 4 n :=
  fun index => Fin.cases tail (Fin.cases head (Fin.cases length (fun _ => element))) index

theorem constructor_declared : selectedRules.constantType vconsName =
    some (closeType constructorTelescope constructorResult) := by decide +kernel

theorem constructor_arguments {n : Nat} {Γ : Tower.Ctx n}
    {element length head tail displayed : Tower.Tm n}
    (context : ContextFormation selectedRules Γ)
    (observed : Typing selectedRules Γ (vconsApp element length head tail) displayed) :
    FormationSensitive.CtxMor selectedRules constructorTelescope Γ
      (constructorArguments element length head tail) := by
  have spine := DeclarationSpine.ofObservedTelescope constructorTelescope constructorResult
    (constructorArguments element length head tail) constructor_declared observed
  exact (spine.recoverTelescope universes pi_boundary context constructorTelescope constructorResult
    (constructorArguments element length head tail) observed).1

/-- The canonical cons target uses the already declared eliminator. Its
closed formation is recovered from the observed source, rather than assumed
subject preservation of the larger operational policy. -/
theorem canonical_cons_target {level : Tower.Head}
    (formed : Typing selectedRules .nil (closeType recursorTelescope recursorResult) (.head level))
    (universeWitness : selectedRules.isUniverse level) :
    Typing selectedRules (RussellTarski.substLevelsCtx levels vecContextAPZSNHeadTail)
      vecConsIotaRight vecConsIotaType := by
  have headTyped : Typing selectedRules
      (RussellTarski.substLevelsCtx levels vecContextAPZSNHeadTail)
      (.const vecEliminateName) (liftClosed (closeType recursorTelescope recursorResult)) :=
    .const recursor_declared formed universeWitness
  have afterElement := Typing.appElim headTyped (Typing.var (6 : Fin 7))
  have afterMotive := Typing.appElim afterElement (Typing.var (5 : Fin 7))
  have afterNil := Typing.appElim afterMotive (Typing.var (4 : Fin 7))
  have afterMethod := Typing.appElim afterNil (Typing.var (3 : Fin 7))
  have afterLength := Typing.appElim afterMethod (Typing.var (2 : Fin 7))
  have recursive := Typing.appElim afterLength (Typing.var (0 : Fin 7))
  have methodLength := Typing.appElim
    (Typing.var (R := selectedRules)
      (Γ := RussellTarski.substLevelsCtx levels vecContextAPZSNHeadTail) (3 : Fin 7))
    (Typing.var (2 : Fin 7))
  have methodHead := Typing.appElim methodLength (Typing.var (1 : Fin 7))
  have methodTail := Typing.appElim methodHead (Typing.var (0 : Fin 7))
  have result := Typing.appElim methodTail recursive
  convert result using 1 <;> decide +kernel

/-- Constructor inversion supplies length, head and tail. They extend the
source's recovered parameter telescope into the original canonical context. -/
theorem cons_preserves {n : Nat} {Γ : Tower.Ctx n}
    {element motive nilCase consCase length head tail displayed : Tower.Tm n}
    (context : ContextFormation selectedRules Γ)
    (observed : Typing selectedRules Γ
      (vecEliminateApp element motive nilCase consCase (succApp length)
        (vconsApp element length head tail)) displayed) :
    Typing selectedRules Γ
      (.app (.app (.app (.app consCase length) head) tail)
        (vecEliminateApp element motive nilCase consCase length tail)) displayed := by
  have recovered := recover context observed
  have constructor := constructor_arguments context (recovered.1 (0 : Fin 6))
  have lengthTyped := constructor (2 : Fin 4)
  have headTyped := constructor (1 : Fin 4)
  have tailTyped := constructor (0 : Fin 4)
  have parameters := recovered.1.dropNewest.dropNewest
  have withLength := parameters.extend (type := natTm) lengthTyped
  have withHead := withLength.extend (type := .var 4) headTyped
  have withTail := withHead.extend (type := vecApp (.var 5) (.var 1)) tailTyped
  obtain ⟨level, formed, universeWitness⟩ :=
    (recursor_spine observed).constant_formed recursor_declared
  have target := (canonical_cons_target formed universeWitness).substitute withTail
  apply recovered.2.2.2
  exact target

end Vector

/-- The original operational roots preserve the smaller checking judgment.
This is a root theorem: dependent contextual transport is not inferred from
the larger relation's unqualified congruence closure. -/
theorem operational_roots {n : Nat} {Γ : Tower.Ctx n} {source target type : Tower.Tm n}
    (judgment : Judgment selectedRules Γ source type)
    (step : IotaEvidence n source target) : Judgment selectedRules Γ target type := by
  refine ⟨judgment.context, ?_⟩
  cases step with
  | natZero => exact zero_preserves judgment.context judgment.typing
  | natSucc => exact successor_preserves judgment.context judgment.typing
  | vecNil => exact Vector.nil_preserves judgment.context judgment.typing
  | vecCons => exact Vector.cons_preserves judgment.context judgment.typing

/-- The original declaration package has no inherited or delta roots.
Its actual operational root relation therefore satisfies the same law. -/
theorem operational_rule_roots {n : Nat} {Γ : Tower.Ctx n} {source target type : Tower.Tm n}
    (judgment : Judgment selectedRules Γ source type)
    (step : Programs.rules.computation.step source target) : Judgment selectedRules Γ target type := by
  obtain ⟨evidence⟩ := (DeclarationConversionCode.opaque_roots_iff Tower.rules Programs.signature
    (fun impossible => impossible.elim) (Annotated.opaque_values naturalOnly)).mp step
  exact operational_roots judgment evidence

/-- The complete four-row operational package is sound against the smaller
natural-only checking judgment.  This cross-policy contract does not install
the vector rows as conversion rules of that judgment. -/
theorem operational_preservation_against :
    RootPreservationAgainst selectedRules Programs.rules := by
  intro n Γ source target type context typed step
  exact (operational_rule_roots ⟨context, typed⟩ step).typing

end Preservation

namespace Controls

open FormationSensitive
open Preservation (selectedRules)

local instance : DecidableRel selectedRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred selectedRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (selectedRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel selectedRules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel selectedRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def zeroSubmission := FormationSensitiveElaboration.elaborate selectedRules (decoder naturalOnly)
  choices 96 .nil (add zeroTm zeroTm) natTm

def successorSubmission := FormationSensitiveElaboration.elaborate selectedRules (decoder naturalOnly)
  choices 96 .nil (add (succApp zeroTm) zeroTm) natTm

theorem zero_produced : zeroSubmission.isSome = true := by decide +kernel
theorem successor_produced : successorSubmission.isSome = true := by decide +kernel

theorem zero_typed : Judgment selectedRules .nil (add zeroTm zeroTm) natTm := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp zero_produced
  exact FormationSensitiveElaboration.elaborate_sound selectedRules (decoder naturalOnly)
    choices 96 .nil (add zeroTm zeroTm) natTm submission produced

theorem successor_typed : Judgment selectedRules .nil (add (succApp zeroTm) zeroTm) natTm := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp successor_produced
  exact FormationSensitiveElaboration.elaborate_sound selectedRules (decoder naturalOnly)
    choices 96 .nil (add (succApp zeroTm) zeroTm) natTm submission produced

/-- This uses the uniform theorem on an actually typed zero redex. -/
theorem zero_preserved : Judgment selectedRules .nil zeroTm natTm :=
  ⟨zero_typed.context, Preservation.zero_preserves zero_typed.context zero_typed.typing⟩

theorem successor_path :
    StepStar selectedRules (add (n := 0) (succApp zeroTm) zeroTm) (succApp zeroTm) := by
  let motive : Tower.Tm 0 := .lam natTm
  let method : Tower.Tm 0 := .lam (.lam (succApp (.var 0)))
  have first : StepCore selectedRules.computation selectedRules.headEq
      (add (succApp zeroTm) zeroTm)
      (.app (.app method zeroTm) (add zeroTm zeroTm)) := by
    apply StepCore.root
    apply roots_exact.mpr
    exact SchemaStep.instantiate Schema.successor
      (fun index => Fin.cases zeroTm (Fin.cases method (Fin.cases zeroTm (fun _ => motive))) index)
  have zeroRoot : StepCore selectedRules.computation selectedRules.headEq
      (add (n := 0) zeroTm zeroTm) zeroTm := by
    apply StepCore.root
    apply roots_exact.mpr
    exact SchemaStep.instantiate Schema.zero
      (fun index : Fin 3 => Fin.cases method (Fin.cases zeroTm (fun _ => motive)) index)
  have last : StepCore selectedRules.computation selectedRules.headEq
      (succApp (add zeroTm zeroTm)) (succApp zeroTm) := .congAppArg zeroRoot
  exact .tail (.tail (.tail (.tail .refl first)
    (.congAppFun (.betaPi (.lam (succApp (.var 0))) zeroTm)))
    (.betaPi (succApp (.var 0)) (add zeroTm zeroTm))) last

/-- Four actual contextual steps retain the computed successor's type. -/
theorem successor_preserved : Judgment selectedRules .nil (succApp zeroTm) natTm :=
  Preservation.steps_preserve successor_typed successor_path

def vectorNilSubmission := FormationSensitiveElaboration.elaborate selectedRules (decoder naturalOnly)
  choices 96 (RussellTarski.substLevelsCtx levels vecContextAPZS) vecNilIotaLeft vecNilIotaType

def vectorConsSubmission := FormationSensitiveElaboration.elaborate selectedRules (decoder naturalOnly)
  choices 96 (RussellTarski.substLevelsCtx levels vecContextAPZSNHeadTail) vecConsIotaLeft vecConsIotaType

theorem vector_nil_produced : vectorNilSubmission.isSome = true := by decide +kernel
theorem vector_cons_produced : vectorConsSubmission.isSome = true := by decide +kernel

theorem vector_nil_typed : Judgment selectedRules
    (RussellTarski.substLevelsCtx levels vecContextAPZS) vecNilIotaLeft vecNilIotaType := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp vector_nil_produced
  exact FormationSensitiveElaboration.elaborate_sound selectedRules (decoder naturalOnly)
    choices 96 _ _ _ submission produced

theorem vector_cons_typed : Judgment selectedRules
    (RussellTarski.substLevelsCtx levels vecContextAPZSNHeadTail) vecConsIotaLeft vecConsIotaType := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp vector_cons_produced
  exact FormationSensitiveElaboration.elaborate_sound selectedRules (decoder naturalOnly)
    choices 96 _ _ _ submission produced

theorem vector_nil_preserved : Judgment selectedRules
    (RussellTarski.substLevelsCtx levels vecContextAPZS) vecNilIotaRight vecNilIotaType :=
  Preservation.operational_rule_roots vector_nil_typed (.declared ⟨.vecNil _ _ _ _⟩)

theorem vector_cons_preserved : Judgment selectedRules
    (RussellTarski.substLevelsCtx levels vecContextAPZSNHeadTail) vecConsIotaRight vecConsIotaType :=
  Preservation.operational_rule_roots vector_cons_typed (.declared ⟨.vecCons _ _ _ _ _ _ _⟩)

/-- The same concrete cons redex is typed and operationally licensed, but
it is not one of the smaller checker's root conversions. -/
theorem vector_cons_root_disabled :
    ¬ selectedRules.computation.step vecConsIotaLeft vecConsIotaRight := by
  intro step
  have arity := congrArg (fun head => head.map Prod.snd) (root_head step)
  change some 6 = some 4 at arity
  cases arity

def vectorConsCitation : (decoder naturalOnly).Code 7 :=
  .declared ⟨3, [.var 0, .var 1, .var 2, .var 3, .var 4, .var 5, .var 6]⟩

theorem vector_cons_citation_refused :
    ((decoder naturalOnly).decode vectorConsCitation).isNone = true := by decide +kernel

theorem vector_cons_citation_enabled :
    ((decoder (fun _ => true)).decode vectorConsCitation) =
      some (vecConsIotaLeft, vecConsIotaRight) := by decide +kernel

def alteredTypeRefused : Bool := match zeroSubmission with
  | none => false
  | some submission => !FormationSensitiveElaboration.replay selectedRules (decoder naturalOnly)
      .nil (add zeroTm zeroTm) (.pi natTm natTm) submission

theorem altered_type_refused : alteredTypeRefused = true := by decide +kernel

def verdicts : List (String × Bool) := [
  ("natural preservation has a typed zero redex", zeroSubmission.isSome),
  ("natural preservation has a typed successor redex", successorSubmission.isSome),
  ("the same natural proof refuses an altered Pi result type", alteredTypeRefused),
  ("smaller checking policy types the original vector nil redex", vectorNilSubmission.isSome),
  ("smaller checking policy types the original vector cons redex", vectorConsSubmission.isSome),
  ("smaller checking policy still refuses the vector cons root", ((decoder naturalOnly).decode vectorConsCitation).isNone),
  ("full policy accepts that same vector cons root",
    ((decoder (fun _ => true)).decode vectorConsCitation) == some (vecConsIotaLeft, vecConsIotaRight))]

theorem all_verdicts : verdicts.all Prod.snd = true := by
  simp only [verdicts, List.all_cons, List.all_nil, zero_produced, successor_produced,
    altered_type_refused, vector_nil_produced, vector_cons_produced,
    vector_cons_citation_refused, vector_cons_citation_enabled, beq_self_eq_true, Bool.and_self]

end Controls

end Programs.ComputationProfiles.NaturalConversion
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
