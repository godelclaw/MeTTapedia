import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationSpine

/-!
# Raw preservation for the original natural-only computation policy

The proof uses the selected raw conversion boundary and existing typed
telescope application. It discharges the legacy signature preservation field
for the two selected original rows, in arbitrary raw contexts, while retaining
all eight declarations. The unselected vector roots and annotation coherence
are separate obligations. No raw-to-formed upgrade is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
namespace Programs.ComputationProfiles.NaturalConversion.RawPreservation

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open TelescopeAbstraction
open Preservation (selectedRules recursorTelescope recursorResult recursor_declared
  arguments application_shape principal_result successor_declared)

theorem recursor_spine {n : Nat} {Γ : Tower.Ctx n} :
    Presentation.HasType.DeclarationSpine selectedRules Γ (.const natEliminateName)
      (liftClosed (closeType recursorTelescope recursorResult)) :=
  .constant recursor_declared

theorem recover {n : Nat} {Γ : Tower.Ctx n}
    {motive zeroCase succCase number displayed : Tower.Tm n}
    (observed : Presentation.HasType selectedRules Γ
      (natEliminateApp motive zeroCase succCase number) displayed) :
    CtxMor selectedRules recursorTelescope Γ (arguments motive zeroCase succCase number) ∧
      Presentation.HasType.DeclarationSpine selectedRules Γ
        (natEliminateApp motive zeroCase succCase number) (.app motive number) ∧
      TypeAdjustment selectedRules (.app motive number) displayed ∧
      (∀ {replacement}, Presentation.HasType selectedRules Γ replacement (.app motive number) →
        Presentation.HasType selectedRules Γ replacement displayed) := by
  have recovered := recursor_spine.recoverTelescope pi_boundary recursorTelescope
    recursorResult (arguments motive zeroCase succCase number) observed
  simpa only [application_shape, principal_result] using recovered

theorem zero_preserves {n : Nat} {Γ : Tower.Ctx n}
    {motive zeroCase succCase displayed : Tower.Tm n}
    (observed : Presentation.HasType selectedRules Γ
      (natEliminateApp motive zeroCase succCase zeroTm) displayed) :
    Presentation.HasType selectedRules Γ zeroCase displayed := by
  have recovered := recover observed
  exact recovered.2.2.2 (recovered.1 (2 : Fin 4))

theorem successor_argument {n : Nat} {Γ : Tower.Ctx n} {number : Tower.Tm n}
    (observed : Presentation.HasType selectedRules Γ (succApp number) natTm) :
    Presentation.HasType selectedRules Γ number natTm := by
  have spine : Presentation.HasType.DeclarationSpine selectedRules Γ (.const succName) (liftClosed succType) :=
    .constant successor_declared
  exact (spine.recoverApplication pi_boundary observed).1

theorem successor_preserves {n : Nat} {Γ : Tower.Ctx n}
    {motive zeroCase succCase number displayed : Tower.Tm n}
    (observed : Presentation.HasType selectedRules Γ
      (natEliminateApp motive zeroCase succCase (succApp number)) displayed) :
    Presentation.HasType selectedRules Γ
      (.app (.app succCase number) (natEliminateApp motive zeroCase succCase number)) displayed := by
  have recovered := recover observed
  have methodTyped := recovered.1 (1 : Fin 4)
  have numberTyped := successor_argument (recovered.1 (0 : Fin 4))
  have parameterTyped : CtxMor selectedRules
      (RussellTarski.substLevelsCtx levels natContextPZS) Γ
      (fun index => arguments motive zeroCase succCase (succApp number) index.succ) :=
    TelescopeAbstraction.CtxMor.prior recovered.1
  have renewed := parameterTyped.extend (type := natTm) numberTyped
  have same : consSub number
      (fun index => arguments motive zeroCase succCase (succApp number) index.succ) =
      arguments motive zeroCase succCase number := by
    funext index
    fin_cases index <;> rfl
  rw [same] at renewed
  have recursiveTyped := applyClosed_typed renewed recursor_spine.typing
  have methodFirst := Presentation.HasType.appElim methodTyped numberTyped
  change Presentation.HasType selectedRules Γ (.app succCase number)
    (inst0 number (.pi (.app (rename wk motive) (.var 0))
      (.app (rename wk (rename wk motive)) (succApp (.var 1))))) at methodFirst
  dsimp only [inst0, subst] at methodFirst
  simp only [subst_liftSub_wk] at methodFirst
  rw [show subst (subst0 number) (rename wk motive) = motive from
    inst0_rename_wk number motive] at methodFirst
  change Presentation.HasType selectedRules Γ (.app succCase number)
    (.pi (.app motive number) (rename wk (.app motive (succApp number)))) at methodFirst
  have recursiveReady : Presentation.HasType selectedRules Γ
      (natEliminateApp motive zeroCase succCase number) (.app motive number) := by
    change Presentation.HasType selectedRules Γ
      (applyClosed recursorTelescope (arguments motive zeroCase succCase number)
        (.const natEliminateName))
      (subst (arguments motive zeroCase succCase number) recursorResult) at recursiveTyped
    simpa only [application_shape, principal_result] using recursiveTyped
  have result := Presentation.HasType.appElim methodFirst recursiveReady
  apply recovered.2.2.2
  simpa only [inst0_rename_wk] using result

theorem roots_preserve {n : Nat} {Γ : Tower.Ctx n} {source target type : Tower.Tm n}
    (step : selectedRules.computation.step source target)
    (observed : Presentation.HasType selectedRules Γ source type) :
    Presentation.HasType selectedRules Γ target type := by
  cases roots_exact.mp step with
  | instantiate rule substitution =>
      cases rule with
      | zero => exact zero_preserves observed
      | successor => exact successor_preserves observed

theorem declared_preserves : (signature naturalOnly).DeclaredPreserves Tower.rules := by
  intro n Γ source target type step observed
  exact roots_preserve (Declaration.RootStep.declared step) observed

namespace Formation

def noIota : Selection := fun _ => false

local instance : DecidableRel (rules noIota).headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred (rules noIota).isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable ((rules noIota).join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel (rules noIota).cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel (rules noIota).headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def requests : List (DeclName × Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat) := [
  (natName, natDeclarationLevel), (zeroName, natLevel),
  (succName, succDeclarationLevel), (natEliminateName, natEliminateDeclarationLevel),
  (vecName, vecDeclarationLevel), (vnilName, vnilDeclarationLevel),
  (vconsName, vconsDeclarationLevel), (vecEliminateName, vecEliminateDeclarationLevel)]

def produced (request : DeclName × Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat) : Bool :=
  match (signature noIota).typeOf? request.1 with
  | none => false
  | some type => (FormationSensitiveElaboration.elaborate (rules noIota) (decoder noIota)
      Programs.choices 96 .nil type
      (.head (RussellTarski.substLevelsHead levels (.sort request.2)))).isSome

theorem all_produced : requests.all produced = true := by decide +kernel

theorem request_formed {request : DeclName × Mettapedia.TypeTheory.UniverseLevel.LevelExpr Nat}
    (member : request ∈ requests) :
    ∃ type, (signature noIota).typeOf? request.1 = some type ∧
      FormationSensitive.Judgment (rules noIota) .nil type
        (.head (RussellTarski.substLevelsHead levels (.sort request.2))) := by
  have checked := (List.all_eq_true.mp all_produced) request member
  cases known : (signature noIota).typeOf? request.1 with
  | none => simp [produced, known] at checked
  | some type =>
      simp only [produced, known] at checked
      obtain ⟨submission, accepted⟩ := Option.isSome_iff_exists.mp checked
      exact ⟨type, rfl, FormationSensitiveElaboration.elaborate_sound
        (rules noIota) (decoder noIota) Programs.choices 96 .nil type
        (.head (RussellTarski.substLevelsHead levels (.sort request.2))) submission accepted⟩

theorem lookup_covered {enabled : Selection} {name : DeclName} {type : Tower.Tm 0}
    (lookup : (signature enabled).typeOf? name = some type) :
    ∃ level, (name, level) ∈ requests := by
  change (rawSignature.instantiateLevels levels Programs.levelInstance.computation).typeOf? name =
    some type at lookup
  obtain ⟨sourceType, original, _⟩ :=
    (Declaration.Signature.typeOf_instantiateLevels_iff levels rawSignature
      Programs.levelInstance.computation name type).mp lookup
  change ((Declaration.Signature.ofList declarations).entries name).map Declaration.Entry.type =
    some sourceType at original
  obtain ⟨entry, selected, _⟩ := Option.map_eq_some_iff.mp original
  have member := Declaration.Signature.entries_ofList_mem declarations selected
  have nameMember : name ∈ declarations.map Prod.fst :=
    List.mem_map.mpr ⟨(name, entry), member, rfl⟩
  have names : name ∈ requests.map Prod.fst := by
    simpa only [declarations, requests, List.map_cons, List.map_nil] using nameMember
  obtain ⟨⟨found, level⟩, requestMember, same⟩ := List.mem_map.mp names
  cases same
  exact ⟨level, requestMember⟩

/-- Declaration formation was checked with every iota row disabled. Its
typing evidence therefore transports to every original permission selection. -/
theorem signature_formed (enabled : Selection) : (signature enabled).Formed Tower.rules where
  fresh := by intro name entry _; rfl
  types := by
    intro name type lookup
    obtain ⟨level, member⟩ := lookup_covered lookup
    obtain ⟨checkedType, known, judgment⟩ := request_formed member
    have same : checkedType = type := Option.some.inj (known.symm.trans lookup)
    subst checkedType
    refine ⟨RussellTarski.substLevelsHead levels (.sort level), .sort _, ?_⟩
    exact Declaration.HasType.monoSignature Tower.rules
      (permissions_mono (small := noIota) (large := enabled) (by intro index impossible; cases impossible))
      judgment.typing.toRaw
  values := by
    intro name type value _ lookup
    rw [Annotated.opaque_values enabled name] at lookup
    cases lookup
  noSelfDelta := by
    intro name value lookup
    rw [Annotated.opaque_values enabled name] at lookup
    cases lookup

end Formation

/-- The actual selected declaration signature, with separately earned
formation and uniform raw root preservation. -/
def checkedSignature : Declaration.CheckedSignature Tower.rules where
  signature := signature naturalOnly
  wellFormed := (Formation.signature_formed naturalOnly).withPreservation declared_preserves

theorem checked_append : Presentation.HasType checkedSignature.rules .nil appendTerm appendType :=
  append_typed_naturalOnly.toRaw

theorem addition_zero_root {n : Nat} (second : Tower.Tm n) :
    selectedRules.computation.step (add zeroTm second) second := by
  apply roots_exact.mpr
  exact AlgebraicSchema.SchemaStep.instantiate Schema.zero
    (fun index => Fin.cases (.lam (.lam (succApp (.var 0))))
      (Fin.cases second (fun _ => .lam natTm)) index)

theorem actual_zero_preserved : Presentation.HasType selectedRules .nil zeroTm natTm :=
  roots_preserve (addition_zero_root zeroTm) Controls.zero_typed.typing.toRaw

theorem actual_successor_target : Presentation.HasType selectedRules .nil
    (.app (.app (.lam (.lam (succApp (.var 0)))) zeroTm) (add zeroTm zeroTm)) natTm :=
  successor_preserves Controls.successor_typed.typing.toRaw

def missingName : DeclName := `CumulativeTower.RawPreservation.missing

theorem missing_lookup : selectedRules.constantType missingName = none := by decide +kernel

theorem missing_spine_refused {n : Nat} {Γ : Tower.Ctx n} {type : Tower.Tm n} :
    ¬ Presentation.HasType.DeclarationSpine selectedRules Γ (.const missingName) type :=
  Presentation.HasType.DeclarationSpine.missingConstant missing_lookup

def verdicts : List (String × Bool) :=
  Formation.requests.map (fun request =>
    ("Opaque declaration formation: " ++ toString request.1, Formation.produced request)) ++ [
    ("Opaque declaration checker refuses a missing name", !Formation.produced (missingName, natDeclarationLevel)),
    ("Opaque declaration checker refuses a lower universe", !Formation.produced (natName, natLevel))]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

end Programs.ComputationProfiles.NaturalConversion.RawPreservation
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
