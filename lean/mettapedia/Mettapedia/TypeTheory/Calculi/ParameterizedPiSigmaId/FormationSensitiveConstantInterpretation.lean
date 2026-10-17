import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationSignature
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantExpansion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationCheckedTelescopePrograms

/-!
# Typed interpretation of declared constants by closed terms

A declaration interpretation is a translation between rule presentations, not
an equation identifying a source constant with its chosen image. Its primitive
obligations are closed typing for each declared image, preservation of universe
rules, and conversion of the images of source root computations. The resulting
theorems transport actual formation-sensitive derivations, formed telescopes,
and typed substitutions through simultaneous constant expansion.

Open parameter interpretation transports root-free templates from primitive
declaration typing and actual variable assignments. Closing the formed parameter
telescope produces one native lambda program; ordinary native substitution and
the existing finite beta replay specialize it to arbitrary native function values.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ConstantExpansion

open FormationSensitive

variable {Head : Type} {n m : Nat}

def expandCtx (bodies : Bodies Head) {n : Nat} : Ctx Head n → Ctx Head n
  | .nil => .nil
  | .snoc Γ A => .snoc (expandCtx bodies Γ) (expand bodies A)

@[simp] theorem expandCtx_lookup (bodies : Bodies Head) (Γ : Ctx Head n)
    (index : Fin n) :
    Ctx.lookup (expandCtx bodies Γ) index = expand bodies (Ctx.lookup Γ index) := by
  induction Γ with
  | nil => exact Fin.elim0 index
  | snoc Γ A ih =>
      refine Fin.cases ?_ ?_ index
      · exact (expand_rename bodies wk A).symm
      · intro prior
        simp only [expandCtx, Ctx.lookup_snoc_succ, ih, expand_rename]

/-- Local evidence for interpreting primitive declarations and rules. The
conclusions about arbitrary derivations below are not fields of this record. -/
structure TypedInterpretation (source target : Rules Head) (bodies : Bodies Head) : Prop where
  headTyping : ∀ {h u}, source.headTyping h u → target.headTyping h u
  isUniverse : ∀ {u}, source.isUniverse u → target.isUniverse u
  join : ∀ {u v w}, source.join u v w → target.join u v w
  cumulative : ∀ {u v}, source.cumulative u v → target.cumulative u v
  headEq : source.headEq = target.headEq
  constant : ∀ {name type}, source.constantType name = some type →
    Typing target .nil (bodies name) (expand bodies type)
  root : ∀ {k : Nat} {left right : Tm Head k}, source.computation.step left right →
    Conv target.headEq (expand bodies left) (expand bodies right) target.computation

namespace TypedInterpretation

variable {source target : Rules Head} {bodies : Bodies Head}

theorem conversion (interpretation : TypedInterpretation source target bodies)
    {left right : Tm Head n} (converted : Conv source.headEq left right source.computation) :
    Conv target.headEq (expand bodies left) (expand bodies right) target.computation := by
  rw [interpretation.headEq] at converted
  exact conv_expand bodies interpretation.root converted

/-- Every source typing constructor, including formation-sensitive conversion,
is transported through the chosen declaration interpretation. -/
theorem typing (interpretation : TypedInterpretation source target bodies)
    {Γ : Ctx Head n} {term type : Tm Head n} (typed : Typing source Γ term type) :
    Typing target (expandCtx bodies Γ) (expand bodies term) (expand bodies type) := by
  induction typed with
  | headType head => exact .headType (interpretation.headTyping head)
  | var index =>
      simpa only [expand, expandCtx_lookup] using
        (Typing.var (R := target) (Γ := expandCtx bodies _) index)
  | @const k Γ name type u known _ _ _ =>
      have lifted := (interpretation.constant known).renameTyping
        (Δ := expandCtx bodies Γ) (ρ := Fin.elim0) (fun index => Fin.elim0 index)
      simpa only [expand, expand_liftClosed, liftClosed, expand_rename] using lifted
  | piForm _ universeA _ universeB joined ihA ihB =>
      exact .piForm ihA (interpretation.isUniverse universeA) ihB
        (interpretation.isUniverse universeB) (interpretation.join joined)
  | sigmaForm _ universeA _ universeB joined ihA ihB =>
      exact .sigmaForm ihA (interpretation.isUniverse universeA) ihB
        (interpretation.isUniverse universeB) (interpretation.join joined)
  | lamIntro _ universeWitness _ ihPi ihBody =>
      exact .lamIntro ihPi (interpretation.isUniverse universeWitness) ihBody
  | appElim _ _ ihFunction ihArgument =>
      simpa only [expand, expand_inst0] using Typing.appElim ihFunction ihArgument
  | pairIntro _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      rw [expand_inst0] at ihSecond
      exact .pairIntro ihSigma (interpretation.isUniverse universeWitness) ihFirst ihSecond
  | fstElim _ ihPair => exact .fstElim ihPair
  | sndElim _ ihPair =>
      simpa only [expand, expand_inst0] using Typing.sndElim ihPair
  | idForm _ universeWitness _ _ ihA ihLeft ihRight =>
      exact .idForm ihA (interpretation.isUniverse universeWitness) ihLeft ihRight
  | reflIntro _ ihTerm => exact .reflIntro ihTerm
  | cumul _ order ihTerm => exact .cumul ihTerm (interpretation.cumulative order)
  | conv _ _ universeWitness converted ihTerm ihTarget =>
      exact .conv ihTerm ihTarget (interpretation.isUniverse universeWitness)
        (interpretation.conversion converted)

theorem context (interpretation : TypedInterpretation source target bodies)
    {Γ : Ctx Head n} (formed : ContextFormation source Γ) :
    ContextFormation target (expandCtx bodies Γ) := by
  induction formed with
  | nil => exact .nil
  | snoc _ typed universeWitness ih =>
      exact .snoc ih (interpretation.typing typed) (interpretation.isUniverse universeWitness)

theorem judgment (interpretation : TypedInterpretation source target bodies)
    {Γ : Ctx Head n} {term type : Tm Head n} (judged : Judgment source Γ term type) :
    Judgment target (expandCtx bodies Γ) (expand bodies term) (expand bodies type) :=
  ⟨interpretation.context judged.context, interpretation.typing judged.typing⟩

/-- Context substitutions are interpreted componentwise, on the same map as
the terms and telescope entries they act on. -/
theorem contextMorphism (interpretation : TypedInterpretation source target bodies)
    {Γ : Ctx Head n} {Δ : Ctx Head m} {sigma : Sub Head n m}
    (typed : FormationSensitive.CtxMor source Γ Δ sigma) :
    FormationSensitive.CtxMor target (expandCtx bodies Γ) (expandCtx bodies Δ)
      (fun index => expand bodies (sigma index)) := by
  intro index
  simpa only [expand_subst, expandCtx_lookup] using interpretation.typing (typed index)

/-- Interpretation and proof reuse by simultaneous substitution form a
commuting square with complete formed-context judgments at the target. -/
theorem substituted_judgment (interpretation : TypedInterpretation source target bodies)
    {Γ : Ctx Head n} {Δ : Ctx Head m} {term type : Tm Head n} {sigma : Sub Head n m}
    (judged : Judgment source Γ term type) (formed : ContextFormation source Δ)
    (typed : FormationSensitive.CtxMor source Γ Δ sigma) :
    Judgment target (expandCtx bodies Δ)
      (subst (fun index => expand bodies (sigma index)) (expand bodies term))
      (subst (fun index => expand bodies (sigma index)) (expand bodies type)) :=
  (interpretation.judgment judged).substitute (interpretation.context formed)
    (interpretation.contextMorphism typed)

end TypedInterpretation

#print axioms expandCtx_lookup
#print axioms TypedInterpretation.conversion
#print axioms TypedInterpretation.typing
#print axioms TypedInterpretation.context
#print axioms TypedInterpretation.judgment
#print axioms TypedInterpretation.contextMorphism
#print axioms TypedInterpretation.substituted_judgment

end ConstantExpansion
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConstantSubstitution

variable {Head : Type} {n m k : Nat}

/-- Primitive universe and head rules are preserved. Source template root
computation is excluded explicitly, rather than silently simulated. -/
structure RulesMap (source target : Rules Head) : Prop where
  headTyping : ∀ {head universeHead}, source.headTyping head universeHead → target.headTyping head universeHead
  isUniverse : ∀ {universeHead}, source.isUniverse universeHead → target.isUniverse universeHead
  join : ∀ {first second result}, source.join first second result → target.join first second result
  cumulative : ∀ {first last}, source.cumulative first last → target.cumulative first last
  headEquality : ∀ {first last}, source.headEq first last → target.headEq first last
  rootFree : RootFree source.computation

/-- Each actual primitive declaration is interpreted by a well-typed value in
the target context. This is local evidence about declarations, not a whole
program typing hypothesis. -/
def TypedValues (source target : Rules Head) (context : Ctx Head m)
    (values : Values Head m) : Prop :=
  ∀ {name type}, source.constantType name = some type →
    FormationSensitive.Typing target context (values name) (interpret values Fin.elim0 type)

def TypedVariables (rules : Rules Head) (source : Ctx Head n) (target : Ctx Head m)
    (values : Values Head m) (variables : Sub Head n m) : Prop :=
  ∀ index, FormationSensitive.Typing rules target (variables index)
    (interpret values variables (Ctx.lookup source index))

theorem TypedValues.weaken {source target : Rules Head} {context : Ctx Head m}
    {values : Values Head m} (typed : TypedValues source target context values)
    (domain : Tm Head m) :
    TypedValues source target (.snoc context domain) (liftValues values) := by
  intro name type known
  have lifted := (typed known).renameTyping (Δ := .snoc context domain) (ρ := wk)
    (fun index => rfl)
  change FormationSensitive.Typing target (.snoc context domain) (rename wk (values name))
    (interpret (fun name => rename wk (values name)) Fin.elim0 type)
  simpa only [rename_interpret_closed] using lifted

theorem TypedVariables.extend {rules : Rules Head} {source : Ctx Head n} {target : Ctx Head m}
    {values : Values Head m} {variables : Sub Head n m}
    (typed : TypedVariables rules source target values variables) (domain : Tm Head n) :
    TypedVariables rules (.snoc source domain) (.snoc target (interpret values variables domain))
      (liftValues values) (liftSub variables) := by
  intro index
  refine Fin.cases ?_ (fun prior => ?_) index
  · simpa only [liftSub_zero, Ctx.lookup_snoc_zero, interpret_weaken] using
      (FormationSensitive.Typing.var (R := rules)
        (Γ := .snoc target (interpret values variables domain)) 0)
  · have lifted := (typed prior).renameTyping
      (Δ := .snoc target (interpret values variables domain)) (ρ := wk) (fun index => rfl)
    simpa only [liftSub_succ, Ctx.lookup_snoc_succ, interpret_weaken] using lifted

/-- All source formation-sensitive typing constructors are transported. Native
function parameters remain actual values; no source-body enumeration is used. -/
theorem typing {source target : Rules Head} (rules : RulesMap source target)
    {context : Ctx Head n} {term type : Tm Head n}
    (typed : FormationSensitive.Typing source context term type) :
    ∀ {m : Nat} {destination : Ctx Head m} {values : Values Head m} {variables : Sub Head n m},
      TypedValues source target destination values →
      TypedVariables target context destination values variables →
      FormationSensitive.Typing target destination
        (interpret values variables term) (interpret values variables type) := by
  induction typed with
  | headType known => intro m destination values variables _ _; exact .headType (rules.headTyping known)
  | var index => intro m destination values variables _ compatible; exact compatible index
  | @const n context name type universeHead known _ _ _ =>
      intro m destination values variables primitive _
      simpa only [interpret, interpret_liftClosed] using primitive known
  | piForm _ universeA _ universeB joined ihDomain ihCodomain =>
      intro m destination values variables primitive compatible
      exact .piForm (ihDomain primitive compatible) (rules.isUniverse universeA)
        (ihCodomain (primitive.weaken _) (compatible.extend _))
        (rules.isUniverse universeB) (rules.join joined)
  | sigmaForm _ universeA _ universeB joined ihDomain ihCodomain =>
      intro m destination values variables primitive compatible
      exact .sigmaForm (ihDomain primitive compatible) (rules.isUniverse universeA)
        (ihCodomain (primitive.weaken _) (compatible.extend _))
        (rules.isUniverse universeB) (rules.join joined)
  | lamIntro _ universeWitness _ ihFunction ihBody =>
      intro m destination values variables primitive compatible
      exact .lamIntro (ihFunction primitive compatible) (rules.isUniverse universeWitness)
        (ihBody (primitive.weaken _) (compatible.extend _))
  | appElim _ _ ihFunction ihArgument =>
      intro m destination values variables primitive compatible
      simpa only [interpret, interpret_inst0] using
        FormationSensitive.Typing.appElim (ihFunction primitive compatible) (ihArgument primitive compatible)
  | pairIntro _ universeWitness _ _ ihSigma ihFirst ihSecond =>
      intro m destination values variables primitive compatible
      have second := ihSecond primitive compatible
      rw [interpret_inst0] at second
      exact .pairIntro (ihSigma primitive compatible) (rules.isUniverse universeWitness)
        (ihFirst primitive compatible) second
  | fstElim _ ihPair =>
      intro m destination values variables primitive compatible
      exact .fstElim (ihPair primitive compatible)
  | sndElim _ ihPair =>
      intro m destination values variables primitive compatible
      simpa only [interpret, interpret_inst0] using FormationSensitive.Typing.sndElim (ihPair primitive compatible)
  | idForm _ universeWitness _ _ ihType ihLeft ihRight =>
      intro m destination values variables primitive compatible
      exact .idForm (ihType primitive compatible) (rules.isUniverse universeWitness)
        (ihLeft primitive compatible) (ihRight primitive compatible)
  | reflIntro _ ihTerm =>
      intro m destination values variables primitive compatible
      exact .reflIntro (ihTerm primitive compatible)
  | cumul _ order ihTerm =>
      intro m destination values variables primitive compatible
      exact .cumul (ihTerm primitive compatible) (rules.cumulative order)
  | conv _ _ universeWitness converted ihTerm ihType =>
      intro m destination values variables primitive compatible
      exact .conv (ihTerm primitive compatible) (ihType primitive compatible)
        (rules.isUniverse universeWitness)
        (conversion_interpret rules.headEquality rules.rootFree converted values variables)


open TelescopeAbstraction FormationCheckedTelescopePrograms

/-- Close the real parameter telescope into one native lambda program. -/
def parameterProgram (context : Ctx Head k) (positions : DeclName → Option (Fin k))
    (term : Tm Head 0) : Tm Head 0 :=
  closeTerm context (parameterTerm positions term)

/-- Primitive parameter typing earns typing for the whole open body. -/
theorem parameterTerm_typing {source target : Rules Head} (rules : RulesMap source target)
    {context : Ctx Head k} {positions : DeclName → Option (Fin k)}
    {term type : Tm Head 0} (typed : FormationSensitive.Typing source .nil term type)
    (primitive : TypedValues source target context (parameterValues positions)) :
    FormationSensitive.Typing target context (parameterTerm positions term) (parameterTerm positions type) :=
  typing rules typed primitive (fun index => Fin.elim0 index)

/-- The parameter telescope is formed independently; closure retains each
actual product and universe join of the target presentation. -/
theorem parameterProgram_typing {source target : Rules Head} (rules : RulesMap source target)
    (universes : FormationSensitive.UniverseRegularity target)
    (joins : ∀ {first second}, target.isUniverse first → target.isUniverse second →
      ∃ result, target.isUniverse result ∧ target.join first second result)
    {context : Ctx Head k} (formed : FormationSensitive.ContextFormation target context)
    {positions : DeclName → Option (Fin k)} {term type : Tm Head 0}
    (typed : FormationSensitive.Typing source .nil term type)
    (primitive : TypedValues source target context (parameterValues positions)) :
    FormationSensitive.Typing target .nil (parameterProgram context positions term)
      (closeType context (parameterTerm positions type)) :=
  close_typed universes joins formed (parameterTerm_typing rules typed primitive)

/-- Specializing the one compiled lambda program is an actual native
application, with the argument substitution checked in the original telescope. -/
theorem parameterApplication_judgment {source target : Rules Head} (rules : RulesMap source target)
    (universes : FormationSensitive.UniverseRegularity target)
    (joins : ∀ {first second}, target.isUniverse first → target.isUniverse second →
      ∃ result, target.isUniverse result ∧ target.join first second result)
    {context : Ctx Head k} (formed : FormationSensitive.ContextFormation target context)
    {positions : DeclName → Option (Fin k)} {term type : Tm Head 0}
    (typed : FormationSensitive.Typing source .nil term type)
    (primitive : TypedValues source target context (parameterValues positions))
    {destination : Ctx Head m} (destinationFormed : FormationSensitive.ContextFormation target destination)
    (arguments : Sub Head k m) (argumentsTyped : FormationSensitive.CtxMor target context destination arguments) :
    FormationSensitive.Judgment target destination
      (applyClosed context arguments (liftClosed (parameterProgram context positions term)))
      (interpret (specializedValues positions arguments) Fin.elim0 type) := by
  have closed := parameterProgram_typing rules universes joins formed typed primitive
  have lifted := liftClosed_typing closed destination
  have applied := apply_typed argumentsTyped lifted
  rw [parameterTerm_specialize] at applied
  exact ⟨destinationFormed, applied⟩

/-- The existing telescope replay is retained. Its exact endpoint is the
specialized original term, rather than a fresh acceptance marker. -/
theorem parameterProgram_checked [DecidableEq Head]
    (context : Ctx Head k) (positions : DeclName → Option (Fin k))
    (arguments : Sub Head k m) (term : Tm Head 0) :
    (applicationCode context arguments (parameterTerm positions term)).check
      (fun _ _ => False) noRoot
      (applyClosed context arguments (liftClosed (parameterProgram context positions term)))
      (interpret (specializedValues positions arguments) Fin.elim0 term) = true := by
  have checked := applicationCode_checked context arguments (parameterTerm positions term)
  rw [parameterTerm_specialize] at checked
  exact checked

theorem parameterProgram_stepCount
    (context : Ctx Head k) (positions : DeclName → Option (Fin k))
    (arguments : Sub Head k m) (term : Tm Head 0) :
    (applicationCode context arguments (parameterTerm positions term)).stepCount = k :=
  applicationCode_stepCount context arguments (parameterTerm positions term)

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConstantSubstitution

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConstantSubstitution

variable {Head : Type} {n m k : Nat}

/-- Literal declaration lookup, primitive type formation and the actual
parameter positions earn the primitive typing contract used by the whole
program theorem. No complete program derivation is supplied as a field. -/
theorem TypedValues.ofDeclarationParameters
    {source target : Rules Head} {context : Ctx Head k}
    {positions : DeclName → Option (Fin k)}
    (typesUnselected : ∀ {name type}, source.constantType name = some type →
      ∀ dependency ∈ ConstantExpansion.constantNames type, positions dependency = none)
    (selected : ∀ {name type index}, source.constantType name = some type →
      positions name = some index → Ctx.lookup context index = liftClosed type)
    (kept : ∀ {name type}, source.constantType name = some type → positions name = none →
      target.constantType name = some type ∧
      ∃ universeHead, FormationSensitive.Typing target .nil type (.head universeHead) ∧
        target.isUniverse universeHead) :
    TypedValues source target context (parameterValues positions) := by
  intro name type known
  have unchanged := parameterTerm_eq_liftClosed (Head := Head) positions type (typesUnselected known)
  change FormationSensitive.Typing target context (parameterValues positions name) (parameterTerm positions type)
  rw [unchanged]
  cases chosen : positions name with
  | some index =>
      have actual := FormationSensitive.Typing.var (R := target) (Γ := context) index
      rw [selected known chosen] at actual
      simpa only [parameterValues, chosen] using actual
  | none =>
      obtain ⟨lookup, universeHead, formed, isUniverse⟩ := kept known chosen
      simpa only [parameterValues, chosen] using
        (FormationSensitive.Typing.const (Γ := context) lookup formed isUniverse)

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.ConstantSubstitution


set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration.FiniteParameters

variable {Head : Type} {count parameterCount : Nat}

/-- The source template computation is genuinely empty. The destination may
retain computation; none is imported into this source premise. -/
theorem rootFree (base : Rules Head) (baseFree : ConstantSubstitution.RootFree base.computation)
    (original : List (DeclName × Entry Head)) (names : Fin count → DeclName)
    (types : Fin count → Tm Head 0)
    (opaqueOriginal : ∀ name value, (name, value) ∈ original → value.value? = none) :
    ConstantSubstitution.RootFree (extendRules base (signature original names types)).computation := by
  intro n left right root
  cases root with
  | inherited inherited => exact baseFree inherited
  | delta selected =>
      rw [value_none original names types opaqueOriginal] at selected
      cases selected
  | declared impossible =>
      rw [signature, Signature.computation_ofList] at impossible
      exact impossible.elim

theorem rulesMap (base : Rules Head) (baseFree : ConstantSubstitution.RootFree base.computation)
    (original : List (DeclName × Entry Head)) (names : Fin count → DeclName)
    (types : Fin count → Tm Head 0)
    (opaqueOriginal : ∀ name value, (name, value) ∈ original → value.value? = none)
    (destination : Signature Head) :
    ConstantSubstitution.RulesMap (extendRules base (signature original names types)) (extendRules base destination) where
  headTyping := fun proof => proof
  isUniverse := fun proof => proof
  join := fun proof => proof
  cumulative := fun proof => proof
  headEquality := fun proof => proof
  rootFree := rootFree base baseFree original names types opaqueOriginal

/-- An actual selected declaration resolves to the same finite native
context position, including when two positions have equal function types. -/
theorem selected_lookup (base : Rules Head)
    (bare : ∀ name, base.constantType name = none)
    (original : List (DeclName × Entry Head)) (names : Fin count → DeclName)
    (types : Fin count → Tm Head 0) (positions : DeclName → Option (Fin parameterCount))
    (indices : Fin count → Fin parameterCount)
    (readback : ∀ index, positions (names index) = some (indices index))
    (untouched : ∀ name value, (name, value) ∈ original → positions name = none)
    (context : Ctx Head parameterCount) (contextLookup : ∀ index, Ctx.lookup context (indices index) = liftClosed (types index))
    {name : DeclName} {type : Tm Head 0} {position : Fin parameterCount}
    (known : (extendRules base (signature original names types)).constantType name = some type)
    (chosen : positions name = some position) : Ctx.lookup context position = liftClosed type := by
  obtain ⟨value, selected, sameType⟩ := constant_entry base bare original names types known
  have member := Signature.entries_ofList_mem (declarations names types ++ original) selected
  rcases List.mem_append.mp member with added | old
  · obtain ⟨index, same⟩ := List.mem_ofFn.mp added
    have nameSame : names index = name := congrArg Prod.fst same
    have valueSame : entry types index = value := congrArg Prod.snd same
    have samePosition : indices index = position := by
      have recovered := readback index
      rw [nameSame, chosen] at recovered
      exact (Option.some.inj recovered).symm
    rw [← samePosition, contextLookup, ← sameType, ← valueSame]
    rfl
  · have unselected := untouched name value old
    rw [unselected] at chosen
    cases chosen

/-- Type dependencies are inspected declaration by declaration in the finite
source. No whole-term preservation statement is an input. -/
theorem dependencies_kept (base : Rules Head)
    (bare : ∀ name, base.constantType name = none)
    (original : List (DeclName × Entry Head)) (names : Fin count → DeclName)
    (types : Fin count → Tm Head 0) (positions : DeclName → Option (Fin parameterCount))
    (indices : Fin count → Fin parameterCount)
    (readback : ∀ index, positions (names index) = some (indices index))
    (untouched : ∀ name value, (name, value) ∈ original → positions name = none)
    (parameterTypes : ∀ index dependency, dependency ∈ ConstantExpansion.constantNames (types index) → positions dependency = none)
    (originalTypes : ∀ name value, (Signature.ofList original).entries name = some value →
      ∀ dependency ∈ ConstantExpansion.constantNames value.type, positions dependency = none)
    {name : DeclName} {type : Tm Head 0}
    (known : (extendRules base (signature original names types)).constantType name = some type) :
    ∀ dependency ∈ ConstantExpansion.constantNames type, positions dependency = none := by
  obtain ⟨value, selected, sameType⟩ := constant_entry base bare original names types known
  subst type
  have member := Signature.entries_ofList_mem (declarations names types ++ original) selected
  rcases List.mem_append.mp member with added | old
  · obtain ⟨index, same⟩ := List.mem_ofFn.mp added
    have valueSame : entry types index = value := congrArg Prod.snd same
    rw [← valueSame]
    exact parameterTypes index
  · rw [kept original names types positions indices readback name (untouched name value old)] at selected
    exact originalTypes name value selected

/-- Primitive target lookup and type formation plus the earned finite selector
and context lookups produce the parameter interpretation used by the generic
native program compiler. -/
theorem values_typed (base : Rules Head)
    (bare : ∀ name, base.constantType name = none)
    (original : List (DeclName × Entry Head)) (names : Fin count → DeclName)
    (types : Fin count → Tm Head 0) (positions : DeclName → Option (Fin parameterCount))
    (indices : Fin count → Fin parameterCount)
    (readback : ∀ index, positions (names index) = some (indices index))
    (untouched : ∀ name value, (name, value) ∈ original → positions name = none)
    (parameterTypes : ∀ index dependency, dependency ∈ ConstantExpansion.constantNames (types index) → positions dependency = none)
    (originalTypes : ∀ name value, (Signature.ofList original).entries name = some value →
      ∀ dependency ∈ ConstantExpansion.constantNames value.type, positions dependency = none)
    (target : Rules Head) (context : Ctx Head parameterCount)
    (contextLookup : ∀ index, Ctx.lookup context (indices index) = liftClosed (types index))
    (primitive : ∀ name value, (Signature.ofList original).entries name = some value →
      target.constantType name = some value.type ∧
      ∃ universeHead, FormationSensitive.Typing target .nil value.type (.head universeHead) ∧ target.isUniverse universeHead) :
    ConstantSubstitution.TypedValues (extendRules base (signature original names types)) target context
      (ConstantSubstitution.parameterValues positions) := by
  apply ConstantSubstitution.TypedValues.ofDeclarationParameters
  · exact dependencies_kept base bare original names types positions indices readback untouched parameterTypes originalTypes
  · exact selected_lookup base bare original names types positions indices readback untouched context contextLookup
  · intro name type known unselected
    obtain ⟨value, selected, sameType⟩ := constant_entry base bare original names types known
    rw [kept original names types positions indices readback name unselected] at selected
    rw [← sameType]
    exact primitive name value selected

/-- The finite signature is well formed once each actual primitive type has
its own source formation proof. Transparency and computation are checked
separately rather than inferred from well-typed endpoints. -/
theorem wellFormed (base : Rules Head)
    (bare : ∀ name, base.constantType name = none)
    (original : List (DeclName × Entry Head)) (names : Fin count → DeclName)
    (types : Fin count → Tm Head 0)
    (opaqueOriginal : ∀ name value, (name, value) ∈ original → value.value? = none)
    (primitiveTypes : ∀ name type, (signature original names types).typeOf? name = some type →
      ∃ universeHead, FormationSensitive.Typing (extendRules base (signature original names types)) .nil type (.head universeHead) ∧
        base.isUniverse universeHead) :
    (signature original names types).WellFormed base where
  fresh := by intro name value _; exact bare name
  types := by
    intro name type known
    obtain ⟨universeHead, typed, universeWitness⟩ := primitiveTypes name type known
    exact ⟨universeHead, universeWitness, typed.toRaw⟩
  values := by
    intro name type value _ impossible
    rw [value_none original names types opaqueOriginal] at impossible
    cases impossible
  noSelfDelta := by
    intro name value impossible
    rw [value_none original names types opaqueOriginal] at impossible
    cases impossible
  declaredPreserves := by
    intro n context left right type impossible _
    rw [signature, Signature.computation_ofList] at impossible
    exact impossible.elim

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration.FiniteParameters

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

namespace FormationSensitive.Typing

variable {Head : Type} {n : Nat} {R : Rules Head}

/-- Constants occurring in a typed term have actual declarations. This concerns
the term's support; it does not demand declarations for arbitrary context data. -/
theorem constants_declared {context : Ctx Head n} {term type : Tm Head n}
    (typed : FormationSensitive.Typing R context term type) :
    ∀ name ∈ ConstantExpansion.constantNames term, R.constantType name ≠ none := by
  induction typed <;>
    simp_all [ConstantExpansion.constantNames, List.mem_append, or_imp, forall_and]

/-- Expansion fixes a typed term when it fixes the actually declared constants.
Undeclared names outside the term's support impose no obligation. -/
theorem expand_eq_of_declared_constants {context : Ctx Head n} {term type : Tm Head n}
    (typed : FormationSensitive.Typing R context term type)
    (bodies : ConstantExpansion.Bodies Head)
    (agreement : ∀ name, R.constantType name ≠ none → bodies name = .const name) :
    ConstantExpansion.expand bodies term = term := by
  calc
    ConstantExpansion.expand bodies term =
        ConstantExpansion.expand (fun name => .const name) term :=
      ConstantExpansion.expand_eq_of_agreement _ _ term
        (fun name present => agreement name (typed.constants_declared name present))
    _ = term := ConstantExpansion.expand_identity term

end FormationSensitive.Typing

#print axioms FormationSensitive.Typing.constants_declared
#print axioms FormationSensitive.Typing.expand_eq_of_declared_constants

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
