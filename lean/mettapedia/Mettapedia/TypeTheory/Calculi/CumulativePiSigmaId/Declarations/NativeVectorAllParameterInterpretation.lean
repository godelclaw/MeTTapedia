import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllOpaqueFormation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.DeclarationParameterTelescope
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.CumulativeConversion
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Conservativity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Cumulative
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.HeadMorphism
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.ContextualSubstitutionEquality
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.ConstantInstantiation

/-!
# Parameter interpretation of native Vector All types

The eight original Nat/Vec declarations generate an ordered dependent
parameter telescope. The existing constant interpreter moves the two actual
All type programs and their four inputs into the declaration-free tower.
Independent replay forms that telescope and both results. Proved tower
conversion transfers this root-free part to typed equality.

A generic typed parameter substitution installs the actual declared
constants. Exact readback recovers the original terms at their original
inputs and universe bounds, in both the opaque and computation-enabled
profiles. No pointwise predicate witnesses are assumed. Local native iota
typing, evidence-map typing and the neutral inverse remain separate.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Declaration RussellTarski
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeVectorAll.Universes (dataLevel predicateLevel resultLevel)
open NativeVectorAll.Universes.CumulativeElimination (upperLevel)
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Universes.ParameterInterpretation

local instance : DecidableRel Tower.rules.headEq :=
  fun h u => LevelTower.instDecidableHeadEq h u

private def decoder : StructuralConversionCode.RootDecoder Tower.rules.computation := .ofEmpty _ rfl

private def choices : FormationSensitiveElaboration.Choices Tower.Head decoder.Code where
  headType head := some (StructuralTypingReplay.TowerDecisions.headTarget head)
  join first second := match first, second with
    | .sort first, .sort second => some (.sort (.max first second))
    | _, _ => none
  cumulative first second := decide (Tower.rules.cumulative first second)
  normalize fuel term := match StructuralConversionSearch.normalize decoder (fun _ => none)
      (headEq := Tower.rules.headEq) fuel term with
    | none => term
    | some result => result.term
  conversion fuel left right := StructuralConversionSearch.compare decoder (fun _ => none)
    (headEq := Tower.rules.headEq) fuel left right


def names (index : Fin 8) : DeclName :=
  (NativeNaturalVectorFamilies.declarations.get index).1

def types (index : Fin 8) : Tower.Tm 0 :=
  substLevelsTm NativeVectorAll.Universes.CumulativeElimination.levels
    (NativeNaturalVectorFamilies.declarations.get index).2.type

def parameters : Tower.Ctx 8 := DependentParameters.context names types 8 (by decide)

def contextA : Tower.Ctx 9 := .snoc parameters (sortTm dataLevel)
def contextAP : Tower.Ctx 10 := .snoc contextA (.pi (.var 0) (sortTm predicateLevel))
def contextAPN : Tower.Ctx 11 := .snoc contextAP (.var 9)
def context : Tower.Ctx 12 := .snoc contextAPN (.app (.app (.var 6) (.var 2)) (.var 0))

def valuesAtInputs : ConstantSubstitution.Values Tower.Head 12 :=
  ConstantSubstitution.liftValues (ConstantSubstitution.liftValues
    (ConstantSubstitution.liftValues (ConstantSubstitution.liftValues (DependentParameters.values names 8 (by decide)))))

def inputVariables : Sub Tower.Head 4 12 :=
  fun index => .var (Fin.castLE (by decide) index)

def lower : Tower.Tm 12 := ConstantSubstitution.interpret valuesAtInputs inputVariables
  NativeVectorAll.Universes.subject

def upper : Tower.Tm 12 := ConstantSubstitution.interpret valuesAtInputs inputVariables
  (NativeVectorAll.Universes.Canonical.typeProgramAtUniverse upperLevel)

def lowerAccepted : Bool := (FormationSensitiveElaboration.elaborate Tower.rules decoder choices 256
  context lower (sortTm resultLevel)).isSome

def upperAccepted : Bool := (FormationSensitiveElaboration.elaborate Tower.rules decoder choices 256
  context upper (sortTm upperLevel)).isSome

theorem lower_accepted : lowerAccepted = true := by decide +kernel
theorem upper_accepted : upperAccepted = true := by decide +kernel

theorem lower_formed : FormationSensitive.Judgment Tower.rules context lower (sortTm resultLevel) := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp lower_accepted
  exact FormationSensitiveElaboration.elaborate_sound Tower.rules decoder choices 256 _ _ _ submission produced

theorem upper_formed : FormationSensitive.Judgment Tower.rules context upper (sortTm upperLevel) := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp upper_accepted
  exact FormationSensitiveElaboration.elaborate_sound Tower.rules decoder choices 256 _ _ _ submission produced

open TypedEquality
open TypedEquality.Normalization (CtxFormed IsType)

theorem context_typed : CtxFormed Tower.rules context :=
  TypedEquality.Normalization.FormationSensitive.ContextFormation.toTyped
    (S := TypedEquality.Normalization.TowerModel.setting (fun _ => (0 : Nat)))
    TypedEquality.Normalization.TowerModel.facts TypedEquality.Normalization.TowerModel.roots
    TypedEquality.Normalization.TowerModel.heads LevelTower.churchRosser lower_formed.context

theorem lower_typed : Typed Tower.rules context lower (sortTm resultLevel) :=
  TypedEquality.Normalization.FormationSensitive.Typing.toTyped
    (S := TypedEquality.Normalization.TowerModel.setting (fun _ => (0 : Nat)))
    TypedEquality.Normalization.TowerModel.facts TypedEquality.Normalization.TowerModel.roots
    TypedEquality.Normalization.TowerModel.heads LevelTower.churchRosser lower_formed.typing context_typed

theorem upper_typed : Typed Tower.rules context upper (sortTm upperLevel) :=
  TypedEquality.Normalization.FormationSensitive.Typing.toTyped
    (S := TypedEquality.Normalization.TowerModel.setting (fun _ => (0 : Nat)))
    TypedEquality.Normalization.TowerModel.facts TypedEquality.Normalization.TowerModel.roots
    TypedEquality.Normalization.TowerModel.heads LevelTower.churchRosser upper_formed.typing context_typed

theorem parameters_formed : CtxFormed Tower.rules parameters := by
  cases context_typed with
  | snoc first _ =>
      cases first with
      | snoc second _ =>
          cases second with
          | snoc third _ =>
              cases third with
              | snoc fourth _ => exact fourth

theorem known (index : Fin 8) : NativeVectorAll.Universes.OpaqueFormation.rules.constantType
    (names index) = some (types index) := by
  fin_cases index <;> rfl

def arguments : Sub Tower.Head 8 0 := DependentParameters.constantArguments names 8 (by decide)

theorem arguments_typed : SubstMor NativeVectorAll.Universes.OpaqueFormation.rules parameters
    (.nil : Tower.Ctx 0) arguments :=
  DependentParameters.constantArguments_typed
    (Declaration.includeMorphism Tower.rules NativeVectorAll.Universes.OpaqueFormation.signature)
    names types known parameters_formed 8 (by decide)

theorem primitive_closed_typed (index : Fin 8) :
    Typed OpaqueFormation.rules (.nil : Tower.Ctx 0) (.const (names index)) (types index) :=
  DependentParameters.constant_typed
    (Declaration.includeMorphism Tower.rules OpaqueFormation.signature)
    names types known parameters_formed index

/-- The actual dependent Vector eliminator is a closed declaration instance. -/
theorem eliminator_closed_typed :
    Typed OpaqueFormation.rules (.nil : Tower.Ctx 0) (.const (names 7)) (types 7) :=
  DependentParameters.constant_typed
    (Declaration.includeMorphism Tower.rules OpaqueFormation.signature)
    names types known parameters_formed 7

theorem primitive_typed {n : Nat} (gamma : Tower.Ctx n) (index : Fin 8) :
    Typed OpaqueFormation.rules gamma (.const (names index)) (liftClosed (types index)) := by
  have lifted := (primitive_closed_typed index).substitute
    (Δ := gamma) (σ := fun index => Fin.elim0 index) (fun index => Fin.elim0 index)
  simpa only [TypedEquality.Normalization.subst_closed, subst] using lifted

def inputSub : Sub Tower.Head 12 4 := liftSub (liftSub (liftSub (liftSub arguments)))

theorem inputs_typed : SubstMor NativeVectorAll.Universes.OpaqueFormation.rules context
    NativeVectorAll.Universes.context inputSub := by
  have first := arguments_typed.lift (sortTm dataLevel)
  have second := first.lift (.pi (.var 0) (sortTm predicateLevel))
  have third := second.lift (.var 9)
  exact third.lift (.app (.app (.var 6) (.var 2)) (.var 0))

theorem value_readback (name : DeclName) :
    subst inputSub (valuesAtInputs name) = (.const name : Tower.Tm 4) := by
  simp only [inputSub, valuesAtInputs, ConstantSubstitution.liftValues,
    subst_liftSub_wk, arguments, DependentParameters.value_readback, rename]

theorem variable_readback (index : Fin 4) :
    subst inputSub (inputVariables index) = (.var index : Tower.Tm 4) := by
  fin_cases index <;> rfl

theorem term_readback (term : Tower.Tm 4) :
    subst inputSub (ConstantSubstitution.interpret valuesAtInputs inputVariables term) = term := by
  rw [ConstantSubstitution.subst_interpret]
  have sameValues : (fun name => subst inputSub (valuesAtInputs name)) =
      (fun name => (.const name : Tower.Tm 4)) := funext value_readback
  have sameVariables : (fun index => subst inputSub (inputVariables index)) =
      (ids : Sub Tower.Head 4 4) := funext variable_readback
  rw [sameValues, sameVariables, ConstantSubstitution.interpret_constants, subst_ids]

/-- The complete checked parameter/input context survives declaration extension. -/
theorem context_core_in_opaque : CtxFormed NativeVectorAll.Universes.OpaqueFormation.rules context :=
  context_typed.of_morphism
    (Declaration.includeMorphism Tower.rules NativeVectorAll.Universes.OpaqueFormation.signature)

theorem context_opaque_formed :
    CtxFormed NativeVectorAll.Universes.OpaqueFormation.rules NativeVectorAll.Universes.context := by
  have first := arguments_typed.lift (sortTm dataLevel)
  have second := first.lift (.pi (.var 0) (sortTm predicateLevel))
  have third := second.lift (.var 9)
  cases context_core_in_opaque with
  | snoc gamma11 vectorType =>
      cases gamma11 with
      | snoc gamma10 naturalType =>
          cases gamma10 with
          | snoc gamma9 predicateType =>
              cases gamma9 with
              | snoc _ elementType =>
                  exact .snoc (.snoc (.snoc (.snoc .nil
                    (TypedEquality.Normalization.IsType.substitute elementType arguments_typed))
                    (TypedEquality.Normalization.IsType.substitute predicateType first))
                    (TypedEquality.Normalization.IsType.substitute naturalType second))
                    (TypedEquality.Normalization.IsType.substitute vectorType third)

theorem context_full_formed :
    CtxFormed NativeVectorAll.Universes.CumulativeElimination.rules NativeVectorAll.Universes.context :=
  context_opaque_formed.of_morphism
    (Declaration.extensionMorphism Tower.rules NativeVectorAll.Universes.OpaqueFormation.includes)

theorem lower_opaque_typed : Typed NativeVectorAll.Universes.OpaqueFormation.rules
    NativeVectorAll.Universes.context NativeVectorAll.Universes.subject (sortTm resultLevel) := by
  have linked := (lower_typed.of_morphism
    (Declaration.includeMorphism Tower.rules NativeVectorAll.Universes.OpaqueFormation.signature)).substitute inputs_typed
  simpa only [lower, term_readback, sortTm, subst] using linked

theorem upper_opaque_typed : Typed NativeVectorAll.Universes.OpaqueFormation.rules
    NativeVectorAll.Universes.context
    (NativeVectorAll.Universes.Canonical.typeProgramAtUniverse upperLevel) (sortTm upperLevel) := by
  have linked := (upper_typed.of_morphism
    (Declaration.includeMorphism Tower.rules NativeVectorAll.Universes.OpaqueFormation.signature)).substitute inputs_typed
  simpa only [upper, term_readback, sortTm, subst] using linked

theorem lower_full_typed : Typed NativeVectorAll.Universes.CumulativeElimination.rules
    NativeVectorAll.Universes.context NativeVectorAll.Universes.subject (sortTm resultLevel) :=
  lower_opaque_typed.of_morphism (Declaration.extensionMorphism Tower.rules NativeVectorAll.Universes.OpaqueFormation.includes)

theorem upper_full_typed : Typed NativeVectorAll.Universes.CumulativeElimination.rules
    NativeVectorAll.Universes.context
    (NativeVectorAll.Universes.Canonical.typeProgramAtUniverse upperLevel) (sortTm upperLevel) :=
  upper_opaque_typed.of_morphism (Declaration.extensionMorphism Tower.rules NativeVectorAll.Universes.OpaqueFormation.includes)

/-- Parameter interpretation retains the complete original term syntax. -/
theorem interpretation_injective :
    Function.Injective (ConstantSubstitution.interpret valuesAtInputs inputVariables) := by
  intro first second same
  have restored := congrArg (subst inputSub) same
  simpa only [term_readback] using restored

/-- The unparameterized eliminator type needs its declared dependencies.
It cannot be formed in the declaration-free tower, at any displayed type. -/
theorem eliminator_type_needs_declarations (displayed : Tower.Tm 0) :
    ¬ FormationSensitive.Typing Tower.rules (.nil : Tower.Ctx 0) (types 7) displayed := by
  intro typed
  have present : NativeNaturalVectorFamilies.natName ∈
      ConstantExpansion.constantNames (types 7) := by decide +kernel
  exact (typed.constants_declared NativeNaturalVectorFamilies.natName present) rfl

#print axioms context_core_in_opaque
#print axioms context_full_formed
#print axioms interpretation_injective
#print axioms eliminator_type_needs_declarations

#print axioms primitive_closed_typed
#print axioms arguments_typed
#print axioms lower_opaque_typed
#print axioms upper_opaque_typed
#print axioms lower_full_typed
#print axioms upper_full_typed

#print axioms lower_typed
#print axioms upper_typed

#print axioms lower_formed
#print axioms upper_formed
/-! ## The constructor branch in the parameterized core

Its beta computation is checked where all datatype operations are parameters.
Native computation is introduced only after the primitive assignment is linked.
-/

namespace TypeBranch

def context : Tower.Ctx 13 := .snoc NativeVectorAll.Universes.ParameterInterpretation.context (.var 3)

theorem context_formed : TypedEquality.Normalization.CtxFormed Tower.rules context :=
  .snoc NativeVectorAll.Universes.ParameterInterpretation.context_typed ⟨_, .sort dataLevel, .var 3⟩

def branch : Tower.Tm 13 := NativeVectorAll.allTypeConsCase (.var 3)

def branchType (level : LevelExpr Nat) : Tower.Tm 13 :=
  .pi (.var 12) (.pi (.var 5)
    (.pi (.app (.app (.var 10) (.var 6)) (.var 1)) (.pi (sortTm level) (sortTm level))))

def branchAccepted (level : LevelExpr Nat) : Bool :=
  (FormationSensitiveElaboration.elaborate Tower.rules decoder choices 256
    context branch (branchType level)).isSome

theorem lower_branch_accepted : branchAccepted resultLevel = true := by decide +kernel
theorem upper_branch_accepted : branchAccepted upperLevel = true := by decide +kernel

theorem branch_formed (level : LevelExpr Nat) (accepted : branchAccepted level = true) :
    FormationSensitive.Judgment Tower.rules context branch (branchType level) := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp accepted
  exact FormationSensitiveElaboration.elaborate_sound Tower.rules decoder choices 256 _ _ _ submission produced

theorem branch_typed (level : LevelExpr Nat) (accepted : branchAccepted level = true) :
    Typed Tower.rules context branch (branchType level) :=
  TypedEquality.Normalization.FormationSensitive.Typing.toTyped
    (S := TypedEquality.Normalization.TowerModel.setting (fun _ => (0 : Nat)))
    TypedEquality.Normalization.TowerModel.facts TypedEquality.Normalization.TowerModel.roots
    TypedEquality.Normalization.TowerModel.heads LevelTower.churchRosser
    (branch_formed level accepted).typing context_formed

def tailType (level : LevelExpr Nat) : Tower.Tm 13 :=
  rename wk (ConstantSubstitution.interpret NativeVectorAll.Universes.ParameterInterpretation.valuesAtInputs
    NativeVectorAll.Universes.ParameterInterpretation.inputVariables
    (NativeVectorAll.Universes.Canonical.typeProgramAtUniverse level))

theorem lower_tail_typed : Typed Tower.rules context (tailType resultLevel) (sortTm resultLevel) := by
  simpa only [context, tailType, NativeVectorAll.Universes.ParameterInterpretation.lower,
    NativeVectorAll.Universes.Canonical.typeProgramAtUniverse, NativeVectorAll.Universes.subject,
    rename, sortTm] using
      (NativeVectorAll.Universes.ParameterInterpretation.lower_typed.weaken (extension := .var 3))

theorem upper_tail_typed : Typed Tower.rules context (tailType upperLevel) (sortTm upperLevel) := by
  exact NativeVectorAll.Universes.ParameterInterpretation.upper_typed.weaken

def rawResult (level : LevelExpr Nat) : Tower.Tm 13 :=
  TypedEquality.Normalization.appSpine branch [.var 2, .var 0, .var 1, tailType level]

def result (level : LevelExpr Nat) : Tower.Tm 13 :=
  .sigma (.app (.var 3) (.var 0)) (rename wk (tailType level))

theorem raw_typed (level : LevelExpr Nat) (accepted : branchAccepted level = true)
    (tailTyped : Typed Tower.rules context (tailType level) (sortTm level)) :
    Typed Tower.rules context (rawResult level) (sortTm level) :=
  .appElim (.appElim (.appElim (.appElim (branch_typed level accepted) (.var 2)) (.var 0))
    (.var 1)) tailTyped

theorem result_typed (level : LevelExpr Nat)
    (bound : Tower.rules.cumulative (.sort predicateLevel) (.sort level))
    (tailTyped : Typed Tower.rules context (tailType level) (sortTm level)) :
    Typed Tower.rules context (result level) (sortTm level) := by
  have predicateTyped : Typed Tower.rules context (.var 3)
      (.pi (.var 4) (sortTm predicateLevel)) := .var 3
  have headTyped : Typed Tower.rules context (.var 0) (.var 4) := .var 0
  have domainTyped : Typed Tower.rules context (.app (.var 3) (.var 0)) (sortTm predicateLevel) :=
    .appElim predicateTyped headTyped
  have formed : Typed Tower.rules context (result level) (sortTm (.max predicateLevel level)) :=
    .sigmaForm domainTyped (.sort predicateLevel) tailTyped.weaken (.sort level) (.sorts _ _)
  apply Derivable.sub formed
  apply Derivable.subUniv
  intro valuation
  exact Nat.max_le.mpr ⟨bound valuation, Nat.le_refl _⟩

theorem raw_steps (level : LevelExpr Nat) : Reduces Tower.rules (rawResult level) (result level) :=
  NativeVectorAll.Universes.Canonical.consType_steps Tower.rules
    (.var 3) (.var 2) (.var 0) (.var 1) (tailType level)

theorem beta_typed (level : LevelExpr Nat) (accepted : branchAccepted level = true)
    (bound : Tower.rules.cumulative (.sort predicateLevel) (.sort level))
    (tailTyped : Typed Tower.rules context (tailType level) (sortTm level)) :
    Equal Tower.rules context (rawResult level) (result level) (sortTm level) := by
  have converted : Conv Tower.rules.headEq (rawResult level) (result level) Tower.rules.computation := by
    exact Relation.EqvGen.reflTransGen_le_eqvGen _ _ _ (raw_steps level)
  exact TypedEquality.Normalization.Conv.toEqual
    (S := TypedEquality.Normalization.TowerModel.setting (fun _ => (0 : Nat)))
    TypedEquality.Normalization.TowerModel.facts TypedEquality.Normalization.TowerModel.roots
    TypedEquality.Normalization.TowerModel.heads LevelTower.churchRosser
    context_formed converted (raw_typed level accepted tailTyped) (result_typed level bound tailTyped)

theorem lower_beta : Equal Tower.rules context (rawResult resultLevel) (result resultLevel) (sortTm resultLevel) :=
  beta_typed resultLevel lower_branch_accepted (by intro valuation; exact Nat.le_max_right _ _) lower_tail_typed

theorem upper_beta : Equal Tower.rules context (rawResult upperLevel) (result upperLevel) (sortTm upperLevel) :=
  beta_typed upperLevel upper_branch_accepted
    (by intro valuation; exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _)) upper_tail_typed

#print axioms lower_beta
#print axioms upper_beta

end TypeBranch

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Universes.ParameterInterpretation
