import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeIdentity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.HeadMorphism
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaboration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSearch
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.Conservativity

/-!
# Object congruence from declared identity elimination

The term is the usual action of a function on an identity proof. It is
checked in the declaration-free cumulative tower with the identity eliminator
as one typed parameter. Tower conversion transfers that checked derivation to
typed equality. Universe substitution and ordinary typed substitution then
install any checked implementation of the original identity declaration.

The parameter is discharged by concrete clients; it is not a new constant,
axiom, computation rule, or global preservation assumption. The negative
control rejects a term that ignores its path and claims reflexivity at the
other endpoint. Producer refusal is not a non-derivability result.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeIdentityCongruence
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
def sourceLevel : LevelExpr Nat := .param 0
def identityLevels (_ : Nat) : LevelExpr Nat := sourceLevel
def identityType := RussellTarski.substLevelsTm identityLevels
  NativeIndexedFamilies.Intrinsic.identityEliminateType

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


def context : Tower.Ctx 1 := .snoc .nil identityType

def type : Tower.Tm 0 :=
  .pi (sortTm sourceLevel) (.pi (sortTm sourceLevel)
    (.pi (.pi (.var 1) (.var 1)) (.pi (.var 2) (.pi (.var 3)
      (.pi (.id (.var 4) (.var 1) (.var 0))
        (.id (.var 4) (.app (.var 3) (.var 2)) (.app (.var 3) (.var 1))))))))

def functionType : Tower.Tm 1 := liftClosed type

def motive : Tower.Tm 7 :=
  .lam (.lam (.id (.var 6) (.app (.var 5) (.var 4)) (.app (.var 5) (.var 1))))

def body : Tower.Tm 7 :=
  .app (.app (.app (.app (.app (.app (.var 6) (.var 5)) (.var 2)) motive)
    (.refl (.app (.var 3) (.var 2)))) (.var 1)) (.var 0)

def subject : Tower.Tm 1 := .lam (.lam (.lam (.lam (.lam (.lam body)))))

def accepted : Bool := (FormationSensitiveElaboration.elaborate Tower.rules decoder choices 256
  context subject functionType).isSome

theorem accepted_eq_true : accepted = true := by decide +kernel

theorem formed : FormationSensitive.Judgment Tower.rules context subject functionType := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp accepted_eq_true
  exact FormationSensitiveElaboration.elaborate_sound Tower.rules decoder choices 256 _ _ _
    submission produced

theorem typed : TypedEquality.Typed Tower.rules context subject functionType :=
  TypedEquality.Normalization.FormationSensitive.Typing.toTyped
    (S := TypedEquality.Normalization.TowerModel.setting (fun _ => (0 : Nat)))
    TypedEquality.Normalization.TowerModel.facts TypedEquality.Normalization.TowerModel.roots
    TypedEquality.Normalization.TowerModel.heads LevelTower.churchRosser
    formed.typing (.snoc .nil ⟨_, .sort _,
      (FormationSensitiveNativeIdentity.TowerFormation.identityEliminateType_typed.mapHead
        (RussellTarski.levelSubstMorphism identityLevels))⟩)

theorem identity_type_at (level : LevelExpr Nat) :
    RussellTarski.substLevelsTm (fun _ => level) identityType =
      RussellTarski.substLevelsTm (fun _ => level)
        NativeIndexedFamilies.Intrinsic.identityEliminateType := rfl

def instantiate {n : Nat} (level : LevelExpr Nat) (implementation : Tower.Tm n) : Tower.Tm n :=
  subst (consSub implementation Fin.elim0)
    (RussellTarski.substLevelsTm (fun _ => level) subject)

theorem instantiate_typed (signature : Declaration.Signature Tower.Head)
    {n : Nat} {ambient : Tower.Ctx n} (level : LevelExpr Nat) (implementation : Tower.Tm n)
    (checked : TypedEquality.Typed (Declaration.extendRules Tower.rules signature) ambient implementation
      (liftClosed (RussellTarski.substLevelsTm (fun _ => level)
        NativeIndexedFamilies.Intrinsic.identityEliminateType))) :
    TypedEquality.Typed (Declaration.extendRules Tower.rules signature) ambient
      (instantiate level implementation)
      (liftClosed (RussellTarski.substLevelsTm (fun _ => level) type)) := by
  have parameter : TypedEquality.SubstMor (Declaration.extendRules Tower.rules signature)
      (RussellTarski.substLevelsCtx (fun _ => level) context) ambient
      (consSub implementation Fin.elim0) := by
    intro index
    fin_cases index
    exact checked
  have lifted := (typed.mapHead (RussellTarski.levelSubstMorphism (fun _ => level))).of_morphism
    (Declaration.includeMorphism Tower.rules signature)
  exact lifted.substitute parameter

/-- Discarding the supplied path does not check at the dependent endpoint. -/
def ignoredPath : Tower.Tm 1 :=
  .lam (.lam (.lam (.lam (.lam (.lam (.refl (.app (.var 3) (.var 2))))))))

def ignoredPathAccepted : Bool :=
  (FormationSensitiveElaboration.elaborate Tower.rules decoder choices 256
    context ignoredPath functionType).isSome

theorem ignored_path_refused : ignoredPathAccepted = false := by decide +kernel

#print axioms ignored_path_refused

#print axioms instantiate_typed

#print axioms formed
#print axioms typed
/-! ## Congruence in a dependent pair fibre

The family may depend on the retained first component. Equality of two
second components at that same fibre is lifted to identity of the pairs.
The source program is checked with function congruence as its one operation
parameter; the concrete client installs the previously checked native program.
-/

namespace Pair

def context : Tower.Ctx 1 := .snoc .nil NativeIdentityCongruence.type

def operationTypeAccepted : Bool :=
  (FormationSensitiveElaboration.elaborate Tower.rules decoder choices 256 .nil
    NativeIdentityCongruence.type (sortTm (.succ sourceLevel))).isSome

theorem operation_type_accepted : operationTypeAccepted = true := by decide +kernel

theorem operation_type_formed : FormationSensitive.Judgment Tower.rules (.nil : Tower.Ctx 0)
    NativeIdentityCongruence.type (sortTm (.succ sourceLevel)) := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp operation_type_accepted
  exact FormationSensitiveElaboration.elaborate_sound Tower.rules decoder choices 256 _ _ _
    submission produced

theorem operation_type_typed : TypedEquality.Typed Tower.rules (.nil : Tower.Ctx 0)
    NativeIdentityCongruence.type (sortTm (.succ sourceLevel)) :=
  TypedEquality.Normalization.FormationSensitive.Typing.toTyped
    (S := TypedEquality.Normalization.TowerModel.setting (fun _ => (0 : Nat)))
    TypedEquality.Normalization.TowerModel.facts TypedEquality.Normalization.TowerModel.roots
    TypedEquality.Normalization.TowerModel.heads LevelTower.churchRosser
    operation_type_formed.typing .nil

def carrier : Tower.Tm 7 := .sigma (.var 5) (.app (.var 5) (.var 0))

def type : Tower.Tm 0 :=
  .pi (sortTm sourceLevel) (.pi (.pi (.var 0) (sortTm sourceLevel))
    (.pi (.var 1) (.pi (.app (.var 1) (.var 0))
      (.pi (.app (.var 2) (.var 1))
        (.pi (.id (.app (.var 3) (.var 2)) (.var 1) (.var 0))
          (.id (.sigma (.var 5) (.app (.var 5) (.var 0)))
            (.pair (.var 3) (.var 2)) (.pair (.var 3) (.var 1))))))))

def bodyAt {n : Nat} (operation : Tower.Tm (n + 6)) : Tower.Tm (n + 6) :=
  TypedEquality.Normalization.appSpine operation
    [.app (.var 4) (.var 3), .sigma (.var 5) (.app (.var 5) (.var 0)),
      .lam (.pair (.var 4) (.var 0)), .var 2, .var 1, .var 0]

def body : Tower.Tm 7 := bodyAt (.var 6)

def subject : Tower.Tm 1 := .lam (.lam (.lam (.lam (.lam (.lam body)))))

def accepted : Bool := (FormationSensitiveElaboration.elaborate Tower.rules decoder choices 512
  context subject (liftClosed type)).isSome

theorem accepted_eq_true : accepted = true := by decide +kernel

theorem formed : FormationSensitive.Judgment Tower.rules context subject (liftClosed type) := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp accepted_eq_true
  exact FormationSensitiveElaboration.elaborate_sound Tower.rules decoder choices 512 _ _ _
    submission produced

theorem typed : TypedEquality.Typed Tower.rules context subject (liftClosed type) :=
  TypedEquality.Normalization.FormationSensitive.Typing.toTyped
    (S := TypedEquality.Normalization.TowerModel.setting (fun _ => (0 : Nat)))
    TypedEquality.Normalization.TowerModel.facts TypedEquality.Normalization.TowerModel.roots
    TypedEquality.Normalization.TowerModel.heads LevelTower.churchRosser
    formed.typing (.snoc .nil ⟨_, .sort _, operation_type_typed⟩)

def shortcut : Tower.Tm 1 := .lam (.lam (.lam (.lam (.lam (.lam (.var 0))))))
def shortcutAccepted : Bool := (FormationSensitiveElaboration.elaborate Tower.rules decoder choices 512
  context shortcut (liftClosed type)).isSome

theorem shortcut_refused : shortcutAccepted = false := by decide +kernel

/-- Install a checked implementation of function congruence in the pair
program. Context, universe and program substitution are the actual core maps. -/
def instantiate {n : Nat} (level : LevelExpr Nat) (implementation : Tower.Tm n) : Tower.Tm n :=
  subst (consSub implementation Fin.elim0)
    (RussellTarski.substLevelsTm (fun _ => level) subject)

/-- The checked template exposes the six data binders while weakening its
operation implementation through those binders. -/
def liftOperation {n : Nat} (operation : Tower.Tm n) : Tower.Tm (n + 6) :=
  rename wk (rename wk (rename wk (rename wk (rename wk (rename wk operation)))))

theorem instantiate_lams {n : Nat} (level : LevelExpr Nat) (operation : Tower.Tm n) :
    instantiate level operation =
      .lam (.lam (.lam (.lam (.lam (.lam (bodyAt (liftOperation operation))))))) := rfl

theorem instantiate_typed (signature : Declaration.Signature Tower.Head)
    {n : Nat} {ambient : Tower.Ctx n} (level : LevelExpr Nat) (implementation : Tower.Tm n)
    (checked : TypedEquality.Typed (Declaration.extendRules Tower.rules signature) ambient implementation
      (liftClosed (RussellTarski.substLevelsTm (fun _ => level) NativeIdentityCongruence.type))) :
    TypedEquality.Typed (Declaration.extendRules Tower.rules signature) ambient
      (instantiate level implementation)
      (liftClosed (RussellTarski.substLevelsTm (fun _ => level) type)) := by
  have parameter : TypedEquality.SubstMor (Declaration.extendRules Tower.rules signature)
      (RussellTarski.substLevelsCtx (fun _ => level) context) ambient
      (consSub implementation Fin.elim0) := by
    intro index
    fin_cases index
    exact checked
  have lifted := (typed.mapHead (RussellTarski.levelSubstMorphism (fun _ => level))).of_morphism
    (Declaration.includeMorphism Tower.rules signature)
  exact lifted.substitute parameter

#print axioms typed
#print axioms instantiate_typed
#print axioms shortcut_refused

end Pair

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeIdentityCongruence
