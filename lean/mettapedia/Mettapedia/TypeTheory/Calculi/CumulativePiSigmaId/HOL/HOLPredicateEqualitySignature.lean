import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLGenericProofFamily

/-!
# Predicate equality over an arbitrary declared HOL signature

The same declared carriers, constants, implication and quantifiers support a
second logical reading whose equality is the usual unary predicate formula.
The equality operation is an actual native lambda term. Its applications
reduce to that formula by two beta steps, with no added equation or declaration.
The original signature and its primitive equality operation remain available.

This construction supplies a signature, rather than proof capabilities for
every HOL rule. Proof decoding and the extensional principles have their own
typing and semantic obligations.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLPredicateEqualitySignature

open Presentation Presentation.FormationSensitive FormationSensitiveHOLInterface
open FormationSensitiveHOLGenericProofFamily (rawImp universalProposition)
open Mettapedia.Logic

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

def raw (source : LogicalSignature Base Const) {n : Nat}
    (type : HOL.Ty Base) (left right : Tower.Tm n) : Tower.Tm n :=
  universalProposition source (.arr type .prop)
    (.lam (rawImp source (.app (.var 0) (rename wk left))
      (.app (.var 0) (rename wk right))))

@[simp] theorem raw_rename (source : LogicalSignature Base Const) {n m : Nat}
    (rho : Ren n m) (type : HOL.Ty Base) (left right : Tower.Tm n) :
    rename rho (raw source type left right) =
      raw source type (rename rho left) (rename rho right) := by
  simp [raw, universalProposition, rawImp, rename, rename_comp, liftRen, wk]

@[simp] theorem raw_subst (source : LogicalSignature Base Const) {n m : Nat}
    (sigma : Sub Tower.Head n m) (type : HOL.Ty Base) (left right : Tower.Tm n) :
    subst sigma (raw source type left right) =
      raw source type (subst sigma left) (subst sigma right) := by
  simp [raw, universalProposition, rawImp, subst, subst_rename,
    rename_subst, liftSub, wk]

def sourceEquality (type : HOL.Ty Base) : HOL.Term Const [] (.arr type (.arr type .prop)) :=
  .lam (.lam (.all (.imp
    (.app (.var .vz) (.var (.vs (.vs .vz))))
    (.app (.var .vz) (.var (.vs .vz))))))

def equality (source : LogicalSignature Base Const) (type : HOL.Ty Base) : Tower.Tm 0 :=
  .lam (.lam (raw source type (.var (Fin.succ 0)) (.var 0)))

theorem sourceEquality_represented (source : LogicalSignature Base Const)
    (type : HOL.Ty Base) :
    represent source (sourceEquality (Const := Const) type) = some (equality source type) := rfl

theorem equality_typed (source : LogicalSignature Base Const) (type : HOL.Ty Base) :
    Typing source.rules .nil (equality source type)
      (typeAt source.types 0 (.arr type (.arr type .prop))) :=
  represent_typed source (sourceEquality type) (sourceEquality_represented source type)

def signature (source : LogicalSignature Base Const) : LogicalSignature Base Const :=
  { source with equality := equality source, equality_typed := equality_typed source }

@[simp] theorem signature_rules (source : LogicalSignature Base Const) :
    (signature source).rules = source.rules := rfl

@[simp] theorem signature_types (source : LogicalSignature Base Const) :
    (signature source).types = source.types := rfl

theorem lifted_equality (source : LogicalSignature Base Const) {n : Nat}
    (type : HOL.Ty Base) :
    (liftClosed (equality source type) : Tower.Tm n) =
      .lam (.lam (raw source type (.var (Fin.succ 0)) (.var 0))) := by
  simp only [equality, liftClosed, rename, raw_rename]
  rfl

theorem application_conversion (source : LogicalSignature Base Const) {n : Nat}
    (type : HOL.Ty Base) (left right : Tower.Tm n) :
    Conv source.rules.headEq
      (.app (.app (liftClosed (equality source type)) left) right)
      (raw source type left right) source.rules.computation := by
  rw [lifted_equality]
  have first : Conv source.rules.headEq
      (.app (.lam (.lam (raw source type (.var (Fin.succ 0)) (.var 0)))) left)
      (.lam (raw source type (rename wk left) (.var 0))) source.rules.computation := by
    simpa only [inst0, subst, raw_subst, liftSub, subst0,
      Fin.cases_succ, Fin.cases_zero] using
      (Relation.EqvGen.rel _ _ (Step.betaPi (root := source.rules.computation)
        (headEq := source.rules.headEq)
        (.lam (raw source type (.var (Fin.succ 0)) (.var 0))) left))
  have second : Conv source.rules.headEq
      (.app (.lam (raw source type (rename wk left) (.var 0))) right)
      (raw source type left right) source.rules.computation := by
    have weakened : subst (subst0 right) (rename wk left) = left := inst0_rename_wk right left
    simpa only [inst0, raw_subst, subst, subst0, Fin.cases_zero, weakened] using
      (Relation.EqvGen.rel _ _ (Step.betaPi (root := source.rules.computation)
        (headEq := source.rules.headEq) (raw source type (rename wk left) (.var 0)) right))
  exact .trans _ _ _ (Conv.congApp first (.refl _)) second

#print axioms equality_typed
#print axioms application_conversion
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLPredicateEqualitySignature
