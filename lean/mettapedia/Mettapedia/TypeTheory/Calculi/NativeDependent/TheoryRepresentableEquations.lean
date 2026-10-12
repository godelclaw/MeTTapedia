import Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryEquationContextualSemanticSubstitution
import Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryEquationNativeAdmission
import Mettapedia.TypeTheory.Calculi.NativeDependent.RepresentableIndexedForgetSubstitution

/-!
# Original category equations in the complete native judgment presentation

Identity, composition and the projection of an original-arrow fibre are
independent raw equation declarations. They extend the complete native
mixed-context rules. Their two formation premises are actual old derivations;
their model admission is earned separately from complete Yoneda readouts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryRepresentables

open _root_.CategoryTheory
open RepresentableIndexedDeclarations
open TheoryEquations

universe u
variable {C : Type u} [Category.{u} C]

inductive Origin (C : Type u) [Category.{u} C] where
  | identity (object : C)
  | composition {source middle target : C} (earlier : source ⟶ middle) (later : middle ⟶ target)
  | fibreProjection (index : ArrowSymbol C)

def compositionDeclaration {source middle target : C}
    (earlier : source ⟶ middle) (later : middle ⟶ target) : Declaration (symbols C) :=
  .substitution (objectContext source) (objectContext target)
    (originalSubstitution (earlier ≫ later))
    (composeSubstitution (originalSubstitution later) (originalSubstitution earlier))

def declaration : Origin C → Declaration (symbols C)
  | .identity object => .substitution (objectContext object) (objectContext object)
      (originalSubstitution (𝟙 object)) TermExpr.var
  | .composition earlier later => compositionDeclaration earlier later
  | .fibreProjection index => .substitution (fibreContext index) (objectContext index.target)
      (composeSubstitution (originalSubstitution index.arrow) (forgetSubstitution index))
      (fun position => .var position.succ)

def equations (C : Type u) [Category.{u} C] : Presentation (symbols C) where
  Origin := Origin C
  declaration := declaration

def theory (C : Type u) [Category.{u} C] : Theory (symbols C) where
  toSignature := signature C
  equations := equations C

def firstPremise (origin : Origin C) :
    Refinement.Derivation (signature C) ((declaration origin).premises.get ⟨0, by cases origin <;> simp [declaration, compositionDeclaration, Declaration.premises]⟩) := by
  cases origin with
  | identity object => exact originalSubstitutionFormed (𝟙 object)
  | composition earlier later => exact originalSubstitutionFormed (earlier ≫ later)
  | fibreProjection index =>
      exact deriveList (.substitutionCompose (fibreContext index) (objectContext index.source)
        (objectContext index.target) (forgetSubstitution index) (originalSubstitution index.arrow))
        (.cons (forgetSubstitutionFormed index) (.cons (originalSubstitutionFormed index.arrow) .nil))

def secondPremise (origin : Origin C) :
    Refinement.Derivation (signature C) ((declaration origin).premises.get ⟨1, by cases origin <;> simp [declaration, compositionDeclaration, Declaration.premises]⟩) := by
  cases origin with
  | identity object =>
      exact deriveList (.substitutionIdentity (objectContext object)) (.cons (objectContextFormed object) .nil)
  | @composition source middle target earlier later =>
      exact deriveList (.substitutionCompose (objectContext source) (objectContext middle) (objectContext target)
        (originalSubstitution earlier) (originalSubstitution later))
        (.cons (originalSubstitutionFormed earlier) (.cons (originalSubstitutionFormed later) .nil))
  | fibreProjection index =>
      exact deriveList (.substitutionWeaken (objectContext index.target) (fibreType index (.var 0)))
        (.cons (genericFibreFormed index) .nil)

def equationTree (origin : Origin C) :
    TheoryEquations.Derivation (signature C) (equations C) (declaration origin).conclusion :=
  TheoryEquations.declare (D := signature C) (equations := equations C) origin (fun position => by
    have bound : position.val < 2 := by
      simpa only [equations, Declaration.premises_length] using position.isLt
    by_cases zero : position.val = 0
    · have same : position = ⟨0, by simpa only [equations, Declaration.premises_length] using Nat.zero_lt_succ 1⟩ := Fin.ext zero
      cases same
      exact TheoryEquations.original (firstPremise origin)
    · have one : position.val = 1 := by omega
      have same : position = ⟨1, by simpa only [equations, Declaration.premises_length] using Nat.lt_succ_self 1⟩ := Fin.ext one
      cases same
      exact TheoryEquations.original (secondPremise origin))

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryRepresentables
