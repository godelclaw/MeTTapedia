import Mettapedia.TypeTheory.Calculi.NativeDependent.TheoryEquationDeclarations

/-!
# Native derivations retaining original rules and theory equations

All 137 original rules can consume premises using the new equation rules.
Every added equation occurrence retains its two independently supplied
formation or typing trees. The extension inclusion acts on whole old trees,
and authored equation origins remain distinguishable even when their
conclusions and semantic readouts agree.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryEquations

universe u

variable {S : Symbols.{u}} {D : Signature S} {equations : Presentation S}

abbrev Derivation (D : Signature S) (equations : Presentation S) (judgment : Judgment S) :=
  JudgmentDerivation.Derivation (equations.extension D).signature judgment

def original {judgment : Judgment S} (tree : Refinement.Derivation D judgment) :
    Derivation D equations judgment := (equations.extension D).original tree

def derive (rule : RuleCode D)
    (premises : (position : Fin rule.premises.length) →
      Derivation D equations (rule.premises.get position)) :
    Derivation D equations rule.conclusion :=
  .node (.inl ⟨rule, rfl⟩) (fun position => premises position.down)

def Premises (D : Signature S) (equations : Presentation S) : List (Judgment S) → Type u
  | [] => PUnit
  | judgment :: remaining => Derivation D equations judgment × Premises D equations remaining

def Premises.get {judgments : List (Judgment S)} (proofs : Premises D equations judgments)
    (position : Fin judgments.length) : Derivation D equations (judgments.get position) := by
  induction judgments with
  | nil => exact Fin.elim0 position
  | cons first remaining ih =>
      cases position using Fin.cases with
      | zero => exact proofs.1
      | succ position => exact ih proofs.2 position

def deriveWith (rule : RuleCode D) (premises : Premises D equations rule.premises) :
    Derivation D equations rule.conclusion := derive rule premises.get

def declare (origin : equations.Origin)
    (premises : (position : Fin (equations.declaration origin).premises.length) →
      Derivation D equations ((equations.declaration origin).premises.get position)) :
    Derivation D equations (equations.declaration origin).conclusion :=
  (equations.extension D).add ⟨origin, rfl⟩ (fun position => premises position.down)

def rootOrigin {judgment : Judgment S} : Derivation D equations judgment → Option equations.Origin
  | .node (.inl _) _ => none
  | .node (.inr rule) _ => some rule.val

@[simp] theorem rootOrigin_derive (rule : RuleCode D)
    (premises : (position : Fin rule.premises.length) →
      Derivation D equations (rule.premises.get position)) :
    rootOrigin (derive rule premises) = none := rfl

@[simp] theorem rootOrigin_declare (origin : equations.Origin)
    (premises : (position : Fin (equations.declaration origin).premises.length) →
      Derivation D equations ((equations.declaration origin).premises.get position)) :
    rootOrigin (declare origin premises) = some origin := rfl

@[simp] theorem rootOrigin_cast {first second : Judgment S} (same : first = second)
    (tree : Derivation D equations first) :
    rootOrigin (cast (congrArg (Derivation D equations) same) tree) = rootOrigin tree := by
  cases same
  rfl

/-- Equal equation content does not identify independently authored trees. -/
theorem distinct_origins {first second : equations.Origin} (different : first ≠ second)
    (same : (equations.declaration first).conclusion = (equations.declaration second).conclusion)
    (firstPremises : (position : Fin (equations.declaration first).premises.length) →
      Derivation D equations ((equations.declaration first).premises.get position))
    (secondPremises : (position : Fin (equations.declaration second).premises.length) →
      Derivation D equations ((equations.declaration second).premises.get position)) :
    HEq (declare first firstPremises) (declare second secondPremises) → False := by
  intro trees
  have transported : cast (congrArg (Derivation D equations) same)
      (declare first firstPremises) = declare second secondPremises :=
    eq_of_heq ((cast_heq _ _).trans trees)
  have origins := (rootOrigin_cast same (declare first firstPremises)).symm.trans
    (congrArg rootOrigin transported)
  exact different (Option.some.inj origins)

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.TheoryEquations
