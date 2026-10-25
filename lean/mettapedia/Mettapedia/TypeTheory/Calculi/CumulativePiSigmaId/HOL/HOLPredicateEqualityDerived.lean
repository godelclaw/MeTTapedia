import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLPredicateEqualityRules

/-!
# Constructive native operations for predicate equality

Symmetry, composition, application congruence and proposition transport are
native lambda terms over the parameterized proof decoder. Their formation and
computation laws hold for every declared HOL signature with a fresh proof family.
No extensionality declaration or native identity equation is introduced.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLPredicateEqualityDerived
open Presentation Presentation.FormationSensitive FormationSensitiveHOLInterface
open FormationSensitiveHOLGenericProofFamily (proof rawImp)
open HOLPredicateEqualitySignature (raw)
open HOLPredicateEqualityRules
open Mettapedia.Logic
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
variable (source : LogicalSignature Base Const) (proofName : DeclName)

def reflTerm {n : Nat} : Tower.Tm n := .lam (.lam (.var 0))

def symmetry {n : Nat} (type : HOL.Ty Base) (x h : Tower.Tm n) : Tower.Tm n :=
  .app (.app h (.lam (raw source type (.var 0) (rename wk x)))) reflTerm

def transitivity {n : Nat} (type : HOL.Ty Base) (x h k : Tower.Tm n) : Tower.Tm n :=
  .app (.app k (.lam (raw source type (rename wk x) (.var 0)))) h

def congruence {n : Nat} (result : HOL.Ty Base) (f x h : Tower.Tm n) : Tower.Tm n :=
  .app (.app h (.lam (raw source result (rename wk (.app f x))
    (.app (rename wk f) (.var 0))))) reflTerm

def functionCongruence {n : Nat} (result : HOL.Ty Base) (f x h : Tower.Tm n) : Tower.Tm n :=
  .app (.app h (.lam (raw source result (rename wk (.app f x))
    (.app (.var 0) (rename wk x))))) reflTerm

def propForward {n : Nat} (h : Tower.Tm n) : Tower.Tm n := .app h (.lam (.var 0))

@[simp] theorem reflTerm_subst {n m : Nat} (sigma : Sub Tower.Head n m) :
    subst sigma reflTerm = reflTerm := rfl

@[simp] theorem symmetry_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    (type : HOL.Ty Base) (x h : Tower.Tm n) :
    subst sigma (symmetry source type x h) = symmetry source type (subst sigma x) (subst sigma h) := by
  simp [symmetry, subst, HOLPredicateEqualitySignature.raw_subst, liftSub, reflTerm]

@[simp] theorem transitivity_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    (type : HOL.Ty Base) (x h k : Tower.Tm n) :
    subst sigma (transitivity source type x h k) =
      transitivity source type (subst sigma x) (subst sigma h) (subst sigma k) := by
  simp [transitivity, subst, HOLPredicateEqualitySignature.raw_subst, liftSub]

@[simp] theorem congruence_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    (type : HOL.Ty Base) (f x h : Tower.Tm n) :
    subst sigma (congruence source type f x h) =
      congruence source type (subst sigma f) (subst sigma x) (subst sigma h) := by
  simp [congruence, subst, HOLPredicateEqualitySignature.raw_subst, liftSub, reflTerm]

@[simp] theorem functionCongruence_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    (type : HOL.Ty Base) (f x h : Tower.Tm n) :
    subst sigma (functionCongruence source type f x h) =
      functionCongruence source type (subst sigma f) (subst sigma x) (subst sigma h) := by
  simp [functionCongruence, subst, HOLPredicateEqualitySignature.raw_subst, liftSub, reflTerm]

@[simp] theorem propForward_subst {n m : Nat} (sigma : Sub Tower.Head n m)
    (h : Tower.Tm n) : subst sigma (propForward h) = propForward (subst sigma h) := rfl

@[simp] theorem subst0_weaken {n : Nat} (argument term : Tower.Tm n) :
    subst (subst0 argument) (rename wk term) = term := inst0_rename_wk argument term

theorem variable_zero {n : Nat} (context : Tower.Ctx n) (type : HOL.Ty Base) :
    Typing (rules source proofName) (.snoc context (typeAt source.types n type)) (.var 0)
      (typeAt source.types (n + 1) type) := by
  simpa only [Ctx.lookup_snoc_zero, typeAt_rename] using
    (Typing.var (R := (rules source proofName)) (Γ := .snoc context (typeAt source.types n type)) 0)

theorem weaken_typed {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base}
    {term : Tower.Tm n} (typed : Typing (rules source proofName) context term (typeAt source.types n type))
    (extension : Tower.Tm n) :
    Typing (rules source proofName) (.snoc context extension) (rename wk term) (typeAt source.types (n + 1) type) := by
  simpa only [typeAt_rename] using typed.weaken (extension := extension)

theorem predicate_lambda {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base}
    {body : Tower.Tm (n + 1)}
    (typed : Typing (rules source proofName) (.snoc context (typeAt source.types n type)) body (typeAt source.types _ .prop)) :
    Typing (rules source proofName) context (.lam body) (typeAt source.types n (.arr type .prop)) :=
  .lamIntro (FormationSensitiveHOLGenericProofFamily.pi_zero (HOLPredicateEqualitySignature.signature source) proofName
    (FormationSensitiveHOLGenericProofFamily.include_typed (HOLPredicateEqualitySignature.signature source) proofName (typeAt_formed (HOLPredicateEqualitySignature.signature source) type context))
    (FormationSensitiveHOLGenericProofFamily.include_typed (HOLPredicateEqualitySignature.signature source) proofName (typeAt_formed (HOLPredicateEqualitySignature.signature source) .prop _))) (.sort Tower.zero) typed

theorem beta_conversion {n : Nat} (body : Tower.Tm (n + 1)) (argument : Tower.Tm n) :
    Conv (rules source proofName).headEq (.app (.lam body) argument) (inst0 argument body) (rules source proofName).computation :=
  .rel _ _ (.betaPi body argument)

/-- The supplied equality chooses an actual lambda predicate. Its beta
computations are checked at both the input and output proof families. -/
theorem eliminate_lambda (fresh : source.rules.constantType proofName = none)
    {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base}
    {x y h input : Tower.Tm n} {body : Tower.Tm (n + 1)}
    (hx : Typing (rules source proofName) context x (typeAt source.types n type))
    (hy : Typing (rules source proofName) context y (typeAt source.types n type))
    (comparison : Typing (rules source proofName) context h (proof proofName (raw source type x y)))
    (bodyTyped : Typing (rules source proofName) (.snoc context (typeAt source.types n type)) body (typeAt source.types _ .prop))
    (inputTyped : Typing (rules source proofName) context input (proof proofName (inst0 x body))) :
    Typing (rules source proofName) context (.app (.app h (.lam body)) input) (proof proofName (inst0 y body)) := by
  have predicate := predicate_lambda source proofName bodyTyped
  have adjusted := Typing.conv inputTyped
    (FormationSensitiveHOLGenericProofFamily.proof_formed (HOLPredicateEqualitySignature.signature source) proofName fresh (application_typed source proofName predicate hx))
    (.sort Tower.zero) (Conv.congApp (.refl _) (.symm _ _ (beta_conversion source proofName body x)))
  have application := elimination source proofName fresh hx hy comparison predicate adjusted
  have target : Typing (rules source proofName) context (inst0 y body)
      (typeAt source.types n .prop) := by
    simpa only [inst0, typeAt_subst] using bodyTyped.instantiate hy
  exact .conv application (FormationSensitiveHOLGenericProofFamily.proof_formed (HOLPredicateEqualitySignature.signature source) proofName fresh target)
    (.sort Tower.zero) (Conv.congApp (.refl _) (beta_conversion source proofName body y))

theorem symmetry_typed (fresh : source.rules.constantType proofName = none)
    {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base}
    {x y h : Tower.Tm n}
    (hx : Typing (rules source proofName) context x (typeAt source.types n type))
    (hy : Typing (rules source proofName) context y (typeAt source.types n type))
    (comparison : Typing (rules source proofName) context h (proof proofName (raw source type x y))) :
    Typing (rules source proofName) context (symmetry source type x h) (proof proofName (raw source type y x)) := by
  have body := raw_typed source proofName (variable_zero source proofName context type)
    (weaken_typed source proofName hx (typeAt source.types n type))
  have initial := reflexivity source proofName fresh hx
  have result := eliminate_lambda source proofName fresh hx hy comparison body
    (input := reflTerm) (by simpa [inst0, HOLPredicateEqualitySignature.raw_subst, reflTerm] using initial)
  simpa only [symmetry, inst0, HOLPredicateEqualitySignature.raw_subst,
    subst, subst0_weaken, subst0, Fin.cases_zero] using result

theorem transitivity_typed (fresh : source.rules.constantType proofName = none)
    {n : Nat} {context : Tower.Ctx n} {type : HOL.Ty Base}
    {x y z h k : Tower.Tm n}
    (hx : Typing (rules source proofName) context x (typeAt source.types n type))
    (hy : Typing (rules source proofName) context y (typeAt source.types n type))
    (hz : Typing (rules source proofName) context z (typeAt source.types n type))
    (first : Typing (rules source proofName) context h (proof proofName (raw source type x y)))
    (second : Typing (rules source proofName) context k (proof proofName (raw source type y z))) :
    Typing (rules source proofName) context (transitivity source type x h k) (proof proofName (raw source type x z)) := by
  have body := raw_typed source proofName (weaken_typed source proofName hx (typeAt source.types n type))
    (variable_zero source proofName context type)
  have result := eliminate_lambda source proofName fresh hy hz second body
    (input := h) (by simpa [inst0, HOLPredicateEqualitySignature.raw_subst] using first)
  simpa only [transitivity, inst0, HOLPredicateEqualitySignature.raw_subst,
    subst, subst0_weaken, subst0, Fin.cases_zero] using result

theorem congruence_typed (fresh : source.rules.constantType proofName = none)
    {n : Nat} {context : Tower.Ctx n} {a b : HOL.Ty Base}
    {f x y h : Tower.Tm n}
    (hf : Typing (rules source proofName) context f (typeAt source.types n (.arr a b)))
    (hx : Typing (rules source proofName) context x (typeAt source.types n a))
    (hy : Typing (rules source proofName) context y (typeAt source.types n a))
    (comparison : Typing (rules source proofName) context h (proof proofName (raw source a x y))) :
    Typing (rules source proofName) context (congruence source b f x h) (proof proofName (raw source b (.app f x) (.app f y))) := by
  have application := application_typed source proofName hf hx
  have body := raw_typed source proofName (weaken_typed source proofName application (typeAt source.types n a))
    (application_typed source proofName (weaken_typed source proofName hf (typeAt source.types n a)) (variable_zero source proofName context a))
  have result := eliminate_lambda source proofName fresh hx hy comparison body (input := reflTerm)
    (by simpa [inst0, HOLPredicateEqualitySignature.raw_subst, reflTerm, subst, subst0] using reflexivity source proofName fresh application)
  simpa only [congruence, inst0, HOLPredicateEqualitySignature.raw_subst, subst, subst0_weaken,
    subst0, Fin.cases_zero] using result

theorem functionCongruence_typed (fresh : source.rules.constantType proofName = none)
    {n : Nat} {context : Tower.Ctx n} {a b : HOL.Ty Base}
    {f g x h : Tower.Tm n}
    (hf : Typing (rules source proofName) context f (typeAt source.types n (.arr a b)))
    (hg : Typing (rules source proofName) context g (typeAt source.types n (.arr a b)))
    (hx : Typing (rules source proofName) context x (typeAt source.types n a))
    (comparison : Typing (rules source proofName) context h (proof proofName (raw source (.arr a b) f g))) :
    Typing (rules source proofName) context (functionCongruence source b f x h)
      (proof proofName (raw source b (.app f x) (.app g x))) := by
  have application := application_typed source proofName hf hx
  have body := raw_typed source proofName (weaken_typed source proofName application (typeAt source.types n (.arr a b)))
    (application_typed source proofName (variable_zero source proofName context (.arr a b))
      (weaken_typed source proofName hx (typeAt source.types n (.arr a b))))
  have result := eliminate_lambda source proofName fresh hf hg comparison body (input := reflTerm)
    (by simpa [inst0, HOLPredicateEqualitySignature.raw_subst, reflTerm, subst, subst0] using reflexivity source proofName fresh application)
  simpa only [functionCongruence, inst0, HOLPredicateEqualitySignature.raw_subst, subst, subst0_weaken,
    subst0, Fin.cases_zero] using result

theorem propForward_typed (fresh : source.rules.constantType proofName = none)
    {n : Nat} {context : Tower.Ctx n} {p q h : Tower.Tm n}
    (hp : Typing (rules source proofName) context p (typeAt source.types _ .prop))
    (hq : Typing (rules source proofName) context q (typeAt source.types _ .prop))
    (comparison : Typing (rules source proofName) context h (proof proofName (raw source .prop p q))) :
    Typing (rules source proofName) context (propForward h) (proof proofName (rawImp source p q)) := by
  have predicate := predicate_lambda source proofName (variable_zero source proofName context .prop)
  have result := specialize source proofName fresh hp hq comparison predicate
  have beta (term : Tower.Tm n) : Conv (rules source proofName).headEq (.app (.lam (.var 0)) term) term
      (rules source proofName).computation := by
    simpa only [inst0, subst, subst0, Fin.cases_zero] using beta_conversion source proofName (.var 0) term
  have implication : Conv (rules source proofName).headEq
      (rawImp source (.app (.lam (.var 0)) p) (.app (.lam (.var 0)) q)) (rawImp source p q)
      (rules source proofName).computation := Conv.congApp (Conv.congApp (.refl _) (beta p)) (beta q)
  exact .conv result
    (FormationSensitiveHOLGenericProofFamily.proof_formed (HOLPredicateEqualitySignature.signature source) proofName fresh
      (FormationSensitiveHOLGenericProofFamily.implication_proposition (HOLPredicateEqualitySignature.signature source) proofName hp hq))
    (.sort Tower.zero) (Conv.congApp (.refl _) implication)

theorem propBackward_typed (fresh : source.rules.constantType proofName = none)
    {n : Nat} {context : Tower.Ctx n} {p q h : Tower.Tm n}
    (hp : Typing (rules source proofName) context p (typeAt source.types _ .prop))
    (hq : Typing (rules source proofName) context q (typeAt source.types _ .prop))
    (comparison : Typing (rules source proofName) context h (proof proofName (raw source .prop p q))) :
    Typing (rules source proofName) context (propForward (symmetry source .prop p h)) (proof proofName (rawImp source q p)) :=
  propForward_typed source proofName fresh hq hp (symmetry_typed source proofName fresh hp hq comparison)

#print axioms symmetry_typed
#print axioms transitivity_typed
#print axioms congruence_typed
#print axioms functionCongruence_typed
#print axioms propForward_typed
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLPredicateEqualityDerived
