import Mettapedia.GSLT.Dedukti.LeanMinusConversion

/-!
# A Lean⁻ term typed in the Dedukti theory of Blanqui and Vaishnav

The Lean⁻ term `fun (A : Prop) (a : A) => a` of type `∀ A : Prop, A → A`,
translated by Definition 1 of the paper with the sorting function that
assigns `Prop` the level `1`, `A` the level `0`, and `∀ A : Prop, A → A` the
level `0`:

* `‖Prop‖ = ε (succ zero) (u zero)` (`propType`);
* the term: `λ A : ‖Prop‖. λ a : ε zero A. a` (`identityTerm`);
* its type: `ε zero (π (succ zero) zero (u zero) (λ A : ‖Prop‖. π zero zero A (λ a : ε zero A. A)))`
  (`identityType`).

`identity_typed`: the term has that type in `pureTheory`, the theory without
universe polymorphism.  The derivation uses the rules `ε _ (u α) ↪ U α` and
`ε _ (π α β t t') ↪ Π x : ε α t. ε β (t' x)`, beta, and the level equations
`imax |0| |0| ≡ |0|` and `imax |1| |0| ≡ |0|` (`imax_zero_zero`,
`imax_one_zero`), which go through the rules for `zero`, `succ`, `Incr`, `Add`
and the first rule for `imax`.  `identity_typed_lean`: the same in the
paper's theory.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.LeanMinus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 Ctx ctxLookup)
open Mettapedia.GSLT.LanguageDef.LFProfile (ProductRule)

/-! ## The terms -/

/-- `‖Prop‖ = ε |1| |Prop| = ε (succ zero) (u zero)`. -/
def propType : Term := eps (succ zero) (ap "u" [zero])

/-- `λ a : ε zero A. a`, beneath the binder of `A`. -/
def innerIdentity : Term := .lam (eps zero (.var 0)) (.var 0)

/-- `|fun (A : Prop) (a : A) => a|`. -/
def identityTerm : Term := .lam propType innerIdentity

/-- `λ a : ε zero A. A`, beneath the binder of `A`: the family of `A → A`. -/
def arrowFamily : Term := .lam (eps zero (.var 0)) (.var 1)

/-- `λ A : ‖Prop‖. |A → A|`: the family of `∀ A : Prop, A → A`. -/
def identityFamily : Term := .lam propType (ap "pi" [zero, zero, .var 0, arrowFamily])

/-- `|∀ A : Prop, A → A|`. -/
def identityCode : Term := ap "pi" [succ zero, zero, ap "u" [zero], identityFamily]

/-- `‖∀ A : Prop, A → A‖`. -/
def identityType : Term := eps zero identityCode

/-! ## Levels -/

theorem zero_typed (context : Ctx) : LambdaPiModulo pureTheory context zero L := .con rfl

theorem succZero_typed (context : Ctx) : LambdaPiModulo pureTheory context (succ zero) L :=
  app_at (.con rfl) (zero_typed context) rfl

theorem conv_zero : Conv pureTheory zero levelZero := zero_reduces.conv

theorem conv_one : Conv pureTheory (succ zero) levelOne := one_reduces.conv

/-- `imax (Max _) (Max (nil _)) ↪ Max nil_S`, at `Max E`. -/
theorem conv_imax_max_nil (first : Term) :
    Conv pureTheory (imax (ap "Max" [first]) levelZero) levelZero :=
  conv_of_instance (rule := rulesI[3]) (pureRule_mem (by decide)) (assign [first, .con "S_code"])
    (by simp [rulesI, mkRule, closePattern, placeholderIndex, nv, assign, ap, apT, imax, levelZero])
    (by simp [rulesI, mkRule, closePattern, placeholderIndex, nv, ap, apT, levelZero])

/-- **`imax |0| |0| ≡ |0|`.** -/
theorem imax_zero_zero : Conv pureTheory (imax zero zero) zero :=
  .trans _ _ _ (Conv.app (Conv.app (.refl _) conv_zero) conv_zero)
    (.trans _ _ _ (conv_imax_max_nil _) (.symm _ _ conv_zero))

/-- **`imax |1| |0| ≡ |0|`.** -/
theorem imax_one_zero : Conv pureTheory (imax (succ zero) zero) zero :=
  .trans _ _ _ (Conv.app (Conv.app (.refl _) conv_one) conv_zero)
    (.trans _ _ _ (conv_imax_max_nil _) (.symm _ _ conv_zero))

/-! ## Codes of propositions -/

theorem uZero_formed (context : Ctx) : LambdaPiModulo pureTheory context (U zero) (.srt .type) :=
  app_at (.con rfl) (zero_typed context) rfl

theorem propType_formed (context : Ctx) :
    LambdaPiModulo pureTheory context propType (.srt .type) :=
  app_at (app_at (.con rfl) (succZero_typed context) rfl)
    (app_at (.con rfl) (zero_typed context) rfl) rfl

/-- `‖Prop‖ ≡ U zero`, by `ε _ (u α) ↪ U α`. -/
theorem conv_propType : Conv pureTheory propType (U zero) :=
  conv_of_instance (rule := rulesP[0]) (pureRule_mem (by decide)) (assign [succ zero, zero])
    (by decide) (by decide)

/-- A variable of type `‖Prop‖` is the code of a proposition. -/
theorem propVariable {context : Ctx} {index : Nat} (found : ctxLookup context index = some propType) :
    LambdaPiModulo pureTheory context (.var index) (U zero) :=
  .conv (.var found) conv_propType (uZero_formed context)

theorem epsZero_formed {context : Ctx} {code : Term}
    (typed : LambdaPiModulo pureTheory context code (U zero)) :
    LambdaPiModulo pureTheory context (eps zero code) (.srt .type) :=
  app_at (app_at (.con rfl) (zero_typed context) rfl) typed rfl

/-! ## The term has the translated type -/

/-- `λ a : ε zero A. a : Π a : ε zero A. ε zero A`, beneath `A : ‖Prop‖`. -/
theorem innerIdentity_typed :
    LambdaPiModulo pureTheory [propType] innerIdentity (.pi (eps zero (.var 0)) (eps zero (.var 1))) :=
  .lam (epsZero_formed (propVariable rfl)) (epsZero_formed (propVariable rfl)) arrow_rule (.var rfl)

/-- `identityTerm : Π A : ‖Prop‖. Π a : ε zero A. ε zero A`. -/
theorem identityTerm_typed_raw :
    LambdaPiModulo pureTheory [] identityTerm
      (.pi propType (.pi (eps zero (.var 0)) (eps zero (.var 1)))) :=
  .lam (propType_formed []) (.pi (epsZero_formed (propVariable rfl)) (epsZero_formed (propVariable rfl))
    arrow_rule) arrow_rule innerIdentity_typed

/-- A beta contraction whose result is computed. -/
theorem conv_beta_at {theory : Theory} {domain body argument result : Term}
    (same : subst0 argument body = result) :
    Conv theory (.app (.lam domain body) argument) result :=
  same ▸ Conv.beta domain body argument

/-- `ε _ (π α β t t') ↪ Π x : ε α t. ε β (t' x)`, at given arguments. -/
theorem conv_eps_pi (level first second code family : Term) :
    Conv pureTheory (eps level (ap "pi" [first, second, code, family]))
      (.pi (eps first code) (eps (lift 1 0 second) (.app (lift 1 0 family) (.var 0)))) :=
  conv_of_instance (rule := rulesP[1]) (pureRule_mem (by decide))
    (assign [level, first, second, code, family])
    (by simp [rulesP, mkRule, closePattern, placeholderIndex, nv, assign, ap, apT, eps, piN, close])
    (by simp [rulesP, mkRule, closePattern, placeholderIndex, nv, assign, ap, apT, eps, piN, close,
      instantiate, lift_zero])

/-- **The translated type computes to the type of the term.** -/
theorem conv_identityType :
    Conv pureTheory identityType (.pi propType (.pi (eps zero (.var 0)) (eps zero (.var 1)))) := by
  have outer := conv_eps_pi zero (succ zero) zero (ap "u" [zero]) identityFamily
  have family : Conv pureTheory (.app (lift 1 0 identityFamily) (.var 0))
      (ap "pi" [zero, zero, .var 0, arrowFamily]) := conv_beta_at (by decide)
  have inner := conv_eps_pi zero zero zero (.var 0) arrowFamily
  have last : Conv pureTheory (.app (lift 1 0 arrowFamily) (.var 0)) (.var 1) :=
    conv_beta_at (by decide)
  refine .trans _ _ _ outer ?_
  refine Conv.pi (.refl _) ?_
  refine .trans _ _ _ (Conv.app (.refl _) family) ?_
  refine .trans _ _ _ inner ?_
  exact Conv.pi (.refl _) (Conv.app (.refl _) last)

/-- The family of `A → A` has its declared type, beneath `A : ‖Prop‖`. -/
theorem arrowFamily_typed :
    LambdaPiModulo pureTheory [propType] arrowFamily (.pi (eps zero (.var 0)) (U zero)) :=
  .lam (epsZero_formed (propVariable rfl)) (uZero_formed _) arrow_rule (propVariable rfl)

/-- The family of `∀ A : Prop, A → A`. -/
theorem identityFamily_typed :
    LambdaPiModulo pureTheory [] identityFamily (.pi propType (U zero)) := by
  have code : LambdaPiModulo pureTheory [propType] (ap "pi" [zero, zero, .var 0, arrowFamily])
      (U (imax zero zero)) :=
    app_at (app_at (app_at (app_at (.con rfl) (zero_typed _) rfl) (zero_typed _) rfl)
      (propVariable rfl) rfl) arrowFamily_typed rfl
  have imaxFormed : LambdaPiModulo pureTheory [propType] (U (imax zero zero)) (.srt .type) :=
    app_at (.con rfl) (app_at (app_at (.con rfl) (zero_typed _) rfl) (zero_typed _) rfl) rfl
  have raw : LambdaPiModulo pureTheory [] identityFamily (.pi propType (U (imax zero zero))) :=
    .lam (propType_formed []) imaxFormed arrow_rule code
  exact .conv raw (Conv.pi (.refl _) (Conv.app (.refl _) imax_zero_zero))
    (.pi (propType_formed []) (uZero_formed _) arrow_rule)

/-- `‖∀ A : Prop, A → A‖` is a type. -/
theorem identityType_formed : LambdaPiModulo pureTheory [] identityType (.srt .type) := by
  have code : LambdaPiModulo pureTheory [] identityCode (U (imax (succ zero) zero)) :=
    app_at (app_at (app_at (app_at (.con rfl) (succZero_typed _) rfl) (zero_typed _) rfl)
      (app_at (.con rfl) (zero_typed _) rfl) rfl) identityFamily_typed rfl
  have codeAtZero : LambdaPiModulo pureTheory [] identityCode (U zero) :=
    .conv code (Conv.app (.refl _) imax_one_zero) (uZero_formed _)
  exact epsZero_formed codeAtZero

/-- **The translation of `fun (A : Prop) (a : A) => a` has the translation of
`∀ A : Prop, A → A`**, in the theory without universe polymorphism. -/
theorem identity_typed : LambdaPiModulo pureTheory [] identityTerm identityType :=
  .conv identityTerm_typed_raw (.symm _ _ conv_identityType) identityType_formed

/-- The same in the paper's theory. -/
theorem identity_typed_lean : LambdaPiModulo leanTheory [] identityTerm identityType :=
  HasType.mono (LFProfile.Subsumed.refl _) pureTheory_extends identity_typed

#print axioms imax_one_zero
#print axioms identity_typed
#print axioms identity_typed_lean

end Mettapedia.GSLT.Dedukti.LeanMinus
