import Mettapedia.GSLT.Dedukti.LeanMinusExplicit

/-!
# Examples in the theory with explicit level substitution

Kernel-checked in `leanTheoryExplicit`, which is confluent
(`leanTheoryExplicit_confluent`), so that statements about its conversion carry
content.

* **Non-collapse.** `zero` and `succ zero` are not convertible
  (`zero_succ_not_conv_explicit`), nor are the level variable `α` and
  `max 1 α` (`var_maxOneVar_not_conv_explicit`); the paper's `ΣU` relates the
  latter two (`paper_max_one_var_reduces`, in `LeanMinusLevels`).
* **The instantiation example of Section 5.** In the context `A : Prop, x : A`,
  `id (inst [|0|]) A x : ε |0| A` (`section5_typed`), where the declared type
  of `id` is `Π fr : Inst, Π A : U (sub fr α), ε (sub fr α) A → ε (sub fr α) A`,
  `v`-free.  The level is reached by `sub (inst [|0|]) α ⟶* |0|`.
* **The four non-rules**, each refuted by the witness of
  `LeanMinusConversion`: (η-fun), (PI), (η-unit), (β-rec-K).
* **The positive example** of `LeanMinusExamples`: `fun (A : Prop) (a : A) => a`
  has the translation of `∀ A : Prop, A → A` (`identity_typed_explicit`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.LeanMinus

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 Ctx ctxLookup)
open Mettapedia.GSLT.LanguageDef.LFProfile (ProductRule)
open Mettapedia.Logic.Relation (Confluent IsNormal)

/-- Two terms that evaluate to one term are convertible. -/
theorem convExplicit_of_evaluate {fuel fuel' : Nat} {left right common : Term}
    (leftComputed : evaluate explicitSig explicitRules fuel left = common)
    (rightComputed : evaluate explicitSig explicitRules fuel' right = common) :
    Conv leanTheoryExplicit left right :=
  Joinable.conv ⟨common, reducesExplicit_of_evaluate leftComputed,
    reducesExplicit_of_evaluate rightComputed⟩

/-! ## Non-collapse -/

theorem levelZero_normal_explicit : IsNormal (Step leanTheoryExplicit) levelZero :=
  normalExplicit_of_stepOnce (by decide +kernel)

theorem levelOne_normal_explicit : IsNormal (Step leanTheoryExplicit) levelOne :=
  normalExplicit_of_stepOnce (by decide +kernel)

theorem zero_reduces_explicit : Reduces leanTheoryExplicit zero levelZero :=
  reducesExplicit_of_evaluate (fuel := 4) (by decide +kernel)

theorem one_reduces_explicit : Reduces leanTheoryExplicit (succ zero) levelOne :=
  reducesExplicit_of_evaluate (fuel := 60) (by decide +kernel)

/-- **Two distinct closed levels are not convertible**: `|0| ≢ |1|`. -/
theorem zero_succ_not_conv_explicit : ¬ Conv leanTheoryExplicit zero (succ zero) := by
  intro convertible
  exact not_conv_of_normal leanTheoryExplicit_confluent levelZero_normal_explicit
    levelOne_normal_explicit (by decide)
    (.trans _ _ _ (.symm _ _ zero_reduces_explicit.conv)
      (.trans _ _ _ convertible one_reduces_explicit.conv))

/-- The normal form of `|max 1 α|`: `Max {C ∅ 1, V {α} α 0}`. -/
def maxOneVarNormal : Term :=
  ap "Max" [ap "cons" [.con "S_code", ap "cst" [ap "nil" [.con "N_code"], oneN],
    singletonSet (ap "var" [guardOf zeroN, zeroN, zeroN])]]

theorem maxOneVar_reduces_explicit :
    Reduces leanTheoryExplicit (code (.max (.succ .zero) (.param 0))) maxOneVarNormal :=
  reducesExplicit_of_evaluate (fuel := 400) (by decide +kernel)

/-- **The level variable and `max 1 α` are not convertible.** -/
theorem var_maxOneVar_not_conv_explicit :
    ¬ Conv leanTheoryExplicit (code (.param 0)) (code (.max (.succ .zero) (.param 0))) := by
  intro convertible
  exact not_conv_of_normal leanTheoryExplicit_confluent
    (normalExplicit_of_stepOnce (by decide +kernel))
    (normalExplicit_of_stepOnce (term := maxOneVarNormal) (by decide +kernel)) (by decide)
    (.trans _ _ _ convertible maxOneVar_reduces_explicit.conv)

/-! ## Typing the levels and the instantiations -/

theorem zero_typed_explicit (context : Ctx) : LambdaPiModulo leanTheoryExplicit context zero L :=
  .con rfl

/-- `|1|` in normal form is a level. -/
theorem levelOne_typed_explicit (context : Ctx) :
    LambdaPiModulo leanTheoryExplicit context levelOne L := by
  have nilN : LambdaPiModulo leanTheoryExplicit context (ap "nil" [.con "N_code"]) G := by
    have applied : LambdaPiModulo leanTheoryExplicit context (ap "nil" [.con "N_code"])
        (tauSet (.con "N_code")) := app_at (.con rfl) (.con rfl) rfl
    have unfold : Conv leanTheoryExplicit G (tauSet (.con "N_code")) :=
      .trans _ _ _ (conv_delta rfl) (Conv.app (.refl _) (conv_delta rfl))
    exact .conv applied (.symm _ _ unfold) (.con rfl)
  have oneTyped : LambdaPiModulo leanTheoryExplicit context oneN N := app_at (.con rfl) (.con rfl) rfl
  have cstTyped : LambdaPiModulo leanTheoryExplicit context
      (ap "cst" [ap "nil" [.con "N_code"], oneN]) S :=
    app_at (app_at (.con rfl) nilN rfl) oneTyped rfl
  have tauS : LambdaPiModulo leanTheoryExplicit context (tau (.con "S_code")) (.srt .type) :=
    app_at (.con rfl) (.con rfl) rfl
  have cstCode : LambdaPiModulo leanTheoryExplicit context (ap "cst" [ap "nil" [.con "N_code"], oneN])
      (tau (.con "S_code")) := .conv cstTyped (conv_delta rfl) tauS
  have consTyped : LambdaPiModulo leanTheoryExplicit context
      (ap "cons" [.con "S_code", ap "cst" [ap "nil" [.con "N_code"], oneN], ap "nil" [.con "S_code"]])
      (tauSet (.con "S_code")) :=
    app_at (app_at (app_at (.con rfl) (.con rfl) rfl) cstCode rfl) (app_at (.con rfl) (.con rfl) rfl) rfl
  have asE : LambdaPiModulo leanTheoryExplicit context
      (ap "cons" [.con "S_code", ap "cst" [ap "nil" [.con "N_code"], oneN], ap "nil" [.con "S_code"]])
      E := .conv consTyped (.symm _ _ (conv_delta rfl)) (.con rfl)
  exact app_at (.con rfl) asE rfl

/-- A list of levels is a list of levels. -/
theorem levelList_typed_explicit (context : Ctx) :
    ∀ levels : List Term, (∀ level ∈ levels, LambdaPiModulo leanTheoryExplicit context level L) →
      LambdaPiModulo leanTheoryExplicit context (levelList levels) LS
  | [], _ => .con rfl
  | level :: rest, typed =>
      app_at (app_at (.con rfl) (typed level (List.mem_cons_self ..)) rfl)
        (levelList_typed_explicit context rest fun other member =>
          typed other (List.mem_cons_of_mem _ member)) rfl

/-- An instantiation by levels is an instantiation. -/
theorem instAt_typed_explicit (context : Ctx) (levels : List Term)
    (typed : ∀ level ∈ levels, LambdaPiModulo leanTheoryExplicit context level L) :
    LambdaPiModulo leanTheoryExplicit context (instAt levels) InstT :=
  app_at (.con rfl) (levelList_typed_explicit context levels typed) rfl

theorem uZero_formed_explicit (context : Ctx) :
    LambdaPiModulo leanTheoryExplicit context (U zero) (.srt .type) :=
  app_at (.con rfl) (zero_typed_explicit context) rfl

theorem epsZero_formed_explicit {context : Ctx} {code : Term}
    (typed : LambdaPiModulo leanTheoryExplicit context code (U zero)) :
    LambdaPiModulo leanTheoryExplicit context (eps zero code) (.srt .type) :=
  app_at (app_at (.con rfl) (zero_typed_explicit context) rfl) typed rfl

/-! ## The instantiation example of Section 5 -/

/-- `sub (inst [|0|]) α ⟶* |0|`: the instantiation computes the level. -/
theorem subZero_reduces : Reduces leanTheoryExplicit (subIn (instAt [zero]) (varCode zeroN)) levelZero :=
  reducesExplicit_of_evaluate (fuel := 100) (by decide +kernel)

theorem subZero_conv : Conv leanTheoryExplicit (subIn (instAt [zero]) (varCode zeroN)) zero :=
  .trans _ _ _ subZero_reduces.conv (.symm _ _ zero_reduces_explicit.conv)

/-- The context `A : Prop, x : A` of the example, translated, innermost first. -/
def section5Context : Ctx := [eps zero (.var 0), U zero]

/-- `|id[0] A x| = id (inst [|0|]) A x`. -/
def section5Term : Term := apT (useTop "id" [.zero]) [.var 1, .var 0]

/-- `‖A‖ = ε |0| A`. -/
def section5Type : Term := eps zero (.var 1)

/-- **The instantiation example of Section 5, typed with `v`-free types**: in
the context `A : Prop, x : A`, `id (inst [|0|]) A x : ε |0| A`. -/
theorem section5_typed : LambdaPiModulo leanTheoryExplicit section5Context section5Term section5Type := by
  have instTyped := instAt_typed_explicit section5Context [zero]
    (fun level member => by
      rw [List.mem_singleton.mp member]
      exact zero_typed_explicit _)
  have declared : LambdaPiModulo leanTheoryExplicit section5Context (useTop "id" [.zero])
      (.pi (U (subIn (instAt [zero]) (varCode zeroN)))
        (.pi (eps (subIn (instAt [zero]) (varCode zeroN)) (.var 0))
          (eps (subIn (instAt [zero]) (varCode zeroN)) (.var 1)))) :=
    app_at (.con rfl) instTyped rfl
  have rule : (⟨.type, .type, .type⟩ : ProductRule) ∈ LFProfile.standardLF.products := by decide
  have codeA : LambdaPiModulo leanTheoryExplicit (U zero :: section5Context) (.var 0) (U zero) :=
    .var rfl
  have target : LambdaPiModulo leanTheoryExplicit section5Context
      (.pi (U zero) (.pi (eps zero (.var 0)) (eps zero (.var 1)))) (.srt .type) :=
    .pi (uZero_formed_explicit _)
      (.pi (epsZero_formed_explicit codeA) (epsZero_formed_explicit (.var rfl)) rule) rule
  have atZero : LambdaPiModulo leanTheoryExplicit section5Context (useTop "id" [.zero])
      (.pi (U zero) (.pi (eps zero (.var 0)) (eps zero (.var 1)))) :=
    .conv declared
      (Conv.pi (Conv.app (.refl _) subZero_conv)
        (Conv.pi (Conv.app (Conv.app (.refl _) subZero_conv) (.refl _))
          (Conv.app (Conv.app (.refl _) subZero_conv) (.refl _))))
      target
  exact app_at (app_at atZero (.var rfl) rfl) (.var rfl) rfl

/-! ## The four non-rules -/

/-- **(η-fun) is not a rule of the theory with explicit substitution.** -/
theorem etaFun_not_joinable_explicit :
    ¬ ∀ (context : Ctx) (function domain codomain : Term),
        LambdaPiModulo leanTheoryExplicit context function (.pi domain codomain) →
          Joinable leanTheoryExplicit function (.lam domain (.app (lift 1 0 function) (.var 0))) :=
  etaFun_not_joinable leanTheoryExplicit_headed (.var rfl)

/-- **(PI) is not a rule of the theory with explicit substitution.** -/
theorem proofIrrelevance_not_joinable_explicit :
    ¬ ∀ (context : Ctx) (code first second : Term),
        LambdaPiModulo leanTheoryExplicit context code (U levelZero) →
        LambdaPiModulo leanTheoryExplicit context first (eps levelZero code) →
        LambdaPiModulo leanTheoryExplicit context second (eps levelZero code) →
          Joinable leanTheoryExplicit first second :=
  proofIrrelevance_not_joinable leanTheoryExplicit_headed (.var rfl) (.var rfl) (.var rfl)

/-- `‖PUnit.{1}‖`, with explicit substitution, the level in normal form. -/
def unitTypeExplicit : Term := eps levelOne (ap "PUnit" [instAt [levelOne]])

/-- `PUnit.unit.{1}`, with explicit substitution, the level in normal form. -/
def unitValueExplicit : Term := ap "PUnit_unit" [instAt [levelOne]]

/-- `sub (inst [|1|]) α ⟶* |1|`. -/
theorem subOne_reduces :
    Reduces leanTheoryExplicit (subIn (instAt [levelOne]) (varCode zeroN)) levelOne :=
  reducesExplicit_of_evaluate (fuel := 200) (by decide +kernel)

/-- `‖PUnit.{1}‖` is a type. -/
theorem unitTypeExplicit_formed (context : Ctx) :
    LambdaPiModulo leanTheoryExplicit context unitTypeExplicit (.srt .type) := by
  have instTyped := instAt_typed_explicit context [levelOne] (fun level member => by
    rw [List.mem_singleton.mp member]
    exact levelOne_typed_explicit _)
  have punit : LambdaPiModulo leanTheoryExplicit context (ap "PUnit" [instAt [levelOne]])
      (U (subIn (instAt [levelOne]) (varCode zeroN))) := app_at (.con rfl) instTyped rfl
  have uFormed : LambdaPiModulo leanTheoryExplicit context (U levelOne) (.srt .type) :=
    app_at (.con rfl) (levelOne_typed_explicit context) rfl
  have punitAt : LambdaPiModulo leanTheoryExplicit context (ap "PUnit" [instAt [levelOne]]) (U levelOne) :=
    .conv punit (Conv.app (.refl _) subOne_reduces.conv) uFormed
  exact app_at (app_at (.con rfl) (levelOne_typed_explicit context) rfl) punitAt rfl

/-- **`PUnit.unit` has the type `‖PUnit‖`**: its declared type at the
instantiation `inst [|1|]` is reached by `sub (inst [|1|]) α ⟶* |1|`. -/
theorem unitValueExplicit_typed (context : Ctx) :
    LambdaPiModulo leanTheoryExplicit context unitValueExplicit unitTypeExplicit := by
  have instTyped := instAt_typed_explicit context [levelOne] (fun level member => by
    rw [List.mem_singleton.mp member]
    exact levelOne_typed_explicit _)
  have declared : LambdaPiModulo leanTheoryExplicit context unitValueExplicit
      (eps (subIn (instAt [levelOne]) (varCode zeroN))
        (ap "PUnit" [instAt [subIn (instAt [levelOne]) (varCode zeroN)]])) :=
    app_at (.con rfl) instTyped rfl
  refine .conv declared ?_ (unitTypeExplicit_formed context)
  exact Conv.app (Conv.app (.refl _) subOne_reduces.conv)
    (Conv.app (.refl _) (Conv.app (.refl _)
      (Conv.app (Conv.app (.refl _) subOne_reduces.conv) (.refl _))))

/-- **(η-unit) is not a rule of the theory with explicit substitution.** -/
theorem unitEta_not_joinable_explicit :
    ¬ ∀ (context : Ctx) (first second : Term),
        LambdaPiModulo leanTheoryExplicit context first unitTypeExplicit →
        LambdaPiModulo leanTheoryExplicit context second unitTypeExplicit →
          Joinable leanTheoryExplicit first second := by
  intro claimed
  exact not_joinable_of_normal (var_normal leanTheoryExplicit_headed 0)
    (normalExplicit_of_stepOnce (term := unitValueExplicit) (by decide +kernel)) (by decide)
    (claimed [unitTypeExplicit] (.var 0) unitValueExplicit (.var rfl) (unitValueExplicit_typed _))

/-- `Eq[1] A x y`, with explicit substitution. -/
def eqOneExplicit (code first second : Term) : Term := ap "Eq" [instAt [levelOne], code, first, second]

/-- `Eq.refl[1] A x`, with explicit substitution. -/
def reflOneExplicit (code element : Term) : Term := ap "Eq_refl" [instAt [levelOne], code, element]

/-- The context `A : Type, a : A, Q : Π b : A, a = b → Prop, h : Q a rfl,
e : a = a`, with explicit substitution, innermost first. -/
def kContextExplicit : Ctx :=
  [eps levelZero (eqOneExplicit (.var 3) (.var 2) (.var 2)),
    eps levelZero (apT (.var 0) [.var 1, reflOneExplicit (.var 2) (.var 1)]),
    .pi (eps levelOne (.var 1)) (.pi (eps levelZero (eqOneExplicit (.var 2) (.var 1) (.var 0)))
      (U levelZero)),
    eps levelOne (.var 0),
    U levelOne]

/-- `Eq.rec.{1, 0} A a Q h a e`, with explicit substitution. -/
def kRedexExplicit : Term :=
  ap "Eq_rec" [instAt [levelOne, levelZero], .var 4, .var 3, .var 2, .var 1, .var 3, .var 0]

/-- **(β-rec-K) is not a rule of the theory with explicit substitution.** -/
theorem kLike_not_joinable_explicit :
    ¬ ∀ (context : Ctx) (code element motive minor proof : Term),
        LambdaPiModulo leanTheoryExplicit context minor
          (eps levelZero (apT motive [element, reflOneExplicit code element])) →
        LambdaPiModulo leanTheoryExplicit context proof
          (eps levelZero (eqOneExplicit code element element)) →
          Joinable leanTheoryExplicit
            (ap "Eq_rec" [instAt [levelOne, levelZero], code, element, motive, minor, element, proof])
            minor := by
  intro claimed
  exact not_joinable_of_normal (normalExplicit_of_stepOnce (term := kRedexExplicit) (by decide +kernel))
    (var_normal leanTheoryExplicit_headed 1) (by decide)
    (claimed kContextExplicit (.var 4) (.var 3) (.var 2) (.var 1) (.var 0) (.var rfl) (.var rfl))

/-! ## The positive example -/

theorem conv_propType_explicit : Conv leanTheoryExplicit propType (U zero) :=
  convExplicit_of_evaluate (fuel := 100) (fuel' := 10) (common := U levelZero)
    (by decide +kernel) (by decide +kernel)

theorem propType_formed_explicit (context : Ctx) :
    LambdaPiModulo leanTheoryExplicit context propType (.srt .type) :=
  app_at (app_at (.con rfl) (app_at (.con rfl) (zero_typed_explicit context) rfl) rfl)
    (app_at (.con rfl) (zero_typed_explicit context) rfl) rfl

theorem propVariable_explicit {context : Ctx} {index : Nat}
    (found : ctxLookup context index = some propType) :
    LambdaPiModulo leanTheoryExplicit context (.var index) (U zero) :=
  .conv (.var found) conv_propType_explicit (uZero_formed_explicit context)

theorem identityTerm_typed_raw_explicit :
    LambdaPiModulo leanTheoryExplicit [] identityTerm
      (.pi propType (.pi (eps zero (.var 0)) (eps zero (.var 1)))) := by
  have rule : (⟨.type, .type, .type⟩ : ProductRule) ∈ LFProfile.standardLF.products := by decide
  have inner : LambdaPiModulo leanTheoryExplicit [propType] innerIdentity
      (.pi (eps zero (.var 0)) (eps zero (.var 1))) :=
    .lam (epsZero_formed_explicit (propVariable_explicit rfl))
      (epsZero_formed_explicit (propVariable_explicit rfl)) rule (.var rfl)
  exact .lam (propType_formed_explicit [])
    (.pi (epsZero_formed_explicit (propVariable_explicit rfl))
      (epsZero_formed_explicit (propVariable_explicit rfl)) rule) rule inner

/-- `imax |0| |0| ≡ |0|` and `imax |1| |0| ≡ |0|`, by evaluation. -/
theorem imax_zero_zero_explicit : Conv leanTheoryExplicit (imax zero zero) zero :=
  convExplicit_of_evaluate (fuel := 40) (fuel' := 4) (common := levelZero)
    (by decide +kernel) (by decide +kernel)

theorem imax_one_zero_explicit : Conv leanTheoryExplicit (imax (succ zero) zero) zero :=
  convExplicit_of_evaluate (fuel := 80) (fuel' := 4) (common := levelZero)
    (by decide +kernel) (by decide +kernel)

theorem identityFamily_typed_explicit :
    LambdaPiModulo leanTheoryExplicit [] identityFamily (.pi propType (U zero)) := by
  have rule : (⟨.type, .type, .type⟩ : ProductRule) ∈ LFProfile.standardLF.products := by decide
  have arrowTyped : LambdaPiModulo leanTheoryExplicit [propType] arrowFamily
      (.pi (eps zero (.var 0)) (U zero)) :=
    .lam (epsZero_formed_explicit (propVariable_explicit rfl)) (uZero_formed_explicit _) rule
      (propVariable_explicit rfl)
  have code : LambdaPiModulo leanTheoryExplicit [propType] (ap "pi" [zero, zero, .var 0, arrowFamily])
      (U (imax zero zero)) :=
    app_at (app_at (app_at (app_at (.con rfl) (zero_typed_explicit _) rfl) (zero_typed_explicit _) rfl)
      (propVariable_explicit rfl) rfl) arrowTyped rfl
  have imaxFormed : LambdaPiModulo leanTheoryExplicit [propType] (U (imax zero zero)) (.srt .type) :=
    app_at (.con rfl) (app_at (app_at (.con rfl) (zero_typed_explicit _) rfl)
      (zero_typed_explicit _) rfl) rfl
  have raw : LambdaPiModulo leanTheoryExplicit [] identityFamily (.pi propType (U (imax zero zero))) :=
    .lam (propType_formed_explicit []) imaxFormed rule code
  exact .conv raw (Conv.pi (.refl _) (Conv.app (.refl _) imax_zero_zero_explicit))
    (.pi (propType_formed_explicit []) (uZero_formed_explicit _) rule)

theorem identityType_formed_explicit :
    LambdaPiModulo leanTheoryExplicit [] identityType (.srt .type) := by
  have code : LambdaPiModulo leanTheoryExplicit [] identityCode (U (imax (succ zero) zero)) :=
    app_at (app_at (app_at (app_at (.con rfl)
      (app_at (.con rfl) (zero_typed_explicit _) rfl) rfl) (zero_typed_explicit _) rfl)
      (app_at (.con rfl) (zero_typed_explicit _) rfl) rfl) identityFamily_typed_explicit rfl
  have codeAtZero : LambdaPiModulo leanTheoryExplicit [] identityCode (U zero) :=
    .conv code (Conv.app (.refl _) imax_one_zero_explicit) (uZero_formed_explicit _)
  exact epsZero_formed_explicit codeAtZero

/-- The translated type and the type of the term have one normal form. -/
theorem conv_identityType_explicit :
    Conv leanTheoryExplicit (.pi propType (.pi (eps zero (.var 0)) (eps zero (.var 1)))) identityType :=
  convExplicit_of_evaluate (fuel := 300) (fuel' := 300)
    (common := evaluate explicitSig explicitRules 300 identityType)
    (by decide +kernel) rfl

/-- **The positive example**: the translation of `fun (A : Prop) (a : A) => a`
has the translation of `∀ A : Prop, A → A` in the theory with explicit
substitution. -/
theorem identity_typed_explicit : LambdaPiModulo leanTheoryExplicit [] identityTerm identityType :=
  .conv identityTerm_typed_raw_explicit conv_identityType_explicit identityType_formed_explicit

#print axioms zero_succ_not_conv_explicit
#print axioms var_maxOneVar_not_conv_explicit
#print axioms section5_typed
#print axioms etaFun_not_joinable_explicit
#print axioms proofIrrelevance_not_joinable_explicit
#print axioms unitValueExplicit_typed
#print axioms unitEta_not_joinable_explicit
#print axioms kLike_not_joinable_explicit
#print axioms identity_typed_explicit

end Mettapedia.GSLT.Dedukti.LeanMinus
