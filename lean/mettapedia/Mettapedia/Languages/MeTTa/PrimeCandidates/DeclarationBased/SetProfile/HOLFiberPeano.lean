import Mettapedia.TypeTheory.HOLFiber.Fiber
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.LinkedEquality
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ConvRecursor
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.Models

/-!
# Large elimination in `objectRules` vs. the three-axiom `zeroAddAssumptions` fixture

The declaration-based candidate `objectRules` reads the `set:` profile's HOL
signature (`setReading`) under the identity reading. Its recursor on the
numbers,
`num-rec : Π P : num → U₀. P zero → (Π v. P v → P (suc v)) → Π t. P t`,
computes by two ι-rules, and the package treats them as definitional equality.

* **Non-carrier dependent family.** `eqAt n`, the identity type `add zero n = n`
  indexed by a number `n`, is a well-formed dependent family in `objectRules`
  (`eqAt_typed`) that is not a simple-type carrier of `setReading`
  (`eqAt_not_carrier`).
* **Disjointness by large elimination (Jan Smith 1988).** Because `prop : U₀`,
  the motive `λ_. prop` defines a code by recursion,
  `T t := num-rec (λ_. prop) (⊥ ⇒ ⊥) (λ v r. ⊥) t`, with
  `T zero ≡ (⊥ ⇒ ⊥)` and `T (suc t) ≡ ⊥`. Transport of `λy. T y` along evidence
  for `zero = suc n` turns `λx. x` into a proof of `⊥`. The package proves the
  decoding of the code of `∀n. zero = suc n → ∀p. p` (`disjointness_typedO`,
  `disjointness_read`).
* **Injectivity.** The motive `λ_. num` defines the predecessor,
  `pred (suc t) ≡ t`. Transport of `λy. a = pred y` along evidence for
  `suc a = suc b` turns `refl a` into a proof of `a = b`. The package proves the
  decoding of the code of `∀a b. suc a = suc b → a = b` (`injectivity_typedO`,
  `injectivity_read`).

By contrast, the three-fact fixture `SetProfile.zeroAddAssumptions`
(`[inductionAxiom, reflAxiom, substAxiom]`, introduced specifically for the
`0 + n = n` example in `SetProfile/Basic.lean`) omits the Peano constructor
axioms and HOL's Axiom of Infinity (from which standard HOL derives both
disjointness and injectivity). Consequently, `zeroAddAssumptions` leaves both
sentences open (`not_provable_modulo_of_countermodel`,
`not_provable_ext_of_countermodel`):

* With one number and one set (`onePoint`), `zeroAddAssumptions` holds and
  `zero = suc zero` (`disjointness_not_provable_modulo`,
  `disjointness_not_provable_assumed`).
* With two numbers whose successor is constantly the second (`lasso`),
  `zeroAddAssumptions` holds and the successor is not injective
  (`injectivity_not_provable_modulo`, `injectivity_not_provable_assumed`).

Both sentences hold in the standard naturals (`disjointness_holds_naturals`,
`injectivity_holds_naturals`). This isolates what `objectRules` uses beyond
`zeroAddAssumptions`: the ι-computation of `num-rec` at the code motive
`λ_. prop` (large elimination) and at the motive `λ_. num`. When translating
between a DTT candidate with large elimination and a HOL fiber, either the HOL
side includes the corresponding Peano/Infinity axioms or the conversion steps
enter as proved equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.HOLFiberPeano

open Mettapedia.TypeTheory.HOLFiber
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Impredicative
open Mettapedia.Logic
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.CodeModel
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile
  (SetBase SetConst numTy setTy zeroT sucT zeroNative sucNative)
open Package (jName numT numRecApp)

/-! ## Non-carrier dependent family -/

/-- `eqAt n`, the identity type `add zero n = n` indexed by a number, is not a
carrier of the set reading: substituting `zero` and `suc zero` for `n` gives
two different types. -/
theorem eqAt_not_carrier :
    ¬ IsCarrier setReading (Package.eqAtApp (.var 0) : Tower.Tm 1) := by
  refine not_isCarrier_of_subst_ne (m := 0) (σ := fun _ => (zeroNative : Tower.Tm 0))
    (σ' := fun _ => (SetProfile.sucNative zeroNative : Tower.Tm 0)) ?_
  intro same
  cases same

/-- The family `eqAt` is a type of the object package over the numbers, so the
non-carrier above is a well-formed dependent type. -/
theorem eqAt_typed : Typed objectRules (.snoc .nil Package.numT) (Package.eqAtApp (.var 0))
    Package.U0 := by
  have declared : objectRules.constantType Package.eqAtName = some Package.eqAtType := rfl
  exact .appElim (.const declared (piO (raiseO num_typedO) U0_typedO) (.sort _)) (.var 0)

/-! ## The sentence and its code -/

/-- `∀n. zero = suc n → ∀p. p`: the successor never returns `zero`. -/
def disjointnessStatement : HOL.Formula SetConst [] :=
  .all (σ := numTy) (.imp (.eq zeroT (sucT (.var .vz))) (.all (σ := .prop) (.var .vz)))

/-- Its code: `all@num (λn. eq@num zero (suc n) ⇒ all@prop (λp. p))`. -/
def disjointnessCode : Tower.Tm 0 :=
  setReading.allOf numTy (.lam (programCodes.impOf
    (setReading.eqOf numTy zeroNative (sucNative (.var 0))) botCode))

/-- The reading of the sentence is its code. -/
theorem disjointness_read : setReading.term disjointnessStatement = some disjointnessCode := rfl

/-! ## A code defined by recursion on the numbers -/

section Recursion

variable {n : Nat} {Γ : Tower.Ctx n}

/-- The constant motive `λ_. prop`. -/
def motive {n : Nat} : Tower.Tm n := .lam (.const propN)

/-- `⊥ ⇒ ⊥`, the value at `zero`. -/
def topCode {n : Nat} : Tower.Tm n := programCodes.impOf botCode botCode

/-- `λ v r. ⊥`, the step. -/
def stepFn {n : Nat} : Tower.Tm n := .lam (.lam botCode)

/-- `T t = num-rec (λ_. prop) (⊥ ⇒ ⊥) (λ v r. ⊥) t`. -/
def tagCode {n : Nat} (t : Tower.Tm n) : Tower.Tm n := numRecApp motive topCode stepFn t

theorem motive_formed : Typed objectRules Γ (.pi numT Package.U0) U1 :=
  piO (raiseO num_typedO) U0_typedO

theorem motive_typed : Typed objectRules Γ motive (.pi numT Package.U0) :=
  .lamIntro motive_formed (.sort _) prop_typedO

/-- `(λ_. prop) t ≡ prop`. -/
theorem motive_beta {t : Tower.Tm n} (ht : Typed objectRules Γ t numT) :
    Equal objectRules Γ (.app motive t) (.const propN) Package.U0 :=
  Derivable.betaPi motive_formed (.sort _) prop_typedO ht

theorem topCode_typed : Typed objectRules Γ topCode (.const propN) :=
  setReading_laws.impOf_typed botCode_typed botCode_typed

theorem stepFn_simple :
    Typed objectRules Γ stepFn (.pi numT (.pi (.const propN) (.const propN))) :=
  .lamIntro (piO num_typedO (piO prop_typedO prop_typedO)) (.sort _)
    (.lamIntro (piO prop_typedO prop_typedO) (.sort _) botCode_typed)

/-- The step at the type the recursor asks for. -/
theorem stepFn_typed :
    Typed objectRules Γ stepFn
      (.pi numT (.pi (.app (Presentation.rename wk motive) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk motive))
          (.app (.const sucN) (.var 1))))) := by
  have atVar : Typed objectRules (.snoc Γ numT) (.app motive (.var 0)) Package.U0 :=
    .appElim motive_typed (.var 0)
  have sucVar : Typed objectRules (.snoc (.snoc Γ numT) (.app motive (.var 0)))
      (.app (.const sucN) (.var 1)) numT :=
    .appElim suc_typedO (.var 1)
  have atSuc : Typed objectRules (.snoc (.snoc Γ numT) (.app motive (.var 0)))
      (.app motive (.app (.const sucN) (.var 1))) Package.U0 :=
    .appElim motive_typed sucVar
  have body : Typed objectRules (.snoc (.snoc Γ numT) (.app motive (.var 0))) botCode
      (.app motive (.app (.const sucN) (.var 1))) :=
    .conv botCode_typed (.symm (motive_beta sucVar)) (.sort _)
  exact .lamIntro (piO num_typedO (piO atVar atSuc)) (.sort _)
    (.lamIntro (piO atVar atSuc) (.sort _) body)

theorem tagCode_motive {t : Tower.Tm n} (ht : Typed objectRules Γ t numT) :
    Typed objectRules Γ (tagCode t) (.app motive t) :=
  numRec_typedO motive_typed (.conv topCode_typed (.symm (motive_beta zero_typedO)) (.sort _))
    stepFn_typed ht

/-- `T t` is a code. -/
theorem tagCode_typed {t : Tower.Tm n} (ht : Typed objectRules Γ t numT) :
    Typed objectRules Γ (tagCode t) (.const propN) :=
  .conv (tagCode_motive ht) (motive_beta ht) (.sort _)

/-- `T zero ≡ ⊥ ⇒ ⊥`, by the ι-rule at `zero`. -/
theorem tagCode_zero : Equal objectRules Γ (tagCode zeroNative) topCode (.const propN) :=
  .root (programCodes.extend_base_step ExecutableModel.rules
      (ConvRules.rules_numRec_zero motive topCode stepFn))
    (tagCode_typed zero_typedO) topCode_typed

/-- `T (suc t) ≡ ⊥`, by the ι-rule at a successor and two β-steps. -/
theorem tagCode_suc {t : Tower.Tm n} (ht : Typed objectRules Γ t numT) :
    Equal objectRules Γ (tagCode (sucNative t)) botCode (.const propN) := by
  have hsuc : Typed objectRules Γ (sucNative t) numT := .appElim suc_typedO ht
  have stepApplied : Typed objectRules Γ (.app stepFn t) (.pi (.const propN) (.const propN)) :=
    .appElim stepFn_simple ht
  have reduct : Typed objectRules Γ (.app (.app stepFn t) (tagCode t)) (.const propN) :=
    .appElim stepApplied (tagCode_typed ht)
  have iota : Equal objectRules Γ (tagCode (sucNative t)) (.app (.app stepFn t) (tagCode t))
      (.const propN) :=
    .root (programCodes.extend_base_step ExecutableModel.rules
        (ConvRules.rules_numRec_suc motive topCode stepFn t))
      (tagCode_typed hsuc) reduct
  have innerBody : Typed objectRules (.snoc Γ numT) (.lam botCode)
      (.pi (.const propN) (.const propN)) :=
    .lamIntro (piO prop_typedO prop_typedO) (.sort _) botCode_typed
  have beta₁ : Equal objectRules Γ (.app stepFn t) (.lam botCode)
      (.pi (.const propN) (.const propN)) :=
    Derivable.betaPi (piO num_typedO (piO prop_typedO prop_typedO)) (.sort _) innerBody ht
  have beta₁' : Equal objectRules Γ (.app (.app stepFn t) (tagCode t))
      (.app (.lam botCode) (tagCode t)) (.const propN) :=
    Derivable.appCong (A := .const propN) (B := .const propN) beta₁ (.refl (tagCode_typed ht))
  have beta₂ : Equal objectRules Γ (.app (.lam botCode) (tagCode t)) botCode (.const propN) :=
    Derivable.betaPi (piO prop_typedO prop_typedO) (.sort _) botCode_typed (tagCode_typed ht)
  exact .trans iota (.trans beta₁' beta₂)

end Recursion

/-! ## The proof -/

/-- `λx. x`, a proof of `holds (⊥ ⇒ ⊥)`. -/
theorem topProof_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed objectRules Γ (.lam (.var 0)) (programCodes.holdsOf topCode) :=
  setReading_laws.impIntro botCode_typed botCode_typed (.var 0)

/-- `λ n e. transport (λy. T y) e (λx. x)`: transport along the evidence for
`zero = suc n` from `T zero` to `T (suc n)`. -/
def disjointnessProof : Tower.Tm 0 :=
  .lam (.lam (setReading.transport jName numT zeroNative (tagCode (.var 0)) (.lam (.var 0))
    (sucNative (.var 1)) (.var 0)))

/-- **The object package proves constructor disjointness.** The closed term
`disjointnessProof` has the decoding of the code of
`∀n. zero = suc n → ∀p. p` as its type. -/
theorem disjointness_typedO :
    Typed objectRules .nil disjointnessProof (programCodes.holdsOf disjointnessCode) := by
  have L := setReading_laws
  -- the context `n : num`
  have zeroAt : ∀ {m : Nat} {Δ : Tower.Ctx m}, Typed objectRules Δ (zeroNative) numT :=
    fun {_ _} => zero_typedO
  have eqCode : Typed objectRules (.snoc .nil numT)
      (setReading.eqOf numTy zeroNative (sucNative (.var 0))) (.const propN) :=
    L.eqOf_typed zeroAt (.appElim suc_typedO (.var 0))
  -- the context `n : num, e : holds (zero = suc n)`
  let Γ₂ : Tower.Ctx 2 :=
    .snoc (.snoc .nil numT) (programCodes.holdsOf (setReading.eqOf numTy zeroNative (sucNative (.var 0))))
  have sucN₂ : Typed objectRules Γ₂ (sucNative (.var 1)) numT := .appElim suc_typedO (.var 1)
  have evidence : Typed objectRules Γ₂ (.var 0) (.id numT zeroNative (sucNative (.var 1))) :=
    .conv (.var 0) (L.equal_holds_eq zeroAt sucN₂) (.sort _)
  have family : Typed objectRules (.snoc Γ₂ numT) (tagCode (.var 0)) (.const propN) :=
    tagCode_typed (.var 0)
  have base : Typed objectRules Γ₂ (.lam (.var 0))
      (programCodes.holdsOf (inst0 zeroNative (tagCode (.var 0)))) :=
    .conv topProof_typed (.symm (L.equal_holdsOf tagCode_zero)) (.sort _)
  have moved : Typed objectRules Γ₂
      (setReading.transport jName numT zeroNative (tagCode (.var 0)) (.lam (.var 0))
        (sucNative (.var 1)) (.var 0))
      (programCodes.holdsOf (inst0 (sucNative (.var 1)) (tagCode (.var 0)))) :=
    setTransport.typed num_typedO zeroAt sucN₂ family base evidence
  have absurd : Typed objectRules Γ₂
      (setReading.transport jName numT zeroNative (tagCode (.var 0)) (.lam (.var 0))
        (sucNative (.var 1)) (.var 0))
      (programCodes.holdsOf botCode) :=
    .conv moved (L.equal_holdsOf (tagCode_suc (.var 1))) (.sort _)
  have implication := L.impIntro eqCode botCode_typed absurd
  exact L.allIntro (L.impOf_typed eqCode botCode_typed) implication

/-! ## The three-axiom `zeroAddAssumptions` fixture does not decide it -/

open SetProfile.Models
open HOL

/-- One number and one set. -/
abbrev onePoint : Interpretation where
  Num := PUnit.{2}
  Sets := PUnit.{2}
  zero := PUnit.unit
  suc := fun _ => PUnit.unit
  add := fun _ _ => PUnit.unit
  pow := fun _ _ => PUnit.unit
  member := fun _ _ => True
  empty := PUnit.unit
  union := id
  power := id
  universeOf := id

theorem onePoint_lawful : onePoint.Lawful where
  add_zero _ := rfl
  add_suc _ _ := rfl
  pow_zero _ := rfl
  pow_suc _ _ := rfl

theorem onePoint_inductive : onePoint.Inductive := by
  intro predicate base _ x
  cases x
  exact base

/-- Facts that hold in an interpretation. -/
def Holds (I : Interpretation) (φ : HOL.Formula SetConst []) : Prop :=
  (HenkinModel.denote I.model φ (emptyValuation I.model)).down

/-- A standard model of the set profile is extensional. -/
theorem model_extensional (I : Interpretation) : I.model.FunctionsRespectEqv :=
  I.model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _)

/-- **A countermodel bounds the extensional calculus.** A sentence that fails in
an interpretation has no derivation in the extensional HOL calculus from any
closed theory that holds there. -/
theorem not_provable_ext_of_countermodel (I : Interpretation) {T : ClosedTheorySet SetConst}
    (satisfied : ∀ φ ∈ T, Holds I φ) {statement : HOL.Formula SetConst []}
    (fails : ¬ Holds I statement) : ¬ ClosedTheorySet.Provable T statement := by
  rintro ⟨Δ, within, derivation⟩
  exact fails (Soundness.extDerivation_sound derivation (ρ := emptyValuation I.model)
    (model_extensional I) (emptyValuation_admissible I.model)
    (fun φ member => satisfied φ (within φ member)))

/-- **A countermodel bounds the checking calculus.** -/
theorem not_provable_modulo_of_countermodel {I : Interpretation} (lawful : I.Lawful)
    (inductive_ : I.Inductive) {statement : HOL.Formula SetConst []}
    (fails : ¬ Holds I statement) :
    ¬ Nonempty (ProofSyntaxModulo SetProfile.definedEquations SetProfile.zeroAddAssumptions
      statement) := by
  rintro ⟨proof⟩
  exact fails (proof_sound I proof (definedEquationsHold lawful) (facts_hold inductive_))

/-- The theory of the facts assumed for `zero-add`: induction, reflexivity and
substitution at the numbers. -/
def assumedFacts : ClosedTheorySet SetConst := {φ | φ ∈ SetProfile.zeroAddAssumptions}

theorem assumedFacts_hold {I : Interpretation} (inductive_ : I.Inductive) :
    ∀ φ ∈ assumedFacts, Holds I φ :=
  fun φ member => facts_hold inductive_ φ member

/-- In the one-point interpretation `zero = suc zero`, so the sentence fails. -/
theorem disjointness_fails_onePoint : ¬ Holds onePoint disjointnessStatement :=
  fun holds => (holds PUnit.unit trivial rfl (ULift.up False) trivial)

/-- **No proof modulo the stored equations.** The profile's checking calculus,
modulo the defining equations of `add`, `pow` and `Falsum` and from the facts
assumed for `zero-add` (induction, reflexivity, substitution), has no proof of
the sentence. -/
theorem disjointness_not_provable_modulo :
    ¬ Nonempty (ProofSyntaxModulo SetProfile.definedEquations SetProfile.zeroAddAssumptions
      disjointnessStatement) :=
  not_provable_modulo_of_countermodel onePoint_lawful onePoint_inductive
    disjointness_fails_onePoint

/-- **No extensional HOL derivation from facts true at one point**, for
instance from the assumed facts (`disjointness_not_provable_assumed`). -/
theorem disjointness_not_provable_ext {T : ClosedTheorySet SetConst}
    (satisfied : ∀ φ ∈ T, Holds onePoint φ) :
    ¬ ClosedTheorySet.Provable T disjointnessStatement :=
  not_provable_ext_of_countermodel onePoint satisfied disjointness_fails_onePoint

theorem disjointness_not_provable_assumed :
    ¬ ClosedTheorySet.Provable assumedFacts disjointnessStatement :=
  disjointness_not_provable_ext (assumedFacts_hold onePoint_inductive)

/-- **It is true of the numbers.** -/
theorem disjointness_holds_naturals : Holds naturals disjointnessStatement := by
  intro number _ same _ _
  have equal : (0 : ℕ) = number.down + 1 := congrArg ULift.down same
  exact absurd equal.symm (Nat.succ_ne_zero _)

/-! ## Injectivity of the successor, by the predecessor

The predecessor is defined by recursion at the motive `λ_. num`:
`pred t := num-rec (λ_. num) zero (λ v r. v) t`, so `pred (suc t) ≡ t` by the
ι-rule and two β-steps. Transport of the code family `λy. a = pred y` along
evidence for `suc a = suc b` turns `refl a` into a proof of `a = b`. With
disjointness, the package proves that the successor is injective and misses
`zero`: Dedekind infinity of the numbers. The facts assumed for `zero-add` do
not prove injectivity: in the interpretation with two numbers whose successor
is constantly the second one, they hold and injectivity fails. -/

/-- `∀a b. suc a = suc b → a = b`. -/
def injectivityStatement : HOL.Formula SetConst [] :=
  .all (σ := numTy) (.all (σ := numTy) (.imp (.eq (sucT (.var (.vs .vz))) (sucT (.var .vz)))
    (.eq (.var (.vs .vz)) (.var .vz))))

def injectivityCode : Tower.Tm 0 :=
  setReading.allOf numTy (.lam (setReading.allOf numTy (.lam (programCodes.impOf
    (setReading.eqOf numTy (sucNative (.var 1)) (sucNative (.var 0)))
    (setReading.eqOf numTy (.var 1) (.var 0))))))

theorem injectivity_read : setReading.term injectivityStatement = some injectivityCode := rfl

section Predecessor

variable {n : Nat} {Γ : Tower.Ctx n}

def numMotive {n : Nat} : Tower.Tm n := .lam numT

/-- `λ v r. v`. -/
def predStep {n : Nat} : Tower.Tm n := .lam (.lam (.var 1))

/-- `pred t = num-rec (λ_. num) zero (λ v r. v) t`. -/
def predApp {n : Nat} (t : Tower.Tm n) : Tower.Tm n := numRecApp numMotive zeroNative predStep t

theorem numMotive_typed : Typed objectRules Γ numMotive (.pi numT Package.U0) :=
  .lamIntro motive_formed (.sort _) num_typedO

theorem numMotive_beta {t : Tower.Tm n} (ht : Typed objectRules Γ t numT) :
    Equal objectRules Γ (.app numMotive t) numT Package.U0 :=
  Derivable.betaPi motive_formed (.sort _) num_typedO ht

theorem predStep_simple : Typed objectRules Γ predStep (.pi numT (.pi numT numT)) :=
  .lamIntro (piO num_typedO (piO num_typedO num_typedO)) (.sort _)
    (.lamIntro (piO num_typedO num_typedO) (.sort _) (.var 1))

theorem predStep_typed :
    Typed objectRules Γ predStep
      (.pi numT (.pi (.app (Presentation.rename wk numMotive) (.var 0))
        (.app (Presentation.rename wk (Presentation.rename wk numMotive))
          (.app (.const sucN) (.var 1))))) := by
  have atVar : Typed objectRules (.snoc Γ numT) (.app numMotive (.var 0)) Package.U0 :=
    .appElim numMotive_typed (.var 0)
  have sucVar : Typed objectRules (.snoc (.snoc Γ numT) (.app numMotive (.var 0)))
      (.app (.const sucN) (.var 1)) numT :=
    .appElim suc_typedO (.var 1)
  have atSuc : Typed objectRules (.snoc (.snoc Γ numT) (.app numMotive (.var 0)))
      (.app numMotive (.app (.const sucN) (.var 1))) Package.U0 :=
    .appElim numMotive_typed sucVar
  have body : Typed objectRules (.snoc (.snoc Γ numT) (.app numMotive (.var 0))) (.var 1)
      (.app numMotive (.app (.const sucN) (.var 1))) :=
    .conv (.var 1) (.symm (numMotive_beta sucVar)) (.sort _)
  exact .lamIntro (piO num_typedO (piO atVar atSuc)) (.sort _)
    (.lamIntro (piO atVar atSuc) (.sort _) body)

theorem predApp_typed {t : Tower.Tm n} (ht : Typed objectRules Γ t numT) :
    Typed objectRules Γ (predApp t) numT :=
  .conv (numRec_typedO numMotive_typed
      (.conv zero_typedO (.symm (numMotive_beta zero_typedO)) (.sort _)) predStep_typed ht)
    (numMotive_beta ht) (.sort _)

/-- `pred (suc t) ≡ t`. -/
theorem predApp_suc {t : Tower.Tm n} (ht : Typed objectRules Γ t numT) :
    Equal objectRules Γ (predApp (sucNative t)) t numT := by
  have hsuc : Typed objectRules Γ (sucNative t) numT := .appElim suc_typedO ht
  have reduct : Typed objectRules Γ (.app (.app predStep t) (predApp t)) numT :=
    .appElim (.appElim predStep_simple ht) (predApp_typed ht)
  have iota : Equal objectRules Γ (predApp (sucNative t)) (.app (.app predStep t) (predApp t))
      numT :=
    .root (programCodes.extend_base_step ExecutableModel.rules
      (ConvRules.rules_numRec_suc numMotive zeroNative predStep t)) (predApp_typed hsuc) reduct
  have innerBody : Typed objectRules (.snoc Γ numT) (.lam (.var 1)) (.pi numT numT) :=
    .lamIntro (piO num_typedO num_typedO) (.sort _) (.var 1)
  have beta₁ : Equal objectRules Γ (.app predStep t) (.lam (Presentation.rename wk t))
      (.pi numT numT) :=
    Derivable.betaPi (piO num_typedO (piO num_typedO num_typedO)) (.sort _) innerBody ht
  have beta₁' : Equal objectRules Γ (.app (.app predStep t) (predApp t))
      (.app (.lam (Presentation.rename wk t)) (predApp t)) numT :=
    Derivable.appCong (A := numT) (B := numT) beta₁ (.refl (predApp_typed ht))
  have weakened : Typed objectRules (.snoc Γ numT) (Presentation.rename wk t) numT := ht.weaken
  have beta₂ : Equal objectRules Γ (.app (.lam (Presentation.rename wk t)) (predApp t)) t numT := by
    have h := Derivable.betaPi (piO num_typedO num_typedO) (.sort _) weakened (predApp_typed ht)
    rwa [inst0_rename_wk] at h
  exact .trans iota (.trans beta₁' beta₂)

end Predecessor

/-- `λ a b e. transport (λy. a = pred y) e (refl a)`. -/
def injectivityProof : Tower.Tm 0 :=
  .lam (.lam (.lam (setReading.transport jName numT (sucNative (.var 2))
    (setReading.eqOf numTy (.var 3) (predApp (.var 0))) (.refl (.var 2))
    (sucNative (.var 1)) (.var 0))))

/-- **The object package proves injectivity of the successor.** -/
theorem injectivity_typedO :
    Typed objectRules .nil injectivityProof (programCodes.holdsOf injectivityCode) := by
  have L := setReading_laws
  let Γ₂ : Tower.Ctx 2 := .snoc (.snoc .nil numT) numT
  have premiseCode : Typed objectRules Γ₂
      (setReading.eqOf numTy (sucNative (.var 1)) (sucNative (.var 0))) (.const propN) :=
    L.eqOf_typed (.appElim suc_typedO (.var 1)) (.appElim suc_typedO (.var 0))
  have conclusionCode : Typed objectRules Γ₂ (setReading.eqOf numTy (.var 1) (.var 0))
      (.const propN) :=
    L.eqOf_typed (.var 1) (.var 0)
  let Γ₃ : Tower.Ctx 3 := .snoc Γ₂ (programCodes.holdsOf
    (setReading.eqOf numTy (sucNative (.var 1)) (sucNative (.var 0))))
  have a₃ : Typed objectRules Γ₃ (.var 2) numT := .var 2
  have sucA : Typed objectRules Γ₃ (sucNative (.var 2)) numT := .appElim suc_typedO (.var 2)
  have sucB : Typed objectRules Γ₃ (sucNative (.var 1)) numT := .appElim suc_typedO (.var 1)
  have evidence : Typed objectRules Γ₃ (.var 0) (.id numT (sucNative (.var 2)) (sucNative (.var 1))) :=
    .conv (.var 0) (L.equal_holds_eq sucA sucB) (.sort _)
  have family : Typed objectRules (.snoc Γ₃ numT)
      (setReading.eqOf numTy (.var 3) (predApp (.var 0))) (.const propN) :=
    L.eqOf_typed (.var 3) (predApp_typed (.var 0))
  have eqA : Typed objectRules Γ₃ (.app (.const eqNumN) (.var 2)) (.pi numT (.const propN)) :=
    .appElim eqNum_typedO a₃
  have atSucA : Equal objectRules Γ₃ (setReading.eqOf numTy (.var 2) (predApp (sucNative (.var 2))))
      (setReading.eqOf numTy (.var 2) (.var 2)) (.const propN) :=
    Derivable.appCong (A := numT) (B := .const propN) (.refl eqA) (predApp_suc a₃)
  have base : Typed objectRules Γ₃ (.refl (.var 2))
      (programCodes.holdsOf (inst0 (sucNative (.var 2))
        (setReading.eqOf numTy (.var 3) (predApp (.var 0))))) :=
    .conv (L.reflIntro (τ := numTy) a₃) (.symm (L.equal_holdsOf atSucA)) (.sort _)
  have moved := setTransport.typed num_typedO sucA sucB family base evidence
  have atSucB : Equal objectRules Γ₃ (setReading.eqOf numTy (.var 2) (predApp (sucNative (.var 1))))
      (setReading.eqOf numTy (.var 2) (.var 1)) (.const propN) :=
    Derivable.appCong (A := numT) (B := .const propN) (.refl eqA) (predApp_suc (.var 1))
  have concluded : Typed objectRules Γ₃
      (setReading.transport jName numT (sucNative (.var 2))
        (setReading.eqOf numTy (.var 3) (predApp (.var 0))) (.refl (.var 2))
        (sucNative (.var 1)) (.var 0))
      (programCodes.holdsOf (Presentation.rename wk (setReading.eqOf numTy (.var 1) (.var 0)))) :=
    .conv moved (L.equal_holdsOf atSucB) (.sort _)
  have implication := L.impIntro premiseCode conclusionCode concluded
  have inner := L.allIntro (τ := numTy) (Γ := .snoc .nil numT)
    (L.impOf_typed premiseCode conclusionCode) implication
  have innerCode : Typed objectRules (.snoc .nil numT)
      (setReading.allOf numTy (.lam (programCodes.impOf
        (setReading.eqOf numTy (sucNative (.var 1)) (sucNative (.var 0)))
        (setReading.eqOf numTy (.var 1) (.var 0))))) (.const propN) :=
    L.allOf_typed (.lamIntro (piO num_typedO prop_typedO) (.sort _)
      (L.impOf_typed premiseCode conclusionCode))
  exact L.allIntro (τ := numTy) (Γ := .nil) innerCode inner

/-- Two numbers; the successor of each is the second. -/
abbrev lasso : Interpretation where
  Num := ULift.{1} Bool
  Sets := PUnit.{2}
  zero := ⟨false⟩
  suc := fun _ => ⟨true⟩
  add := fun left right => if right.down then ⟨true⟩ else left
  pow := fun _ set => set
  member := fun _ _ => True
  empty := PUnit.unit
  union := id
  power := id
  universeOf := id

theorem lasso_lawful : lasso.Lawful where
  add_zero _ := rfl
  add_suc _ _ := rfl
  pow_zero _ := rfl
  pow_suc _ _ := rfl

theorem lasso_inductive : lasso.Inductive := by
  intro predicate base step x
  obtain ⟨b⟩ := x
  cases b with
  | false => exact base
  | true => exact step ⟨false⟩ base

/-- Injectivity fails in the lasso: both numbers have the same successor. -/
theorem injectivity_fails_lasso : ¬ Holds lasso injectivityStatement := by
  intro holds
  have same := holds ⟨false⟩ trivial ⟨true⟩ trivial rfl
  exact Bool.false_ne_true (congrArg ULift.down same)

theorem injectivity_not_provable_modulo :
    ¬ Nonempty (ProofSyntaxModulo SetProfile.definedEquations SetProfile.zeroAddAssumptions
      injectivityStatement) :=
  not_provable_modulo_of_countermodel lasso_lawful lasso_inductive injectivity_fails_lasso

theorem injectivity_not_provable_assumed :
    ¬ ClosedTheorySet.Provable assumedFacts injectivityStatement :=
  not_provable_ext_of_countermodel lasso (assumedFacts_hold lasso_inductive)
    injectivity_fails_lasso

theorem injectivity_holds_naturals : Holds naturals injectivityStatement := by
  intro a _ b _ same
  have equal : a.down + 1 = b.down + 1 := congrArg ULift.down same
  exact congrArg ULift.up (Nat.succ_injective equal)

/-! ## Axiom audit -/

#print axioms eqAt_not_carrier
#print axioms eqAt_typed
#print axioms disjointness_read
#print axioms disjointness_typedO
#print axioms disjointness_not_provable_modulo
#print axioms disjointness_not_provable_ext
#print axioms disjointness_not_provable_assumed
#print axioms disjointness_holds_naturals
#print axioms injectivity_read
#print axioms injectivity_typedO
#print axioms injectivity_not_provable_modulo
#print axioms injectivity_not_provable_assumed
#print axioms injectivity_holds_naturals

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.HOLFiberPeano
