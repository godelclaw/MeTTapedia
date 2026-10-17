import Mettapedia.Logic.HOL.ContextualTrinity
import Mettapedia.Logic.Arithmetic.PresburgerHenkin
import Mettapedia.Logic.PresburgerUniversal

/-!
# Standard-semantics bubbles on the extensional face of the HOL kernel

A standard-semantics bubble decides sentences in one intended model. Over the
signature of zero, one and addition, the Presburger bubble decides a fragment
of closed sentences in the standard model on the natural numbers, and its
verdicts agree with that model (`presburgerBubble_iff_arithStandard`). That
model is a full-domain Henkin model, so it is an extensional face of the HOL
kernel's computational trinity (`presburgerTrinity`).

The bubble and the kernel meet only on that face:

* **A negative verdict refutes kernel evidence.** If the bubble decides a
  sentence false, no retained proof of it exists, at any assumption-free
  sequent (`bubble_false_no_proof`), and no element of the trinity's
  intensional face at the empty context has that sequent
  (`bubble_false_no_logic_element`). Soundness into the standard face carries
  every proof to a true sentence.
* **A positive verdict is not kernel evidence.** The bubble decides `0 ≠ 1`
  true, yet the assumption-free kernel has no proof of it
  (`bubble_true_without_proof`): a one-point model of the same signature,
  another extensional face, refutes it. Deciding the intended model is a
  property of one face; a proof must hold in every face.

So a decision procedure for an intended model sits beside the kernel as an
oracle on one extensional face. Its refutations transfer to the intensional
face, its confirmations do not.

**Two independent authorities on one face.** The universally quantified
affine inequalities of `PresburgerUniversal` translate into the bubble's
sentences (`claimSentence`). The affine checker accepts exactly the claims
whose translation holds in the standard model (`affine_check_iff_models`), and
wherever the bubble decides a translated claim its verdict is the checker's
(`bubble_agrees_with_affine`). The assumption-free kernel proves none of these
sentences, true or false (`affine_sentences_unprovable`): the one-point model
refutes every one of them.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.StandardSemanticsBubbles

open Mettapedia.Logic.Arithmetic.PresburgerHenkin
open Mettapedia.Logic.Arithmetic.PresburgerBubble (presburgerBubble closedEq)

abbrev Sentence := Mettapedia.Logic.Arithmetic.PresburgerBubble.Formula 0

/-- The standard model of addition respects extensional equality. -/
theorem arithStandard_respects : arithStandard.FunctionsRespectEqv := by
  rw [arithStandard_standard]
  exact HenkinModel.functionsRespectEqv_of_fullDomains _ (HenkinModel.fullDomains_standard _ _)

/-- The HOL kernel's trinity over the signature of addition, with the standard
model of the natural numbers as its extensional face. -/
abbrev presburgerTrinity :=
  ContextualTrinity.comparison arithStandard arithStandard_respects

/-- A retained assumption-free proof holds in every full-domain extensional
face whose functions respect extensional equality. -/
theorem proof_models {M : HenkinModel.{0, 0, 0} ArithBase ArithConst}
    (respects : M.FunctionsRespectEqv) {sentence : ClosedFormula ArithConst}
    (proof : ProofSyntax ArithConst [] sentence) : M.models sentence :=
  Soundness.extDerivation_sound proof.erase respects (fun index => nomatch index)
    (fun _ member => nomatch member)

/-- **A negative verdict refutes every kernel proof.** -/
theorem bubble_false_no_proof (φ : Sentence)
    (refuted : presburgerBubble.decide φ = some false) :
    IsEmpty (ProofSyntax ArithConst [] (embed φ)) := by
  refine ⟨fun proof => ?_⟩
  have holds := proof_models arithStandard_respects proof
  have verdict := (presburgerBubble_iff_arithStandard φ refuted).mpr holds
  cases verdict

/-- The same refutation on the trinity's intensional face at the empty
context. -/
theorem bubble_false_no_logic_element (φ : Sentence)
    (refuted : presburgerBubble.decide φ = some false)
    (proved : ContextualTrinity.ProvedSequent (Const := ArithConst) []) :
    proved.1 ≠ ([], embed φ) := by
  obtain ⟨⟨hypotheses, conclusion⟩, proof⟩ := proved
  intro same
  cases same
  exact (bubble_false_no_proof φ refuted).false proof

/-- A one-point model of the signature of addition. -/
def onePoint : HenkinModel.{0, 0, 0} ArithBase ArithConst :=
  HenkinModel.standard (fun _ => PUnit.{2})
    (fun {τ} constant => match τ, constant with
      | _, .zero => PUnit.unit
      | _, .one => PUnit.unit
      | _, .add => fun _ _ => PUnit.unit)

theorem onePoint_respects : onePoint.FunctionsRespectEqv :=
  HenkinModel.functionsRespectEqv_of_fullDomains _ (HenkinModel.fullDomains_standard _ _)

/-- `0 ≠ 1`. -/
def zeroNeOne : Sentence := .neg (closedEq 0 1)

theorem zeroNeOne_decided : presburgerBubble.decide zeroNeOne = some true := rfl

/-- The one-point model identifies every pair of individuals. -/
theorem onePoint_refutes_zeroNeOne : ¬ onePoint.models (embed zeroNeOne) := by
  intro holds
  apply holds
  exact Subsingleton.elim (α := PUnit.{2}) _ _

/-- **A positive verdict is not kernel evidence.** -/
theorem bubble_true_without_proof :
    presburgerBubble.decide zeroNeOne = some true ∧
      arithStandard.models (embed zeroNeOne) ∧
      IsEmpty (ProofSyntax ArithConst [] (embed zeroNeOne)) :=
  ⟨zeroNeOne_decided,
    (presburgerBubble_iff_arithStandard zeroNeOne zeroNeOne_decided).mp rfl,
    ⟨fun proof => onePoint_refutes_zeroNeOne (proof_models onePoint_respects proof)⟩⟩

/-- Negative control: `0 = 1` is decided false, so it has no proof. -/
theorem zeroEqOne_no_proof : IsEmpty (ProofSyntax ArithConst [] (embed (closedEq 0 1))) :=
  bubble_false_no_proof (closedEq 0 1) rfl

/-! ## Affine claims: the checker, the bubble and the kernel -/

open Mettapedia.Logic.Arithmetic.PresburgerBubble (Coeff LinTerm Atom envCons env0)
open Mettapedia.Logic.PresburgerUniversal (Affine Claim normalize normalize_correct)

/-- Coefficients from a function on variable positions. -/
def Coeff.ofFun : {n : Nat} → (Fin n → Nat) → Coeff n
  | 0, _ => .nil
  | _ + 1, coefficients => .cons (coefficients 0) (Coeff.ofFun fun index => coefficients index.succ)

theorem Coeff.dot_ofFun : {n : Nat} → (coefficients : Fin n → Nat) → (env : Fin n → Nat) →
    (Coeff.ofFun coefficients).dot env = ∑ index, coefficients index * env index
  | 0, _, _ => rfl
  | _ + 1, coefficients, env => by
      simp only [Coeff.ofFun, Mettapedia.Logic.Arithmetic.PresburgerBubble.dot_cons,
        Coeff.dot_ofFun, Fin.sum_univ_succ]

/-- The affine form as a linear term of the bubble. -/
def toLinTerm {n : Nat} (form : Affine n) : LinTerm n := ⟨Coeff.ofFun form.coefficient, form.constant⟩

theorem toLinTerm_eval {n : Nat} (form : Affine n) (env : Fin n → Nat) :
    (toLinTerm form).eval env = form.eval env := by
  simp only [toLinTerm, Mettapedia.Logic.Arithmetic.PresburgerBubble.LinTerm.eval,
    Coeff.dot_ofFun, Affine.eval]
  omega

/-- Close a formula by existential quantifiers over all its variables. -/
def existsAll : {n : Nat} → Mettapedia.Logic.Arithmetic.PresburgerBubble.Formula n → Sentence
  | 0, body => body
  | _ + 1, body => existsAll (.ex body)

theorem existsAll_sat : {n : Nat} → (body : Mettapedia.Logic.Arithmetic.PresburgerBubble.Formula n) →
    (existsAll body).sat env0 ↔ ∃ env, body.sat env
  | 0, body => by
      constructor
      · intro holds
        exact ⟨env0, holds⟩
      · rintro ⟨env, holds⟩
        have same : env = env0 := funext fun index => index.elim0
        subst same
        exact holds
  | n + 1, body => by
      rw [existsAll, existsAll_sat]
      constructor
      · rintro ⟨env, value, holds⟩
        exact ⟨envCons value env, holds⟩
      · rintro ⟨env, holds⟩
        refine ⟨fun index => env index.succ, env 0, ?_⟩
        have same : envCons (env 0) (fun index => env index.succ) = env := by
          funext index
          refine Fin.cases ?_ (fun index => ?_) index <;> rfl
        rw [same]
        exact holds

/-- `∀x. left ≤ right`, as the negation of `∃x. right < left`. -/
def claimSentence {n : Nat} (claim : Claim n) : Sentence :=
  .neg (existsAll (.atom (.lt (toLinTerm (normalize claim.right)) (toLinTerm (normalize claim.left)))))

theorem claimSentence_sat_iff {n : Nat} (claim : Claim n) :
    (claimSentence claim).sat env0 ↔ claim.Meaning := by
  simp only [claimSentence, Mettapedia.Logic.Arithmetic.PresburgerBubble.Formula.sat,
    existsAll_sat, Mettapedia.Logic.Arithmetic.PresburgerBubble.Atom.sat, toLinTerm_eval,
    normalize_correct, not_exists, not_lt, Claim.Meaning]

/-- **The affine checker accepts exactly the claims true on the standard
face.** -/
theorem affine_check_iff_models {n : Nat} (claim : Claim n) :
    claim.check = true ↔ arithStandard.models (embed (claimSentence claim)) :=
  (Claim.check_eq_true_iff claim).trans
    ((claimSentence_sat_iff claim).symm.trans (embed_models_iff _).symm)

/-- **The bubble and the affine checker agree wherever the bubble decides.** -/
theorem bubble_agrees_with_affine {n : Nat} (claim : Claim n) {verdict : Bool}
    (decided : presburgerBubble.decide (claimSentence claim) = some verdict) :
    verdict = claim.check := by
  have viaBubble := presburgerBubble_iff_arithStandard (claimSentence claim) decided
  have viaChecker := affine_check_iff_models claim
  cases verdict <;> cases checked : claim.check <;> simp_all

/-- In the one-point model every existential closure of a strict comparison
holds. -/
theorem onePoint_existsAll_lt : {n : Nat} → (left right : LinTerm n) →
    onePoint.models (embed (existsAll (.atom (.lt left right))))
  | n, left, right => by
      have general : ∀ {m : Nat} (body : Mettapedia.Logic.Arithmetic.PresburgerBubble.Formula m),
          (∀ valuation : HenkinModel.Valuation onePoint (arithCtx m),
            (HenkinModel.denote onePoint (embed body) valuation).down) →
          onePoint.models (embed (existsAll body)) := by
        intro m
        induction m with
        | zero =>
            intro body holds
            exact holds _
        | succ m ih =>
            intro body holds
            apply ih (.ex body)
            intro valuation
            exact ⟨PUnit.unit, trivial, holds _⟩
      apply general
      intro valuation
      exact ⟨PUnit.unit, trivial, Subsingleton.elim (α := PUnit.{2}) _ _⟩

/-- **No translated affine claim is provable in the assumption-free kernel.**
The one-point model refutes all of them, whether the standard model makes
them true or false. -/
theorem affine_sentences_unprovable {n : Nat} (claim : Claim n) :
    IsEmpty (ProofSyntax ArithConst [] (embed (claimSentence claim))) := by
  refine ⟨fun proof => ?_⟩
  have holds := proof_models onePoint_respects proof
  exact holds (onePoint_existsAll_lt _ _)

namespace Controls

open FirstOrder

/-- `2x + 1 ≤ 3x + 4`, true for every natural. -/
def increasing : Claim 1 where
  left := (Language.Term.var 0 + Language.Term.var 0) + 1
  right := (Language.Term.var 0 + Language.Term.var 0) + Language.Term.var 0 + 4

/-- `3x ≤ 2x + 10`, false from eleven on. -/
def eventuallyFalse : Claim 1 where
  left := (Language.Term.var 0 + Language.Term.var 0) + Language.Term.var 0
  right := (Language.Term.var 0 + Language.Term.var 0) + 10

theorem increasing_checked : increasing.check = true := by decide

theorem eventuallyFalse_refused : eventuallyFalse.check = false := by decide

theorem increasing_decided : presburgerBubble.decide (claimSentence increasing) = some true := by
  decide +kernel

theorem eventuallyFalse_decided :
    presburgerBubble.decide (claimSentence eventuallyFalse) = some false := by
  decide +kernel

/-- Both authorities place the true claim on the standard face; the kernel
still has no proof of it. -/
theorem increasing_standard_not_kernel :
    arithStandard.models (embed (claimSentence increasing)) ∧
      IsEmpty (ProofSyntax ArithConst [] (embed (claimSentence increasing))) :=
  ⟨(affine_check_iff_models increasing).mp increasing_checked,
    affine_sentences_unprovable increasing⟩

end Controls

#print axioms affine_check_iff_models
#print axioms bubble_agrees_with_affine
#print axioms affine_sentences_unprovable
#print axioms bubble_false_no_proof
#print axioms bubble_false_no_logic_element
#print axioms bubble_true_without_proof
#print axioms zeroEqOne_no_proof

end Mettapedia.Logic.HOL.StandardSemanticsBubbles
