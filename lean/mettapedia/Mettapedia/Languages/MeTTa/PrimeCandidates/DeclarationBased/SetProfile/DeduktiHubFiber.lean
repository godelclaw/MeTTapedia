import Mettapedia.GSLT.Dedukti.HOLHubFiber
import Mettapedia.GSLT.Dedukti.HOLHubAdequacy
import Mettapedia.GSLT.Dedukti.HOLHubAdequacyForall
import Mettapedia.GSLT.Dedukti.HOLHubProofs
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.SetReading

/-!
# The set profile, in the STTfa hub and in the object package

The generic comparison of `GSLT.Dedukti.HOLHubFiber` relates a theory of an
encoding in the λΠ-calculus modulo with a lawful reading of the same HOL
signature in a package of proposition codes.  This module instantiates it at
one signature, the set profile's: encoded in the STTfa hub (`sttfaSet`,
`sttfaSetHub`) and read in the object package of the declaration-based
candidate (`setReading`, lawful by `setReading_laws`).

* **A conversion of the hub is an equality of the package**: the hub converts
  the translations of `(λ x. suc x) zero` and `suc zero`, and the package
  equates their reads at the carrier of `num` (`sucRedex_fiber_equal`).
* **The package equates more**: the reads of `λ x. f x` and `f` at `num ⇒ num`
  are equal in the package, while their translations are not convertible in
  the hub (`set_fiber_not_conservative`).
* **The package equates more than βη, through its computations**: the reads
  of `add x zero` and `x` are equal in the package, by the root step of `add`,
  while the two terms are not βη-convertible: a model in which `add n m` is
  `n + 1` separates them (`set_fiber_beyond_betaEta`).  And βη inside the read
  terms is equality of the package (`set_readBetaEta_eta`).
* **A theorem is inhabited in both**: the proof of
  `(∀ x. suc x = suc x) ⇒ suc zero = suc zero` compiles to a term of `eps` of its
  translation in the STTfa hub, and to a term of the decoding of its code in the
  object package (`sucProof_in_both`).
* **Normal proofs of the hub are proofs of the source** on the closed
  implicational fragment, for the set profile (`set_identity_adequate`, an
  instance of `HOLHub.sttfa_adequate_closed`); and the bare `and` of the set
  profile converts with no translation (`set_bareAnd_not_conv_translate`).
* **The normal form of the compiled `sucProof` gives back a proof**: the
  normal term `λ h. h zero` of the type of the proofs of
  `(∀ x. suc x = suc x) ⇒ suc zero = suc zero`, whose ∀-witness `zero` is the
  translation of a HOL term, gives a proof of it (`set_sucProof_adequate`, an
  instance of `HOLHub.sttfa_adequate_coded`).

This is one named comparison, between one hub and one reading.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.DeduktiHubFiber

open Mettapedia.Logic
open Mettapedia.GSLT.Dedukti
open Mettapedia.GSLT.Dedukti.HOLHub
open Mettapedia.GSLT.Dedukti.HOLHubFiber
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.CodeModel
  (setReading setReading_laws setReading_realizes)
open SetProfile (SetBase SetConst numTy)

/-! ## The set profile in the STTfa hub -/

/-- The names of the set profile's symbols in the STTfa hub. -/
def setName : Symbol SetBase SetConst → String
  | .sort .set => "set"
  | .sort .num => "num"
  | .const .falsum => "Falsum"
  | .const .member => "In"
  | .const .empty => "Empty"
  | .const .union => "Union"
  | .const .power => "Power"
  | .const .separation => "Sep"
  | .const .replacement => "Repl"
  | .const .epsilon => "Eps_set"
  | .const .universeOf => "UnivOf"
  | .const .zero => "zero"
  | .const .suc => "suc"
  | .const .add => "add"
  | .const .pow => "pow"
  | .bool => "bool"
  | .arrow => "arrow"
  | .top => "top"
  | .bot => "bot"
  | .and => "and"
  | .or => "or"
  | .imp => "impl"
  | .not => "not"
  | .eq => "eq"
  | .all => "forall"
  | .ex => "exists"

theorem setName_injective : Function.Injective setName := by
  intro a b same
  cases a <;> (try (rename_i c; cases c)) <;> cases b <;> (try (rename_i c; cases c)) <;>
    simp_all [setName]

/-- The set profile encoded in the STTfa hub. -/
def sttfaSet : Encoding SetBase SetConst := ⟨"eta", setName, setName_injective⟩

/-- **The STTfa hub hosts the set profile.** -/
def sttfaSetHub : HubTheory sttfaSet :=
  sttfaHub sttfaSet rfl rfl fun s => by
    cases s <;> (try (rename_i c; cases c)) <;> simp [sttfaSet, setName]

/-! ## A conversion of the hub is an equality of the package -/

/-- `(λ x. suc x) zero`. -/
def sucRedex : HOL.Term SetConst [] numTy :=
  .app (.lam (.app (.const SetConst.suc) (.var .vz))) (.const SetConst.zero)

/-- `suc zero`. -/
def sucZero : HOL.Term SetConst [] numTy := .app (.const SetConst.suc) (.const SetConst.zero)

theorem sucRedex_conv :
    Conv TranslationTransport.STTfa.theory (sttfaSet.translate sucRedex) (sttfaSet.translate sucZero) :=
  Encoding.translate_conv
    (.rel _ _ ⟨.beta (.app (.const SetConst.suc) (.var .vz)) (.const SetConst.zero)⟩)

theorem sucRedex_read :
    setReading.term sucRedex = some (.app (.lam (.app (.const sucN) (.var 0))) (.const zeroN)) := rfl

theorem sucZero_read : setReading.term sucZero = some (.app (.const sucN) (.const zeroN)) := rfl

/-- **A conversion of the hub is an equality of the package**: the STTfa hub
converts the translations of `(λ x. suc x) zero` and `suc zero`, so the object
package equates their reads at the carrier of `num`. -/
theorem sucRedex_fiber_equal :
    Equal setReading.rules (setReading.objCtx [])
      (.app (.lam (.app (.const sucN) (.var 0))) (.const zeroN)) (.app (.const sucN) (.const zeroN))
      (setReading.carrierAt 0 numTy) :=
  fiber_equal_of_conv setReading_laws sttfaSetHub sucRedex_read sucZero_read sucRedex_conv

/-! ## The package equates more -/

/-- **The package equates more than the hub converts**: the reads of
`λ x. f x` and `f` at `num ⇒ num` are equal in the object package, while their
translations are not convertible in the STTfa hub. -/
theorem set_fiber_not_conservative :
    setReading.term (etaExpanded (Const := SetConst) numTy numTy) =
        some (.lam (.app (.var 1) (.var 0))) ∧
      setReading.term (etaContracted (Const := SetConst) numTy numTy) = some (.var 0) ∧
      Equal setReading.rules (setReading.objCtx [.arr numTy numTy]) (.lam (.app (.var 1) (.var 0)))
        (.var 0) (setReading.carrierAt 1 (.arr numTy numTy)) ∧
      ¬ Conv TranslationTransport.STTfa.theory
        (sttfaSet.translate (etaExpanded (Const := SetConst) numTy numTy))
        (sttfaSet.translate (etaContracted (Const := SetConst) numTy numTy)) :=
  fiber_not_conservative setReading_laws sttfaSetHub numTy numTy

/-! ## Beyond βη: the package's computations -/

/-- `add x zero`, in the context `x : num`. -/
def addXZero : HOL.Term SetConst [numTy] numTy := SetProfile.addT (.var .vz) SetProfile.zeroT

theorem addXZero_read :
    setReading.term addXZero = some (.app (.app (.const addN) (.var 0)) (.const zeroN)) := rfl

theorem varX_read : setReading.term (.var .vz : HOL.Term SetConst [numTy] numTy) = some (.var 0) :=
  rfl

/-- **The package equates the reads of `add x zero` and `x`**, by the root step
of `add` it computes with. -/
theorem addXZero_fiber_equal :
    Equal setReading.rules (setReading.objCtx [numTy])
      (.app (.app (.const addN) (.var 0)) (.const zeroN)) (.var 0) (setReading.carrierAt 1 numTy) :=
  setReading_laws.conversion_equal setReading_realizes
    (.rel _ _ ⟨rfl, rfl, .delta SetProfile.addZeroEquation (by simp [SetProfile.sourceEquations])
      HOL.Subst.id (fun _ => rfl)⟩) addXZero_read varX_read

/-- The constants of the set profile read in a model of numbers in which
`add n m` is `n + 1`. -/
def skewConst : {τ : HOL.Ty SetBase} → SetConst τ →
    HOL.Ty.denote.{0, 0} (fun _ : SetBase => ULift.{1} Nat) τ
  | _, .falsum => ULift.up False
  | _, .member => fun _ _ => ULift.up False
  | _, .empty => ULift.up 0
  | _, .union => fun x => x
  | _, .power => fun x => x
  | _, .separation => fun x _ => x
  | _, .replacement => fun x _ => x
  | _, .epsilon => fun _ => ULift.up 0
  | _, .universeOf => fun x => x
  | _, .zero => ULift.up 0
  | _, .suc => fun n => ULift.up (n.down + 1)
  | _, .add => fun n _ => ULift.up (n.down + 1)
  | _, .pow => fun _ x => x

/-- A Henkin model of the set profile's signature in which `add n m` is
`n + 1`. -/
def skewModel : HOL.HenkinModel.{0, 0, 0} SetBase SetConst where
  Carrier := fun _ => ULift.{1} Nat
  adm := fun _ _ => True
  base_mem := fun _ _ => trivial
  prop_mem := fun _ => trivial
  app_mem := fun _ _ => trivial
  constDen := skewConst
  const_mem := fun _ => trivial
  term_closed := fun _ _ _ => trivial

/-- **`add x zero` and `x` are not βη-convertible**: in the model where `add n m`
is `n + 1`, they differ. -/
theorem addXZero_not_betaEtaConv :
    ¬ HOL.EtaConversion.BetaEtaConv addXZero (.var .vz) := by
  intro converted
  let ρ : HOL.HenkinModel.Valuation skewModel [numTy] := fun v => match v with
    | .vz => ULift.up 0
  have same : (ULift.up 1 : ULift.{1} Nat) = ULift.up 0 :=
    HOL.EtaConversion.denote_of_betaEtaConv skewModel converted ρ
  exact absurd (congrArg ULift.down same) (by decide)

/-- **The package's equality on read terms is not βη-conversion**: it equates
the reads of `add x zero` and `x`, which are not βη-convertible. -/
theorem set_fiber_beyond_betaEta :
    Equal setReading.rules (setReading.objCtx [numTy])
        (.app (.app (.const addN) (.var 0)) (.const zeroN)) (.var 0) (setReading.carrierAt 1 numTy) ∧
      ¬ HOL.EtaConversion.BetaEtaConv addXZero (.var .vz) :=
  ⟨addXZero_fiber_equal, addXZero_not_betaEtaConv⟩

/-- **βη inside the read terms is equality of the package**, at the η-pair. -/
theorem set_readBetaEta_eta :
    Equal setReading.rules (setReading.objCtx [.arr numTy numTy]) (.lam (.app (.var 1) (.var 0)))
      (.var 0) (setReading.carrierAt 1 (.arr numTy numTy)) :=
  readBetaEta_equal setReading_laws
    (.rel _ _ ⟨rfl, rfl, Or.inr (.eta (.var .vz))⟩)
    (term_etaExpanded setReading numTy numTy) (term_etaContracted setReading numTy numTy)

/-- An η-step between read terms is equality of the package, at the η-pair. -/
theorem set_etaStep_equal :
    Equal setReading.rules (setReading.objCtx [.arr numTy numTy]) (.lam (.app (.var 1) (.var 0)))
      (.var 0) (setReading.carrierAt 1 (.arr numTy numTy)) :=
  etaStep_equal setReading_laws (.eta (.var .vz)) (term_etaExpanded setReading numTy numTy)
    (term_etaContracted setReading numTy numTy)

/-! ## A theorem in both -/

theorem sttfaSet_fresh (s : Symbol SetBase SetConst) :
    sttfaSet.name s ≠ "eta" ∧ sttfaSet.name s ≠ "etap" ∧ sttfaSet.name s ≠ "eps" := by
  cases s <;> (try (rename_i c; cases c)) <;> simp [sttfaSet, setName]

theorem sttfaSet_typeFresh (s : Symbol SetBase SetConst) : sttfaSet.name s ≠ "type" := by
  cases s <;> (try (rename_i c; cases c)) <;> simp [sttfaSet, setName]

/-- `suc x = suc x`, in the context `x : num`. -/
def sucRefl : HOL.Formula SetConst [numTy] :=
  .eq (.app (.const SetConst.suc) (.var .vz)) (.app (.const SetConst.suc) (.var .vz))

/-- `(∀ x. suc x = suc x) ⇒ suc zero = suc zero`. -/
def sucStatement : HOL.Formula SetConst [] :=
  .imp (.all sucRefl)
    (.eq (.app (.const SetConst.suc) (.const SetConst.zero))
      (.app (.const SetConst.suc) (.const SetConst.zero)))

/-- The proof: instantiate the hypothesis at `zero`. -/
def sucProof : HOL.ProofSyntaxModulo [] ([] : List (HOL.Formula SetConst [])) sucStatement :=
  .impI (.allE (Δ := [.all sucRefl]) (φ := sucRefl) (.const SetConst.zero) (.hyp ⟨0, by decide⟩))

theorem sucProof_articles : setReading.ArticlesRead [] sucProof :=
  .impI (.allE _ (.hyp _))

theorem sucProof_compiled :
    setReading.compile (n := 0) sucProof Fin.elim0 Fin.elim0 =
      some (.lam (.app (.var 0) (.const zeroN))) :=
  rfl

/-- **A theorem is inhabited in both**: the proof of
`(∀ x. suc x = suc x) ⇒ suc zero = suc zero` compiles to a term of `eps` of its
translation in the STTfa hub, and to a closed term of the decoding of its code
in the object package. -/
theorem sucProof_in_both :
    LambdaPiModulo (sttfaProofTheory sttfaSet) (sttfaSet.ctx [])
        (compile sttfaSet "eps" sucProof (.base []) Fin.elim0)
        (.app (.con "eps") (sttfaSet.translate sucStatement)) ∧
      ∃ code, setReading.term sucStatement = some code ∧
        Typed setReading.rules .nil (.lam (.app (.var 0) (.const zeroN)))
          (setReading.holdsOf code) := by
  refine ⟨sttfa_theorem_typed sttfaSet rfl rfl rfl rfl sttfaSet_fresh sttfaSet_typeFresh sucProof,
    ?_⟩
  obtain ⟨code, read, typed⟩ := setReading_laws.compile_typed (realizes_nil setReading)
    sucProof_articles (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) sucProof_compiled
  rw [SetProfile.subst_elim0] at typed
  exact ⟨code, read, typed⟩

/-! ## Normal proofs of the hub are proofs of the source -/

/-- The set profile has the names of the STTfa hub with proofs. -/
theorem sttfaSet_names : SttfaNames sttfaSet where
  el := rfl
  arrow := rfl
  imp := rfl
  all := rfl
  fresh := sttfaSet_fresh
  typeFresh := sttfaSet_typeFresh
  forallPFresh s := by cases s <;> (try (rename_i c; cases c)) <;> simp [sttfaSet, setName]
  pFresh s := by cases s <;> (try (rename_i c; cases c)) <;> simp [sttfaSet, setName]
  forallKFresh s := by cases s <;> (try (rename_i c; cases c)) <;> simp [sttfaSet, setName]

/-- `Falsum`. -/
def falsumF : HOL.Formula SetConst [] := .const SetConst.falsum

theorem falsumF_atom : Atom falsumF where
  normal := by
    rintro target ⟨step⟩
    cases step
  notImp _ _ same := by simp [falsumF] at same
  notAll _ same := by simp [falsumF] at same

/-- `⊢ Falsum ⇒ Falsum`. -/
def falsumIdentity :
    HOL.ProofSyntaxModulo [] ([] : List (HOL.Formula SetConst [])) (.imp falsumF falsumF) :=
  .impI (.hyp ⟨0, by decide⟩)

theorem falsumIdentity_normal :
    Mettapedia.Logic.Relation.IsNormal (Step (sttfaProofTheory sttfaSet))
      (compile sttfaSet "eps" falsumIdentity (.base []) Fin.elim0) := by
  rw [step_proofTheory]
  have domainNormal := epsNF_normal sttfaSet_names (.atom falsumF_atom)
  rw [sttfaSet.epsNF_atom _ falsumF_atom] at domainNormal
  have headed := TranslationTransport.STTfa.orthogonal.leftAlgebraic.headed
  intro target step
  rcases step.lam_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
  · exact RootStep.not_lam headed root
  · exact domainNormal _ inner
  · exact var_normal headed _ _ inner

/-- **The normal compiled identity of the set profile gives back a proof of
`Falsum ⇒ Falsum`**, by adequacy of the STTfa hub on the closed implicational
fragment. -/
theorem set_identity_adequate :
    Nonempty (HOL.ProofSyntaxModulo [] ([] : List (HOL.Formula SetConst []))
      (.imp falsumF falsumF)) :=
  sttfa_adequate_closed sttfaSet_names (.imp (.atom falsumF_atom) (.atom falsumF_atom))
    falsumIdentity_normal
    (sttfa_theorem_typed sttfaSet rfl rfl rfl rfl sttfaSet_fresh sttfaSet_typeFresh falsumIdentity)

/-- **The bare `and` of the set profile converts with no translation.** -/
theorem set_bareAnd_not_conv_translate {Γ : HOL.Ctx SetBase} {τ : HOL.Ty SetBase}
    (t : HOL.Term SetConst Γ τ) :
    ¬ Conv TranslationTransport.STTfa.theory (.con "and") (sttfaSet.translate t) :=
  bareAnd_not_conv_translate sttfaSet_names (by decide) t

/-- The normal type of the proofs of `∀ x. suc x = suc x`. -/
abbrev sucAllProofs : Mettapedia.GSLT.LanguageDef.LF.Term :=
  sttfaSet.epsNF sttfaSet_names.base (.all sucRefl : HOL.Formula SetConst [])

/-- **The normal form of the compiled `sucProof`**: `λ h. h zero`. -/
def sucProofNormal : Mettapedia.GSLT.LanguageDef.LF.Term :=
  .lam sucAllProofs (.app (.var 0) (.con "zero"))

theorem sucProofNormal_coded :
    Coded sttfaSet_names (HOL.Rename.id (Γ := [])) sucProofNormal :=
  .lamHyp (.pi (.eps _)) (.appObj (.const SetConst.zero) rfl (.hyp fun v => nomatch v))

theorem sucRefl_normal : HOL.BetaNormalization.Normal sucRefl := by
  rintro target ⟨step⟩
  cases step with
  | eqLeft _ inner =>
      cases inner with
      | appFun _ inner' => cases inner'
      | appArg _ inner' => cases inner'
  | eqRight _ inner =>
      cases inner with
      | appFun _ inner' => cases inner'
      | appArg _ inner' => cases inner'

theorem sucProofNormal_normal :
    Mettapedia.Logic.Relation.IsNormal (Step (sttfaProofTheory sttfaSet)) sucProofNormal := by
  rw [step_proofTheory]
  have headed := TranslationTransport.STTfa.orthogonal.leftAlgebraic.headed
  have allNormal : HOL.BetaNormalization.Normal (.all sucRefl : HOL.Formula SetConst []) :=
    fun target ⟨step⟩ => by
      cases step with
      | all inner => exact sucRefl_normal _ ⟨inner⟩
  intro target step
  rcases step.lam_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
  · exact RootStep.not_lam headed root
  · exact epsNF_normal_all sttfaSet_names _ allNormal _ inner
  · rcases inner.app_inv with root | ⟨_, inner', _⟩ | ⟨_, inner', _⟩
    · rcases root.headConst_or_beta headed with ⟨_, _, _, same⟩ | ⟨_, head⟩
      · cases same
      · simp [headConst] at head
    · exact var_normal headed _ _ inner'
    · exact sttfa_con_normal (by decide) _ inner'

theorem sucProofNormal_typed :
    LambdaPiModulo (sttfaProofTheory sttfaSet) [] sucProofNormal
      (.app (.con "eps") (sttfaSet.translate sucStatement)) := by
  have names := sttfaSet_names
  have declares := proofTheory_declares names
  have proofs := sttfaProofHub sttfaSet rfl rfl rfl rfl sttfaSet_fresh sttfaSet_typeFresh
  have objects := (scoped_objects sttfaSet []).extendObj names numTy
  have firstTyped := translateNF_typed_scoped names sucRefl objects
  have allTyped : LambdaPiModulo (sttfaProofTheory sttfaSet) [] sucAllProofs (.srt .type) :=
    .pi (elNF_typed names numTy) (proofs.proof_typed firstTyped) arrow_rule
  have closedAll : Closed sucAllProofs := sttfaSet.epsNF_closed names.base_closed _
  have headTyped : LambdaPiModulo (sttfaProofTheory sttfaSet) [sucAllProofs] (.var 0)
      sucAllProofs := .var (by rw [lookup_cons_zero, closedAll.lift])
  have zeroTyped : LambdaPiModulo (sttfaProofTheory sttfaSet) [sucAllProofs] (.con "zero")
      (Encoding.elNF names.base numTy) :=
    .conv (declares.sym_typed (.const .zero)) (conv_toProofTheory (El_conv_elNF names numTy))
      (elNF_typed names numTy)
  have applied := HasType.app headTyped zeroTyped
  have shape : Mettapedia.GSLT.LanguageDef.LFTyping.subst0 (.con "zero")
      (sttfaSet.epsNF names.base sucRefl) =
      sttfaSet.epsNF names.base (.eq (.app (.const SetConst.suc) (.const SetConst.zero))
        (.app (.const SetConst.suc) (.const SetConst.zero)) : HOL.Formula SetConst []) := rfl
  rw [shape] at applied
  have hypothesis := (scoped_objects sttfaSet []).extendHyp (domain := sucAllProofs)
    (p := .all sucRefl) rfl (.symm _ _ (conv_eps_epsNF names _))
  have conclusionTyped := translateNF_typed_scoped names
    (.eq (.app (.const SetConst.suc) (.const SetConst.zero))
      (.app (.const SetConst.suc) (.const SetConst.zero)) : HOL.Formula SetConst []) hypothesis
  have lamTyped := HasType.lam allTyped (proofs.proof_typed conclusionTyped) arrow_rule applied
  have converted := conv_eps_epsNF names sucStatement
  rw [show sucStatement = .imp (.all sucRefl) (.eq (.app (.const SetConst.suc) (.const SetConst.zero))
      (.app (.const SetConst.suc) (.const SetConst.zero))) from rfl,
    sttfaSet.epsNF_imp names.base_closed] at converted
  exact .conv lamTyped (conv_toProofTheory (.symm _ _ converted))
    (proofs.proof_typed (declares.translate_typed (Γ := []) _))

/-- **The normal form of the compiled `sucProof` gives back a proof** of
`(∀ x. suc x = suc x) ⇒ suc zero = suc zero`, by adequacy of the STTfa hub with
universal quantification, modulo the coding of witnesses. -/
theorem set_sucProof_adequate :
    Nonempty (HOL.ProofSyntaxModulo [] ([] : List (HOL.Formula SetConst [])) sucStatement) :=
  sttfa_adequate_coded sttfaSet_names (Δ := []) (fun _ member => absurd member List.not_mem_nil)
    rfl sucProofNormal_coded sucProofNormal_normal sucProofNormal_typed

#print axioms setName_injective
#print axioms sucRedex_fiber_equal
#print axioms set_fiber_not_conservative
#print axioms sucProof_in_both
#print axioms set_fiber_beyond_betaEta
#print axioms set_readBetaEta_eta
#print axioms set_identity_adequate
#print axioms set_bareAnd_not_conv_translate
#print axioms set_sucProof_adequate

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.DeduktiHubFiber
