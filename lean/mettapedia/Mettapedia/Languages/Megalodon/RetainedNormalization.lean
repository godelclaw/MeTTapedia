import Mettapedia.Languages.Megalodon.HenkinErasureInversion
import Mettapedia.Languages.Megalodon.HenkinTermSubstitution
import Mettapedia.Languages.Megalodon.HenkinTermStrengthening
import Mettapedia.Logic.HOL.ContextualTrinity

/-!
# Retained HOL evidence for Megalodon's beta/eta normalization

The native monomorphic normalization pass is elaborated into the existing
retained HOL proof calculus. The result contains an actual typed target and
an equality proof built from beta, eta, congruence and transitivity. Native
erasure is a separate comparison, including the test that an eta-contracted
function does not contain its removed variable.

The additional intrinsic HOL connectives have no native constructor image;
they are left unchanged by this pass. All correspondence claims require a
successful native erasure. Definition unfolding and prefix polymorphism are
separate from this beta/eta pass.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.Megalodon.RetainedNormalization

open MathdataKernel HenkinTermInterpretation
open Mettapedia.Logic.HOL
open ContextualTrinity

variable {environment : Environment} {Γ : Ctx Base} {σ τ : Ty Base}

/-- One computed pass and its ordinary source equality proof. -/
structure Pass (source : Term (Constant environment) Γ τ) where
  target : Term (Constant environment) Γ τ
  stable : Bool
  proof : ProofSyntax (Constant environment) [] (.eq source target)

def unchanged (source : Term (Constant environment) Γ τ) (stable : Bool) : Pass source :=
  ⟨source, stable, .eqRefl source⟩

def betaHead (function : Term (Constant environment) Γ (σ ⇒ τ))
    (argument : Term (Constant environment) Γ σ) (stable : Bool) : Pass (.app function argument) :=
  match function with
  | .lam body => ⟨instantiate argument body, false, .beta argument body⟩
  | other => unchanged (.app other argument) stable

def etaHead (body : Term (Constant environment) (σ :: Γ) τ) (stable : Bool) : Pass (.lam body) :=
  match body with
  | .app function (.var .vz) =>
      match lowered : rename? PartialRename.drop function with
      | none => unchanged (.lam (.app function (.var .vz))) stable
      | some function' =>
          ⟨function', false, ProofSyntax.castIndices rfl
            (congrArg (fun f => Term.eq (.lam (.app f (.var .vz))) function')
              (weaken_of_rename?_drop lowered)) (.eta function')⟩
  | other => unchanged (.lam other) stable

private theorem instantiateLeft (left right : Formula (Constant environment) Γ) :
    instantiate left (.imp (.var .vz) (weaken right)) = .imp left right := by
  change Term.imp left (instantiate left (weaken right)) = _
  rw [instantiate_weaken]

private theorem instantiateRight (left right : Formula (Constant environment) Γ) :
    instantiate right (.imp (weaken left) (.var .vz)) = .imp left right := by
  change Term.imp (instantiate right (weaken left)) right = _
  rw [instantiate_weaken]

private def implicationCongr {left left' right right' : Formula (Constant environment) Γ}
    (first : ProofSyntax (Constant environment) [] (.eq left left'))
    (second : ProofSyntax (Constant environment) [] (.eq right right')) :
    ProofSyntax (Constant environment) [] (.eq (.imp left right) (.imp left' right')) :=
  .eqTrans
    (castEq (instantiateLeft left right) (instantiateLeft left' right)
      (holeCongr (.imp (.var .vz) (weaken right)) first))
    (castEq (instantiateRight left' right) (instantiateRight left' right')
      (holeCongr (.imp (weaken left') (.var .vz)) second))

private def nativeBetaHead (function argument : Tm) (stable : Bool) : Tm × Bool :=
  match function with
  | .lam _ body => (Tm.instantiate argument body, false)
  | _ => (.app function argument, stable)

private theorem betaHead_erases
    (function : Term (Constant environment) Γ (σ ⇒ τ))
    (argument : Term (Constant environment) Γ σ) (stable : Bool) {rawFunction rawArgument : Tm}
    (functionErased : erase function = some rawFunction) (argumentErased : erase argument = some rawArgument) :
    erase (betaHead function argument stable).target = some (nativeBetaHead rawFunction rawArgument stable).1 ∧
      (betaHead function argument stable).stable = (nativeBetaHead rawFunction rawArgument stable).2 := by
  cases function with
  | var index =>
      cases Option.some.inj functionErased
      simp [betaHead, unchanged, erase, argumentErased, nativeBetaHead]
  | const constant =>
      cases Option.some.inj functionErased
      cases constant <;> simp [betaHead, unchanged, erase, argumentErased, nativeBetaHead, Constant.erase]
  | app function argument' =>
      cases hf : erase function <;> cases ha : erase argument' <;>
        simp [erase, hf, ha] at functionErased
      subst rawFunction
      simp [betaHead, unchanged, erase, hf, ha, argumentErased, nativeBetaHead]
  | lam body =>
      cases hb : erase body <;> simp [erase, hb] at functionErased
      obtain ⟨rfl, rfl⟩ := functionErased
      simp only [betaHead, nativeBetaHead, and_true]
      rw [erase_instantiate argument body argumentErased, hb]
      rfl

private def nativeEtaHead (type : Tp) (body : Tm) (stable : Bool) : Tm × Bool :=
  match body with
  | .app function (.db 0) =>
      match Tm.dropAt? 0 function with
      | some lowered => (lowered, false)
      | none => (.lam type body, stable)
  | _ => (.lam type body, stable)

private theorem etaHead_newest_erases
    (function : Term (Constant environment) (σ :: Γ) (σ ⇒ τ))
    (stable : Bool) {rawFunction : Tm} (erased : erase function = some rawFunction) :
    erase (etaHead (.app function (.var .vz)) stable).target =
        some (nativeEtaHead (reifyType σ) (.app rawFunction (.db 0)) stable).1 ∧
      (etaHead (.app function (.var .vz)) stable).stable =
        (nativeEtaHead (reifyType σ) (.app rawFunction (.db 0)) stable).2 := by
  have comparison := erase_rename?_drop function
  rw [erased, Option.bind_some] at comparison
  cases lowered : rename? PartialRename.drop function with
  | none =>
      rw [lowered, Option.bind_none] at comparison
      simp only [etaHead]
      split
      · simp [nativeEtaHead, ← comparison, unchanged, erase, erased, variableIndex]
      · rename_i result computed
        have impossible := computed.symm.trans lowered
        cases impossible
  | some target =>
      have weakened : weaken target = function := weaken_of_rename?_drop lowered
      have targetErased := erase_weaken (σ := σ) target
      rw [weakened, erased] at targetErased
      cases ht : erase target with
      | none => simp [ht] at targetErased
      | some rawTarget =>
          rw [lowered, Option.bind_some, ht] at comparison
          simp only [etaHead]
          split
          · rename_i computed
            have impossible := computed.symm.trans lowered
            cases impossible
          · rename_i result computed
            have equal := Option.some.inj (computed.symm.trans lowered)
            subst result
            simp [nativeEtaHead, ← comparison, ht]

private theorem nativeEtaHead_other_argument (type : Tp) (function argument : Tm) (stable : Bool)
    (different : argument ≠ .db 0) :
    nativeEtaHead type (.app function argument) stable = (.lam type (.app function argument), stable) := by
  cases argument <;> simp only [nativeEtaHead]
  rename_i index
  cases index with
  | zero => exact False.elim (different rfl)
  | succ index => rfl

private theorem erase_lam_app {resultType : Ty Base} (function : Term (Constant environment) (σ :: Γ) (τ ⇒ resultType))
    (argument : Term (Constant environment) (σ :: Γ) τ) {rawFunction rawArgument : Tm}
    (hf : erase function = some rawFunction) (ha : erase argument = some rawArgument) :
    erase (.lam (.app function argument)) = some (.lam (reifyType σ) (.app rawFunction rawArgument)) := by
  change ((erase function).bind (fun f => (erase argument).bind (fun a => some (Tm.app f a)))).bind
    (fun b => some (Tm.lam (reifyType σ) b)) = _
  rw [hf, ha]
  rfl

private theorem etaHead_erases (body : Term (Constant environment) (σ :: Γ) τ)
    (stable : Bool) {rawBody : Tm} (bodyErased : erase body = some rawBody) :
    erase (etaHead body stable).target = some (nativeEtaHead (reifyType σ) rawBody stable).1 ∧
      (etaHead body stable).stable = (nativeEtaHead (reifyType σ) rawBody stable).2 := by
  cases body with
  | var index =>
      cases Option.some.inj bodyErased
      simp [etaHead, unchanged, erase, nativeEtaHead]
  | const constant =>
      cases Option.some.inj bodyErased
      cases constant <;> simp [etaHead, unchanged, erase, nativeEtaHead, Constant.erase]
  | lam body =>
      cases hb : erase body <;> simp [erase, hb] at bodyErased
      obtain ⟨rfl, rfl⟩ := bodyErased
      simp [etaHead, unchanged, erase, hb, nativeEtaHead]
  | imp left right =>
      cases hl : erase left <;> cases hr : erase right <;> simp [erase, hl, hr] at bodyErased
      subst rawBody
      simp [etaHead, unchanged, erase, hl, hr, nativeEtaHead]
  | all body =>
      cases hb : erase body <;> simp [erase, hb] at bodyErased
      obtain ⟨rfl, rfl⟩ := bodyErased
      simp [etaHead, unchanged, erase, hb, nativeEtaHead]
  | top | bot | and | or | not | eq | ex => simp [erase] at bodyErased
  | app function argument =>
      cases hf : erase function <;> cases ha : erase argument <;> simp [erase, hf, ha] at bodyErased
      subst rawBody
      rename_i rawFunction rawArgument
      cases argument with
      | var index =>
          cases index with
          | vz =>
              cases Option.some.inj ha
              exact etaHead_newest_erases function stable hf
          | vs index =>
              cases Option.some.inj ha
              simp [etaHead, unchanged, erase, hf, nativeEtaHead, variableIndex]
      | const constant =>
          cases Option.some.inj ha
          cases constant <;> simp [etaHead, unchanged, erase, hf, nativeEtaHead, Constant.erase]
      | app function' argument' =>
          have notZero : rawArgument ≠ .db 0 := by
            intro same
            rw [same] at ha
            obtain ⟨index, impossible, _⟩ := erase_db_inv ha
            cases impossible
          rw [nativeEtaHead_other_argument _ _ _ _ notZero]
          exact ⟨erase_lam_app function _ hf ha, rfl⟩
      | lam body | all body =>
          have notZero : rawArgument ≠ .db 0 := by
            intro same
            rw [same] at ha
            obtain ⟨index, impossible, _⟩ := erase_db_inv ha
            cases impossible
          rw [nativeEtaHead_other_argument _ _ _ _ notZero]
          exact ⟨erase_lam_app function _ hf ha, rfl⟩
      | imp left right =>
          have notZero : rawArgument ≠ .db 0 := by
            intro same
            rw [same] at ha
            obtain ⟨index, impossible, _⟩ := erase_db_inv ha
            cases impossible
          rw [nativeEtaHead_other_argument _ _ _ _ notZero]
          exact ⟨erase_lam_app function _ hf ha, rfl⟩
      | top | bot | and | or | not | eq | ex => simp [erase] at ha

/-- Structural recursion computes both the native pass and its proof. -/
def normalizeOne : {Γ : Ctx Base} → {τ : Ty Base} →
    (source : Term (Constant environment) Γ τ) → Pass source
  | _, _, .app function argument =>
      let first := normalizeOne function
      let second := normalizeOne argument
      let head := betaHead first.target second.target (first.stable && second.stable)
      ⟨head.target, head.stable,
        .eqTrans (.eqApp argument first.proof)
          (.eqTrans (.eqAppArg first.target second.proof) head.proof)⟩
  | _, _, .lam body =>
      let inner := normalizeOne body
      let head := etaHead inner.target inner.stable
      ⟨head.target, head.stable, .eqTrans (.eqLam inner.proof) head.proof⟩
  | _, _, .imp left right =>
      let first := normalizeOne left
      let second := normalizeOne right
      ⟨.imp first.target second.target, first.stable && second.stable,
        implicationCongr first.proof second.proof⟩
  | _, _, .all body =>
      let inner := normalizeOne body
      ⟨.all inner.target, inner.stable, allCongr (Δ := []) inner.proof⟩
  | _, _, source => unchanged source true

private theorem native_app_one (function argument : Tm) :
    Tm.normalizeOne (.app function argument) = nativeBetaHead
      (Tm.normalizeOne function).1 (Tm.normalizeOne argument).1
      ((Tm.normalizeOne function).2 && (Tm.normalizeOne argument).2) := by
  cases hf : Tm.normalizeOne function with
  | mk f fs =>
      cases ha : Tm.normalizeOne argument with
      | mk a ast =>
          cases f <;> simp [Tm.normalizeOne, hf, ha, nativeBetaHead]

private theorem native_lam_one (type : Tp) (body : Tm) :
    Tm.normalizeOne (.lam type body) = nativeEtaHead type
      (Tm.normalizeOne body).1 (Tm.normalizeOne body).2 := by
  cases hb : Tm.normalizeOne body with
  | mk b stable =>
      cases b <;> simp only [Tm.normalizeOne, hb, nativeEtaHead]
      rename_i function argument
      cases argument <;> rfl

/-- The independent native algorithm and retained pass have identical raw
outputs and stability flags on the supported intrinsic syntax. -/
theorem normalizeOne_erases (source : Term (Constant environment) Γ τ)
    {raw : Tm} (erased : erase source = some raw) :
    erase (normalizeOne source).target = some (Tm.normalizeOne raw).1 ∧
      (normalizeOne source).stable = (Tm.normalizeOne raw).2 := by
  induction source generalizing raw with
  | var index =>
      cases Option.some.inj erased
      simp [normalizeOne, unchanged, erase, Tm.normalizeOne]
  | const constant =>
      cases Option.some.inj erased
      cases constant <;> simp [normalizeOne, unchanged, erase, Tm.normalizeOne, Constant.erase]
  | app function argument ihf iha =>
      cases hf : erase function <;> cases ha : erase argument <;> simp [erase, hf, ha] at erased
      subst raw
      obtain ⟨functionErased, functionStable⟩ := ihf hf
      obtain ⟨argumentErased, argumentStable⟩ := iha ha
      have head := betaHead_erases (normalizeOne function).target (normalizeOne argument).target
        ((normalizeOne function).stable && (normalizeOne argument).stable) functionErased argumentErased
      rw [functionStable, argumentStable] at head
      simpa only [normalizeOne, native_app_one, functionStable, argumentStable] using head
  | lam body ih =>
      cases hb : erase body <;> simp [erase, hb] at erased
      obtain ⟨rfl, rfl⟩ := erased
      obtain ⟨bodyErased, bodyStable⟩ := ih hb
      have head := etaHead_erases (normalizeOne body).target (normalizeOne body).stable bodyErased
      rw [bodyStable] at head
      simpa only [normalizeOne, native_lam_one, bodyStable] using head
  | imp left right ihl ihr =>
      cases hl : erase left <;> cases hr : erase right <;> simp [erase, hl, hr] at erased
      subst raw
      obtain ⟨leftErased, leftStable⟩ := ihl hl
      obtain ⟨rightErased, rightStable⟩ := ihr hr
      simp [normalizeOne, erase, leftErased, rightErased, leftStable, rightStable, Tm.normalizeOne]
  | all body ih =>
      cases hb : erase body <;> simp [erase, hb] at erased
      obtain ⟨rfl, rfl⟩ := erased
      obtain ⟨bodyErased, bodyStable⟩ := ih hb
      simp [normalizeOne, erase, bodyErased, bodyStable, Tm.normalizeOne]
  | top | bot | and | or | not | eq | ex => simp [erase] at erased

/-- A finite successful run carries its cumulative equality proof. -/
def normalize : Nat → {Γ : Ctx Base} → {τ : Ty Base} →
    (source : Term (Constant environment) Γ τ) → Option (Pass source)
  | 0, _, _, source =>
      let result := normalizeOne source
      if result.stable then some result else none
  | fuel + 1, _, _, source =>
      let result := normalizeOne source
      if result.stable then some result
      else do
        let rest ← normalize fuel result.target
        return ⟨rest.target, rest.stable, .eqTrans result.proof rest.proof⟩

/-- Exact finite-fuel agreement includes resource failure. -/
theorem normalize_erases (fuel : Nat) (source : Term (Constant environment) Γ τ)
    {raw : Tm} (erased : erase source = some raw) :
    (normalize fuel source).bind (fun result => erase result.target) = Tm.normalize fuel raw := by
  induction fuel generalizing source raw with
  | zero =>
      obtain ⟨targetErased, stable⟩ := normalizeOne_erases source erased
      simp only [normalize, Tm.normalize]
      rw [← stable]
      split <;> simp_all
  | succ fuel ih =>
      obtain ⟨targetErased, stable⟩ := normalizeOne_erases source erased
      have rest := ih (normalizeOne source).target targetErased
      simp only [normalize, Tm.normalize]
      rw [← stable]
      split
      · simp_all
      · cases result : normalize fuel (normalizeOne source).target <;> simp_all

/-- Successful native normalization computes a retained proof of its exact
result. If the checked result already equals the input, reflexivity supplies
the equality without rebuilding congruences through the whole input. This
preserves endpoints, not the identity of normalization histories. No source
proof is recovered by choosing from mere derivability. -/
def readback (fuel : Nat) (source : Term (Constant environment) Γ τ)
    {raw target : Tm} (erased : erase source = some raw)
    (accepted : Tm.normalize fuel raw = some target) :
    {result : Pass source // erase result.target = some target} := by
  if same : raw = target then
    exact ⟨unchanged source true, erased.trans (congrArg some same)⟩
  else
    have correspondence := normalize_erases fuel source erased
    rw [accepted] at correspondence
    cases computed : normalize fuel source with
    | none => simp [computed] at correspondence
    | some result => exact ⟨result, by simpa [computed] using correspondence⟩

namespace Controls

abbrev NoConstants := Constant ({} : Environment)

def betaSource : Term NoConstants [] .prop :=
  .app (.lam (.var .vz)) (.app (.lam (.var .vz)) (.all (.imp (.var .vz) (.var .vz))))

def betaTarget : Term NoConstants [] .prop := .all (.imp (.var .vz) (.var .vz))

def etaSource : Term NoConstants [.arr .prop .prop] (.arr .prop .prop) :=
  .lam (.app (.var (.vs .vz)) (.var .vz))

def etaRaw : Tm := .lam .prop (.app (.db 1) (.db 0))

theorem eta_erased : erase etaSource = some etaRaw := rfl

theorem eta_native_accepted : Tm.normalize 1 etaRaw = some (.db 0) := rfl

def etaReadback := readback 1 etaSource eta_erased eta_native_accepted

theorem eta_readback_exact : erase etaReadback.val.target = some (.db 0) := etaReadback.property

theorem eta_zero_fuel : Tm.normalize 0 etaRaw = none := rfl

theorem retained_zero_fuel : (normalize 0 etaSource).isNone = true := rfl

theorem forged_eta_result_refused : Tm.normalize 1 etaRaw ≠ some (.db 1) := by decide

/-- The candidate function uses the variable being removed, below a binder. -/
def capturedFunction : Term NoConstants [.prop] (.arr .prop .prop) := .lam (.var (.vs .vz))

theorem captured_eta_refused :
    (etaHead (.app capturedFunction (.var .vz)) true).target =
      .lam (.app capturedFunction (.var .vz)) := rfl

theorem captured_native_eta_refused : Tm.dropAt? 0 (.lam .prop (.db 1)) = none := rfl

theorem nested_beta_target :
    (normalize 1 betaSource).map (fun result => erase result.target) = some (erase betaTarget) := rfl

end Controls

end Mettapedia.Languages.Megalodon.RetainedNormalization
