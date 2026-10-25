import Mettapedia.GSLT.Dedukti.HOLHubAdequacyForall
import Mettapedia.GSLT.Dedukti.TypePreservation

/-!
# Type preservation in the typed STTfa hub

`TypePreservation.typePreservation` reduces type preservation of a confluent
theory with headed rules and closed definitions and declared types to three
obligations: its declared types are types, its definitions have their declared
types, and its rules keep the type of their left sides.  This module discharges
them for the typed STTfa hub of `HOLHubProofs`, whose declarations are those of
Logipedia's theory file (`theories/sttfa/sttfa.dk` at commit `0bcb193`) together
with the encoding of a HOL signature.

* **Declared types are types** (`formedSignature`), in the empty context.
* **Definitions** are vacuous: the hub defines no constant (`typedBodies`).
* **Rules keep types** (`rulesPreserveTypes`).  By typing inversion on each
  instance of a left side:
  - `eta ↪ λ t. etap (p t)` keeps `type → Type`;
  - `etap (p (arrow l r)) ↪ eta l → eta r` and `etap (forallK f) ↪ Π x. etap (f x)`
    keep `Type`, with `l r : type` and `f : type → ptype`;
  - `eps (forall t f) ↪ Π x : eta t. eps (f x)`, `eps (impl l r) ↪ eps l → eps r`
    and `eps (forallP f) ↪ Π x : type. eps (f x)` keep `Type`, with
    `f : eta t → eta bool`, `l r : eta bool` and `f : type → eta bool`.
* **Type preservation** (`sttfa_typePreservation`): every reduct of a term typed
  in a well-formed context has its type.

**Controls.**  The compiled proof `λ h : eps (tr (∀ x. pred x)). h point` reduces
to its normal form, and type preservation types the normal form at the type of
the proofs of `(∀ x. pred x) ⇒ pred point` (`predInstance_typed_by_preservation`).
In the earlier typed hub, which declared `eps` and nothing else of the theory
file, `eta bool` is a type whose one-step reduct has no type
(`formerHub_not_typePreserving`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.HOLHub

open Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 lookupBody)
open Mettapedia.Logic.Relation (Confluent IsNormal)
open Mettapedia.Logic.HOL (Ty Ctx Var Term Formula)
open TranslationTransport

universe u v

theorem kind_rule : (⟨.type, .kind, .kind⟩ : LFProfile.ProductRule) ∈ LFProfile.standardLF.products := by
  decide

section Declarations

variable {Base : Type u} {Const : Ty Base → Type v}
variable {e : Encoding Base Const} (names : SttfaNames e)
include names

theorem constType_type : (sttfaProofTheory e).constType "type" = some (.srt .type) :=
  e.typedTheory_codes STTfa.theory (sttfaProofTypes e) names.typeFresh

theorem constType_eta :
    (sttfaProofTheory e).constType "eta" = some (.pi (.con "type") (.srt .type)) := by
  have found := e.typedTheory_el STTfa.theory (codes := "type") (sttfaProofTypes e)
    (fun s same => (names.fresh s).1 (same.trans names.el)) (by rw [names.el]; decide)
  rwa [names.el] at found

theorem constType_logipedia {name : String} (unnamed : ∀ s, e.name s ≠ name)
    (notCodes : name ≠ "type") (notEta : name ≠ "eta") :
    (sttfaProofTheory e).constType name = sttfaProofTypes e name :=
  sttfaProofTheory_constType_extra e unnamed notCodes (by rw [names.el]; exact notEta)

theorem constType_eps :
    (sttfaProofTheory e).constType "eps" =
      some (.pi (.app (.con "eta") (.con (e.name .bool))) (.srt .type)) := by
  rw [constType_logipedia names (fun s => (names.fresh s).2.2) (by decide) (by decide)]
  simp [sttfaProofTypes, Encoding.El, Encoding.sym, names.el]

theorem constType_ptype : (sttfaProofTheory e).constType "ptype" = some (.srt .type) := by
  rw [constType_logipedia names (fun s => (names.pFresh s).2) (by decide) (by decide)]
  simp [sttfaProofTypes]

theorem constType_forallK :
    (sttfaProofTheory e).constType "forallK" =
      some (.pi (.pi (.con "type") (.con "ptype")) (.con "ptype")) := by
  rw [constType_logipedia names names.forallKFresh (by decide) (by decide)]
  simp [sttfaProofTypes]

theorem constType_forallP :
    (sttfaProofTheory e).constType "forallP" =
      some (.pi (.pi (.con "type") (.app (.con "eta") (.con (e.name .bool))))
        (.app (.con "eta") (.con (e.name .bool)))) := by
  rw [constType_logipedia names names.forallPFresh (by decide) (by decide)]
  simp [sttfaProofTypes, Encoding.El, Encoding.sym, names.el]

omit names in
theorem constType_symbol (s : Symbol Base Const) :
    (sttfaProofTheory e).constType (e.name s) = some (e.declaredType (.con "type") s) :=
  e.typedTheory_symbol STTfa.theory "type" (sttfaProofTypes e) s

end Declarations

/-! ## Declared types are types -/

section Signature

variable {Base : Type u} {Const : Ty Base → Type v}
variable {e : Encoding Base Const} (names : SttfaNames e)
include names

theorem codes_typed {context : LFTyping.Ctx} :
    LambdaPiModulo (sttfaProofTheory e) context (.con "type") (.srt .type) :=
  .con (constType_type names)

omit names in
theorem var_codes_typed {context : LFTyping.Ctx} :
    LambdaPiModulo (sttfaProofTheory e) (.con "type" :: context) (.var 0) (.con "type") :=
  .var (lookup_cons_zero _ _)

/-- The code of a function type is a code when its two sides are. -/
theorem arr_typed {context : LFTyping.Ctx} {a b : LF.Term}
    (aTyped : LambdaPiModulo (sttfaProofTheory e) context a (.con "type"))
    (bTyped : LambdaPiModulo (sttfaProofTheory e) context b (.con "type")) :
    LambdaPiModulo (sttfaProofTheory e) context (e.arr a b) (.con "type") :=
  .app (.app ((proofTheory_declares names).sym_typed .arrow) aTyped) bTyped

theorem declaredType_formed (s : Symbol Base Const) :
    ∃ sort, LambdaPiModulo (sttfaProofTheory e) [] (e.declaredType (.con "type") s) (.srt sort) := by
  have declares := proofTheory_declares names
  have boolTyped : ∀ {context : LFTyping.Ctx},
      LambdaPiModulo (sttfaProofTheory e) context (e.sym .bool) (.con "type") :=
    declares.sym_typed .bool
  cases s with
  | sort b => exact ⟨.type, codes_typed names⟩
  | const c => exact ⟨.type, declares.El_code_typed _⟩
  | bool => exact ⟨.type, codes_typed names⟩
  | arrow => exact ⟨.type, .pi (codes_typed names) (.pi (codes_typed names) (codes_typed names)
      arrow_rule) arrow_rule⟩
  | top => exact ⟨.type, declares.El_code_typed _⟩
  | bot => exact ⟨.type, declares.El_code_typed _⟩
  | and => exact ⟨.type, declares.El_code_typed _⟩
  | or => exact ⟨.type, declares.El_code_typed _⟩
  | imp => exact ⟨.type, declares.El_code_typed _⟩
  | not => exact ⟨.type, declares.El_code_typed _⟩
  | eq =>
      exact ⟨.type, .pi (codes_typed names) (declares.El_typed (arr_typed names
        var_codes_typed (arr_typed names var_codes_typed boolTyped))) arrow_rule⟩
  | all =>
      exact ⟨.type, .pi (codes_typed names) (declares.El_typed (arr_typed names
        (arr_typed names var_codes_typed boolTyped) boolTyped)) arrow_rule⟩
  | ex =>
      exact ⟨.type, .pi (codes_typed names) (declares.El_typed (arr_typed names
        (arr_typed names var_codes_typed boolTyped) boolTyped)) arrow_rule⟩

/-- **Every declared type of the typed hub is a type.** -/
theorem formedSignature : (sttfaProofTheory e).FormedSignature LFProfile.standardLF := by
  have declares := proofTheory_declares names
  have boolDecoding : ∀ {context : LFTyping.Ctx}, LambdaPiModulo (sttfaProofTheory e) context
      (.app (.con "eta") (.con (e.name .bool))) (.srt .type) := by
    intro context
    have typed := declares.El_typed (Γ := context) (declares.sym_typed .bool)
    simpa [Encoding.El, Encoding.sym, names.el] using typed
  intro name type declared
  simp only [sttfaProofTheory, Encoding.typedTheory] at declared
  split_ifs at declared with named
  · cases declared
    exact declaredType_formed names _
  · cases declared
    exact ⟨.kind, .sort rfl⟩
  · cases declared
    exact ⟨.kind, .pi (codes_typed names) (.sort rfl) kind_rule⟩
  · simp only [sttfaProofTypes] at declared
    split_ifs at declared <;> cases declared <;>
      try simp only [Encoding.El, Encoding.sym, names.el]
    · exact ⟨.kind, .pi boolDecoding (.sort rfl) kind_rule⟩
    · exact ⟨.kind, .sort rfl⟩
    · exact ⟨.type, .pi (codes_typed names) (.con (constType_ptype names)) arrow_rule⟩
    · exact ⟨.kind, .pi (.con (constType_ptype names)) (.sort rfl) kind_rule⟩
    · exact ⟨.type, .pi (.pi (codes_typed names) (.con (constType_ptype names)) arrow_rule)
        (.con (constType_ptype names)) arrow_rule⟩
    · exact ⟨.type, .pi (.pi (codes_typed names) boolDecoding arrow_rule) boolDecoding arrow_rule⟩

end Signature

theorem typedBodies {Base : Type u} {Const : Ty Base → Type v} (e : Encoding Base Const) :
    (sttfaProofTheory e).TypedBodies LFProfile.standardLF := by
  intro name body type defined _
  simp [sttfaProofTheory, Encoding.typedTheory, STTfa.theory, Theory.ofSig, lookupBody] at defined

/-! ## Rules keep types -/

section Rules

variable {Base : Type u} {Const : Ty Base → Type v}
variable {e : Encoding Base Const} (names : SttfaNames e)
include names

omit names in
/-- Retyping along a conversion of the type in the hub with proofs. -/
theorem retype {context : LFTyping.Ctx} {M A B : LF.Term}
    (typed : LambdaPiModulo (sttfaProofTheory e) context M A)
    (converted : Conv STTfa.theory A B) {sort : LF.Srt}
    (formed : LambdaPiModulo (sttfaProofTheory e) context B (.srt sort)) :
    LambdaPiModulo (sttfaProofTheory e) context M B :=
  .conv typed (conv_toProofTheory converted) formed

/-- A type that converts with `Type` is typed at a sort. -/
theorem formed_of_conv_type {context : LFTyping.Ctx} {M A : LF.Term}
    (wellFormed : WellFormedCtx LFProfile.standardLF (sttfaProofTheory e) context)
    (typed : LambdaPiModulo (sttfaProofTheory e) context M A)
    (converted : Conv STTfa.theory (.srt .type) A) :
    ∃ sort, LambdaPiModulo (sttfaProofTheory e) context A (.srt sort) := by
  rcases HasType.correct (sttfaProofTheory_closedBodies e) (sttfaProofTheory_closedTypes e)
      (formedSignature names) wellFormed typed with ⟨sort, rfl, top⟩ | formed
  · cases sort with
    | type => cases top
    | kind =>
        have same := Conv.srt_injective STTfa.confluent STTfa.orthogonal.leftAlgebraic.headed
          converted
        cases same
  · exact formed

/-- A type that converts with a product is typed at a sort. -/
theorem formed_of_conv_pi {context : LFTyping.Ctx} {M A domain body : LF.Term}
    (wellFormed : WellFormedCtx LFProfile.standardLF (sttfaProofTheory e) context)
    (typed : LambdaPiModulo (sttfaProofTheory e) context M A)
    (converted : Conv STTfa.theory (.pi domain body) A) :
    ∃ sort, LambdaPiModulo (sttfaProofTheory e) context A (.srt sort) := by
  rcases HasType.correct (sttfaProofTheory_closedBodies e) (sttfaProofTheory_closedTypes e)
      (formedSignature names) wellFormed typed with ⟨sort, rfl, _⟩ | formed
  · exact absurd (.symm _ _ converted)
      (Conv.srt_ne_pi STTfa.confluent STTfa.orthogonal.leftAlgebraic.headed)
  · exact formed

omit names in
/-- **Inversion at a constant applied to an argument**, whose declared type
converts with a product. -/
theorem app_con_inv {context : LFTyping.Ctx} {name : String} {argument A declared domain body : LF.Term}
    (found : (sttfaProofTheory e).constType name = some declared)
    (shape : Conv STTfa.theory declared (.pi domain body))
    (typed : LambdaPiModulo (sttfaProofTheory e) context (.app (.con name) argument) A) :
    (∃ D, LambdaPiModulo (sttfaProofTheory e) context argument D ∧ Conv STTfa.theory D domain) ∧
      Conv STTfa.theory (subst0 argument body) A := by
  obtain ⟨D, B, functionTyped, argumentTyped, convA⟩ := typed.app_inv
  obtain ⟨X, foundX, convX⟩ := functionTyped.con_inv
  rw [found] at foundX
  cases foundX
  obtain ⟨convDomain, convBody⟩ := Conv.pi_injective STTfa.confluent
    STTfa.orthogonal.leftAlgebraic.headed
    (.trans _ _ _ (.symm _ _ shape) (conv_proofTheory convX))
  exact ⟨⟨D, argumentTyped, .symm _ _ convDomain⟩,
    .trans _ _ _ (Conv.subst sttfa_closedBodies convBody 0 argument) (conv_proofTheory convA)⟩

omit names in
/-- Weakening by one entry. -/
theorem weaken_one {context : LFTyping.Ctx} {M A : LF.Term} (entry : LF.Term)
    (typed : LambdaPiModulo (sttfaProofTheory e) context M A) :
    LambdaPiModulo (sttfaProofTheory e) (entry :: context) (lift 1 0 M) (lift 1 0 A) := by
  have weakened := typed.weaken_at (sttfaProofTheory_closedBodies e)
    (sttfaProofTheory_closedTypes e) context entry [] rfl
  simpa [liftCtx] using weakened

/-- `eta c` is a type for a code `c`. -/
theorem eta_typed {context : LFTyping.Ctx} {code : LF.Term}
    (codeTyped : LambdaPiModulo (sttfaProofTheory e) context code (.con "type")) :
    LambdaPiModulo (sttfaProofTheory e) context (.app (.con "eta") code) (.srt .type) :=
  .app (.con (constType_eta names)) codeTyped

/-- `eps p` is a type for a proposition `p`. -/
theorem eps_typed {context : LFTyping.Ctx} {proposition : LF.Term}
    (propositionTyped : LambdaPiModulo (sttfaProofTheory e) context proposition
      (.app (.con "eta") (.con (e.name .bool)))) :
    LambdaPiModulo (sttfaProofTheory e) context (.app (.con "eps") proposition) (.srt .type) :=
  .app (.con (constType_eps names)) propositionTyped

theorem boolCode_typed {context : LFTyping.Ctx} :
    LambdaPiModulo (sttfaProofTheory e) context (.con (e.name .bool)) (.con "type") :=
  (proofTheory_declares names).sym_typed .bool

theorem boolDecoding_typed {context : LFTyping.Ctx} :
    LambdaPiModulo (sttfaProofTheory e) context (.app (.con "eta") (.con (e.name .bool)))
      (.srt .type) :=
  eta_typed names (boolCode_typed names)

/-- `arrow a b` is a code when `a` and `b` are, in the hub's own names. -/
theorem arrow_typed {context : LFTyping.Ctx} {a b : LF.Term}
    (aTyped : LambdaPiModulo (sttfaProofTheory e) context a (.con "type"))
    (bTyped : LambdaPiModulo (sttfaProofTheory e) context b (.con "type")) :
    LambdaPiModulo (sttfaProofTheory e) context (.app (.app (.con "arrow") a) b) (.con "type") := by
  have typed := arr_typed names aTyped bTyped
  simpa [Encoding.arr, Encoding.sym, names.arrow] using typed

/-- The two codes under `arrow` are codes. -/
theorem arrow_arguments {context : LFTyping.Ctx} {l r : LF.Term}
    (typed : LambdaPiModulo (sttfaProofTheory e) context
      (.app (.app (.con "arrow") l) r) (.con "type")) :
    LambdaPiModulo (sttfaProofTheory e) context l (.con "type") ∧
      LambdaPiModulo (sttfaProofTheory e) context r (.con "type") := by
  obtain ⟨D, B, functionTyped, rTyped, _⟩ := typed.app_inv
  have arrowDeclared : (sttfaProofTheory e).constType "arrow" =
      some (.pi (.con "type") (.pi (.con "type") (.con "type"))) := by
    rw [← names.arrow, constType_symbol]
    rfl
  obtain ⟨⟨D', lTyped, convL⟩, convPi⟩ := app_con_inv arrowDeclared (.refl _) functionTyped
  obtain ⟨convD, _⟩ := Conv.pi_injective STTfa.confluent STTfa.orthogonal.leftAlgebraic.headed
    convPi
  exact ⟨retype lTyped convL (codes_typed names),
    retype rTyped (.symm _ _ convD) (codes_typed names)⟩

omit names in
/-- The decoding of the code of a function type converts with the product of the
decodings, in the hub's own names. -/
theorem eta_arrow_conv (a b : LF.Term) :
    Conv STTfa.theory (.app (.con "eta") (.app (.app (.con "arrow") a) b))
      (.pi (.app (.con "eta") a) (.app (.con "eta") (lift 1 0 b))) :=
  (sttfa_eta_arrow a b).conv

/-- The declared type of `forall`, in the hub's own names. -/
theorem constType_forall :
    (sttfaProofTheory e).constType "forall" =
      some (.pi (.con "type") (.app (.con "eta") (.app (.app (.con "arrow")
        (.app (.app (.con "arrow") (.var 0)) (.con (e.name .bool)))) (.con (e.name .bool))))) := by
  rw [← names.all, constType_symbol]
  simp [Encoding.declaredType, Encoding.El, Encoding.arr, Encoding.sym, names.el, names.arrow]

/-- The declared type of `impl`, in the hub's own names. -/
theorem constType_impl :
    (sttfaProofTheory e).constType "impl" =
      some (.app (.con "eta") (.app (.app (.con "arrow") (.con (e.name .bool)))
        (.app (.app (.con "arrow") (.con (e.name .bool))) (.con (e.name .bool))))) := by
  rw [← names.imp, constType_symbol]
  simp [Encoding.declaredType, Encoding.El, Encoding.code, Encoding.arr, Encoding.sym, names.el,
    names.arrow]

/-- **The rules of the hub keep the types of their left sides.** -/
theorem rulesPreserveTypes : (sttfaProofTheory e).RulesPreserveTypes LFProfile.standardLF := by
  have headed := STTfa.orthogonal.leftAlgebraic.headed
  intro rule assignment context type member wellFormed typed
  have member' : STTfa.theory.rule rule := member
  rcases sttfa_rules member' with rfl | rfl | rfl | rfl | rfl | rfl
  · -- `eta ↪ λ t. etap (p t)`
    simp only [STTfa.etaDef, STTfa.etap, inst, Dedukti.instantiate] at typed ⊢
    obtain ⟨X, found, convX⟩ := typed.con_inv
    rw [constType_eta names] at found
    cases found
    have bodyTyped : LambdaPiModulo (sttfaProofTheory e) (.con "type" :: context)
        (.app (.con "etap") (.app (.con "p") (.var 0))) (.srt .type) :=
      .app (.con (constType_etap names)) (.app (.con (constType_p names)) var_codes_typed)
    have rhsTyped : LambdaPiModulo (sttfaProofTheory e) context
        (.lam (.con "type") (.app (.con "etap") (.app (.con "p") (.var 0))))
        (.pi (.con "type") (.srt .type)) :=
      .lam (codes_typed names) (.sort rfl) kind_rule bodyTyped
    obtain ⟨sort, formed⟩ := formed_of_conv_pi names wellFormed typed (conv_proofTheory convX)
    exact retype rhsTyped (conv_proofTheory convX) formed
  · -- `etap (p (arrow l r)) ↪ eta l → eta r`
    simp only [STTfa.etapArrow, STTfa.etap, STTfa.eta, STTfa.binary, inst,
      Dedukti.instantiate] at typed ⊢
    simp only [Nat.lt_irrefl, if_false, Nat.sub_zero, Mettapedia.GSLT.Dedukti.lift_zero,
      show (1 : Nat) - 1 = 0 from rfl, show ¬ (1 : Nat) < 0 from by decide] at typed ⊢
    obtain ⟨⟨_, argumentTyped, _⟩, convA⟩ := app_con_inv (constType_etap names) (.refl _) typed
    obtain ⟨⟨_, arrowTyped, convArrow⟩, _⟩ :=
      app_con_inv (constType_p names) (.refl _) argumentTyped
    obtain ⟨leftTyped, rightTyped⟩ :=
      arrow_arguments names (retype arrowTyped convArrow (codes_typed names))
    have rhsTyped := HasType.pi (eta_typed names leftTyped)
      (eta_typed names (weaken_one _ rightTyped)) arrow_rule
    obtain ⟨sort, formed⟩ := formed_of_conv_type names wellFormed typed convA
    exact retype rhsTyped convA formed
  · -- `etap (forallK f) ↪ Π x : type. etap (f x)`
    simp only [STTfa.etapForall, STTfa.etap, inst, Dedukti.instantiate] at typed ⊢
    simp only [Nat.lt_irrefl, if_false, Nat.sub_self, Mettapedia.GSLT.Dedukti.lift_zero,
      show (0 : Nat) < 1 from by decide, if_true] at typed ⊢
    obtain ⟨⟨_, argumentTyped, _⟩, convA⟩ := app_con_inv (constType_etap names) (.refl _) typed
    obtain ⟨⟨_, familyTyped, convFamily⟩, _⟩ :=
      app_con_inv (constType_forallK names) (.refl _) argumentTyped
    have familyTyped' := retype familyTyped convFamily
      (.pi (codes_typed names) (.con (constType_ptype names)) arrow_rule)
    have bodyTyped : LambdaPiModulo (sttfaProofTheory e) (.con "type" :: context)
        (.app (.con "etap") (.app (lift 1 0 (assignment 0)) (.var 0))) (.srt .type) :=
      .app (.con (constType_etap names)) (.app (weaken_one _ familyTyped') var_codes_typed)
    obtain ⟨sort, formed⟩ := formed_of_conv_type names wellFormed typed convA
    exact retype (.pi (codes_typed names) bodyTyped arrow_rule) convA formed
  · -- `eps (forall t f) ↪ Π x : eta t. eps (f x)`
    simp only [STTfa.epsForall, STTfa.eps, STTfa.eta, STTfa.binary, inst,
      Dedukti.instantiate] at typed ⊢
    simp only [Nat.lt_irrefl, if_false, Nat.sub_zero, Mettapedia.GSLT.Dedukti.lift_zero,
      show ¬ (1 : Nat) < 0 from by decide, show (0 : Nat) < 1 from by decide, if_true,
      show (1 : Nat) - 1 = 0 from rfl] at typed ⊢
    obtain ⟨⟨_, argumentTyped, _⟩, convA⟩ := app_con_inv (constType_eps names) (.refl _) typed
    obtain ⟨D, B, quantifierTyped, familyTyped, _⟩ := argumentTyped.app_inv
    obtain ⟨⟨_, codeTyped, convCode⟩, convPi⟩ :=
      app_con_inv (constType_forall names) (.refl _) quantifierTyped
    have codeTyped' := retype codeTyped convCode (codes_typed names)
    have shapeConv := Relation.EqvGen.trans _ _ _ (.symm _ _ convPi)
      (eta_arrow_conv (.app (.app (.con "arrow") (assignment 1)) (.con (e.name .bool)))
        (.con (e.name .bool)))
    obtain ⟨convD, _⟩ := Conv.pi_injective STTfa.confluent headed shapeConv
    have familyTyped' := retype familyTyped convD
      (eta_typed names (arrow_typed names codeTyped' (boolCode_typed names)))
    have familyTyped'' := retype familyTyped'
      (eta_arrow_conv (assignment 1) (.con (e.name .bool)))
      (.pi (eta_typed names codeTyped') (eta_typed names (boolCode_typed names)) arrow_rule)
    have bodyTyped : LambdaPiModulo (sttfaProofTheory e) (.app (.con "eta") (assignment 1) :: context)
        (.app (.con "eps") (.app (lift 1 0 (assignment 0)) (.var 0))) (.srt .type) :=
      eps_typed names (.app (weaken_one _ familyTyped'') (.var (lookup_cons_zero _ _)))
    obtain ⟨sort, formed⟩ := formed_of_conv_type names wellFormed typed convA
    exact retype (.pi (eta_typed names codeTyped') bodyTyped arrow_rule) convA formed
  · -- `eps (impl l r) ↪ eps l → eps r`
    simp only [STTfa.epsImpl, STTfa.eps, STTfa.binary, inst, Dedukti.instantiate] at typed ⊢
    simp only [Nat.lt_irrefl, if_false, Nat.sub_zero, Mettapedia.GSLT.Dedukti.lift_zero,
      show ¬ (1 : Nat) < 0 from by decide, show (1 : Nat) - 1 = 0 from rfl] at typed ⊢
    obtain ⟨⟨_, argumentTyped, _⟩, convA⟩ := app_con_inv (constType_eps names) (.refl _) typed
    obtain ⟨D, B, implTyped, rightTyped, _⟩ := argumentTyped.app_inv
    have implShape : Conv STTfa.theory
        (.app (.con "eta") (.app (.app (.con "arrow") (.con (e.name .bool)))
          (.app (.app (.con "arrow") (.con (e.name .bool))) (.con (e.name .bool)))))
        (.pi (.app (.con "eta") (.con (e.name .bool)))
          (.pi (.app (.con "eta") (.con (e.name .bool))) (.app (.con "eta") (.con (e.name .bool))))) :=
      .trans _ _ _ (eta_arrow_conv _ _)
        (Conv.pi (.refl _) (eta_arrow_conv (.con (e.name .bool)) (.con (e.name .bool))))
    obtain ⟨⟨_, leftTyped, convLeft⟩, convPi⟩ := app_con_inv (constType_impl names) implShape implTyped
    obtain ⟨convD, _⟩ := Conv.pi_injective STTfa.confluent headed convPi
    have leftTyped' := retype leftTyped convLeft (boolDecoding_typed names)
    have rightTyped' := retype rightTyped (.symm _ _ convD) (boolDecoding_typed names)
    have rhsTyped := HasType.pi (eps_typed names leftTyped')
      (eps_typed names (weaken_one _ rightTyped')) arrow_rule
    obtain ⟨sort, formed⟩ := formed_of_conv_type names wellFormed typed convA
    exact retype rhsTyped convA formed
  · -- `eps (forallP f) ↪ Π x : type. eps (f x)`
    simp only [STTfa.epsForallP, STTfa.eps, inst, Dedukti.instantiate] at typed ⊢
    simp only [Nat.lt_irrefl, if_false, Nat.sub_self, Mettapedia.GSLT.Dedukti.lift_zero,
      show (0 : Nat) < 1 from by decide, if_true] at typed ⊢
    obtain ⟨⟨_, argumentTyped, _⟩, convA⟩ := app_con_inv (constType_eps names) (.refl _) typed
    obtain ⟨⟨_, familyTyped, convFamily⟩, _⟩ :=
      app_con_inv (constType_forallP names) (.refl _) argumentTyped
    have familyTyped' := retype familyTyped convFamily
      (.pi (codes_typed names) (boolDecoding_typed names) arrow_rule)
    have bodyTyped : LambdaPiModulo (sttfaProofTheory e) (.con "type" :: context)
        (.app (.con "eps") (.app (lift 1 0 (assignment 0)) (.var 0))) (.srt .type) :=
      eps_typed names (.app (weaken_one _ familyTyped') var_codes_typed)
    obtain ⟨sort, formed⟩ := formed_of_conv_type names wellFormed typed convA
    exact retype (.pi (codes_typed names) bodyTyped arrow_rule) convA formed

/-- **Type preservation in the typed STTfa hub**: every reduct of a term typed
in a well-formed context has its type. -/
theorem sttfa_typePreservation {context : LFTyping.Ctx} {source target type : LF.Term}
    (wellFormed : WellFormedCtx LFProfile.standardLF (sttfaProofTheory e) context)
    (typed : LambdaPiModulo (sttfaProofTheory e) context source type)
    (reduces : Reduces (sttfaProofTheory e) source target) :
    LambdaPiModulo (sttfaProofTheory e) context target type :=
  typePreservation_reduces (proofTheory_confluent e) (proofTheory_headed e)
    (sttfaProofTheory_closedBodies e) (sttfaProofTheory_closedTypes e) (formedSignature names)
    (typedBodies e) (rulesPreserveTypes names) wellFormed typed reduces

end Rules

/-! ## Controls -/

/-- The compiled proof of `(∀ x. pred x) ⇒ pred point` is
`λ h : eps (tr (∀ x. pred x)). h point`. -/
theorem compile_predInstance :
    compile sttfaControl "eps" predInstanceProof (.base []) Fin.elim0 =
      .lam (.app (.con "eps") (sttfaControl.translate (.all predVar))) (.app (.var 0) (.con "point")) :=
  rfl

theorem reduces_toProofTheory {Base : Type u} {Const : Ty Base → Type v} {e : Encoding Base Const}
    {a b : LF.Term} (reduces : Reduces STTfa.theory a b) : Reduces (sttfaProofTheory e) a b := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih =>
      exact ih.tail (Step.of_sameRules (theory := STTfa.theory) (theory' := sttfaProofTheory e)
        rfl rfl step)

/-- The compiled proof reduces to its normal form `λ h. h point`. -/
theorem compile_predInstance_reduces :
    Reduces (sttfaProofTheory sttfaControl)
      (compile sttfaControl "eps" predInstanceProof (.base []) Fin.elim0) predInstanceTerm := by
  rw [compile_predInstance]
  apply reduces_toProofTheory
  have allNormal : HOL.BetaNormalization.Normal (.all predVar : Formula ControlConst []) :=
    fun target ⟨step⟩ => by
      cases step with
      | all inner => exact predVar_normal _ ⟨inner⟩
  have domain := sttfa_reduces_of_conv (conv_eps_epsNF sttfaControl_names (.all predVar))
    (epsNF_normal_all sttfaControl_names _ allNormal)
  exact Reduces.lam domain .refl

/-- **Type preservation at work**: the normal form of the compiled proof has the
type of the proofs of `(∀ x. pred x) ⇒ pred point`, by type preservation from
the typing of the compiled proof. -/
theorem predInstance_typed_by_preservation :
    LambdaPiModulo (sttfaProofTheory sttfaControl) [] predInstanceTerm
      (.app (.con "eps") (sttfaControl.translate (.imp (.all predVar) predPoint))) :=
  sttfa_typePreservation sttfaControl_names .nil
    (sttfaControlProofs.theorem_typed predInstanceProof) compile_predInstance_reduces

/-- The declarations of the earlier typed hub beyond the encoding: `eps` only. -/
def formerProofTypes {Base : Type u} {Const : Ty Base → Type v} (e : Encoding Base Const)
    (name : String) : Option LF.Term :=
  if name = "eps" then some (.pi (e.El (e.sym .bool)) (.srt .type)) else none

/-- The earlier typed hub. -/
noncomputable def formerProofTheory {Base : Type u} {Const : Ty Base → Type v}
    (e : Encoding Base Const) : Theory :=
  e.typedTheory STTfa.theory "type" (formerProofTypes e)

/-- **The earlier typed hub is not type preserving**: `eta bool` is a type, and
its reduct `(λ t. etap (p t)) bool` has no type, since `etap` has no declared
type there. -/
theorem formerHub_not_typePreserving :
    LambdaPiModulo (formerProofTheory sttfaControl) [] (.app (.con "eta") (.con "bool")) (.srt .type) ∧
      Step (formerProofTheory sttfaControl) (.app (.con "eta") (.con "bool"))
        (.app (.lam (.con "type") (.app (.con "etap") (.app (.con "p") (.var 0)))) (.con "bool")) ∧
      ∀ type : LF.Term, ¬ LambdaPiModulo (formerProofTheory sttfaControl) []
        (.app (.lam (.con "type") (.app (.con "etap") (.app (.con "p") (.var 0)))) (.con "bool")) type := by
  have etaDeclared : (formerProofTheory sttfaControl).constType "eta" =
      some (.pi (.con "type") (.srt .type)) :=
    sttfaControl.typedTheory_el STTfa.theory (codes := "type") (formerProofTypes sttfaControl)
      (fun s same => (sttfaControl_fresh s).1 same) (by decide)
  have boolDeclared : (formerProofTheory sttfaControl).constType "bool" = some (.con "type") :=
    sttfaControl.typedTheory_symbol STTfa.theory "type" (formerProofTypes sttfaControl) .bool
  have etapUndeclared : (formerProofTheory sttfaControl).constType "etap" = none := by
    have unnamed : ¬ ∃ s, controlName "arrow" s = "etap" :=
      fun ⟨s, same⟩ => (sttfaControl_fresh s).2.1 same
    simp [formerProofTheory, Encoding.typedTheory, formerProofTypes, sttfaControl,
      controlEncoding, unnamed]
  refine ⟨.app (.con etaDeclared) (.con boolDeclared), ?_, ?_⟩
  · have member : STTfa.theory.rule STTfa.etaDef := by
      simp [STTfa.theory, Theory.ofSig, STTfa.rules]
    have root := Step.root (RootStep.rule (theory := formerProofTheory sttfaControl)
      (fun _ => .con "type") member)
    simpa [STTfa.etaDef, STTfa.etap, inst, Dedukti.instantiate,
      LFContextualBetaEta.Context.plug] using root.plug (.appFunction .hole (.con "bool"))
  · intro type typed
    obtain ⟨_, _, functionTyped, _, _⟩ := typed.app_inv
    obtain ⟨_, _, _, _, _, _, _, bodyTyped, _⟩ := functionTyped.lam_inv
    obtain ⟨_, _, etapTyped, _, _⟩ := bodyTyped.app_inv
    obtain ⟨_, found, _⟩ := etapTyped.con_inv
    rw [etapUndeclared] at found
    cases found

#print axioms formedSignature
#print axioms rulesPreserveTypes
#print axioms sttfa_typePreservation
#print axioms predInstance_typed_by_preservation
#print axioms formerHub_not_typePreserving

end Mettapedia.GSLT.Dedukti.HOLHub
