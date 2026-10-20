import Mettapedia.GSLT.Dedukti.HOLHubTransport

/-!
# Typing the translation of higher-order logic in the hubs

`HOLHubTransport` proves that a hub decides conversion of translated HOL terms.
This module types the translated terms.

**Declarations** (`Encoding.declaredType`).  Over a constant `codes` of type
codes, the named symbols are declared as the encodings of HOL declare them: a
sort and `prop` are codes, the arrow takes two codes to a code, a constant of
type `τ` is a term of the decoding of the code of `τ`, the connectives decode
their simple types, and equality and the quantifiers take the code of their
type first.  A theory *declares* an encoding (`Declares`) when it declares
`codes`, the decoder `El : codes → Type` and every named symbol this way, and
converts the decoding of a function code with the product of the
decodings.

* **The translation preserves typing** (`Declares.translate_typed`): a term of
  type `τ` in the context `Γ` is translated to a term of `El (code τ)` in the
  context of the decodings of `Γ`.
* The **typed theory** of a hub (`HubTheory.typed`) adds these declarations to
  the hub's theory and changes neither its definitions nor its rules, so its
  steps are the hub's steps (`step_typedTheory`) and it is again a theory of the
  encoding; it declares the encoding (`HubTheory.typed_declares`).  So on typed
  translations the end-to-end theorem holds in a typed theory
  (`HubTheory.typed_conv_iff`).
* **Holide** (`holide_translate_typed`, `holide_typed_conv_iff`) and the
  **STTfa hub** (`sttfa_translate_typed`).  For the controls, the typed theory
  extends Holide's theory as transcribed in `TwoRoutes.holTheory`: it adds
  declarations and keeps every declared type (`holideControl_extends`).  In
  the STTfa hub the declared types of `impl` and `forall` are those of
  Logipedia's theory file up to the hub's conversion
  (`sttfa_impl_type_conv`, `sttfa_forall_type_conv`).

The statement `holide_translate_typed` replaces an earlier one for simply
typed λ-terms over a single base type,
`TwoRoutes.Hol (holideCtx Γ) (holideCodes.translate t) (TwoRoutes.termOf (holideCodes.code A))`,
typed in `TwoRoutes.holTheory` itself.  The present source has constants and
connectives, so the typing theory also declares them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.HOLHub

open Mettapedia.Logic
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LFTyping (lift subst subst0 lookupBody)
open Mettapedia.Logic.HOL (Ty Ctx Var Term)

universe u v

/-! ## Steps do not read declared types -/

theorem RootStep.of_sameRules {theory theory' : Theory} (body : theory.body = theory'.body)
    (rule : theory.rule = theory'.rule) {source target : LF.Term}
    (root : RootStep theory source target) : RootStep theory' source target := by
  cases root with
  | beta domain body' argument => exact .beta domain body' argument
  | delta defined => exact .delta (body ▸ defined)
  | rule assignment member => exact .rule assignment (rule ▸ member)

theorem Step.of_sameRules {theory theory' : Theory} (body : theory.body = theory'.body)
    (rule : theory.rule = theory'.rule) {source target : LF.Term}
    (step : Step theory source target) : Step theory' source target := by
  cases step with
  | inContext context root => exact .inContext context (RootStep.of_sameRules body rule root)

/-- Two theories with the same definitions and rules have the same steps. -/
theorem step_eq_of_sameRules {theory theory' : Theory} (body : theory.body = theory'.body)
    (rule : theory.rule = theory'.rule) : Step theory = Step theory' := by
  funext source target
  exact propext ⟨Step.of_sameRules body rule, Step.of_sameRules body.symm rule.symm⟩

/-! ## Declarations -/

namespace Encoding

variable {Base : Type u} {Const : Ty Base → Type v} (e : Encoding Base Const)

/-- The declared type of a named symbol, over the type `codes` of type codes. -/
def declaredType (codes : LF.Term) : Symbol Base Const → LF.Term
  | .sort _ => codes
  | .const (τ := τ) _ => e.El (e.code τ)
  | .bool => codes
  | .arrow => .pi codes (.pi codes codes)
  | .top => e.El (e.code .prop)
  | .bot => e.El (e.code .prop)
  | .and => e.El (e.code (.arr .prop (.arr .prop .prop)))
  | .or => e.El (e.code (.arr .prop (.arr .prop .prop)))
  | .imp => e.El (e.code (.arr .prop (.arr .prop .prop)))
  | .not => e.El (e.code (.arr .prop .prop))
  | .eq => .pi codes (e.El (e.arr (.var 0) (e.arr (.var 0) (e.sym .bool))))
  | .all => .pi codes (e.El (e.arr (e.arr (.var 0) (e.sym .bool)) (e.sym .bool)))
  | .ex => .pi codes (e.El (e.arr (e.arr (.var 0) (e.sym .bool)) (e.sym .bool)))

/-- The context of the decodings of a source context. -/
def ctx (Γ : Ctx Base) : LFTyping.Ctx := Γ.map fun σ => e.El (e.code σ)

theorem ctx_getElem : ∀ {Γ : Ctx Base} {τ : Ty Base} (v : Var Γ τ),
    (e.ctx Γ)[varIndex v]? = some (e.El (e.code τ))
  | _, _, .vz => rfl
  | _, _, .vs prior => by simpa [ctx, varIndex] using ctx_getElem prior

theorem ctxLookup_var {Γ : Ctx Base} {τ : Ty Base} (v : Var Γ τ) :
    LFTyping.ctxLookup (e.ctx Γ) (varIndex v) = some (e.El (e.code τ)) := by
  rw [ctxLookup_eq_getElem?, e.ctx_getElem v, Option.map_some]
  exact congrArg some ((e.El_code_closed τ).lift _ _)

open Classical in
/-- **The typed theory**: a theory with the named symbols declared at their
declared types, `codes` a type, and `El` a family over `codes`; every other
constant keeps its declared type, and the definitions and rules are kept. -/
noncomputable def typedTheory (theory : Theory) (codes : String)
    (extra : String → Option LF.Term := theory.constType) : Theory where
  constType name :=
    if found : ∃ s, e.name s = name then some (e.declaredType (.con codes) found.choose)
    else if name = codes then some (.srt .type)
    else if name = e.el then some (.pi (.con codes) (.srt .type))
    else extra name
  body := theory.body
  rule := theory.rule

theorem typedTheory_symbol (theory : Theory) (codes : String) (extra : String → Option LF.Term)
    (s : Symbol Base Const) :
    (e.typedTheory theory codes extra).constType (e.name s) =
      some (e.declaredType (.con codes) s) := by
  have found : ∃ s', e.name s' = e.name s := ⟨s, rfl⟩
  simp only [typedTheory, dif_pos found]
  rw [e.injective found.choose_spec]

theorem typedTheory_codes (theory : Theory) {codes : String} (extra : String → Option LF.Term)
    (fresh : ∀ s, e.name s ≠ codes) :
    (e.typedTheory theory codes extra).constType codes = some (.srt .type) := by
  have unnamed : ¬ ∃ s, e.name s = codes := fun ⟨s, same⟩ => fresh s same
  simp [typedTheory, unnamed]

theorem typedTheory_el (theory : Theory) {codes : String} (extra : String → Option LF.Term)
    (unnamed : ∀ s, e.name s ≠ e.el) (codesEl : codes ≠ e.el) :
    (e.typedTheory theory codes extra).constType e.el = some (.pi (.con codes) (.srt .type)) := by
  have none_ : ¬ ∃ s, e.name s = e.el := fun ⟨s, same⟩ => unnamed s same
  simp [typedTheory, none_, Ne.symm codesEl]

/-- The declared types are closed. -/
theorem declaredType_closed (codes : String) : ∀ s : Symbol Base Const,
    Closed (e.declaredType (.con codes) s)
  | .sort _ => .con
  | .const _ => e.El_code_closed _
  | .bool => .con
  | .arrow => .pi .con (.pi .con .con)
  | .top => e.El_code_closed _
  | .bot => e.El_code_closed _
  | .and => e.El_code_closed _
  | .or => e.El_code_closed _
  | .imp => e.El_code_closed _
  | .not => e.El_code_closed _
  | .eq => .pi .con (.app .con (.app (.app .con (.var (by decide)))
      (.app (.app .con (.var (by decide))) .con)))
  | .all => .pi .con (.app .con (.app (.app .con (.app (.app .con (.var (by decide))) .con)) .con))
  | .ex => .pi .con (.app .con (.app (.app .con (.app (.app .con (.var (by decide))) .con)) .con))

theorem step_typedTheory (theory : Theory) (codes : String) (extra : String → Option LF.Term) :
    Step (e.typedTheory theory codes extra) = Step theory :=
  step_eq_of_sameRules rfl rfl

end Encoding

/-- A theory **declares** an encoding over the constant `codes`: `codes` is a
type, `El` is a family over it, every named symbol has its declared type, and
the decoding of a function code converts with the product of the decodings. -/
structure Declares {Base : Type u} {Const : Ty Base → Type v} (e : Encoding Base Const)
    (theory : Theory) (codes : String) : Prop where
  codes_type : theory.constType codes = some (.srt .type)
  el_type : theory.constType e.el = some (.pi (.con codes) (.srt .type))
  symbol_type : ∀ s, theory.constType (e.name s) = some (e.declaredType (.con codes) s)
  arrow_conv : ∀ σ τ : Ty Base,
    Conv theory (e.El (e.code (.arr σ τ))) (.pi (e.El (e.code σ)) (e.El (e.code τ)))

namespace Declares

variable {Base : Type u} {Const : Ty Base → Type v} {e : Encoding Base Const}
variable {theory : Theory} {codes : String} (d : Declares e theory codes)
include d

theorem sym_typed {Γ : LFTyping.Ctx} (s : Symbol Base Const) :
    LambdaPiModulo theory Γ (e.sym s) (e.declaredType (.con codes) s) :=
  .con (d.symbol_type s)

theorem code_typed {Γ : LFTyping.Ctx} : ∀ τ : Ty Base, LambdaPiModulo theory Γ (e.code τ) (.con codes)
  | .prop => d.sym_typed .bool
  | .base b => d.sym_typed (.sort b)
  | .arr σ τ => .app (.app (d.sym_typed .arrow) (code_typed σ)) (code_typed τ)

theorem El_typed {Γ : LFTyping.Ctx} {code : LF.Term}
    (typed : LambdaPiModulo theory Γ code (.con codes)) :
    LambdaPiModulo theory Γ (e.El code) (.srt .type) :=
  .app (.con d.el_type) typed

theorem El_code_typed {Γ : LFTyping.Ctx} (τ : Ty Base) :
    LambdaPiModulo theory Γ (e.El (e.code τ)) (.srt .type) :=
  d.El_typed (d.code_typed τ)

/-- The decoding of a function code, as the product of the decodings. -/
theorem conv_El_arr (σ τ : Ty Base) :
    Conv theory (e.El (e.code (.arr σ τ))) (.pi (e.El (e.code σ)) (e.El (e.code τ))) :=
  d.arrow_conv σ τ

theorem pi_El_typed {Γ : LFTyping.Ctx} (σ τ : Ty Base) :
    LambdaPiModulo theory Γ (.pi (e.El (e.code σ)) (e.El (e.code τ))) (.srt .type) :=
  .pi (d.El_code_typed σ) (d.El_code_typed τ) arrow_rule

/-- A term of the decoding of a function code is a function of the framework. -/
theorem as_function {Γ : LFTyping.Ctx} {function : LF.Term} {σ τ : Ty Base}
    (typed : LambdaPiModulo theory Γ function (e.El (e.code (.arr σ τ)))) :
    LambdaPiModulo theory Γ function (.pi (e.El (e.code σ)) (e.El (e.code τ))) :=
  .conv typed (d.conv_El_arr σ τ) (d.pi_El_typed σ τ)

theorem apply_typed {Γ : LFTyping.Ctx} {function argument : LF.Term} {σ τ : Ty Base}
    (functionTyped : LambdaPiModulo theory Γ function (e.El (e.code (.arr σ τ))))
    (argumentTyped : LambdaPiModulo theory Γ argument (e.El (e.code σ))) :
    LambdaPiModulo theory Γ (.app function argument) (e.El (e.code τ)) := by
  have applied := HasType.app (d.as_function functionTyped) argumentTyped
  rwa [show subst0 argument (e.El (e.code τ)) = e.El (e.code τ) from
    (e.El_code_closed τ).subst 0 argument] at applied

theorem lam_typed {Γ : LFTyping.Ctx} {body : LF.Term} {σ τ : Ty Base}
    (bodyTyped : LambdaPiModulo theory (e.El (e.code σ) :: Γ) body (e.El (e.code τ))) :
    LambdaPiModulo theory Γ (.lam (e.El (e.code σ)) body) (e.El (e.code (.arr σ τ))) :=
  .conv (.lam (d.El_code_typed σ) (d.El_code_typed τ) arrow_rule bodyTyped)
    (.symm _ _ (d.conv_El_arr σ τ)) (d.El_code_typed (.arr σ τ))

/-- Equality at `τ`, applied to the code of `τ`. -/
theorem eq_typed {Γ : LFTyping.Ctx} (τ : Ty Base) :
    LambdaPiModulo theory Γ (.app (e.sym .eq) (e.code τ)) (e.El (e.code (.arr τ (.arr τ .prop)))) := by
  have applied := HasType.app (d.sym_typed (Γ := Γ) .eq) (d.code_typed τ)
  simpa [subst0, LFTyping.subst, Encoding.El, Encoding.arr, Encoding.sym, Encoding.code,
    (e.code_closed τ).lift] using applied

/-- A quantifier over `σ`, applied to the code of `σ`. -/
theorem quantifier_typed {Γ : LFTyping.Ctx} {s : Symbol Base Const}
    (declared : e.declaredType (.con codes) s =
      .pi (.con codes) (e.El (e.arr (e.arr (.var 0) (e.sym .bool)) (e.sym .bool))))
    (σ : Ty Base) :
    LambdaPiModulo theory Γ (.app (e.sym s) (e.code σ)) (e.El (e.code (.arr (.arr σ .prop) .prop))) := by
  have head : LambdaPiModulo theory Γ (e.sym s)
      (.pi (.con codes) (e.El (e.arr (e.arr (.var 0) (e.sym .bool)) (e.sym .bool)))) := by
    rw [← declared]
    exact d.sym_typed s
  have applied := HasType.app head (d.code_typed σ)
  simpa [subst0, LFTyping.subst, Encoding.El, Encoding.arr, Encoding.sym, Encoding.code,
    (e.code_closed σ).lift] using applied

/-- **The translation preserves typing**: a term of type `τ` in `Γ` is
translated to a term of the decoding of the code of `τ`, in the context of the
decodings of `Γ`. -/
theorem translate_typed : ∀ {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ),
    LambdaPiModulo theory (e.ctx Γ) (e.translate t) (e.El (e.code τ)) := by
  intro Γ τ t
  induction t with
  | var v => exact .var (e.ctxLookup_var v)
  | const c => exact d.sym_typed (.const c)
  | app f a ihf iha => exact d.apply_typed ihf iha
  | lam body ih => exact d.lam_typed ih
  | top => exact d.sym_typed .top
  | bot => exact d.sym_typed .bot
  | and p q ihp ihq =>
      exact d.apply_typed (σ := .prop) (d.apply_typed (σ := .prop) (d.sym_typed .and) ihp) ihq
  | or p q ihp ihq =>
      exact d.apply_typed (σ := .prop) (d.apply_typed (σ := .prop) (d.sym_typed .or) ihp) ihq
  | imp p q ihp ihq =>
      exact d.apply_typed (σ := .prop) (d.apply_typed (σ := .prop) (d.sym_typed .imp) ihp) ihq
  | not p ih => exact d.apply_typed (σ := .prop) (d.sym_typed .not) ih
  | @eq Γ τ l r ihl ihr => exact d.apply_typed (d.apply_typed (d.eq_typed τ) ihl) ihr
  | @all σ Γ body ih => exact d.apply_typed (d.quantifier_typed (s := .all) rfl σ) (d.lam_typed ih)
  | @ex σ Γ body ih => exact d.apply_typed (d.quantifier_typed (s := .ex) rfl σ) (d.lam_typed ih)

end Declares

/-! ## The typed theory of a hub -/

namespace HubTheory

variable {Base : Type u} {Const : Ty Base → Type v} {e : Encoding Base Const} (h : HubTheory e)

/-- **The decoder is defined**: the decoding of a function code has a step,
and since codes are normal the step is at `El`. -/
theorem el_defines : h.theory.Defines e.el := by
  rcases (h.arrow_reduces .prop .prop).cases_head with same | ⟨middle, step, _⟩
  · simp [Encoding.El] at same
  · rcases step.app_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
    · rcases root.defines h.headed with ⟨_, _, _, shape⟩ | ⟨name, head, defines⟩
      · simp at shape
      · simp only [headConst, Option.some.injEq] at head
        subst head
        exact defines
    · rcases inner.con_inv.defines h.headed with ⟨_, _, _, shape⟩ | ⟨name, head, defines⟩
      · cases shape
      · simp only [headConst, Option.some.injEq] at head
        subst head
        exact defines
    · exact absurd inner (h.code_normal (.arr .prop .prop) _)

include h in
/-- So no symbol is named after the decoder. -/
theorem el_unnamed (s : Symbol Base Const) : e.name s ≠ e.el := fun same =>
  h.rigid s (same ▸ h.el_defines)

theorem reduces_typedTheory {theory : Theory} {codes : String} {extra : String → Option LF.Term}
    {source target : LF.Term} (reduces : Reduces theory source target) :
    Reduces (e.typedTheory theory codes extra) source target := by
  induction reduces with
  | refl => exact .refl
  | tail _ step ih =>
      exact ih.tail (Step.of_sameRules (theory := theory)
        (theory' := e.typedTheory theory codes extra) rfl rfl step)

/-- **The typed theory of a hub** is again a theory of the encoding: it adds
declarations and keeps the definitions and the rules. -/
noncomputable def typed (codes : String) (extra : String → Option LF.Term := h.theory.constType) :
    HubTheory e where
  theory := e.typedTheory h.theory codes extra
  headed := h.headed
  confluent := by rw [e.step_typedTheory]; exact h.confluent
  rigid := h.rigid
  elAt := h.elAt
  elAt_reduces s := reduces_typedTheory (h.elAt_reduces s)
  elAt_normal s := by rw [e.step_typedTheory]; exact h.elAt_normal s
  elAt_closed := h.elAt_closed
  elAt_injective := h.elAt_injective
  elAt_not_pi := h.elAt_not_pi
  arrow_reduces σ τ := reduces_typedTheory (h.arrow_reduces σ τ)

theorem typed_declares {codes : String} (extra : String → Option LF.Term)
    (fresh : ∀ s, e.name s ≠ codes) (codesEl : codes ≠ e.el) :
    Declares e (h.typed codes extra).theory codes where
  codes_type := e.typedTheory_codes h.theory extra fresh
  el_type := e.typedTheory_el h.theory extra h.el_unnamed codesEl
  symbol_type := e.typedTheory_symbol h.theory codes extra
  arrow_conv σ τ := ((h.typed codes extra).arrow_reduces σ τ).conv

/-- **End to end, typed**: in the typed theory of a hub, translations are
typed, and two of them are convertible exactly when the source terms are
β-convertible. -/
theorem typed_conv_iff {codes : String} (fresh : ∀ s, e.name s ≠ codes) (codesEl : codes ≠ e.el)
    {Γ : Ctx Base} {τ : Ty Base} (s t : Term Const Γ τ) :
    LambdaPiModulo (h.typed codes).theory (e.ctx Γ) (e.translate s) (e.El (e.code τ)) ∧
      LambdaPiModulo (h.typed codes).theory (e.ctx Γ) (e.translate t) (e.El (e.code τ)) ∧
      (Conv (h.typed codes).theory (e.translate s) (e.translate t) ↔ BetaConv s t) :=
  ⟨(h.typed_declares _ fresh codesEl).translate_typed s,
    (h.typed_declares _ fresh codesEl).translate_typed t, (h.typed codes).translate_conv_iff s t⟩

end HubTheory

/-! ## Holide and the STTfa hub -/

section Hubs

variable {Base : Type u} {Const : Ty Base → Type v}

/-- **Holide's encoding types the translations**, in Holide's theory with the
symbols of the signature declared. -/
theorem holide_translate_typed (e : Encoding Base Const) (el : e.el = "term")
    (arrow : e.name .arrow = "arr") (fresh : ∀ s, e.name s ≠ "term")
    (typeFresh : ∀ s, e.name s ≠ "type") {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    LambdaPiModulo (e.typedTheory TwoRoutes.holTheory "type") (e.ctx Γ) (e.translate t)
      (e.El (e.code τ)) :=
  ((holideHub e el arrow fresh).typed_declares _ typeFresh (by rw [el]; decide)).translate_typed t

/-- **End to end, typed, through Holide's encoding.** -/
theorem holide_typed_conv_iff (e : Encoding Base Const) (el : e.el = "term")
    (arrow : e.name .arrow = "arr") (fresh : ∀ s, e.name s ≠ "term")
    (typeFresh : ∀ s, e.name s ≠ "type") {Γ : Ctx Base} {τ : Ty Base} (s t : Term Const Γ τ) :
    LambdaPiModulo (e.typedTheory TwoRoutes.holTheory "type") (e.ctx Γ) (e.translate s)
        (e.El (e.code τ)) ∧
      LambdaPiModulo (e.typedTheory TwoRoutes.holTheory "type") (e.ctx Γ) (e.translate t)
        (e.El (e.code τ)) ∧
      (Conv (e.typedTheory TwoRoutes.holTheory "type") (e.translate s) (e.translate t) ↔
        BetaConv s t) :=
  (holideHub e el arrow fresh).typed_conv_iff typeFresh (by rw [el]; decide) s t

/-- **The STTfa hub types the translations**, with the symbols of the signature
declared. -/
theorem sttfa_translate_typed (e : Encoding Base Const) (el : e.el = "eta")
    (arrow : e.name .arrow = "arrow")
    (fresh : ∀ s, e.name s ≠ "eta" ∧ e.name s ≠ "etap" ∧ e.name s ≠ "eps")
    (typeFresh : ∀ s, e.name s ≠ "type") {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    LambdaPiModulo (e.typedTheory TranslationTransport.STTfa.theory "type") (e.ctx Γ)
      (e.translate t) (e.El (e.code τ)) :=
  ((sttfaHub e el arrow fresh).typed_declares _ typeFresh (by rw [el]; decide)).translate_typed t

end Hubs

/-! ## Controls -/

theorem holideControl_typeFresh (s : Symbol Unit ControlConst) : holideControl.name s ≠ "type" := by
  cases s <;> (try (rename_i c; cases c)) <;> simp [holideControl, controlEncoding, controlName]

theorem holideControl_fresh (s : Symbol Unit ControlConst) : holideControl.name s ≠ "term" := by
  cases s <;> (try (rename_i c; cases c)) <;> simp [holideControl, controlEncoding, controlName]

/-- **The typed theory of the controls extends Holide's theory**: it declares
the controls' symbols and keeps every type `TwoRoutes.holTheory` declares. -/
theorem holideControl_extends :
    TwoRoutes.holTheory.Extends (holideControl.typedTheory TwoRoutes.holTheory "type") := by
  refine ⟨fun name type declared => ?_, fun _ _ same => same, fun _ member => member⟩
  by_cases named : ∃ s, holideControl.name s = name
  · obtain ⟨s, rfl⟩ := named
    rw [holideControl.typedTheory_symbol]
    cases s <;> (try (rename_i c; cases c)) <;>
      simp_all [holideControl, controlEncoding, controlName, TwoRoutes.holTheory, Theory.ofSig,
        TwoRoutes.holSig, LFTyping.sigT, LFTyping.lookupType, Encoding.declaredType, Encoding.El,
        Encoding.arr, Encoding.sym, TwoRoutes.holType, TwoRoutes.termOf, TwoRoutes.arr,
        TwoRoutes.bool]
  · by_cases isType : name = "type"
    · subst isType
      have holide : TwoRoutes.holTheory.constType "type" = some (.srt .type) := by
        simp [TwoRoutes.holTheory, Theory.ofSig, TwoRoutes.holSig, LFTyping.sigT,
          LFTyping.lookupType]
      rw [holide] at declared
      cases declared
      exact holideControl.typedTheory_codes TwoRoutes.holTheory _ holideControl_typeFresh
    · by_cases isEl : name = holideControl.el
      · subst isEl
        have holide : TwoRoutes.holTheory.constType holideControl.el =
            some (.pi (.con "type") (.srt .type)) := by
          simp [TwoRoutes.holTheory, Theory.ofSig, TwoRoutes.holSig, LFTyping.sigT,
            LFTyping.lookupType, TwoRoutes.holType, holideControl, controlEncoding]
        rw [holide] at declared
        cases declared
        exact holideControl.typedTheory_el TwoRoutes.holTheory _ holideControlHub.el_unnamed
          (by decide)
      · simp only [Encoding.typedTheory, dif_neg named, if_neg isType, if_neg isEl]
        exact declared

/-- `(λ x. pred x) point`, typed in Holide's encoding of the controls. -/
theorem holide_predicate_typed :
    LambdaPiModulo (holideControl.typedTheory TwoRoutes.holTheory "type") (holideControl.ctx [])
      (holideControl.translate predicateRedex) (holideControl.El (holideControl.code .prop)) :=
  holide_translate_typed holideControl rfl rfl holideControl_fresh holideControl_typeFresh _

/-- The end-to-end theorem, typed, at the controls. -/
theorem holide_predicate_typed_conv :
    Conv (holideControl.typedTheory TwoRoutes.holTheory "type")
      (holideControl.translate predicateRedex) (holideControl.translate predicateContractum) :=
  ((holide_typed_conv_iff holideControl rfl rfl holideControl_fresh holideControl_typeFresh
    predicateRedex predicateContractum).2.2).mpr
    (.rel _ _ ⟨.andLeft .top
      (.beta (.app (.const ControlConst.pred) (.var .vz)) (.const ControlConst.point))⟩)

theorem sttfaControl_fresh (s : Symbol Unit ControlConst) :
    sttfaControl.name s ≠ "eta" ∧ sttfaControl.name s ≠ "etap" ∧ sttfaControl.name s ≠ "eps" := by
  cases s <;> (try (rename_i c; cases c)) <;> simp [sttfaControl, controlEncoding, controlName]

theorem sttfaControl_typeFresh (s : Symbol Unit ControlConst) : sttfaControl.name s ≠ "type" := by
  cases s <;> (try (rename_i c; cases c)) <;> simp [sttfaControl, controlEncoding, controlName]

/-- **The declared type of `impl` is the source's, up to conversion**: the
encoding declares `impl : eta (arrow bool (arrow bool bool))`, the theory file
`eta bool → eta bool → eta bool`. -/
theorem sttfa_impl_type_conv :
    Conv TranslationTransport.STTfa.theory
      (sttfaControl.declaredType (.con "type") .imp)
      (.pi (.app (.con "eta") (.con "bool"))
        (.pi (.app (.con "eta") (.con "bool")) (.app (.con "eta") (.con "bool")))) := by
  have outer := sttfa_eta_arrow (.con "bool")
    (.app (.app (.con "arrow") (.con "bool")) (.con "bool"))
  have inner := sttfa_eta_arrow (.con "bool") (.con "bool")
  simp only [LFTyping.lift] at outer inner
  exact Reduces.conv (outer.trans (Reduces.pi .refl inner))

/-- **The declared type of `forall` is the source's, up to conversion**: the
encoding declares `forall : Π t : type. eta (arrow (arrow t bool) bool)`, the
theory file `Π t : type. (eta t → eta bool) → eta bool`. -/
theorem sttfa_forall_type_conv :
    Conv TranslationTransport.STTfa.theory
      (sttfaControl.declaredType (.con "type") .all)
      (.pi (.con "type") (.pi (.pi (.app (.con "eta") (.var 0)) (.app (.con "eta") (.con "bool")))
        (.app (.con "eta") (.con "bool")))) := by
  have outer := sttfa_eta_arrow (.app (.app (.con "arrow") (.var 0)) (.con "bool")) (.con "bool")
  have inner := sttfa_eta_arrow (.var 0) (.con "bool")
  simp only [LFTyping.lift] at outer inner
  exact Reduces.conv (Reduces.pi .refl (outer.trans (Reduces.pi inner .refl)))

/-- `(λ x. pred x) point`, typed in the STTfa hub's encoding of the controls. -/
theorem sttfa_predicate_typed :
    LambdaPiModulo (sttfaControl.typedTheory TranslationTransport.STTfa.theory "type")
      (sttfaControl.ctx []) (sttfaControl.translate predicateRedex)
      (sttfaControl.El (sttfaControl.code .prop)) :=
  sttfa_translate_typed sttfaControl rfl rfl sttfaControl_fresh sttfaControl_typeFresh _

#print axioms Declares.translate_typed
#print axioms Encoding.declaredType_closed
#print axioms HubTheory.typed_conv_iff
#print axioms holide_translate_typed
#print axioms holide_typed_conv_iff
#print axioms sttfa_translate_typed
#print axioms holideControl_extends
#print axioms holide_predicate_typed
#print axioms holide_predicate_typed_conv
#print axioms sttfa_predicate_typed
#print axioms sttfa_impl_type_conv
#print axioms sttfa_forall_type_conv

end Mettapedia.GSLT.Dedukti.HOLHub
