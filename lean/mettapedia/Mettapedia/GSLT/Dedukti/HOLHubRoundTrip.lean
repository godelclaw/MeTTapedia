import Mettapedia.GSLT.Dedukti.HOLHubPreservation

/-!
# Compile, normalize, decode: the round trip through the STTfa hub
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

/-! ## Layouts are placements -/

/-- Skip the position `cutoff`: the index map of a lift by one at `cutoff`. -/
def shiftAt (cutoff index : Nat) : Nat := if index < cutoff then index else index + 1

theorem lift_var (cutoff index : Nat) : lift 1 cutoff (.var index) = .var (shiftAt cutoff index) := rfl

theorem shiftAt_succ (cutoff index : Nat) : shiftAt (cutoff + 1) (index + 1) = shiftAt cutoff index + 1 := by
  unfold shiftAt
  split_ifs <;> omega

theorem shiftAt_of_lt {cutoff index : Nat} (below : index < cutoff) : shiftAt cutoff index = index := by
  simp [shiftAt, below]

theorem shiftAt_zero (index : Nat) : shiftAt 0 index = index + 1 := by
  simp [shiftAt]

theorem shiftAt_ne (cutoff index : Nat) : shiftAt cutoff index ≠ cutoff := by
  unfold shiftAt
  split_ifs <;> omega

theorem shiftAt_injective (cutoff : Nat) {i j : Nat} (same : shiftAt cutoff i = shiftAt cutoff j) :
    i = j := by
  unfold shiftAt at same
  split_ifs at same <;> omega

variable {Base : Type u} {Const : Ty Base → Type v}

namespace Layout

/-- The index map of placement under `k` local binders. -/
def shiftIndex : {Γ : Ctx Base} → Layout Const Γ → Nat → Nat → Nat
  | _, .base _, _, index => index
  | _, .obj rest _, k, index => rest.shiftIndex (k + 1) index
  | _, .hyp rest _, k, index => shiftAt k (rest.shiftIndex k index)

theorem place_var : ∀ {Γ : Ctx Base} (L : Layout Const Γ) (k index : Nat),
    L.place k (.var index) = .var (L.shiftIndex k index)
  | _, .base _, _, _ => rfl
  | _, .obj rest _, k, index => place_var rest (k + 1) index
  | _, .hyp rest _, k, index => by
      simp only [place, shiftIndex]
      rw [place_var rest k index]
      rfl

theorem shiftIndex_of_lt : ∀ {Γ : Ctx Base} (L : Layout Const Γ) {k index : Nat}, index < k →
    L.shiftIndex k index = index
  | _, .base _, _, _, _ => rfl
  | _, .obj rest _, _, _, below => shiftIndex_of_lt rest (Nat.lt_succ_of_lt below)
  | _, .hyp rest _, _, _, below => by
      simp only [shiftIndex]
      rw [shiftIndex_of_lt rest below, shiftAt_of_lt below]

theorem shiftIndex_succ : ∀ {Γ : Ctx Base} (L : Layout Const Γ) (k index : Nat),
    L.shiftIndex (k + 1) (index + 1) = L.shiftIndex k index + 1
  | _, .base _, _, _ => rfl
  | _, .obj rest _, k, index => shiftIndex_succ rest (k + 1) index
  | _, .hyp rest _, k, index => by
      simp only [shiftIndex]
      rw [shiftIndex_succ rest k index, shiftAt_succ]

theorem place_pi {Γ : Ctx Base} (L : Layout Const Γ) : ∀ (k : Nat) (domain body : LF.Term),
    L.place k (.pi domain body) = .pi (L.place k domain) (L.place (k + 1) body) := by
  induction L with
  | base _ => intro k domain body; rfl
  | obj rest _ ih => intro k domain body; exact ih (k + 1) domain body
  | hyp rest _ ih => intro k domain body; simp only [place, ih, LFTyping.lift]

theorem place_binary_at (e : Encoding Base Const) {Γ : Ctx Base} (L : Layout Const Γ) (k : Nat)
    (s : Symbol Base Const) (a b : LF.Term) :
    L.place k (e.binary s a b) = e.binary s (L.place k a) (L.place k b) := by
  simp only [Encoding.binary, place_app, L.place_closed (t := e.sym s) .con]

/-- **Placement of a translation is the translation of a renaming**, under
`k` local binders. -/
theorem place_translate_general (e : Encoding Base Const) {Γ : Ctx Base} (L : Layout Const Γ) :
    ∀ {Ψ Ψ' : Ctx Base} {τ : Ty Base} (t : Term Const Ψ τ) (k : Nat) (r : HOL.Rename Base Ψ Ψ'),
      (∀ {σ : Ty Base} (v : Var Ψ σ), varIndex (r v) = L.shiftIndex k (varIndex v)) →
      L.place k (e.translate t) = e.translate (HOL.rename r t) := by
  intro Ψ Ψ' τ t
  induction t generalizing Ψ' with
  | var v =>
      intro k r index
      simp only [Encoding.translate, HOL.rename]
      rw [place_var, index]
  | const c => intro k r _; exact L.place_closed .con k
  | app f a ihf iha =>
      intro k r index
      simp only [Encoding.translate, HOL.rename]
      rw [place_app, ihf k r index, iha k r index]
  | @lam σ Ψ τ body ih =>
      intro k r index
      simp only [Encoding.translate, HOL.rename]
      rw [place_lam, L.place_closed (e.El_code_closed σ), ih (k + 1) (HOL.Rename.lift r) (by
        intro ρ v
        cases v with
        | vz => simp [HOL.Rename.lift, varIndex, shiftIndex_of_lt L (Nat.succ_pos k)]
        | vs w => simp [HOL.Rename.lift, varIndex, index w, shiftIndex_succ])]
  | top => intro k r _; exact L.place_closed .con k
  | bot => intro k r _; exact L.place_closed .con k
  | and p q ihp ihq =>
      intro k r index
      simp only [Encoding.translate, HOL.rename]
      rw [place_binary_at e L k, ihp k r index, ihq k r index]
  | or p q ihp ihq =>
      intro k r index
      simp only [Encoding.translate, HOL.rename]
      rw [place_binary_at e L k, ihp k r index, ihq k r index]
  | imp p q ihp ihq =>
      intro k r index
      simp only [Encoding.translate, HOL.rename]
      rw [place_binary_at e L k, ihp k r index, ihq k r index]
  | not p ih =>
      intro k r index
      simp only [Encoding.translate, HOL.rename, Encoding.sym]
      rw [place_app, L.place_closed (t := .con _) .con k, ih k r index]
  | @eq Ψ τ l r' ihl ihr =>
      intro k r index
      simp only [Encoding.translate, HOL.rename, Encoding.equation, Encoding.sym]
      rw [place_app, place_app, place_app, L.place_closed (t := .con _) .con k,
        L.place_closed (e.code_closed τ) k, ihl k r index, ihr k r index]
  | @all σ Ψ body ih =>
      intro k r index
      simp only [Encoding.translate, HOL.rename, Encoding.binder, Encoding.sym]
      rw [place_app, place_app, place_lam, L.place_closed (t := .con _) .con k,
        L.place_closed (e.code_closed σ) k,
        L.place_closed (e.El_code_closed σ) k, ih (k + 1) (HOL.Rename.lift r) (by
          intro ρ v
          cases v with
          | vz => simp [HOL.Rename.lift, varIndex, shiftIndex_of_lt L (Nat.succ_pos k)]
          | vs w => simp [HOL.Rename.lift, varIndex, index w, shiftIndex_succ])]
  | @ex σ Ψ body ih =>
      intro k r index
      simp only [Encoding.translate, HOL.rename, Encoding.binder, Encoding.sym]
      rw [place_app, place_app, place_lam, L.place_closed (t := .con _) .con k,
        L.place_closed (e.code_closed σ) k,
        L.place_closed (e.El_code_closed σ) k, ih (k + 1) (HOL.Rename.lift r) (by
          intro ρ v
          cases v with
          | vz => simp [HOL.Rename.lift, varIndex, shiftIndex_of_lt L (Nat.succ_pos k)]
          | vs w => simp [HOL.Rename.lift, varIndex, index w, shiftIndex_succ])]

/-- The variables of the framework in the scope of a layout, as a HOL context:
each object at its type, each hypothesis at `prop`. -/
def toCtx : {Γ : Ctx Base} → Layout Const Γ → Ctx Base
  | _, .base Γ => Γ
  | _, .obj rest σ => σ :: rest.toCtx
  | _, .hyp rest _ => .prop :: rest.toCtx

/-- The placement of the objects of a layout among the variables of the
framework. -/
def toRename : {Γ : Ctx Base} → (L : Layout Const Γ) → HOL.Rename Base Γ L.toCtx
  | _, .base _ => fun v => v
  | _, .obj rest _ => HOL.Rename.lift rest.toRename
  | _, .hyp rest _ => fun v => .vs (rest.toRename v)

theorem toRename_index : ∀ {Γ : Ctx Base} (L : Layout Const Γ) {σ : Ty Base} (v : Var Γ σ),
    varIndex (L.toRename v) = L.shiftIndex 0 (varIndex v)
  | _, .base _, _, _ => rfl
  | _, .obj rest _, _, v => by
      cases v with
      | vz => simp [toRename, HOL.Rename.lift, varIndex, shiftIndex, shiftIndex_of_lt rest Nat.one_pos]
      | vs w =>
          simp only [toRename, HOL.Rename.lift, varIndex, shiftIndex]
          rw [toRename_index rest w, shiftIndex_succ]
  | _, .hyp rest _, _, v => by
      simp only [toRename, varIndex, shiftIndex]
      rw [toRename_index rest v, shiftAt_zero]

/-- **Placing a translation over a layout is translating the placed term.** -/
theorem place_translate (e : Encoding Base Const) {Γ : Ctx Base} (L : Layout Const Γ)
    {τ : Ty Base} (t : Term Const Γ τ) :
    L.place 0 (e.translate t) = e.translate (HOL.rename L.toRename t) :=
  L.place_translate_general e t 0 L.toRename (L.toRename_index)

end Layout

/-! ## Normal forms of compiled proofs -/

/-- A chosen β-normal form of a HOL term. -/
noncomputable def nf {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) : Term Const Γ τ :=
  Classical.choose (exists_normalForm t)

theorem nf_reduces {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    HOL.BetaNormalization.ReducesStar t (nf t) :=
  (Classical.choose_spec (exists_normalForm t)).1

theorem nf_normal {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    HOL.BetaNormalization.Normal (nf t) :=
  (Classical.choose_spec (exists_normalForm t)).2

/-- A proof whose last rule is an introduction, through retyping steps. -/
def IsIntro : {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} → {φ : Formula Const Γ} →
    HOL.ProofSyntaxModulo [] Δ φ → Prop
  | _, _, _, .impI _ => True
  | _, _, _, .allI _ => True
  | _, _, _, .convert _ inner => IsIntro inner
  | _, _, _, _ => False

/-- **A proof without detours**: no introduction is eliminated directly,
through retyping steps. -/
def DetourFree : {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} → {φ : Formula Const Γ} →
    HOL.ProofSyntaxModulo [] Δ φ → Prop
  | _, _, _, .hyp _ => True
  | _, _, _, .impI body => DetourFree body
  | _, _, _, .impE function argument => ¬ IsIntro function ∧ DetourFree function ∧ DetourFree argument
  | _, _, _, .allI body => DetourFree body
  | _, _, _, .allE _ function => ¬ IsIntro function ∧ DetourFree function
  | _, _, _, .convert _ inner => DetourFree inner

/-- A proof whose ∀-witnesses are core terms. -/
def CoreWitnesses : {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} → {φ : Formula Const Γ} →
    HOL.ProofSyntaxModulo [] Δ φ → Prop
  | _, _, _, .hyp _ => True
  | _, _, _, .impI body => CoreWitnesses body
  | _, _, _, .impE function argument => CoreWitnesses function ∧ CoreWitnesses argument
  | _, _, _, .allI body => CoreWitnesses body
  | _, _, _, .allE t function => t.isCore = true ∧ CoreWitnesses function
  | _, _, _, .convert _ inner => CoreWitnesses inner

/-- **The normal form of a compiled proof**, computed: the compiled proof with
every type of proofs and every ∀-witness in normal form. -/
noncomputable def normalCompile (e : Encoding Base Const) (base : Symbol Base Const → LF.Term) :
    {Γ : Ctx Base} → {Δ : List (Formula Const Γ)} → {φ : Formula Const Γ} →
    HOL.ProofSyntaxModulo [] Δ φ → Layout Const Γ → (Fin Δ.length → Nat) → LF.Term
  | _, _, _, .hyp occurrence, _, hypVar => .var (hypVar occurrence)
  | _, _, _, .impI (φ := premise) body, L, hypVar =>
      .lam (e.epsNF base (HOL.rename L.toRename (nf premise)))
        (normalCompile e base body (L.hyp premise) (Fin.cases 0 fun i => hypVar i + 1))
  | _, _, _, .impE function argument, L, hypVar =>
      .app (normalCompile e base function L hypVar) (normalCompile e base argument L hypVar)
  | _, _, _, .allI (σ := σ) body, L, hypVar =>
      .lam (Encoding.elNF base σ)
        (normalCompile e base body (L.obj σ) fun i =>
          hypVar (i.cast (by simp [HOL.weakenHyps])) + 1)
  | _, _, _, .allE t function, L, hypVar =>
      .app (normalCompile e base function L hypVar)
        (e.translateNF base (HOL.rename L.toRename (nf t)))
  | _, _, _, .convert _ inner, L, hypVar => normalCompile e base inner L hypVar

section Normalize

variable {e : Encoding Base Const} (names : SttfaNames e)
include names

/-- The type of the proofs of a placed formula reduces to the normal type of the
proofs of its placed normal form. -/
theorem eps_reduces_nf {Γ Θ : Ctx Base} (ρ : HOL.Rename Base Γ Θ) (φ : Formula Const Γ) :
    Reduces STTfa.theory (.app (.con "eps") (e.translate (HOL.rename ρ φ)))
      (e.epsNF names.base (HOL.rename ρ (nf φ))) :=
  sttfa_reduces_of_conv (eps_conv_normalForm names ρ φ (nf_reduces φ))
    (epsNF_normal_all names _ (HOL.BetaNormalization.normal_rename ρ (nf_normal φ)))

/-- **A compiled proof reduces to its computed normal form.** -/
theorem compile_reduces_normalCompile : ∀ {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (d : HOL.ProofSyntaxModulo [] Δ φ) (L : Layout Const Γ)
    (hypVar : Fin Δ.length → Nat),
    Reduces STTfa.theory (compile e "eps" d L hypVar) (normalCompile e names.base d L hypVar) := by
  intro Γ Δ φ d
  induction d with
  | hyp _ => intro L hypVar; exact .refl
  | @impI Γ Δ premise conclusion body ih =>
      intro L hypVar
      simp only [compile, normalCompile]
      rw [L.place_translate e]
      exact Reduces.lam (eps_reduces_nf names L.toRename premise) (ih _ _)
  | impE function argument ihFunction ihArgument =>
      intro L hypVar
      exact Reduces.app (ihFunction L hypVar) (ihArgument L hypVar)
  | @allI Γ Δ σ body inner ih =>
      intro L hypVar
      exact Reduces.lam (names.hub.reduces_El_code σ) (ih _ _)
  | @allE Γ Δ σ body t function ih =>
      intro L hypVar
      simp only [compile, normalCompile]
      rw [L.place_translate e]
      exact Reduces.app (ih L hypVar)
        ((Encoding.translate_reduces (HOL.BetaNormalization.star_rename L.toRename
          (nf_reduces t))).trans (names.hub.reduces_translateNF _))
  | convert _ inner ih => intro L hypVar; exact ih L hypVar

/-- **The computed normal form of a compiled proof is coded**, when its
∀-witnesses are core and the hypotheses sit at no place of an object. -/
theorem normalCompile_coded : ∀ {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (d : HOL.ProofSyntaxModulo [] Δ φ), CoreWitnesses d →
    ∀ (L : Layout Const Γ) (hypVar : Fin Δ.length → Nat),
      (∀ (i : Fin Δ.length) {σ : Ty Base} (v : Var Γ σ), varIndex (L.toRename v) ≠ hypVar i) →
      Coded names (@L.toRename) (normalCompile e names.base d L hypVar) := by
  intro Γ Δ φ d
  induction d with
  | hyp occurrence =>
      intro _ L hypVar avoid
      exact .hyp fun v same => avoid occurrence v same
  | @impI Γ Δ premise conclusion body ih =>
      intro core L hypVar avoid
      refine .lamHyp (epsNF_proofShape names _) (ih core (L.hyp premise) _ ?_)
      intro i σ v
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [Layout.toRename, varIndex]
      · simp only [Fin.cases_succ, Layout.toRename, varIndex]
        exact fun same => avoid j v (Nat.succ_injective same)
  | impE function argument ihFunction ihArgument =>
      intro core L hypVar avoid
      exact .appProof (ihFunction core.1 L hypVar avoid) (ihArgument core.2 L hypVar avoid)
  | @allI Γ Δ σ body inner ih =>
      intro core L hypVar avoid
      refine .lamObj σ (ih core (L.obj σ) _ ?_)
      intro i τ v
      cases v with
      | vz => simp [Layout.toRename, HOL.Rename.lift, varIndex]
      | vs w =>
          simp only [Layout.toRename, HOL.Rename.lift, varIndex]
          exact fun same => avoid _ w (Nat.succ_injective same)
  | @allE Γ Δ σ body t function ih =>
      intro core L hypVar avoid
      exact .appObj (nf t) (HOL.Term.isCore_of_reducesStar (nf_reduces t) core.1)
        (ih core.2 L hypVar avoid)
  | convert _ inner ih =>
      intro core L hypVar avoid
      exact ih core L hypVar avoid

theorem normalCompile_headConst : ∀ {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (d : HOL.ProofSyntaxModulo [] Δ φ) (L : Layout Const Γ)
    (hypVar : Fin Δ.length → Nat), headConst (normalCompile e names.base d L hypVar) = none := by
  intro Γ Δ φ d
  induction d with
  | hyp _ => intro L hypVar; rfl
  | impI _ _ => intro L hypVar; rfl
  | impE function argument ihFunction _ =>
      intro L hypVar
      simp only [normalCompile, headConst]
      exact ihFunction L hypVar
  | allI _ _ => intro L hypVar; rfl
  | allE t function ih =>
      intro L hypVar
      simp only [normalCompile, headConst]
      exact ih L hypVar
  | convert _ inner ih => intro L hypVar; exact ih L hypVar

theorem normalCompile_not_lam : ∀ {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (d : HOL.ProofSyntaxModulo [] Δ φ), ¬ IsIntro d →
    ∀ (L : Layout Const Γ) (hypVar : Fin Δ.length → Nat) (domain body : LF.Term),
      normalCompile e names.base d L hypVar ≠ .lam domain body := by
  intro Γ Δ φ d
  induction d with
  | hyp _ => intro _ L hypVar domain body same; cases same
  | impI _ _ => intro notIntro; exact absurd trivial notIntro
  | impE _ _ _ _ => intro _ L hypVar domain body same; cases same
  | allI _ _ => intro notIntro; exact absurd trivial notIntro
  | allE _ _ _ => intro _ L hypVar domain body same; cases same
  | convert _ inner ih => intro notIntro L hypVar domain body; exact ih notIntro L hypVar domain body

/-- **The computed normal form of a detour-free compiled proof is normal.** -/
theorem normalCompile_normal : ∀ {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (d : HOL.ProofSyntaxModulo [] Δ φ), DetourFree d →
    ∀ (L : Layout Const Γ) (hypVar : Fin Δ.length → Nat),
      IsNormal (Step STTfa.theory) (normalCompile e names.base d L hypVar) := by
  have headed := STTfa.orthogonal.leftAlgebraic.headed
  have appNormal : ∀ {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
      (d : HOL.ProofSyntaxModulo [] Δ φ) (L : Layout Const Γ) (hypVar : Fin Δ.length → Nat)
      (argument : LF.Term), ¬ IsIntro d →
      IsNormal (Step STTfa.theory) (normalCompile e names.base d L hypVar) →
      IsNormal (Step STTfa.theory) argument →
      IsNormal (Step STTfa.theory) (.app (normalCompile e names.base d L hypVar) argument) := by
    intro Γ Δ φ d L hypVar argument notIntro functionNormal argumentNormal target step
    rcases step.app_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
    · rcases root.headConst_or_beta headed with ⟨domain, body, _, same⟩ | ⟨name, head⟩
      · simp only [LF.Term.app.injEq] at same
        exact normalCompile_not_lam names d notIntro L hypVar domain body same.1
      · simp only [headConst] at head
        rw [normalCompile_headConst names d L hypVar] at head
        cases head
    · exact functionNormal _ inner
    · exact argumentNormal _ inner
  intro Γ Δ φ d
  induction d with
  | hyp _ => intro _ L hypVar; exact var_normal headed _
  | @impI Γ Δ premise conclusion body ih =>
      intro free L hypVar target step
      rcases step.lam_inv with root | ⟨_, inner, _⟩ | ⟨_, inner, _⟩
      · exact RootStep.not_lam headed root
      · exact epsNF_normal_all names _
          (HOL.BetaNormalization.normal_rename _ (nf_normal premise)) _ inner
      · exact ih free _ _ _ inner
  | impE function argument ihFunction ihArgument =>
      intro free L hypVar
      exact appNormal function L hypVar _ free.1 (ihFunction free.2.1 L hypVar)
        (ihArgument free.2.2 L hypVar)
  | @allI Γ Δ σ body inner ih =>
      intro free L hypVar target step
      rcases step.lam_inv with root | ⟨_, inner', _⟩ | ⟨_, inner', _⟩
      · exact RootStep.not_lam headed root
      · exact names.hub.elNF_normal σ _ inner'
      · exact ih free _ _ _ inner'
  | @allE Γ Δ σ body t function ih =>
      intro free L hypVar
      exact appNormal function L hypVar _ free.1 (ih free.2 L hypVar)
        (names.hub.translateNF_normal _
          (HOL.BetaNormalization.normal_rename _ (nf_normal t)))
  | convert _ inner ih => intro free L hypVar; exact ih free L hypVar

end Normalize

/-! ## The round trip -/

section RoundTrip

variable {e : Encoding Base Const} (names : SttfaNames e)
include names

/-- **Compile, normalize, decode.**  A detour-free theorem whose ∀-witnesses and
conclusion are core compiles to a term that reduces to a normal, coded term of
the type of the proofs of its conclusion, which decodes to a proof of it. -/
theorem sttfa_round_trip {φ : Formula Const []} (coreφ : φ.isCore = true)
    (d : HOL.ProofSyntaxModulo [] [] φ) (free : DetourFree d) (core : CoreWitnesses d) :
    Reduces (sttfaProofTheory e) (compile e "eps" d (.base []) Fin.elim0)
        (normalCompile e names.base d (.base []) Fin.elim0) ∧
      IsNormal (Step (sttfaProofTheory e)) (normalCompile e names.base d (.base []) Fin.elim0) ∧
      Coded names (HOL.Rename.id (Γ := [])) (normalCompile e names.base d (.base []) Fin.elim0) ∧
      LambdaPiModulo (sttfaProofTheory e) [] (normalCompile e names.base d (.base []) Fin.elim0)
        (.app (.con "eps") (e.translate φ)) ∧
      Nonempty (HOL.ProofSyntaxModulo [] [] φ) := by
  have reduces := reduces_toProofTheory (e := e) (compile_reduces_normalCompile names d (.base []) Fin.elim0)
  have normal : IsNormal (Step (sttfaProofTheory e)) (normalCompile e names.base d (.base []) Fin.elim0) := by
    rw [step_proofTheory]
    exact normalCompile_normal names d free (.base []) Fin.elim0
  have coded : Coded names (HOL.Rename.id (Γ := [])) (normalCompile e names.base d (.base []) Fin.elim0) :=
    normalCompile_coded names d core (.base []) Fin.elim0 (fun i => i.elim0)
  have proofs := sttfaProofHub e names.el names.arrow names.imp names.all names.fresh names.typeFresh
  have typed := sttfa_typePreservation names .nil (proofs.theorem_typed d) reduces
  exact ⟨reduces, normal, coded, typed,
    sttfa_adequate_coded names (Δ := []) (fun _ member => absurd member List.not_mem_nil) coreφ
      coded normal typed⟩

/-- **Every normal form of a detour-free compiled theorem is its computed normal
form, so it is coded.** -/
theorem compile_normalForm_coded {φ : Formula Const []} (d : HOL.ProofSyntaxModulo [] [] φ)
    (free : DetourFree d) (core : CoreWitnesses d) {N : LF.Term}
    (reduces : Reduces (sttfaProofTheory e) (compile e "eps" d (.base []) Fin.elim0) N)
    (normal : IsNormal (Step (sttfaProofTheory e)) N) :
    N = normalCompile e names.base d (.base []) Fin.elim0 ∧
      Coded names (HOL.Rename.id (Γ := [])) N := by
  have computed := reduces_toProofTheory (e := e)
    (compile_reduces_normalCompile names d (.base []) Fin.elim0)
  have computedNormal : IsNormal (Step (sttfaProofTheory e))
      (normalCompile e names.base d (.base []) Fin.elim0) := by
    rw [step_proofTheory]
    exact normalCompile_normal names d free (.base []) Fin.elim0
  have same := normal_form_unique (proofTheory_confluent e) reduces normal computed computedNormal
  subst same
  exact ⟨rfl, normalCompile_coded names d core (.base []) Fin.elim0 (fun i => i.elim0)⟩

end RoundTrip

/-! ## Controls -/

theorem predInstanceProof_detourFree : DetourFree predInstanceProof :=
  ⟨fun intro => intro, trivial⟩

theorem predInstanceProof_coreWitnesses : CoreWitnesses predInstanceProof :=
  ⟨rfl, trivial⟩

/-- **The round trip at a ∀-witness**: the compiled proof of
`(∀ x. pred x) ⇒ pred point` normalizes to a normal coded term that decodes. -/
theorem predInstance_round_trip :
    IsNormal (Step (sttfaProofTheory sttfaControl))
        (normalCompile sttfaControl sttfaControl_names.base predInstanceProof (.base []) Fin.elim0) ∧
      Coded sttfaControl_names (HOL.Rename.id (Γ := []))
        (normalCompile sttfaControl sttfaControl_names.base predInstanceProof (.base []) Fin.elim0) ∧
      Nonempty (HOL.ProofSyntaxModulo [] ([] : List (Formula ControlConst []))
        (.imp (.all predVar) predPoint)) :=
  let trip := sttfa_round_trip sttfaControl_names (φ := .imp (.all predVar) predPoint) rfl
    predInstanceProof predInstanceProof_detourFree predInstanceProof_coreWitnesses
  ⟨trip.2.1, trip.2.2.1, trip.2.2.2.2⟩

theorem predSelfProof_detourFree : DetourFree predSelfProof := trivial

theorem predSelfProof_coreWitnesses : CoreWitnesses predSelfProof := trivial

/-- **The round trip at a ∀-introduction**: the compiled proof of
`∀ x. pred x ⇒ pred x` normalizes to a normal coded term that decodes. -/
theorem predSelf_round_trip :
    IsNormal (Step (sttfaProofTheory sttfaControl))
        (normalCompile sttfaControl sttfaControl_names.base predSelfProof (.base []) Fin.elim0) ∧
      Coded sttfaControl_names (HOL.Rename.id (Γ := []))
        (normalCompile sttfaControl sttfaControl_names.base predSelfProof (.base []) Fin.elim0) ∧
      Nonempty (HOL.ProofSyntaxModulo [] ([] : List (Formula ControlConst []))
        (.all (.imp predVar predVar))) :=
  let trip := sttfa_round_trip sttfaControl_names (φ := .all (.imp predVar predVar)) rfl
    predSelfProof predSelfProof_detourFree predSelfProof_coreWitnesses
  ⟨trip.2.1, trip.2.2.1, trip.2.2.2.2⟩

#print axioms Layout.place_translate
#print axioms normalCompile_coded
#print axioms normalCompile_normal
#print axioms sttfa_round_trip
#print axioms compile_normalForm_coded
#print axioms predInstance_round_trip
#print axioms predSelf_round_trip

end Mettapedia.GSLT.Dedukti.HOLHub
