import Mathlib.Tactic.FinCases
import Mettapedia.Protocols.Symbolic.Message

/-!
# Normal forms for the destructor equations

The destructor part of the Dolev–Yao theory, `fst ⟨x, y⟩ = x`, `snd ⟨x, y⟩ = y`,
`sdec k (senc k m) = m` and `verify (pk k) (sign k m) = m` (`destructorEquations`), is decided
by normalization, as DyLean's method prescribes (Wallez, Cremers, IACR ePrint 2026/1493, §2.2).
Each symbol gets a normalizing constructor (`normalizing`): a destructor applied to an argument of
the matching shape returns the component, any other application is left as it is, and every
other symbol builds its term. The three local conditions of `isNormalizer_normalizeWith` hold
(`isNormalizer_normalForm`), so two messages are equal modulo the destructor equations exactly
when their normal forms coincide (`eqMod_iff`), and that equality is decidable.

The normal forms here are those of the free term model: a destructor applied to a term of the
wrong shape stays as a term. The message type `Msg` of `Symbolic.Message` collapses all such
terms into `fail`; evaluation in `Msg` does not see the difference between a term and its normal
form (`realize_normalForm`). Diffie–Hellman commutation is not covered: its normal forms need a
canonical order on exponents.
-/

namespace Mettapedia.Protocols.Symbolic.Destructors

open FirstOrder FirstOrder.Language DYEq

variable {N : Type} [DecidableEq N]

/-- Messages of the term model: Dolev–Yao terms over the names `N`. -/
abbrev T (N : Type) := dyLanguage.Term N

/-- Recognizes a pair. -/
def pairView : T N → Option (T N × T N)
  | Term.func DYFun.pair ts => some (ts 0, ts 1)
  | _ => none

/-- Recognizes a ciphertext, returning key and plaintext. -/
def sencView : T N → Option (T N × T N)
  | Term.func DYFun.senc ts => some (ts 0, ts 1)
  | _ => none

/-- Recognizes a signature, returning key and message. -/
def signView : T N → Option (T N × T N)
  | Term.func DYFun.sign ts => some (ts 0, ts 1)
  | _ => none

omit [DecidableEq N] in
theorem fin1_eq (ts : Fin 1 → T N) : ts = ![ts 0] := by
  funext i; fin_cases i; rfl

omit [DecidableEq N] in
theorem fin2_eq (ts : Fin 2 → T N) : ts = ![ts 0, ts 1] := by
  funext i; fin_cases i <;> rfl

omit [DecidableEq N] in
theorem const_fin1 (t : T N) : (fun _ : Fin 1 => t) = ![t] := by
  funext i; fin_cases i; rfl

omit [DecidableEq N] in
theorem subst_vec1 (t : dyLanguage.Term ℕ) (σ : ℕ → T N) :
    (fun i : Fin 1 => (![t] i).subst σ) = ![t.subst σ] := by
  funext i; fin_cases i; rfl

omit [DecidableEq N] in
theorem subst_vec2 (t u : dyLanguage.Term ℕ) (σ : ℕ → T N) :
    (fun i : Fin 2 => (![t, u] i).subst σ) = ![t.subst σ, u.subst σ] := by
  funext i; fin_cases i <;> rfl

omit [DecidableEq N] in
theorem pairView_eq_some {t a b : T N} :
    pairView t = some (a, b) ↔ t = Term.func DYFun.pair ![a, b] := by
  constructor
  · intro h
    unfold pairView at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact congrArg _ (fin2_eq _)
    · simp at h
  · rintro rfl
    simp [pairView]

omit [DecidableEq N] in
theorem sencView_eq_some {t a b : T N} :
    sencView t = some (a, b) ↔ t = Term.func DYFun.senc ![a, b] := by
  constructor
  · intro h
    unfold sencView at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact congrArg _ (fin2_eq _)
    · simp at h
  · rintro rfl
    simp [sencView]

omit [DecidableEq N] in
theorem signView_eq_some {t a b : T N} :
    signView t = some (a, b) ↔ t = Term.func DYFun.sign ![a, b] := by
  constructor
  · intro h
    unfold signView at h
    split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact congrArg _ (fin2_eq _)
    · simp at h
  · rintro rfl
    simp [signView]

/-- The normalizing constructors. -/
def normalizing : ∀ {n}, DYFun n → (Fin n → T N) → T N
  | _, .fst, ts =>
      match pairView (ts 0) with
      | some (a, _) => a
      | none => Term.func DYFun.fst ts
  | _, .snd, ts =>
      match pairView (ts 0) with
      | some (_, b) => b
      | none => Term.func DYFun.snd ts
  | _, .sdec, ts =>
      match sencView (ts 1) with
      | some (k, m) => if k = ts 0 then m else Term.func DYFun.sdec ts
      | none => Term.func DYFun.sdec ts
  | _, .verify, ts =>
      match signView (ts 1) with
      | some (k, m) => if Term.func DYFun.pk ![k] = ts 0 then m else Term.func DYFun.verify ts
      | none => Term.func DYFun.verify ts
  | _, .pk, ts => Term.func DYFun.pk ts
  | _, .pair, ts => Term.func DYFun.pair ts
  | _, .hash, ts => Term.func DYFun.hash ts
  | _, .senc, ts => Term.func DYFun.senc ts
  | _, .sign, ts => Term.func DYFun.sign ts
  | _, .dh, ts => Term.func DYFun.dh ts
  | _, .fail, ts => Term.func DYFun.fail ts

/-- The normal form of a message modulo the destructor equations. -/
def normalForm : T N → T N := normalizeWith normalizing

theorem normalForm_func {n : ℕ} (f : DYFun n) (ts : Fin n → T N) :
    normalForm (Term.func f ts) = normalizing f fun i => normalForm (ts i) := rfl

theorem normalForm_var (a : N) : normalForm (Term.var a : T N) = Term.var a := rfl

/-- A destructor equation instance, with its two pattern variables instantiated by `a` and `b`. -/
def inst2 (a b : T N) : ℕ → T N
  | 0 => a
  | _ => b

omit [DecidableEq N] in
theorem func_inj {n : ℕ} {f : DYFun n} {ts us : Fin n → T N}
    (h : Term.func (L := dyLanguage) f ts = Term.func f us) : ts = us :=
  eq_of_heq (Term.func.inj h).2.2

/-- The arguments of a normal application of a constructor symbol are normal. -/
theorem normal_args {n : ℕ} {f : DYFun n}
    (hf : normalizing f = Term.func (L := dyLanguage) (α := N) f)
    {us : Fin n → T N} (h : normalForm (Term.func f us) = Term.func f us) (j : Fin n) :
    normalForm (us j) = us j := by
  rw [normalForm_func, hf] at h
  exact congrFun (func_inj h) j

theorem mem_fstPair : (app1 .fst (app2 .pair (x 0) (x 1)), x 0) ∈ destructorEquations := by
  simp [destructorEquations]

theorem mem_sndPair : (app1 .snd (app2 .pair (x 0) (x 1)), x 1) ∈ destructorEquations := by
  simp [destructorEquations]

theorem mem_sdecSenc :
    (app2 .sdec (x 0) (app2 .senc (x 0) (x 1)), x 1) ∈ destructorEquations := by
  simp [destructorEquations]

theorem mem_verifySign :
    (app2 .verify (app1 .pk (x 0)) (app2 .sign (x 0) (x 1)), x 1) ∈ destructorEquations := by
  simp [destructorEquations]

/-- The normalizing constructors are a normalization function for the destructor equations. -/
theorem isNormalizer_normalForm : IsNormalizer destructorEquations (normalForm (N := N)) := by
  apply isNormalizer_normalizeWith
  · -- instances of the equations get equal normal forms
    intro l r hlr σ
    simp only [destructorEquations, Set.mem_insert_iff, Set.mem_singleton_iff,
      Prod.mk.injEq] at hlr
    rcases hlr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp [normalizeWith, normalizing, pairView, sencView, signView, const_fin1]
  · -- each normalizing constructor is sound modulo the equations
    intro n f ts
    cases f with
    | fst =>
        show EqMod _ (normalizing DYFun.fst ts) _
        cases hv : pairView (ts 0) with
        | none => simpa [normalizing, hv] using EqMod.refl _
        | some ab =>
            obtain ⟨a, b⟩ := ab
            have h0 := pairView_eq_some.mp hv
            have e := (EqMod.inst mem_fstPair (inst2 a b)).symm
            rw [fin1_eq ts, h0]
            simpa [normalizing, pairView, inst2, subst_vec1, subst_vec2, const_fin1] using e
    | snd =>
        show EqMod _ (normalizing DYFun.snd ts) _
        cases hv : pairView (ts 0) with
        | none => simpa [normalizing, hv] using EqMod.refl _
        | some ab =>
            obtain ⟨a, b⟩ := ab
            have h0 := pairView_eq_some.mp hv
            have e := (EqMod.inst mem_sndPair (inst2 a b)).symm
            rw [fin1_eq ts, h0]
            simpa [normalizing, pairView, inst2, subst_vec1, subst_vec2, const_fin1] using e
    | sdec =>
        show EqMod _ (normalizing DYFun.sdec ts) _
        cases hv : sencView (ts 1) with
        | none => simpa [normalizing, hv] using EqMod.refl _
        | some km =>
            obtain ⟨k, m⟩ := km
            by_cases hk : k = ts 0
            · have h1 := sencView_eq_some.mp hv
              have e := (EqMod.inst mem_sdecSenc (inst2 k m)).symm
              rw [fin2_eq ts, h1, ← hk]
              simpa [normalizing, sencView, inst2, subst_vec1, subst_vec2, const_fin1] using e
            · simpa [normalizing, hv, hk] using EqMod.refl _
    | verify =>
        show EqMod _ (normalizing DYFun.verify ts) _
        cases hv : signView (ts 1) with
        | none => simpa [normalizing, hv] using EqMod.refl _
        | some km =>
            obtain ⟨k, m⟩ := km
            by_cases hk : Term.func DYFun.pk ![k] = ts 0
            · have h1 := signView_eq_some.mp hv
              have e := (EqMod.inst mem_verifySign (inst2 k m)).symm
              rw [fin2_eq ts, h1, ← hk]
              simpa [normalizing, signView, inst2, subst_vec1, subst_vec2, const_fin1] using e
            · simpa [normalizing, hv, hk] using EqMod.refl _
    | pk => exact EqMod.refl _
    | pair => exact EqMod.refl _
    | hash => exact EqMod.refl _
    | senc => exact EqMod.refl _
    | sign => exact EqMod.refl _
    | dh => exact EqMod.refl _
    | fail => exact EqMod.refl _
  · -- normalizing constructors map normal arguments to normal results
    intro n f ts hts
    have hts' : (fun i => normalForm (ts i)) = ts := funext hts
    change normalForm (normalizing f ts) = normalizing f ts
    cases f with
    | fst =>
        cases hv : pairView (ts 0) with
        | none =>
            simp only [normalizing, hv]
            rw [normalForm_func, hts']
            simp [normalizing, hv]
        | some ab =>
            obtain ⟨a, b⟩ := ab
            have h0 := pairView_eq_some.mp hv
            simp only [normalizing, hv]
            have := normal_args (f := DYFun.pair) rfl (h0 ▸ hts 0) 0
            simpa using this
    | snd =>
        cases hv : pairView (ts 0) with
        | none =>
            simp only [normalizing, hv]
            rw [normalForm_func, hts']
            simp [normalizing, hv]
        | some ab =>
            obtain ⟨a, b⟩ := ab
            have h0 := pairView_eq_some.mp hv
            simp only [normalizing, hv]
            have := normal_args (f := DYFun.pair) rfl (h0 ▸ hts 0) 1
            simpa using this
    | sdec =>
        cases hv : sencView (ts 1) with
        | none =>
            simp only [normalizing, hv]
            rw [normalForm_func, hts']
            simp [normalizing, hv]
        | some km =>
            obtain ⟨k, m⟩ := km
            by_cases hk : k = ts 0
            · have h1 := sencView_eq_some.mp hv
              simp only [normalizing, hv, hk, if_true]
              have := normal_args (f := DYFun.senc) rfl (h1 ▸ hts 1) 1
              simpa using this
            · simp only [normalizing, hv, hk, if_false]
              rw [normalForm_func, hts']
              simp [normalizing, hv, hk]
    | verify =>
        cases hv : signView (ts 1) with
        | none =>
            simp only [normalizing, hv]
            rw [normalForm_func, hts']
            simp [normalizing, hv]
        | some km =>
            obtain ⟨k, m⟩ := km
            by_cases hk : Term.func DYFun.pk ![k] = ts 0
            · have h1 := signView_eq_some.mp hv
              simp only [normalizing, hv, hk, if_true]
              have := normal_args (f := DYFun.sign) rfl (h1 ▸ hts 1) 1
              simpa using this
            · simp only [normalizing, hv, hk, if_false]
              rw [normalForm_func, hts']
              simp [normalizing, hv, hk]
    | pk => rw [normalizing, normalForm_func, hts']; rfl
    | pair => rw [normalizing, normalForm_func, hts']; rfl
    | hash => rw [normalizing, normalForm_func, hts']; rfl
    | senc => rw [normalizing, normalForm_func, hts']; rfl
    | sign => rw [normalizing, normalForm_func, hts']; rfl
    | dh => rw [normalizing, normalForm_func, hts']; rfl
    | fail => rw [normalizing, normalForm_func, hts']; rfl

/-- Equality modulo the destructor equations is equality of normal forms. -/
theorem eqMod_iff {t u : T N} : EqMod destructorEquations t u ↔ normalForm t = normalForm u :=
  isNormalizer_normalForm.eqMod_iff

/-- Equality modulo the destructor equations is decidable. -/
instance : DecidableRel (EqMod (N := N) destructorEquations) :=
  fun _ _ => decidable_of_iff _ eqMod_iff.symm

/-- Evaluation in the message algebra `Msg` does not distinguish a term from its normal form. -/
theorem realize_normalForm (t : T N) :
    (normalForm t).realize Msg.name = t.realize Msg.name := by
  have hsat : Satisfies (Msg N) destructorEquations :=
    fun e he => satisfies_dyEquations e (Set.mem_insert_of_mem _ he)
  exact ((isNormalizer_normalForm.eqMod_self t).realize_eq hsat Msg.name).symm

end Mettapedia.Protocols.Symbolic.Destructors
