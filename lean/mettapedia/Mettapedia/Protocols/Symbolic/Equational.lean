import Mathlib.ModelTheory.Semantics
import Mettapedia.Protocols.Symbolic.Knowledge

/-!
# Symbolic messages and equational theories

Messages of a symbolic protocol model are terms built by cryptographic function symbols
from *names* (keys, nonces, identities) treated as atoms. Mathlib's first-order terms give
this directly: for a signature `L`, `L.Term N` is the free term algebra over the names `N`.
An equational theory is a set `E` of equations between terms with pattern variables
`0, 1, …`, such as `sdec(k, senc(k, m)) = m`. Two messages are equal modulo `E` (`EqMod E`)
when the least congruence containing all substitution instances of `E` relates them. The
signature and the theory are parameters, so every protocol chooses its own primitives and
equations, as in DyLean.

A theory is decided by a *normalization function* (Wallez, Cremers, *Bob DyLean*, IACR
ePrint 2026/1493, §2.2). Following DyLean's Definition 1, `nf` is one for `E`
(`IsNormalizer`) when the two sides of every instance of an equation have the same normal
form, every message equals its normal form modulo `E`, and normalizing a symbol applied to
normal forms agrees with normalizing the original application. Then two messages are equal
modulo `E` exactly when their normal forms coincide (`IsNormalizer.eqMod_iff`, DyLean's
Theorem 1). Such a function can be assembled bottom-up from one *normalizing constructor*
per symbol whose properties are checked locally (`isNormalizer_normalizeWith`, Theorem 2).
This is what entitles a protocol model to compare messages by syntactic equality of normal
forms while meaning equality modulo the theory.

An algebra `M` (an `L.Structure`) satisfying `E` receives every equality modulo `E`
(`EqMod.realize_eq`). The attacker of the term model applies public symbols and rewrites
modulo `E` (`TermRule`); its deductions map into deductions in every algebra satisfying `E`,
where it applies the same public symbols (`FunRule`, `deducible_realize`). Hence secrecy in
any algebra satisfying `E` implies secrecy in the term model (`secret_of_realize`). A concrete
message type used for proofs may identify more than the theory requires, for instance by
collapsing every failed destructor application into one error value as LeanDY's normalizer
does (Jeanteur, Veronese, Solitro, Maffei, arXiv:2607.03406, §3.1.2); a secrecy proof there
remains a secrecy proof for the symbolic term model.

What is not modelled: this is symbolic, not computational, security. Equal normal forms
mean equal messages and distinct normal forms mean distinct messages; there are no
probabilities, collisions or partial information.
-/

namespace Mettapedia.Protocols.Symbolic

open FirstOrder FirstOrder.Language Structure

/-- An equational theory over the signature `L`: equations between terms whose variables are
pattern variables. -/
abbrev Equations (L : Language.{0, 0}) := Set (L.Term ℕ × L.Term ℕ)

variable {L : Language.{0, 0}} {N : Type}

/-- Equality modulo `E` of messages over the names `N`: the least congruence containing every
substitution instance of an equation of `E`. -/
inductive EqMod (E : Equations L) : L.Term N → L.Term N → Prop
  /-- Every instance of an equation. -/
  | inst {l r : L.Term ℕ} (h : (l, r) ∈ E) (σ : ℕ → L.Term N) : EqMod E (l.subst σ) (r.subst σ)
  | refl (t : L.Term N) : EqMod E t t
  | symm {t u : L.Term N} : EqMod E t u → EqMod E u t
  | trans {t u v : L.Term N} : EqMod E t u → EqMod E u v → EqMod E t v
  /-- Congruence for every function symbol. -/
  | congr {n : ℕ} (f : L.Functions n) {ts us : Fin n → L.Term N} :
      (∀ i, EqMod E (ts i) (us i)) → EqMod E (func f ts) (func f us)

/-- Messages modulo `E`: equality modulo `E` is an equivalence relation. -/
def eqModSetoid (E : Equations L) : Setoid (L.Term N) :=
  ⟨EqMod E, ⟨EqMod.refl, EqMod.symm, EqMod.trans⟩⟩

/-- An algebra satisfies `E` when both sides of every equation agree under every valuation of
the pattern variables. -/
def Satisfies (M : Type) [L.Structure M] (E : Equations L) : Prop :=
  ∀ e ∈ E, ∀ v : ℕ → M, e.1.realize v = e.2.realize v

/-- Soundness: equality modulo `E` holds in every algebra satisfying `E`, for every
interpretation of the names. -/
theorem EqMod.realize_eq {M : Type} [L.Structure M] {E : Equations L} (hM : Satisfies M E)
    (v : N → M) {t u : L.Term N} (h : EqMod E t u) : t.realize v = u.realize v := by
  induction h with
  | inst h σ =>
      rw [Term.realize_subst, Term.realize_subst]
      exact hM _ h _
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | congr f _ ih =>
      show funMap f _ = funMap f _
      exact congrArg (funMap f) (funext ih)

/-! ## Normalization decides the theory -/

/-- `nf` is a normalization function for `E` (DyLean, Definition 1). -/
structure IsNormalizer (E : Equations L) (nf : L.Term N → L.Term N) : Prop where
  /-- Instances of an equation have equal normal forms. -/
  equation : ∀ {l r : L.Term ℕ}, (l, r) ∈ E → ∀ σ : ℕ → L.Term N,
    nf (l.subst σ) = nf (r.subst σ)
  /-- Normalizing does not leave the class modulo `E`. -/
  eqMod_self : ∀ t, EqMod E t (nf t)
  /-- Normalizing arguments first does not change the normal form. -/
  func_normal : ∀ {n} (f : L.Functions n) (ts : Fin n → L.Term N),
    nf (func f fun i => nf (ts i)) = nf (func f ts)

/-- Two messages are equal modulo `E` exactly when their normal forms coincide (DyLean,
Theorem 1). -/
theorem IsNormalizer.eqMod_iff {E : Equations L} {nf : L.Term N → L.Term N}
    (h : IsNormalizer E nf) {t u : L.Term N} : EqMod E t u ↔ nf t = nf u := by
  constructor
  · intro htu
    induction htu with
    | inst hlr σ => exact h.equation hlr σ
    | refl => rfl
    | symm _ ih => exact ih.symm
    | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
    | @congr n f ts us _ ih =>
        have hargs : (fun i => nf (ts i)) = fun i => nf (us i) := funext ih
        rw [← h.func_normal f ts, ← h.func_normal f us, hargs]
  · intro htu
    exact (h.eqMod_self t).trans (htu ▸ (h.eqMod_self u).symm)

/-- Normalization assembled from one normalizing constructor per function symbol, applied
bottom-up: names are already normal, and `c f` normalizes an application of `f` to normal
arguments. -/
def normalizeWith (c : ∀ {n}, L.Functions n → (Fin n → L.Term N) → L.Term N) :
    L.Term N → L.Term N
  | var a => var a
  | func f ts => c f fun i => normalizeWith c (ts i)

/-- Local conditions on normalizing constructors that make `normalizeWith` a normalization
function (DyLean, Theorem 2): the instances of every equation get equal normal forms, each
constructor is sound modulo `E`, and it maps normal arguments to normal results. -/
theorem isNormalizer_normalizeWith {E : Equations L}
    {c : ∀ {n}, L.Functions n → (Fin n → L.Term N) → L.Term N}
    (equation : ∀ {l r : L.Term ℕ}, (l, r) ∈ E → ∀ σ : ℕ → L.Term N,
      normalizeWith c (l.subst σ) = normalizeWith c (r.subst σ))
    (sound : ∀ {n} (f : L.Functions n) (ts : Fin n → L.Term N), EqMod E (c f ts) (func f ts))
    (normal : ∀ {n} (f : L.Functions n) (ts : Fin n → L.Term N),
      (∀ i, normalizeWith c (ts i) = ts i) → normalizeWith c (c f ts) = c f ts) :
    IsNormalizer E (normalizeWith c) := by
  have idem : ∀ t, normalizeWith c (normalizeWith c t) = normalizeWith c t := by
    intro t
    induction t with
    | var a => rfl
    | func f ts ih => exact normal f _ ih
  refine ⟨equation, ?_, ?_⟩
  · intro t
    induction t with
    | var a => exact EqMod.refl _
    | func f ts ih => exact (EqMod.congr f ih).trans (sound f _).symm
  · intro n f ts
    show c f (fun i => normalizeWith c (normalizeWith c (ts i))) =
      c f (fun i => normalizeWith c (ts i))
    simp only [idem]

/-! ## The attacker in the term model and in its algebras -/

/-- One attacker step in an algebra: apply a public function symbol to known arguments. -/
inductive FunRule (M : Type) [L.Structure M] (pub : ∀ {n}, L.Functions n → Prop) : Rules M
  | apply {n : ℕ} (f : L.Functions n) (hf : pub f) (args : Fin n → M) :
      FunRule M pub (List.ofFn args) (funMap f args)

/-- One attacker step in the term model modulo `E`: apply a public function symbol, or
replace a message by one equal modulo `E`. -/
inductive TermRule (E : Equations L) (pub : ∀ {n}, L.Functions n → Prop) : Rules (L.Term N)
  | apply {n : ℕ} (f : L.Functions n) (hf : pub f) (ts : Fin n → L.Term N) :
      TermRule E pub (List.ofFn ts) (func f ts)
  | rewrite {t u : L.Term N} : EqMod E t u → TermRule E pub [t] u

/-- Deductions in the term model modulo `E` are reflected in every algebra satisfying `E`. -/
theorem deducible_realize {M : Type} [L.Structure M] {E : Equations L} (hM : Satisfies M E)
    (pub : ∀ {n}, L.Functions n → Prop) (v : N → M) {K : Set (L.Term N)} {t : L.Term N}
    (h : Deducible (TermRule E pub) K t) :
    Deducible (FunRule M pub) (Term.realize v '' K) (t.realize v) := by
  refine Deducible.map (Term.realize v) ?_ h
  intro ps m hr
  cases hr with
  | apply f hf ts =>
      refine Deducible.rule (FunRule.apply f hf fun i => (ts i).realize v) ?_
      intro p hp
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
      exact Deducible.known ⟨ts i, List.mem_ofFn.mpr ⟨i, rfl⟩, rfl⟩
  | rewrite htu =>
      exact Deducible.known ⟨_, List.mem_singleton_self _, htu.realize_eq hM v⟩

/-- Secrecy in an algebra satisfying `E` implies secrecy in the term model modulo `E`. -/
theorem secret_of_realize {M : Type} [L.Structure M] {E : Equations L} (hM : Satisfies M E)
    (pub : ∀ {n}, L.Functions n → Prop) (v : N → M) {K : Set (L.Term N)} {t : L.Term N}
    (h : Secret (FunRule M pub) (Term.realize v '' K) (t.realize v)) :
    Secret (TermRule E pub) K t :=
  fun hd => h (deducible_realize hM pub v hd)

end Mettapedia.Protocols.Symbolic
