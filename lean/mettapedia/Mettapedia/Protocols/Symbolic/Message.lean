import Mathlib.Data.Sym.Sym2
import Mathlib.Data.Fin.VecNotation
import Mettapedia.Protocols.Symbolic.Equational
import Mettapedia.Protocols.Symbolic.Invariant

/-!
# A Dolev–Yao message algebra

Messages are built from names `N` (keys, nonces, identities) by the usual symbolic primitives:
public keys, pairs, hashes (also used for key derivation), authenticated symmetric encryption,
signatures and Diffie–Hellman shared secrets. `Msg N` is a type of normal forms, and every
operation is a normalizing constructor in DyLean's sense (Wallez, Cremers, IACR ePrint 2026/1493,
§2.2): it returns a normal form, so protocols compare messages by syntactic equality.
Destructors (projections, decryption, verification) return `fail` on ill-formed input, as
LeanDY's normalizer does (Jeanteur, Veronese, Solitro, Maffei, arXiv:2607.03406, §3.1.2).
Decryption under any other key fails, which models authenticated encryption. For
Diffie–Hellman, `dh a (pk b)` with names `a` and `b` is the secret `shared s(a, b)` of the
unordered pair, so both parties compute the same key; `dh` of anything else fails, so private
exponents are names, as they are in every key exchange modelled here.

`dyEquations` states the theory as a first-order equation system: projection of pairs,
decryption of encryptions, verification of signatures, and commutation of Diffie–Hellman.
`Msg N` satisfies it (`satisfies_dyEquations`). It is not the free model: it identifies every
failed destructor application with `fail`, and Diffie–Hellman with an exponent that is not a
name fails. (The free normal forms of the destructor equations are in `Symbolic.Destructors`.)
By `secret_of_realize`, secrecy proved in `Msg N` is nevertheless secrecy in the term model
modulo `dyEquations` (`secret_term_of_secret`).

The attacker may apply every operation (`DYRule`); names are not operations, so it learns
them only by observation. Labels and well-formedness follow DY* and LeanDY. A name is
labelled by a protocol-chosen labelling `Γ`; public keys, ciphertexts and `fail` are public; a
pair is learned with both components; a hash or signature is as secret as what it hashes or
signs (LeanDY labels hashes public; here hashes derive keys, so a hash keeps the label of its
input); a shared secret leaks when either private key does (`label`). Well-formedness
(`WellFormed`) asks of a ciphertext that the label of its key flows to the label of its
plaintext, and that its key is compromised or the protocol's encryption predicate allows it;
of a signature, that its key is compromised or the signing predicate allows it (`CryptoPreds`).
`publishability` packages labels and well-formedness, and `publishable_closed` proves that
every attacker operation preserves publishability: the soundness of the type system for this
algebra. Its authentication content is `WellFormed.sign_allowed`: a well-formed signature under
an uncompromised key was allowed by the signing predicate.

Not modelled: lengths, padding, nonces of the encryption scheme, algebraic properties beyond
the listed equations (no exponent arithmetic, no XOR), and any computational aspect.
-/

namespace Mettapedia.Protocols.Symbolic

/-- Messages in normal form over the names `N`. -/
inductive Msg (N : Type) where
  /-- A name: a key, nonce or identity, known to the attacker only by observation. -/
  | name (n : N)
  /-- The public key of the secret `x`. -/
  | pk (x : Msg N)
  | pair (x y : Msg N)
  /-- A hash, also used as key derivation. -/
  | hash (x : Msg N)
  /-- Authenticated symmetric encryption of `m` under the key `k`. -/
  | senc (k m : Msg N)
  /-- The signature on `m` with the signing key `k`. -/
  | sign (k m : Msg N)
  /-- The Diffie–Hellman secret shared by two private keys. -/
  | shared (s : Sym2 N)
  /-- The result of a failed destructor. -/
  | fail
deriving DecidableEq

namespace Msg

variable {N : Type}

/-- First projection. -/
def fst : Msg N → Msg N
  | pair x _ => x
  | _ => fail

/-- Second projection. -/
def snd : Msg N → Msg N
  | pair _ y => y
  | _ => fail

/-- Decryption with the key `k`. -/
def sdec [DecidableEq N] (k : Msg N) : Msg N → Msg N
  | senc k' m => if k' = k then m else fail
  | _ => fail

/-- Verification with the public key `vk`, returning the signed message. -/
def verify [DecidableEq N] (vk : Msg N) : Msg N → Msg N
  | sign k m => if pk k = vk then m else fail
  | _ => fail

/-- Diffie–Hellman: a private key and another party's public key give their shared secret. -/
def dh : Msg N → Msg N → Msg N
  | name a, pk (name b) => shared s(a, b)
  | _, _ => fail

@[simp] theorem fst_pair (x y : Msg N) : fst (pair x y) = x := rfl

@[simp] theorem snd_pair (x y : Msg N) : snd (pair x y) = y := rfl

@[simp] theorem sdec_senc [DecidableEq N] (k m : Msg N) : sdec k (senc k m) = m := by
  simp [sdec]

@[simp] theorem verify_sign [DecidableEq N] (k m : Msg N) : verify (pk k) (sign k m) = m := by
  simp [verify]

@[simp] theorem dh_name_pk (a b : N) : dh (name a) (pk (name b)) = shared s(a, b) := rfl

/-- Both parties compute the same Diffie–Hellman secret. -/
theorem dh_comm (x y : Msg N) : dh x (pk y) = dh y (pk x) := by
  cases x <;> cases y <;> simp [dh, Sym2.eq_swap]

theorem fst_cases (x : Msg N) : fst x = fail ∨ ∃ a b, x = pair a b := by
  cases x <;> simp [fst]

theorem snd_cases (x : Msg N) : snd x = fail ∨ ∃ a b, x = pair a b := by
  cases x <;> simp [snd]

theorem sdec_cases [DecidableEq N] (k c : Msg N) :
    sdec k c = fail ∨ ∃ m, c = senc k m ∧ sdec k c = m := by
  cases c with
  | senc k' m =>
      by_cases h : k' = k
      · subst h; exact Or.inr ⟨m, rfl, sdec_senc _ _⟩
      · exact Or.inl (by simp [sdec, h])
  | _ => exact Or.inl rfl

theorem verify_cases [DecidableEq N] (vk s : Msg N) :
    verify vk s = fail ∨ ∃ k m, s = sign k m ∧ vk = pk k ∧ verify vk s = m := by
  cases s with
  | sign k m =>
      by_cases h : pk k = vk
      · subst h; exact Or.inr ⟨k, m, rfl, rfl, verify_sign _ _⟩
      · exact Or.inl (by simp [verify, h])
  | _ => exact Or.inl rfl

theorem dh_cases (x y : Msg N) :
    dh x y = fail ∨ ∃ a b, x = name a ∧ y = pk (name b) ∧ dh x y = shared s(a, b) := by
  unfold dh
  split
  · exact Or.inr ⟨_, _, rfl, rfl, rfl⟩
  · exact Or.inl rfl

/-- A successful decryption reveals the ciphertext. -/
theorem eq_senc_of_sdec [DecidableEq N] {k c m : Msg N} (h : sdec k c = m) (hm : m ≠ fail) :
    c = senc k m := by
  rcases sdec_cases k c with h' | ⟨m', rfl, h'⟩
  · exact absurd (h.symm.trans h') hm
  · rw [h'] at h; rw [h]

/-- A successful verification reveals the signature and its key. -/
theorem eq_sign_of_verify [DecidableEq N] {vk s m : Msg N} (h : verify vk s = m) (hm : m ≠ fail) :
    ∃ k, s = sign k m ∧ vk = pk k := by
  rcases verify_cases vk s with h' | ⟨k, m', rfl, rfl, h'⟩
  · exact absurd (h.symm.trans h') hm
  · rw [h'] at h; exact ⟨k, by rw [h], rfl⟩

end Msg

/-! ## The equational theory -/

open FirstOrder FirstOrder.Language Structure

/-- Function symbols of the Dolev–Yao signature, indexed by arity. Every symbol is public. -/
inductive DYFun : ℕ → Type
  | pk : DYFun 1
  | pair : DYFun 2
  | fst : DYFun 1
  | snd : DYFun 1
  | hash : DYFun 1
  | senc : DYFun 2
  | sdec : DYFun 2
  | sign : DYFun 2
  | verify : DYFun 2
  | dh : DYFun 2
  | fail : DYFun 0
deriving DecidableEq

/-- The Dolev–Yao signature as a first-order language without relations. -/
def dyLanguage : Language.{0, 0} := ⟨DYFun, fun _ => Empty⟩

instance (n : ℕ) : IsEmpty (dyLanguage.Relations n) := inferInstanceAs (IsEmpty Empty)

instance (n : ℕ) : DecidableEq (dyLanguage.Functions n) := inferInstanceAs (DecidableEq (DYFun n))

/-- The interpretation of the symbols on normal forms. -/
def DYFun.eval {N : Type} [DecidableEq N] : ∀ {n}, DYFun n → (Fin n → Msg N) → Msg N
  | _, .pk, a => .pk (a 0)
  | _, .pair, a => .pair (a 0) (a 1)
  | _, .fst, a => (a 0).fst
  | _, .snd, a => (a 0).snd
  | _, .hash, a => .hash (a 0)
  | _, .senc, a => .senc (a 0) (a 1)
  | _, .sdec, a => Msg.sdec (a 0) (a 1)
  | _, .sign, a => .sign (a 0) (a 1)
  | _, .verify, a => Msg.verify (a 0) (a 1)
  | _, .dh, a => Msg.dh (a 0) (a 1)
  | _, .fail, _ => .fail

instance {N : Type} [DecidableEq N] : dyLanguage.Structure (Msg N) where
  funMap := DYFun.eval

@[simp] theorem funMap_msg {N : Type} [DecidableEq N] {n : ℕ} (f : DYFun n) (a : Fin n → Msg N) :
    (funMap (L := dyLanguage) f a : Msg N) = DYFun.eval f a := rfl

namespace DYEq

/-- The pattern variable `i`. -/
abbrev x (i : ℕ) : dyLanguage.Term ℕ := Term.var i

/-- A unary symbol applied to a pattern. -/
abbrev app1 (f : DYFun 1) (a : dyLanguage.Term ℕ) : dyLanguage.Term ℕ :=
  Term.func (L := dyLanguage) f ![a]

/-- A binary symbol applied to two patterns. -/
abbrev app2 (f : DYFun 2) (a b : dyLanguage.Term ℕ) : dyLanguage.Term ℕ :=
  Term.func (L := dyLanguage) f ![a, b]

end DYEq

open DYEq in
/-- The destructor equations: `fst ⟨x, y⟩ = x`, `snd ⟨x, y⟩ = y`, `sdec k (senc k m) = m`,
`verify (pk k) (sign k m) = m`. -/
def destructorEquations : Equations dyLanguage :=
  {(app1 .fst (app2 .pair (x 0) (x 1)), x 0),
   (app1 .snd (app2 .pair (x 0) (x 1)), x 1),
   (app2 .sdec (x 0) (app2 .senc (x 0) (x 1)), x 1),
   (app2 .verify (app1 .pk (x 0)) (app2 .sign (x 0) (x 1)), x 1)}

open DYEq in
/-- The Dolev–Yao equational theory: the destructor equations and commutation of
Diffie–Hellman, `dh x (pk y) = dh y (pk x)`. -/
def dyEquations : Equations dyLanguage :=
  insert (app2 .dh (x 0) (app1 .pk (x 1)), app2 .dh (x 1) (app1 .pk (x 0))) destructorEquations

/-- The normal forms satisfy the Dolev–Yao theory. -/
theorem satisfies_dyEquations {N : Type} [DecidableEq N] : Satisfies (Msg N) dyEquations := by
  intro e he v
  simp only [dyEquations, destructorEquations, Set.mem_insert_iff, Set.mem_singleton_iff] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;>
    simp [Term.realize, DYFun.eval, Msg.dh_comm]

/-! ## The attacker -/

/-- The attacker's steps: every operation of the algebra. -/
inductive DYRule {N : Type} [DecidableEq N] : Rules (Msg N)
  | pk (x : Msg N) : DYRule [x] (.pk x)
  | pair (x y : Msg N) : DYRule [x, y] (.pair x y)
  | fst (x : Msg N) : DYRule [x] x.fst
  | snd (x : Msg N) : DYRule [x] x.snd
  | hash (x : Msg N) : DYRule [x] (.hash x)
  | senc (k m : Msg N) : DYRule [k, m] (.senc k m)
  | sdec (k c : Msg N) : DYRule [k, c] (Msg.sdec k c)
  | sign (k m : Msg N) : DYRule [k, m] (.sign k m)
  | verify (vk s : Msg N) : DYRule [vk, s] (Msg.verify vk s)
  | dh (x y : Msg N) : DYRule [x, y] (Msg.dh x y)
  | fail : DYRule [] .fail

/-- The attacker's steps are exactly the applications of the (all public) symbols of
`dyLanguage`. -/
theorem dyRule_iff_funRule {N : Type} [DecidableEq N] {ps : List (Msg N)} {m : Msg N} :
    DYRule ps m ↔ FunRule (L := dyLanguage) (Msg N) (fun _ => True) ps m := by
  have app : ∀ {n} (f : DYFun n) (args : Fin n → Msg N),
      FunRule (L := dyLanguage) (Msg N) (fun _ => True) (List.ofFn args) (DYFun.eval f args) :=
    fun f args =>
      FunRule.apply (L := dyLanguage) (M := Msg N) (pub := fun _ => True) f trivial args
  constructor
  · intro h
    cases h with
    | pk x => simpa [DYFun.eval] using app .pk ![x]
    | pair x y => simpa [DYFun.eval] using app .pair ![x, y]
    | fst x => simpa [DYFun.eval] using app .fst ![x]
    | snd x => simpa [DYFun.eval] using app .snd ![x]
    | hash x => simpa [DYFun.eval] using app .hash ![x]
    | senc k m => simpa [DYFun.eval] using app .senc ![k, m]
    | sdec k c => simpa [DYFun.eval] using app .sdec ![k, c]
    | sign k m => simpa [DYFun.eval] using app .sign ![k, m]
    | verify vk s => simpa [DYFun.eval] using app .verify ![vk, s]
    | dh x y => simpa [DYFun.eval] using app .dh ![x, y]
    | fail => simpa [DYFun.eval] using app .fail ![]
  · intro h
    cases h with
    | apply f _ args =>
        cases f <;> simp only [List.ofFn_succ, List.ofFn_zero, funMap_msg, DYFun.eval,
          Fin.succ_zero_eq_one] <;> constructor

/-- Secrecy in `Msg N` is secrecy in the term model modulo `dyEquations`: if the image of a term
cannot be deduced from the images of the observations, the term cannot be deduced symbolically. -/
theorem secret_term_of_secret {N : Type} [DecidableEq N] {K : Set (dyLanguage.Term N)}
    {t : dyLanguage.Term N}
    (h : Secret DYRule (Term.realize Msg.name '' K) (t.realize Msg.name)) :
    Secret (TermRule dyEquations (fun _ => True)) K t :=
  secret_of_realize satisfies_dyEquations _ Msg.name
    (fun hd => h (hd.mono_rules fun _ _ hr => dyRule_iff_funRule.mpr hr))

/-! ## Labels and well-formedness -/

namespace Msg

variable {N Ev : Type}

/-- The label of a Diffie–Hellman secret: corrupt when either private key is. -/
noncomputable def sharedLabel (Γ : N → Label Ev) : Sym2 N → Label Ev :=
  Sym2.lift ⟨fun a b => Γ a ⊔ Γ b, fun a b => sup_comm (Γ a) (Γ b)⟩

@[simp] theorem sharedLabel_mk (Γ : N → Label Ev) (a b : N) :
    sharedLabel Γ s(a, b) = Γ a ⊔ Γ b := rfl

/-- The secrecy label of a message, given the labels `Γ` of the names. -/
@[simp] noncomputable def label (Γ : N → Label Ev) : Msg N → Label Ev
  | name n => Γ n
  | pk _ => ⊤
  | pair x y => label Γ x ⊓ label Γ y
  | hash x => label Γ x
  | senc _ _ => ⊤
  | sign _ m => label Γ m
  | shared s => sharedLabel Γ s
  | fail => ⊤

end Msg

/-- The protocol's integrity predicates (DY*'s signature and encryption predicates, LeanDY's
`CryptoPreds`): when an uncompromised key may sign, or encrypt, a message. Both are stable under
extension of the trace. -/
structure CryptoPreds (Ev M : Type) where
  /-- `sign τ k m`: the owner of the signing key `k` may sign `m` at `τ`. -/
  sign : List Ev → M → M → Prop
  /-- `enc τ k m`: an honest holder of the key `k` may encrypt `m` at `τ`. -/
  enc : List Ev → M → M → Prop
  sign_mono : ∀ {τ τ' : List Ev} {k m : M}, τ <+: τ' → sign τ k m → sign τ' k m
  enc_mono : ∀ {τ τ' : List Ev} {k m : M}, τ <+: τ' → enc τ k m → enc τ' k m

namespace Msg

variable {N Ev : Type}

/-- Well-formedness at a trace (DY*'s bytes invariant, LeanDY's `valid_bytes`): a ciphertext's
key label flows to its plaintext label and its key is compromised or the encryption is allowed;
a signature's key is compromised or the signature is allowed; recursively in every
subterm. -/
@[simp] def WellFormed (Γ : N → Label Ev) (C : CryptoPreds Ev (Msg N)) (τ : List Ev) :
    Msg N → Prop
  | name _ => True
  | pk x => WellFormed Γ C τ x
  | pair x y => WellFormed Γ C τ x ∧ WellFormed Γ C τ y
  | hash x => WellFormed Γ C τ x
  | senc k m => WellFormed Γ C τ k ∧ WellFormed Γ C τ m ∧
      Label.FlowsAt τ (label Γ k) (label Γ m) ∧ (label Γ k τ ∨ C.enc τ k m)
  | sign k m => WellFormed Γ C τ k ∧ WellFormed Γ C τ m ∧ (label Γ k τ ∨ C.sign τ k m)
  | shared _ => True
  | fail => True

variable {Γ : N → Label Ev} {C : CryptoPreds Ev (Msg N)}

theorem WellFormed.mono {τ τ' : List Ev} (hτ : τ <+: τ') :
    ∀ {m : Msg N}, WellFormed Γ C τ m → WellFormed Γ C τ' m := by
  intro m
  induction m with
  | name => intro _; trivial
  | pk x ih => exact ih
  | pair x y ihx ihy => exact fun h => ⟨ihx h.1, ihy h.2⟩
  | hash x ih => exact ih
  | senc k m ihk ihm =>
      exact fun h => ⟨ihk h.1, ihm h.2.1, h.2.2.1.mono hτ,
        h.2.2.2.imp ((label Γ k).mono hτ) (C.enc_mono hτ)⟩
  | sign k m ihk ihm =>
      exact fun h => ⟨ihk h.1, ihm h.2.1, h.2.2.imp ((label Γ k).mono hτ) (C.sign_mono hτ)⟩
  | shared => intro _; trivial
  | fail => intro _; trivial

/-- A well-formed signature under an uncompromised key was allowed by the signing predicate. -/
theorem WellFormed.sign_allowed {τ : List Ev} {k m : Msg N} (h : WellFormed Γ C τ (sign k m)) :
    label Γ k τ ∨ C.sign τ k m :=
  h.2.2

/-- The contents of a well-formed ciphertext are well formed. -/
theorem WellFormed.senc_plain {τ : List Ev} {k m : Msg N} (h : WellFormed Γ C τ (senc k m)) :
    WellFormed Γ C τ m :=
  h.2.1

/-- Every attacker operation preserves publishability: label corrupt and well formed. -/
theorem publishable_closed [DecidableEq N] (Γ : N → Label Ev) (C : CryptoPreds Ev (Msg N))
    (τ : List Ev) {ps : List (Msg N)} {m : Msg N} (hr : DYRule ps m)
    (hps : ∀ p ∈ ps, label Γ p τ ∧ WellFormed Γ C τ p) :
    label Γ m τ ∧ WellFormed Γ C τ m := by
  cases hr with
  | pk x =>
      exact ⟨trivial, (hps x (by simp)).2⟩
  | pair x y =>
      obtain ⟨hx, hx'⟩ := hps x (by simp)
      obtain ⟨hy, hy'⟩ := hps y (by simp)
      exact ⟨⟨hx, hy⟩, hx', hy'⟩
  | fst x =>
      obtain ⟨hx, hx'⟩ := hps x (by simp)
      rcases fst_cases x with h | ⟨a, b, rfl⟩
      · rw [h]; exact ⟨trivial, trivial⟩
      · exact ⟨hx.1, hx'.1⟩
  | snd x =>
      obtain ⟨hx, hx'⟩ := hps x (by simp)
      rcases snd_cases x with h | ⟨a, b, rfl⟩
      · rw [h]; exact ⟨trivial, trivial⟩
      · exact ⟨hx.2, hx'.2⟩
  | hash x =>
      exact hps x (by simp)
  | senc k m =>
      obtain ⟨hk, hk'⟩ := hps k (by simp)
      obtain ⟨hm, hm'⟩ := hps m (by simp)
      exact ⟨trivial, hk', hm', Label.flowsAt_of_corrupt hm, Or.inl hk⟩
  | sdec k c =>
      obtain ⟨hk, -⟩ := hps k (by simp)
      obtain ⟨-, hc'⟩ := hps c (by simp)
      rcases sdec_cases k c with h | ⟨m, rfl, h⟩
      · rw [h]; exact ⟨trivial, trivial⟩
      · rw [h]; exact ⟨hc'.2.2.1.corrupt hk, hc'.2.1⟩
  | sign k m =>
      obtain ⟨hk, hk'⟩ := hps k (by simp)
      obtain ⟨hm, hm'⟩ := hps m (by simp)
      exact ⟨hm, hk', hm', Or.inl hk⟩
  | verify vk s =>
      obtain ⟨hs, hs'⟩ := hps s (by simp)
      rcases verify_cases vk s with h | ⟨k, m, rfl, -, h⟩
      · rw [h]; exact ⟨trivial, trivial⟩
      · rw [h]; exact ⟨hs, hs'.2.1⟩
  | dh x y =>
      obtain ⟨hx, -⟩ := hps x (by simp)
      rcases dh_cases x y with h | ⟨a, b, rfl, rfl, h⟩
      · rw [h]; exact ⟨trivial, trivial⟩
      · rw [h]; exact ⟨Or.inl hx, trivial⟩
  | fail =>
      exact ⟨trivial, trivial⟩

/-- Publishability of normal forms, for the name labelling `Γ` and the integrity predicates `C`:
closed under every attacker operation. -/
noncomputable def publishability [DecidableEq N] (Γ : N → Label Ev) (C : CryptoPreds Ev (Msg N)) :
    Publishability Ev (Msg N) DYRule where
  label := label Γ
  wf := WellFormed Γ C
  wf_mono h hm := WellFormed.mono h hm
  closed τ _ _ hr hps := publishable_closed Γ C τ hr hps

end Msg

end Mettapedia.Protocols.Symbolic
