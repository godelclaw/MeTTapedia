import Mettapedia.Protocols.Symbolic.Label
import Mettapedia.Protocols.Symbolic.ThreatModel

/-!
# The proof method: publishability and trace invariants

Secrecy and authentication are proved by over-approximating what the attacker can know. A
message is *publishable* at a trace when its label is corrupt there and it is *well formed*
(`Publishability`). The label captures confidentiality. Well-formedness, DY*'s bytes invariant
and LeanDY's `valid_bytes`, captures integrity: for instance a signature under a key that is not
compromised was made by the key's owner for a purpose the protocol allows. Publishability must
be stable as the trace grows and closed under the attacker's rules. That closure is the
soundness of LeanDY's type system (Jeanteur, Veronese, Solitro, Maffei, arXiv:2607.03406,
Property 2) and of publishability in DY* and DyLean (Wallez, Cremers, IACR ePrint 2026/1493,
§3.4); a message algebra establishes it once (`Symbolic.Message`).

A protocol proof provides an entry invariant and discharges the obligations collected in
`InvariantProof`:
* the attacker's initial knowledge is publishable;
* whatever an entry reveals is publishable once the entry has happened;
* the attacker's publications and actions keep the invariant;
* honest steps keep the invariant, knowing that everything the attacker knows is publishable
  (in particular every message they receive): DyLean's Hoare triples for protocol actions.

Then, on every trace reachable with the attacker as the network,
* everything the attacker knows is publishable (`InvariantProof.knows_pub`): the key
  attacker-knowledge theorem of DyLean (§3.4), LeanDY's `attacker_sound` and `attacker_valid`;
* in particular the label of everything the attacker knows is corrupt
  (`InvariantProof.label_corrupt`), the central secrecy statement: a secret labelled "readable
  by `a` and `b`" is known only after `a` or `b` was compromised;
* every entry satisfies the invariant with respect to its past (`InvariantProof.entry`). This
  is how authentication is stated: the invariant at an acceptance event says that the claimed
  sender acted before, or was compromised before.
-/

namespace Mettapedia.Protocols.Symbolic

/-- Publishability for the deduction system `rules`: a message is publishable at `τ` when its
label is corrupt at `τ` and it is well formed at `τ`. Well-formedness grows with the trace, and
the attacker's rules preserve publishability. -/
structure Publishability (Ev M : Type) (rules : Rules M) where
  /-- The secrecy label of a message. -/
  label : M → Label Ev
  /-- The integrity invariant on messages. -/
  wf : List Ev → M → Prop
  wf_mono : ∀ {τ τ' : List Ev} {m : M}, τ <+: τ' → wf τ m → wf τ' m
  /-- Every attacker step preserves publishability. -/
  closed : ∀ (τ : List Ev) {ps : List M} {m : M}, rules ps m →
    (∀ p ∈ ps, label p τ ∧ wf τ p) → label m τ ∧ wf τ m

namespace Publishability

variable {Ev M : Type} {rules : Rules M} (P : Publishability Ev M rules)

/-- `m` is publishable at `τ`. -/
def Pub (τ : List Ev) (m : M) : Prop := P.label m τ ∧ P.wf τ m

variable {P}

theorem Pub.mono {τ τ' : List Ev} {m : M} (h : τ <+: τ') (hm : P.Pub τ m) : P.Pub τ' m :=
  ⟨(P.label m).mono h hm.1, P.wf_mono h hm.2⟩

/-- If the observations are publishable, everything deducible from them is. -/
theorem deducible_pub {τ : List Ev} {K : Set M} (hK : ∀ x ∈ K, P.Pub τ x) {m : M}
    (h : Deducible rules K m) : P.Pub τ m :=
  h.mem_of_closed (X := {x | P.Pub τ x}) hK (fun _ _ hr hps => P.closed τ hr hps)

end Publishability

/-- The obligations of a trace-invariant proof against the threat model `T`, for a protocol
whose honest steps are `honest`: a publishability predicate for the attacker's rules, an entry
invariant `inv`, and the facts that make the invariant hold on every reachable trace. -/
structure InvariantProof {Ev M : Type} (T : ThreatModel Ev M)
    (honest : List Ev → List Ev → Prop) where
  pub : Publishability Ev M T.rules
  inv : List Ev → Ev → Prop
  /-- The attacker's initial knowledge is publishable. -/
  initial_pub : ∀ m ∈ T.initial, pub.Pub [] m
  /-- What an entry reveals is publishable once the entry has happened. -/
  reveals_pub : ∀ τ e, Holds inv τ → inv τ e → ∀ m ∈ T.reveals τ e, pub.Pub (τ ++ [e]) m
  /-- Publishing a publishable message keeps the invariant. -/
  inject_inv : ∀ τ m, Holds inv τ → pub.Pub τ m → inv τ (T.inject m)
  /-- Attacker actions keep the invariant. -/
  act_inv : ∀ τ e, Holds inv τ → T.act τ e → inv τ e
  /-- Honest steps keep the invariant, given that the attacker's knowledge is publishable. -/
  honest_inv : ∀ τ new, Holds inv τ → (∀ m, T.Knows τ m → pub.Pub τ m) → honest τ new →
    HoldsFrom inv τ new

namespace InvariantProof

variable {Ev M : Type} {T : ThreatModel Ev M} {honest : List Ev → List Ev → Prop}
  (Φ : InvariantProof T honest)

/-- On a trace satisfying the invariant, everything observed is publishable. -/
theorem observed_pub {τ : List Ev} (h : Holds Φ.inv τ) : ∀ m ∈ T.Observed τ, Φ.pub.Pub τ m := by
  rintro m (hm | ⟨pre, e, post, rfl, hm⟩)
  · exact Publishability.Pub.mono (List.nil_prefix) (Φ.initial_pub m hm)
  · have hpre : Holds Φ.inv pre := h.of_prefix (by simp)
    have hm' := Φ.reveals_pub pre e hpre (h.entry rfl) m hm
    exact hm'.mono ⟨post, by simp⟩

/-- The key attacker-knowledge theorem: on a trace satisfying the invariant, everything the
attacker knows is publishable. -/
theorem knows_pub_of_holds {τ : List Ev} (h : Holds Φ.inv τ) {m : M} (hk : T.Knows τ m) :
    Φ.pub.Pub τ m :=
  Publishability.deducible_pub (Φ.observed_pub h) hk

/-- The invariant holds on every reachable trace. -/
theorem holds {τ : List Ev} (h : Reachable (DYStep T honest) τ) : Holds Φ.inv τ := by
  refine Reachable.invariant (holds_nil) ?_ h
  intro τ new _ hτ hs
  cases hs with
  | honest hh =>
      exact (holds_append τ new).mpr
        ⟨hτ, Φ.honest_inv τ new hτ (fun _ => Φ.knows_pub_of_holds hτ) hh⟩
  | inject hk =>
      exact (holds_snoc τ _).mpr ⟨hτ, Φ.inject_inv τ _ hτ (Φ.knows_pub_of_holds hτ hk)⟩
  | act ha =>
      exact (holds_snoc τ _).mpr ⟨hτ, Φ.act_inv τ _ hτ ha⟩

/-- On every reachable trace, everything the attacker knows is publishable. -/
theorem knows_pub {τ : List Ev} (h : Reachable (DYStep T honest) τ) {m : M} (hk : T.Knows τ m) :
    Φ.pub.Pub τ m :=
  Φ.knows_pub_of_holds (Φ.holds h) hk

/-- Labelled secrecy: on every reachable trace, the label of everything the attacker knows is
corrupt. -/
theorem label_corrupt {τ : List Ev} (h : Reachable (DYStep T honest) τ) {m : M}
    (hk : T.Knows τ m) : Φ.pub.label m τ :=
  (Φ.knows_pub h hk).1

/-- A message whose label is not corrupt on a reachable trace is unknown to the attacker. -/
theorem not_knows {τ : List Ev} (h : Reachable (DYStep T honest) τ) {m : M}
    (hl : ¬ Φ.pub.label m τ) : ¬ T.Knows τ m :=
  fun hk => hl (Φ.label_corrupt h hk)

/-- On every reachable trace, everything the attacker knows is well formed. -/
theorem knows_wf {τ : List Ev} (h : Reachable (DYStep T honest) τ) {m : M} (hk : T.Knows τ m) :
    Φ.pub.wf τ m :=
  (Φ.knows_pub h hk).2

/-- On every reachable trace, every entry satisfies the invariant with respect to its past. -/
theorem entry {τ pre post : List Ev} {e : Ev} (h : Reachable (DYStep T honest) τ)
    (he : τ = pre ++ e :: post) : Φ.inv pre e :=
  (Φ.holds h).entry he

end InvariantProof

end Mettapedia.Protocols.Symbolic
