import Mathlib.Order.Hom.Order

/-!
# Secrecy labels

A trace is the list of events of an execution, oldest first; it only grows, by appending. A
*label* says when a value may become known to the attacker: it is a compromise condition on
traces that, once true, stays true as the trace grows, because a compromise cannot be undone
and the attacker forgets nothing. Labels are therefore monotone predicates on traces ordered
by extension (`Label`), and they form a complete lattice (Mathlib's lattice of monotone maps
into `Prop`). In that lattice `⊤` is public and `⊥` is secret; `l₁ ⊓ l₂` is corrupt when both
are, the label of a pair, which the attacker learns only with both components; `l₁ ⊔ l₂` is
corrupt when either is, the label of a key shared by two parties, which leaks when either
party is compromised. The order `l₁ ≤ l₂` reads "whenever `l₁` is corrupt, so is `l₂`": `l₁` is
at most as public as `l₂`. `Label.after e` is corrupt once the event `e` has happened; the
label "readable by `p`" is `Label.after` of the event that compromises `p`.

Encryption needs the order relative to a trace: `l₁` *flows to* `l₂` from `τ` on
(`Label.FlowsAt`) when, in every extension of `τ`, `l₁` corrupt implies `l₂` corrupt. A
ciphertext under a key labelled `l₁` may carry a plaintext labelled `l₂` when `l₁` flows to
`l₂`, since whoever learns the key can decrypt. The relative order holds at `τ` as soon as
`l₂` is corrupt at `τ`, which is what the attacker needs to encrypt data it knows under keys
it knows; the global order would not allow that.

Labels as growing trace predicates with meet, join and the trace-relative flow are LeanDY's
(Jeanteur, Veronese, Solitro, Maffei, arXiv:2607.03406, §3.1.3), generalizing the fixed label
syntax of DY*. DyLean (Wallez, Cremers, IACR ePrint 2026/1493, §3.1) likewise takes the
security label of a value to be a predicate on execution traces.
-/

namespace Mettapedia.Protocols.Symbolic

/-- Traces carrying the extension order. Traces are plain lists `List Ev`, oldest event
first; this synonym only supplies the prefix order on which labels are monotone. -/
def TraceOrder (Ev : Type) := List Ev

instance (Ev : Type) : Preorder (TraceOrder Ev) where
  le a b := List.IsPrefix a b
  le_refl a := List.prefix_refl a
  le_trans _ _ _ := List.IsPrefix.trans

/-- A secrecy label: a condition under which a value may be known to the attacker, stable
under extension of the trace. A label holding at a trace is *corrupt* there. -/
abbrev Label (Ev : Type) := TraceOrder Ev →o Prop

namespace Label

variable {Ev : Type} {l l₁ l₂ l₃ : Label Ev} {τ τ' : List Ev}

/-- A corrupt label stays corrupt as the trace grows. -/
theorem corrupt_mono (l : Label Ev) (h : τ <+: τ') (hl : l τ) : l τ' := l.mono h hl

@[simp] theorem top_apply (τ : List Ev) : (⊤ : Label Ev) τ := trivial

@[simp] theorem bot_apply (τ : List Ev) : ¬ (⊥ : Label Ev) τ := id

@[simp] theorem sup_apply (l₁ l₂ : Label Ev) (τ : List Ev) : (l₁ ⊔ l₂) τ ↔ l₁ τ ∨ l₂ τ :=
  Iff.rfl

@[simp] theorem inf_apply (l₁ l₂ : Label Ev) (τ : List Ev) : (l₁ ⊓ l₂) τ ↔ l₁ τ ∧ l₂ τ :=
  Iff.rfl

theorem le_iff : l₁ ≤ l₂ ↔ ∀ τ : List Ev, l₁ τ → l₂ τ := Iff.rfl

/-- Corrupt once some event satisfying `P` has happened. -/
def once (P : Ev → Prop) : Label Ev :=
  ⟨fun (τ : List Ev) => ∃ e ∈ τ, P e, fun _ _ h ⟨e, he, hP⟩ => ⟨e, List.IsPrefix.mem he h, hP⟩⟩

@[simp] theorem once_apply (P : Ev → Prop) (τ : List Ev) : once P τ ↔ ∃ e ∈ τ, P e := Iff.rfl

/-- Corrupt once the event `e` has happened. -/
def after (e : Ev) : Label Ev :=
  ⟨fun (τ : List Ev) => e ∈ τ, fun _ _ h he => List.IsPrefix.mem he h⟩

@[simp] theorem after_apply (e : Ev) (τ : List Ev) : after e τ ↔ e ∈ τ := Iff.rfl

/-- `l₁` flows to `l₂` from `τ` on: in every extension of `τ`, if `l₁` is corrupt so is `l₂`. -/
def FlowsAt (τ : List Ev) (l₁ l₂ : Label Ev) : Prop :=
  ∀ τ' : List Ev, τ <+: τ' → l₁ τ' → l₂ τ'

theorem flowsAt_of_le (h : l₁ ≤ l₂) : FlowsAt τ l₁ l₂ := fun τ' _ h₁ => h τ' h₁

/-- Anything flows to a label that is already corrupt. -/
theorem flowsAt_of_corrupt (h : l₂ τ) : FlowsAt τ l₁ l₂ :=
  fun _ hτ' _ => l₂.mono hτ' h

theorem FlowsAt.refl (τ : List Ev) (l : Label Ev) : FlowsAt τ l l := fun _ _ h => h

theorem FlowsAt.trans (h₁ : FlowsAt τ l₁ l₂) (h₂ : FlowsAt τ l₂ l₃) : FlowsAt τ l₁ l₃ :=
  fun τ' hτ' h => h₂ τ' hτ' (h₁ τ' hτ' h)

/-- A flow from `τ` on persists in extensions of `τ`. -/
theorem FlowsAt.mono (h : τ <+: τ') (hf : FlowsAt τ l₁ l₂) : FlowsAt τ' l₁ l₂ :=
  fun τ'' hτ'' => hf τ'' (h.trans hτ'')

/-- If `l₁` flows to `l₂` and `l₁` is corrupt, then `l₂` is corrupt. -/
theorem FlowsAt.corrupt (hf : FlowsAt τ l₁ l₂) (h : l₁ τ) : l₂ τ :=
  hf τ (List.prefix_refl τ) h

/-- From the empty trace on, flowing is the global order. -/
theorem flowsAt_nil_iff : FlowsAt ([] : List Ev) l₁ l₂ ↔ l₁ ≤ l₂ :=
  ⟨fun h τ hl => h τ (List.nil_prefix) hl, flowsAt_of_le⟩

end Label

end Mettapedia.Protocols.Symbolic
