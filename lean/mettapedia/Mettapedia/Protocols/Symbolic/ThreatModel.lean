import Mettapedia.Protocols.Symbolic.Knowledge
import Mettapedia.Protocols.Symbolic.Trace

/-!
# Threat models: the attacker as the network

A threat model fixes what the attacker can compute and what an execution shows it
(`ThreatModel`):
* `rules`, its deduction system, for a message algebra the operations it may apply;
* `initial`, what it knows before anything happens, such as public constants and a directory
  of public keys;
* `reveals pre e`, what the trace entry `e` exposes, given the entries `pre` before it: the
  message of a send, or the secrets a compromise exposes. This is DyLean's base attacker
  knowledge per trace entry (Wallez, Cremers, IACR ePrint 2026/1493, §2.4);
* `inject m`, the entry by which the attacker publishes a message of its own;
* `act τ e`, the further actions it may take at the trace `τ`, such as corrupting a principal.

The attacker knows at `τ` whatever it can deduce from its initial knowledge and the messages the
entries of `τ` reveal (`ThreatModel.Knows`). The corruption model is a parameter, as DyLean
insists (§2.6, §4.5): which events count as a compromise and what each one exposes are choices
of the threat model, not of the proof method.

The attacker is the network. An execution grows by honest protocol steps, by the attacker
publishing a message it can deduce, and by attacker actions (`DYStep`). Honest steps take
their inputs from the attacker's knowledge, so a participant receives only messages the
attacker could have delivered, and the attacker can deliver all of them.

`Event` is a standard event vocabulary: generation of a fresh value, sending, receiving,
storing local state, compromise of a principal, and protocol-specific signals that record
what a participant believes (sent, accepted). `standardThreat` is the usual adaptive corruption
model on it: a send reveals its message, a compromised principal exposes its long-term secrets
and every state it stored so far, and any principal may be corrupted at any time.
-/

namespace Mettapedia.Protocols.Symbolic

/-- A threat model for executions with entries `Ev` and messages `M`. -/
structure ThreatModel (Ev M : Type) where
  /-- The attacker's deduction system. -/
  rules : Rules M
  /-- What the attacker knows before the execution starts. -/
  initial : Set M
  /-- What an entry reveals to the attacker, given the entries before it. -/
  reveals : List Ev → Ev → Set M
  /-- The entry by which the attacker publishes a message. -/
  inject : M → Ev
  /-- Further attacker actions allowed at a trace, such as corruption. -/
  act : List Ev → Ev → Prop

namespace ThreatModel

variable {Ev M : Type} (T : ThreatModel Ev M)

/-- The messages the attacker has observed by the end of `τ`: its initial knowledge and what
the entries of `τ` revealed. -/
def Observed (τ : List Ev) : Set M :=
  T.initial ∪ {m | ∃ pre e post, τ = pre ++ e :: post ∧ m ∈ T.reveals pre e}

/-- What the attacker knows at `τ`. -/
def Knows (τ : List Ev) (m : M) : Prop := Deducible T.rules (T.Observed τ) m

variable {T} {τ τ' : List Ev} {m : M}

theorem observed_mono (h : τ <+: τ') : T.Observed τ ⊆ T.Observed τ' := by
  obtain ⟨rest, rfl⟩ := h
  rintro x (hx | ⟨pre, e, post, rfl, hx⟩)
  · exact Or.inl hx
  · exact Or.inr ⟨pre, e, post ++ rest, by simp, hx⟩

/-- The attacker forgets nothing. -/
theorem knows_mono (h : τ <+: τ') (hk : T.Knows τ m) : T.Knows τ' m :=
  Deducible.mono (observed_mono h) hk

theorem knows_of_initial (hm : m ∈ T.initial) : T.Knows τ m :=
  Deducible.known (Or.inl hm)

/-- What an entry of the trace reveals is known. -/
theorem knows_of_reveals {pre post : List Ev} {e : Ev} (hτ : τ = pre ++ e :: post)
    (hm : m ∈ T.reveals pre e) : T.Knows τ m :=
  Deducible.known (Or.inr ⟨pre, e, post, hτ, hm⟩)

/-- Knowledge is closed under the attacker's rules. -/
theorem knows_rule {ps : List M} (hr : T.rules ps m) (hps : ∀ p ∈ ps, T.Knows τ p) :
    T.Knows τ m :=
  Deducible.rule hr hps

end ThreatModel

/-- One step of an execution against the threat model `T`: an honest step of the protocol, the
attacker publishing a message it knows, or an attacker action. -/
inductive DYStep {Ev M : Type} (T : ThreatModel Ev M) (honest : List Ev → List Ev → Prop) :
    List Ev → List Ev → Prop
  | honest {τ new : List Ev} : honest τ new → DYStep T honest τ new
  | inject {τ : List Ev} {m : M} : T.Knows τ m → DYStep T honest τ [T.inject m]
  | act {τ : List Ev} {e : Ev} : T.act τ e → DYStep T honest τ [e]

/-! ## Standard events and corruption -/

/-- Standard trace events, with principals `P`, messages `M` and protocol signals `S`. -/
inductive Event (P M S : Type) where
  /-- `p` generated the fresh value `n`. -/
  | gen (p : P) (n : M)
  /-- `m` was published on the network. -/
  | send (m : M)
  /-- `p` received `m` from the network. -/
  | recv (p : P) (m : M)
  /-- `p` stored `s` in its local state. -/
  | state (p : P) (s : M)
  /-- `p` was compromised. -/
  | corrupt (p : P)
  /-- A protocol-specific event of `p`, recording what `p` did or believes. -/
  | signal (p : P) (s : S)

/-- The standard adaptive corruption model: a send reveals its message; corrupting `p` reveals
`secretsOf p` and every state `p` stored before; any principal may be corrupted at any time. -/
def standardThreat {P M S : Type} (rules : Rules M) (initial : Set M) (secretsOf : P → Set M) :
    ThreatModel (Event P M S) M where
  rules := rules
  initial := initial
  reveals pre e :=
    match e with
    | .send m => {m}
    | .corrupt p => secretsOf p ∪ {s | Event.state p s ∈ pre}
    | _ => ∅
  inject := .send
  act _ e := ∃ p, e = .corrupt p

section standard

variable {P M S : Type} {rules : Rules M} {initial : Set M} {secretsOf : P → Set M}

@[simp] theorem standardThreat_rules :
    (standardThreat (S := S) rules initial secretsOf).rules = rules := rfl

@[simp] theorem standardThreat_initial :
    (standardThreat (S := S) rules initial secretsOf).initial = initial := rfl

@[simp] theorem standardThreat_inject (m : M) :
    (standardThreat (S := S) rules initial secretsOf).inject m = .send m := rfl

theorem standardThreat_act {τ : List (Event P M S)} {e : Event P M S} :
    (standardThreat rules initial secretsOf).act τ e ↔ ∃ p, e = .corrupt p := Iff.rfl

theorem standardThreat_reveals (pre : List (Event P M S)) (e : Event P M S) :
    (standardThreat rules initial secretsOf).reveals pre e =
      match e with
      | .send m => {m}
      | .corrupt p => secretsOf p ∪ {s | Event.state p s ∈ pre}
      | _ => ∅ := rfl

/-- After `p` is corrupted, the attacker knows `p`'s secrets. -/
theorem standardThreat_knows_secret {τ pre post : List (Event P M S)} {p : P} {m : M}
    (hτ : τ = pre ++ .corrupt p :: post) (hm : m ∈ secretsOf p) :
    (standardThreat rules initial secretsOf).Knows τ m :=
  ThreatModel.knows_of_reveals hτ (Or.inl hm)

/-- The attacker knows every message sent. -/
theorem standardThreat_knows_sent {τ pre post : List (Event P M S)} {m : M}
    (hτ : τ = pre ++ .send m :: post) :
    (standardThreat rules initial secretsOf).Knows τ m :=
  ThreatModel.knows_of_reveals hτ rfl

end standard

end Mettapedia.Protocols.Symbolic
