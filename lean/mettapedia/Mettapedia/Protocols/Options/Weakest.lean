import Mathlib.Tactic.Push
import Mathlib.Data.Fintype.Basic

/-!
# The weakest safe policy, and when a refusal is necessary

A recipient decides on each item from what it can observe: the fields it has
checked. The world the item comes from is hidden from it: who really wrote the
item, and whether a claimed name is true. A policy is the set of observations it
accepts. It is safe for a requirement `safe` on worlds when it accepts an item
only from worlds where `safe` holds.

The theorems:
- `weakest_safe` and `safe_le_weakest`: accepting an observation exactly when
  every world that shows it is safe is a safe policy, and every safe policy
  accepts no more. So the weakest safe policy exists and is unique
  (`eq_weakest`).
- `refuse_iff`: it refuses an observation exactly when some world showing that
  observation is unsafe. That world is the counterexample a necessity theorem
  names, and every policy accepting the observation is unsafe
  (`refusal_necessary`). A safe policy that refuses more than the weakest one
  refuses some observation that no unsafe world shows (`unnecessary_refusal`):
  that refusal can have no necessity theorem.
- Options. An option adds a requirement to the protocol's own. The weakest
  policy for both requirements is the conjunction of the two weakest policies
  (`weakest_and`), so independently chosen options combine without loss. For a
  disjunction of requirements this fails (`weakest_or_counterexample`). Adding a
  requirement never accepts more (`weakest_mono`), so the default, which adds
  nothing, is the weakest of all the options (`default_weakest`).
- Observation. Seeing more never accepts less (`weakest_finer`). Checking
  signatures therefore widens what may safely be accepted.

The instance in `Standing`: an item's world is its true author key and the name
it claims, and the requirement is that the author is allowed.
- With signatures checked, the weakest policy accepts exactly the items whose
  signing key is allowed, whatever name they claim (`verified_weakest`). A rule
  that also checks the name refuses mail that no unsafe world shows
  (`name_check_unnecessary`). Accepting by claimed name alone is unsafe
  (`name_policy_unsafe`).
- With only the claimed name observed, nothing may be accepted once some key is
  not allowed (`unverified_accepts_nothing`).
- An option of hearing only the registry refuses a stranger's mail that the
  default hears (`registry_option_refuses_stranger`). That is what a user gives
  up by choosing it.

Scope: one decision per item, from one observation. Sequences of decisions in
which a policy can block only some events (the controllability of supervisory
control, Ramadge and Wonham 1987) are not modelled here.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Options.Weakest

section General

variable {W O : Type}

/-- A policy: the observations it accepts. -/
abbrev Policy (O : Type) := O → Prop

/-- `p` is safe for `safe` when it accepts an item only from worlds meeting
`safe`. -/
def Safe (obs : W → O) (safe : W → Prop) (p : Policy O) : Prop :=
  ∀ w, p (obs w) → safe w

/-- Accept an observation exactly when every world that shows it is safe. -/
def weakest (obs : W → O) (safe : W → Prop) : Policy O :=
  fun o => ∀ w, obs w = o → safe w

theorem weakest_safe (obs : W → O) (safe : W → Prop) : Safe obs safe (weakest obs safe) :=
  fun w h => h w rfl

theorem safe_le_weakest {obs : W → O} {safe : W → Prop} {p : Policy O}
    (hp : Safe obs safe p) (o : O) (ho : p o) : weakest obs safe o := by
  intro w hw
  subst hw
  exact hp w ho

/-- The weakest safe policy is unique: a safe policy that accepts whatever any
safe policy accepts is `weakest`. -/
theorem eq_weakest {obs : W → O} {safe : W → Prop} {p : Policy O}
    (hp : Safe obs safe p) (hmax : ∀ q, Safe obs safe q → ∀ o, q o → p o) :
    p = weakest obs safe := by
  funext o
  apply propext
  exact ⟨safe_le_weakest hp o, hmax _ (weakest_safe obs safe) o⟩

theorem refuse_iff {obs : W → O} {safe : W → Prop} {o : O} :
    ¬ weakest obs safe o ↔ ∃ w, obs w = o ∧ ¬ safe w := by
  unfold weakest
  push Not
  rfl

/-- A refusal by the weakest policy is necessary: every policy that accepts the
observation is unsafe. -/
theorem refusal_necessary {obs : W → O} {safe : W → Prop} {o : O}
    (h : ¬ weakest obs safe o) {p : Policy O} (hp : p o) : ¬ Safe obs safe p :=
  fun hs => h (safe_le_weakest hs o hp)

/-- A safe policy other than the weakest refuses some observation that every
world showing it makes safe. -/
theorem unnecessary_refusal {obs : W → O} {safe : W → Prop} {p : Policy O}
    (hp : Safe obs safe p) (hne : p ≠ weakest obs safe) :
    ∃ o, ¬ p o ∧ weakest obs safe o := by
  by_contra hno
  push Not at hno
  apply hne
  funext o
  apply propext
  exact ⟨safe_le_weakest hp o, fun hw => by_contra fun hpo => hno o hpo hw⟩

/-- Options combine without loss: the weakest policy for two requirements is the
conjunction of their weakest policies. -/
theorem weakest_and (obs : W → O) (s t : W → Prop) :
    weakest obs (fun w => s w ∧ t w) = fun o => weakest obs s o ∧ weakest obs t o := by
  funext o
  apply propext
  constructor
  · intro h
    exact ⟨fun w hw => (h w hw).1, fun w hw => (h w hw).2⟩
  · rintro ⟨hs, ht⟩ w hw
    exact ⟨hs w hw, ht w hw⟩

/-- A requirement that implies another refuses at least what the other refuses. -/
theorem weakest_mono {obs : W → O} {s t : W → Prop} (hst : ∀ w, s w → t w) {o : O}
    (h : weakest obs s o) : weakest obs t o :=
  fun w hw => hst w (h w hw)

/-- The default adds no requirement to the protocol's `base`. Whatever an option
`extra` accepts, the default accepts too. -/
theorem default_weakest (obs : W → O) (base extra : W → Prop) {o : O}
    (h : weakest obs (fun w => base w ∧ extra w) o) : weakest obs base o :=
  weakest_mono (fun _ hw => hw.1) h

/-- Seeing more never accepts less: when the coarse observation is computed from
the fine one by `g`, the weakest policy on the fine observation accepts whatever
the coarse one accepts. -/
theorem weakest_finer {O' : Type} (fine : W → O) (g : O → O') (safe : W → Prop) {o : O}
    (h : weakest (fun w => g (fine w)) safe (g o)) : weakest fine safe o :=
  fun w hw => h w (congrArg g hw)

end General

/-- The mutant of `weakest_and`: for a disjunction of requirements, the weakest
policy can accept what neither requirement's weakest policy accepts. One world
shows nothing to tell `true` from `false`, but each world meets one of the two
requirements. -/
theorem weakest_or_counterexample :
    weakest (fun _ : Bool => ()) (fun w => w = true ∨ w = false) () ∧
      ¬ (weakest (fun _ : Bool => ()) (fun w => w = true) () ∨
        weakest (fun _ : Bool => ()) (fun w => w = false) ()) := by
  refine ⟨fun w _ => by cases w <;> simp, ?_⟩
  rintro (h | h)
  · exact Bool.false_ne_true (h false rfl)
  · exact Bool.noConfusion (h true rfl)

/-- The mutant of `safe_le_weakest`: without safety, a policy accepts more than
the weakest safe one. Accepting everything accepts the observation that the
unsafe world `false` shows. -/
theorem unsafe_exceeds_weakest :
    (fun _ : Unit => True) () ∧ ¬ weakest (fun _ : Bool => ()) (fun w => w = true) () :=
  ⟨trivial, fun h => Bool.false_ne_true (h false rfl)⟩

section Standing

variable {K N : Type}

/-- A received item's world: the key that really wrote it, and the name it
claims. -/
structure Item (K N : Type) where
  author : K
  claimed : N

/-- The requirement: the item's true author is allowed. -/
def authorAllowed (allowed : K → Prop) (i : Item K N) : Prop :=
  allowed i.author

/-- With signatures checked, the recipient sees the author key as well as the
claimed name. The weakest policy accepts exactly the items whose key is
allowed. -/
theorem verified_weakest (allowed : K → Prop) (i : Item K N) :
    weakest id (authorAllowed allowed) i ↔ allowed i.author :=
  ⟨fun h => h i rfl, fun h w hw => by subst hw; exact h⟩

/-- The verified weakest policy depends on the key alone: two items with one
author are both accepted or both refused, whatever names they claim. -/
theorem verified_ignores_name (allowed : K → Prop) (i j : Item K N)
    (h : i.author = j.author) :
    weakest id (authorAllowed allowed) i ↔ weakest id (authorAllowed allowed) j := by
  rw [verified_weakest, verified_weakest, h]

/-- A rule that also requires the claimed name to be `plain` is safe, but it
refuses mail from an allowed key with another name, and no unsafe world shows
that mail. -/
theorem name_check_unnecessary (allowed : K → Prop) (plain : N → Prop) {k : K} {n : N}
    (hk : allowed k) (hn : ¬ plain n) :
    Safe id (authorAllowed allowed) (fun i : Item K N => allowed i.author ∧ plain i.claimed) ∧
      ¬ (allowed k ∧ plain n) ∧ weakest id (authorAllowed allowed) (⟨k, n⟩ : Item K N) :=
  ⟨fun _ h => h.1, fun h => hn h.2, (verified_weakest allowed ⟨k, n⟩).2 hk⟩

/-- Accepting by the claimed name alone is unsafe: a key that is not allowed may
claim the name of one that is. -/
theorem name_policy_unsafe (allowed : K → Prop) (good : N → Prop) {bad : K} {n : N}
    (hbad : ¬ allowed bad) (hn : good n) :
    ¬ Safe id (authorAllowed allowed) (fun i : Item K N => good i.claimed) :=
  fun hs => hbad (hs ⟨bad, n⟩ hn)

/-- Without signatures, the recipient sees only the claimed name, and any key can
claim any name. Once some key is not allowed, no name may be accepted. -/
theorem unverified_accepts_nothing (allowed : K → Prop) {bad : K} (hbad : ¬ allowed bad)
    (n : N) : ¬ weakest (fun i : Item K N => i.claimed) (authorAllowed allowed) n :=
  fun h => hbad (h ⟨bad, n⟩ rfl)

/-- Hearing mail needs only a valid signature, so the default requirement is
`True`. The option of hearing only the registry refuses mail from a stranger's
key, which the default hears. -/
theorem registry_option_refuses_stranger (registry : K → Prop) {stranger : K}
    (hs : ¬ registry stranger) (n : N) :
    weakest id (fun _ : Item K N => True) (⟨stranger, n⟩ : Item K N) ∧
      ¬ weakest id (fun i : Item K N => True ∧ registry i.author) (⟨stranger, n⟩ : Item K N) :=
  ⟨fun _ _ => trivial, fun h => hs (h ⟨stranger, n⟩ rfl).2⟩

end Standing

/-! ## Non-vacuity: every hypothesis above is met on concrete values -/

section Examples

/-- Two keys, `0` allowed and `1` not; two names, `0` plain and `1` not. -/
private abbrev allowed₀ (k : Fin 2) : Prop := k = 0
private abbrev plain₀ (n : Fin 2) : Prop := n = 0

example : Safe id (authorAllowed allowed₀)
    (fun i : Item (Fin 2) (Fin 2) => allowed₀ i.author ∧ plain₀ i.claimed) ∧
      ¬ (allowed₀ 0 ∧ plain₀ 1) ∧
      weakest id (authorAllowed allowed₀) (⟨0, 1⟩ : Item (Fin 2) (Fin 2)) :=
  name_check_unnecessary allowed₀ plain₀ (k := 0) (n := 1) rfl (by decide)

example : ¬ Safe id (authorAllowed allowed₀) (fun i : Item (Fin 2) (Fin 2) => plain₀ i.claimed) :=
  name_policy_unsafe allowed₀ plain₀ (bad := 1) (n := 0) (by decide) rfl

example : ¬ weakest (fun i : Item (Fin 2) (Fin 2) => i.claimed) (authorAllowed allowed₀) 0 :=
  unverified_accepts_nothing allowed₀ (bad := 1) (by decide) 0

/-- The name check is safe and differs from the weakest policy, so
`unnecessary_refusal` applies to it. -/
example : ∃ o : Item (Fin 2) (Fin 2),
    ¬ (allowed₀ o.author ∧ plain₀ o.claimed) ∧ weakest id (authorAllowed allowed₀) o := by
  refine unnecessary_refusal (fun _ h => h.1) ?_
  intro heq
  have h := congrFun heq ⟨0, 1⟩
  have hw : weakest id (authorAllowed allowed₀) (⟨0, 1⟩ : Item (Fin 2) (Fin 2)) :=
    (verified_weakest allowed₀ _).2 rfl
  rw [← h] at hw
  exact absurd (hw.2 : (1 : Fin 2) = 0) (by decide)

/-- `refusal_necessary` with its hypotheses met: the weakest policy refuses key
`1`, and accepting everything accepts it. -/
example : ¬ Safe id (authorAllowed allowed₀) (fun _ : Item (Fin 2) (Fin 2) => True) :=
  refusal_necessary (o := (⟨1, 0⟩ : Item (Fin 2) (Fin 2)))
    (fun h => absurd (h ⟨1, 0⟩ rfl : (1 : Fin 2) = 0) (by decide)) trivial

/-- `default_weakest` and `weakest_finer` with their hypotheses met. -/
example : weakest id (fun _ : Item (Fin 2) (Fin 2) => True) (⟨1, 0⟩ : Item (Fin 2) (Fin 2)) :=
  default_weakest id (fun _ => True) (fun _ => True) (fun _ _ => ⟨trivial, trivial⟩)

/-- Seeing only the key already accepts key `0`; seeing the whole item accepts
it too. -/
example : weakest id (authorAllowed allowed₀) (⟨0, 1⟩ : Item (Fin 2) (Fin 2)) :=
  weakest_finer id (fun i : Item (Fin 2) (Fin 2) => i.author) (authorAllowed allowed₀)
    (o := ⟨0, 1⟩) (fun _ hw => hw)

/-- The mutant of `weakest_finer`: its converse fails. Seeing the key accepts the
item from key `0`; seeing only its claimed name refuses it. -/
theorem coarser_accepts_less :
    weakest id (authorAllowed allowed₀) (⟨0, 0⟩ : Item (Fin 2) (Fin 2)) ∧
      ¬ weakest (fun i : Item (Fin 2) (Fin 2) => i.claimed) (authorAllowed allowed₀) 0 :=
  ⟨(verified_weakest allowed₀ _).2 rfl, unverified_accepts_nothing allowed₀ (bad := 1) (by decide) 0⟩

end Examples

end Mettapedia.Protocols.Options.Weakest
