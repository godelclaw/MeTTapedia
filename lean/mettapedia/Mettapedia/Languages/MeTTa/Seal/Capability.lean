import Mettapedia.Logic.Derivation
import Mettapedia.Logic.DerivationGraph.CheckedCursor
import Mathlib.Logic.Relation
import Mathlib.Logic.Function.Basic

/-!
# The seal primitive as a capability calculus

`(new-seal NICK)` makes a brand with both rights, `sealer-of` and
`unsealer-of` keep one right, `(seal S V)` puts `V` in a box of the brand of
`S`, and `(unseal S X)` opens `X` only when it is a box of that brand. This
module runs these operations for any number of principals. Each principal acts
only through the values it holds, as in Morris's protection discipline and the
object-capability rules (initial conditions, parenthood, endowment,
introduction). A policy may restrict what trusted principals do; everyone else
may do anything enabled.

What a seal guarantees, whatever the untrusted principals do:

* **Rights only shrink** (`anyCap_of_reach`): after any run, a capability with
  a given right for an existing brand is held somewhere only if one was held
  before. No operation adds a right.
* **No unseal without the unsealer** (`unexposed_of_reach`): when nobody holds
  an unsealing capability for a brand, a nonce that occurs only inside boxes of
  that brand never occurs anywhere else.
* **No mint without the sealer** (`authentic_of_reach`, Morris's induction
  rule): when only trusted principals can seal with a brand, and they seal only
  values with a property `P`, every box of the brand holds a value with `P`.
* **Checked inference over a private mint** (`lcf_sound`, `lcf_complete`): a
  kernel that keeps the sealing right and seals only conclusions of checked rule
  instances whose premises it holds sealed makes exactly the derivable
  judgments available as boxes, to every principal. The inference service is
  public; only the sealing right is private. A leaked sealing right forges a
  box of a judgment that is not derivable (`Controls.leaked_sealer_forges`).

The model is an operational specification of the primitive. It says nothing
about a runtime's memory safety, reflection on equation bodies or foreign
functions; `Seal.Observation` states which observers a runtime must exclude for
the abstraction guarantees and shows what each excluded observer breaks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Seal

/-- The identity of one `new-seal`. -/
abbrev Brand := Nat

/-- A name that only `newNonce` makes, like `ν` in the ν-calculus. -/
abbrev Nonce := Nat

/-- The rights a capability carries. -/
structure Rights where
  sealRight : Bool
  unsealRight : Bool
  deriving DecidableEq, Repr

namespace Rights

/-- What `new-seal` returns. -/
def both : Rights := ⟨true, true⟩
/-- What `sealer-of` keeps. -/
def sealOnly : Rights := ⟨true, false⟩
/-- What `unsealer-of` keeps. -/
def unsealOnly : Rights := ⟨false, true⟩

/-- Attenuation: a right survives only if the held capability has it and it is
wanted. -/
def meet (held wanted : Rights) : Rights := ⟨held.sealRight && wanted.sealRight, held.unsealRight && wanted.unsealRight⟩

theorem meet_seal {held wanted : Rights} (kept : (held.meet wanted).sealRight = true) :
    held.sealRight = true := by
  simp only [meet, Bool.and_eq_true] at kept
  exact kept.1

theorem meet_unseal {held wanted : Rights} (kept : (held.meet wanted).unsealRight = true) :
    held.unsealRight = true := by
  simp only [meet, Bool.and_eq_true] at kept
  exact kept.1

end Rights

/-- Values held by principals: data, nonces, pairs, capabilities and boxes. A
box carries its brand and its content, as W7's capsules do; only `unseal`
reads the content. -/
inductive Val (D : Type) where
  | data (d : D)
  | nonce (n : Nonce)
  | pair (left right : Val D)
  | cap (brand : Brand) (rights : Rights)
  | box (brand : Brand) (content : Val D)
  deriving DecidableEq, Repr

/-- Who holds what, and the next fresh brand and nonce. -/
structure Config (D : Type) where
  holds : Nat → List (Val D)
  nextBrand : Brand
  nextNonce : Nonce

variable {D : Type}

/-- Principal `receiver` receives `v`; nothing else changes. Values are not
linear: a sender keeps what it sends. -/
def Config.give (c : Config D) (receiver : Nat) (v : Val D) : Config D :=
  { c with holds := Function.update c.holds receiver (c.holds receiver ++ [v]) }

theorem Config.mem_give {c : Config D} {receiver principal : Nat} {v w : Val D} :
    w ∈ (c.give receiver v).holds principal ↔
      w ∈ c.holds principal ∨ (principal = receiver ∧ w = v) := by
  unfold Config.give
  by_cases same : principal = receiver
  · subst same
    simp [Function.update_self]
  · simp [same]

/-- The `index`-th value held by `principal`. -/
def Config.held (c : Config D) (principal index : Nat) : Option (Val D) :=
  (c.holds principal)[index]?

theorem Config.mem_of_held {c : Config D} {principal index : Nat} {v : Val D}
    (found : c.held principal index = some v) : v ∈ c.holds principal :=
  List.mem_of_getElem? found

theorem Config.held_give_stable {c : Config D} {receiver principal index : Nat} {v w : Val D}
    (found : c.held principal index = some w) : (c.give receiver v).held principal index = some w := by
  unfold Config.give Config.held at *
  by_cases same : principal = receiver
  · subst same
    simp only [Function.update_self]
    rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
    exact found
  · simpa [Function.update_of_ne same] using found

theorem Config.held_give_last (c : Config D) (receiver : Nat) (v : Val D) :
    (c.give receiver v).held receiver (c.holds receiver).length = some v := by
  simp [Config.give, Config.held, Function.update_self]

/-- The operations, each performed by one principal on values it holds, named
by their positions in its list. -/
inductive Action (D : Type) where
  | newSeal
  | newNonce
  | make (d : D)
  | pair (left right : Nat)
  | fst (index : Nat)
  | snd (index : Nat)
  | attenuate (index : Nat) (wanted : Rights)
  | sealBox (capability content : Nat)
  | unsealBox (capability box : Nat)
  | send (index : Nat) (receiver : Nat)

namespace Action

/-- The value an enabled action produces and who receives it. A disabled
action (a missing value, a wrong shape, a missing right, a box of another
brand) produces nothing, as `unseal` gives no result for a foreign box. -/
def output (c : Config D) (principal : Nat) : Action D → Option (Nat × Val D)
  | .newSeal => some (principal, .cap c.nextBrand Rights.both)
  | .newNonce => some (principal, .nonce c.nextNonce)
  | .make d => some (principal, .data d)
  | .pair i j =>
      match c.held principal i, c.held principal j with
      | some v, some w => some (principal, .pair v w)
      | _, _ => none
  | .fst i =>
      match c.held principal i with
      | some (.pair v _) => some (principal, v)
      | _ => none
  | .snd i =>
      match c.held principal i with
      | some (.pair _ w) => some (principal, w)
      | _ => none
  | .attenuate i wanted =>
      match c.held principal i with
      | some (.cap b r) => some (principal, .cap b (r.meet wanted))
      | _ => none
  | .sealBox i j =>
      match c.held principal i, c.held principal j with
      | some (.cap b r), some v => if r.sealRight = true then some (principal, .box b v) else none
      | _, _ => none
  | .unsealBox i j =>
      match c.held principal i, c.held principal j with
      | some (.cap b r), some (.box b' v) =>
          if r.unsealRight = true ∧ b = b' then some (principal, v) else none
      | _, _ => none
  | .send i receiver =>
      match c.held principal i with
      | some v => some (receiver, v)
      | none => none

/-- `newSeal` and `newNonce` advance their counters. -/
def advance (c : Config D) : Action D → Config D
  | .newSeal => { c with nextBrand := c.nextBrand + 1 }
  | .newNonce => { c with nextNonce := c.nextNonce + 1 }
  | _ => c

/-- Perform an action: advance the counters and hand over its output. -/
def run (c : Config D) (principal : Nat) (a : Action D) : Option (Config D) :=
  (a.output c principal).map fun out => (a.advance c).give out.1 out.2

theorem advance_holds (c : Config D) (a : Action D) : (a.advance c).holds = c.holds := by
  cases a <;> rfl

theorem advance_nextBrand_ge (c : Config D) (a : Action D) :
    c.nextBrand ≤ (a.advance c).nextBrand := by
  cases a <;> simp [advance]

theorem advance_nextNonce_ge (c : Config D) (a : Action D) :
    c.nextNonce ≤ (a.advance c).nextNonce := by
  cases a <;> simp [advance]

theorem run_of_output {c : Config D} {principal receiver : Nat} {a : Action D} {v : Val D}
    (out : a.output c principal = some (receiver, v)) :
    a.run c principal = some ((a.advance c).give receiver v) := by
  simp [run, out]

/-! ### What each action produces -/

theorem output_pair {c : Config D} {p i j receiver : Nat} {v : Val D}
    (out : (Action.pair i j).output c p = some (receiver, v)) :
    receiver = p ∧ ∃ x y, c.held p i = some x ∧ c.held p j = some y ∧ v = .pair x y := by
  simp only [output] at out
  split at out
  · rename_i x y hx hy
    simp only [Option.some.injEq, Prod.mk.injEq] at out
    exact ⟨out.1.symm, x, y, hx, hy, out.2.symm⟩
  · cases out

theorem output_fst {c : Config D} {p i receiver : Nat} {v : Val D}
    (out : (Action.fst i).output c p = some (receiver, v)) :
    receiver = p ∧ ∃ y, c.held p i = some (.pair v y) := by
  simp only [output] at out
  split at out
  · rename_i x y hx
    simp only [Option.some.injEq, Prod.mk.injEq] at out
    obtain ⟨rfl, rfl⟩ := out
    exact ⟨rfl, y, hx⟩
  · cases out

theorem output_snd {c : Config D} {p i receiver : Nat} {v : Val D}
    (out : (Action.snd i).output c p = some (receiver, v)) :
    receiver = p ∧ ∃ x, c.held p i = some (.pair x v) := by
  simp only [output] at out
  split at out
  · rename_i x y hx
    simp only [Option.some.injEq, Prod.mk.injEq] at out
    obtain ⟨rfl, rfl⟩ := out
    exact ⟨rfl, x, hx⟩
  · cases out

theorem output_attenuate {c : Config D} {p i receiver : Nat} {wanted : Rights} {v : Val D}
    (out : (Action.attenuate i wanted).output c p = some (receiver, v)) :
    receiver = p ∧ ∃ b r, c.held p i = some (.cap b r) ∧ v = .cap b (r.meet wanted) := by
  simp only [output] at out
  split at out
  · rename_i b r hx
    simp only [Option.some.injEq, Prod.mk.injEq] at out
    exact ⟨out.1.symm, b, r, hx, out.2.symm⟩
  · cases out

theorem output_seal {c : Config D} {p i j receiver : Nat} {v : Val D}
    (out : (Action.sealBox i j).output c p = some (receiver, v)) :
    receiver = p ∧ ∃ b r x, c.held p i = some (.cap b r) ∧ r.sealRight = true ∧
      c.held p j = some x ∧ v = .box b x := by
  simp only [output] at out
  split at out
  · rename_i b r x hc hx
    split_ifs at out with allowed
    simp only [Option.some.injEq, Prod.mk.injEq] at out
    exact ⟨out.1.symm, b, r, x, hc, allowed, hx, out.2.symm⟩
  · cases out

theorem output_unseal {c : Config D} {p i j receiver : Nat} {v : Val D}
    (out : (Action.unsealBox i j).output c p = some (receiver, v)) :
    receiver = p ∧ ∃ b r, c.held p i = some (.cap b r) ∧ r.unsealRight = true ∧
      c.held p j = some (.box b v) := by
  simp only [output] at out
  split at out
  · rename_i b r b' x hc hx
    split_ifs at out with allowed
    simp only [Option.some.injEq, Prod.mk.injEq] at out
    obtain ⟨rfl, rfl⟩ := out
    obtain ⟨right, rfl⟩ := allowed
    exact ⟨rfl, b, r, hc, right, hx⟩
  · cases out

theorem output_send {c : Config D} {p i q receiver : Nat} {v : Val D}
    (out : (Action.send i q).output c p = some (receiver, v)) :
    receiver = q ∧ c.held p i = some v := by
  simp only [output] at out
  split at out
  · rename_i x hx
    simp only [Option.some.injEq, Prod.mk.injEq] at out
    obtain ⟨rfl, rfl⟩ := out
    exact ⟨rfl, hx⟩
  · cases out

/-- Only `send` hands its output to another principal. -/
theorem output_receiver {c : Config D} {p receiver : Nat} {a : Action D} {v : Val D}
    (out : a.output c p = some (receiver, v)) :
    (∃ i q, a = .send i q) ∨ receiver = p := by
  cases a with
  | send i q => exact Or.inl ⟨i, q, rfl⟩
  | newSeal =>
      simp only [output, Option.some.injEq, Prod.mk.injEq] at out
      exact Or.inr out.1.symm
  | newNonce =>
      simp only [output, Option.some.injEq, Prod.mk.injEq] at out
      exact Or.inr out.1.symm
  | make d =>
      simp only [output, Option.some.injEq, Prod.mk.injEq] at out
      exact Or.inr out.1.symm
  | pair i j => exact Or.inr (output_pair out).1
  | fst i => exact Or.inr (output_fst out).1
  | snd i => exact Or.inr (output_snd out).1
  | attenuate i wanted => exact Or.inr (output_attenuate out).1
  | sealBox i j => exact Or.inr (output_seal out).1
  | unsealBox i j => exact Or.inr (output_unseal out).1

end Action

/-- What each principal may do. A principal outside the trusted base may do
anything enabled. -/
abbrev Policy (D : Type) := Nat → Action D → Config D → Prop

/-- One action by one principal, allowed by the policy. -/
def Step (policy : Policy D) (c c' : Config D) : Prop :=
  ∃ principal a, policy principal a c ∧ a.run c principal = some c'

/-- Any number of steps. -/
abbrev Reach (policy : Policy D) := Relation.ReflTransGen (Step policy)

theorem Reach.invariant {policy : Policy D} (Inv : Config D → Prop)
    (preserve : ∀ c c', Inv c → Step policy c c' → Inv c') {c c' : Config D}
    (start : Inv c) (run : Reach policy c c') : Inv c' := by
  induction run with
  | refl => exact start
  | tail _ step ih => exact preserve _ _ ih step

/-- The shape of one step: the counters do not move back, and one principal
receives one new value produced by an enabled action. -/
theorem Step.cases {policy : Policy D} {c c' : Config D} (step : Step policy c c') :
    ∃ principal a receiver v, policy principal a c ∧ a.output c principal = some (receiver, v) ∧
      c.nextBrand ≤ c'.nextBrand ∧ c.nextNonce ≤ c'.nextNonce ∧
      (∀ q w, w ∈ c'.holds q ↔ w ∈ c.holds q ∨ (q = receiver ∧ w = v)) ∧
      (∀ q i w, c.held q i = some w → c'.held q i = some w) := by
  obtain ⟨principal, a, allowed, ran⟩ := step
  unfold Action.run at ran
  obtain ⟨⟨receiver, v⟩, out, rfl⟩ := Option.map_eq_some_iff.mp ran
  refine ⟨principal, a, receiver, v, allowed, out, ?_, ?_, ?_, ?_⟩
  · exact Action.advance_nextBrand_ge c a
  · exact Action.advance_nextNonce_ge c a
  · intro q w
    rw [Config.mem_give, Action.advance_holds]
  · intro q i w found
    have found' : (a.advance c).held q i = some w := by
      simpa [Config.held, Action.advance_holds] using found
    exact Config.held_give_stable found'

/-- Holdings only grow, at stable positions. -/
theorem Reach.held_stable {policy : Policy D} {c c' : Config D} (run : Reach policy c c')
    {q i : Nat} {w : Val D} (found : c.held q i = some w) : c'.held q i = some w := by
  induction run with
  | refl => exact found
  | tail _ step ih =>
      obtain ⟨_, _, _, _, _, _, _, _, _, stable⟩ := Step.cases step
      exact stable q i w ih

theorem Reach.mem_stable {policy : Policy D} {c c' : Config D} (run : Reach policy c c')
    {q : Nat} {w : Val D} (held : w ∈ c.holds q) : w ∈ c'.holds q := by
  obtain ⟨i, found⟩ := List.mem_iff_getElem?.mp held
  exact Config.mem_of_held (run.held_stable (i := i) found)

/-! ## Rights only shrink -/

/-- `v` contains a capability for brand `b` with the right selected by `right`,
anywhere, including inside boxes (an unsealer of the enclosing box could take it
out). -/
def Val.hasCap (b : Brand) (right : Rights → Bool) : Val D → Prop
  | .data _ => False
  | .nonce _ => False
  | .pair x y => x.hasCap b right ∨ y.hasCap b right
  | .cap b' r => b' = b ∧ right r = true
  | .box _ x => x.hasCap b right

@[simp] theorem Val.hasCap_data {b : Brand} {right : Rights → Bool} {d : D} :
    (Val.data d).hasCap b right ↔ False := Iff.rfl
@[simp] theorem Val.hasCap_nonce {b : Brand} {right : Rights → Bool} {n : Nonce} :
    (Val.nonce n : Val D).hasCap b right ↔ False := Iff.rfl
@[simp] theorem Val.hasCap_pair {b : Brand} {right : Rights → Bool} {x y : Val D} :
    (Val.pair x y).hasCap b right ↔ x.hasCap b right ∨ y.hasCap b right := Iff.rfl
@[simp] theorem Val.hasCap_cap {b b' : Brand} {right : Rights → Bool} {r : Rights} :
    (Val.cap b' r : Val D).hasCap b right ↔ b' = b ∧ right r = true := Iff.rfl
@[simp] theorem Val.hasCap_box {b b' : Brand} {right : Rights → Bool} {x : Val D} :
    (Val.box b' x).hasCap b right ↔ x.hasCap b right := Iff.rfl

/-- Somebody holds such a capability. -/
def Config.anyCap (c : Config D) (b : Brand) (right : Rights → Bool) : Prop :=
  ∃ principal v, v ∈ c.holds principal ∧ v.hasCap b right

/-- The two rights, each kept by attenuation only if the held capability has
it. -/
inductive RightSel : (Rights → Bool) → Prop
  | sealing : RightSel Rights.sealRight
  | unsealing : RightSel Rights.unsealRight

theorem RightSel.meet {right : Rights → Bool} (sel : RightSel right) {held wanted : Rights}
    (kept : right (held.meet wanted) = true) : right held = true := by
  cases sel
  · exact Rights.meet_seal kept
  · exact Rights.meet_unseal kept

/-- The value an action produces contains a capability for an existing brand
with a right only if a value the actor held does. -/
theorem output_hasCap {c : Config D} {p receiver : Nat} {a : Action D} {v : Val D}
    {b : Brand} {right : Rights → Bool} (sel : RightSel right) (old : b < c.nextBrand)
    (out : a.output c p = some (receiver, v)) (has : v.hasCap b right) :
    ∃ w, w ∈ c.holds p ∧ w.hasCap b right := by
  cases a with
  | newSeal =>
      simp only [Action.output, Option.some.injEq, Prod.mk.injEq] at out
      obtain ⟨_, rfl⟩ := out
      exact absurd (Val.hasCap_cap.mp has).1 (Nat.ne_of_gt old)
  | newNonce =>
      simp only [Action.output, Option.some.injEq, Prod.mk.injEq] at out
      obtain ⟨_, rfl⟩ := out
      exact (Val.hasCap_nonce.mp has).elim
  | make d =>
      simp only [Action.output, Option.some.injEq, Prod.mk.injEq] at out
      obtain ⟨_, rfl⟩ := out
      exact (Val.hasCap_data.mp has).elim
  | pair i j =>
      obtain ⟨_, x, y, hx, hy, rfl⟩ := Action.output_pair out
      rcases Val.hasCap_pair.mp has with hasX | hasY
      · exact ⟨x, Config.mem_of_held hx, hasX⟩
      · exact ⟨y, Config.mem_of_held hy, hasY⟩
  | fst i =>
      obtain ⟨_, y, hx⟩ := Action.output_fst out
      exact ⟨_, Config.mem_of_held hx, Val.hasCap_pair.mpr (Or.inl has)⟩
  | snd i =>
      obtain ⟨_, x, hx⟩ := Action.output_snd out
      exact ⟨_, Config.mem_of_held hx, Val.hasCap_pair.mpr (Or.inr has)⟩
  | attenuate i wanted =>
      obtain ⟨_, b', r, hx, rfl⟩ := Action.output_attenuate out
      obtain ⟨same, kept⟩ := Val.hasCap_cap.mp has
      exact ⟨_, Config.mem_of_held hx, Val.hasCap_cap.mpr ⟨same, sel.meet kept⟩⟩
  | sealBox i j =>
      obtain ⟨_, b', r, x, _, _, hx, rfl⟩ := Action.output_seal out
      exact ⟨x, Config.mem_of_held hx, Val.hasCap_box.mp has⟩
  | unsealBox i j =>
      obtain ⟨_, b', r, _, _, hx⟩ := Action.output_unseal out
      exact ⟨_, Config.mem_of_held hx, Val.hasCap_box.mpr has⟩
  | send i q =>
      obtain ⟨_, hx⟩ := Action.output_send out
      exact ⟨v, Config.mem_of_held hx, has⟩

/-- **Rights only shrink.** After any run, under any policy, a capability for
an existing brand with a given right is held somewhere only if one was held at
the start. -/
theorem anyCap_of_reach {policy : Policy D} {c c' : Config D} {b : Brand}
    {right : Rights → Bool} (sel : RightSel right) (run : Reach policy c c')
    (old : b < c.nextBrand) (now : c'.anyCap b right) : c.anyCap b right := by
  by_contra absent
  have keep := Reach.invariant (policy := policy)
    (fun c => b < c.nextBrand ∧ ¬ c.anyCap b right)
    (by
      rintro c c' ⟨older, none⟩ step
      obtain ⟨p, a, receiver, v, _, out, grows, _, members, _⟩ := Step.cases step
      refine ⟨lt_of_lt_of_le older grows, ?_⟩
      rintro ⟨q, w, held, has⟩
      rcases (members q w).mp held with old' | ⟨_, rfl⟩
      · exact none ⟨q, w, old', has⟩
      · obtain ⟨w', held', has'⟩ := output_hasCap sel older out has
        exact none ⟨p, w', held', has'⟩)
    ⟨old, absent⟩ run
  exact keep.2 now

/-! ## No unseal without the unsealer -/

/-- `v` shows nonce `m` somewhere other than inside a box of brand `b`. -/
def Val.exposes (b : Brand) (m : Nonce) : Val D → Prop
  | .data _ => False
  | .nonce n => n = m
  | .pair x y => x.exposes b m ∨ y.exposes b m
  | .cap _ _ => False
  | .box b' x => b' ≠ b ∧ x.exposes b m

@[simp] theorem Val.exposes_data {b : Brand} {m : Nonce} {d : D} :
    (Val.data d).exposes b m ↔ False := Iff.rfl
@[simp] theorem Val.exposes_nonce {b : Brand} {m n : Nonce} :
    (Val.nonce n : Val D).exposes b m ↔ n = m := Iff.rfl
@[simp] theorem Val.exposes_pair {b : Brand} {m : Nonce} {x y : Val D} :
    (Val.pair x y).exposes b m ↔ x.exposes b m ∨ y.exposes b m := Iff.rfl
@[simp] theorem Val.exposes_cap {b b' : Brand} {m : Nonce} {r : Rights} :
    (Val.cap b' r : Val D).exposes b m ↔ False := Iff.rfl
@[simp] theorem Val.exposes_box {b b' : Brand} {m : Nonce} {x : Val D} :
    (Val.box b' x).exposes b m ↔ b' ≠ b ∧ x.exposes b m := Iff.rfl

/-- Nobody's value shows `m` outside a box of brand `b`. -/
def Config.sealedUnder (c : Config D) (b : Brand) (m : Nonce) : Prop :=
  ∀ principal v, v ∈ c.holds principal → ¬ v.exposes b m

/-- The value an action produces shows the nonce only if a held value does,
when nobody can unseal the brand and the nonce already exists. -/
theorem output_exposes {c : Config D} {p receiver : Nat} {a : Action D} {v : Val D}
    {b : Brand} {m : Nonce} (oldNonce : m < c.nextNonce) (noUnsealer : ¬ c.anyCap b Rights.unsealRight)
    (out : a.output c p = some (receiver, v)) (shows : v.exposes b m) :
    ∃ w, w ∈ c.holds p ∧ w.exposes b m := by
  cases a with
  | newSeal =>
      simp only [Action.output, Option.some.injEq, Prod.mk.injEq] at out
      obtain ⟨_, rfl⟩ := out
      exact (Val.exposes_cap.mp shows).elim
  | newNonce =>
      simp only [Action.output, Option.some.injEq, Prod.mk.injEq] at out
      obtain ⟨_, rfl⟩ := out
      exact absurd (Val.exposes_nonce.mp shows) (Nat.ne_of_gt oldNonce)
  | make d =>
      simp only [Action.output, Option.some.injEq, Prod.mk.injEq] at out
      obtain ⟨_, rfl⟩ := out
      exact (Val.exposes_data.mp shows).elim
  | pair i j =>
      obtain ⟨_, x, y, hx, hy, rfl⟩ := Action.output_pair out
      rcases Val.exposes_pair.mp shows with sx | sy
      · exact ⟨x, Config.mem_of_held hx, sx⟩
      · exact ⟨y, Config.mem_of_held hy, sy⟩
  | fst i =>
      obtain ⟨_, y, hx⟩ := Action.output_fst out
      exact ⟨_, Config.mem_of_held hx, Val.exposes_pair.mpr (Or.inl shows)⟩
  | snd i =>
      obtain ⟨_, x, hx⟩ := Action.output_snd out
      exact ⟨_, Config.mem_of_held hx, Val.exposes_pair.mpr (Or.inr shows)⟩
  | attenuate i wanted =>
      obtain ⟨_, b', r, _, rfl⟩ := Action.output_attenuate out
      exact (Val.exposes_cap.mp shows).elim
  | sealBox i j =>
      obtain ⟨_, b', r, x, _, _, hx, rfl⟩ := Action.output_seal out
      exact ⟨x, Config.mem_of_held hx, (Val.exposes_box.mp shows).2⟩
  | unsealBox i j =>
      obtain ⟨_, b', r, hc, right, hx⟩ := Action.output_unseal out
      have other : b' ≠ b := by
        rintro rfl
        exact noUnsealer ⟨p, _, Config.mem_of_held hc, Val.hasCap_cap.mpr ⟨rfl, right⟩⟩
      exact ⟨_, Config.mem_of_held hx, Val.exposes_box.mpr ⟨other, shows⟩⟩
  | send i q =>
      obtain ⟨_, hx⟩ := Action.output_send out
      exact ⟨v, Config.mem_of_held hx, shows⟩

/-- **No unseal without the unsealer.** If nobody holds a capability that can
unseal brand `b`, a nonce that occurs only inside boxes of brand `b` keeps
occurring only there, after any run under any policy. -/
theorem unexposed_of_reach {policy : Policy D} {c c' : Config D} {b : Brand} {m : Nonce}
    (run : Reach policy c c') (oldBrand : b < c.nextBrand) (oldNonce : m < c.nextNonce)
    (noUnsealer : ¬ c.anyCap b Rights.unsealRight) (sealed : c.sealedUnder b m) :
    c'.sealedUnder b m := by
  have keep := Reach.invariant (policy := policy)
    (fun c => b < c.nextBrand ∧ m < c.nextNonce ∧ ¬ c.anyCap b Rights.unsealRight ∧ c.sealedUnder b m)
    (by
      rintro c c' ⟨older, olderNonce, none, hidden⟩ step
      obtain ⟨p, a, receiver, v, _, out, grows, growsNonce, members, _⟩ := Step.cases step
      refine ⟨lt_of_lt_of_le older grows, lt_of_lt_of_le olderNonce growsNonce, ?_, ?_⟩
      · rintro ⟨q, w, held, has⟩
        rcases (members q w).mp held with old' | ⟨_, rfl⟩
        · exact none ⟨q, w, old', has⟩
        · obtain ⟨w', held', has'⟩ := output_hasCap RightSel.unsealing older out has
          exact none ⟨p, w', held', has'⟩
      · intro q w held shows
        rcases (members q w).mp held with old' | ⟨_, rfl⟩
        · exact hidden q w old' shows
        · obtain ⟨w', held', shows'⟩ := output_exposes olderNonce none out shows
          exact hidden p w' held' shows')
    ⟨oldBrand, oldNonce, noUnsealer, sealed⟩ run
  exact keep.2.2.2

/-! ## No mint without the sealer -/

/-- Every box of brand `b` inside `v` holds a value with property `P`. -/
def Val.boxesSatisfy (b : Brand) (P : Val D → Prop) : Val D → Prop
  | .data _ => True
  | .nonce _ => True
  | .pair x y => x.boxesSatisfy b P ∧ y.boxesSatisfy b P
  | .cap _ _ => True
  | .box b' x => (b' = b → P x) ∧ x.boxesSatisfy b P

@[simp] theorem Val.boxesSatisfy_data {b : Brand} {P : Val D → Prop} {d : D} :
    (Val.data d).boxesSatisfy b P ↔ True := Iff.rfl
@[simp] theorem Val.boxesSatisfy_nonce {b : Brand} {P : Val D → Prop} {n : Nonce} :
    (Val.nonce n : Val D).boxesSatisfy b P ↔ True := Iff.rfl
@[simp] theorem Val.boxesSatisfy_pair {b : Brand} {P : Val D → Prop} {x y : Val D} :
    (Val.pair x y).boxesSatisfy b P ↔ x.boxesSatisfy b P ∧ y.boxesSatisfy b P := Iff.rfl
@[simp] theorem Val.boxesSatisfy_cap {b b' : Brand} {P : Val D → Prop} {r : Rights} :
    (Val.cap b' r : Val D).boxesSatisfy b P ↔ True := Iff.rfl
@[simp] theorem Val.boxesSatisfy_box {b b' : Brand} {P : Val D → Prop} {x : Val D} :
    (Val.box b' x).boxesSatisfy b P ↔ (b' = b → P x) ∧ x.boxesSatisfy b P := Iff.rfl

/-- Every box of brand `b` anywhere holds a value with property `P`. -/
def Config.allBoxes (c : Config D) (b : Brand) (P : Val D → Prop) : Prop :=
  ∀ principal v, v ∈ c.holds principal → v.boxesSatisfy b P

/-- The invariant of the authentication theorem: the brand exists, its boxes
hold `P`-values, and no untrusted principal can seal with it. -/
def Authentic (trusted : Nat → Prop) (b : Brand) (P : Val D → Prop) (c : Config D) : Prop :=
  b < c.nextBrand ∧ c.allBoxes b P ∧
    ∀ principal v, ¬ trusted principal → v ∈ c.holds principal → ¬ v.hasCap b Rights.sealRight

/-- What a policy must ensure of trusted principals: they seal with brand `b`
only `P`-values, given that every box of `b` so far holds one, and they never
hand a sealing capability for `b` to an untrusted principal. -/
structure TrustedSealing (policy : Policy D) (trusted : Nat → Prop) (b : Brand)
    (P : Val D → Prop) : Prop where
  seals : ∀ c p i j r x, trusted p → policy p (.sealBox i j) c → c.held p i = some (.cap b r) →
    r.sealRight = true → c.held p j = some x → c.allBoxes b P → P x
  keeps : ∀ c p i q v, trusted p → ¬ trusted q → policy p (.send i q) c → c.held p i = some v →
    ¬ v.hasCap b Rights.sealRight

theorem Authentic.step {policy : Policy D} {trusted : Nat → Prop} {b : Brand}
    {P : Val D → Prop} (rules : TrustedSealing policy trusted b P) {c c' : Config D}
    (inv : Authentic trusted b P c) (step : Step policy c c') : Authentic trusted b P c' := by
  obtain ⟨older, boxes, untrustedNone⟩ := inv
  obtain ⟨p, a, receiver, v, allowed, out, grows, _, members, _⟩ := Step.cases step
  -- The new value's boxes of brand `b` hold `P`-values.
  have newBoxes : v.boxesSatisfy b P := by
    cases a with
    | newSeal =>
        simp only [Action.output, Option.some.injEq, Prod.mk.injEq] at out
        obtain ⟨_, rfl⟩ := out
        exact Val.boxesSatisfy_cap.mpr trivial
    | newNonce =>
        simp only [Action.output, Option.some.injEq, Prod.mk.injEq] at out
        obtain ⟨_, rfl⟩ := out
        exact Val.boxesSatisfy_nonce.mpr trivial
    | make d =>
        simp only [Action.output, Option.some.injEq, Prod.mk.injEq] at out
        obtain ⟨_, rfl⟩ := out
        exact Val.boxesSatisfy_data.mpr trivial
    | pair i j =>
        obtain ⟨_, x, y, hx, hy, rfl⟩ := Action.output_pair out
        exact Val.boxesSatisfy_pair.mpr
          ⟨boxes p x (Config.mem_of_held hx), boxes p y (Config.mem_of_held hy)⟩
    | fst i =>
        obtain ⟨_, y, hx⟩ := Action.output_fst out
        exact (Val.boxesSatisfy_pair.mp (boxes p _ (Config.mem_of_held hx))).1
    | snd i =>
        obtain ⟨_, x, hx⟩ := Action.output_snd out
        exact (Val.boxesSatisfy_pair.mp (boxes p _ (Config.mem_of_held hx))).2
    | attenuate i wanted =>
        obtain ⟨_, b', r, _, rfl⟩ := Action.output_attenuate out
        exact Val.boxesSatisfy_cap.mpr trivial
    | sealBox i j =>
        obtain ⟨_, b', r, x, hc, right, hx, rfl⟩ := Action.output_seal out
        refine Val.boxesSatisfy_box.mpr ⟨?_, boxes p x (Config.mem_of_held hx)⟩
        intro same
        subst same
        by_cases isTrusted : trusted p
        · exact rules.seals c p i j r x isTrusted allowed hc right hx boxes
        · exact absurd (Val.hasCap_cap.mpr ⟨rfl, right⟩)
            (untrustedNone p _ isTrusted (Config.mem_of_held hc))
    | unsealBox i j =>
        obtain ⟨_, b', r, _, _, hx⟩ := Action.output_unseal out
        exact (Val.boxesSatisfy_box.mp (boxes p _ (Config.mem_of_held hx))).2
    | send i q =>
        obtain ⟨_, hx⟩ := Action.output_send out
        exact boxes p v (Config.mem_of_held hx)
  refine ⟨lt_of_lt_of_le older grows, ?_, ?_⟩
  · intro q w held
    rcases (members q w).mp held with old' | ⟨_, rfl⟩
    · exact boxes q w old'
    · exact newBoxes
  · intro q w notTrusted held has
    rcases (members q w).mp held with old' | ⟨rfl, rfl⟩
    · exact untrustedNone q w notTrusted old' has
    · rcases Action.output_receiver out with ⟨i, q', rfl⟩ | actor
      · obtain ⟨same, hx⟩ := Action.output_send out
        subst same
        by_cases senderTrusted : trusted p
        · exact rules.keeps c p i _ _ senderTrusted notTrusted allowed hx has
        · exact untrustedNone p _ senderTrusted (Config.mem_of_held hx) has
      · subst actor
        obtain ⟨w', held', has'⟩ := output_hasCap RightSel.sealing older out has
        exact untrustedNone _ w' notTrusted held' has'

/-- **No mint without the sealer** (Morris's induction rule). When the policy
lets only trusted principals seal with brand `b`, and they seal only
`P`-values, every box of brand `b` in every reachable configuration holds a
`P`-value; so does every value any principal obtains by unsealing one. -/
theorem authentic_of_reach {policy : Policy D} {trusted : Nat → Prop} {b : Brand}
    {P : Val D → Prop} (rules : TrustedSealing policy trusted b P) {c c' : Config D}
    (run : Reach policy c c') (start : Authentic trusted b P c) : Authentic trusted b P c' :=
  Reach.invariant _ (fun _ _ inv step => inv.step rules step) start run

theorem Authentic.box {trusted : Nat → Prop} {b : Brand} {P : Val D → Prop} {c : Config D}
    (inv : Authentic trusted b P c) {principal : Nat} {x : Val D}
    (held : Val.box b x ∈ c.holds principal) : P x :=
  (Val.boxesSatisfy_box.mp (inv.2.1 principal _ held)).1 rfl

/-! ## Checked inference over a private mint -/

section LCF

variable {J : Type} (rules : List J → J → Prop)

/-- The kernel's boxes hold derivable judgments. -/
def Derivable : Val J → Prop := fun v => ∃ j, v = .data j ∧ Mettapedia.Logic.Derives rules j

/-- What the kernel itself may do: seal only a conclusion of a rule instance
whose premises it holds in boxes of its brand, and send only values that cannot
seal with its brand. -/
def kernelAllows (b : Brand) (p : Nat) : Action J → Config J → Prop
  | .sealBox _ j, c => ∃ conclusion premises, c.held p j = some (.data conclusion) ∧
      rules premises conclusion ∧ ∀ premise ∈ premises, Val.box b (.data premise) ∈ c.holds p
  | .send i _, c => ∀ v, c.held p i = some v → ¬ v.hasCap b Rights.sealRight
  | _, _ => True

/-- The kernel `k` with brand `b`; every other principal may do anything,
including asking the kernel for inferences by sending it boxes. -/
def kernelPolicy (k : Nat) (b : Brand) : Policy J := fun p a c =>
  p ≠ k ∨ kernelAllows rules b p a c

theorem kernelPolicy_sealing (k : Nat) (b : Brand) :
    TrustedSealing (kernelPolicy rules k b) (· = k) b (Derivable rules) where
  seals := by
    intro c p i j r x isKernel allowed _ _ hx boxes
    rcases allowed with notKernel | ⟨conclusion, premises, hj, rule, held⟩
    · exact absurd isKernel notKernel
    · rw [hx] at hj
      cases hj
      refine ⟨conclusion, rfl, Mettapedia.Logic.Derives.node premises conclusion rule ?_⟩
      intro premise member
      obtain ⟨j', same, derived⟩ := (Val.boxesSatisfy_box.mp (boxes p _ (held premise member))).1 rfl
      cases same
      exact derived
  keeps := by
    intro c p i q v isKernel _ allowed hv
    rcases allowed with notKernel | keeps
    · exact absurd isKernel notKernel
    · exact keeps v hv

/-- The start: the kernel holds the sealer for an existing brand, nobody else
can seal with it, and every box of the brand already holds a derivable
judgment (typically: none exists). -/
structure KernelStart (k : Nat) (b : Brand) (c : Config J) : Prop where
  fresh : b < c.nextBrand
  boxes : c.allBoxes b (Derivable rules)
  othersCannotSeal : ∀ principal v, principal ≠ k → v ∈ c.holds principal →
    ¬ v.hasCap b Rights.sealRight

/-- **Soundness of the sealed kernel.** In every configuration reachable under
the kernel policy, every box of the kernel's brand, held by anybody, holds a
derivable judgment. A reader with the published unsealer obtains only
derivable judgments. -/
theorem lcf_sound {k : Nat} {b : Brand} {c c' : Config J} (start : KernelStart rules k b c)
    (run : Reach (kernelPolicy rules k b) c c') {principal : Nat} {x : Val J}
    (held : Val.box b x ∈ c'.holds principal) : Derivable rules x :=
  (authentic_of_reach (kernelPolicy_sealing rules k b) run
    ⟨start.fresh, start.boxes, start.othersCannotSeal⟩).box held

/-- The two LCF disciplines agree: every judgment a sealed kernel hands out is
the judgment of a certificate that the shared derivation-graph checker mints
(`CheckedJudgment.exists_mint_iff`). -/
theorem lcf_sound_certificate (interface : Mettapedia.Logic.RuleWitness rules) {Origin : Type}
    (origin : Origin) {k : Nat} {b : Brand} {c c' : Config J} (start : KernelStart rules k b c)
    (run : Reach (kernelPolicy rules k b) c c') {principal : Nat} {x : Val J}
    (held : Val.box b x ∈ c'.holds principal) :
    ∃ j, x = .data j ∧ ∃ (nodes : List (Mettapedia.Logic.DerivationGraph.Node J interface.W Origin))
      (root : Nat),
      (Mettapedia.Logic.DerivationGraph.CheckedJudgment.mint interface nodes root).map
        Mettapedia.Logic.DerivationGraph.CheckedJudgment.judgment = some j := by
  obtain ⟨j, rfl, derived⟩ := lcf_sound rules start run held
  exact ⟨j, rfl, (Mettapedia.Logic.DerivationGraph.CheckedJudgment.exists_mint_iff
    interface origin j).mpr derived⟩

/-- **Completeness of the public inference service.** For every derivable
judgment there is a run in which the kernel holds a box of it, from any
configuration where the kernel holds its sealer. -/
theorem lcf_complete {k : Nat} {b : Brand} {i : Nat} :
    ∀ {j : J}, Mettapedia.Logic.Derives rules j → ∀ c : Config J,
      c.held k i = some (.cap b Rights.both) →
      ∃ c', Reach (kernelPolicy rules k b) c c' ∧ Val.box b (.data j) ∈ c'.holds k := by
  intro j derived
  induction derived with
  | node premises conclusion rule _ ih =>
      intro c sealer
      -- First box every premise, one after another.
      have gather : ∀ (pending : List J), (∀ q ∈ pending, q ∈ premises) → ∀ c : Config J,
          c.held k i = some (.cap b Rights.both) →
          ∃ c', Reach (kernelPolicy rules k b) c c' ∧
            ∀ q ∈ pending, Val.box b (.data q) ∈ c'.holds k := by
        intro pending
        induction pending with
        | nil => intro _ c _; exact ⟨c, Relation.ReflTransGen.refl, by simp⟩
        | cons q rest ihRest =>
            intro sub c sealer'
            obtain ⟨c₁, run₁, boxed₁⟩ := ih q (sub q (List.mem_cons.mpr (Or.inl rfl))) c sealer'
            obtain ⟨c₂, run₂, boxed₂⟩ :=
              ihRest (fun q' m => sub q' (List.mem_cons.mpr (Or.inr m))) c₁
                (run₁.held_stable sealer')
            refine ⟨c₂, run₁.trans run₂, ?_⟩
            intro q' m
            rcases List.mem_cons.mp m with rfl | later
            · exact run₂.mem_stable boxed₁
            · exact boxed₂ q' later
      obtain ⟨c₁, run₁, boxed⟩ := gather premises (fun _ m => m) c sealer
      have sealer₁ := run₁.held_stable sealer
      -- The kernel makes the conclusion as data,
      have out₂ : (Action.make conclusion : Action J).output c₁ k = some (k, .data conclusion) := rfl
      let c₂ := ((Action.make conclusion : Action J).advance c₁).give k (.data conclusion)
      have step₂ : Step (kernelPolicy rules k b) c₁ c₂ :=
        ⟨k, .make conclusion, Or.inr trivial, Action.run_of_output out₂⟩
      have dataAt : c₂.held k (c₁.holds k).length = some (.data conclusion) :=
        Config.held_give_last c₁ k _
      have sealer₂ : c₂.held k i = some (.cap b Rights.both) :=
        Reach.held_stable (Relation.ReflTransGen.single step₂) sealer₁
      -- and seals it.
      have out₃ : (Action.sealBox i (c₁.holds k).length : Action J).output c₂ k =
          some (k, .box b (.data conclusion)) := by
        simp [Action.output, sealer₂, dataAt, Rights.both]
      let c₃ := ((Action.sealBox i (c₁.holds k).length : Action J).advance c₂).give k
        (.box b (.data conclusion))
      have step₃ : Step (kernelPolicy rules k b) c₂ c₃ := by
        refine ⟨k, .sealBox i (c₁.holds k).length, Or.inr ⟨conclusion, premises, dataAt, rule, ?_⟩,
          Action.run_of_output out₃⟩
        intro q m
        exact Reach.mem_stable (Relation.ReflTransGen.single step₂) (boxed q m)
      refine ⟨c₃, (run₁.tail step₂).tail step₃, ?_⟩
      exact Config.mem_of_held (Config.held_give_last _ k _)

end LCF

/-! ## Controls -/

namespace Controls

/-- Nobody holds anything; brands and nonces start at zero. -/
def empty : Config Bool := ⟨fun _ => [], 0, 0⟩

/-- Everybody may do anything. -/
def anything : Policy Bool := fun _ _ _ => True

/-- Principal 0 holds two brands' seals and a box of the first. -/
def twoSeals : Config Bool :=
  ((empty.give 0 (.cap 0 Rights.both)).give 0 (.cap 1 Rights.both)).give 0 (.box 0 (.data true))

/-- Two calls of `new-seal` give two brands; the second does not open a box of
the first: `unseal` produces nothing. The first does. -/
example : (Action.unsealBox 1 2 : Action Bool).output twoSeals 0 = none := by decide
example : (Action.unsealBox 0 2 : Action Bool).output twoSeals 0 = some (0, .data true) := by decide

/-- Principal 0 holds a sealer facet and a box. -/
def sealerAndBox : Config Bool := (empty.give 0 (.cap 0 Rights.sealOnly)).give 0 (.box 0 (.data true))
/-- Principal 0 holds an unsealer facet and a box. -/
def unsealerAndBox : Config Bool :=
  (empty.give 0 (.cap 0 Rights.unsealOnly)).give 0 (.box 0 (.data true))

/-- The sealer facet seals and does not unseal. -/
example : (Action.unsealBox 0 1 : Action Bool).output sealerAndBox 0 = none := by decide
example : (Action.sealBox 0 1 : Action Bool).output sealerAndBox 0 =
    some (0, .box 0 (.box 0 (.data true))) := by decide
/-- The unsealer facet unseals and does not seal. -/
example : (Action.sealBox 0 1 : Action Bool).output unsealerAndBox 0 = none := by decide
example : (Action.unsealBox 0 1 : Action Bool).output unsealerAndBox 0 = some (0, .data true) := by
  decide

/-- Attenuation never adds a right: `unsealer-of` of a sealer facet keeps
nothing. -/
example : (Action.attenuate 0 Rights.unsealOnly : Action Bool).output
    (empty.give 0 (.cap 0 Rights.sealOnly)) 0 = some (0, .cap 0 ⟨false, false⟩) := by decide

/-- A principal with the unsealer and a box of a nonce. -/
def unsealerAndNonce : Config Bool :=
  ((⟨fun _ => [], 1, 1⟩ : Config Bool).give 0 (.cap 0 Rights.unsealOnly)).give 0 (.box 0 (.nonce 0))

/-- With the unsealer the nonce is exposed in one step: the secrecy theorem
needs nobody to hold one. -/
example : ∃ c', Step anything unsealerAndNonce c' ∧ ¬ c'.sealedUnder 0 0 := by
  have out : (Action.unsealBox 0 1 : Action Bool).output unsealerAndNonce 0 = some (0, .nonce 0) := by
    decide
  refine ⟨_, ⟨0, .unsealBox 0 1, trivial, Action.run_of_output out⟩, ?_⟩
  intro sealed
  exact sealed 0 (.nonce 0) (Config.mem_of_held (Config.held_give_last _ 0 _)) rfl

/-- With only the sealer, it stays sealed, whatever anybody does. -/
def sealerAndNonce : Config Bool :=
  ((⟨fun _ => [], 1, 1⟩ : Config Bool).give 0 (.cap 0 Rights.sealOnly)).give 0 (.box 0 (.nonce 0))

example {c : Config Bool} (run : Reach anything sealerAndNonce c) : c.sealedUnder 0 0 := by
  refine unexposed_of_reach run (by decide) (by decide) ?_ ?_
  · rintro ⟨p, v, held, has⟩
    by_cases same : p = 0
    · subst same
      simp [sealerAndNonce, Config.give, Function.update_self] at held
      rcases held with rfl | rfl <;> simp [Rights.sealOnly] at has
    · simp [sealerAndNonce, Config.give, Function.update_of_ne same] at held
  · intro p v held shows
    by_cases same : p = 0
    · subst same
      simp [sealerAndNonce, Config.give, Function.update_self] at held
      rcases held with rfl | rfl <;> simp at shows
    · simp [sealerAndNonce, Config.give, Function.update_of_ne same] at held

/-- The kernel's judgments: only `true` is derivable. -/
def onlyTrue : List Bool → Bool → Prop := fun premises conclusion =>
  premises = [] ∧ conclusion = true

theorem false_not_derivable : ¬ Mettapedia.Logic.Derives onlyTrue false := by
  intro derived
  have := Mettapedia.Logic.Derives.least (rules := onlyTrue) (fun j => j = true)
    (fun _ _ rule _ => rule.2) derived
  cases this

/-- The kernel (principal 0) holds the sealer of brand 0. -/
def kernelStart : Config Bool := (⟨fun _ => [], 1, 0⟩ : Config Bool).give 0 (.cap 0 Rights.both)

theorem kernelStart_ok : KernelStart onlyTrue 0 0 kernelStart := by
  refine ⟨by decide, ?_, ?_⟩
  · intro p v held
    by_cases same : p = 0
    · subst same
      simp [kernelStart, Config.give, Function.update_self] at held
      subst held
      exact Val.boxesSatisfy_cap.mpr trivial
    · simp [kernelStart, Config.give, Function.update_of_ne same] at held
  · intro p v notKernel held
    simp [kernelStart, Config.give, Function.update_of_ne notKernel] at held

/-- Under the kernel policy nobody ever holds a box of `false`. -/
theorem no_false_box {c : Config Bool} (run : Reach (kernelPolicy onlyTrue 0 0) kernelStart c)
    (p : Nat) : Val.box 0 (.data false) ∉ c.holds p := by
  intro held
  obtain ⟨j, same, derived⟩ := lcf_sound onlyTrue kernelStart_ok run held
  cases same
  exact false_not_derivable derived

/-- Public inference: the kernel boxes `true`. -/
example : ∃ c, Reach (kernelPolicy onlyTrue 0 0) kernelStart c ∧
    Val.box 0 (.data true) ∈ c.holds 0 :=
  lcf_complete onlyTrue (i := 0)
    (Mettapedia.Logic.Derives.node [] true ⟨rfl, rfl⟩ (by simp)) kernelStart (by decide)

/-- **Negative control: a leaked sealer forges.** If the kernel sends its
sealer to principal 1, principal 1 boxes the judgment `false`, which is not
derivable. -/
theorem leaked_sealer_forges : ∃ c, Reach anything kernelStart c ∧
    Val.box 0 (.data false) ∈ c.holds 1 ∧ ¬ Mettapedia.Logic.Derives onlyTrue false := by
  have out₁ : (Action.send 0 1 : Action Bool).output kernelStart 0 = some (1, .cap 0 Rights.both) := by
    decide
  let c₁ := kernelStart.give 1 (.cap 0 Rights.both)
  have s₁ : Step anything kernelStart c₁ := ⟨0, .send 0 1, trivial, Action.run_of_output out₁⟩
  have out₂ : (Action.make false : Action Bool).output c₁ 1 = some (1, .data false) := rfl
  let c₂ := c₁.give 1 (.data false)
  have s₂ : Step anything c₁ c₂ := ⟨1, .make false, trivial, Action.run_of_output out₂⟩
  have out₃ : (Action.sealBox 0 1 : Action Bool).output c₂ 1 = some (1, .box 0 (.data false)) := by
    decide
  let c₃ := c₂.give 1 (.box 0 (.data false))
  have s₃ : Step anything c₂ c₃ := ⟨1, .sealBox 0 1, trivial, Action.run_of_output out₃⟩
  refine ⟨c₃, ((Relation.ReflTransGen.single s₁).tail s₂).tail s₃, ?_, false_not_derivable⟩
  exact Config.mem_of_held (Config.held_give_last _ 1 _)

end Controls

end Mettapedia.Languages.MeTTa.Seal
