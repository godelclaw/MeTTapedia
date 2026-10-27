/-!
# A capability kernel for a single address space

Protection domains share one address space. A capability names a domain's message ring or a physical
frame; a user mapping tags a frame with a protection key, and a domain reaches a mapping exactly when
its key register opens that key. The kernel mediates sending, listening, replying, allocating and
mapping frames, and lending a fresh frame to a domain one can send to.

The model is the abstract layer of a kernel in the style of SexOS: a ring per domain, a one-deep reply
slot, frames allocated in order. It records two ghost counters, calls heard and replies sent, so that
the authenticity of replies is a property of states.

Main results, for the kernel defined here (`step`):
- `Good.step`: the invariant is inductive;
- `step_store_authorized`, `step_mem_integrity`: a domain changes a frame only if it owns it or holds a
  capability to it (integrity as an upper bound on writes);
- `step_ring_integrity`, `step_caps_integrity`, `step_slot_integrity`: other domains' rings, tables
  and reply slots change only along authority the acting domain holds;
- `step_ring_caps_fixed`: the communication graph never changes after genesis;
- `Good.answered_le_heard`: every reply is backed by a distinct call the replier heard;
- `Good.frame_access_confined`: a domain reaches another domain's memory only if that domain can send
  to it and lent the frame.

`SingleAddressSpaceAsWritten` gives the kernel as SexOS writes it, its counterexamples, and the
simulation showing that both kernels agree on every operation this one accepts.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel

/-- Point update of a function. -/
def upd {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) : α → β :=
  fun x => if x = a then b else f x

@[simp] theorem upd_same {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) :
    upd f a b a = b := by simp [upd]

@[simp] theorem upd_ne {α β : Type} [DecidableEq α] (f : α → β) {a x : α} (b : β) (h : x ≠ a) :
    upd f a b x = f x := by simp [upd, h]

theorem upd_apply {α β : Type} [DecidableEq α] (f : α → β) (a : α) (b : β) (x : α) :
    upd f a b x = if x = a then b else f x := rfl

/-- What a capability names. -/
inductive Obj (D : Type) where
  | ring (d : D)
  | frame (f : Nat)
  deriving DecidableEq, Repr

/-- A capability: its object and whether it carries write (send, store) authority. -/
structure Cap (D : Type) where
  obj : Obj D
  write : Bool
  deriving DecidableEq, Repr

/-- Fixed parameters: each domain's protection key, and the capacity of a ring. -/
structure Config (D : Type) where
  key : D → Nat
  key_inj : ∀ a b, key a = key b → a = b
  bound : Nat

/-- Kernel state. `heard d e` counts calls from `e` that `d` received; `answered d e` counts replies from
`d` to `e`. They are ghost state: no transition reads them. -/
structure State (D : Type) where
  caps : D → Nat → Option (Cap D)
  ring : D → List (D × Nat)
  owner : Nat → Option D
  maps : List (Nat × Nat)
  mask : D → Nat → Bool
  mem : Nat → Nat
  fresh : Nat
  pending : D → List D
  slot : D → Option Nat
  heard : D → D → Nat
  answered : D → D → Nat

/-- What a domain asks of the kernel, or does in user mode (`store`, `load`, `setKeys`). -/
inductive Op (D : Type) where
  | send (slot word : Nat)
  | listen
  | reply (to : D) (word : Nat)
  | alloc
  | map (frame : Nat)
  | lend (slot dst : Nat)
  | mapLent (slot : Nat)
  | store (frame word : Nat)
  | load (frame : Nat)
  | setKeys (key : Nat)

/-- What the domain sees. -/
inductive Result (D : Type) where
  | done (word : Nat)
  | message (sender : D) (word : Nat)
  | answer (word : Nat)
  | empty
  | refused
  deriving DecidableEq, Repr

variable {D : Type} [DecidableEq D]

/-- A domain reaches a frame in user mode: some mapping of it carries a key its register opens. -/
def canAccess (s : State D) (d : D) (f : Nat) : Bool :=
  s.maps.any fun m => m.1 == f && s.mask d m.2

/-- `d` holds a capability to frame `f`. -/
def HoldsFrame (s : State D) (d : D) (f : Nat) : Prop :=
  ∃ sl w, s.caps d sl = some ⟨.frame f, w⟩

/-- `d` holds a capability to the ring of `t`. -/
def HoldsRing (s : State D) (d t : D) : Prop :=
  ∃ sl w, s.caps d sl = some ⟨.ring t, w⟩

/-- Two-level update of a table. -/
def upd2 {β : Type} (f : D → Nat → β) (d : D) (n : Nat) (b : β) : D → Nat → β :=
  upd f d (upd (f d) n b)

/-- Two-level update of a counter. -/
def bump (f : D → D → Nat) (d e : D) : D → D → Nat :=
  upd f d (upd (f d) e (f d e + 1))

/-- The kernel's step. A refused request leaves the state unchanged. -/
def step (c : Config D) (s : State D) (d : D) : Op D → State D × Result D
  | .send sl w =>
      match s.caps d sl with
      | some ⟨.ring t, true⟩ =>
          if (s.ring t).length < c.bound then
            ({ s with ring := upd s.ring t (s.ring t ++ [(d, w)]) }, .done 0)
          else (s, .refused)
      | _ => (s, .refused)
  | .listen =>
      match s.slot d with
      | some w => ({ s with slot := upd s.slot d none }, .answer w)
      | none =>
          match s.ring d with
          | [] => (s, .empty)
          | (e, w) :: rest =>
              ({ s with ring := upd s.ring d rest, pending := upd s.pending d (e :: s.pending d),
                        heard := bump s.heard d e }, .message e w)
  | .reply t w =>
      if t ∈ s.pending d then
        ({ s with pending := upd s.pending d ((s.pending d).erase t), slot := upd s.slot t (some w),
                  answered := bump s.answered d t }, .done 0)
      else (s, .refused)
  | .alloc => ({ s with owner := upd s.owner s.fresh (some d), fresh := s.fresh + 1 }, .done s.fresh)
  | .map f =>
      if s.owner f = some d then ({ s with maps := (f, c.key d) :: s.maps }, .done 0)
      else (s, .refused)
  | .lend sl dst =>
      match s.caps d sl with
      | some ⟨.ring t, _⟩ =>
          if s.caps t dst = none then
            ({ s with owner := upd s.owner s.fresh (some d), fresh := s.fresh + 1,
                      maps := (s.fresh, c.key d) :: s.maps,
                      caps := upd2 s.caps t dst (some ⟨.frame s.fresh, true⟩) }, .done s.fresh)
          else (s, .refused)
      | _ => (s, .refused)
  | .mapLent sl =>
      match s.caps d sl with
      | some ⟨.frame f, true⟩ => ({ s with maps := (f, c.key d) :: s.maps }, .done 0)
      | _ => (s, .refused)
  | .store f w =>
      if canAccess s d f then ({ s with mem := upd s.mem f w }, .done 0) else (s, .refused)
  | .load f => if canAccess s d f then (s, .done (s.mem f)) else (s, .refused)
  | .setKeys _ => (s, .refused)

/-! ## The invariant -/

/-- The inductive invariant of the kernel. -/
structure Good (c : Config D) (s : State D) : Prop where
  /-- A domain's key register opens only its own key. -/
  mask_own : ∀ d k, s.mask d k = true → k = c.key d
  /-- Every user mapping is justified for the domain whose key it carries. -/
  maps_ok : ∀ f k, (f, k) ∈ s.maps → ∀ d, c.key d = k → s.owner f = some d ∨ HoldsFrame s d f
  /-- Frames at or above `fresh` are unallocated and unnamed. -/
  fresh_owner : ∀ f, s.fresh ≤ f → s.owner f = none
  fresh_caps : ∀ d sl f w, s.caps d sl = some ⟨.frame f, w⟩ → f < s.fresh
  /-- A frame capability was lent: its frame's owner can send to its holder. -/
  lent : ∀ d sl f w, s.caps d sl = some ⟨.frame f, w⟩ → ∃ e, s.owner f = some e ∧ HoldsRing s e d
  /-- Reply accounting: each heard call is still pending or has been answered once. -/
  replies : ∀ d e, (s.pending d).count e + s.answered d e = s.heard d e

section lemmas

variable {c : Config D} {s : State D}

omit [DecidableEq D] in
theorem canAccess_iff (s : State D) (d : D) (f : Nat) :
    canAccess s d f = true ↔ ∃ k, (f, k) ∈ s.maps ∧ s.mask d k = true := by
  unfold canAccess
  constructor
  · intro h
    obtain ⟨⟨f', k⟩, hm, hb⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq] at hb
    exact ⟨k, hb.1 ▸ hm, hb.2⟩
  · rintro ⟨k, hm, hk⟩
    exact List.any_eq_true.mpr ⟨(f, k), hm, by simp [hk]⟩

/-- In a good state a domain reaches only frames it owns or holds a capability to. -/
theorem Good.access (hg : Good c s) {d : D} {f : Nat} (h : canAccess s d f = true) :
    s.owner f = some d ∨ HoldsFrame s d f := by
  obtain ⟨k, hm, hk⟩ := (canAccess_iff s d f).mp h
  exact hg.maps_ok f k hm d (hg.mask_own d k hk).symm

theorem Good.owner_lt (hg : Good c s) {f : Nat} {d : D} (h : s.owner f = some d) : f < s.fresh := by
  rcases Nat.lt_or_ge f s.fresh with h' | h'
  · exact h'
  · have := hg.fresh_owner f h'
    simp [this] at h

theorem count_erase_self (l : List D) (a : D) (h : a ∈ l) :
    (l.erase a).count a + 1 = l.count a := by
  rw [List.count_erase_self]
  have : 0 < l.count a := List.count_pos_iff.mpr h
  omega

theorem count_erase_other (l : List D) {a b : D} (h : b ≠ a) : (l.erase a).count b = l.count b :=
  List.count_erase_of_ne h

theorem bump_same (f : D → D → Nat) (d e : D) : bump f d e d e = f d e + 1 := by simp [bump]

theorem bump_ne_left (f : D → D → Nat) {d e x : D} (y : D) (h : x ≠ d) : bump f d e x y = f x y := by
  simp [bump, h]

theorem bump_ne_right (f : D → D → Nat) {d e y : D} (h : y ≠ e) : bump f d e d y = f d y := by
  simp [bump, h]

end lemmas

/-! ## Preservation -/

section preservation

variable {c : Config D}

omit [DecidableEq D] in
theorem HoldsRing_of_caps {s s' : State D} (hc : s'.caps = s.caps) {d t : D} :
    HoldsRing s' d t ↔ HoldsRing s d t := by
  unfold HoldsRing; rw [hc]

omit [DecidableEq D] in
theorem HoldsFrame_of_caps {s s' : State D} (hc : s'.caps = s.caps) {d : D} {f : Nat} :
    HoldsFrame s' d f ↔ HoldsFrame s d f := by
  unfold HoldsFrame; rw [hc]

/-- A step that changes only rings, reply bookkeeping and memory keeps the invariant, given the reply
accounting. -/
theorem Good.of_frame_fields {s s' : State D} (hg : Good c s) (hc : s'.caps = s.caps)
    (ho : s'.owner = s.owner) (hm : s'.maps = s.maps) (hk : s'.mask = s.mask) (hf : s'.fresh = s.fresh)
    (hr : ∀ d e, (s'.pending d).count e + s'.answered d e = s'.heard d e) : Good c s' where
  mask_own := by rw [hk]; exact hg.mask_own
  maps_ok := by
    intro f k hmem d hkd
    rw [hm] at hmem
    rw [ho, HoldsFrame_of_caps hc]
    exact hg.maps_ok f k hmem d hkd
  fresh_owner := by rw [ho, hf]; exact hg.fresh_owner
  fresh_caps := by rw [hc, hf]; exact hg.fresh_caps
  lent := by
    intro d sl f w h
    rw [hc] at h
    obtain ⟨e, he, hr⟩ := hg.lent d sl f w h
    exact ⟨e, ho ▸ he, (HoldsRing_of_caps hc).mpr hr⟩
  replies := hr

theorem Good.next {s : State D} (hg : Good c s) (d : D) (op : Op D) : Good c (step c s d op).1 := by
  cases op with
  | send sl w =>
      simp only [step]
      split
      · split
        · exact hg.of_frame_fields rfl rfl rfl rfl rfl hg.replies
        · exact hg
      · exact hg
  | listen =>
      simp only [step]
      split
      · exact hg.of_frame_fields rfl rfl rfl rfl rfl hg.replies
      · split
        · exact hg
        · rename_i e w rest _
          refine hg.of_frame_fields rfl rfl rfl rfl rfl ?_
          intro x y
          dsimp only
          by_cases hx : x = d
          · subst hx
            have h1 := hg.replies x y
            by_cases hy : y = e
            · subst hy
              rw [upd_same, bump_same, List.count_cons_self]; omega
            · rw [upd_same, bump_ne_right _ hy, List.count_cons_of_ne (Ne.symm hy)]; exact h1
          · rw [upd_ne _ _ hx, bump_ne_left _ _ hx]; exact hg.replies x y
  | reply t w =>
      simp only [step]
      split
      · rename_i hmem
        refine hg.of_frame_fields rfl rfl rfl rfl rfl ?_
        intro x y
        dsimp only
        by_cases hx : x = d
        · subst hx
          have h1 := hg.replies x y
          by_cases hy : y = t
          · subst hy
            have h2 := count_erase_self (s.pending x) y hmem
            rw [upd_same, bump_same]; omega
          · rw [upd_same, bump_ne_right _ hy, count_erase_other _ hy]; exact h1
        · rw [upd_ne _ _ hx, bump_ne_left _ _ hx]; exact hg.replies x y
      · exact hg
  | alloc =>
      simp only [step]
      refine ⟨hg.mask_own, ?_, ?_, ?_, ?_, hg.replies⟩ <;> dsimp only
      · intro f k hm e hke
        rcases hg.maps_ok f k hm e hke with h | h
        · left
          have hlt := hg.owner_lt h
          simp [upd, Nat.ne_of_lt hlt, h]
        · exact Or.inr h
      · intro f hf
        simp [upd, show f ≠ s.fresh by omega, hg.fresh_owner f (by omega)]
      · intro e sl f w h
        have := hg.fresh_caps e sl f w h; omega
      · intro e sl f w h
        obtain ⟨o, ho, hr⟩ := hg.lent e sl f w h
        have hlt := hg.fresh_caps e sl f w h
        exact ⟨o, by simp [upd, Nat.ne_of_lt hlt, ho], hr⟩
  | map f =>
      simp only [step]
      split
      · rename_i hown
        refine ⟨hg.mask_own, ?_, hg.fresh_owner, hg.fresh_caps, hg.lent, hg.replies⟩
        intro f' k hm e hke
        rcases List.mem_cons.mp hm with h | h
        · cases h
          have : e = d := c.key_inj e d hke
          subst this
          exact Or.inl hown
        · exact hg.maps_ok f' k h e hke
      · exact hg
  | lend sl dst =>
      simp only [step]
      split
      · rename_i t w hcap
        split
        · rename_i hfree
          have hnew : ∀ e n, (upd2 s.caps t dst (some ⟨.frame s.fresh, true⟩)) e n =
              if e = t ∧ n = dst then some ⟨.frame s.fresh, true⟩ else s.caps e n := by
            intro e n
            by_cases he : e = t
            · subst he; by_cases hn : n = dst
              · subst hn; simp [upd2, upd]
              · simp [upd2, upd, hn]
            · simp [upd2, upd, he]
          -- every capability present before is still present
          have hkeep : ∀ e n x, s.caps e n = some x →
              (upd2 s.caps t dst (some ⟨.frame s.fresh, true⟩)) e n = some x := by
            intro e n x h
            rw [hnew]
            by_cases h' : e = t ∧ n = dst
            · obtain ⟨rfl, rfl⟩ := h'; rw [hfree] at h; cases h
            · simp [h', h]
          have hring_keep : ∀ a b, HoldsRing s a b →
              ∃ sl w, (upd2 s.caps t dst (some ⟨.frame s.fresh, true⟩)) a sl = some ⟨.ring b, w⟩ := by
            rintro a b ⟨sl', w', h⟩; exact ⟨sl', w', hkeep a sl' _ h⟩
          refine ⟨hg.mask_own, ?_, ?_, ?_, ?_, hg.replies⟩ <;> dsimp only
          · intro f k hm e hke
            rcases List.mem_cons.mp hm with h | h
            · cases h
              have : e = d := c.key_inj e d hke
              subst this
              left; simp [upd]
            · rcases hg.maps_ok f k h e hke with h' | ⟨sl', w', h'⟩
              · left
                have hlt := hg.owner_lt h'
                simp [upd, Nat.ne_of_lt hlt, h']
              · exact Or.inr ⟨sl', w', hkeep e sl' _ h'⟩
          · intro f hf
            simp [upd, show f ≠ s.fresh by omega, hg.fresh_owner f (by omega)]
          · intro e n f w' h
            rw [hnew] at h
            by_cases h' : e = t ∧ n = dst
            · simp [h'] at h; omega
            · simp [h'] at h
              have := hg.fresh_caps e n f w' h; omega
          · intro e n f w' h
            rw [hnew] at h
            by_cases h' : e = t ∧ n = dst
            · simp [h'] at h
              obtain ⟨rfl, -⟩ := h
              obtain ⟨rfl, -⟩ := h'
              exact ⟨d, by simp [upd], hring_keep d e ⟨sl, w, hcap⟩⟩
            · simp [h'] at h
              obtain ⟨o, ho, hr⟩ := hg.lent e n f w' h
              have hlt := hg.fresh_caps e n f w' h
              exact ⟨o, by simp [upd, Nat.ne_of_lt hlt, ho], hring_keep o e hr⟩
        · exact hg
      · exact hg
  | mapLent sl =>
      simp only [step]
      split
      · rename_i f hcap
        refine ⟨hg.mask_own, ?_, hg.fresh_owner, hg.fresh_caps, hg.lent, hg.replies⟩
        intro f' k hm e hke
        rcases List.mem_cons.mp hm with h | h
        · cases h
          have : e = d := c.key_inj e d hke
          subst this
          exact Or.inr ⟨sl, true, hcap⟩
        · exact hg.maps_ok f' k h e hke
      · exact hg
  | store f w =>
      simp only [step]
      split
      · exact hg.of_frame_fields rfl rfl rfl rfl rfl hg.replies
      · exact hg
  | load f =>
      simp only [step]
      split <;> exact hg
  | setKeys k => exact hg

end preservation

/-! ## Runs -/

/-- States reachable from `s₀` by any sequence of requests from any domains. -/
inductive Reachable (c : Config D) (s₀ : State D) : State D → Prop
  | init : Reachable c s₀ s₀
  | next {s : State D} (d : D) (op : Op D) : Reachable c s₀ s → Reachable c s₀ (step c s d op).1

theorem Reachable.good {c : Config D} {s₀ s : State D} (h₀ : Good c s₀) (h : Reachable c s₀ s) :
    Good c s := by
  induction h with
  | init => exact h₀
  | next d op _ ih => exact ih.next d op

/-! ## Properties of single steps -/

section properties

variable {c : Config D} {s : State D}

/-- A store succeeds only on a frame the domain owns or holds a capability to. -/
theorem step_store_authorized (hg : Good c s) {d : D} {f w : Nat}
    (h : (step c s d (.store f w)).2 ≠ .refused) : s.owner f = some d ∨ HoldsFrame s d f := by
  simp only [step] at h
  split at h
  · exact hg.access ‹_›
  · exact absurd rfl h

/-- A load succeeds only on a frame the domain owns or holds a capability to. -/
theorem step_load_authorized (hg : Good c s) {d : D} {f : Nat}
    (h : (step c s d (.load f)).2 ≠ .refused) : s.owner f = some d ∨ HoldsFrame s d f := by
  simp only [step] at h
  split at h
  · exact hg.access ‹_›
  · exact absurd rfl h

/-- Integrity of memory: a frame's contents change only through a domain that owns it or holds a
capability to it. -/
theorem step_mem_integrity (hg : Good c s) (d : D) (op : Op D) {f : Nat}
    (h : (step c s d op).1.mem f ≠ s.mem f) : s.owner f = some d ∨ HoldsFrame s d f := by
  cases op with
  | store g w =>
      simp only [step] at h
      split at h
      · rename_i hacc
        by_cases hfg : f = g
        · subst hfg; exact hg.access hacc
        · simp [upd, hfg] at h
      · exact absurd rfl h
  | send => simp only [step] at h; split at h <;> (try split at h) <;> exact absurd rfl h
  | listen => simp only [step] at h; split at h <;> (try split at h) <;> exact absurd rfl h
  | reply => simp only [step] at h; split at h <;> exact absurd rfl h
  | alloc => exact absurd rfl h
  | map => simp only [step] at h; split at h <;> exact absurd rfl h
  | lend => simp only [step] at h; split at h <;> (try split at h) <;> exact absurd rfl h
  | mapLent => simp only [step] at h; split at h <;> exact absurd rfl h
  | load => simp only [step] at h; split at h <;> exact absurd rfl h
  | setKeys => exact absurd rfl h

/-- Integrity of rings: another domain's ring changes only if the acting domain can send to it. -/
theorem step_ring_integrity (d : D) (op : Op D) {t : D} (ht : t ≠ d)
    (h : (step c s d op).1.ring t ≠ s.ring t) : ∃ sl, s.caps d sl = some ⟨.ring t, true⟩ := by
  cases op with
  | send sl w =>
      simp only [step] at h
      split at h
      · rename_i t' hcap
        split at h
        · by_cases htt : t = t'
          · subst htt; exact ⟨sl, hcap⟩
          · simp [upd, htt] at h
        · exact absurd rfl h
      · exact absurd rfl h
  | listen =>
      simp only [step] at h
      split at h
      · exact absurd rfl h
      · split at h
        · exact absurd rfl h
        · simp [upd, ht] at h
  | reply => simp only [step] at h; split at h <;> exact absurd rfl h
  | alloc => exact absurd rfl h
  | map => simp only [step] at h; split at h <;> exact absurd rfl h
  | lend => simp only [step] at h; split at h <;> (try split at h) <;> exact absurd rfl h
  | mapLent => simp only [step] at h; split at h <;> exact absurd rfl h
  | store => simp only [step] at h; split at h <;> exact absurd rfl h
  | load => simp only [step] at h; split at h <;> exact absurd rfl h
  | setKeys => exact absurd rfl h

/-- Integrity of capability tables: a domain's table changes only by a loan from a domain that can send
to it, and the new capability names a fresh frame owned by the lender. -/
theorem step_caps_cases (d : D) (op : Op D) :
    (step c s d op).1.caps = s.caps ∨
      ∃ sl dst t w, op = .lend sl dst ∧ s.caps d sl = some ⟨.ring t, w⟩ ∧ s.caps t dst = none ∧
        (step c s d op).1.caps = upd2 s.caps t dst (some ⟨.frame s.fresh, true⟩) ∧
        (step c s d op).1.owner = upd s.owner s.fresh (some d) := by
  cases op with
  | lend sl dst =>
      cases hc : s.caps d sl with
      | none => left; simp [step, hc]
      | some cp =>
          obtain ⟨o, w⟩ := cp
          cases o with
          | frame f => left; simp [step, hc]
          | ring t =>
              by_cases hfree : s.caps t dst = none
              · right; exact ⟨sl, dst, t, w, rfl, hc, hfree, by simp [step, hc, hfree], by simp [step, hc, hfree]⟩
              · left; simp [step, hc, hfree]
  | send sl w => left; simp only [step]; split <;> (try split) <;> rfl
  | listen => left; simp only [step]; split <;> (try split) <;> rfl
  | reply => left; simp only [step]; split <;> rfl
  | alloc => left; rfl
  | map => left; simp only [step]; split <;> rfl
  | mapLent => left; simp only [step]; split <;> rfl
  | store => left; simp only [step]; split <;> rfl
  | load => left; simp only [step]; split <;> rfl
  | setKeys => left; rfl

/-- Integrity of capability tables: a domain's table changes only by a loan from a domain that can send
to it, and the new capability names a fresh frame owned by the lender. -/
theorem step_caps_integrity (d : D) (op : Op D) {t : D} {n : Nat}
    (h : (step c s d op).1.caps t n ≠ s.caps t n) :
    HoldsRing s d t ∧ s.caps t n = none ∧
      (step c s d op).1.caps t n = some ⟨.frame s.fresh, true⟩ ∧
      (step c s d op).1.owner s.fresh = some d := by
  rcases step_caps_cases d op with hc | ⟨sl, dst, t', w, -, hcap, hfree, hcaps, hown⟩
  · rw [hc] at h; exact absurd rfl h
  · rw [hcaps] at h ⊢
    rw [hown]
    by_cases htt : t = t'
    · subst htt
      by_cases hn : n = dst
      · subst hn
        exact ⟨⟨sl, w, hcap⟩, hfree, by simp [upd2], by simp⟩
      · simp [upd2, upd, hn] at h
    · simp [upd2, upd, htt] at h

/-- The communication graph is fixed: ring capabilities are never created, moved or removed. -/
theorem step_ring_caps_fixed (d : D) (op : Op D) (t : D) (n : Nat) (e : D) (w : Bool) :
    (step c s d op).1.caps t n = some ⟨.ring e, w⟩ ↔ s.caps t n = some ⟨.ring e, w⟩ := by
  by_cases h : (step c s d op).1.caps t n = s.caps t n
  · rw [h]
  · obtain ⟨-, hnone, hnew, -⟩ := step_caps_integrity d op h
    rw [hnew, hnone]; simp

/-- A reply slot changes only through a reply from a domain that heard a call from its owner and has
not yet answered it, or through the owner's own listen. -/
theorem step_slot_integrity (d : D) (op : Op D) {t : D} (ht : t ≠ d)
    (h : (step c s d op).1.slot t ≠ s.slot t) : t ∈ s.pending d := by
  cases op with
  | reply t' w =>
      simp only [step] at h
      split at h
      · rename_i hmem
        by_cases htt : t = t'
        · subst htt; exact hmem
        · simp [upd, htt] at h
      · exact absurd rfl h
  | listen =>
      simp only [step] at h
      split at h
      · simp [upd, ht] at h
      · split at h <;> exact absurd rfl h
  | send => simp only [step] at h; split at h <;> (try split at h) <;> exact absurd rfl h
  | alloc => exact absurd rfl h
  | map => simp only [step] at h; split at h <;> exact absurd rfl h
  | lend => simp only [step] at h; split at h <;> (try split at h) <;> exact absurd rfl h
  | mapLent => simp only [step] at h; split at h <;> exact absurd rfl h
  | store => simp only [step] at h; split at h <;> exact absurd rfl h
  | load => simp only [step] at h; split at h <;> exact absurd rfl h
  | setKeys => exact absurd rfl h

/-- Every reply is backed by a distinct call that the replier heard from the receiver. -/
theorem Good.answered_le_heard (hg : Good c s) (d e : D) : s.answered d e ≤ s.heard d e := by
  have := hg.replies d e; omega

/-- Confinement of memory authority: a domain reaches a frame owned by another domain only if that
domain can send to it (and lent the frame). -/
theorem Good.frame_access_confined (hg : Good c s) {d e : D} {f : Nat} (hde : d ≠ e)
    (hown : s.owner f = some e) (h : canAccess s d f = true) : HoldsRing s e d := by
  rcases hg.access h with h' | ⟨sl, w, hcap⟩
  · rw [hown] at h'; cases h'; exact absurd rfl hde
  · obtain ⟨o, ho, hr⟩ := hg.lent d sl f w hcap
    rw [hown] at ho; cases ho; exact hr

end properties

/-! ## Genesis -/

/-- A genesis state: tables and rings as declared, no frames, no mappings, each key register open
on its own key only, empty reply bookkeeping. It satisfies the invariant when it names no frames. -/
def genesis (c : Config D) (caps : D → Nat → Option (Cap D)) : State D where
  caps := caps
  ring := fun _ => []
  owner := fun _ => none
  maps := []
  mask := fun d k => k == c.key d
  mem := fun _ => 0
  fresh := 0
  pending := fun _ => []
  slot := fun _ => none
  heard := fun _ _ => 0
  answered := fun _ _ => 0

theorem genesis_good (c : Config D) (caps : D → Nat → Option (Cap D))
    (hcaps : ∀ d n f w, caps d n ≠ some ⟨.frame f, w⟩) : Good c (genesis c caps) where
  mask_own := by intro d k h; simpa [genesis] using h
  maps_ok := by intro f k h; simp [genesis] at h
  fresh_owner := by intro f _; rfl
  fresh_caps := by intro d n f w h; exact absurd h (hcaps d n f w)
  lent := by intro d n f w h; exact absurd h (hcaps d n f w)
  replies := by intro d e; simp [genesis]

/-- Ring capabilities in a reachable state are those of the start. -/
theorem Reachable.ring_caps_fixed {c : Config D} {s₀ s : State D} (hs : Reachable c s₀ s) :
    ∀ t n e w, s.caps t n = some ⟨.ring e, w⟩ ↔ s₀.caps t n = some ⟨.ring e, w⟩ := by
  induction hs with
  | init => intro t n e w; exact Iff.rfl
  | next d op _ ih => intro t n e w; rw [step_ring_caps_fixed]; exact ih t n e w

/-- Over whole runs from a genesis: rings are reached only along declared ring capabilities, memory of
another domain only along a declared ring capability from its owner, and replies never outnumber heard
calls. -/
theorem genesis_run (c : Config D) (caps : D → Nat → Option (Cap D))
    (hcaps : ∀ d n f w, caps d n ≠ some ⟨.frame f, w⟩) {s : State D}
    (hs : Reachable c (genesis c caps) s) :
    (∀ t n e w, s.caps t n = some ⟨.ring e, w⟩ ↔ caps t n = some ⟨.ring e, w⟩) ∧
    (∀ d e f, d ≠ e → s.owner f = some e → canAccess s d f = true → ∃ n w, caps e n = some ⟨.ring d, w⟩) ∧
    (∀ d e, s.answered d e ≤ s.heard d e) := by
  have hg := hs.good (genesis_good c caps hcaps)
  have hfix := hs.ring_caps_fixed
  refine ⟨hfix, ?_, hg.answered_le_heard⟩
  intro d e f hde hown hacc
  obtain ⟨n, w, h⟩ := hg.frame_access_confined hde hown hacc
  exact ⟨n, w, (hfix e n d w).mp h⟩

end Mettapedia.Machines.Kernel
