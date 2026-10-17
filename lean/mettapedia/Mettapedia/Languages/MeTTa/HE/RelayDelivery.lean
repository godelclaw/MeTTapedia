import Mathlib.Data.List.Forall2

/-!
# Delivery through a run of HE relays

A relay is a frame whose only work after its children is publishing their
results: a copy, the visible-frontier normalization (drop `Empty` when some
item is not `Empty`, then drop errors when some item succeeds), or the
publication of a call whose call and type are ground (an invocation with the
caller's environment).

Sequentially, every relay publishes its children's results into its parent.
Delivered, the relays of one run share a buffer: each relay finishes on its
own range, and does work only where the range's items need it:

* a copy does nothing;
* a normalization does nothing when no item of the range is special;
* an invocation does nothing when every item of the range is plain, an
  invocation lies above it in the run, and its own environment vanishes
  under projection onto ground roots. A plain item is a good value whose
  environment vanishes; the invocation publishes it as
  `(value, caller environment)`.

Below an invocation, a plain item may also drop its environment early.

`deliver_eq_out` states that a delivered run publishes exactly the sequential
output. The examples show that each side condition is needed.

`normalize_append_normalize`: normalizing parts and then their concatenation
is normalizing the concatenation once, since the normalization reads only
whether some item is not `Empty` and whether some item succeeds, and keeps
both. A run of normalizing relays may therefore leave the work to its
outermost one (`normalize_normalize` is the one-part case).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.RelayDelivery

/-- An item of an outcome set: a value with its environment. -/
structure Item (V E : Type) where
  value : V
  env : E
  deriving DecidableEq, Repr

/-- A relay, by what it does at its pop. -/
inductive Relay (E : Type) where
  | copy
  | normalize
  | invoke (caller : E)
  deriving DecidableEq, Repr

/-- A run: produced items, children in order, and relays over a body. -/
inductive Run (V E : Type) where
  | leaf (items : List (Item V E))
  | seq (first second : Run V E)
  | relay (r : Relay E) (body : Run V E)

/-! ## The shared buffer

Natively, a run's relays share one buffer. A relay opens a range at the
buffer's current length; its children append; at its pop it finishes its
range in place, or, when it leaves without publishing, drops the range.
Finishing and dropping touch nothing below the range's start, so the results
earlier siblings committed stay, and executing a run on the buffer leaves the
prefix followed by the delivered output. -/

/-- The run's buffer and its open ranges, innermost first. -/
structure Buffer (V E : Type) where
  items : List (Item V E)
  starts : List Nat

namespace Buffer

variable {V E : Type}

def openRange (b : Buffer V E) : Buffer V E :=
  ⟨b.items, b.items.length :: b.starts⟩

def emit (b : Buffer V E) (xs : List (Item V E)) : Buffer V E :=
  ⟨b.items ++ xs, b.starts⟩

/-- The innermost range, finished in place by `f`. -/
def finishWith (b : Buffer V E) (f : List (Item V E) → List (Item V E)) :
    Buffer V E :=
  match b.starts with
  | s :: rest => ⟨b.items.take s ++ f (b.items.drop s), rest⟩
  | [] => b

/-- The innermost range, dropped: its relay left without publishing. -/
def unwind (b : Buffer V E) : Buffer V E :=
  match b.starts with
  | s :: rest => ⟨b.items.take s, rest⟩
  | [] => b

theorem finishWith_prefix (b : Buffer V E) (s : Nat) (rest : List Nat)
    (f : List (Item V E) → List (Item V E)) (h : b.starts = s :: rest)
    (hs : s ≤ b.items.length) :
    (b.finishWith f).items.take s = b.items.take s := by
  simp only [finishWith, h]
  rw [List.take_append_of_le_length (by simp [List.length_take, hs])]
  simp [List.take_take]

theorem unwind_prefix (b : Buffer V E) (s : Nat) (rest : List Nat)
    (h : b.starts = s :: rest) :
    (b.unwind).items = b.items.take s := by
  simp [unwind, h]

/-- A relay that opens a range, receives `xs` and leaves without publishing
restores the buffer it found. -/
theorem unwind_after_open (b : Buffer V E) (xs : List (Item V E)) :
    ((b.openRange).emit xs).unwind = b := by
  cases b
  simp [openRange, emit, unwind]

end Buffer

/-- The value and environment classes, and the invocation transform. -/
structure Model (V E : Type) where
  good : V → Bool
  isEmpty : V → Bool
  isError : V → Bool
  vanishes : E → Bool
  empty : E
  transform : E → Item V E → Option (Item V E)

namespace Model

variable {V E : Type} (m : Model V E)

/-- Plain: a good value whose environment vanishes. -/
def plain (x : Item V E) : Bool := m.good x.value && m.vanishes x.env

/-- Special: an item the normalization reads. -/
def special (x : Item V E) : Bool := m.isEmpty x.value || m.isError x.value

/-- Keep the items whose value passes `keep`, when some item's value passes
`test`. -/
def filterIf (test keep : V → Bool) (xs : List (Item V E)) : List (Item V E) :=
  if xs.any (fun x => test x.value) then xs.filter (fun x => keep x.value) else xs

/-- The visible-frontier normalization: drop `Empty` when some item is not
`Empty`, then drop errors when some item succeeds. -/
def normalize (xs : List (Item V E)) : List (Item V E) :=
  filterIf (fun v => !m.isEmpty v && !m.isError v) (fun v => !m.isError v)
    (filterIf (fun v => !m.isEmpty v) (fun v => !m.isEmpty v) xs)

/-- Sequential publication by one relay. -/
def publish : Relay E → List (Item V E) → List (Item V E)
  | .copy, xs => xs
  | .normalize, xs => m.normalize xs
  | .invoke e, xs => xs.filterMap (m.transform e)

/-- The sequential output of a run. -/
def out : Run V E → List (Item V E)
  | .leaf xs => xs
  | .seq a b => out a ++ out b
  | .relay r body => m.publish r (out body)

/-- A plain item below an invocation carries no environment of its own. -/
def clear (xs : List (Item V E)) : List (Item V E) :=
  xs.map (fun x => if m.plain x then ⟨x.value, m.empty⟩ else x)

/-- A relay's finish on its range, given whether an invocation lies above. -/
def finish (above : Bool) : Relay E → List (Item V E) → List (Item V E)
  | .copy, xs => xs
  | .normalize, xs =>
      let ys := if above then m.clear xs else xs
      if ys.any m.special then m.normalize ys else ys
  | .invoke e, xs =>
      let ys := m.clear xs
      if ys.all m.plain && above && m.vanishes e then ys
      else ys.filterMap (m.transform e)

def isInvoke : Relay E → Bool
  | .invoke _ => true
  | _ => false

/-- The delivered output of a run. -/
def deliver (above : Bool) : Run V E → List (Item V E)
  | .leaf xs => xs
  | .seq a b => deliver above a ++ deliver above b
  | .relay r body => m.finish above r (deliver (above || isInvoke r) body)

/-- Executing a run on the buffer: leaves append, a relay opens a range,
runs its body and finishes the range in place. -/
def exec (above : Bool) : Run V E → Buffer V E → Buffer V E
  | .leaf xs, b => b.emit xs
  | .seq a c, b => exec above c (exec above a b)
  | .relay r body, b =>
      ((exec (above || isInvoke r) body) b.openRange).finishWith (m.finish above r)

/-- The laws the native classification and transform satisfy. -/
structure Laws : Prop where
  good_not_empty : ∀ v, m.good v = true → m.isEmpty v = false
  good_not_error : ∀ v, m.good v = true → m.isError v = false
  empty_vanishes : m.vanishes m.empty = true
  transform_plain : ∀ e x, m.plain x = true →
    m.transform e x = some ⟨x.value, e⟩

/-- Delivered and sequential items agree, or are plain with one value. -/
def Rel (x y : Item V E) : Prop :=
  x = y ∨ (m.plain x = true ∧ m.plain y = true ∧ x.value = y.value)

variable {m}

theorem Rel.value_eq {x y : Item V E} (h : m.Rel x y) : x.value = y.value := by
  rcases h with rfl | ⟨_, _, h⟩
  · rfl
  · exact h

theorem Rel.special_eq {x y : Item V E} (h : m.Rel x y) :
    m.special x = m.special y := by
  simp [special, h.value_eq]

theorem Rel.plain_eq {x y : Item V E} (h : m.Rel x y) : m.plain x = m.plain y := by
  rcases h with rfl | ⟨hx, hy, _⟩
  · rfl
  · rw [hx, hy]

theorem forall₂_rel_refl (xs : List (Item V E)) : List.Forall₂ m.Rel xs xs :=
  List.forall₂_same.mpr (fun _ _ => Or.inl rfl)

/-- A Boolean test of the value agrees across related lists. -/
theorem any_value_eq (p : V → Bool) :
    ∀ {xs ys : List (Item V E)}, List.Forall₂ m.Rel xs ys →
      xs.any (fun x => p x.value) = ys.any (fun x => p x.value)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h rest => by
      simp only [List.any_cons, h.value_eq, any_value_eq p rest]

/-- Filtering by the value keeps lists related. -/
theorem filter_value_rel (p : V → Bool) :
    ∀ {xs ys : List (Item V E)}, List.Forall₂ m.Rel xs ys →
      List.Forall₂ m.Rel (xs.filter (fun x => p x.value))
        (ys.filter (fun x => p x.value))
  | [], [], .nil => .nil
  | x :: _, y :: _, .cons h rest => by
      have hv := h.value_eq
      by_cases hp : p y.value = true
      · simp only [List.filter_cons, hv, hp, ↓reduceIte]
        exact .cons h (filter_value_rel p rest)
      · simp only [List.filter_cons, hv, hp, Bool.false_eq_true, ↓reduceIte]
        exact filter_value_rel p rest

theorem filterIf_rel (test keep : V → Bool) {xs ys : List (Item V E)}
    (h : List.Forall₂ m.Rel xs ys) :
    List.Forall₂ m.Rel (filterIf test keep xs) (filterIf test keep ys) := by
  unfold filterIf
  rw [any_value_eq test h]
  split
  · exact filter_value_rel keep h
  · exact h

theorem normalize_rel {xs ys : List (Item V E)} (h : List.Forall₂ m.Rel xs ys) :
    List.Forall₂ m.Rel (m.normalize xs) (m.normalize ys) :=
  filterIf_rel _ _ (filterIf_rel _ _ h)

theorem any_special_eq {xs ys : List (Item V E)} (h : List.Forall₂ m.Rel xs ys) :
    xs.any m.special = ys.any m.special :=
  any_value_eq (fun v => m.isEmpty v || m.isError v) h

/-- With no special item, normalization keeps every item. -/
theorem normalize_of_no_special {xs : List (Item V E)}
    (h : xs.any m.special = false) : m.normalize xs = xs := by
  have hs : ∀ x ∈ xs, m.special x = false := by
    intro x hx
    simpa using List.any_eq_false.mp h x hx
  have hE : ∀ x ∈ xs, m.isEmpty x.value = false := by
    intro x hx
    have := hs x hx
    simp only [special, Bool.or_eq_false_iff] at this
    exact this.1
  have hR : ∀ x ∈ xs, m.isError x.value = false := by
    intro x hx
    have := hs x hx
    simp only [special, Bool.or_eq_false_iff] at this
    exact this.2
  have f₁ : filterIf (fun v => !m.isEmpty v) (fun v => !m.isEmpty v) xs = xs := by
    unfold filterIf
    rw [List.filter_eq_self.mpr (fun x hx => by simp [hE x hx]), ite_self]
  have f₂ : filterIf (fun v => !m.isEmpty v && !m.isError v) (fun v => !m.isError v) xs =
      xs := by
    unfold filterIf
    rw [List.filter_eq_self.mpr (fun x hx => by simp [hR x hx]), ite_self]
  unfold normalize
  rw [f₁, f₂]

theorem clear_rel (laws : m.Laws) :
    ∀ {xs ys : List (Item V E)}, List.Forall₂ m.Rel xs ys →
      List.Forall₂ m.Rel (m.clear xs) ys
  | [], [], .nil => .nil
  | x :: _, y :: _, .cons h rest => by
      refine .cons ?_ (clear_rel laws rest)
      by_cases hx : m.plain x = true
      · simp only [hx, ↓reduceIte]
        have hgood : m.good x.value = true := by
          simp only [plain, Bool.and_eq_true] at hx
          exact hx.1
        right
        refine ⟨?_, ?_, h.value_eq⟩
        · simp [plain, hgood, laws.empty_vanishes]
        · rw [← h.plain_eq]
          exact hx
      · simp only [hx, Bool.false_eq_true, ↓reduceIte]
        exact h

theorem transform_rel (laws : m.Laws) (e : E) {x y : Item V E} (h : m.Rel x y) :
    m.transform e x = m.transform e y := by
  rcases h with rfl | ⟨hx, hy, hv⟩
  · rfl
  · rw [laws.transform_plain e x hx, laws.transform_plain e y hy, hv]

theorem filterMap_eq (laws : m.Laws) (e : E) :
    ∀ {xs ys : List (Item V E)}, List.Forall₂ m.Rel xs ys →
      xs.filterMap (m.transform e) = ys.filterMap (m.transform e)
  | [], [], .nil => rfl
  | _ :: _, _ :: _, .cons h rest => by
      simp only [List.filterMap_cons, transform_rel laws e h, filterMap_eq laws e rest]

theorem all_plain_of_rel :
    ∀ {xs ys : List (Item V E)}, List.Forall₂ m.Rel xs ys →
      xs.all m.plain = true → ys.all m.plain = true
  | [], [], .nil, _ => rfl
  | _ :: _, _ :: _, .cons h rest, hall => by
      simp only [List.all_cons, Bool.and_eq_true] at hall ⊢
      exact ⟨h.plain_eq ▸ hall.1, all_plain_of_rel rest hall.2⟩

/-- On plain items, an invocation publishes each value with the caller's
environment. -/
theorem settle_rel (laws : m.Laws) (e : E) (he : m.vanishes e = true) :
    ∀ {xs ys : List (Item V E)}, List.Forall₂ m.Rel xs ys →
      xs.all m.plain = true →
        List.Forall₂ m.Rel xs (ys.filterMap (m.transform e))
  | [], [], .nil, _ => .nil
  | x :: _, y :: _, .cons h rest, hall => by
      simp only [List.all_cons, Bool.and_eq_true] at hall
      have hy : m.plain y = true := h.plain_eq ▸ hall.1
      simp only [List.filterMap_cons, laws.transform_plain e y hy]
      refine .cons (Or.inr ⟨hall.1, ?_, h.value_eq⟩) (settle_rel laws e he rest hall.2)
      have hgood : m.good y.value = true := by
        simp only [plain, Bool.and_eq_true] at hy
        exact hy.1
      simp [plain, hgood, he]

/-- The delivered output is related to the sequential one, and equal to it
where no invocation lies above. -/
theorem deliver_rel (laws : m.Laws) :
    ∀ (t : Run V E) (above : Bool),
      List.Forall₂ m.Rel (m.deliver above t) (m.out t) ∧
        (above = false → m.deliver above t = m.out t)
  | .leaf xs, _ => ⟨forall₂_rel_refl xs, fun _ => rfl⟩
  | .seq a b, above => by
      obtain ⟨ra, ea⟩ := deliver_rel laws a above
      obtain ⟨rb, eb⟩ := deliver_rel laws b above
      refine ⟨List.rel_append ra rb, fun h => ?_⟩
      simp only [deliver, out, ea h, eb h]
  | .relay .copy body, above => by
      obtain ⟨r, e⟩ := deliver_rel laws body above
      simp only [deliver, isInvoke, Bool.or_false, finish, out, publish]
      exact ⟨r, e⟩
  | .relay .normalize body, above => by
      obtain ⟨r, e⟩ := deliver_rel laws body above
      simp only [deliver, isInvoke, Bool.or_false, finish, out, publish]
      have rc : List.Forall₂ m.Rel
          (if above then m.clear (m.deliver above body) else m.deliver above body)
          (m.out body) := by
        split
        · exact clear_rel laws r
        · exact r
      refine ⟨?_, fun h => ?_⟩
      · rw [any_special_eq rc]
        split
        · exact normalize_rel rc
        · next hs =>
            rw [normalize_of_no_special (Bool.eq_false_iff.mpr hs)]
            exact rc
      · subst h
        simp only [Bool.false_eq_true, ↓reduceIte, e rfl]
        split
        · rfl
        · next hs => exact (normalize_of_no_special (Bool.eq_false_iff.mpr hs)).symm
  | .relay (.invoke c) body, above => by
      obtain ⟨r, _⟩ := deliver_rel laws body true
      simp only [deliver, isInvoke, Bool.or_true, finish, out, publish]
      have rc := clear_rel laws r
      refine ⟨?_, fun h => ?_⟩
      · split
        · next hfast =>
            simp only [Bool.and_eq_true] at hfast
            exact settle_rel laws c hfast.2 rc hfast.1.1
        · rw [filterMap_eq laws c rc]
          exact forall₂_rel_refl _
      · subst h
        simp only [Bool.and_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        exact filterMap_eq laws c rc

/-- A delivered run publishes exactly the sequential output. -/
theorem deliver_eq_out (laws : m.Laws) (t : Run V E) :
    m.deliver false t = m.out t :=
  (deliver_rel laws t false).2 rfl

theorem exec_spec (above : Bool) :
    ∀ (t : Run V E) (b : Buffer V E),
      exec m above t b = ⟨b.items ++ m.deliver above t, b.starts⟩
  | .leaf xs, b => rfl
  | .seq a c, b => by
      simp only [exec, exec_spec above a b, exec_spec above c, deliver, List.append_assoc]
  | .relay r body, b => by
      simp only [exec, Buffer.openRange, exec_spec (above || isInvoke r) body,
        Buffer.finishWith, deliver]
      simp

/-- A delivered run on the native buffer publishes exactly the sequential
output after what the buffer held. -/
theorem exec_eq_out (laws : m.Laws) (t : Run V E) (b : Buffer V E) :
    exec m false t b = ⟨b.items ++ m.out t, b.starts⟩ := by
  rw [exec_spec, deliver_eq_out laws]

/-! ## Normalization composes

The visible-frontier normalization reads two flags of its list: whether some
item is not `Empty`, and whether some item succeeds. It keeps every success,
so it keeps both flags; and a longer list only raises them. Hence normalizing
parts and then their concatenation equals normalizing the concatenation once:
a run of normalizing relays may leave the work to its outermost one. -/

/-- Some item is not `Empty`. -/
def someValue (xs : List (Item V E)) : Bool := xs.any (fun x => !m.isEmpty x.value)

/-- Some item succeeds: neither `Empty` nor an error. -/
def someSuccess (xs : List (Item V E)) : Bool :=
  xs.any (fun x => !m.isEmpty x.value && !m.isError x.value)

/-- The items a frontier with these flags keeps. -/
def keepFor (value success : Bool) (x : Item V E) : Bool :=
  (!value || !m.isEmpty x.value) && (!success || !m.isError x.value)

theorem someSuccess_le_someValue (xs : List (Item V E)) :
    m.someSuccess xs = true → m.someValue xs = true := by
  simp only [someSuccess, someValue, List.any_eq_true, Bool.and_eq_true]
  rintro ⟨x, hx, hne, -⟩
  exact ⟨x, hx, hne⟩

theorem normalize_eq_filter (xs : List (Item V E)) :
    m.normalize xs = xs.filter (m.keepFor (m.someValue xs) (m.someSuccess xs)) := by
  unfold normalize filterIf
  by_cases hv : xs.any (fun x => !m.isEmpty x.value) = true
  · have hs : (xs.filter (fun x => !m.isEmpty x.value)).any
        (fun x => !m.isEmpty x.value && !m.isError x.value) = m.someSuccess xs := by
      unfold someSuccess
      induction xs with
      | nil => rfl
      | cons y ys ih =>
        by_cases hy : m.isEmpty y.value = true
        · simp [hy]
        · simp [hy]
    rw [if_pos hv, hs]
    have hv' : m.someValue xs = true := hv
    by_cases hsucc : m.someSuccess xs = true
    · rw [if_pos hsucc, hv', hsucc, List.filter_filter]
      congr 1
      funext x
      simp [keepFor, Bool.and_comm]
    · have hf : m.someSuccess xs = false := by simpa using hsucc
      rw [if_neg hsucc, hv', hf]
      congr 1
      funext x
      simp [keepFor]
  · have hf : m.someValue xs = false := by simpa [someValue] using hv
    have hsf : m.someSuccess xs = false := by
      cases h : m.someSuccess xs
      · rfl
      · exact absurd (m.someSuccess_le_someValue xs h) (by simp [hf])
    have hsucc : ¬ xs.any (fun x => !m.isEmpty x.value && !m.isError x.value) = true := by
      simpa [someSuccess] using hsf
    rw [if_neg hv, if_neg hsucc, hf, hsf]
    exact (List.filter_eq_self.mpr (by intro x _; simp [Model.keepFor])).symm

theorem someSuccess_normalize (xs : List (Item V E)) :
    m.someSuccess (m.normalize xs) = m.someSuccess xs := by
  rw [m.normalize_eq_filter]
  unfold someSuccess
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_filter, Bool.and_eq_true]
  constructor
  · rintro ⟨x, ⟨hx, -⟩, h⟩
    exact ⟨x, hx, h⟩
  · rintro ⟨x, hx, hne, herr⟩
    refine ⟨x, ⟨hx, ?_⟩, hne, herr⟩
    simp [keepFor, hne, herr]

theorem someValue_normalize (xs : List (Item V E)) :
    m.someValue (m.normalize xs) = m.someValue xs := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    rw [m.normalize_eq_filter] at h
    simp only [someValue, List.any_eq_true, List.mem_filter] at h ⊢
    obtain ⟨x, ⟨hx, -⟩, hne⟩ := h
    exact ⟨x, hx, hne⟩
  · intro h
    by_cases hs : m.someSuccess xs = true
    · have := m.someSuccess_normalize xs
      exact m.someSuccess_le_someValue _ (this.trans hs)
    · have hsf : m.someSuccess xs = false := by simpa using hs
      rw [m.normalize_eq_filter]
      simp only [someValue, List.any_eq_true, List.mem_filter] at h ⊢
      obtain ⟨x, hx, hne⟩ := h
      exact ⟨x, ⟨hx, by simp [keepFor, hsf, hne]⟩, hne⟩

theorem keepFor_mono {v v' s s' : Bool} (hv : v = true → v' = true)
    (hs : s = true → s' = true) (x : Item V E) :
    m.keepFor v' s' x = true → m.keepFor v s x = true := by
  cases v <;> cases v' <;> cases s <;> cases s' <;> simp_all [keepFor]

/-- Normalizing the parts, then their concatenation, is normalizing once. -/
theorem normalize_append_normalize (xs ys : List (Item V E)) :
    m.normalize (m.normalize xs ++ m.normalize ys) = m.normalize (xs ++ ys) := by
  have hv : m.someValue (m.normalize xs ++ m.normalize ys) = m.someValue (xs ++ ys) := by
    simp only [someValue, List.any_append] at *
    rw [show (m.normalize xs).any (fun x => !m.isEmpty x.value) = m.someValue xs from
          m.someValue_normalize xs,
        show (m.normalize ys).any (fun x => !m.isEmpty x.value) = m.someValue ys from
          m.someValue_normalize ys]
    rfl
  have hs : m.someSuccess (m.normalize xs ++ m.normalize ys) = m.someSuccess (xs ++ ys) := by
    simp only [someSuccess, List.any_append] at *
    rw [show (m.normalize xs).any (fun x => !m.isEmpty x.value && !m.isError x.value) =
          m.someSuccess xs from m.someSuccess_normalize xs,
        show (m.normalize ys).any (fun x => !m.isEmpty x.value && !m.isError x.value) =
          m.someSuccess ys from m.someSuccess_normalize ys]
    rfl
  rw [m.normalize_eq_filter (m.normalize xs ++ m.normalize ys), hv, hs,
      m.normalize_eq_filter (xs ++ ys), m.normalize_eq_filter xs, m.normalize_eq_filter ys,
      List.filter_append, List.filter_append, List.filter_filter, List.filter_filter]
  have hxv : m.someValue xs = true → m.someValue (xs ++ ys) = true := by
    simp only [someValue, List.any_append, Bool.or_eq_true]; exact Or.inl
  have hxs : m.someSuccess xs = true → m.someSuccess (xs ++ ys) = true := by
    simp only [someSuccess, List.any_append, Bool.or_eq_true]; exact Or.inl
  have hyv : m.someValue ys = true → m.someValue (xs ++ ys) = true := by
    simp only [someValue, List.any_append, Bool.or_eq_true]; exact Or.inr
  have hys : m.someSuccess ys = true → m.someSuccess (xs ++ ys) = true := by
    simp only [someSuccess, List.any_append, Bool.or_eq_true]; exact Or.inr
  congr 1
  · congr 1; funext x
    cases h : m.keepFor (m.someValue (xs ++ ys)) (m.someSuccess (xs ++ ys)) x
    · simp
    · simp [m.keepFor_mono hxv hxs x h]
  · congr 1; funext x
    cases h : m.keepFor (m.someValue (xs ++ ys)) (m.someSuccess (xs ++ ys)) x
    · simp
    · simp [m.keepFor_mono hyv hys x h]

/-- Normalization is idempotent. -/
theorem normalize_normalize (xs : List (Item V E)) :
    m.normalize (m.normalize xs) = m.normalize xs := by
  have h := m.normalize_append_normalize xs []
  simpa [normalize, filterIf] using h


/-! ## A completed producer may stream its successes

When nothing the producer does can be observed before it completes, its
consumer may take each success as it arrives: the errors wait for the end and
are published only when nothing succeeded. The answers, with `Empty` dropped
as delivery drops it, are the normalized collection's, in the same order. -/

/-- The streamed publication: the successes in arrival order, then the errors
when nothing succeeded. -/
def streamed (xs : List (Item V E)) : List (Item V E) :=
  xs.filter (fun x => !m.isEmpty x.value && !m.isError x.value) ++
    (if m.someSuccess xs then [] else
      xs.filter (fun x => !m.isEmpty x.value && m.isError x.value))

theorem streamed_eq_normalize (xs : List (Item V E)) :
    m.streamed xs = (m.normalize xs).filter (fun x => !m.isEmpty x.value) := by
  rw [m.normalize_eq_filter, List.filter_filter]
  unfold streamed
  cases hs : m.someSuccess xs
  · have hnone : ∀ x ∈ xs, (!m.isEmpty x.value && !m.isError x.value) = false := by
      intro x hx
      cases h : (!m.isEmpty x.value && !m.isError x.value)
      · rfl
      · have hany : m.someSuccess xs = true := List.any_eq_true.mpr ⟨x, hx, h⟩
        rw [hs] at hany; exact absurd hany Bool.false_ne_true
    rw [if_neg Bool.false_ne_true,
      List.filter_congr (q := fun _ => false) hnone, List.filter_false, List.nil_append]
    apply List.filter_congr
    intro x hx
    have h := hnone x hx
    cases he : m.isEmpty x.value <;> cases hr : m.isError x.value <;>
      simp_all [keepFor]
  · have hv := m.someSuccess_le_someValue xs hs
    rw [if_pos rfl, List.append_nil, hv]
    apply List.filter_congr
    intro x _
    cases he : m.isEmpty x.value <;> cases hr : m.isError x.value <;>
      simp [keepFor, he, hr]

/-! ## Examples -/

/-- Values: plain atoms, `Empty`, an error, and an open value. -/
inductive Val where
  | atom (n : Nat)
  | emptyVal
  | errorVal
  | openVal
  deriving DecidableEq, Repr

/-- An environment: its bindings, and whether it carries a constraint. -/
structure Env where
  names : List Nat
  constrained : Bool
  deriving DecidableEq, Repr

/-- The native shape: a plain item is published with the caller's
environment; any other item keeps its constraint alongside it. -/
def native : Model Val Env where
  good := fun | .atom _ => true | _ => false
  isEmpty := fun | .emptyVal => true | _ => false
  isError := fun | .errorVal => true | _ => false
  vanishes := fun e => !e.constrained
  empty := ⟨[], false⟩
  transform := fun e x =>
    if (match x.value with | .atom _ => true | _ => false) && !x.env.constrained
      then some ⟨x.value, e⟩
      else some ⟨x.value, ⟨e.names ++ x.env.names, e.constrained || x.env.constrained⟩⟩

theorem native_laws : native.Laws where
  good_not_empty := by intro v hv; cases v <;> simp_all [native]
  good_not_error := by intro v hv; cases v <;> simp_all [native]
  empty_vanishes := rfl
  transform_plain := by
    intro e x hx
    rcases x with ⟨v, env⟩
    cases v <;> simp_all [native, Model.plain]

def callerOuter : Env := ⟨[1], false⟩
def callerInner : Env := ⟨[2], false⟩
def producerEnv : Env := ⟨[7, 8], false⟩

/-- Two levels of a recursive call: each level's dispatch, normalizing
caller and copying result over the answers found below. -/
def twoLevels (answers : List (Item Val Env)) : Run Val Env :=
  .relay (.invoke callerOuter) <| .relay .normalize <| .relay .copy <|
    .relay (.invoke callerInner) <| .relay .normalize <| .leaf answers

def plainAnswers : List (Item Val Env) :=
  [⟨.atom 3, producerEnv⟩, ⟨.atom 4, producerEnv⟩]

/-- Positive: plain answers reach the outer caller with its environment, and
delivery skips the inner publication. -/
example : native.out (twoLevels plainAnswers) =
    [⟨.atom 3, callerOuter⟩, ⟨.atom 4, callerOuter⟩] := by decide

example : native.deliver false (twoLevels plainAnswers) =
    native.out (twoLevels plainAnswers) := deliver_eq_out native_laws _

/-- The inner invocation is skipped: its finish keeps the range as it is. -/
example : native.finish true (.invoke callerInner)
    (native.clear plainAnswers) = native.clear plainAnswers := by decide

/-- Positive: with an `Empty` beside an answer, the normalization does its work
in delivery too. -/
example : native.deliver false
    (.relay .normalize (.leaf [⟨.emptyVal, producerEnv⟩, ⟨.atom 3, producerEnv⟩])) =
    [⟨.atom 3, producerEnv⟩] := by decide

/-- A finish that always skips an inner invocation. -/
def skipInner (above : Bool) (r : Relay Env) (xs : List (Item Val Env)) :
    List (Item Val Env) :=
  match r with
  | .invoke _ => if above then xs else native.publish r xs
  | _ => native.finish above r xs

def deliverSkipping (above : Bool) : Run Val Env → List (Item Val Env)
  | .leaf xs => xs
  | .seq a b => deliverSkipping above a ++ deliverSkipping above b
  | .relay r body => skipInner above r (deliverSkipping (above || Model.isInvoke r) body)

def constrainedInner : Env := ⟨[2], true⟩

/-- Negative: an inner caller environment with a constraint does not vanish;
skipping its publication loses the constraint. -/
example : deliverSkipping false
    (.relay (.invoke callerOuter) <| .relay (.invoke constrainedInner) <|
      .leaf plainAnswers) ≠
    native.out (.relay (.invoke callerOuter) <| .relay (.invoke constrainedInner) <|
      .leaf plainAnswers) := by decide

/-- Negative: an open answer is not plain; an invocation must publish it. -/
example : deliverSkipping false
    (.relay (.invoke callerOuter) <| .relay (.invoke callerInner) <|
      .leaf [⟨.openVal, ⟨[5], true⟩⟩]) ≠
    native.out (.relay (.invoke callerOuter) <| .relay (.invoke callerInner) <|
      .leaf [⟨.openVal, ⟨[5], true⟩⟩]) := by decide

/-- Negative: skipping a normalization with an `Empty` in its range keeps it. -/
example : native.deliver false (.leaf [⟨.emptyVal, producerEnv⟩, ⟨.atom 3, producerEnv⟩]) ≠
    native.out (.relay .normalize
      (.leaf [⟨.emptyVal, producerEnv⟩, ⟨.atom 3, producerEnv⟩])) := by decide

/-- Negative: the outermost invocation cannot be skipped; its caller's
environment is what the answers carry. -/
example : native.clear plainAnswers ≠
    native.out (.relay (.invoke callerOuter) (.leaf plainAnswers)) := by decide


/-- Positive: an `Empty` and an error below, a success beside them; normalizing
each part and then the whole is normalizing once. -/
example :
    let xs : List (Item Val Env) := [⟨.emptyVal, producerEnv⟩, ⟨.errorVal, producerEnv⟩]
    let ys : List (Item Val Env) := [⟨.atom 3, producerEnv⟩, ⟨.emptyVal, producerEnv⟩]
    native.normalize (native.normalize xs ++ native.normalize ys) =
      native.normalize (xs ++ ys) ∧
    native.normalize (xs ++ ys) = [⟨.atom 3, producerEnv⟩] := by decide

/-- Negative: the parts normalized but not the whole keep an `Empty` and an
error that the whole drops; the outermost normalization is still needed. -/
example :
    let xs : List (Item Val Env) := [⟨.emptyVal, producerEnv⟩, ⟨.errorVal, producerEnv⟩]
    let ys : List (Item Val Env) := [⟨.atom 3, producerEnv⟩]
    native.normalize xs ++ native.normalize ys ≠ native.normalize (xs ++ ys) := by decide

/-- Negative: an error alone survives normalization; a success elsewhere in
the run removes it only when the run is normalized as a whole. -/
example :
    native.normalize [⟨.errorVal, producerEnv⟩] = [⟨Val.errorVal, producerEnv⟩] := by decide

/-- Positive: an error before a success; streaming holds the error, and the
success alone is published, as normalizing the collection publishes it. -/
example :
    let xs : List (Item Val Env) :=
      [⟨.errorVal, producerEnv⟩, ⟨.emptyVal, producerEnv⟩, ⟨.atom 3, producerEnv⟩]
    native.streamed xs = [⟨.atom 3, producerEnv⟩] ∧
    native.streamed xs = (native.normalize xs).filter (fun x => !native.isEmpty x.value) := by
  decide

/-- Positive: only errors; they are published at the end. -/
example :
    native.streamed [⟨.errorVal, producerEnv⟩, ⟨.emptyVal, producerEnv⟩] =
      [⟨.errorVal, producerEnv⟩] := by decide

/-- Negative: handing every item on as it arrives publishes the error that a
later success removes. -/
example :
    let xs : List (Item Val Env) := [⟨.errorVal, producerEnv⟩, ⟨.atom 3, producerEnv⟩]
    xs.filter (fun x => !native.isEmpty x.value) ≠
      (native.normalize xs).filter (fun x => !native.isEmpty x.value) := by decide

end Model

end Mettapedia.Languages.MeTTa.HE.RelayDelivery
