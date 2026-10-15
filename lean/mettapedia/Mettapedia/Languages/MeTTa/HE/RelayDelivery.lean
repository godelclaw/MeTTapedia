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

end Model

end Mettapedia.Languages.MeTTa.HE.RelayDelivery
