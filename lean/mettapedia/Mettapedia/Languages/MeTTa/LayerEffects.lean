import Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra

/-!
# The effects of the lower layers as one monad

A speculative computation over a space runs from a world `W` (the space it
reads) and returns weighted answers, each with the world its branch left and
the cost attributed to that successful branch:

  `Spec K C W X = W → Ans K (X × W × C)`.

`K` annotates answers (layer 3, and probability or evidence as a choice of
`K`), `C` is a monoid of costs, and each branch carries its own world, so
writes are speculative until a commit decides them (layer 5).  This is the
state and writer transformers over the weighted answer monad; its laws are
`pure_bind`, `bind_pure` and `bind_assoc`.

This is an answer readout, not a complete operational account. Equal outcomes
are aggregated, order is forgotten, and a branch that returns no answer loses
its cost annotation (`bind_fail`). No observer of this readout can recover all
charges preceding failure (`no_failed_cost_recovery`). Work actually performed
on failed or shared production belongs in the existing run-account/history
interfaces, separately from per-answer attribution. The commutations below do
not authorize duplicating paid work or externally visible effects.

## Operations

* `choose` and `fail`: nondeterministic choice and no answer;
* `weight k`: scale every answer by `k` (probabilistic choice is
  `weight p m + weight (1 - p) m'`);
* `tick c`: spend `c`;
* `get` and `put`: read and write the branch's world;
* `absentAt key`: a read that succeeds when `key` has no annotation, a negative
  read of the world.

Each is an algebraic operation in the sense of Plotkin and Power: bind
distributes over it (`choose_bind`, `fail_bind`, `weight_bind`).

## The commutation table

Two effects combine as a tensor (Hyland, Plotkin and Power, *Combining
effects: sum and tensor*) when every operation of one commutes with every
operation of the other.  Here:

* choice commutes with weighting, cost, reads and writes
  (`weight_choose`, `choose_tick`, `choose_get`, `choose_put`), and weighting
  commutes with cost and writes (`weight_tick`, `weight_put`), because worlds and
  costs are per branch;
* two costs commute when the cost monoid is commutative (`tick_tick`), and cost
  commutes with reads and writes (`tick_get`, `tick_put`);
* a write does not commute with a read (`Controls.put_get_not_comm`), and a
  write into a key does not commute with a negative read of it
  (`Controls.put_absent_not_comm`): the world is the one non-commutative
  effect of the speculative layer, and absence reads are reads.

So the speculative layer is the tensor of choice, weights and costs, beside
local state.  What a tensor cannot provide is sharing a world between branches:
that is the commit, where the coordination results of
`Mettapedia.GSLT.Contracts.Coordination` apply.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.LayerEffects

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra

universe u v w

variable {K : Type u} [CommSemiring K] {C : Type v} [CommMonoid C] {W : Type w}

/-- A speculative computation. -/
abbrev Spec (K : Type u) [CommSemiring K] (C : Type v) (W : Type w) (X : Type*) :=
  W → Ans K (X × W × C)

namespace Spec

variable {X Y Z : Type*}

/-- Return a value without effect. -/
noncomputable def pure (x : X) : Spec K C W X := fun world => Ans.pure (x, world, 1)

/-- Charge the cost of a branch to the cost of what follows. -/
noncomputable def charge (cost : C) (answers : Ans K (Y × W × C)) : Ans K (Y × W × C) :=
  Ans.map (fun result => (result.1, result.2.1, cost * result.2.2)) answers

/-- Run one computation, then another from each branch's world. -/
noncomputable def bind (m : Spec K C W X) (f : X → Spec K C W Y) : Spec K C W Y :=
  fun world => Ans.bind (m world) fun result => charge result.2.2 (f result.1 result.2.1)

theorem map_map {A B D : Type*} (g : A → B) (h : B → D) (answers : Ans K A) :
    Ans.map h (Ans.map g answers) = Ans.map (h ∘ g) answers := by
  rw [Ans.map_eq_mapDomain, Ans.map_eq_mapDomain, Ans.map_eq_mapDomain, Finsupp.mapDomain_comp]

theorem map_bind {A B D : Type*} (h : B → D) (answers : Ans K A) (f : A → Ans K B) :
    Ans.map h (Ans.bind answers f) = Ans.bind answers fun a => Ans.map h (f a) := by
  rw [Ans.map, Ans.bind_assoc]
  rfl

theorem bind_map {A B D : Type*} (g : A → B) (answers : Ans K A) (f : B → Ans K D) :
    Ans.bind (Ans.map g answers) f = Ans.bind answers (f ∘ g) := by
  rw [Ans.map, Ans.bind_assoc]
  congr 1
  funext a
  exact Ans.pure_bind _ _

theorem map_id' {A : Type*} (answers : Ans K A) : Ans.map (fun a => a) answers = answers := by
  rw [Ans.map_eq_mapDomain]
  exact Finsupp.mapDomain_id

theorem map_pure {A B : Type*} (h : A → B) (a : A) :
    Ans.map h (Ans.pure a : Ans K A) = Ans.pure (h a) :=
  Ans.pure_bind _ _

theorem charge_one (answers : Ans K (Y × W × C)) : charge 1 answers = answers := by
  rw [charge]
  simp only [one_mul]
  exact map_id' answers

theorem charge_charge (first second : C) (answers : Ans K (Y × W × C)) :
    charge first (charge second answers) = charge (first * second) answers := by
  rw [charge, charge, charge, map_map]
  congr 1
  funext result
  simp [mul_assoc]

theorem charge_bind (cost : C) (m : Ans K (X × W × C)) (f : X × W × C → Ans K (Y × W × C)) :
    charge cost (Ans.bind m f) = Ans.bind m fun result => charge cost (f result) :=
  map_bind _ _ _

@[simp] theorem pure_bind (x : X) (f : X → Spec K C W Y) : bind (pure x) f = f x := by
  funext world
  rw [bind, pure, Ans.pure_bind]
  exact charge_one _

@[simp] theorem bind_pure (m : Spec K C W X) : bind m pure = m := by
  funext world
  rw [bind]
  conv_rhs => rw [← Ans.bind_pure (m world)]
  congr 1
  funext result
  rw [pure, charge, map_pure, mul_one]

theorem bind_assoc (m : Spec K C W X) (f : X → Spec K C W Y) (g : Y → Spec K C W Z) :
    bind (bind m f) g = bind m fun x => bind (f x) g := by
  funext world
  simp only [bind]
  rw [Ans.bind_assoc]
  congr 1
  funext result
  rw [charge, bind_map, charge_bind]
  congr 1
  funext inner
  simp only [Function.comp, charge_charge]

/-! ## Operations -/

/-- Nondeterministic choice. -/
noncomputable def choose (first second : Spec K C W X) : Spec K C W X := fun world => first world + second world

/-- No answer. -/
def fail : Spec K C W X := fun _ => 0

/-- Scale every answer. -/
noncomputable def weight (k : K) (m : Spec K C W X) : Spec K C W X := fun world => k • m world

/-- Attribute a cost to the branch if its continuation returns an answer. -/
noncomputable def tick (cost : C) : Spec K C W Unit := fun world => Ans.pure ((), world, cost)

/-- Read the branch's world. -/
noncomputable def get : Spec K C W W := fun world => Ans.pure (world, world, 1)

/-- Write the branch's world. -/
noncomputable def put (next : W) : Spec K C W Unit := fun _ => Ans.pure ((), next, 1)

/-- Then: discard the first value. -/
noncomputable def andThen (first : Spec K C W Unit) (second : Spec K C W X) : Spec K C W X :=
  bind first fun _ => second

/-! ### Evaluation -/

theorem bind_returning {x : X} {next : W} {cost : C} (m : Spec K C W X)
    (returns : ∀ world, m world = Ans.pure (x, next, cost)) (f : X → Spec K C W Y) (world : W) :
    bind m f world = charge cost (f x next) := by
  rw [bind, returns, Ans.pure_bind]

theorem andThen_put (next : W) (m : Spec K C W X) (world : W) :
    andThen (put next) m world = m next := by
  rw [andThen, bind_returning (put next) (fun _ => rfl), charge_one]

theorem bind_get (f : W → Spec K C W X) (world : W) : bind get f world = f world world := by
  rw [bind, get, Ans.pure_bind, charge_one]

theorem pure_apply (x : X) (world : W) :
    (pure x : Spec K C W X) world = Ans.pure (x, world, 1) := rfl

theorem get_apply (world : W) : (get : Spec K C W W) world = Ans.pure (world, world, 1) := rfl

/-! ### Algebraicity -/

theorem choose_bind (first second : Spec K C W X) (f : X → Spec K C W Y) :
    bind (choose first second) f = choose (bind first f) (bind second f) := by
  funext world
  exact Ans.add_bind _ _ _

theorem fail_bind (f : X → Spec K C W Y) : bind (fail : Spec K C W X) f = fail := by
  funext world
  exact Ans.zero_bind _

@[simp] theorem charge_zero (cost : C) :
    charge cost (0 : Ans K (Y × W × C)) = 0 := by
  rw [charge, Ans.map_eq_mapDomain, Finsupp.mapDomain_zero]

/-- Failure erases the entire successful-answer readout, including earlier
branch-local cost and world annotations. -/
@[simp] theorem bind_fail (m : Spec K C W X) :
    bind m (fun _ => (fail : Spec K C W Y)) = fail := by
  funext world
  simp only [bind, fail, charge_zero, Ans.bind_zero_right]

theorem tick_fail (cost : C) :
    andThen (tick cost : Spec K C W Unit) (fail : Spec K C W X) = fail :=
  bind_fail _

/-- With at least two possible charges, the answer readout cannot retain the
charge preceding failure. This rules out recovering a complete paid account
from successful answers alone. -/
theorem no_failed_cost_recovery [Nontrivial C] :
    ¬ ∃ observe : Spec K C W X → C, ∀ cost : C,
      observe (andThen (tick cost) fail) = cost := by
  rintro ⟨observe, recovers⟩
  obtain ⟨first, second, different⟩ := exists_pair_ne C
  apply different
  have first_eq := recovers first
  have second_eq := recovers second
  rw [tick_fail] at first_eq second_eq
  exact first_eq.symm.trans second_eq

theorem weight_bind (k : K) (m : Spec K C W X) (f : X → Spec K C W Y) :
    bind (weight k m) f = weight k (bind m f) := by
  funext world
  exact Ans.smul_bind _ _ _

/-! ### Commutation -/

theorem bind_choose (m : Spec K C W X) (f g : X → Spec K C W Y) :
    bind m (fun x => choose (f x) (g x)) = choose (bind m f) (bind m g) := by
  funext world
  simp only [bind, choose, charge]
  rw [← Ans.bind_add_right]
  congr 1
  funext result
  rw [Ans.map_eq_mapDomain, Ans.map_eq_mapDomain, Ans.map_eq_mapDomain, Finsupp.mapDomain_add]

/-- **Choice commutes with cost.** -/
theorem choose_tick (cost : C) (first second : Spec K C W X) :
    andThen (tick cost) (choose first second) =
      choose (andThen (tick cost) first) (andThen (tick cost) second) :=
  bind_choose _ _ _

/-- **Choice commutes with writes**: worlds are per branch. -/
theorem choose_put (next : W) (first second : Spec K C W X) :
    andThen (put next) (choose first second) =
      choose (andThen (put next) first) (andThen (put next) second) :=
  bind_choose _ _ _

/-- **Choice commutes with reads.** -/
theorem choose_get (first second : W → Spec K C W X) :
    bind get (fun world => choose (first world) (second world)) =
      choose (bind get first) (bind get second) :=
  bind_choose _ _ _

theorem bind_weight (m : Spec K C W X) (k : K) (f : X → Spec K C W Y) :
    bind m (fun x => weight k (f x)) = weight k (bind m f) := by
  funext world
  simp only [bind, weight, charge]
  rw [← Ans.bind_smul_right]
  congr 1
  funext result
  rw [Ans.map_eq_mapDomain, Ans.map_eq_mapDomain, Finsupp.mapDomain_smul]

/-- **Weighting commutes with cost.** -/
theorem weight_tick (k : K) (cost : C) (m : Spec K C W X) :
    andThen (tick cost) (weight k m) = weight k (andThen (tick cost) m) :=
  bind_weight _ _ _

/-- **Weighting commutes with writes.** -/
theorem weight_put (k : K) (next : W) (m : Spec K C W X) :
    andThen (put next) (weight k m) = weight k (andThen (put next) m) :=
  bind_weight _ _ _

/-- **Two costs commute** in a commutative cost monoid. -/
theorem tick_tick (first second : C) :
    andThen (tick first) (tick second) = (andThen (tick second) (tick first) : Spec K C W Unit) := by
  funext world
  simp only [andThen, bind, tick, Ans.pure_bind, charge, map_pure, mul_comm]

omit [CommMonoid C] in
/-- **Weighting distributes over choice.** -/
theorem weight_choose (k : K) (first second : Spec K C W X) :
    weight k (choose first second) = choose (weight k first) (weight k second) := by
  funext world
  exact smul_add k (first world) (second world)

theorem bind_tick (cost : C) (f : Unit → Spec K C W X) (world : W) :
    bind (tick cost) f world = charge cost (f () world) := by
  rw [bind, tick, Ans.pure_bind]

/-- **Cost commutes with writes.** -/
theorem tick_put (cost : C) (next : W) :
    andThen (tick cost) (put next) = (andThen (put next) (tick cost) : Spec K C W Unit) := by
  funext world
  rw [andThen_put, andThen, bind_tick]
  simp only [put, tick, charge, map_pure, mul_one]

/-- **Cost commutes with reads.** -/
theorem tick_get (cost : C) :
    bind (tick cost) (fun _ => get) =
      (bind get fun world => andThen (tick cost) (pure world) : Spec K C W W) := by
  funext world
  rw [bind_get, bind_tick, andThen, bind_tick]
  rfl

/-! ## Absence -/

section Absence

variable {Key : Type*} [DecidableEq K]

/-- A negative read of a space: succeed when `key` carries no annotation. -/
noncomputable def absentAt (key : Key) : Spec K C (Space K Key) Unit :=
  fun space => if space key = 0 then Ans.pure ((), space, 1) else 0

theorem absentAt_present {key : Key} {space : Space K Key} (present : space key ≠ 0) :
    (absentAt key : Spec K C (Space K Key) Unit) space = 0 := by
  rw [absentAt, if_neg present]

theorem andThen_absentAt_absent {X : Type*} {key : Key} {space : Space K Key} (absent : space key = 0)
    (m : Spec K C (Space K Key) X) : andThen (absentAt key) m space = m space := by
  rw [andThen, bind, absentAt, if_pos absent, Ans.pure_bind, charge_one]

end Absence

end Spec

/-! ## Controls -/

namespace Controls

/-- Speculative computations with counts, additive costs and a Boolean world. -/
abbrev BoolSpec (X : Type) := Spec ℕ (Multiplicative ℕ) Bool X

/-- **A write does not commute with a read**: writing then reading returns the
written world; reading then writing returns the old one. -/
theorem put_get_not_comm :
    Spec.andThen (Spec.put true) (Spec.get : BoolSpec Bool) ≠
      Spec.bind Spec.get (fun world => Spec.andThen (Spec.put true) (Spec.pure world)) := by
  intro same
  have := congrFun same false
  rw [Spec.andThen_put, Spec.bind_get, Spec.andThen_put, Spec.get_apply, Spec.pure_apply] at this
  have := congrArg (fun answers : Ans ℕ (Bool × Bool × Multiplicative ℕ) => answers (true, true, 1))
    this
  simp [Ans.pure] at this

/-- Speculative computations over a counted space of one key. -/
abbrev UnitSpec (X : Type) := Spec ℕ (Multiplicative ℕ) (Space ℕ Unit) X

/-- **A write into a key does not commute with a negative read of it.** -/
theorem put_absent_not_comm :
    Spec.andThen (Spec.put (Finsupp.single () 1)) (Spec.absentAt () : UnitSpec Unit) ≠
      Spec.andThen (Spec.absentAt ()) (Spec.put (Finsupp.single () 1)) := by
  intro same
  have := congrFun same 0
  rw [Spec.andThen_put, Spec.absentAt_present (by simp),
    Spec.andThen_absentAt_absent (by simp)] at this
  have := congrArg
    (fun answers : Ans ℕ (Unit × Space ℕ Unit × Multiplicative ℕ) =>
      answers ((), Finsupp.single () 1, 1)) this
  simp [Spec.put, Ans.pure] at this

end Controls

end Mettapedia.Languages.MeTTa.LayerEffects
