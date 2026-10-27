import Mettapedia.Logic.HOL.ImpredicativeKripke
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipExcludedMiddle
import Mathlib.Data.Nat.Log

/-!
# Excluded middle does not follow from the laws of sets

The set package proves native types from the laws of the empty set, the power set and separation, and some
every-splits are excluded middle over these laws (`SetMembershipExcludedMiddle`). Here excluded middle is shown not to
follow from them, by a Kripke model of the checker's proofs (`KripkeModulo.Model.proofSyntaxModulo_sound`).

- **Two stages** (`stages`): now and later. A proposition holds never, only later, or from now on (`level`).
- **Three-valued sets as numbers** (`mem`): the base-three digit of `y` at position `z` says when `z` is a member of
  `y`, never (`0`), later (`1`) or from now on (`2`). Every number is such a set and every finite three-valued set is a
  number (`digit_build`), so a member lies below its set (`lt_of_mem`).
- **The operations** (`sep`, `pow`, `union`, `replace`): separation by any upward-closed predicate keeps the meet of the
  membership and the predicate; the power set holds each set at the stages where it is a subset, and only finitely many
  sets are subsets at the later stage.
- **The laws hold** (`modelLaws_hold`): empty set, power set, separation, union, replacement, induction along
  membership over every predicate, weak excluded middle, and the Gödel–Dummett law `(p → q) ∨ (q → p)`.
- **Excluded middle fails now** (`middle_fails`): "only later" is neither true now nor false at every later stage.

So excluded middle is not derivable from these laws (`middle_not_derivable`), and with the reductions of
`SetMembershipExcludedMiddle`:

- the every-split "every split of `1` has a first part that is empty or has a member" is true, and has no proof from
  them (`emptyOrInhabited_not_derivable`);
- no hypotheses among them prove every true regional native type (`not_regionalComplete`).

The witness is the set `1`, the empty set as a member only later: now it is neither inhabited nor known to be empty
(`one_neither_now`). Extensionality fails in the model (`extensionality_fails`): `1` and `2` have the same members
later. With an equality that grows along the stages it holds, and excluded middle still fails
(`SetMembershipExtensionalIndependence`).

**What Kripke models with identity as equality cannot separate** (`KripkeLaws`). In every Kripke model of the
checker's proofs whose functions are all functions and whose equality is identity, two stages above a stage where the
three laws hold have a common later stage (`directed_of_laws`). Otherwise the parts of `P(∅)` cut
out from one stage on would all lie in `P(∅)` at the other, one for each subset of `P(∅)`'s members there, against
Cantor's theorem. So weak excluded middle holds wherever the laws hold (`weakMiddle_of_laws`), although it fails at the
root of a branching frame (`weakMiddle_fails_branching`). Its independence from the laws needs models outside this
class: in `SetMembershipExtensionalIndependence` the stages of a fork identify sets, and weak excluded middle fails.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL (Ty Ctx Var Term ClosedFormula)
open Mettapedia.Logic.HOL.KripkeModulo (Frame Model Den)
open Mettapedia.Logic.HOL.ImpredicativeConnectives (disjunctionFormula)
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol unionLaw replacementLaw setInduction)

namespace ThreeValued

/-! ## Two stages and three truth values -/

/-- Two stages, now (`false`) and later (`true`). -/
abbrev stages : Frame where
  World := Bool
  le now later := now = false ∨ later = true
  le_refl w := by cases w <;> simp
  le_trans := by
    intro u v w first second
    cases u <;> cases v <;> cases w <;> simp_all

theorem stages_le_later (w : stages.World) : stages.le w true := .inr rfl

theorem holds_of_eq {d e : stages.Up} (same : d = e) (w : stages.World) : d.holds w → e.holds w :=
  same ▸ id

/-- What holds at a stage holds later. -/
theorem holds_later {u : stages.Up} {w : stages.World} (held : u.holds w) : u.holds true :=
  u.mono (stages_le_later w) held

/-- **The three truth values**: `0` never, `1` only later, `2` from now on. -/
def level (d : ℕ) : stages.Up where
  holds w := 2 ≤ d ∨ (1 ≤ d ∧ w = true)
  mono := by
    intro w v later held
    rcases held with held | ⟨held, rfl⟩
    · exact .inl held
    · rcases later with impossible | rfl
      · exact absurd impossible (by decide)
      · exact .inr ⟨held, rfl⟩

theorem holds_level {d : ℕ} {w : stages.World} : (level d).holds w ↔ 2 ≤ d ∨ (1 ≤ d ∧ w = true) := Iff.rfl

theorem holds_level_later {d : ℕ} : (level d).holds true ↔ d ≠ 0 := by
  rw [holds_level]
  simp only [and_true]
  omega

theorem level_mono {a b : ℕ} (le : a ≤ b) {w : stages.World} (held : (level a).holds w) : (level b).holds w := by
  rcases holds_level.mp held with two | ⟨one, rfl⟩
  · exact holds_level.mpr (.inl (by omega))
  · exact holds_level.mpr (.inr ⟨by omega, rfl⟩)

theorem level_min (a b : ℕ) : level (min a b) = stages.andUp (level a) (level b) := by
  apply Frame.Up.ext
  funext w
  apply propext
  change (2 ≤ min a b ∨ (1 ≤ min a b ∧ w = true)) ↔ (2 ≤ a ∨ (1 ≤ a ∧ w = true)) ∧ (2 ≤ b ∨ (1 ≤ b ∧ w = true))
  cases w
  · simp
  · simp only [and_true]
    omega

open Classical in
/-- The level of an upward-closed proposition. -/
noncomputable def levelOf (u : stages.Up) : ℕ := if u.holds false then 2 else if u.holds true then 1 else 0

theorem levelOf_lt (u : stages.Up) : levelOf u < 3 := by
  unfold levelOf
  split_ifs <;> decide

theorem levelOf_eq_zero {u : stages.Up} : levelOf u = 0 ↔ ¬ u.holds true := by
  unfold levelOf
  by_cases now : u.holds false
  · simp [now, holds_later now]
  · by_cases later : u.holds true <;> simp [now, later]

theorem level_levelOf (u : stages.Up) : level (levelOf u) = u := by
  apply Frame.Up.ext
  funext w
  apply propext
  rw [holds_level]
  unfold levelOf
  by_cases now : u.holds false
  · have always : ∀ w : stages.World, u.holds w := fun w => u.mono (show stages.le false w from .inl rfl) now
    simp [now, always w]
  · by_cases later : u.holds true
    · cases w
      · simp [now, later]
      · simp [now, later]
    · cases w
      · simp [now, later]
      · simp [now, later]

/-! ## Base-three digits -/

/-- The digit of `n` at position `z`, in base three. -/
def digit (n z : ℕ) : ℕ := n / 3 ^ z % 3

theorem digit_lt (n z : ℕ) : digit n z < 3 := Nat.mod_lt _ (by decide)

theorem digit_zero (z : ℕ) : digit 0 z = 0 := by simp [digit]

/-- A nonzero digit lies below the number. -/
theorem lt_of_digit_ne_zero {n z : ℕ} (nonzero : digit n z ≠ 0) : z < n := by
  have large : 3 ^ z ≤ n := by
    by_contra small
    apply nonzero
    simp [digit, Nat.div_eq_of_lt (Nat.lt_of_not_le small)]
  exact lt_of_lt_of_le (Nat.lt_pow_self (by decide)) large

/-- A number at least `3 ^ x` has a nonzero digit at a position at least `x`. -/
theorem exists_digit_of_pow_le {n x : ℕ} (large : 3 ^ x ≤ n) : ∃ w, x ≤ w ∧ digit n w ≠ 0 := by
  have nonzero : n ≠ 0 := Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (pow_pos (by decide : 0 < 3) x) large)
  refine ⟨Nat.log 3 n, Nat.le_log_of_pow_le (by decide) large, ?_⟩
  have low := Nat.pow_log_le_self 3 nonzero
  have high := Nat.lt_pow_succ_log_self (by decide : 1 < 3) n
  rw [pow_succ] at high
  have positive : 0 < 3 ^ Nat.log 3 n := pow_pos (by decide) _
  have one : 1 ≤ n / 3 ^ Nat.log 3 n := (Nat.le_div_iff_mul_le positive).mpr (by simpa using low)
  have two : n / 3 ^ Nat.log 3 n < 3 := (Nat.div_lt_iff_lt_mul positive).mpr (by rw [mul_comm]; exact high)
  unfold digit
  rw [Nat.mod_eq_of_lt two]
  omega

/-- The number with digit `f z` at each position `z` below `bound`. -/
def build (bound : ℕ) (f : ℕ → ℕ) : ℕ := ∑ z ∈ Finset.range bound, f z * 3 ^ z

theorem build_succ (bound : ℕ) (f : ℕ → ℕ) : build (bound + 1) f = build bound f + f bound * 3 ^ bound :=
  Finset.sum_range_succ _ _

theorem build_lt {f : ℕ → ℕ} (small : ∀ z, f z < 3) (bound : ℕ) : build bound f < 3 ^ bound := by
  induction bound with
  | zero => simp [build]
  | succ bound ih =>
    rw [build_succ, pow_succ]
    have digitBound : f bound * 3 ^ bound ≤ 2 * 3 ^ bound := Nat.mul_le_mul_right _ (by have := small bound; omega)
    generalize 3 ^ bound = power at *
    omega

/-- **Every finite three-valued set is a number**: the digits of `build bound f` are `f` below the bound. -/
theorem digit_build {f : ℕ → ℕ} (small : ∀ z, f z < 3) (bound z : ℕ) :
    digit (build bound f) z = if z < bound then f z else 0 := by
  induction bound with
  | zero => simp [build, digit]
  | succ bound ih =>
    have below := build_lt small bound
    rw [build_succ]
    rcases lt_trichotomy z bound with lower | rfl | higher
    · have split : 3 ^ bound = 3 ^ (bound - z - 1) * 3 * 3 ^ z := by
        rw [← pow_succ, ← pow_add]
        congr 1
        omega
      rw [if_pos (by omega)]
      have previous := ih
      rw [if_pos lower] at previous
      unfold digit at previous ⊢
      rw [split, ← mul_assoc, ← mul_assoc, Nat.add_mul_div_right _ _ (pow_pos (by decide : 0 < 3) _),
        Nat.add_mul_mod_self_right]
      exact previous
    · rw [if_pos (by omega)]
      unfold digit
      rw [Nat.add_mul_div_right _ _ (pow_pos (by decide : 0 < 3) _), Nat.div_eq_of_lt below, zero_add,
        Nat.mod_eq_of_lt (small _)]
    · rw [if_neg (by omega)]
      have total : build bound f + f bound * 3 ^ bound < 3 ^ z := by
        have step : 3 ^ (bound + 1) ≤ 3 ^ z := Nat.pow_le_pow_right (by decide) (Nat.succ_le_of_lt higher)
        rw [pow_succ] at step
        have digitBound : f bound * 3 ^ bound ≤ 2 * 3 ^ bound :=
          Nat.mul_le_mul_right _ (by have := small bound; omega)
        generalize 3 ^ bound = power at *
        omega
      unfold digit
      rw [Nat.div_eq_of_lt total]

theorem digit_build_eq {f : ℕ → ℕ} (small : ∀ z, f z < 3) {bound : ℕ} (vanish : ∀ z, bound ≤ z → f z = 0)
    (z : ℕ) : digit (build bound f) z = f z := by
  rw [digit_build small]
  split_ifs with lower
  · rfl
  · exact (vanish z (Nat.le_of_not_lt lower)).symm

/-! ## Three-valued sets -/

/-- **Membership**: the digit of the set at the member's position, read as a truth value. -/
def mem (z y : ℕ) : stages.Up := level (digit y z)

theorem holds_mem_later {z y : ℕ} : (mem z y).holds true ↔ digit y z ≠ 0 := holds_level_later

/-- A member lies below its set. -/
theorem lt_of_mem {z y : ℕ} {w : stages.World} (held : (mem z y).holds w) : z < y :=
  lt_of_digit_ne_zero (holds_mem_later.mp (holds_later held))

theorem not_mem_zero (z : ℕ) (w : stages.World) : ¬ (mem z 0).holds w := fun held =>
  absurd (lt_of_mem held) (Nat.not_lt_zero z)

/-- Inclusion, as a truth value. -/
def subset (z x : ℕ) : stages.Up := stages.allUp fun w : ℕ => stages.impUp (mem w z) (mem w x)

/-- **Separation** by an upward-closed predicate. -/
noncomputable def sep (x : ℕ) (p : ℕ → stages.Up) : ℕ := build x fun z => min (digit x z) (levelOf (p z))

/-- **The power set**: each set at the stages where it is a subset. -/
noncomputable def pow (x : ℕ) : ℕ := build (3 ^ x) fun z => levelOf (subset z x)

/-- **The union** of the members. -/
noncomputable def union (x : ℕ) : ℕ :=
  build x fun z => levelOf (stages.exUp fun y : ℕ => stages.andUp (mem y x) (mem z y))

/-- **The image** of the members. -/
noncomputable def replace (x : ℕ) (f : ℕ → ℕ) : ℕ :=
  build ((Finset.range x).sup f + 1) fun z =>
    levelOf (stages.exUp fun y : ℕ => stages.andUp (mem y x) (stages.constUp (f y = z)))

theorem mem_sep (z x : ℕ) (p : ℕ → stages.Up) : mem z (sep x p) = stages.andUp (mem z x) (p z) := by
  unfold mem sep
  rw [digit_build_eq (fun z => lt_of_le_of_lt (min_le_left _ _) (digit_lt x z)), level_min, level_levelOf]
  intro z beyond
  have missing : digit x z = 0 := by
    by_contra nonzero
    exact absurd (lt_of_digit_ne_zero nonzero) (Nat.not_lt.mpr beyond)
  simp [missing]

theorem mem_pow (z x : ℕ) : mem z (pow x) = subset z x := by
  unfold mem pow
  rw [digit_build_eq (fun z => levelOf_lt _), level_levelOf]
  intro z large
  refine levelOf_eq_zero.mpr fun included => ?_
  obtain ⟨w, beyond, nonzero⟩ := exists_digit_of_pow_le large
  have inside := included w true (stages_le_later true) (holds_mem_later.mpr nonzero)
  exact absurd (lt_of_mem inside) (Nat.not_lt.mpr beyond)

theorem mem_union (z x : ℕ) :
    mem z (union x) = stages.exUp fun y : ℕ => stages.andUp (mem y x) (mem z y) := by
  change level (digit (union x) z) = _
  unfold union
  rw [digit_build_eq (fun z => levelOf_lt _), level_levelOf]
  intro z beyond
  refine levelOf_eq_zero.mpr ?_
  rintro ⟨y, inside, held⟩
  exact absurd (lt_trans (lt_of_mem held) (lt_of_mem inside)) (Nat.not_lt.mpr beyond)

theorem mem_replace (z x : ℕ) (f : ℕ → ℕ) :
    mem z (replace x f) = stages.exUp fun y : ℕ => stages.andUp (mem y x) (stages.constUp (f y = z)) := by
  change level (digit (replace x f) z) = _
  unfold replace
  rw [digit_build_eq (fun z => levelOf_lt _), level_levelOf]
  intro z beyond
  refine levelOf_eq_zero.mpr ?_
  rintro ⟨y, inside, image⟩
  have bounded : f y ≤ (Finset.range x).sup f := Finset.le_sup (Finset.mem_range.mpr (lt_of_mem inside))
  change f y = z at image
  omega

/-! ## The model -/

/-- The symbols, read on three-valued sets. -/
noncomputable def denoteSymbol : {τ : Ty Unit} → Symbol τ → Den stages (fun _ => ℕ) τ
  | _, .member => mem
  | _, .empty => (0 : ℕ)
  | _, .union => union
  | _, .power => pow
  | _, .separate => sep
  | _, .replace => replace

/-- **The Kripke model**: three-valued sets over two stages. -/
noncomputable def model : Model Unit Symbol where
  frame := stages
  Carrier _ := ℕ
  constDen := denoteSymbol

/-- The valuation of the empty context. -/
def closed : model.Valuation [] := fun index => nomatch index

/-- **Gödel–Dummett**: `∀ p q. (p → q) ∨ (q → p)`. -/
def linearityLaw : ClosedFormula Symbol :=
  .all (σ := .prop) (.all (σ := .prop)
    (disjunctionFormula (.imp (.var (.vs .vz)) (.var .vz)) (.imp (.var .vz) (.var (.vs .vz)))))

/-- The laws the model satisfies. -/
def modelLaws : List (ClosedFormula Symbol) :=
  [lawEmpty, lawPower, lawSeparation, unionLaw, replacementLaw, setInduction, weakMiddleLaw, linearityLaw]

theorem lawEmpty_holds (w : stages.World) : (model.denote lawEmpty closed).holds w := by
  intro x
  exact (model.holds_negation _ _ w).mpr fun v _ => not_mem_zero x v

theorem lawPower_holds (w : stages.World) : (model.denote lawPower closed).holds w := by
  intro a b
  refine (model.holds_conjunctionFormula _ _ _ w).mpr ⟨fun v _ held => ?_, fun v _ held => ?_⟩
  · exact holds_of_eq (mem_pow b a) v held
  · exact holds_of_eq (mem_pow b a).symm v held

theorem lawSeparation_holds (w : stages.World) : (model.denote lawSeparation closed).holds w := by
  intro a p z
  refine (model.holds_conjunctionFormula _ _ _ w).mpr ⟨fun v _ held => ?_, fun v _ held => ?_⟩
  · obtain ⟨inside, chosen⟩ := holds_of_eq (mem_sep z a p) v held
    exact (model.holds_conjunctionFormula _ _ _ v).mpr ⟨inside, chosen⟩
  · obtain ⟨inside, chosen⟩ := (model.holds_conjunctionFormula _ _ _ v).mp held
    exact holds_of_eq (mem_sep z a p).symm v ⟨inside, chosen⟩

theorem unionLaw_holds (w : stages.World) : (model.denote unionLaw closed).holds w := by
  intro a z
  exact ⟨fun v _ held => holds_of_eq (mem_union z a) v held, fun v _ held => holds_of_eq (mem_union z a).symm v held⟩

theorem replacementLaw_holds (w : stages.World) : (model.denote replacementLaw closed).holds w := by
  intro a f z
  exact ⟨fun v _ held => holds_of_eq (mem_replace z a f) v held,
    fun v _ held => holds_of_eq (mem_replace z a f).symm v held⟩

/-- **Induction along membership**, for every predicate: a member lies below its set. -/
theorem setInduction_holds (w : stages.World) : (model.denote setInduction closed).holds w := by
  intro p v _ step x
  induction x using Nat.strong_induction_on with
  | _ x ih =>
    exact step x v (stages.le_refl v) fun y u hvu inside =>
      (p y).mono hvu (ih y (lt_of_mem inside))

theorem weakMiddle_holds (w : stages.World) : (model.denote weakMiddleLaw closed).holds w := by
  intro p
  change stages.Up at p
  refine (model.holds_disjunctionFormula _ _ _ w).mpr ?_
  by_cases late : p.holds true
  · refine .inr ((model.holds_negation _ _ w).mpr fun v _ refuted => ?_)
    exact (model.holds_negation _ _ v).mp refuted true (stages_le_later v) late
  · exact .inl ((model.holds_negation _ _ w).mpr fun v _ held => late (holds_later held))

theorem linearity_holds (w : stages.World) : (model.denote linearityLaw closed).holds w := by
  intro p q
  change stages.Up at p q
  refine (model.holds_disjunctionFormula _ _ _ w).mpr ?_
  rcases le_total (levelOf p) (levelOf q) with order | order
  · refine .inl fun v _ held => ?_
    exact holds_of_eq (level_levelOf q) v (level_mono order (holds_of_eq (level_levelOf p).symm v held))
  · refine .inr fun v _ held => ?_
    exact holds_of_eq (level_levelOf p) v (level_mono order (holds_of_eq (level_levelOf q).symm v held))

theorem modelLaws_hold (w : stages.World) : ∀ δ ∈ modelLaws, (model.denote δ closed).holds w := by
  intro δ listed
  simp only [modelLaws, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lawEmpty_holds w
  · exact lawPower_holds w
  · exact lawSeparation_holds w
  · exact unionLaw_holds w
  · exact replacementLaw_holds w
  · exact setInduction_holds w
  · exact weakMiddle_holds w
  · exact linearity_holds w

/-- **Excluded middle fails now**: "only later" is not true now, and it is not false later. -/
theorem middle_fails : ¬ (model.denote middleLaw closed).holds false := by
  intro middle
  rcases (model.holds_disjunctionFormula _ _ _ false).mp (middle (level 1)) with now | never
  · exact absurd (holds_level.mp now) (by decide)
  · exact (model.holds_negation _ _ false).mp never true (stages_le_later false) (holds_level.mpr (.inr ⟨le_rfl, rfl⟩))

/-! ## Independence -/

/-- **Soundness for closed proofs**: a proof from hypotheses that hold at a stage proves a formula holding there. -/
theorem sound {Δ : List (ClosedFormula Symbol)} {φ : ClosedFormula Symbol} (proof : Proof Δ φ) (w : stages.World)
    (hyps : ∀ δ ∈ Δ, (model.denote δ closed).holds w) : (model.denote φ closed).holds w :=
  model.proofSyntaxModulo_sound (fun _ listed => absurd listed List.not_mem_nil) proof closed w hyps

/-- **Excluded middle is not derivable** from the laws of the empty set, the power set, separation, union,
replacement and induction along membership, with weak excluded middle and the Gödel–Dummett law. -/
theorem middle_not_derivable {Δ : List (ClosedFormula Symbol)} (among : ∀ δ ∈ Δ, δ ∈ modelLaws)
    (proof : Proof Δ middleLaw) : False :=
  middle_fails (sound proof false fun δ listed => modelLaws_hold false δ (among δ listed))

theorem isEmpty_middle : IsEmpty (Proof modelLaws middleLaw) := ⟨middle_not_derivable fun _ => id⟩

/-- The three laws, among the model's laws. -/
def lawsOfModelLaws : HasLaws modelLaws where
  empty := Proof.cast (atContext_nil _).symm (.hyp ⟨0, by decide⟩)
  power := Proof.cast (atContext_nil _).symm (.hyp ⟨1, by decide⟩)
  separation := Proof.cast (atContext_nil _).symm (.hyp ⟨2, by decide⟩)

/-- **A true every-split with no proof**: every split of `1` has a first part that is empty or has a member, and no
hypotheses among the model's laws prove it. -/
theorem emptyOrInhabited_not_derivable {Δ : List (ClosedFormula Symbol)} (among : ∀ δ ∈ Δ, δ ∈ modelLaws)
    (proof : Proof Δ (nativeTypeSentence emptyOrInhabited one)) : False := by
  have holds := sound proof false fun δ listed => modelLaws_hold false δ (among δ listed)
  have gives := sound (middleOfEmptyOrInhabited lawsOfModelLaws one_isHF (value := zero) (List.mem_singleton.mpr rfl))
    false (modelLaws_hold false)
  exact middle_fails (gives false (stages.le_refl false) holds)

/-- **The model's laws are not complete for the regional fragment**: some true regional native type has no proof
from them. -/
theorem not_regionalComplete :
    ¬ ∀ formula : Formula 0, formula.regional = true → ∀ term : Pattern, IsHF term →
      Membership.sat Env.closed formula term → Nonempty (Proof modelLaws (nativeTypeSentence formula term)) := by
  intro complete
  obtain ⟨middle⟩ := (regionalComplete_iff_middle lawsOfModelLaws).mp complete
  exact isEmpty_middle.false middle

/-! ## Controls -/

theorem digit_one_le (z : ℕ) : digit 1 z ≤ 1 :=
  le_trans (Nat.mod_le _ _) (Nat.div_le_self _ _)

theorem digit_pos_eq_zero {n z : ℕ} (small : n < 3) (positive : 1 ≤ z) : digit n z = 0 := by
  have large : 3 ≤ 3 ^ z := by simpa using Nat.pow_le_pow_right (by decide : 0 < 3) positive
  simp [digit, Nat.div_eq_of_lt (lt_of_lt_of_le small large)]

/-- **The witness**: the set `1` has the empty set as a member only later, so now it is neither inhabited nor known
to be empty. -/
theorem one_neither_now : (¬ ∃ z, (mem z 1).holds false) ∧ (mem 0 1).holds true := by
  refine ⟨?_, holds_mem_later.mpr (by decide)⟩
  rintro ⟨z, held⟩
  have := digit_one_le z
  rcases holds_level.mp held with two | ⟨_, impossible⟩
  · omega
  · exact absurd impossible (by decide)

/-- The set `2` has the empty set as a member from now on. -/
theorem two_inhabited_now : (mem 0 2).holds false := holds_level.mpr (.inl (by decide))

/-- The empty set is in its power set from now on. -/
theorem zero_mem_pow_zero : (mem 0 (pow 0)).holds false :=
  holds_of_eq (mem_pow 0 0).symm false fun _ _ _ held => held

/-- **Not every law holds**: extensionality fails, since `1` and `2` have the same members later. -/
theorem extensionality_fails :
    ¬ (model.denote Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation.extensionality closed).holds false := by
  intro extensional
  have same : ∀ z : ℕ, ∀ u : stages.World, stages.le true u → ((mem z 1).holds u ↔ (mem z 2).holds u) := by
    intro z u later
    rcases later with impossible | rfl
    · exact absurd impossible (by decide)
    · rw [holds_mem_later, holds_mem_later]
      rcases Nat.eq_zero_or_pos z with rfl | positive
      · decide
      · rw [digit_pos_eq_zero (by decide) positive, digit_pos_eq_zero (by decide) positive]
  have equal := extensional (1 : ℕ) (2 : ℕ) true (stages_le_later false) fun z => ⟨fun u later held => (same z u later).mp held,
    fun u later held => (same z u later).mpr held⟩
  exact (by decide : (1 : ℕ) ≠ 2) ((model.holds_eq _ _ _ true).mp equal)

end ThreeValued

/-! ## What Kripke models cannot separate -/

namespace KripkeLaws

variable (M : Model Unit Symbol)

/-- The valuation of the empty context. -/
def closedOf : M.Valuation [] := fun index => nomatch index

/-- Membership in a model. -/
def memOf : M.Carrier () → M.Carrier () → M.frame.Up := M.constDen .member

def emptyOf : M.Carrier () := M.constDen .empty

def powOf : M.Carrier () → M.Carrier () := M.constDen .power

def sepOf : M.Carrier () → (M.Carrier () → M.frame.Up) → M.Carrier () := M.constDen .separate

/-- The three laws at a stage. -/
structure LawsAt (r : M.frame.World) : Prop where
  empty : (M.denote lawEmpty (closedOf M)).holds r
  power : (M.denote lawPower (closedOf M)).holds r
  separation : (M.denote lawSeparation (closedOf M)).holds r

variable {M}

theorem LawsAt.later {r v : M.frame.World} (laws : LawsAt M r) (later : M.frame.le r v) : LawsAt M v :=
  ⟨Frame.Up.mono (M.denote lawEmpty (closedOf M)) later laws.empty,
    Frame.Up.mono (M.denote lawPower (closedOf M)) later laws.power,
    Frame.Up.mono (M.denote lawSeparation (closedOf M)) later laws.separation⟩

theorem LawsAt.not_mem_empty {v : M.frame.World} (laws : LawsAt M v) (x : M.Carrier ()) :
    ¬ (memOf M x (emptyOf M)).holds v :=
  (M.holds_negation _ _ v).mp (laws.empty x) v (M.frame.le_refl v)

theorem LawsAt.mem_pow {v : M.frame.World} (laws : LawsAt M v) (a b : M.Carrier ()) :
    (memOf M b (powOf M a)).holds v ↔
      ∀ z u, M.frame.le v u → (memOf M z b).holds u → (memOf M z a).holds u := by
  have both := (M.holds_conjunctionFormula _ _ _ v).mp (laws.power a b)
  exact ⟨fun held => both.1 v (M.frame.le_refl v) held, fun held => both.2 v (M.frame.le_refl v) held⟩

theorem LawsAt.mem_sep {v : M.frame.World} (laws : LawsAt M v) (a : M.Carrier ()) (p : M.Carrier () → M.frame.Up)
    (z : M.Carrier ()) : (memOf M z (sepOf M a p)).holds v ↔ (memOf M z a).holds v ∧ (p z).holds v := by
  have both := (M.holds_conjunctionFormula _ _ _ v).mp (laws.separation a p z)
  exact ⟨fun held => (M.holds_conjunctionFormula _ _ _ v).mp (both.1 v (M.frame.le_refl v) held),
    fun held => both.2 v (M.frame.le_refl v) ((M.holds_conjunctionFormula _ _ _ v).mpr held)⟩

/-- `P(∅)` holds a set at a stage when the set has no member at any later stage. -/
theorem LawsAt.mem_powEmpty {v : M.frame.World} (laws : LawsAt M v) (z : M.Carrier ()) :
    (memOf M z (powOf M (emptyOf M))).holds v ↔ ∀ u, M.frame.le v u → ∀ y, ¬ (memOf M y z).holds u := by
  rw [laws.mem_pow]
  exact ⟨fun included u later y held => (laws.later later).not_mem_empty y (included y u later held),
    fun none y u later held => absurd held (none u later y)⟩

variable (M)

/-- The members of `S` cut out of `P(∅)` from stage `w` on. -/
def cut (w : M.frame.World) (S : Set (M.Carrier ())) : M.Carrier () :=
  sepOf M (powOf M (emptyOf M)) fun z =>
    ⟨fun u => z ∈ S ∧ M.frame.le w u, fun later held => ⟨held.1, M.frame.le_trans held.2 later⟩⟩

variable {M}

/-- **Two stages above a stage where the laws hold have a common later stage.** Otherwise the cuts from one stage
would all be empty at the other, and each subset of `P(∅)`'s members at one stage would give a different such member
(Cantor). -/
theorem directed_of_laws {r : M.frame.World} (laws : LawsAt M r) {a b : M.frame.World} (ra : M.frame.le r a)
    (rb : M.frame.le r b) : ∃ c, M.frame.le a c ∧ M.frame.le b c := by
  by_contra apart
  simp only [not_exists, not_and] at apart
  have mem_cut : ∀ w v, M.frame.le r v → ∀ S z, (memOf M z (cut M w S)).holds v ↔
      (memOf M z (powOf M (emptyOf M))).holds v ∧ z ∈ S ∧ M.frame.le w v :=
    fun w v later S z => (laws.later later).mem_sep _ _ z
  have cut_b_at_a : ∀ S, (memOf M (cut M b S) (powOf M (emptyOf M))).holds a := by
    intro S
    refine ((laws.later ra).mem_powEmpty _).mpr fun u later y held => ?_
    exact apart u later ((mem_cut b u (M.frame.le_trans ra later) S y).mp held).2.2
  have cut_a_at_b : ∀ S, (memOf M (cut M a S) (powOf M (emptyOf M))).holds b := by
    intro S
    refine ((laws.later rb).mem_powEmpty _).mpr fun u later y held => ?_
    exact apart u ((mem_cut a u (M.frame.le_trans rb later) S y).mp held).2.2 later
  let K := {z : M.Carrier () // (memOf M z (powOf M (emptyOf M))).holds b}
  let encode : Set K → K := fun A => ⟨cut M a {cut M b (Subtype.val '' A)}, cut_a_at_b _⟩
  apply Function.cantor_injective encode
  intro A A' same
  have equal : cut M a {cut M b (Subtype.val '' A)} = cut M a {cut M b (Subtype.val '' A')} := congrArg Subtype.val same
  have self : (memOf M (cut M b (Subtype.val '' A)) (cut M a {cut M b (Subtype.val '' A)})).holds a :=
    (mem_cut a a ra _ _).mpr ⟨cut_b_at_a _, rfl, M.frame.le_refl a⟩
  rw [equal] at self
  have cuts : cut M b (Subtype.val '' A) = cut M b (Subtype.val '' A') := ((mem_cut a a ra _ _).mp self).2.1
  ext k
  have read : ∀ B : Set K, k ∈ B ↔ (memOf M k.val (cut M b (Subtype.val '' B))).holds b := by
    intro B
    rw [mem_cut b b rb]
    exact ⟨fun inside => ⟨k.2, ⟨k, inside, rfl⟩, M.frame.le_refl b⟩,
      fun ⟨_, ⟨k', inside, same'⟩, _⟩ => (Subtype.val_injective same' : k' = k) ▸ inside⟩
  rw [read A, read A', cuts]

/-- **The laws fail below two stages with no common later stage**, in every Kripke model. -/
theorem not_lawsAt_of_apart {r a b : M.frame.World} (ra : M.frame.le r a) (rb : M.frame.le r b)
    (apart : ∀ c, M.frame.le a c → ¬ M.frame.le b c) : ¬ LawsAt M r := fun laws =>
  let ⟨c, ac, bc⟩ := directed_of_laws laws ra rb
  apart c ac bc

/-- **Weak excluded middle holds wherever the laws hold**, in every Kripke model: no Kripke model separates weak
excluded middle from the laws of the empty set, the power set and separation. -/
theorem weakMiddle_of_laws {r : M.frame.World} (laws : LawsAt M r) :
    (M.denote weakMiddleLaw (closedOf M)).holds r := by
  intro p
  change M.frame.Up at p
  refine (M.holds_disjunctionFormula _ _ _ r).mpr ?_
  by_cases somewhere : ∃ v, M.frame.le r v ∧ p.holds v
  · obtain ⟨v₀, rv₀, held⟩ := somewhere
    refine .inr ((M.holds_negation _ _ r).mpr fun v rv refuted => ?_)
    obtain ⟨c, vc, v₀c⟩ := directed_of_laws laws rv rv₀
    exact (M.holds_negation _ _ v).mp refuted c vc (p.mono v₀c held)
  · simp only [not_exists, not_and] at somewhere
    exact .inl ((M.holds_negation _ _ r).mpr fun v rv held => somewhere v rv held)

/-! ### Controls: a branching frame -/

/-- A root with two incomparable later stages. -/
abbrev branching : Frame where
  World := Option Bool
  le now later := now = none ∨ now = later
  le_refl w := .inr rfl
  le_trans := by
    intro u v w first second
    rcases first with rfl | rfl
    · exact .inl rfl
    · exact second

/-- Some interpretation of the symbols over the branching frame. -/
def branchingSymbol : {τ : Ty Unit} → Symbol τ → Den branching (fun _ => Unit) τ
  | _, .member => fun _ _ => branching.constUp False
  | _, .empty => ()
  | _, .union => fun _ => ()
  | _, .power => fun _ => ()
  | _, .separate => fun _ _ => ()
  | _, .replace => fun _ _ => ()

def branchingModel : Model Unit Symbol where
  frame := branching
  Carrier _ := Unit
  constDen := branchingSymbol

/-- **Weak excluded middle can fail in a Kripke model**: at the root of the branching frame, "from the first branch
on" is neither refuted nor doubly negated. -/
theorem weakMiddle_fails_branching : ¬ (branchingModel.denote weakMiddleLaw (closedOf branchingModel)).holds none := by
  intro weakMiddle
  let first : branching.Up := ⟨fun w => w = some true, by
    intro w v later held
    rcases later with rfl | rfl
    · cases held
    · exact held⟩
  rcases (branchingModel.holds_disjunctionFormula _ _ _ none).mp (weakMiddle first) with refuted | doubly
  · exact (branchingModel.holds_negation _ _ none).mp refuted (some true) (.inl rfl) rfl
  · refine (branchingModel.holds_negation _ _ none).mp doubly (some false) (.inl rfl) ?_
    refine (branchingModel.holds_negation _ _ (some false)).mpr fun v later held => ?_
    rcases later with impossible | rfl
    · cases impossible
    · cases held


end KripkeLaws

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
