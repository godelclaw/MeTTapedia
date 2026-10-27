import Mettapedia.Logic.HOL.Semantics.ImpredicativeKripkeHenkin
import Mettapedia.Logic.HOL.Semantics.KripkeFrameModel
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipIndependence

/-!
# Sets whose equality grows along the stages

`SetMembershipIndependence` reads sets with a crisp equality: two sets with the same members at a later stage stay two
sets. Then extensionality fails, and over any branching of stages the laws of the empty set, the power set and
separation fail too (`KripkeLaws.not_lawsAt_of_apart`). Here sets become equal as soon as their members agree at every
later stage, over any frame whose upward-closed sets of stages can be listed.

- **The truth values** (`Stages`): a preorder of stages with its upward-closed sets listed as `level d` for `d` below
  `count`, `level 0` the empty one.
- **Sets as numbers**: the base-`count` digit of `x` at position `z` is the truth value of "`z` is listed in `x`"
  (`lit`), so every finite family of truth values is a set (`digit_build`).
- **Equality** (`same`): `x` and `y` are equal at a stage when at every later stage each listed member of one is equal,
  there, to a listed member of the other. It is an equivalence that grows along the stages, and **membership** (`mem`),
  being equal to a listed member, respects it on both sides. Two sets are equal exactly when they have the same members
  at every later stage (`same_iff_members`): extensionality holds by construction.
- **The operations**: the empty set (`0`), separation (`sep`), the power set (`pow`, listing the sets whose listed
  members are listed in the set), and the union (`union`) have their members as the laws say (`mem_sep`, `mem_pow`,
  `mem_union`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings.KripkeSets

/-! ## Digits in base `b` -/

/-- The digit of `n` at position `z`, in base `b`. -/
def digit (b n z : ℕ) : ℕ := n / b ^ z % b

variable {b : ℕ}

theorem digit_lt (one : 1 < b) (n z : ℕ) : digit b n z < b := Nat.mod_lt _ (by omega)

/-- A nonzero digit lies below the number. -/
theorem lt_of_digit_ne_zero (one : 1 < b) {n z : ℕ} (nonzero : digit b n z ≠ 0) : z < n := by
  have large : b ^ z ≤ n := by
    by_contra small
    apply nonzero
    simp [digit, Nat.div_eq_of_lt (Nat.lt_of_not_le small)]
  exact lt_of_lt_of_le (Nat.lt_pow_self one) large

/-- A number at least `b ^ x` has a nonzero digit at a position at least `x`. -/
theorem exists_digit_of_pow_le (one : 1 < b) {n x : ℕ} (large : b ^ x ≤ n) : ∃ w, x ≤ w ∧ digit b n w ≠ 0 := by
  have nonzero : n ≠ 0 := Nat.pos_iff_ne_zero.mp (lt_of_lt_of_le (pow_pos (by omega : 0 < b) x) large)
  refine ⟨Nat.log b n, Nat.le_log_of_pow_le one large, ?_⟩
  have low := Nat.pow_log_le_self b nonzero
  have high := Nat.lt_pow_succ_log_self one n
  rw [pow_succ] at high
  have positive : 0 < b ^ Nat.log b n := pow_pos (by omega) _
  have atLeast : 1 ≤ n / b ^ Nat.log b n := (Nat.le_div_iff_mul_le positive).mpr (by simpa using low)
  have below : n / b ^ Nat.log b n < b := (Nat.div_lt_iff_lt_mul positive).mpr (by rw [mul_comm]; exact high)
  unfold digit
  rw [Nat.mod_eq_of_lt below]
  omega

/-- The number with digit `f z` at each position `z` below `bound`. -/
def build (b bound : ℕ) (f : ℕ → ℕ) : ℕ := ∑ z ∈ Finset.range bound, f z * b ^ z

theorem build_succ (bound : ℕ) (f : ℕ → ℕ) : build b (bound + 1) f = build b bound f + f bound * b ^ bound :=
  Finset.sum_range_succ _ _

theorem build_add_lt {f : ℕ → ℕ} (small : ∀ z, f z < b) {bound : ℕ} (below : build b bound f < b ^ bound) :
    build b bound f + f bound * b ^ bound < b ^ (bound + 1) := by
  have digitBound : (f bound + 1) * b ^ bound ≤ b * b ^ bound := Nat.mul_le_mul_right _ (small bound)
  rw [Nat.add_mul, one_mul] at digitBound
  rw [pow_succ, mul_comm (b ^ bound) b]
  generalize b ^ bound = power at *
  omega

theorem build_lt {f : ℕ → ℕ} (small : ∀ z, f z < b) (bound : ℕ) : build b bound f < b ^ bound := by
  induction bound with
  | zero => simp [build]
  | succ bound ih =>
    rw [build_succ]
    exact build_add_lt small ih

/-- **Every finite family of digits is a number**: the digits of `build b bound f` are `f` below the bound. -/
theorem digit_build (one : 1 < b) {f : ℕ → ℕ} (small : ∀ z, f z < b) (bound z : ℕ) :
    digit b (build b bound f) z = if z < bound then f z else 0 := by
  have positive : 0 < b := by omega
  induction bound with
  | zero => simp [build, digit]
  | succ bound ih =>
    have below := build_lt small bound
    rw [build_succ]
    rcases lt_trichotomy z bound with lower | rfl | higher
    · have split : b ^ bound = b ^ (bound - z - 1) * b * b ^ z := by
        rw [← pow_succ, ← pow_add]
        congr 1
        omega
      rw [if_pos (by omega)]
      have previous := ih
      rw [if_pos lower] at previous
      unfold digit at previous ⊢
      rw [split, ← mul_assoc, ← mul_assoc, Nat.add_mul_div_right _ _ (pow_pos positive _),
        Nat.add_mul_mod_self_right]
      exact previous
    · rw [if_pos (by omega)]
      unfold digit
      rw [Nat.add_mul_div_right _ _ (pow_pos positive _), Nat.div_eq_of_lt below, zero_add,
        Nat.mod_eq_of_lt (small _)]
    · rw [if_neg (by omega)]
      have total : build b bound f + f bound * b ^ bound < b ^ z :=
        lt_of_lt_of_le (build_add_lt small below) (Nat.pow_le_pow_right positive (Nat.succ_le_of_lt higher))
      unfold digit
      rw [Nat.div_eq_of_lt total, Nat.zero_mod]

theorem digit_build_eq (one : 1 < b) {f : ℕ → ℕ} (small : ∀ z, f z < b) {bound : ℕ}
    (vanish : ∀ z, bound ≤ z → f z = 0) (z : ℕ) : digit b (build b bound f) z = f z := by
  rw [digit_build one small]
  split_ifs with lower
  · rfl
  · exact (vanish z (Nat.le_of_not_lt lower)).symm

/-! ## Stages and their truth values -/

/-- **A preorder of stages with its truth values listed**: the upward-closed sets of stages are `level d` for `d`
below `count`; `level 0` holds nowhere and the others somewhere. -/
structure Stages where
  World : Type
  le : World → World → Prop
  le_refl : ∀ w, le w w
  le_trans : ∀ {u v w : World}, le u v → le v w → le u w
  count : ℕ
  one_lt_count : 1 < count
  level : ℕ → World → Prop
  level_mono : ∀ (d : ℕ) {v w : World}, le v w → level d v → level d w
  level_zero : ∀ w, ¬ level 0 w
  level_pos : ∀ d, 0 < d → d < count → ∃ w, level d w
  level_onto : ∀ P : World → Prop, (∀ {v w : World}, le v w → P v → P w) → ∃ d < count, ∀ w, level d w ↔ P w

namespace Stages

variable (S : Stages)

/-- An upward-closed set of stages. -/
def Upward (P : S.World → Prop) : Prop := ∀ {v w : S.World}, S.le v w → P v → P w

open Classical in
/-- **The truth value of an upward-closed set of stages**: the least index listing it. -/
noncomputable def levelOf (P : S.World → Prop) : ℕ :=
  if h : ∃ d, d < S.count ∧ ∀ w, S.level d w ↔ P w then Nat.find h else 0

variable {S}

theorem levelOf_lt (P : S.World → Prop) : S.levelOf P < S.count := by
  classical
  unfold levelOf
  split_ifs with h
  · exact (Nat.find_spec h).1
  · exact lt_trans Nat.zero_lt_one S.one_lt_count

theorem level_levelOf {P : S.World → Prop} (up : S.Upward P) (w : S.World) : S.level (S.levelOf P) w ↔ P w := by
  classical
  obtain ⟨d, small, same⟩ := S.level_onto P up
  have h : ∃ d, d < S.count ∧ ∀ w, S.level d w ↔ P w := ⟨d, small, same⟩
  unfold levelOf
  rw [dif_pos h]
  exact (Nat.find_spec h).2 w

/-- The truth value of the empty set of stages is `0`. -/
theorem levelOf_eq_zero {P : S.World → Prop} (never : ∀ w, ¬ P w) : S.levelOf P = 0 := by
  classical
  have h : ∃ d, d < S.count ∧ ∀ w, S.level d w ↔ P w :=
    ⟨0, lt_trans Nat.zero_lt_one S.one_lt_count, fun w => iff_of_false (S.level_zero w) (never w)⟩
  unfold levelOf
  rw [dif_pos h]
  exact Nat.eq_zero_of_le_zero (Nat.find_min' h ⟨lt_trans Nat.zero_lt_one S.one_lt_count,
    fun w => iff_of_false (S.level_zero w) (never w)⟩)

/-! ## Sets as numbers -/

/-- **`z` is listed in `x`** at a stage: the digit of `x` at `z`, read as a truth value. -/
def lit (S : Stages) (w : S.World) (z x : ℕ) : Prop := S.level (digit S.count x z) w

theorem lit_mono {v w : S.World} (later : S.le v w) {z x : ℕ} (listed : S.lit v z x) : S.lit w z x :=
  S.level_mono _ later listed

/-- A listed member lies below its set. -/
theorem lt_of_lit {w : S.World} {z x : ℕ} (listed : S.lit w z x) : z < x := by
  refine lt_of_digit_ne_zero S.one_lt_count fun zero => ?_
  unfold lit at listed
  rw [zero] at listed
  exact S.level_zero w listed

/-- **Equality at a stage**: at every later stage each listed member of one set is equal, there, to a listed member of
the other. -/
def same (S : Stages) : ℕ → ℕ → S.World → Prop
  | x, y, w => ∀ v, S.le w v →
      (∀ z : Fin x, S.lit v z x → ∃ z' : Fin y, S.lit v z' y ∧ same S z z' v) ∧
      (∀ z' : Fin y, S.lit v z' y → ∃ z : Fin x, S.lit v z x ∧ same S z z' v)
termination_by x y => x + y
decreasing_by all_goals (have := z.isLt; have := z'.isLt; omega)

theorem same_iff {x y : ℕ} {w : S.World} : S.same x y w ↔ ∀ v, S.le w v →
    (∀ z, S.lit v z x → ∃ z', S.lit v z' y ∧ S.same z z' v) ∧
    (∀ z', S.lit v z' y → ∃ z, S.lit v z x ∧ S.same z z' v) := by
  rw [same]
  refine forall_congr' fun v => imp_congr_right fun _ => and_congr ⟨fun forth z listed => ?_, fun forth z => ?_⟩
    ⟨fun back z' listed => ?_, fun back z' => ?_⟩
  · obtain ⟨z', listed', related⟩ := forth ⟨z, lt_of_lit listed⟩ listed
    exact ⟨z', listed', related⟩
  · intro listed
    obtain ⟨z', listed', related⟩ := forth z listed
    exact ⟨⟨z', lt_of_lit listed'⟩, listed', related⟩
  · obtain ⟨z, listed, related⟩ := back ⟨z', lt_of_lit listed⟩ listed
    exact ⟨z, listed, related⟩
  · intro listed
    obtain ⟨z, listed', related⟩ := back z' listed
    exact ⟨⟨z, lt_of_lit listed'⟩, listed', related⟩

theorem same_mono {x y : ℕ} {u w : S.World} (related : S.same x y u) (later : S.le u w) : S.same x y w :=
  same_iff.mpr fun v later' => same_iff.mp related v (S.le_trans later later')

theorem same_refl (x : ℕ) (w : S.World) : S.same x x w := by
  induction x using Nat.strong_induction_on generalizing w with
  | _ x ih =>
    refine same_iff.mpr fun v _ => ⟨fun z listed => ⟨z, listed, ih z (lt_of_lit listed) v⟩,
      fun z listed => ⟨z, listed, ih z (lt_of_lit listed) v⟩⟩

theorem same_symm {x y : ℕ} {w : S.World} (related : S.same x y w) : S.same y x w := by
  induction hSum : x + y using Nat.strong_induction_on generalizing x y w with
  | _ n ih =>
    refine same_iff.mpr fun v later => ?_
    obtain ⟨forth, back⟩ := same_iff.mp related v later
    refine ⟨fun z' listed => ?_, fun z listed => ?_⟩
    · obtain ⟨z, listed', related'⟩ := back z' listed
      exact ⟨z, listed', ih (z + z') (by have := lt_of_lit listed; have := lt_of_lit listed'; omega) related' rfl⟩
    · obtain ⟨z', listed', related'⟩ := forth z listed
      exact ⟨z', listed', ih (z + z') (by have := lt_of_lit listed; have := lt_of_lit listed'; omega) related' rfl⟩

theorem same_trans {x y t : ℕ} {w : S.World} (first : S.same x y w) (second : S.same y t w) : S.same x t w := by
  induction hSum : x + y + t using Nat.strong_induction_on generalizing x y t w with
  | _ n ih =>
    refine same_iff.mpr fun v later => ?_
    obtain ⟨forth, back⟩ := same_iff.mp first v later
    obtain ⟨forth', back'⟩ := same_iff.mp second v later
    refine ⟨fun z listed => ?_, fun z'' listed => ?_⟩
    · obtain ⟨z', listed', related⟩ := forth z listed
      obtain ⟨z'', listed'', related'⟩ := forth' z' listed'
      exact ⟨z'', listed'', ih (z + z' + z'')
        (by have := lt_of_lit listed; have := lt_of_lit listed'; have := lt_of_lit listed''; omega)
        related related' rfl⟩
    · obtain ⟨z', listed', related'⟩ := back' z'' listed
      obtain ⟨z, listed'', related⟩ := back z' listed'
      exact ⟨z, listed'', ih (z + z' + z'')
        (by have := lt_of_lit listed; have := lt_of_lit listed'; have := lt_of_lit listed''; omega)
        related related' rfl⟩

/-- **Membership**: being equal to a listed member. -/
def mem (S : Stages) (w : S.World) (z x : ℕ) : Prop := ∃ z', S.lit w z' x ∧ S.same z z' w

theorem mem_mono {v w : S.World} (later : S.le v w) {z x : ℕ} (held : S.mem v z x) : S.mem w z x := by
  obtain ⟨z', listed, related⟩ := held
  exact ⟨z', lit_mono later listed, same_mono related later⟩

theorem mem_of_lit {w : S.World} {z x : ℕ} (listed : S.lit w z x) : S.mem w z x := ⟨z, listed, same_refl z w⟩

/-- Membership respects equality of the member. -/
theorem mem_of_same_left {w : S.World} {z z' x : ℕ} (related : S.same z z' w) (held : S.mem w z x) :
    S.mem w z' x := by
  obtain ⟨z'', listed, related'⟩ := held
  exact ⟨z'', listed, same_trans (same_symm related) related'⟩

/-- Membership respects equality of the set. -/
theorem mem_of_same_right {w : S.World} {z x y : ℕ} (related : S.same x y w) (held : S.mem w z x) :
    S.mem w z y := by
  obtain ⟨z', listed, related'⟩ := held
  obtain ⟨z'', listed', related''⟩ := (same_iff.mp related w (S.le_refl w)).1 z' listed
  exact ⟨z'', listed', same_trans related' related''⟩

/-- **Extensionality**: two sets are equal at a stage exactly when they have the same members at every later stage. -/
theorem same_iff_members {x y : ℕ} {w : S.World} :
    S.same x y w ↔ ∀ v, S.le w v → ∀ z, S.mem v z x ↔ S.mem v z y := by
  constructor
  · intro related v later z
    exact ⟨mem_of_same_right (same_mono related later), mem_of_same_right (same_symm (same_mono related later))⟩
  · intro members
    refine same_iff.mpr fun v later => ⟨fun z listed => ?_, fun z' listed => ?_⟩
    · obtain ⟨z', listed', related⟩ := (members v later z).mp (mem_of_lit listed)
      exact ⟨z', listed', related⟩
    · obtain ⟨z, listed', related⟩ := (members v later z').mpr (mem_of_lit listed)
      exact ⟨z, listed', same_symm related⟩

theorem not_lit_zero (w : S.World) (z : ℕ) : ¬ S.lit w z 0 := fun listed => absurd (lt_of_lit listed) (Nat.not_lt_zero z)

theorem not_mem_zero (w : S.World) (z : ℕ) : ¬ S.mem w z 0 := fun ⟨_, listed, _⟩ => not_lit_zero w _ listed

/-- A listed member somewhere: a nonzero digit holds at some stage. -/
theorem exists_lit_of_digit_ne_zero {z x : ℕ} (nonzero : digit S.count x z ≠ 0) : ∃ w, S.lit w z x :=
  S.level_pos _ (Nat.pos_of_ne_zero nonzero) (digit_lt S.one_lt_count x z)

/-- The number listing each position below `bound` where `P z` holds. -/
noncomputable def collect (S : Stages) (bound : ℕ) (P : ℕ → S.World → Prop) : ℕ :=
  build S.count bound fun z => S.levelOf (P z)

theorem lit_collect {bound : ℕ} {P : ℕ → S.World → Prop} (up : ∀ z, S.Upward (P z))
    (vanish : ∀ z, bound ≤ z → ∀ w, ¬ P z w) (w : S.World) (z : ℕ) : S.lit w z (S.collect bound P) ↔ P z w := by
  unfold lit collect
  rw [digit_build_eq S.one_lt_count (fun z => levelOf_lt _) (fun z beyond => levelOf_eq_zero (vanish z beyond))]
  exact level_levelOf (up z) w

/-! ## The operations -/

/-- **Separation**: the members of `x` listed where the predicate holds. -/
noncomputable def sep (S : Stages) (x : ℕ) (p : ℕ → S.World → Prop) : ℕ :=
  S.collect x fun z w => S.lit w z x ∧ p z w

/-- A predicate on sets: upward closed, and the same at equal sets. -/
structure Predicate (p : ℕ → S.World → Prop) : Prop where
  up : ∀ z, S.Upward (p z)
  respects : ∀ {z z' : ℕ} {w : S.World}, S.same z z' w → (p z w ↔ p z' w)

theorem lit_sep {x : ℕ} {p : ℕ → S.World → Prop} (up : ∀ z, S.Upward (p z)) (w : S.World) (z : ℕ) :
    S.lit w z (S.sep x p) ↔ S.lit w z x ∧ p z w :=
  lit_collect (fun z _ _ later held => ⟨lit_mono later held.1, up z later held.2⟩)
    (fun _ beyond _ held => absurd (lt_of_lit held.1) (Nat.not_lt.mpr beyond)) w z

theorem mem_sep {x : ℕ} {p : ℕ → S.World → Prop} (predicate : Predicate p) (w : S.World) (z : ℕ) :
    S.mem w z (S.sep x p) ↔ S.mem w z x ∧ p z w := by
  constructor
  · rintro ⟨z', listed, related⟩
    obtain ⟨inside, holds⟩ := (lit_sep predicate.up w z').mp listed
    exact ⟨⟨z', inside, related⟩, (predicate.respects related).mpr holds⟩
  · rintro ⟨⟨z', listed, related⟩, holds⟩
    exact ⟨z', (lit_sep predicate.up w z').mpr ⟨listed, (predicate.respects related).mp holds⟩, related⟩

/-- Membership in a set is a predicate. -/
theorem memPredicate (b : ℕ) : Predicate fun z w => S.mem w z b :=
  ⟨fun _ _ _ later held => mem_mono later held, fun related => ⟨mem_of_same_left related,
    mem_of_same_left (same_symm related)⟩⟩

/-- `c` lists only members listed in `x`, at every stage. -/
def Included (S : Stages) (c x : ℕ) : Prop := ∀ v z, S.lit v z c → S.lit v z x

/-- **The power set**: the sets listing only members listed in `x`. -/
noncomputable def pow (S : Stages) (x : ℕ) : ℕ := S.collect (S.count ^ x) fun c _ => S.Included c x

theorem lit_pow (x c : ℕ) (w : S.World) : S.lit w c (S.pow x) ↔ S.Included c x := by
  refine lit_collect (fun _ _ _ _ held => held) (fun c large _ included => ?_) w c
  obtain ⟨z, beyond, nonzero⟩ := exists_digit_of_pow_le S.one_lt_count large
  obtain ⟨v, listed⟩ := exists_lit_of_digit_ne_zero nonzero
  exact absurd (lt_of_lit (included v z listed)) (Nat.not_lt.mpr beyond)

theorem mem_pow (x y : ℕ) (w : S.World) :
    S.mem w y (S.pow x) ↔ ∀ v, S.le w v → ∀ z, S.mem v z y → S.mem v z x := by
  constructor
  · rintro ⟨c, listed, related⟩ v later z held
    obtain ⟨z', listed', related'⟩ := mem_of_same_right (same_mono related later) held
    exact ⟨z', (lit_pow x c w).mp listed v z' listed', related'⟩
  · intro included
    let c := S.sep x fun z v => S.mem v z y
    refine ⟨c, (lit_pow x c w).mpr fun v z listed => ((lit_sep (memPredicate y).up v z).mp listed).1,
      same_iff_members.mpr fun v later z => ?_⟩
    rw [mem_sep (memPredicate y)]
    exact ⟨fun held => ⟨included v later z held, held⟩, fun held => held.2⟩

/-- **The union** of the listed members' listed members. -/
noncomputable def union (S : Stages) (x : ℕ) : ℕ := S.collect x fun z w => ∃ y, S.lit w y x ∧ S.lit w z y

theorem lit_union (x : ℕ) (w : S.World) (z : ℕ) : S.lit w z (S.union x) ↔ ∃ y, S.lit w y x ∧ S.lit w z y :=
  lit_collect (fun _ _ _ later ⟨y, inside, listed⟩ => ⟨y, lit_mono later inside, lit_mono later listed⟩)
    (fun _ beyond _ ⟨_, inside, listed⟩ =>
      absurd (lt_trans (lt_of_lit listed) (lt_of_lit inside)) (Nat.not_lt.mpr beyond)) w z

theorem mem_union (x : ℕ) (w : S.World) (z : ℕ) : S.mem w z (S.union x) ↔ ∃ y, S.mem w y x ∧ S.mem w z y := by
  constructor
  · rintro ⟨z', listed, related⟩
    obtain ⟨y, inside, listed'⟩ := (lit_union x w z').mp listed
    exact ⟨y, mem_of_lit inside, z', listed', related⟩
  · rintro ⟨y, ⟨y', inside, relatedY⟩, member, listed, relatedZ⟩
    obtain ⟨image, listed', related⟩ := (same_iff.mp relatedY w (S.le_refl w)).1 member listed
    exact ⟨image, (lit_union x w image).mpr ⟨y', inside, listed'⟩, same_trans relatedZ related⟩

/-- **The image** of the listed members. -/
noncomputable def replace (S : Stages) (x : ℕ) (f : ℕ → ℕ) : ℕ :=
  S.collect ((Finset.range x).sup f + 1) fun z w => ∃ y, S.lit w y x ∧ f y = z

theorem lit_replace (x : ℕ) (f : ℕ → ℕ) (w : S.World) (z : ℕ) :
    S.lit w z (S.replace x f) ↔ ∃ y, S.lit w y x ∧ f y = z := by
  refine lit_collect (fun _ _ _ later ⟨y, inside, image⟩ => ⟨y, lit_mono later inside, image⟩)
    (fun z beyond _ ⟨y, inside, image⟩ => ?_) w z
  have bounded : f y ≤ (Finset.range x).sup f := Finset.le_sup (Finset.mem_range.mpr (lt_of_lit inside))
  omega

/-- A function on sets: the same at equal sets. -/
def Respects (S : Stages) (f : ℕ → ℕ) : Prop := ∀ {y y' : ℕ} {w : S.World}, S.same y y' w → S.same (f y) (f y') w

theorem mem_replace {x : ℕ} {f : ℕ → ℕ} (respects : S.Respects f) (w : S.World) (z : ℕ) :
    S.mem w z (S.replace x f) ↔ ∃ y, S.mem w y x ∧ S.same (f y) z w := by
  constructor
  · rintro ⟨z', listed, related⟩
    obtain ⟨y, inside, rfl⟩ := (lit_replace x f w z').mp listed
    exact ⟨y, mem_of_lit inside, same_symm related⟩
  · rintro ⟨y, ⟨y', inside, relatedY⟩, relatedZ⟩
    exact ⟨f y', (lit_replace x f w _).mpr ⟨y', inside, rfl⟩,
      same_trans (same_symm relatedZ) (respects relatedY)⟩

/-! ## The operations respect equality -/

theorem sep_same_set {x x' : ℕ} {p : ℕ → S.World → Prop} (predicate : Predicate p) {w : S.World}
    (related : S.same x x' w) : S.same (S.sep x p) (S.sep x' p) w :=
  same_iff_members.mpr fun v later z => by
    rw [mem_sep predicate, mem_sep predicate]
    exact and_congr_left fun _ => ⟨mem_of_same_right (same_mono related later),
      mem_of_same_right (same_symm (same_mono related later))⟩

theorem sep_same_predicate {x : ℕ} {p q : ℕ → S.World → Prop} (first : Predicate p) (second : Predicate q)
    {w : S.World} (agree : ∀ v, S.le w v → ∀ z, p z v ↔ q z v) : S.same (S.sep x p) (S.sep x q) w :=
  same_iff_members.mpr fun v later z => by
    rw [mem_sep first, mem_sep second]
    exact and_congr_right fun _ => agree v later z

theorem pow_same {x x' : ℕ} {w : S.World} (related : S.same x x' w) : S.same (S.pow x) (S.pow x') w :=
  same_iff_members.mpr fun v later y => by
    rw [mem_pow, mem_pow]
    have members := same_iff_members.mp related
    exact ⟨fun included u later' z held => (members u (S.le_trans later later') z).mp (included u later' z held),
      fun included u later' z held => (members u (S.le_trans later later') z).mpr (included u later' z held)⟩

theorem union_same {x x' : ℕ} {w : S.World} (related : S.same x x' w) : S.same (S.union x) (S.union x') w :=
  same_iff_members.mpr fun v later z => by
    rw [mem_union, mem_union]
    have members := same_iff_members.mp related v later
    exact exists_congr fun y => and_congr_left fun _ => members y

theorem replace_same_set {x x' : ℕ} {f : ℕ → ℕ} (respects : S.Respects f) {w : S.World}
    (related : S.same x x' w) : S.same (S.replace x f) (S.replace x' f) w :=
  same_iff_members.mpr fun v later z => by
    rw [mem_replace respects, mem_replace respects]
    have members := same_iff_members.mp related v later
    exact exists_congr fun y => and_congr_left fun _ => members y

theorem replace_same_function {x : ℕ} {f g : ℕ → ℕ} (first : S.Respects f) (second : S.Respects g) {w : S.World}
    (agree : ∀ v, S.le w v → ∀ y, S.same (f y) (g y) v) : S.same (S.replace x f) (S.replace x g) w :=
  same_iff_members.mpr fun v later z => by
    rw [mem_replace first, mem_replace second]
    exact exists_congr fun y => and_congr_right fun _ =>
      ⟨fun related => same_trans (same_symm (agree v later y)) related,
        fun related => same_trans (agree v later y) related⟩

end Stages

/-! ## The Kripke–Henkin model -/

section Model

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol member separate replace iffFormula unionLaw
  replacementLaw setInduction extensionality)

variable (S : Stages)

/-- **The frame of a listing**: sets as numbers, equal at a stage as `same` says. -/
def frame : KripkeFrameModel.Frame.{0, 0} Unit where
  World := S.World
  le := S.le
  le_refl := S.le_refl
  le_trans := S.le_trans
  Carrier _ := ℕ
  baseEq w _ x y := S.same x y w
  baseEq_mono later related := Stages.same_mono related later
  baseEq_refl w _ x := Stages.same_refl x w
  baseEq_symm related := Stages.same_symm related
  baseEq_trans first second := Stages.same_trans first second

/-- The symbols, read on these sets. -/
noncomputable def denoteSymbol : {τ : Ty Unit} → Symbol τ → (frame S).Val τ
  | _, .member => fun (z x : ℕ) (w : S.World) => S.mem w z x
  | _, .empty => (0 : ℕ)
  | _, .union => S.union
  | _, .power => S.pow
  | _, .separate => fun (x : ℕ) (p : ℕ → S.World → Prop) => S.sep x p
  | _, .replace => fun (x : ℕ) (f : ℕ → ℕ) => S.replace x f

variable {S}

/-- An admissible predicate is a predicate on sets. -/
theorem predicate_of_adm {p : (frame S).Val (.arr (.base ()) .prop)} (admissible : (frame S).Adm _ p) :
    Stages.Predicate p :=
  ⟨fun z => admissible.1 z trivial, fun {z z' w} related =>
    admissible.2 w z z' trivial trivial related w (S.le_refl w)⟩

/-- An admissible function respects equality. -/
theorem respects_of_adm {f : (frame S).Val (.arr (.base ()) (.base ()))} (admissible : (frame S).Adm _ f) :
    S.Respects f :=
  fun related => admissible.2 _ _ _ trivial trivial related

variable (S)

/-- **Every symbol denotes an admissible value**: membership is upward closed and respects equality on both sides,
and the operations respect equality. -/
theorem constAdm : ∀ {τ : Ty Unit} (c : Symbol τ), (frame S).Adm τ (denoteSymbol S c)
  | _, .member => by
    refine ⟨fun z _ => ⟨fun x _ => ?_, fun W x x' _ _ related => ?_⟩, fun W z z' _ _ related => ?_⟩
    · exact fun later held => Stages.mem_mono later held
    · intro V later
      exact ⟨Stages.mem_of_same_right (Stages.same_mono related later),
        Stages.mem_of_same_right (Stages.same_symm (Stages.same_mono related later))⟩
    · intro V later x _ V' later'
      have related' := Stages.same_mono related (S.le_trans later later')
      exact ⟨Stages.mem_of_same_left related', Stages.mem_of_same_left (Stages.same_symm related')⟩
  | _, .empty => trivial
  | _, .union => ⟨fun _ _ => trivial, fun _ _ _ _ _ related => Stages.union_same related⟩
  | _, .power => ⟨fun _ _ => trivial, fun _ _ _ _ _ related => Stages.pow_same related⟩
  | _, .separate => by
    refine ⟨fun x _ => ⟨fun _ _ => trivial, fun W p q pAdmissible qAdmissible related => ?_⟩,
      fun W x x' _ _ related => ?_⟩
    · exact Stages.sep_same_predicate (predicate_of_adm pAdmissible) (predicate_of_adm qAdmissible)
        fun v later z => related v later z trivial v (S.le_refl v)
    · intro V later p pAdmissible
      exact Stages.sep_same_set (predicate_of_adm pAdmissible) (Stages.same_mono related later)
  | _, .replace => by
    refine ⟨fun x _ => ⟨fun _ _ => trivial, fun W f g fAdmissible gAdmissible related => ?_⟩,
      fun W x x' _ _ related => ?_⟩
    · exact Stages.replace_same_function (respects_of_adm fAdmissible) (respects_of_adm gAdmissible)
        fun v later y => related v later y trivial
    · intro V later f fAdmissible
      exact Stages.replace_same_set (respects_of_adm fAdmissible) (Stages.same_mono related later)

/-- **The Kripke–Henkin model of the sets of a listing.** -/
noncomputable def model : KripkeHenkinGeneral.{0, 0, 0} Unit Symbol :=
  KripkeFrameModel.model (frame S) (denoteSymbol S) (constAdm S)

end Model

/-! ## The laws hold -/

section Laws

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol unionLaw replacementLaw setInduction
  extensionality)

variable (S : Stages)

/-- **Equal sets are indiscernible**: `∀ x y. x = y → ∀ P. P x → P y`. -/
def leibnizLaw : ClosedFormula Symbol :=
  .all (.all (.imp (.eq (.var (.vs .vz)) (.var .vz))
    (.all (σ := .arr (.base ()) .prop) (.imp (.app (.var .vz) (.var (.vs (.vs .vz)))) (.app (.var .vz) (.var (.vs .vz)))))))

/-- The laws these models satisfy: the empty set, the power set, separation, union, replacement, induction along
membership, extensionality, and the indiscernibility of equal sets. -/
def extensionalLaws : List (ClosedFormula Symbol) :=
  [lawEmpty, lawPower, lawSeparation, unionLaw, replacementLaw, setInduction, extensionality, leibnizLaw]

theorem lawEmpty_holds (W : S.World) : (model S).denote lawEmpty (model S).emptyVal W := by
  intro V _ d dAdmissible
  exact ((model S).denote_negation _ ((model S).toKripkePreModel.extend_adm ((model S).emptyVal_adm V) dAdmissible)).mpr
    fun V' _ held => Stages.not_mem_zero V' d held

theorem lawPower_holds (W : S.World) : (model S).denote lawPower (model S).emptyVal W := by
  intro V _ a aAdmissible V' _ b bAdmissible
  refine ((model S).denote_conjunctionFormula _ _ ((model S).toKripkePreModel.extend_adm
    ((model S).toKripkePreModel.extend_adm ((model S).emptyVal_adm V') aAdmissible) bAdmissible)).mpr
    ⟨fun U _ held => ?_, fun U _ held => ?_⟩
  · intro U' later z _ U'' later' inside
    exact (Stages.mem_pow a b U).mp held U'' (S.le_trans later later') z inside
  · exact (Stages.mem_pow a b U).mpr fun v later z inside => held v later z trivial v (S.le_refl v) inside

theorem lawSeparation_holds (W : S.World) : (model S).denote lawSeparation (model S).emptyVal W := by
  intro V _ a aAdmissible V' _ p pAdmissible V'' _ z zAdmissible
  have predicate : Stages.Predicate p := predicate_of_adm pAdmissible
  have admissible : ∀ U : S.World, (model S).ValuationAdm U
      ((model S).extend ((model S).extend ((model S).extend (model S).emptyVal a) p) z) := fun U =>
    (model S).toKripkePreModel.extend_adm ((model S).toKripkePreModel.extend_adm
      ((model S).toKripkePreModel.extend_adm ((model S).emptyVal_adm U) aAdmissible) pAdmissible) zAdmissible
  refine ((model S).denote_conjunctionFormula _ _ (admissible V'')).mpr ⟨fun U _ held => ?_, fun U _ held => ?_⟩
  · exact ((model S).denote_conjunctionFormula _ _ (admissible U)).mpr ((Stages.mem_sep predicate U z).mp held)
  · exact (Stages.mem_sep predicate U z).mpr (((model S).denote_conjunctionFormula _ _ (admissible U)).mp held)

theorem unionLaw_holds (W : S.World) : (model S).denote unionLaw (model S).emptyVal W := by
  intro V _ a _ V' _ z _
  constructor
  · intro U _ held
    obtain ⟨y, inside, member⟩ := (Stages.mem_union a U z).mp held
    exact ⟨y, trivial, inside, member⟩
  · rintro U _ ⟨y, _, inside, member⟩
    exact (Stages.mem_union a U z).mpr ⟨y, inside, member⟩

theorem replacementLaw_holds (W : S.World) : (model S).denote replacementLaw (model S).emptyVal W := by
  intro V _ a _ V' _ f fAdmissible V'' _ z _
  have respects : S.Respects f := respects_of_adm fAdmissible
  constructor
  · intro U _ held
    obtain ⟨y, inside, image⟩ := (Stages.mem_replace respects U z).mp held
    exact ⟨y, trivial, inside, image⟩
  · rintro U _ ⟨y, _, inside, image⟩
    exact (Stages.mem_replace respects U z).mpr ⟨y, inside, image⟩

/-- **Induction along membership**, for every admissible predicate: a listed member lies below its set. -/
theorem setInduction_holds (W : S.World) : (model S).denote setInduction (model S).emptyVal W := by
  intro V _ P PAdmissible V' _ step V'' later x _
  have predicate : Stages.Predicate P := predicate_of_adm PAdmissible
  clear * - predicate step later
  induction x using Nat.strong_induction_on generalizing V'' with
  | _ x ih =>
    refine step V'' later x trivial V'' (S.le_refl V'') ?_
    rintro U later' y _ U' later'' ⟨y', listed, related⟩
    exact (predicate.respects related).mpr
      (ih y' (Stages.lt_of_lit listed) U' (S.le_trans later (S.le_trans later' later'')))

/-- **Extensionality**: sets with the same members at every later stage are equal. -/
theorem extensionality_holds (W : S.World) : (model S).denote extensionality (model S).emptyVal W := by
  intro V _ x _ V' _ y _ U _ members
  exact Stages.same_iff_members.mpr fun v later z =>
    ⟨(members v later z trivial).1 v (S.le_refl v), (members v later z trivial).2 v (S.le_refl v)⟩

/-- **Equal sets are indiscernible** by every admissible predicate. -/
theorem leibnizLaw_holds (W : S.World) : (model S).denote leibnizLaw (model S).emptyVal W := by
  intro V _ x _ V' _ y _ U _ related U' later P PAdmissible U'' later' held
  exact ((predicate_of_adm PAdmissible).respects (Stages.same_mono related (S.le_trans later later'))).mp held

theorem extensionalLaws_hold (W : S.World) : ∀ δ ∈ extensionalLaws, (model S).denote δ (model S).emptyVal W := by
  intro δ listed
  simp only [extensionalLaws, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lawEmpty_holds S W
  · exact lawPower_holds S W
  · exact lawSeparation_holds S W
  · exact unionLaw_holds S W
  · exact replacementLaw_holds S W
  · exact setInduction_holds S W
  · exact extensionality_holds S W
  · exact leibnizLaw_holds S W

/-- **Soundness for closed proofs** of the checker: a proof from hypotheses that hold at a stage proves a formula
holding there. -/
theorem sound {Δ : List (ClosedFormula Symbol)} {φ : ClosedFormula Symbol} (proof : Proof Δ φ) (W : S.World)
    (hyps : ∀ δ ∈ Δ, (model S).denote δ (model S).emptyVal W) : (model S).denote φ (model S).emptyVal W :=
  (model S).proofSyntaxModulo_sound_closed (fun _ listed => absurd listed List.not_mem_nil) proof W hyps

end Laws

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings.KripkeSets
