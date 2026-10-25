import Mettapedia.Algebra.Order.Infinitesimal.LevelField
import Mathlib.Data.List.Sort

/-!
# Canonical finite presentations in the level field

`LevelField` is a `HahnSeries`, which stores a coefficient *function* and is
therefore noncomputable.  This module supplies the finite data a program can
actually hold — a list of level/coefficient pairs — together with arithmetic
that runs, and proves the list denotes what the arithmetic says it does.

The design keeps two things apart that are easy to conflate.

* **Denotation** (`toHahn`) is defined on *arbitrary* lists, with no invariant:
  a list denotes the sum of its terms.  Repeated levels and zero coefficients
  are allowed and denote exactly what they should.  This is what makes the
  homomorphism theorems clean — `add` is list append, and
  `toHahn_append` is `List.sum_append`.
* **Canonical form** (`norm`) is a separate operation that merges repeated
  levels, drops zero coefficients and sorts.  `toHahn_norm` proves it changes
  no numerical value, although it can change order and occurrence observations.

Multiplication is the pairwise product of terms, and `toHahn_mul` proves it is
the field's multiplication.  Nothing here uses the order, so nothing here has
to be re-proved when the order is brought in.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Order.Infinitesimal

open HahnSeries

/-- A term: a coefficient at a level. -/
abbrev Term : Type := ℤ × ℚ

/-- The finite data a program holds. -/
abbrev LevelSeries : Type := List Term

namespace LevelSeries

/-! ## Denotation -/

/-- What a list of terms denotes: the sum of its terms. -/
noncomputable def toHahn (l : LevelSeries) : HahnSeries ℤ ℚ :=
  (l.map fun t => single t.1 t.2).sum

/-- Its image in the ordered field. -/
noncomputable def toLevelField (l : LevelSeries) : LevelField := toLex (toHahn l)

@[simp] theorem toHahn_nil : toHahn [] = 0 := rfl

@[simp] theorem toHahn_cons (t : Term) (l : LevelSeries) :
    toHahn (t :: l) = single t.1 t.2 + toHahn l := by
  simp [toHahn]

/-! ## Addition is append -/

/-- Addition: concatenate the terms. -/
def add (p q : LevelSeries) : LevelSeries := p ++ q

@[simp] theorem toHahn_append (p q : LevelSeries) :
    toHahn (p ++ q) = toHahn p + toHahn q := by
  simp [toHahn, List.map_append, List.sum_append]

/-- **Addition is the field's addition.** -/
theorem toHahn_add (p q : LevelSeries) : toHahn (add p q) = toHahn p + toHahn q :=
  toHahn_append p q

/-! ## Negation -/

/-- Negation: negate every coefficient. -/
def neg (p : LevelSeries) : LevelSeries := p.map fun t => (t.1, -t.2)

/-- **Negation is the field's negation.** -/
theorem toHahn_neg (p : LevelSeries) : toHahn (neg p) = - toHahn p := by
  simp [neg, toHahn, List.map_map, Function.comp_def, single_neg, List.sum_neg]

/-- Subtraction. -/
def sub (p q : LevelSeries) : LevelSeries := add p (neg q)

theorem toHahn_sub (p q : LevelSeries) : toHahn (sub p q) = toHahn p - toHahn q := by
  rw [sub, toHahn_add, toHahn_neg, sub_eq_add_neg]

/-! ## Multiplication -/

/-- One term against a whole series. -/
def scaleTerm (t : Term) (q : LevelSeries) : LevelSeries :=
  q.map fun u => (t.1 + u.1, t.2 * u.2)

theorem toHahn_scaleTerm (t : Term) (q : LevelSeries) :
    toHahn (scaleTerm t q) = single t.1 t.2 * toHahn q := by
  simpa only [scaleTerm, toHahn, List.map_map, Function.comp_def, single_mul_single] using
    List.sum_map_mul_left q (fun u => single u.1 u.2) (single t.1 t.2)

/-- Multiplication: every term against every term. -/
def mul (p q : LevelSeries) : LevelSeries :=
  p.flatMap fun t => scaleTerm t q

/-- **Multiplication is the field's multiplication.** -/
theorem toHahn_mul (p q : LevelSeries) : toHahn (mul p q) = toHahn p * toHahn q := by
  induction p with
  | nil => simp [mul]
  | cons t l ih =>
      simp only [mul, List.flatMap_cons] at *
      rw [toHahn_append, toHahn_scaleTerm, ih, toHahn_cons, add_mul]

/-! ## The generators, as data -/

/-- `1`, as a one-term list. -/
def one : LevelSeries := [(0, 1)]

/-- `Ω`, as a one-term list. -/
def omega : LevelSeries := [(-1, 1)]

/-- `Ω⁻¹`, as a one-term list. -/
def omegaInv : LevelSeries := [(1, 1)]

/-- A rational, as a one-term list. -/
def ofRat (q : ℚ) : LevelSeries := [(0, q)]

@[simp] theorem toHahn_one : toHahn one = 1 := by
  simp [one, toHahn]

theorem toLevelField_omega : toLevelField omega = Om := by
  simp [toLevelField, toHahn, omega, Om]

theorem toLevelField_omegaInv : toLevelField omegaInv = omInv := by
  simp [toLevelField, toHahn, omegaInv, omInv]

/-- **The executable product of the two generators is one**, and it computes:
`mul omega omegaInv` reduces to `[(0, 1)]`. -/
theorem mul_omega_omegaInv : mul omega omegaInv = one := by
  norm_num [mul, omega, omegaInv, one, scaleTerm]

/-- And the denotation agrees with the field law proved in `LevelField`. -/
theorem toLevelField_mul_omega_omegaInv :
    toLevelField (mul omega omegaInv) = 1 := by
  rw [mul_omega_omegaInv, toLevelField, toHahn_one]
  rfl

/-! ## Canonical form

Merging repeated levels, dropping zero coefficients and sorting is an
optimisation: `toHahn_norm` proves it preserves the denotation exactly, so a
program may canonicalise whenever it likes and never at the cost of meaning. -/

/-- Insert one term into a list kept sorted by level, merging on collision and
dropping a coefficient that cancels. -/
def insertTerm (t : Term) : LevelSeries → LevelSeries
  | [] => if t.2 = 0 then [] else [t]
  | u :: rest =>
      if t.1 = u.1 then
        (if t.2 + u.2 = 0 then rest else (t.1, t.2 + u.2) :: rest)
      else if t.1 < u.1 then
        (if t.2 = 0 then u :: rest else t :: u :: rest)
      else u :: insertTerm t rest

/-- Canonical form. -/
def norm : LevelSeries → LevelSeries
  | [] => []
  | t :: rest => insertTerm t (norm rest)

theorem toHahn_insertTerm (t : Term) (l : LevelSeries) :
    toHahn (insertTerm t l) = single t.1 t.2 + toHahn l := by
  induction l with
  | nil => by_cases zero : t.2 = 0 <;> simp [insertTerm, zero, toHahn]
  | cons u rest ih =>
      rw [insertTerm]
      split_ifs with same cancel before zero
      · rw [toHahn_cons, ← add_assoc, same, ← single_add, cancel, single_eq_zero, zero_add]
      · simp only [toHahn_cons, same, single_add]
        abel
      · simp [toHahn_cons, zero]
      · exact toHahn_cons _ _
      · rw [toHahn_cons, ih, toHahn_cons, add_left_comm]

/-- **Canonicalisation preserves the value.** -/
theorem toHahn_norm (l : LevelSeries) : toHahn (norm l) = toHahn l := by
  induction l with
  | nil => rfl
  | cons t rest ih => rw [norm, toHahn_insertTerm, ih, toHahn_cons]

theorem toLevelField_norm (l : LevelSeries) :
    toLevelField (norm l) = toLevelField l := by
  rw [toLevelField, toLevelField, toHahn_norm]

/-! ## Canonical form is genuinely canonical

`norm` produces a list whose levels strictly increase and whose coefficients
are all nonzero.  That is what lets the sign be read straight off the head: the
head sits at the lowest level, hence the largest magnitude. -/

/-- The head's level is strictly below every later level. -/
def Sorted : LevelSeries → Prop
  | [] => True
  | t :: rest => (∀ u ∈ rest, t.1 < u.1) ∧ Sorted rest

/-- No term carries a zero coefficient. -/
def NoZero (l : LevelSeries) : Prop := ∀ t ∈ l, t.2 ≠ 0

@[simp] theorem noZero_cons (t : Term) (rest : LevelSeries) :
    NoZero (t :: rest) ↔ t.2 ≠ 0 ∧ NoZero rest := by simp [NoZero]

/-- Canonical: sorted, with no vanishing term. -/
def Normalized (l : LevelSeries) : Prop := Sorted l ∧ NoZero l

/-- Inserting can introduce a term only at the inserted level. -/
theorem mem_insertTerm_level {t v : Term} : ∀ {l : LevelSeries}, v ∈ insertTerm t l →
    v.1 = t.1 ∨ v ∈ l := by
  intro l member
  fun_induction insertTerm t l <;> simp_all
  all_goals grind

theorem sorted_insertTerm (t : Term) : ∀ {l : LevelSeries}, Sorted l →
    Sorted (insertTerm t l) := by
  intro l sorted
  fun_induction insertTerm t l <;> simp_all [Sorted] <;> try grind
  intro i c member
  rcases mem_insertTerm_level (t := t) (v := (i, c)) member with level | earlier
  · omega
  · exact sorted.1 i c earlier

theorem noZero_insertTerm (t : Term) : ∀ {l : LevelSeries}, NoZero l →
    NoZero (insertTerm t l) := by
  intro l nonzero
  fun_induction insertTerm t l <;> simp_all only [noZero_cons] <;> simp_all [NoZero]

/-- **`norm` is canonical.** -/
theorem normalized_norm : ∀ l : LevelSeries, Normalized (norm l)
  | [] => ⟨trivial, by simp [NoZero, norm]⟩
  | t :: rest => by
      obtain ⟨hs, hz⟩ := normalized_norm rest
      exact ⟨sorted_insertTerm t hs, noZero_insertTerm t hz⟩

/-! ## Reading the sign off the head -/

/-- A coefficient vanishes when no raw term occurs at that level. -/
theorem coeff_toHahn_of_not_levels {j : ℤ} {l : LevelSeries}
    (absent : ∀ t ∈ l, j ≠ t.1) : (toHahn l).coeff j = 0 := by
  induction l with
  | nil => simp
  | cons t rest ih =>
      rw [toHahn_cons, coeff_add, coeff_single_of_ne (absent t List.mem_cons_self),
        ih (fun u member => absent u (List.mem_cons_of_mem t member)), add_zero]

theorem coeff_toHahn_of_all_gt {j : ℤ} {l : LevelSeries}
    (above : ∀ u ∈ l, j < u.1) : (toHahn l).coeff j = 0 :=
  coeff_toHahn_of_not_levels (fun u member => ne_of_lt (above u member))

theorem coeff_toHahn_head {i : ℤ} {a : ℚ} {rest : LevelSeries}
    (hs : Sorted ((i, a) :: rest)) : (toHahn ((i, a) :: rest)).coeff i = a := by
  rw [toHahn_cons, coeff_add, coeff_single_same,
    coeff_toHahn_of_all_gt (fun u hu => hs.1 u hu), add_zero]

theorem coeff_toHahn_lt_head {i j : ℤ} {a : ℚ} {rest : LevelSeries}
    (hs : Sorted ((i, a) :: rest)) (hj : j < i) :
    (toHahn ((i, a) :: rest)).coeff j = 0 :=
  coeff_toHahn_of_all_gt (by
    intro u hu
    rcases List.mem_cons.mp hu with rfl | hu'
    · exact hj
    · exact hj.trans (hs.1 u hu'))

theorem toLevelField_pos_of_head {i : ℤ} {a : ℚ} {rest : LevelSeries}
    (hs : Sorted ((i, a) :: rest)) (ha : 0 < a) :
    0 < toLevelField ((i, a) :: rest) := by
  refine ⟨i, fun j hj => (coeff_toHahn_lt_head hs hj).symm, ?_⟩
  change (0 : ℚ) < (toHahn ((i, a) :: rest)).coeff i
  rwa [coeff_toHahn_head hs]

theorem toLevelField_neg_of_head {i : ℤ} {a : ℚ} {rest : LevelSeries}
    (hs : Sorted ((i, a) :: rest)) (ha : a < 0) :
    toLevelField ((i, a) :: rest) < 0 := by
  refine ⟨i, fun j hj => coeff_toHahn_lt_head hs hj, ?_⟩
  change (toHahn ((i, a) :: rest)).coeff i < (0 : ℚ)
  rwa [coeff_toHahn_head hs]

/-! ## Canonical presentations are their coefficient tables -/

/-- The recursive presentation invariant is Mathlib's pairwise level order. -/
theorem sorted_iff_pairwise (l : LevelSeries) :
    Sorted l ↔ l.Pairwise (fun t u => t.1 < u.1) := by
  induction l <;> simp_all [Sorted, List.pairwise_cons]

/-- At a retained level, a sorted list has exactly its stored coefficient. -/
theorem coeff_toHahn_of_mem {t : Term} {l : LevelSeries} (sorted : Sorted l) (member : t ∈ l) :
    (toHahn l).coeff t.1 = t.2 := by
  induction l with
  | nil => simp at member
  | cons u rest ih =>
      rcases List.mem_cons.mp member with rfl | member
      · exact coeff_toHahn_head sorted
      · rw [toHahn_cons, coeff_add, coeff_single_of_ne (ne_of_gt (sorted.1 t member)), zero_add]
        exact ih sorted.2 member

/-- A canonical list contains precisely the nonzero entries of its coefficient function. -/
theorem Normalized.mem_iff {l : LevelSeries} (normal : Normalized l) {t : Term} :
    t ∈ l ↔ (toHahn l).coeff t.1 = t.2 ∧ t.2 ≠ 0 := by
  refine ⟨fun member => ⟨coeff_toHahn_of_mem normal.1 member, normal.2 t member⟩, ?_⟩
  rintro ⟨coefficient, nonzero⟩
  by_contra absent
  apply nonzero
  refine coefficient.symm.trans (coeff_toHahn_of_not_levels ?_)
  intro u member level
  have same : t = u := Prod.ext level (by
    rw [← coeff_toHahn_of_mem normal.1 member, ← level]
    exact coefficient.symm)
  exact absent (same.symm ▸ member)

/-- Denotation is injective on canonical presentations, including their coefficients. -/
theorem Normalized.toHahn_injective {p q : LevelSeries} (first : Normalized p)
    (second : Normalized q) (same : toHahn p = toHahn q) : p = q := by
  let : Std.Antisymm (fun t u : Term => t.1 < u.1) := ⟨fun _ _ h k => (lt_asymm h k).elim⟩
  let : Std.Irrefl (fun t u : Term => t.1 < u.1) := ⟨fun _ => lt_irrefl _⟩
  apply List.Pairwise.eq_of_mem_iff ((sorted_iff_pairwise p).mp first.1)
    ((sorted_iff_pairwise q).mp second.1)
  intro t
  rw [first.mem_iff, second.mem_iff, same]

/-- Equality of normal forms is exactly equality of denotations. -/
theorem norm_eq_norm_iff (p q : LevelSeries) : norm p = norm q ↔ toHahn p = toHahn q :=
  ⟨fun equal => by simpa only [toHahn_norm] using congrArg toHahn equal,
    fun equal => (normalized_norm p).toHahn_injective (normalized_norm q)
      (by simpa only [toHahn_norm] using equal)⟩

@[simp] theorem norm_idempotent (p : LevelSeries) : norm (norm p) = norm p :=
  (norm_eq_norm_iff _ _).mpr (toHahn_norm p)

/-! ## Comparison

Comparison is by subtraction: canonicalise the difference and read the sign of
its head, which is its term of largest magnitude. -/

/-- The sign of a canonical series, read from its head. -/
def signOf : LevelSeries → Ordering
  | [] => .eq
  | (_, a) :: _ => if 0 < a then .gt else .lt

/-- Compare by canonicalising the difference. -/
def cmp (p q : LevelSeries) : Ordering := signOf (norm (sub p q))

/-- Executable strict order. -/
def lt (p q : LevelSeries) : Prop := cmp p q = .lt

instance (p q : LevelSeries) : Decidable (lt p q) := by
  unfold lt; infer_instance

/-- **The head's sign is the sign of the value.** -/
theorem signOf_eq_lt_iff {l : LevelSeries} (hn : Normalized l) :
    signOf l = .lt ↔ toLevelField l < 0 := by
  cases l with
  | nil => simp [signOf, toLevelField, toHahn]
  | cons t rest =>
      obtain ⟨i, a⟩ := t
      have hane : a ≠ 0 := hn.2 (i, a) List.mem_cons_self
      by_cases hpos : 0 < a
      · simp only [signOf, hpos, if_true, reduceCtorEq, false_iff, not_lt]
        exact (toLevelField_pos_of_head hn.1 hpos).le
      · have hneg : a < 0 := lt_of_le_of_ne (not_lt.mp hpos) hane
        simp only [signOf, hpos, if_false, true_iff]
        exact toLevelField_neg_of_head hn.1 hneg

/-- **The executable comparison agrees with the field order.**  Nothing about
the order was assumed of the representation: it is read off the canonical form
and matched against the order upstream already proved. -/
theorem toLevelField_sub (p q : LevelSeries) :
    toLevelField (sub p q) = toLevelField p - toLevelField q := by
  exact congrArg toLex (toHahn_sub p q)

theorem lt_iff_toLevelField_lt (p q : LevelSeries) :
    lt p q ↔ toLevelField p < toLevelField q := by
  rw [lt, cmp, signOf_eq_lt_iff (normalized_norm _), toLevelField_norm, toLevelField_sub]
  exact sub_neg

/-- Only the empty canonical presentation has equality as its sign. -/
theorem signOf_eq_eq_iff (l : LevelSeries) : signOf l = .eq ↔ l = [] := by
  cases l with
  | nil => simp [signOf]
  | cons t rest => simp only [signOf, List.cons_ne_nil, iff_false]; split_ifs <;> decide

/-- The equality outcome observes exact numerical equality. -/
theorem cmp_eq_iff (p q : LevelSeries) : cmp p q = .eq ↔ toLevelField p = toLevelField q := by
  rw [cmp, signOf_eq_eq_iff, show ([] : LevelSeries) = norm [] from rfl,
    norm_eq_norm_iff, toHahn_sub, toHahn_nil, sub_eq_zero]
  exact toLex.injective.eq_iff.symm

/-- The greater-than outcome observes the opposite strict field order. -/
theorem cmp_gt_iff (p q : LevelSeries) : cmp p q = .gt ↔ toLevelField q < toLevelField p := by
  have lower := lt_iff_toLevelField_lt p q
  have equal := cmp_eq_iff p q
  unfold lt at lower
  cases answer : cmp p q <;> simp_all only [reduceCtorEq, false_iff, true_iff, not_lt]
  · exact le_of_lt lower
  · exact lt_of_le_of_ne lower (Ne.symm equal)

/-! ## Controls: the arithmetic runs -/

/-- `Ω + Ω = 2Ω`, computed. -/
theorem two_omega : norm (add omega omega) = [(-1, 2)] := by
  norm_num [norm, insertTerm, add, omega]

/-- `Ω − Ω = 0`, computed: the cancellation is dropped, not carried. -/
theorem omega_sub_omega : norm (sub omega omega) = [] := by
  norm_num [norm, insertTerm, sub, add, neg, omega]

/-- `(Ω + 1)(Ω − 1) = Ω² − 1`, computed. -/
theorem difference_of_squares :
    norm (mul [(-1, 1), (0, 1)] [(-1, 1), (0, -1)]) = [(-2, 1), (0, -1)] := by
  norm_num [norm, insertTerm, mul, scaleTerm]

/-- The numerical observer forgets raw order, cancellation and invalid normal forms. -/
theorem raw_presentations_can_agree :
    norm [(0, 1), (0, -1)] = norm [] ∧ ¬ Normalized [(0, 1), (0, -1)] ∧
      ¬ Normalized [(0, 0)] := by norm_num [norm, insertTerm, Normalized, Sorted, NoZero]

theorem reordering_changes_presentation :
    norm [(1, 2), (0, 3)] = norm [(0, 3), (1, 2)] ∧
      ([(1, 2), (0, 3)] : LevelSeries) ≠ [(0, 3), (1, 2)] := by decide +kernel

theorem all_comparison_outcomes :
    cmp one omega = .lt ∧ cmp omega one = .gt ∧ cmp [(0, 1), (0, -1)] [] = .eq := by decide +kernel

/-- A multi-scale value: `3Ω − 5 + 2Ω⁻¹`, already canonical. -/
def sample : LevelSeries := [(-1, 3), (0, -5), (1, 2)]

theorem sample_norm : norm sample = sample := by
  norm_num [norm, insertTerm, sample]

end LevelSeries

end Mettapedia.Algebra.Order.Infinitesimal
