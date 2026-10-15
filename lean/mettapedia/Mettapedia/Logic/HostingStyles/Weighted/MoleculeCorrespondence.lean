import Mettapedia.Logic.HostingStyles.Weighted.Division
import Mettapedia.Logic.HostingStyles.Weighted.FibreSum
import Mettapedia.Logic.HostingStyles.Weighted.MoleculeSplit

/-!
# Weighted correspondence and locality of μ

Meredith, *Collision and Scattering for Process Molecules*, Theorem `thm:corr`,
Remark `rem:local`, and Finding `find:e1`.

Weighting each candidate of a fibre by a `Splits` quotient of `w` by `μ`
makes the fibre sum `w`. Weighting by the quotient of `w` by `k!` makes the
fibre sum `w` times `∏_a T_a`. That product is `2` at two messages, one atom,
and two roles with margins `(1, 1)` by `(1, 1)`, and it is never `2` for fewer
than two messages. `μ` depends on the messages and the outcome through their
atom counts.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Weighted

universe u

open scoped BigOperators

open Mettapedia.GSLT.Dynamics.JoinAggregation

variable {Atom : Type u} [DecidableEq Atom]

/-- The copies of one fibre: one index for each candidate, in the order of
`Fin`. -/
def fibreCopies {Role : Type*} [Fintype Role] [DecidableEq Role] {k : ℕ}
    (messages : Fin k → Message Atom) (outcome : Role → Message Atom) :
    List (Fin (fibreMultiplicity messages outcome)) :=
  List.ofFn id

/-- **Positive.** The collision fibre has two copies. -/
theorem collision_copies_length :
    (fibreCopies collisionMessages collisionOutcome).length = 2 := by
  rw [fibreCopies, List.length_ofFn, collision_mu_eq_twoBodyMultiplicity, twoBodyMultiplicity_eq]

/-- **Negative.** It does not have one copy. -/
theorem collision_copies_length_ne_one :
    (fibreCopies collisionMessages collisionOutcome).length ≠ 1 := by
  rw [collision_copies_length]
  decide

theorem constant_groupSum {K : Type*} [CommSemiring K] (n : ℕ) (w : K) :
    groupSum (fun _ : Fin n => ()) (fun _ => w) (List.ofFn id) () = (n : K) * w := by
  unfold groupSum
  have filtered :
      List.filter (fun _ : Fin n => () = ()) (List.ofFn id) = List.ofFn (id : Fin n → Fin n) := by
    refine List.filter_eq_self.mpr ?_
    intro _ _
    rfl
  rw [filtered]
  have mapped :
      (List.ofFn (id : Fin n → Fin n)).map (fun _ => w) = List.ofFn fun _ : Fin n => w := by
    rw [List.map_ofFn]
    rfl
  rw [mapped, List.sum_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **Positive.** `ℚ` splits the collision weight by `μ`. -/
theorem collision_rat_splits (w : ℚ) :
    Nonempty (Splits ℚ (fibreMultiplicity collisionMessages collisionOutcome) w) := by
  refine rat_splits _ ?_ w
  rw [collision_mu_eq_twoBodyMultiplicity, twoBodyMultiplicity_eq]
  decide

/-- **Negative.** `ℕ` does not split `1` by the collision multiplicity. -/
theorem collision_nat_no_split :
    ¬ Nonempty (Splits ℕ (fibreMultiplicity collisionMessages collisionOutcome) 1) := by
  intro h
  rw [collision_mu_eq_twoBodyMultiplicity, twoBodyMultiplicity_eq] at h
  exact nat_one_not_split_by_two h

/-- Weighting every candidate by the `Splits` quotient of `w` by `μ` makes the
fibre sum `w`. `Role` is finite and has decidable equality, `Atom` has
decidable equality, and `K` supplies the quotient, so `μ ≠ 0`. -/
theorem fibre_splits_preserves {K : Type*} [CommSemiring K] {Role : Type*} [Fintype Role]
    [DecidableEq Role] {k : ℕ} (messages : Fin k → Message Atom) (outcome : Role → Message Atom)
    (w : K) (split : Splits K (fibreMultiplicity messages outcome) w) :
    weightPreserving (fun _ : Unit => w)
      (fun _ : Fin (fibreMultiplicity messages outcome) => ()) (fun _ => split.quotient)
      (fibreCopies messages outcome) := by
  intro event
  cases event
  rw [fibreCopies, constant_groupSum, split.equation]

/-- Dividing `w` only by `k!` leaves the fibre sum equal to `w` times `∏_a T_a`. -/
theorem factorial_fibre_overcount {K : Type*} [CommSemiring K] {Role : Type*} [Fintype Role]
    [DecidableEq Role] {k : ℕ} (messages : Fin k → Message Atom) (outcome : Role → Message Atom)
    (w : K) (split : Splits K k.factorial w) :
    groupSum (fun _ : Fin (fibreMultiplicity messages outcome) => ()) (fun _ => split.quotient)
      (fibreCopies messages outcome) () = (orderingBlindCount messages outcome : K) * w := by
  rw [fibreCopies, constant_groupSum, fibreMultiplicity_eq_factorial_blind, Nat.cast_mul,
    mul_assoc, mul_left_comm, split.equation]

/-- Two messages, each one occurrence of the only atom. -/
def spreadMessages : Fin 2 → Message Unit :=
  fun _ => {()}

/-- **Positive.** Each spread message has one occurrence. -/
theorem spreadMessages_count (i : Fin 2) : Multiset.count () (spreadMessages i) = 1 := by
  rw [spreadMessages, message_singleton_count]

/-- **Negative.** A spread message is not empty. -/
theorem spreadMessages_ne_zero (i : Fin 2) : spreadMessages i ≠ 0 := by
  rw [spreadMessages]
  exact message_singleton_ne_zero ()

/-- Two roles, each receiving one occurrence. -/
def spreadOutcome : Fin 2 → Message Unit :=
  fun _ => {()}

/-- **Positive.** Each spread role has one occurrence. -/
theorem spreadOutcome_count (role : Fin 2) : Multiset.count () (spreadOutcome role) = 1 := by
  rw [spreadOutcome, message_singleton_count]

/-- **Negative.** A spread role does not have two occurrences. -/
theorem spreadOutcome_count_ne_two (role : Fin 2) :
    Multiset.count () (spreadOutcome role) ≠ 2 := by
  rw [spreadOutcome_count]
  decide

/-- The first row `(1, 0)` under column sums `(1, 1)`. -/
def spreadRow10 : FirstRow (Role := Fin 2) (fun _ => 1) 1 :=
  ⟨fun role => if role = 0 then 1 else 0,
    ⟨fun role => by
      cases role using Fin.cases with
      | zero => decide
      | succ r =>
        have hr : r = 0 := Subsingleton.elim r 0
        subst hr
        decide,
     by rw [sum_fin2]; decide⟩⟩

theorem spreadRow10_zero : spreadRow10.1 0 = 1 := by
  show (if (0 : Fin 2) = 0 then 1 else 0) = 1
  rw [if_pos rfl]

theorem spreadRow10_one : spreadRow10.1 1 = 0 := by
  show (if (1 : Fin 2) = 0 then 1 else 0) = 0
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- The first row `(0, 1)` under column sums `(1, 1)`. -/
def spreadRow01 : FirstRow (Role := Fin 2) (fun _ => 1) 1 :=
  ⟨fun role => if role = 0 then 0 else 1,
    ⟨fun role => by
      cases role using Fin.cases with
      | zero => decide
      | succ r =>
        have hr : r = 0 := Subsingleton.elim r 0
        subst hr
        decide,
     by rw [sum_fin2]; decide⟩⟩

theorem spreadRow01_zero : spreadRow01.1 0 = 0 := by
  show (if (0 : Fin 2) = 0 then 0 else 1) = 0
  rw [if_pos rfl]

theorem spreadRow01_one : spreadRow01.1 1 = 1 := by
  show (if (1 : Fin 2) = 0 then 0 else 1) = 1
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]

/-- **Negative.** The two first rows are distinct, so `T_a` is not `1`. -/
theorem spreadRow10_ne_01 : spreadRow10 ≠ spreadRow01 := by
  intro h
  have h0 := congrArg (fun x : FirstRow (fun _ : Fin 2 => 1) 1 => x.1 0) h
  rw [spreadRow10_zero, spreadRow01_zero] at h0
  exact absurd h0 (by decide)

theorem spread_row_dichotomy (x : FirstRow (Role := Fin 2) (fun _ => 1) 1) :
    x = spreadRow10 ∨ x = spreadRow01 := by
  have hx0 : x.1 0 = 0 ∨ x.1 0 = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp (show x.1 0 ≤ 1 from x.2.1 0)
  have hx1 : x.1 1 = 0 ∨ x.1 1 = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp (show x.1 1 ≤ 1 from x.2.1 1)
  have hsum := x.2.2
  rw [sum_fin2] at hsum
  rcases hx0 with h0 | h0
  · rcases hx1 with h1 | h1
    · rw [h0, h1] at hsum
      exact absurd hsum (by decide)
    · right
      apply Subtype.ext
      funext role
      cases role using Fin.cases with
      | zero => rw [h0, spreadRow01_zero]
      | succ r =>
        have hr : r = 0 := Subsingleton.elim r 0
        subst hr
        have hone : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by decide
        rw [← hone, h1, spreadRow01_one]
  · rcases hx1 with h1 | h1
    · left
      apply Subtype.ext
      funext role
      cases role using Fin.cases with
      | zero => rw [h0, spreadRow10_zero]
      | succ r =>
        have hr : r = 0 := Subsingleton.elim r 0
        subst hr
        have hone : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by decide
        rw [← hone, h1, spreadRow10_one]
    · rw [h0, h1] at hsum
      exact absurd hsum (by decide)

def spreadFirstRowEquiv : FirstRow (Role := Fin 2) (fun _ => 1) 1 ≃ Fin 2 where
  toFun x := if x.1 0 = 1 then 0 else 1
  invFun j := if j = 0 then spreadRow10 else spreadRow01
  left_inv x := by
    rcases spread_row_dichotomy x with h | h
    · subst h
      dsimp
      rw [spreadRow10_zero, if_pos rfl, if_pos rfl]
    · subst h
      dsimp
      rw [spreadRow01_zero, if_neg (by decide : (0 : ℕ) ≠ 1),
        if_neg (by decide : (1 : Fin 2) ≠ 0)]
  right_inv j := by
    cases j using Fin.cases with
    | zero =>
      dsimp
      rw [spreadRow10_zero, if_pos rfl]
    | succ r =>
      have hr : r = 0 := Subsingleton.elim r 0
      subst hr
      dsimp
      rw [spreadRow01_zero, if_neg (by decide : (0 : ℕ) ≠ 1)]

/-- **Positive.** The row `(1, 0)` is sent to `0`. -/
theorem spreadFirstRowEquiv_ten : spreadFirstRowEquiv spreadRow10 = 0 := by
  show (if spreadRow10.1 0 = 1 then (0 : Fin 2) else 1) = 0
  rw [spreadRow10_zero, if_pos rfl]

/-- **Negative.** That row is not sent to `1`. -/
theorem spreadFirstRowEquiv_ten_ne : spreadFirstRowEquiv spreadRow10 ≠ 1 := by
  rw [spreadFirstRowEquiv_ten]
  decide

theorem spread_matrix_two :
    Fintype.card (MarginMatrix (Fin 2) 2 (fun _ => 1) (fun _ => 1)) = 2 := by
  have hTotal : ∑ role : Fin 2, (1 : ℕ) = 1 + 1 := by
    rw [sum_fin2]
  have hrow : (fun _ : Fin 2 => (1 : ℕ)) = fun i => if i = 0 then 1 else 1 := by
    funext i
    split_ifs <;> rfl
  have hty := congrArg (fun rowCount => MarginMatrix (Fin 2) 2 rowCount (fun _ => 1)) hrow
  rw [Fintype.card_congr (Equiv.cast hty), twoRow_matrixCount (fun _ : Fin 2 => 1) 1 1 hTotal]
  rw [@Fintype.card_congr (FirstRow (fun _ : Fin 2 => 1) 1) (Fin 2)
    (Fintype.ofEquiv _ (twoRowEquiv (fun _ : Fin 2 => 1) 1 1 hTotal)) inferInstance
    spreadFirstRowEquiv, Fintype.card_fin]

theorem spread_support :
    atomSupport spreadMessages spreadOutcome = ({()} : Finset Unit) := by
  ext a
  cases a
  refine Iff.intro ?_ ?_
  · intro _
    exact Finset.mem_singleton_self ()
  · intro _
    exact mem_atomSupport_of_mem_message (messages := spreadMessages) (outcome := spreadOutcome)
      (i := 0) (by rw [spreadMessages]; exact Multiset.mem_singleton_self ())

/-- At margins row sums `(1, 1)` and column sums `(1, 1)`, `∏_a T_a = 2`. -/
theorem spread_blind_two : orderingBlindCount spreadMessages spreadOutcome = 2 := by
  have hrow : (fun i => Multiset.count () (spreadMessages i)) = fun _ => 1 :=
    funext spreadMessages_count
  have hcol : (fun role => Multiset.count () (spreadOutcome role)) = fun _ => 1 :=
    funext spreadOutcome_count
  have hty := congrArg₂ (MarginMatrix (Fin 2) 2) hrow hcol
  rw [orderingBlindCount, spread_support, Finset.prod_singleton,
    Fintype.card_congr (Equiv.cast hty), spread_matrix_two]

theorem natProd_le_one {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℕ}
    (h : ∀ a ∈ s, f a ≤ 1) :
    ∏ a ∈ s, f a ≤ 1 := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hfa : f a = 0 ∨ f a = 1 := by
      have hle := h a (Finset.mem_insert_self a s)
      omega
    have hs : ∀ b ∈ s, f b ≤ 1 := fun b hb => h b (Finset.mem_insert_of_mem hb)
    rcases hfa with h0 | h1
    · rw [h0, zero_mul]
      exact Nat.zero_le _
    · rw [h1, one_mul]
      exact ih hs

theorem matrixCard_below_two {Role : Type*} [Fintype Role] [DecidableEq Role] {k : ℕ}
    (hk : k < 2) (rowCount : Fin k → ℕ) (columnCount : Role → ℕ) :
    Fintype.card (MarginMatrix Role k rowCount columnCount) ≤ 1 := by
  cases k with
  | zero =>
    rw [Fintype.card_le_one_iff_subsingleton]
    exact ⟨fun m₁ m₂ => by
      apply MarginMatrix.ext_eq
      funext i
      exact Fin.elim0 i⟩
  | succ k =>
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.lt_of_succ_lt_succ hk))
    subst hk0
    rw [Fintype.card_le_one_iff_subsingleton]
    exact ⟨fun m₁ m₂ => by
      apply MarginMatrix.ext_eq
      funext i role
      cases i using Fin.cases with
      | zero =>
        have h1 := m₁.columnSum role
        have h2 := m₂.columnSum role
        rw [sum_fin1] at h1 h2
        exact h1.trans h2.symm
      | succ i' => exact Fin.elim0 i'⟩

theorem blind_below_two {Role : Type*} [Fintype Role] [DecidableEq Role] {k : ℕ} (hk : k < 2)
    (messages : Fin k → Message Atom) (outcome : Role → Message Atom) :
    orderingBlindCount messages outcome ≤ 1 := by
  rw [orderingBlindCount]
  exact natProd_le_one fun a _ => matrixCard_below_two hk _ _

theorem unit_matrix_card_le_one (k : ℕ) (rowCount : Fin k → ℕ) (columnCount : Unit → ℕ) :
    Fintype.card (MarginMatrix Unit k rowCount columnCount) ≤ 1 := by
  rw [Fintype.card_le_one_iff_subsingleton]
  exact ⟨fun m₁ m₂ => by
    apply MarginMatrix.ext_eq
    funext i role
    cases role
    have h1 := m₁.rowSum i
    have h2 := m₂.rowSum i
    rw [sum_unit] at h1 h2
    exact h1.trans h2.symm⟩

/-- One role gives `T_a ≤ 1` for every atom, so the product is not `2`. -/
theorem unit_blind_le_one {k : ℕ} (messages : Fin k → Message Atom)
    (outcome : Unit → Message Atom) : orderingBlindCount messages outcome ≤ 1 := by
  rw [orderingBlindCount]
  exact natProd_le_one fun _ _ => unit_matrix_card_le_one k _ _

/-- The product of the `T_a` is `2` at the spread site, and at no site with
fewer than two messages. -/
theorem spread_product_least :
    orderingBlindCount spreadMessages spreadOutcome = 2 ∧
      ∀ k : ℕ, k < 2 → ∀ {Atom : Type u} [DecidableEq Atom] {Role : Type*} [Fintype Role]
        [DecidableEq Role] (messages : Fin k → Message Atom) (outcome : Role → Message Atom),
        orderingBlindCount messages outcome ≠ 2 := by
  refine ⟨spread_blind_two, ?_⟩
  intro k hk Atom _ Role _ _ messages outcome
  exact ne_of_lt (Nat.lt_of_le_of_lt (blind_below_two hk messages outcome) (by decide))

/-- The message that carries the atom in the first position. -/
def orderedMessages : Fin 2 → Message Unit :=
  fun i => if i = 0 then {()} else 0

/-- **Positive.** The first ordered message has the occurrence. -/
theorem orderedMessages_zero : Multiset.count () (orderedMessages 0) = 1 := by
  rw [orderedMessages, if_pos rfl, message_singleton_count]

/-- **Negative.** The second ordered message is empty. -/
theorem orderedMessages_one : Multiset.count () (orderedMessages 1) = 0 := by
  rw [orderedMessages, if_neg (by decide : (1 : Fin 2) ≠ 0), message_zero_count]

/-- The message that carries the atom in the second position. -/
def swappedMessages : Fin 2 → Message Unit :=
  fun i => if i = 0 then 0 else {()}

/-- **Positive.** The second swapped message has the occurrence. -/
theorem swappedMessages_one : Multiset.count () (swappedMessages 1) = 1 := by
  rw [swappedMessages, if_neg (by decide : (1 : Fin 2) ≠ 0), message_singleton_count]

/-- **Negative.** The first swapped message is empty. -/
theorem swappedMessages_zero : Multiset.count () (swappedMessages 0) = 0 := by
  rw [swappedMessages, if_pos rfl, message_zero_count]

/-- **Negative.** The ordered messages are not the swapped messages. -/
theorem ordered_ne_swapped : orderedMessages ≠ swappedMessages := by
  intro h
  have h0 := congrFun h 0
  rw [orderedMessages, swappedMessages, if_pos rfl] at h0
  exact message_singleton_ne_zero () h0

/-- The outcome in which the one role receives the one occurrence. -/
def oneAtomOutcome : Unit → Message Unit :=
  fun _ => {()}

/-- **Positive.** That role has one occurrence. -/
theorem oneAtomOutcome_count : Multiset.count () (oneAtomOutcome ()) = 1 := by
  rw [oneAtomOutcome, message_singleton_count]

/-- **Negative.** It is not the empty outcome. -/
theorem oneAtomOutcome_ne_zero : oneAtomOutcome () ≠ 0 := by
  rw [oneAtomOutcome]
  exact message_singleton_ne_zero ()

/-- The outcome that receives nothing. -/
def emptyRoleOutcome : Unit → Message Unit :=
  fun _ => 0

/-- **Positive.** The empty outcome has no occurrences. -/
theorem emptyRoleOutcome_count : Multiset.count () (emptyRoleOutcome ()) = 0 := by
  rw [emptyRoleOutcome, message_zero_count]

/-- **Negative.** It is not the one-atom outcome. -/
theorem emptyRoleOutcome_ne_oneAtom : emptyRoleOutcome ≠ oneAtomOutcome := by
  intro h
  have h0 := congrFun h ()
  rw [emptyRoleOutcome, oneAtomOutcome] at h0
  exact message_singleton_ne_zero () h0.symm

/-- `μ` agrees when a permutation of the messages preserves atom counts and the
outcomes have the same atom counts. -/
theorem multiplicity_local {Role : Type*} [Fintype Role] [DecidableEq Role] {k : ℕ}
    (messages messages' : Fin k → Message Atom) (outcome outcome' : Role → Message Atom)
    (σ : Equiv.Perm (Fin k))
    (hmsg : ∀ a i, Multiset.count a (messages (σ i)) = Multiset.count a (messages' i))
    (hout : ∀ a role, Multiset.count a (outcome role) = Multiset.count a (outcome' role)) :
    fibreMultiplicity messages outcome = fibreMultiplicity messages' outcome' := by
  have hsupport :
      atomSupport (fun i => messages (σ i)) outcome = atomSupport messages' outcome' := by
    ext a
    constructor
    · intro h
      rcases Finset.mem_union.mp h with hmem | hmem
      · rcases Finset.mem_biUnion.mp hmem with ⟨i, _, hi⟩
        exact mem_atomSupport_of_mem_message (messages := messages') (outcome := outcome')
          (i := i) (Multiset.count_ne_zero.mp (by
            rw [← hmsg a i]
            exact Multiset.count_ne_zero.mpr (Multiset.mem_toFinset.mp hi)))
      · rcases Finset.mem_biUnion.mp hmem with ⟨role, _, ho⟩
        exact mem_atomSupport_of_mem_outcome (messages := messages') (outcome := outcome')
          (role := role) (Multiset.count_ne_zero.mp (by
            rw [← hout a role]
            exact Multiset.count_ne_zero.mpr (Multiset.mem_toFinset.mp ho)))
    · intro h
      rcases Finset.mem_union.mp h with hmem | hmem
      · rcases Finset.mem_biUnion.mp hmem with ⟨i, _, hi⟩
        exact mem_atomSupport_of_mem_message (messages := fun j => messages (σ j))
          (outcome := outcome) (i := i) (Multiset.count_ne_zero.mp (by
            rw [hmsg a i]
            exact Multiset.count_ne_zero.mpr (Multiset.mem_toFinset.mp hi)))
      · rcases Finset.mem_biUnion.mp hmem with ⟨role, _, ho⟩
        exact mem_atomSupport_of_mem_outcome (messages := fun j => messages (σ j))
          (outcome := outcome) (role := role) (Multiset.count_ne_zero.mp (by
            rw [hout a role]
            exact Multiset.count_ne_zero.mpr (Multiset.mem_toFinset.mp ho)))
  rw [fibreMultiplicity, fibreMultiplicity, ← atomSupport_perm σ messages outcome, hsupport]
  refine congrArg (fun t => Nat.factorial k * t) ?_
  refine Finset.prod_congr rfl fun a _ => ?_
  have hrow : (fun i => Multiset.count a (messages (σ i))) =
      fun i => Multiset.count a (messages' i) :=
    funext fun i => hmsg a i
  have hcol : (fun role => Multiset.count a (outcome role)) =
      fun role => Multiset.count a (outcome' role) :=
    funext fun role => hout a role
  have hty := congrArg₂ (MarginMatrix Role k) hrow hcol
  exact (Fintype.card_congr (marginRowPermute k (fun i => Multiset.count a (messages i))
    (fun role => Multiset.count a (outcome role)) σ)).trans (Fintype.card_congr (Equiv.cast hty))

/-- **Positive.** Swapping the ordered messages leaves `μ` unchanged. -/
theorem ordered_swapped_local :
    fibreMultiplicity orderedMessages oneAtomOutcome =
      fibreMultiplicity swappedMessages oneAtomOutcome := by
  refine multiplicity_local orderedMessages swappedMessages oneAtomOutcome oneAtomOutcome
    (Equiv.swap 0 1) ?_ ?_
  · intro a i
    cases a
    cases i using Fin.cases with
    | zero =>
      rw [Equiv.swap_apply_left, orderedMessages_one, swappedMessages_zero]
    | succ r =>
      have hr : r = 0 := Subsingleton.elim r 0
      subst hr
      have hone : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by decide
      rw [← hone, Equiv.swap_apply_right, orderedMessages_zero, swappedMessages_one]
  · intro a role
    cases a
    cases role
    rfl

def orderedMatrix : MarginMatrix Unit 2 (fun i => Multiset.count () (orderedMessages i))
    (fun role => Multiset.count () (oneAtomOutcome role)) where
  entry := fun i _ => Multiset.count () (orderedMessages i)
  rowSum := fun i => by
    rw [sum_unit]
  columnSum := fun role => by
    cases role
    rw [sum_fin2, orderedMessages_zero, orderedMessages_one, Nat.add_zero, oneAtomOutcome_count]

/-- **Positive.** The atom in the first message is sent to the role. -/
theorem orderedMatrix_entry_zero : orderedMatrix.entry 0 () = 1 := by
  show Multiset.count () (orderedMessages 0) = 1
  exact orderedMessages_zero

/-- **Negative.** The empty message contributes nothing. -/
theorem orderedMatrix_entry_one_ne_one : orderedMatrix.entry 1 () ≠ 1 := by
  show Multiset.count () (orderedMessages 1) ≠ 1
  rw [orderedMessages_one]
  decide

/-- **Positive.** The one-atom outcome has a nonempty fibre, so `μ` is not zero. -/
theorem ordered_mu_ne_zero :
    fibreMultiplicity orderedMessages oneAtomOutcome ≠ 0 := by
  have hmem : () ∈ atomSupport orderedMessages oneAtomOutcome :=
    mem_atomSupport_of_mem_message (messages := orderedMessages) (outcome := oneAtomOutcome)
      (i := 0) (by
        rw [orderedMessages, if_pos rfl]
        exact Multiset.mem_singleton_self ())
  have hsupport : atomSupport orderedMessages oneAtomOutcome = ({()} : Finset Unit) := by
    ext a
    cases a
    refine Iff.intro (fun _ => Finset.mem_singleton_self ()) (fun _ => hmem)
  have : Nonempty (MarginMatrix Unit 2 (fun i => Multiset.count () (orderedMessages i))
      (fun role => Multiset.count () (oneAtomOutcome role))) :=
    ⟨orderedMatrix⟩
  rw [fibreMultiplicity, hsupport, Finset.prod_singleton]
  exact Nat.mul_ne_zero (by decide) Fintype.card_ne_zero

/-- **Negative.** Sending the ordered messages to the empty outcome makes `μ` zero. -/
theorem ordered_empty_mu_zero :
    fibreMultiplicity orderedMessages emptyRoleOutcome = 0 := by
  have hmem : () ∈ atomSupport orderedMessages emptyRoleOutcome :=
    mem_atomSupport_of_mem_message (messages := orderedMessages) (outcome := emptyRoleOutcome)
      (i := 0) (by
        rw [orderedMessages, if_pos rfl]
        exact Multiset.mem_singleton_self ())
  have hempty : IsEmpty (MarginMatrix Unit 2 (fun i => Multiset.count () (orderedMessages i))
      (fun role => Multiset.count () (emptyRoleOutcome role))) := by
    refine ⟨fun m => ?_⟩
    have hrow := m.rowSum 0
    rw [sum_unit, orderedMessages_zero] at hrow
    have hcol := m.columnSum ()
    rw [sum_fin2, hrow, emptyRoleOutcome_count] at hcol
    omega
  have hcard : Fintype.card (MarginMatrix Unit 2 (fun i => Multiset.count () (orderedMessages i))
      (fun role => Multiset.count () (emptyRoleOutcome role))) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact hempty
  rw [fibreMultiplicity, Finset.prod_eq_zero hmem hcard, Nat.mul_zero]

/-- **Negative.** The empty outcome and the one-atom outcome do not share `μ`. -/
theorem ordered_outcomes_separate :
    fibreMultiplicity orderedMessages emptyRoleOutcome ≠
      fibreMultiplicity orderedMessages oneAtomOutcome := by
  rw [ordered_empty_mu_zero]
  exact Ne.symm ordered_mu_ne_zero

end Mettapedia.Logic.HostingStyles.Weighted
