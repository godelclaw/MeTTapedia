import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Multiset
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Unique

/-!
# Matrix-free candidates for a process-molecule fibre

Meredith, *Collision and Scattering for Process Molecules*, the candidate of the
proof sketch of `thm:corr`. A message is a `Multiset` of atoms. The roles of a
pattern are its constant part and its variables. A candidate for `k` messages
is an ordering of those message occurrences together with, for each message, a
family of multisets indexed by the roles whose sum is that message. The
outcome gives each role the sum of the parts it received.

For one fixed ordering, the fibre of an outcome is equivalent to the families,
indexed by the atoms that occur, of matrices of naturals with those row and
column sums. The candidate itself is not a matrix.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Weighted

universe u v

open scoped BigOperators

/-- Roles of a pattern: the constant part, or one variable of the pattern. -/
inductive PatternRole (Var : Type u) where
  | constantPart
  | var (v : Var)
  deriving DecidableEq

/-- **Positive.** Every role is the constant part or a variable. -/
theorem patternRole_constant_or_var {Var : Type u} (role : PatternRole Var) :
    role = PatternRole.constantPart ∨ ∃ v : Var, role = PatternRole.var v := by
  cases role with
  | constantPart => exact Or.inl rfl
  | var v => exact Or.inr ⟨v, rfl⟩

/-- **Negative.** The constant part is not a variable. -/
theorem constantPart_ne_var {Var : Type u} (v : Var) :
    PatternRole.constantPart (Var := Var) ≠ PatternRole.var v := by
  intro h
  cases h

/-- The roles are the constant part together with the variables. -/
def patternRoleEquiv (Var : Type u) : PatternRole Var ≃ Option Var where
  toFun
    | .constantPart => none
    | .var v => some v
  invFun
    | none => .constantPart
    | some v => .var v
  left_inv
    | .constantPart => rfl
    | .var _ => rfl
  right_inv
    | none => rfl
    | some _ => rfl

/-- **Positive.** The constant part is the role that is not a variable. -/
theorem patternRoleEquiv_constant (Var : Type u) :
    patternRoleEquiv Var PatternRole.constantPart = none :=
  rfl

/-- **Negative.** A variable role is not the constant part. -/
theorem patternRoleEquiv_var_ne_none {Var : Type u} (v : Var) :
    patternRoleEquiv Var (PatternRole.var v) ≠ none := by
  intro h
  cases h

/-- A message is a multiset of atoms. -/
abbrev Message (Atom : Type u) :=
  Multiset Atom

/-- **Positive.** One occurrence of an atom is one copy in the message. -/
theorem message_singleton_count {Atom : Type u} [DecidableEq Atom] (a : Atom) :
    Multiset.count a ({a} : Message Atom) = 1 :=
  Multiset.count_singleton_self a

/-- **Negative.** The empty message has no occurrence of an atom. -/
theorem message_zero_count {Atom : Type u} [DecidableEq Atom] (a : Atom) :
    Multiset.count a (0 : Message Atom) = 0 :=
  Multiset.count_zero a

/-- The singleton message is not the empty message. -/
theorem message_singleton_ne_zero {Atom : Type u} [DecidableEq Atom] (a : Atom) :
    ({a} : Message Atom) ≠ 0 := by
  intro h
  have hc := congrArg (Multiset.count a) h
  rw [message_singleton_count, message_zero_count] at hc
  exact Nat.one_ne_zero hc

/-- Assemble a multiset from occurrence counts on a finite set of atoms.
`Multiset.sum` adds one scaled singleton per atom in the set. -/
def countsToMultiset {Atom : Type u} [DecidableEq Atom] (support : Finset Atom)
    (n : Atom → ℕ) : Message Atom :=
  Multiset.sum (support.1.map fun a => n a • ({a} : Message Atom))

/-- `countsToMultiset` is the finset sum of the scaled singletons. -/
theorem countsToMultiset_finsetSum {Atom : Type u} [DecidableEq Atom]
    (support : Finset Atom) (n : Atom → ℕ) :
    countsToMultiset support n = ∑ a ∈ support, n a • ({a} : Message Atom) :=
  rfl

/-- Occurrence of an atom in `countsToMultiset`: the supplied count on the
support, and zero outside it. -/
theorem count_countsToMultiset {Atom : Type u} [DecidableEq Atom]
    (support : Finset Atom) (n : Atom → ℕ) (b : Atom) :
    Multiset.count b (countsToMultiset support n) = if b ∈ support then n b else 0 := by
  rw [countsToMultiset_finsetSum, Multiset.count_sum']
  by_cases hb : b ∈ support
  · rw [Finset.sum_eq_single_of_mem b hb, if_pos hb]
    · rw [Multiset.count_nsmul, Multiset.count_singleton_self, Nat.mul_one]
    · intro a _ hba
      rw [Multiset.count_nsmul, Multiset.count_singleton, if_neg (Ne.symm hba), Nat.mul_zero]
  · have hsum :
        ∑ a ∈ support, Multiset.count b (n a • ({a} : Message Atom)) = 0 :=
      Finset.sum_eq_zero fun a ha => by
        have hba : b ≠ a := by
          intro h
          exact hb (h ▸ ha)
        rw [Multiset.count_nsmul, Multiset.count_singleton, if_neg hba, Nat.mul_zero]
    rw [hsum, if_neg hb]

/-- **Positive.** One counted atom on a singleton support is the singleton message. -/
theorem countsToMultiset_singleton :
    countsToMultiset ({()} : Finset Unit) (fun _ : Unit => 1) = ({()} : Message Unit) := by
  rw [countsToMultiset_finsetSum, Finset.sum_singleton, one_nsmul]

/-- **Negative.** The empty support builds the empty message, not a singleton. -/
theorem countsToMultiset_empty_ne_singleton :
    countsToMultiset (∅ : Finset Unit) (fun _ : Unit => 1) ≠ ({()} : Message Unit) := by
  intro h
  have hc := congrArg (Multiset.count ()) h
  rw [count_countsToMultiset, message_singleton_count, if_neg (Finset.notMem_empty ())] at hc
  exact Nat.one_ne_zero hc.symm

theorem countsToMultiset_congr {Atom : Type u} [DecidableEq Atom] {support : Finset Atom}
    {n n' : Atom → ℕ} (h : ∀ a ∈ support, n a = n' a) :
    countsToMultiset support n = countsToMultiset support n' := by
  rw [countsToMultiset_finsetSum, countsToMultiset_finsetSum]
  exact Finset.sum_congr rfl fun a ha =>
    congrArg (fun t => t • ({a} : Message Atom)) (h a ha)

/-- Counts on a support that contains every atom of `s` rebuild `s`. -/
theorem countsToMultiset_recover {Atom : Type u} [DecidableEq Atom] (s : Message Atom)
    {support : Finset Atom} (hsub : s.toFinset ⊆ support) :
    countsToMultiset support (fun a => Multiset.count a s) = s := by
  rw [countsToMultiset_finsetSum]
  have hsum :
      ∑ a ∈ s.toFinset, Multiset.count a s • ({a} : Message Atom) =
        ∑ a ∈ support, Multiset.count a s • ({a} : Message Atom) :=
    Finset.sum_subset hsub fun a _ hnot => by
      have hz : Multiset.count a s = 0 := by
        rw [Multiset.count_eq_zero]
        intro hmem
        exact hnot (Multiset.mem_toFinset.mpr hmem)
      rw [hz, zero_nsmul]
  exact (hsum.symm).trans (Multiset.toFinset_sum_count_nsmul_eq s)

/-- A candidate for `k` messages. `ordering` arranges the message occurrences.
`part i role` is the multiset that role receives from the message in row `i`.
Those parts sum to the ordered message. This is not a matrix of naturals. -/
structure Candidate (Atom : Type u) [DecidableEq Atom] (Role : Type v) [Fintype Role]
    (k : ℕ) (messages : Fin k → Message Atom) where
  ordering : Equiv.Perm (Fin k)
  part : Fin k → Role → Message Atom
  rowSum : ∀ i : Fin k, ∑ role : Role, part i role = messages (ordering i)

theorem Candidate.ext_eq {Atom : Type u} [DecidableEq Atom] {Role : Type v} [Fintype Role]
    {k : ℕ} {messages : Fin k → Message Atom} {c₁ c₂ : Candidate Atom Role k messages}
    (hord : c₁.ordering = c₂.ordering) (hpart : c₁.part = c₂.part) : c₁ = c₂ := by
  cases c₁
  cases c₂
  cases hord
  cases hpart
  rfl

/-- One message, whose single occurrence is the atom `()`. -/
def unitMessages : Fin 1 → Message Unit :=
  fun _ => {()}

/-- **Positive.** The unit message carries the atom. -/
theorem unitMessages_count : Multiset.count () (unitMessages 0) = 1 := by
  rw [unitMessages, message_singleton_count]

/-- **Negative.** The unit message is not empty. -/
theorem unitMessages_ne_zero : unitMessages 0 ≠ 0 := by
  rw [unitMessages]
  exact message_singleton_ne_zero ()

/-- **Positive.** The one message sent entirely to the one role is a candidate. -/
def unitCandidate : Candidate Unit Unit 1 unitMessages where
  ordering := Equiv.refl (Fin 1)
  part := fun _ _ => {()}
  rowSum := fun _ => by
    rw [Finset.univ_unique, Finset.sum_singleton]
    rfl

/-- **Positive.** That candidate gives the role the singleton message. -/
theorem unitCandidate_part : unitCandidate.part 0 () = {()} :=
  rfl

/-- **Negative.** No candidate gives the only role the empty multiset. -/
theorem not_zero_part_candidate (c : Candidate Unit Unit 1 unitMessages) :
    c.part 0 () ≠ 0 := by
  intro h
  have hrow := c.rowSum 0
  rw [Finset.univ_unique, Finset.sum_singleton, h, unitMessages] at hrow
  exact message_singleton_ne_zero () hrow.symm

/-- The outcome of a candidate: each role receives the sum, over the messages,
of the part assigned to it. -/
def Candidate.outcome {Atom : Type u} [DecidableEq Atom] {Role : Type v} [Fintype Role]
    {k : ℕ} {messages : Fin k → Message Atom} (c : Candidate Atom Role k messages) :
    Role → Message Atom :=
  fun role => ∑ i : Fin k, c.part i role

/-- **Positive.** The unit candidate's outcome is the singleton message. -/
theorem unitCandidate_outcome : unitCandidate.outcome () = {()} := by
  rw [Candidate.outcome, Finset.univ_unique, Finset.sum_singleton]
  rfl

/-- **Negative.** That outcome is not the empty multiset. -/
theorem unitCandidate_outcome_ne_zero : unitCandidate.outcome () ≠ 0 := by
  rw [unitCandidate_outcome]
  exact message_singleton_ne_zero ()

/-- The fibre of an outcome is the set of candidates with that outcome. -/
def Fibre (Atom : Type u) [DecidableEq Atom] (Role : Type v) [Fintype Role] (k : ℕ)
    (messages : Fin k → Message Atom) (outcome : Role → Message Atom) :=
  { c : Candidate Atom Role k messages // c.outcome = outcome }

/-- The outcome in which the one role receives the singleton. -/
def unitOutcome : Unit → Message Unit :=
  fun _ => {()}

/-- **Positive.** The unit outcome contains the atom. -/
theorem unitOutcome_count : Multiset.count () (unitOutcome ()) = 1 := by
  rw [unitOutcome, message_singleton_count]

/-- **Negative.** The unit outcome is not empty. -/
theorem unitOutcome_ne_zero : unitOutcome () ≠ 0 :=
  message_singleton_ne_zero ()

/-- **Positive.** The unit candidate lies on the fibre of the unit outcome. -/
def unitFibreElement : Fibre Unit Unit 1 unitMessages unitOutcome :=
  ⟨unitCandidate, by
    funext role
    cases role
    exact unitCandidate_outcome⟩

/-- **Negative.** The empty outcome is not the unit outcome. -/
theorem unitOutcome_ne_zeroOutcome : unitOutcome ≠ (fun _ : Unit => (0 : Message Unit)) := by
  intro h
  have hc := congrFun h ()
  exact unitOutcome_ne_zero hc

/-- The outcome in which the one role receives nothing. -/
def zeroOutcome : Unit → Message Unit :=
  fun _ => 0

/-- **Positive.** The zero outcome is empty at the only role. -/
theorem zeroOutcome_count : Multiset.count () (zeroOutcome ()) = 0 := by
  rw [zeroOutcome, message_zero_count]

/-- **Negative.** The zero outcome is not the singleton outcome. -/
theorem zeroOutcome_ne_unitOutcome : zeroOutcome ≠ unitOutcome := by
  intro h
  have hc := congrFun h ()
  exact unitOutcome_ne_zero hc.symm

theorem sum_unit {α : Type*} [AddCommMonoid α] (f : Unit → α) :
    (∑ r : Unit, f r) = f () := by
  rw [Finset.univ_unique, Finset.sum_singleton]

theorem sum_fin1 {α : Type*} [AddCommMonoid α] (f : Fin 1 → α) :
    (∑ i : Fin 1, f i) = f 0 := by
  rw [Finset.univ_unique, Finset.sum_singleton]
  exact congrArg f (Subsingleton.elim (default : Fin 1) 0)

/-- **Negative.** No candidate for the unit message has the empty outcome. -/
theorem zeroOutcome_fibre_empty : IsEmpty (Fibre Unit Unit 1 unitMessages zeroOutcome) := by
  refine ⟨fun c => ?_⟩
  have hrow := c.1.rowSum 0
  rw [sum_unit, unitMessages] at hrow
  have hout := congrFun c.property ()
  rw [Candidate.outcome, sum_fin1, zeroOutcome] at hout
  exact message_singleton_ne_zero () (hrow.symm.trans hout)

/-- The fibre of an outcome at one fixed ordering of the messages. -/
def FibreAt (Atom : Type u) [DecidableEq Atom] (Role : Type v) [Fintype Role] (k : ℕ)
    (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom) :=
  { c : Fibre Atom Role k messages outcome // c.1.ordering = σ }

/-- **Positive.** The unit candidate uses the only ordering of one message. -/
def unitFibreAt :
    FibreAt Unit Unit 1 (Equiv.refl (Fin 1)) unitMessages unitOutcome :=
  ⟨unitFibreElement, rfl⟩

/-- **Negative.** The empty outcome has no candidate at that ordering either. -/
theorem zeroOutcome_fibreAt_empty :
    IsEmpty (FibreAt Unit Unit 1 (Equiv.refl (Fin 1)) unitMessages zeroOutcome) :=
  ⟨fun c => zeroOutcome_fibre_empty.false c.1⟩

/-- Atoms that occur in some message or in some role of the outcome. -/
def atomSupport {Atom : Type u} [DecidableEq Atom] {Role : Type v} [Fintype Role] {k : ℕ}
    (messages : Fin k → Message Atom) (outcome : Role → Message Atom) : Finset Atom :=
  (Finset.univ : Finset (Fin k)).biUnion (fun i => (messages i).toFinset) ∪
    (Finset.univ : Finset Role).biUnion (fun role => (outcome role).toFinset)

theorem mem_atomSupport_of_mem_message {Atom : Type u} [DecidableEq Atom] {Role : Type v}
    [Fintype Role] {k : ℕ} {messages : Fin k → Message Atom} {outcome : Role → Message Atom}
    {a : Atom} {i : Fin k} (h : a ∈ messages i) : a ∈ atomSupport messages outcome :=
  Finset.mem_union.mpr
    (Or.inl (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, Multiset.mem_toFinset.mpr h⟩))

theorem mem_atomSupport_of_mem_outcome {Atom : Type u} [DecidableEq Atom] {Role : Type v}
    [Fintype Role] {k : ℕ} {messages : Fin k → Message Atom} {outcome : Role → Message Atom}
    {a : Atom} {role : Role} (h : a ∈ outcome role) : a ∈ atomSupport messages outcome :=
  Finset.mem_union.mpr
    (Or.inr (Finset.mem_biUnion.mpr ⟨role, Finset.mem_univ role, Multiset.mem_toFinset.mpr h⟩))

theorem message_count_zero_outside {Atom : Type u} [DecidableEq Atom] {Role : Type v}
    [Fintype Role] {k : ℕ} {messages : Fin k → Message Atom} {outcome : Role → Message Atom}
    {a : Atom} (ha : a ∉ atomSupport messages outcome) (i : Fin k) :
    Multiset.count a (messages i) = 0 := by
  rw [Multiset.count_eq_zero]
  intro hmem
  exact ha (mem_atomSupport_of_mem_message hmem)

theorem outcome_count_zero_outside {Atom : Type u} [DecidableEq Atom] {Role : Type v}
    [Fintype Role] {k : ℕ} {messages : Fin k → Message Atom} {outcome : Role → Message Atom}
    {a : Atom} (ha : a ∉ atomSupport messages outcome) (role : Role) :
    Multiset.count a (outcome role) = 0 := by
  rw [Multiset.count_eq_zero]
  intro hmem
  exact ha (mem_atomSupport_of_mem_outcome hmem)

/-- **Positive.** The atom of the unit message is in the support. -/
theorem unit_mem_atomSupport : () ∈ atomSupport unitMessages unitOutcome :=
  mem_atomSupport_of_mem_message (messages := unitMessages) (outcome := unitOutcome) (i := 0)
    (Multiset.mem_singleton_self ())

/-- Messages and outcome with no atoms. -/
def emptyMessages : Fin 1 → Message Unit :=
  fun _ => 0

/-- **Positive.** The empty message has count zero. -/
theorem emptyMessages_count : Multiset.count () (emptyMessages 0) = 0 := by
  rw [emptyMessages, message_zero_count]

/-- **Negative.** The empty message is not the unit message. -/
theorem emptyMessages_ne_unit : emptyMessages ≠ unitMessages := by
  intro h
  have hc := congrFun h 0
  exact unitMessages_ne_zero hc.symm

/-- **Negative.** An atom that occurs nowhere is outside the support. -/
theorem empty_not_mem_atomSupport : () ∉ atomSupport emptyMessages zeroOutcome := by
  intro h
  cases Finset.mem_union.mp h with
  | inl hm =>
    rcases Finset.mem_biUnion.mp hm with ⟨i, _, hi⟩
    have hmem : () ∈ emptyMessages i := Multiset.mem_toFinset.mp hi
    have hne : Multiset.count () (emptyMessages i) ≠ 0 := Multiset.count_ne_zero.mpr hmem
    rw [emptyMessages, message_zero_count] at hne
    exact hne rfl
  | inr ho =>
    rcases Finset.mem_biUnion.mp ho with ⟨role, _, hrole⟩
    have hmem : () ∈ zeroOutcome role := Multiset.mem_toFinset.mp hrole
    have hne : Multiset.count () (zeroOutcome role) ≠ 0 := Multiset.count_ne_zero.mpr hmem
    rw [zeroOutcome, message_zero_count] at hne
    exact hne rfl

/-- A matrix of naturals with prescribed row and column sums. Rows are messages
and columns are roles. This is not a candidate. -/
structure MarginMatrix (Role : Type v) [Fintype Role] (k : ℕ) (rowCount : Fin k → ℕ)
    (columnCount : Role → ℕ) where
  entry : Fin k → Role → ℕ
  rowSum : ∀ i : Fin k, ∑ role : Role, entry i role = rowCount i
  columnSum : ∀ role : Role, ∑ i : Fin k, entry i role = columnCount role

theorem MarginMatrix.ext_eq {Role : Type v} [Fintype Role] {k : ℕ} {rowCount : Fin k → ℕ}
    {columnCount : Role → ℕ} {m₁ m₂ : MarginMatrix Role k rowCount columnCount}
    (h : m₁.entry = m₂.entry) : m₁ = m₂ := by
  cases m₁
  cases m₂
  cases h
  rfl

/-- **Positive.** One row, one column, both sums `1`, filled by `1`. -/
def unitMatrix : MarginMatrix Unit 1 (fun _ => 1) (fun _ => 1) where
  entry := fun _ _ => 1
  rowSum := fun _ => by
    rw [Finset.univ_unique, Finset.sum_singleton]
  columnSum := fun _ => by
    rw [Finset.univ_unique, Finset.sum_singleton]

/-- **Positive.** The single entry of `unitMatrix` is `1`. -/
theorem unitMatrix_entry : unitMatrix.entry 0 () = 1 :=
  rfl

/-- **Negative.** No such matrix has entry `0`. -/
theorem unitMatrix_entry_ne_zero (m : MarginMatrix Unit 1 (fun _ => 1) (fun _ => 1)) :
    m.entry 0 () ≠ 0 := by
  intro h
  have hrow := m.rowSum 0
  rw [Finset.univ_unique, Finset.sum_singleton, h] at hrow
  exact Nat.one_ne_zero hrow.symm

/-- Families of matrices, one per atom in the support. The row sums are the
counts of that atom in the messages, and the column sums are its counts in the
roles of the outcome. -/
def MatrixFamily (Atom : Type u) [DecidableEq Atom] (Role : Type v) [Fintype Role] (k : ℕ)
    (messages : Fin k → Message Atom) (outcome : Role → Message Atom) :=
  ∀ a : { a : Atom // a ∈ atomSupport messages outcome },
    MarginMatrix Role k (fun i => Multiset.count a.1 (messages i))
      (fun role => Multiset.count a.1 (outcome role))

/-- **Positive.** The unit site has the matrix whose only entry is `1`. -/
def unitMatrixFamily : MatrixFamily Unit Unit 1 unitMessages unitOutcome :=
  fun a =>
    { entry := fun _ _ => 1
      rowSum := fun i => by
        cases a.val
        rw [Finset.univ_unique, Finset.sum_singleton, unitMessages, message_singleton_count]
      columnSum := fun _ => by
        cases a.val
        rw [Finset.univ_unique, Finset.sum_singleton, unitOutcome, message_singleton_count] }

/-- **Positive.** That family records the one occurrence. -/
theorem unitMatrixFamily_entry :
    (unitMatrixFamily ⟨(), unit_mem_atomSupport⟩).entry 0 () = 1 :=
  rfl

/-- **Negative.** The unit message and the empty outcome admit no matrix. -/
theorem zeroMatrixFamily_empty :
    IsEmpty (MatrixFamily Unit Unit 1 unitMessages zeroOutcome) := by
  refine ⟨fun m => ?_⟩
  have hmem : () ∈ atomSupport unitMessages zeroOutcome :=
    mem_atomSupport_of_mem_message (messages := unitMessages) (outcome := zeroOutcome) (i := 0)
      (Multiset.mem_singleton_self ())
  have hrow := (m ⟨(), hmem⟩).rowSum 0
  have hcol := (m ⟨(), hmem⟩).columnSum ()
  rw [Finset.univ_unique, Finset.sum_singleton, unitMessages, message_singleton_count] at hrow
  rw [Finset.univ_unique, Finset.sum_singleton, zeroOutcome, message_zero_count] at hcol
  exact Nat.one_ne_zero (hrow.symm.trans hcol)

theorem part_toFinset_subset {Atom : Type u} [DecidableEq Atom] {Role : Type v} [Fintype Role]
    {k : ℕ} (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom) (c : FibreAt Atom Role k σ messages outcome) (i : Fin k)
    (role : Role) :
    (c.1.1.part i role).toFinset ⊆ atomSupport (fun j => messages (σ j)) outcome := by
  intro a ha
  have hmem : a ∈ c.1.1.part i role := Multiset.mem_toFinset.mp ha
  have hpos : 0 < Multiset.count a (c.1.1.part i role) := Multiset.count_pos.mpr hmem
  have hsum := congrArg (Multiset.count a) (c.1.1.rowSum i)
  rw [Multiset.count_sum'] at hsum
  have hle : Multiset.count a (c.1.1.part i role) ≤
      ∑ r : Role, Multiset.count a (c.1.1.part i r) :=
    Finset.single_le_sum (f := fun r => Multiset.count a (c.1.1.part i r))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ role)
  have hmsg : Multiset.count a (c.1.1.part i role) ≤
      Multiset.count a (messages (c.1.1.ordering i)) :=
    le_trans hle (le_of_eq hsum)
  rw [c.2] at hmsg
  exact mem_atomSupport_of_mem_message (Multiset.count_pos.mp (Nat.lt_of_lt_of_le hpos hmsg))

/-- The multiset a role receives from one ordered message, rebuilt from the
matrix entries of a family. -/
def matrixPart {Atom : Type u} [DecidableEq Atom] {Role : Type v} [Fintype Role] {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom) (outcome : Role → Message Atom)
    (m : MatrixFamily Atom Role k (fun i => messages (σ i)) outcome) (i : Fin k) (role : Role) :
    Message Atom :=
  countsToMultiset (atomSupport (fun j => messages (σ j)) outcome) fun a =>
    if h : a ∈ atomSupport (fun j => messages (σ j)) outcome then
      (m ⟨a, h⟩).entry i role
    else
      0

theorem matrixPart_count {Atom : Type u} [DecidableEq Atom] {Role : Type v} [Fintype Role]
    {k : ℕ} (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom)
    (m : MatrixFamily Atom Role k (fun i => messages (σ i)) outcome) (i : Fin k) (role : Role)
    (b : Atom) :
    Multiset.count b (matrixPart σ messages outcome m i role) =
      if h : b ∈ atomSupport (fun j => messages (σ j)) outcome then
        (m ⟨b, h⟩).entry i role
      else
        0 := by
  rw [matrixPart, count_countsToMultiset]
  by_cases hb : b ∈ atomSupport (fun j => messages (σ j)) outcome
  · rw [if_pos hb, dif_pos hb]
  · rw [if_neg hb, dif_neg hb]

theorem matrixPart_count_mem {Atom : Type u} [DecidableEq Atom] {Role : Type v} [Fintype Role]
    {k : ℕ} (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom)
    (m : MatrixFamily Atom Role k (fun i => messages (σ i)) outcome) (i : Fin k) (role : Role)
    {b : Atom} (hb : b ∈ atomSupport (fun j => messages (σ j)) outcome) :
    Multiset.count b (matrixPart σ messages outcome m i role) = (m ⟨b, hb⟩).entry i role := by
  rw [matrixPart_count, dif_pos hb]

theorem matrixPart_count_not_mem {Atom : Type u} [DecidableEq Atom] {Role : Type v} [Fintype Role]
    {k : ℕ} (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom)
    (m : MatrixFamily Atom Role k (fun i => messages (σ i)) outcome) (i : Fin k) (role : Role)
    {b : Atom} (hb : b ∉ atomSupport (fun j => messages (σ j)) outcome) :
    Multiset.count b (matrixPart σ messages outcome m i role) = 0 := by
  rw [matrixPart_count, dif_neg hb]

theorem matrixPart_sums_to_message {Atom : Type u} [DecidableEq Atom] {Role : Type v}
    [Fintype Role] {k : ℕ} (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom)
    (m : MatrixFamily Atom Role k (fun i => messages (σ i)) outcome) (i : Fin k) :
    ∑ role : Role, matrixPart σ messages outcome m i role = messages (σ i) := by
  refine Multiset.ext.mpr fun b => ?_
  rw [Multiset.count_sum']
  by_cases hb : b ∈ atomSupport (fun j => messages (σ j)) outcome
  · rw [Finset.sum_congr rfl fun role _ => matrixPart_count_mem σ messages outcome m i role hb]
    exact (m ⟨b, hb⟩).rowSum i
  · rw [Finset.sum_eq_zero fun role _ => matrixPart_count_not_mem σ messages outcome m i role hb]
    exact (message_count_zero_outside hb i).symm

theorem matrixPart_sums_to_outcome {Atom : Type u} [DecidableEq Atom] {Role : Type v}
    [Fintype Role] {k : ℕ} (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom)
    (m : MatrixFamily Atom Role k (fun i => messages (σ i)) outcome) (role : Role) :
    ∑ i : Fin k, matrixPart σ messages outcome m i role = outcome role := by
  refine Multiset.ext.mpr fun b => ?_
  rw [Multiset.count_sum']
  by_cases hb : b ∈ atomSupport (fun j => messages (σ j)) outcome
  · rw [Finset.sum_congr rfl fun i _ => matrixPart_count_mem σ messages outcome m i role hb]
    exact (m ⟨b, hb⟩).columnSum role
  · rw [Finset.sum_eq_zero fun i _ => matrixPart_count_not_mem σ messages outcome m i role hb]
    exact (outcome_count_zero_outside hb role).symm

/-- **Positive.** On the unit family the rebuilt part is the singleton message. -/
theorem matrixPart_unit :
    matrixPart (Equiv.refl (Fin 1)) unitMessages unitOutcome unitMatrixFamily 0 () = {()} := by
  refine Multiset.ext.mpr fun b => ?_
  cases b
  have hb : () ∈ atomSupport (fun j => unitMessages (Equiv.refl (Fin 1) j)) unitOutcome :=
    mem_atomSupport_of_mem_message
      (messages := fun j => unitMessages (Equiv.refl (Fin 1) j)) (outcome := unitOutcome)
      (i := 0) (Multiset.mem_singleton_self ())
  have hcount :=
    matrixPart_count (Equiv.refl (Fin 1)) unitMessages unitOutcome unitMatrixFamily 0 () ()
  rw [hcount, dif_pos hb, message_singleton_count]
  rfl

/-- **Negative.** That rebuilt part is not empty. -/
theorem matrixPart_unit_ne_zero :
    matrixPart (Equiv.refl (Fin 1)) unitMessages unitOutcome unitMatrixFamily 0 () ≠ 0 := by
  rw [matrixPart_unit]
  exact message_singleton_ne_zero ()

/-- Read the count matrices of one ordered candidate. -/
def fibreAtToFamily {Atom : Type u} [DecidableEq Atom] {Role : Type v} [Fintype Role] {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom) (outcome : Role → Message Atom)
    (c : FibreAt Atom Role k σ messages outcome) :
    MatrixFamily Atom Role k (fun i => messages (σ i)) outcome :=
  fun a =>
    { entry := fun i role => Multiset.count a.1 (c.1.1.part i role)
      rowSum := fun i => by
        have hsum := congrArg (Multiset.count a.1) (c.1.1.rowSum i)
        rw [Multiset.count_sum'] at hsum
        rw [hsum, c.2]
      columnSum := fun role => by
        have hout := congrFun c.1.property role
        rw [Candidate.outcome] at hout
        have hsum := congrArg (Multiset.count a.1) hout
        rw [Multiset.count_sum'] at hsum
        exact hsum }

/-- **Positive.** The unit candidate is read as the matrix entry `1`. -/
theorem fibreAtToFamily_unit_entry :
    (fibreAtToFamily (Equiv.refl (Fin 1)) unitMessages unitOutcome unitFibreAt
      ⟨(), unit_mem_atomSupport⟩).entry 0 () = 1 := by
  unfold fibreAtToFamily unitFibreAt unitFibreElement unitCandidate
  exact Multiset.count_singleton_self ()

/-- **Negative.** That entry is not `0`. -/
theorem fibreAtToFamily_unit_entry_ne_zero :
    (fibreAtToFamily (Equiv.refl (Fin 1)) unitMessages unitOutcome unitFibreAt
      ⟨(), unit_mem_atomSupport⟩).entry 0 () ≠ 0 := by
  rw [fibreAtToFamily_unit_entry]
  exact Nat.one_ne_zero

/-- Rebuild the ordered candidate from its count matrices. -/
def familyToFibreAt {Atom : Type u} [DecidableEq Atom] {Role : Type v} [Fintype Role] {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom) (outcome : Role → Message Atom)
    (m : MatrixFamily Atom Role k (fun i => messages (σ i)) outcome) :
    FibreAt Atom Role k σ messages outcome :=
  { val :=
    { val :=
      { ordering := σ
        part := fun i role => matrixPart σ messages outcome m i role
        rowSum := fun i => matrixPart_sums_to_message σ messages outcome m i }
      property := by
        funext role
        rw [Candidate.outcome]
        exact matrixPart_sums_to_outcome σ messages outcome m role }
    property := rfl }

/-- **Positive.** The unit matrix family rebuilds the singleton part. -/
theorem familyToFibreAt_unit_part :
    (familyToFibreAt (Equiv.refl (Fin 1)) unitMessages unitOutcome unitMatrixFamily).1.1.part
      0 () = {()} :=
  matrixPart_unit

/-- **Negative.** The rebuilt part is not empty. -/
theorem familyToFibreAt_unit_part_ne_zero :
    (familyToFibreAt (Equiv.refl (Fin 1)) unitMessages unitOutcome unitMatrixFamily).1.1.part
      0 () ≠ 0 :=
  matrixPart_unit_ne_zero

theorem matrixPart_fibreAtToFamily {Atom : Type u} [DecidableEq Atom] {Role : Type v}
    [Fintype Role] {k : ℕ} (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom) (c : FibreAt Atom Role k σ messages outcome) (i : Fin k)
    (role : Role) :
    matrixPart σ messages outcome (fibreAtToFamily σ messages outcome c) i role =
      c.1.1.part i role := by
  unfold matrixPart
  refine Eq.trans
      (countsToMultiset_congr fun a ha => ?_)
      (countsToMultiset_recover (c.1.1.part i role)
        (part_toFinset_subset σ messages outcome c i role))
  rw [dif_pos ha, fibreAtToFamily]

theorem familyToFibreAt_fibreAtToFamily {Atom : Type u} [DecidableEq Atom] {Role : Type v}
    [Fintype Role] {k : ℕ} (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom) (c : FibreAt Atom Role k σ messages outcome) :
    familyToFibreAt σ messages outcome (fibreAtToFamily σ messages outcome c) = c := by
  refine Subtype.ext ?_
  refine Subtype.ext ?_
  refine Candidate.ext_eq ?_ ?_
  · exact c.2.symm
  · funext i role
    exact matrixPart_fibreAtToFamily σ messages outcome c i role

theorem fibreAtToFamily_familyToFibreAt {Atom : Type u} [DecidableEq Atom] {Role : Type v}
    [Fintype Role] {k : ℕ} (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom)
    (m : MatrixFamily Atom Role k (fun i => messages (σ i)) outcome) :
    fibreAtToFamily σ messages outcome (familyToFibreAt σ messages outcome m) = m := by
  funext a
  refine MarginMatrix.ext_eq ?_
  funext i role
  rw [fibreAtToFamily, familyToFibreAt]
  exact matrixPart_count_mem σ messages outcome m i role a.2

/-- For a fixed ordering, the fibre of an outcome is in bijection with the
families of count matrices. Rows are the ordered messages and columns are the
roles. The equivalence uses decidable equality of atoms, so that occurrences
are counts, and a finite role type, so that the role sums exist. It does not
require the atom type to be finite: atoms outside the finite support of the
messages and the outcome do not appear. -/
def fibreAtEquiv {Atom : Type u} [DecidableEq Atom] {Role : Type v} [Fintype Role] {k : ℕ}
    (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom) :
    FibreAt Atom Role k σ messages outcome ≃
      MatrixFamily Atom Role k (fun i => messages (σ i)) outcome where
  toFun := fibreAtToFamily σ messages outcome
  invFun := familyToFibreAt σ messages outcome
  left_inv := familyToFibreAt_fibreAtToFamily σ messages outcome
  right_inv := fibreAtToFamily_familyToFibreAt σ messages outcome

/-- **Positive.** The equivalence sends the unit candidate to the entry `1`. -/
theorem fibreAtEquiv_unit_entry :
    ((fibreAtEquiv (Equiv.refl (Fin 1)) unitMessages unitOutcome) unitFibreAt
      ⟨(), unit_mem_atomSupport⟩).entry 0 () = 1 :=
  fibreAtToFamily_unit_entry

/-- **Negative.** It does not send that candidate to the entry `0`. -/
theorem fibreAtEquiv_unit_entry_ne_zero :
    ((fibreAtEquiv (Equiv.refl (Fin 1)) unitMessages unitOutcome) unitFibreAt
      ⟨(), unit_mem_atomSupport⟩).entry 0 () ≠ 0 :=
  fibreAtToFamily_unit_entry_ne_zero

end Mettapedia.Logic.HostingStyles.Weighted
