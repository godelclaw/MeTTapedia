import Mettapedia.Logic.HostingStyles.Weighted.MoleculeCandidate
import Mettapedia.Logic.HostingStyles.Weighted.TwoBody
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sets
import Mathlib.Logic.Equiv.Sum

/-!
# Fibre multiplicity μ = k! ∏_a T_a

Meredith, *Collision and Scattering for Process Molecules*, Definition `def:mu`.
`T_a` is the number of natural-number matrices with the row sums of atom `a`
in the messages and the column sums of atom `a` in the outcome. `μ` is `k!`
times the product of the `T_a`.

Finiteness used by the cardinality: the role type is finite and has decidable
equality, so the matrices can be enumerated, and atoms have decidable equality,
so occurrences are counts. The product runs over the finite support of the
messages and the outcome. The atom type itself need not be finite: an atom
outside that support contributes the factor `1`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Weighted

universe u v

open scoped BigOperators

variable {Atom : Type u} [DecidableEq Atom]
variable {Role : Type v} [Fintype Role] [DecidableEq Role]

/-- Functions whose value in row `i` is strictly below `rowCount i + 1`. -/
def entryBound (k : ℕ) (rowCount : Fin k → ℕ) : Finset (Fin k → Role → ℕ) :=
  Fintype.piFinset fun i => Fintype.piFinset fun _ : Role => Finset.range (rowCount i + 1)

/-- Matrices, as functions, whose entries are below the row sums and whose row
and column sums are the prescribed margins. -/
def admissible (k : ℕ) (rowCount : Fin k → ℕ) (columnCount : Role → ℕ) :
    Finset (Fin k → Role → ℕ) :=
  (entryBound k rowCount).filter fun entry =>
    (∀ i, ∑ role : Role, entry i role = rowCount i) ∧
    (∀ role : Role, ∑ i : Fin k, entry i role = columnCount role)

theorem marginMatrixEquiv_mem (k : ℕ) (rowCount : Fin k → ℕ) (columnCount : Role → ℕ)
    (m : MarginMatrix Role k rowCount columnCount) : m.entry ∈ admissible k rowCount columnCount := by
  refine Finset.mem_filter.mpr ⟨?_, ⟨m.rowSum, m.columnSum⟩⟩
  rw [entryBound, Fintype.mem_piFinset]
  intro i
  rw [Fintype.mem_piFinset]
  intro role
  rw [Finset.mem_range, Nat.lt_succ_iff]
  have hle : m.entry i role ≤ ∑ r : Role, m.entry i r :=
    Finset.single_le_sum (f := fun r => m.entry i r) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ role)
  exact hle.trans (le_of_eq (m.rowSum i))

/-- A margin matrix is exactly an admissible entry function. -/
def marginMatrixEquiv (k : ℕ) (rowCount : Fin k → ℕ) (columnCount : Role → ℕ) :
    MarginMatrix Role k rowCount columnCount ≃
      { entry : Fin k → Role → ℕ // entry ∈ admissible k rowCount columnCount } where
  toFun m := ⟨m.entry, marginMatrixEquiv_mem k rowCount columnCount m⟩
  invFun e :=
    ⟨e.1, (Finset.mem_filter.mp e.2).2.1, (Finset.mem_filter.mp e.2).2.2⟩
  left_inv _ := MarginMatrix.ext_eq rfl
  right_inv _ := Subtype.ext rfl

instance marginMatrixFintype (k : ℕ) (rowCount : Fin k → ℕ) (columnCount : Role → ℕ) :
    Fintype (MarginMatrix Role k rowCount columnCount) :=
  Fintype.ofEquiv _ (marginMatrixEquiv k rowCount columnCount).symm

/-- **Positive.** Below a row sum of `1` there is room for the entry `0`. -/
theorem zero_mem_entryBound :
    (fun (_ : Fin 1) (_ : Unit) => (0 : ℕ)) ∈ entryBound (Role := Unit) 1 (fun _ => 1) := by
  rw [entryBound, Fintype.mem_piFinset]
  intro _
  rw [Fintype.mem_piFinset]
  intro _
  rw [Finset.mem_range]
  decide

/-- **Negative.** An entry equal to the successor of the row sum is not below it. -/
theorem succ_not_mem_entryBound :
    (fun (_ : Fin 1) (_ : Unit) => (2 : ℕ)) ∉ entryBound (Role := Unit) 1 (fun _ => 1) := by
  intro h
  rw [entryBound, Fintype.mem_piFinset] at h
  have h0 := h 0
  rw [Fintype.mem_piFinset] at h0
  have hrole := h0 ()
  rw [Finset.mem_range] at hrole
  exact Nat.not_lt.mpr (Nat.le_refl 2) hrole

/-- Permuting the rows of a matrix permutes its row sums and preserves the
column sums. -/
def marginRowPermute (k : ℕ) (rowCount : Fin k → ℕ) (columnCount : Role → ℕ)
    (σ : Equiv.Perm (Fin k)) :
    MarginMatrix Role k rowCount columnCount ≃
      MarginMatrix Role k (fun i => rowCount (σ i)) columnCount where
  toFun m :=
    { entry := fun i role => m.entry (σ i) role
      rowSum := fun i => m.rowSum (σ i)
      columnSum := fun role => by
        rw [← m.columnSum role]
        exact Equiv.sum_comp σ fun i => m.entry i role }
  invFun m :=
    { entry := fun i role => m.entry (σ.symm i) role
      rowSum := fun i => by
        have h := m.rowSum (σ.symm i)
        rwa [Equiv.apply_symm_apply] at h
      columnSum := fun role => by
        rw [← m.columnSum role]
        exact Equiv.sum_comp σ.symm fun i => m.entry i role }
  left_inv m := by
    apply MarginMatrix.ext_eq
    funext i role
    exact congrArg (fun j => m.entry j role) (Equiv.apply_symm_apply σ i)
  right_inv m := by
    apply MarginMatrix.ext_eq
    funext i role
    exact congrArg (fun j => m.entry j role) (Equiv.symm_apply_apply σ i)

omit [DecidableEq Role] in
theorem atomSupport_perm {k : ℕ} (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom) :
    atomSupport (fun i => messages (σ i)) outcome = atomSupport messages outcome := by
  ext a
  constructor
  · intro h
    rcases Finset.mem_union.mp h with hmsg | hout
    · rcases Finset.mem_biUnion.mp hmsg with ⟨i, _, hi⟩
      exact mem_atomSupport_of_mem_message (messages := messages) (outcome := outcome)
        (i := σ i) (Multiset.mem_toFinset.mp hi)
    · rcases Finset.mem_biUnion.mp hout with ⟨role, _, ho⟩
      exact mem_atomSupport_of_mem_outcome (messages := messages) (outcome := outcome)
        (Multiset.mem_toFinset.mp ho)
  · intro h
    rcases Finset.mem_union.mp h with hmsg | hout
    · rcases Finset.mem_biUnion.mp hmsg with ⟨i, _, hi⟩
      refine mem_atomSupport_of_mem_message
        (messages := fun j => messages (σ j)) (outcome := outcome) (i := σ.symm i) ?_
      rw [Equiv.apply_symm_apply]
      exact Multiset.mem_toFinset.mp hi
    · rcases Finset.mem_biUnion.mp hout with ⟨role, _, ho⟩
      exact mem_atomSupport_of_mem_outcome
        (messages := fun j => messages (σ j)) (outcome := outcome)
        (Multiset.mem_toFinset.mp ho)

/-- The fibre is the disjoint union of its fixed-ordering slices. -/
def fibreSigmaEquiv {k : ℕ} (messages : Fin k → Message Atom) (outcome : Role → Message Atom) :
    Fibre Atom Role k messages outcome ≃
      Σ σ : Equiv.Perm (Fin k), FibreAt Atom Role k σ messages outcome :=
  (Equiv.sigmaFiberEquiv
    (fun c : Fibre Atom Role k messages outcome => c.1.ordering)).symm

instance matrixFamilyFintype {k : ℕ} (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom) : Fintype (MatrixFamily Atom Role k messages outcome) := by
  unfold MatrixFamily
  infer_instance

instance fibreAtFintype {k : ℕ} (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom) : Fintype (FibreAt Atom Role k σ messages outcome) :=
  Fintype.ofEquiv
    (∀ a : { a : Atom // a ∈ atomSupport (fun i => messages (σ i)) outcome },
      MarginMatrix Role k (fun i => Multiset.count a.1 (messages (σ i)))
        (fun role => Multiset.count a.1 (outcome role)))
    ((fibreAtEquiv σ messages outcome).symm :
      (∀ a : { a : Atom // a ∈ atomSupport (fun i => messages (σ i)) outcome },
        MarginMatrix Role k (fun i => Multiset.count a.1 (messages (σ i)))
          (fun role => Multiset.count a.1 (outcome role))) ≃
        FibreAt Atom Role k σ messages outcome)

noncomputable instance fibreFintype {k : ℕ} (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom) : Fintype (Fibre Atom Role k messages outcome) :=
  Fintype.ofEquiv _ (fibreSigmaEquiv messages outcome).symm

theorem sum_fin2 {α : Type*} [AddCommMonoid α] (f : Fin 2 → α) :
    ∑ i : Fin 2, f i = f 0 + f 1 := by
  have huniv : (Finset.univ : Finset (Fin 2)) = {0, 1} := by
    decide
  rw [huniv, Finset.sum_pair (by decide : (0 : Fin 2) ≠ 1)]

/-- `μ = k! ∏_a T_a`, with `T_a` the number of margin matrices of atom `a` and
the product taken over the atoms that occur. -/
def fibreMultiplicity {k : ℕ} (messages : Fin k → Message Atom) (outcome : Role → Message Atom) :
    ℕ :=
  Nat.factorial k *
    ∏ a ∈ atomSupport messages outcome,
      Fintype.card (MarginMatrix Role k (fun i => Multiset.count a (messages i))
        (fun role => Multiset.count a (outcome role)))

/-- **Positive.** One ordering and the empty support contribute `1!`. -/
theorem empty_multiplicity_one :
    fibreMultiplicity (Atom := Unit) (Role := Unit) emptyMessages zeroOutcome = 1 := by
  have hempty : atomSupport emptyMessages zeroOutcome = (∅ : Finset Unit) := by
    ext a
    cases a
    refine Iff.intro ?_ ?_
    · intro h
      exact False.elim (empty_not_mem_atomSupport h)
    · intro h
      exact False.elim (Finset.notMem_empty () h)
  rw [fibreMultiplicity, hempty, Finset.prod_empty, Nat.factorial_one, Nat.mul_one]

/-- **Negative.** A message that cannot meet the empty outcome has multiplicity `0`,
not `1`. -/
theorem zeroOutcome_multiplicity_zero :
    fibreMultiplicity (Atom := Unit) (Role := Unit) unitMessages zeroOutcome = 0 := by
  have hmem : () ∈ atomSupport unitMessages zeroOutcome :=
    mem_atomSupport_of_mem_message (messages := unitMessages) (outcome := zeroOutcome) (i := 0)
      (Multiset.mem_singleton_self ())
  have hempty : IsEmpty (MarginMatrix Unit 1 (fun _ => Multiset.count () (unitMessages 0))
      (fun _ => Multiset.count () (zeroOutcome ()))) := by
    refine ⟨fun m => ?_⟩
    have hrow := m.rowSum 0
    have hcol := m.columnSum ()
    rw [sum_unit] at hrow
    rw [sum_fin1] at hcol
    have hsame : Multiset.count () (unitMessages 0) = Multiset.count () (zeroOutcome ()) :=
      hrow.symm.trans hcol
    rw [unitMessages_count, zeroOutcome_count] at hsame
    exact Nat.one_ne_zero hsame
  have hcard : Fintype.card (MarginMatrix Unit 1
      (fun i => Multiset.count () (unitMessages i))
      (fun role => Multiset.count () (zeroOutcome role))) = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact hempty
  have hsupport : ∏ a ∈ atomSupport unitMessages zeroOutcome,
      Fintype.card (MarginMatrix Unit 1 (fun i => Multiset.count a (unitMessages i))
        (fun role => Multiset.count a (zeroOutcome role))) = 0 :=
    Finset.prod_eq_zero hmem hcard
  rw [fibreMultiplicity, hsupport, Nat.mul_zero]

theorem fibreAt_card {k : ℕ} (σ : Equiv.Perm (Fin k)) (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom) :
    Fintype.card (FibreAt Atom Role k σ messages outcome) =
      ∏ a ∈ atomSupport (fun i => messages (σ i)) outcome,
        Fintype.card (MarginMatrix Role k (fun i => Multiset.count a (messages (σ i)))
          (fun role => Multiset.count a (outcome role))) := by
  rw [Fintype.card_congr (fibreAtEquiv σ messages outcome)]
  unfold MatrixFamily
  rw [Fintype.card_pi]
  refine (Finset.prod_subtype (atomSupport (fun i => messages (σ i)) outcome)
    (fun _ => Iff.rfl) fun a =>
      Fintype.card (MarginMatrix Role k (fun i => Multiset.count a (messages (σ i)))
        (fun role => Multiset.count a (outcome role)))).symm

theorem fibreAt_card_invariant {k : ℕ} (σ : Equiv.Perm (Fin k))
    (messages : Fin k → Message Atom) (outcome : Role → Message Atom) :
    Fintype.card (FibreAt Atom Role k σ messages outcome) =
      ∏ a ∈ atomSupport messages outcome,
        Fintype.card (MarginMatrix Role k (fun i => Multiset.count a (messages i))
          (fun role => Multiset.count a (outcome role))) := by
  rw [fibreAt_card, atomSupport_perm σ messages outcome]
  refine Finset.prod_congr rfl fun a _ => ?_
  exact Fintype.card_congr
    (marginRowPermute k (fun i => Multiset.count a (messages i))
      (fun role => Multiset.count a (outcome role)) σ).symm

/-- The fibre has `k!` times `∏_a T_a` elements. `Role` is finite and has
decidable equality, and `Atom` has decidable equality. Atoms outside
`atomSupport` are omitted; `offSupport_matrixCount` says each of them
contributes the factor `1`. -/
theorem fibre_card_eq_mu {k : ℕ} (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom) :
    Fintype.card (Fibre Atom Role k messages outcome) =
      fibreMultiplicity messages outcome := by
  rw [Fintype.card_congr (fibreSigmaEquiv messages outcome), Fintype.card_sigma]
  have hsame : ∀ σ : Equiv.Perm (Fin k),
      Fintype.card (FibreAt Atom Role k σ messages outcome) =
        ∏ a ∈ atomSupport messages outcome,
          Fintype.card (MarginMatrix Role k (fun i => Multiset.count a (messages i))
            (fun role => Multiset.count a (outcome role))) :=
    fun σ => fibreAt_card_invariant σ messages outcome
  rw [Finset.sum_congr rfl fun σ _ => hsame σ, Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, fibreMultiplicity, nsmul_eq_mul, Nat.cast_id]

/-- The only matrix with every margin zero is the zero matrix. -/
instance zeroMarginUnique (k : ℕ) : Unique (MarginMatrix Role k (fun _ => 0) (fun _ => 0)) where
  default :=
    { entry := fun _ _ => 0
      rowSum := fun _ => by simp
      columnSum := fun _ => by simp }
  uniq m := by
    apply MarginMatrix.ext_eq
    funext i role
    have hrow := m.rowSum i
    have hle : m.entry i role ≤ ∑ r : Role, m.entry i r :=
      Finset.single_le_sum (f := fun r => m.entry i r) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ role)
    have hz : m.entry i role ≤ 0 := by
      rw [hrow] at hle
      exact hle
    exact Nat.eq_zero_of_le_zero hz

/-- An atom that occurs in no message and in no role of the outcome has exactly
one margin matrix, the zero matrix, so it contributes the factor `1`. -/
theorem offSupport_matrixCount {k : ℕ} (messages : Fin k → Message Atom)
    (outcome : Role → Message Atom) (a : Atom) (ha : a ∉ atomSupport messages outcome) :
    Fintype.card (MarginMatrix Role k (fun i => Multiset.count a (messages i))
      (fun role => Multiset.count a (outcome role))) = 1 := by
  have hrow : (fun i => Multiset.count a (messages i)) = fun _ => 0 :=
    funext fun i => message_count_zero_outside ha i
  have hcol : (fun role => Multiset.count a (outcome role)) = fun _ => 0 :=
    funext fun role => outcome_count_zero_outside ha role
  have hty := congrArg₂ (MarginMatrix Role k) hrow hcol
  exact (Fintype.card_congr (Equiv.cast hty)).trans Fintype.card_unique

/-- A first row of a two-row matrix: it lies under the column sums and has the
prescribed row sum. The second row is then the column-wise remainder. -/
abbrev FirstRow (columnCount : Role → ℕ) (rowSum : ℕ) :=
  { x : Role → ℕ // (∀ role, x role ≤ columnCount role) ∧ ∑ role : Role, x role = rowSum }

/-- **Positive.** The row `(1)` lies under the column sum `2` and sums to `1`. -/
def oneUnderTwo : FirstRow (Role := Unit) (fun _ => 2) 1 where
  val := fun _ => 1
  property := ⟨fun _ => Nat.le_succ 1, by rw [sum_unit]⟩

/-- **Positive.** That row's only entry is `1`. -/
theorem oneUnderTwo_entry : oneUnderTwo.1 () = 1 :=
  rfl

/-- **Negative.** The row `(3)` does not lie under the column sum `2`. -/
theorem three_not_under_two (x : FirstRow (Role := Unit) (fun _ => 2) 1) : x.1 () ≠ 3 := by
  intro h
  have hle := x.2.1 ()
  rw [h] at hle
  exact Nat.not_succ_le_self 2 hle

omit [DecidableEq Role] in
theorem twoRow_toMatrix_row (columnCount : Role → ℕ) (firstRow secondRow : ℕ)
    (hTotal : ∑ role : Role, columnCount role = firstRow + secondRow)
    (x : FirstRow columnCount firstRow) (i : Fin 2) :
    ∑ role : Role,
        (if i = 0 then x.1 role else columnCount role - x.1 role) =
      if i = 0 then firstRow else secondRow := by
  cases i using Fin.cases with
  | zero =>
    rw [if_pos rfl]
    exact x.2.2
  | succ i' =>
    have hi' : i' = (0 : Fin 1) := Subsingleton.elim i' 0
    subst hi'
    have hi : Fin.succ (0 : Fin 1) ≠ (0 : Fin 2) := by decide
    rw [if_neg hi]
    rw [Finset.sum_congr rfl (fun _ _ => if_neg hi)]
    have hsum : ∑ role, ((columnCount role - x.1 role) + x.1 role) =
        ∑ role, columnCount role :=
      Finset.sum_congr rfl fun role _ => Nat.sub_add_cancel (x.2.1 role)
    rw [Finset.sum_add_distrib, x.2.2, hTotal] at hsum
    have hcomm : ∑ role, (columnCount role - x.1 role) + firstRow =
        secondRow + firstRow := by
      rw [hsum, Nat.add_comm]
    exact Nat.add_right_cancel hcomm

/-- With two rows whose sums add to the sum of the column sums, `T_a` is the
number of first rows that lie under the column sums and have the first row sum. -/
def twoRowEquiv (columnCount : Role → ℕ) (firstRow secondRow : ℕ)
    (hTotal : ∑ role : Role, columnCount role = firstRow + secondRow) :
    MarginMatrix Role 2 (fun i => if i = 0 then firstRow else secondRow) columnCount ≃
      FirstRow columnCount firstRow where
  toFun m :=
    ⟨fun role => m.entry 0 role, by
      refine ⟨?_, ?_⟩
      · intro role
        have hcol := m.columnSum role
        rw [sum_fin2] at hcol
        exact le_of_le_of_eq (Nat.le_add_right (m.entry 0 role) (m.entry 1 role)) hcol
      · have hrow := m.rowSum 0
        rw [if_pos rfl] at hrow
        exact hrow⟩
  invFun x :=
    { entry := fun i role => if i = 0 then x.1 role else columnCount role - x.1 role
      rowSum := fun i => twoRow_toMatrix_row columnCount firstRow secondRow hTotal x i
      columnSum := fun role => by
        rw [sum_fin2]
        have hne : (1 : Fin 2) ≠ 0 := by decide
        rw [if_pos rfl, if_neg hne, Nat.add_sub_of_le (x.2.1 role)] }
  left_inv m := by
    apply MarginMatrix.ext_eq
    funext i role
    cases i using Fin.cases with
    | zero => rfl
    | succ i' =>
      have hi' : i' = (0 : Fin 1) := Subsingleton.elim i' 0
      subst hi'
      simp only [if_neg (by decide : Fin.succ (0 : Fin 1) ≠ (0 : Fin 2))]
      have hcol := m.columnSum role
      have hone : (1 : Fin 2) = Fin.succ (0 : Fin 1) := by decide
      rw [sum_fin2, hone] at hcol
      exact (Nat.eq_sub_of_add_eq (by rw [Nat.add_comm, hcol])).symm
  right_inv x := by
    apply Subtype.ext
    funext role
    rfl

theorem twoRow_matrixCount (columnCount : Role → ℕ) (firstRow secondRow : ℕ)
    (hTotal : ∑ role : Role, columnCount role = firstRow + secondRow) :
    Fintype.card (MarginMatrix Role 2 (fun i => if i = 0 then firstRow else secondRow)
        columnCount) =
      @Fintype.card (FirstRow columnCount firstRow)
        (Fintype.ofEquiv _
          (twoRowEquiv columnCount firstRow secondRow hTotal)) :=
  @Fintype.card_congr
    (MarginMatrix Role 2 (fun i => if i = 0 then firstRow else secondRow) columnCount)
    (FirstRow columnCount firstRow)
    inferInstance
    (Fintype.ofEquiv _
      (twoRowEquiv columnCount firstRow secondRow hTotal))
    (twoRowEquiv columnCount firstRow secondRow hTotal)

/-- One atom, two messages each carrying that atom once, and one role receiving
both occurrences. The margins are row sums `(1, 1)` and column sum `2`. -/
def collisionMessages : Fin 2 → Message Unit :=
  fun _ => {()}

/-- **Positive.** Each collision message has one occurrence. -/
theorem collisionMessages_count (i : Fin 2) :
    Multiset.count () (collisionMessages i) = 1 := by
  rw [collisionMessages, message_singleton_count]

/-- **Negative.** A collision message is not empty. -/
theorem collisionMessages_ne_zero (i : Fin 2) : collisionMessages i ≠ 0 := by
  rw [collisionMessages]
  exact message_singleton_ne_zero ()

/-- The outcome role receives both occurrences. -/
def collisionOutcome : Unit → Message Unit :=
  fun _ => 2 • ({()} : Message Unit)

/-- **Positive.** The column sum is `2`. -/
theorem collisionOutcome_count : Multiset.count () (collisionOutcome ()) = 2 := by
  rw [collisionOutcome, Multiset.count_nsmul, message_singleton_count, Nat.mul_one]

/-- **Negative.** The column is not a single occurrence. -/
theorem collisionOutcome_ne_one : Multiset.count () (collisionOutcome ()) ≠ 1 := by
  rw [collisionOutcome_count]
  decide

theorem collision_support :
    atomSupport collisionMessages collisionOutcome = ({()} : Finset Unit) := by
  ext a
  cases a
  refine Iff.intro ?_ ?_
  · intro _
    exact Finset.mem_singleton_self ()
  · intro _
    exact mem_atomSupport_of_mem_message (messages := collisionMessages)
      (outcome := collisionOutcome) (i := 0) (Multiset.mem_singleton_self ())

theorem collision_margins :
    (∀ i, Multiset.count () (collisionMessages i) = 1) ∧
      Multiset.count () (collisionOutcome ()) = 2 :=
  ⟨collisionMessages_count, collisionOutcome_count⟩

def collisionMatrix : MarginMatrix Unit 2 (fun _ => 1) (fun _ => 2) where
  entry := fun _ _ => 1
  rowSum := fun _ => by rw [sum_unit]
  columnSum := fun _ => by
    rw [sum_fin2]

theorem collisionMatrix_entry (m : MarginMatrix Unit 2 (fun _ => 1) (fun _ => 2)) (i : Fin 2) :
    m.entry i () = 1 := by
  have hrow := m.rowSum i
  rwa [sum_unit] at hrow

instance collisionMatrixUnique : Unique (MarginMatrix Unit 2 (fun _ => 1) (fun _ => 2)) where
  default := collisionMatrix
  uniq m := by
    apply MarginMatrix.ext_eq
    funext i role
    cases role
    rw [collisionMatrix_entry m i, collisionMatrix_entry collisionMatrix i]

theorem collision_firstRow_entry (x : FirstRow (Role := Unit) (fun _ => 2) 1) : x.1 () = 1 := by
  have h := x.2.2
  rwa [sum_unit] at h

instance collisionFirstRowUnique : Unique (FirstRow (Role := Unit) (fun _ => 2) 1) where
  default := oneUnderTwo
  uniq x := by
    apply Subtype.ext
    funext role
    cases role
    rw [collision_firstRow_entry x, oneUnderTwo_entry]

/-- At the margins row sums `(1, 1)` and column sum `2`, one atom and one role,
`T_a = 1` and `μ = 2! · 1`, which is `twoBodyMultiplicity`. -/
theorem collision_mu_eq_twoBodyMultiplicity :
    fibreMultiplicity collisionMessages collisionOutcome = twoBodyMultiplicity := by
  have hcard : Fintype.card (MarginMatrix Unit 2
      (fun i => Multiset.count () (collisionMessages i))
      (fun role => Multiset.count () (collisionOutcome role))) = 1 := by
    have hrowFun : (fun i => Multiset.count () (collisionMessages i)) = fun _ => 1 :=
      funext collisionMessages_count
    have hcolFun : (fun role => Multiset.count () (collisionOutcome role)) = fun _ => 2 := by
      funext role
      cases role
      exact collisionOutcome_count
    have hty := congrArg₂ (MarginMatrix Unit 2) hrowFun hcolFun
    exact (Fintype.card_congr (Equiv.cast hty)).trans Fintype.card_unique
  rw [fibreMultiplicity, collision_support, Finset.prod_singleton, hcard,
    twoBodyMultiplicity, twoBodyMatrixCount, Nat.mul_one]

end Mettapedia.Logic.HostingStyles.Weighted
