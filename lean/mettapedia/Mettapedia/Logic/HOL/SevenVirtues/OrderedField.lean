import Mettapedia.Logic.HOL.Semantics.StandardTransport
import Mettapedia.Logic.HOL.CanonicalTheory
import Mathlib.Algebra.Order.CompleteField
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.DeriveCountable

/-!
# Virtue 4, second example: the complete ordered field

The theory of a complete ordered field in simple type theory: one base type
`ι`, the constants `0, 1 : ι`, `+, · : ι ⇒ ι ⇒ ι` and `≤ : ι ⇒ ι ⇒ prop`,
seventeen first-order axioms (field, total order, compatibility) and one
completeness axiom quantified over the predicates `ι ⇒ prop`.

* `isCOF_of_models`: a full-domain model of the axioms is a complete ordered
  field in Mathlib's sense (`IsCOF.toField`, `IsCOF.toCCLO`,
  `IsCOF.isStrictOrderedRing`);
* `categorical`: any two full-domain models are isomorphic by a bijection of
  individuals preserving all five constants (uniqueness of the complete
  ordered field, `LinearOrderedField.inducedOrderRingIso`);
* `models_iff_of_models`: they satisfy the same sentences;
* `realModel_models`: the real numbers are a full-domain model.

Inverses are asserted to exist rather than named by a constant. With a
primitive inverse whose value at `0` the axioms leave open, the theory is no
longer categorical: `inverse_not_categorical` gives two full models on `ℝ`,
with `0⁻¹ = 0` and with `0⁻¹ = 1`, that no bijection preserving the six
constants identifies.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.SevenVirtues.OrderedField

universe w w'

/-! ## The algebraic content -/

/-- A complete ordered field, stated with the five primitive operations. -/
structure IsCOF (R : Type*) (zero one : R) (add mul : R → R → R) (le : R → R → Prop) : Prop where
  add_assoc : ∀ x y z, add (add x y) z = add x (add y z)
  add_comm : ∀ x y, add x y = add y x
  add_zero : ∀ x, add x zero = x
  add_inv : ∀ x, ∃ y, add x y = zero
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  mul_comm : ∀ x y, mul x y = mul y x
  mul_one : ∀ x, mul x one = x
  mul_inv : ∀ x, x ≠ zero → ∃ y, mul x y = one
  zero_ne_one : zero ≠ one
  distrib : ∀ x y z, mul x (add y z) = add (mul x y) (mul x z)
  le_refl : ∀ x, le x x
  le_antisymm : ∀ x y, le x y → le y x → x = y
  le_trans : ∀ x y z, le x y → le y z → le x z
  le_total : ∀ x y, le x y ∨ le y x
  add_mono : ∀ x y z, le x y → le (add x z) (add y z)
  mul_nonneg : ∀ x y, le zero x → le zero y → le zero (mul x y)
  complete : ∀ S : R → Prop, (∃ x, S x) → (∃ b, ∀ x, S x → le x b) →
    ∃ l, (∀ x, S x → le x l) ∧ ∀ b, (∀ x, S x → le x b) → le l b

namespace IsCOF

variable {R : Type*} {zero one : R} {add mul : R → R → R} {le : R → R → Prop}
  (h : IsCOF R zero one add mul le)

include h

/-- A chosen additive inverse. -/
noncomputable def neg (x : R) : R := Classical.choose (h.add_inv x)

theorem add_neg (x : R) : add x (h.neg x) = zero := Classical.choose_spec (h.add_inv x)

open Classical in
/-- A chosen multiplicative inverse, `0` at `0`. -/
noncomputable def inv (x : R) : R :=
  if hx : x = zero then zero else Classical.choose (h.mul_inv x hx)

omit h in
/-- `n • x`. -/
def nsmul (n : ℕ) (x : R) : R := Nat.rec zero (fun _ acc => add acc x) n

/-- `n • x` for integers. -/
noncomputable def zsmul : ℤ → R → R
  | .ofNat n, x => nsmul (add := add) (zero := zero) n x
  | .negSucc n, x => h.neg (nsmul (add := add) (zero := zero) (n + 1) x)

theorem add_cancel_self {a : R} (ha : add a a = a) : a = zero := by
  calc a = add a zero := (h.add_zero a).symm
    _ = add a (add a (h.neg a)) := by rw [h.add_neg]
    _ = add (add a a) (h.neg a) := (h.add_assoc _ _ _).symm
    _ = add a (h.neg a) := by rw [ha]
    _ = zero := h.add_neg a

theorem mul_zero (x : R) : mul x zero = zero := by
  apply h.add_cancel_self
  rw [← h.distrib, h.add_zero]

/-- The field structure. -/
@[instance_reducible]
noncomputable def toField : Field R where
  add := add
  add_assoc := h.add_assoc
  zero := zero
  zero_add := fun x => (h.add_comm _ _).trans (h.add_zero x)
  add_zero := h.add_zero
  nsmul := nsmul (add := add) (zero := zero)
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  add_comm := h.add_comm
  mul := mul
  left_distrib := h.distrib
  right_distrib := fun x y z => by
    change mul (add x y) z = add (mul x z) (mul y z)
    rw [h.mul_comm, h.distrib, h.mul_comm z x, h.mul_comm z y]
  zero_mul := fun x => (h.mul_comm _ _).trans (h.mul_zero x)
  mul_zero := h.mul_zero
  mul_assoc := h.mul_assoc
  one := one
  one_mul := fun x => (h.mul_comm _ _).trans (h.mul_one x)
  mul_one := h.mul_one
  neg := h.neg
  zsmul := h.zsmul
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl
  neg_add_cancel := fun x => (h.add_comm _ _).trans (h.add_neg x)
  inv := h.inv
  exists_pair_ne := ⟨zero, one, h.zero_ne_one⟩
  mul_inv_cancel := fun x hx => by
    change mul x (h.inv x) = one
    have hx' : ¬ x = zero := hx
    rw [inv, dif_neg hx']
    exact Classical.choose_spec (h.mul_inv x hx')
  inv_zero := by
    change h.inv zero = zero
    simp [inv]
  mul_comm := h.mul_comm
  nnqsmul := _
  qsmul := _

/-- The linear order. -/
@[instance_reducible]
noncomputable def toLinearOrder : LinearOrder R where
  le := le
  le_refl := h.le_refl
  le_trans := h.le_trans
  le_antisymm := h.le_antisymm
  le_total := h.le_total
  toDecidableLE := Classical.decRel _

theorem zero_le_one : le zero one := by
  let _ := h.toField
  rcases h.le_total zero one with h01 | h10
  · exact h01
  · exfalso
    have hneg : le zero (h.neg one) := by
      have := h.add_mono one zero (h.neg one) h10
      rwa [h.add_neg, (h.add_comm zero _).trans (h.add_zero _)] at this
    have hsq := h.mul_nonneg _ _ hneg hneg
    have hone : mul (h.neg one) (h.neg one) = one := by
      change (-1 : R) * (-1) = 1
      rw [neg_mul_neg, one_mul]
    rw [hone] at hsq
    exact h.zero_ne_one (h.le_antisymm _ _ hsq h10)

/-- The order is compatible with the ring operations. -/
theorem isStrictOrderedRing :
    letI := h.toField
    letI := h.toLinearOrder
    IsStrictOrderedRing R := by
  let _ := h.toField
  let _ := h.toLinearOrder
  have : IsOrderedAddMonoid R := ⟨fun a b hab c => h.add_mono a b c hab, fun a b hab c => by
    change le (add c a) (add c b)
    rw [h.add_comm c a, h.add_comm c b]
    exact h.add_mono a b c hab⟩
  have : ZeroLEOneClass R := ⟨h.zero_le_one⟩
  exact IsStrictOrderedRing.of_mul_pos fun a b ha hb =>
    lt_of_le_of_ne (h.mul_nonneg a b ha.le hb.le) (Ne.symm (mul_ne_zero ha.ne' hb.ne'))

/-- Least upper bounds of nonempty bounded sets. -/
theorem exists_lub (s : Set R) (hs : s.Nonempty ∧ ∃ b, ∀ x ∈ s, le x b) :
    ∃ l, (∀ x ∈ s, le x l) ∧ ∀ b, (∀ x ∈ s, le x b) → le l b :=
  h.complete (fun x => x ∈ s) hs.1 hs.2

open Classical in
/-- The supremum: the least upper bound when it exists, otherwise `0`. -/
noncomputable def sup (s : Set R) : R :=
  if hs : s.Nonempty ∧ ∃ b, ∀ x ∈ s, le x b then Classical.choose (h.exists_lub s hs) else zero

/-- The conditionally complete linear order. -/
@[instance_reducible]
noncomputable def toCCLO : ConditionallyCompleteLinearOrder R :=
  letI := h.toLinearOrder
  letI : SupSet R := ⟨h.sup⟩
  have hLUB : ∀ s : Set R, BddAbove s → s.Nonempty → IsLUB s (sSup s) := by
    intro s hb hn
    have hs : s.Nonempty ∧ ∃ b, ∀ x ∈ s, le x b :=
      ⟨hn, let ⟨b, hb⟩ := hb; ⟨b, fun x hx => hb hx⟩⟩
    change IsLUB s (h.sup s)
    simp only [sup, dif_pos hs]
    obtain ⟨hup, hleast⟩ := Classical.choose_spec (h.exists_lub s hs)
    exact ⟨fun x hx => hup x hx, fun b hb => hleast b (fun x hx => hb hx)⟩
  have hNoMax : ¬ BddAbove (Set.univ : Set R) := by
    let _ := h.toField
    have := h.isStrictOrderedRing
    rintro ⟨b, hb⟩
    have hle : b + 1 ≤ b := hb (Set.mem_univ _)
    exact absurd hle (not_le.mpr (lt_add_one b))
  have hSupEmpty : sSup (∅ : Set R) = zero := by
    change h.sup ∅ = zero
    simp [sup]
  have hSupUniv : sSup (Set.univ : Set R) = zero := by
    change h.sup Set.univ = zero
    have : ¬ ((Set.univ : Set R).Nonempty ∧ ∃ b, ∀ x ∈ (Set.univ : Set R), le x b) :=
      fun hs => hNoMax (let ⟨b, hb⟩ := hs.2; ⟨b, fun x hx => hb x hx⟩)
    simp only [sup, dif_neg this]
  { h.toLinearOrder, conditionallyCompleteLatticeOfLatticeOfsSup R hLUB with
    csSup_of_not_bddAbove := fun s hs => by
      change h.sup s = h.sup ∅
      have : ¬ (s.Nonempty ∧ ∃ b, ∀ x ∈ s, le x b) :=
        fun hns => hs (let ⟨b, hb⟩ := hns.2; ⟨b, fun x hx => hb x hx⟩)
      simp only [sup, dif_neg this]
      exact hSupEmpty.symm
    csInf_of_not_bddBelow := fun s hs => by
      change sSup (lowerBounds s) = sSup (lowerBounds ∅)
      have hlow : lowerBounds s = ∅ := by
        ext b
        simp only [Set.mem_empty_iff_false, iff_false]
        exact fun hb => hs ⟨b, hb⟩
      rw [hlow, lowerBounds_empty, hSupEmpty, hSupUniv] }

end IsCOF

/-- **Uniqueness of the complete ordered field**, for the five-operation
presentation: two complete ordered fields are isomorphic by a bijection that
preserves zero, one, addition, multiplication and the order. -/
theorem IsCOF.isomorphic {R : Type w} {R' : Type w'}
    {zero one : R} {add mul : R → R → R} {le : R → R → Prop}
    {zero' one' : R'} {add' mul' : R' → R' → R'} {le' : R' → R' → Prop}
    (h : IsCOF R zero one add mul le) (h' : IsCOF R' zero' one' add' mul' le') :
    ∃ e : R ≃ R', e zero = zero' ∧ e one = one' ∧
      (∀ x y, e (add x y) = add' (e x) (e y)) ∧ (∀ x y, e (mul x y) = mul' (e x) (e y)) ∧
      ∀ x y, le' (e x) (e y) ↔ le x y := by
  let _ := h.toField
  let _ := h.toCCLO
  have := h.isStrictOrderedRing
  let _ := h'.toField
  let _ := h'.toCCLO
  have := h'.isStrictOrderedRing
  let e := ConditionallyCompleteLinearOrderedField.inducedOrderRingIso R R'
  exact ⟨e.toEquiv, map_zero e, map_one e, fun x y => map_add e x y, fun x y => map_mul e x y,
    fun x y => map_le_map_iff e⟩

/-! ## The theory in simple type theory -/

/-- The individuals. -/
abbrev ι : Ty Unit := .base ()

/-- Zero, one, addition, multiplication and the order. -/
inductive FieldConst : Ty Unit → Type
  | zero : FieldConst ι
  | one : FieldConst ι
  | add : FieldConst (ι ⇒ ι ⇒ ι)
  | mul : FieldConst (ι ⇒ ι ⇒ ι)
  | le : FieldConst (ι ⇒ ι ⇒ .prop)
  deriving DecidableEq, Countable

section Syntax

variable {Γ : Ctx Unit}

/-- `a + b`. -/
def addT (a b : Term FieldConst Γ ι) : Term FieldConst Γ ι := .app (.app (.const .add) a) b
/-- `a · b`. -/
def mulT (a b : Term FieldConst Γ ι) : Term FieldConst Γ ι := .app (.app (.const .mul) a) b
/-- `a ≤ b`. -/
def leT (a b : Term FieldConst Γ ι) : Formula FieldConst Γ := .app (.app (.const .le) a) b
/-- `0`. -/
def zeroT : Term FieldConst Γ ι := .const .zero
/-- `1`. -/
def oneT : Term FieldConst Γ ι := .const .one

/-- The innermost bound individual. -/
abbrev v0 : Term FieldConst (ι :: Γ) ι := .var .vz
/-- The second innermost bound individual. -/
abbrev v1 {σ : Ty Unit} : Term FieldConst (σ :: ι :: Γ) ι := .var (.vs .vz)
/-- The third innermost bound individual. -/
abbrev v2 {σ ρ : Ty Unit} : Term FieldConst (σ :: ρ :: ι :: Γ) ι := .var (.vs (.vs .vz))

/-- Quantify over one individual. -/
abbrev all1 (b : Formula FieldConst (ι :: Γ)) : Formula FieldConst Γ := .all b

/-- Quantify over one individual, existentially. -/
abbrev ex1 (b : Formula FieldConst (ι :: Γ)) : Formula FieldConst Γ := .ex b

end Syntax

/-- `∀ x y z. (x + y) + z = x + (y + z)`. -/
def axAddAssoc : ClosedFormula FieldConst :=
  all1 (all1 (all1 (.eq (addT (addT v2 v1) v0) (addT v2 (addT v1 v0)))))
/-- `∀ x y. x + y = y + x`. -/
def axAddComm : ClosedFormula FieldConst := all1 (all1 (.eq (addT v1 v0) (addT v0 v1)))
/-- `∀ x. x + 0 = x`. -/
def axAddZero : ClosedFormula FieldConst := all1 (.eq (addT v0 zeroT) v0)
/-- `∀ x. ∃ y. x + y = 0`. -/
def axAddInv : ClosedFormula FieldConst := all1 (ex1 (.eq (addT v1 v0) zeroT))
/-- `∀ x y z. (x · y) · z = x · (y · z)`. -/
def axMulAssoc : ClosedFormula FieldConst :=
  all1 (all1 (all1 (.eq (mulT (mulT v2 v1) v0) (mulT v2 (mulT v1 v0)))))
/-- `∀ x y. x · y = y · x`. -/
def axMulComm : ClosedFormula FieldConst := all1 (all1 (.eq (mulT v1 v0) (mulT v0 v1)))
/-- `∀ x. x · 1 = x`. -/
def axMulOne : ClosedFormula FieldConst := all1 (.eq (mulT v0 oneT) v0)
/-- `∀ x. x ≠ 0 → ∃ y. x · y = 1`. -/
def axMulInv : ClosedFormula FieldConst :=
  all1 (.imp (.not (.eq v0 zeroT)) (ex1 (.eq (mulT v1 v0) oneT)))
/-- `0 ≠ 1`. -/
def axZeroNeOne : ClosedFormula FieldConst := .not (.eq zeroT oneT)
/-- `∀ x y z. x · (y + z) = x · y + x · z`. -/
def axDistrib : ClosedFormula FieldConst :=
  all1 (all1 (all1 (.eq (mulT v2 (addT v1 v0)) (addT (mulT v2 v1) (mulT v2 v0)))))
/-- `∀ x. x ≤ x`. -/
def axLeRefl : ClosedFormula FieldConst := all1 (leT v0 v0)
/-- `∀ x y. x ≤ y → y ≤ x → x = y`. -/
def axLeAntisymm : ClosedFormula FieldConst :=
  all1 (all1 (.imp (leT v1 v0) (.imp (leT v0 v1) (.eq v1 v0))))
/-- `∀ x y z. x ≤ y → y ≤ z → x ≤ z`. -/
def axLeTrans : ClosedFormula FieldConst :=
  all1 (all1 (all1 (.imp (leT v2 v1) (.imp (leT v1 v0) (leT v2 v0)))))
/-- `∀ x y. x ≤ y ∨ y ≤ x`. -/
def axLeTotal : ClosedFormula FieldConst := all1 (all1 (.or (leT v1 v0) (leT v0 v1)))
/-- `∀ x y z. x ≤ y → x + z ≤ y + z`. -/
def axAddMono : ClosedFormula FieldConst :=
  all1 (all1 (all1 (.imp (leT v2 v1) (leT (addT v2 v0) (addT v1 v0)))))
/-- `∀ x y. 0 ≤ x → 0 ≤ y → 0 ≤ x · y`. -/
def axMulNonneg : ClosedFormula FieldConst :=
  all1 (all1 (.imp (leT zeroT v1) (.imp (leT zeroT v0) (leT zeroT (mulT v1 v0)))))
/-- Completeness: `∀ S. (∃ x. S x) → (∃ b. ∀ x. S x → x ≤ b) →
∃ l. (∀ x. S x → x ≤ l) ∧ ∀ b. (∀ x. S x → x ≤ b) → l ≤ b`. -/
def axComplete : ClosedFormula FieldConst :=
  .all (σ := ι ⇒ .prop) (.imp (ex1 (.app (.var (.vs .vz)) (.var .vz)))
    (.imp (ex1 (all1 (.imp (.app (.var (.vs (.vs .vz))) (.var .vz)) (leT v0 v1))))
      (ex1 (.and
        (all1 (.imp (.app (.var (.vs (.vs .vz))) (.var .vz)) (leT v0 v1)))
        (all1 (.imp (all1 (.imp (.app (.var (.vs (.vs (.vs .vz)))) (.var .vz)) (leT v0 v1)))
          (leT v1 v0)))))))

/-- The seventeen first-order axioms and completeness. -/
def axioms : ClosedTheorySet FieldConst :=
  {axAddAssoc, axAddComm, axAddZero, axAddInv, axMulAssoc, axMulComm, axMulOne, axMulInv,
    axZeroNeOne, axDistrib, axLeRefl, axLeAntisymm, axLeTrans, axLeTotal, axAddMono,
    axMulNonneg, axComplete}

section Semantics

variable (M : HenkinModel.{0, 0, w} Unit FieldConst)

/-- Zero of a model. -/
def zeroOf : M.Carrier () := M.constDen .zero
/-- One of a model. -/
def oneOf : M.Carrier () := M.constDen .one
/-- Addition of a model. -/
def addOf : M.Carrier () → M.Carrier () → M.Carrier () := M.constDen .add
/-- Multiplication of a model. -/
def mulOf : M.Carrier () → M.Carrier () → M.Carrier () := M.constDen .mul
/-- The order of a model, as a ULift-valued function. -/
def leFun : M.Carrier () → M.Carrier () → ULift.{max 1 w} Prop := M.constDen .le
/-- The order of a model. -/
def leOf (x y : M.Carrier ()) : Prop := (leFun M x y).down

/-- **A full model of the axioms is a complete ordered field.** -/
theorem isCOF_of_models (full : M.FullDomains) (hM : ∀ ψ ∈ axioms, M.models ψ) :
    IsCOF (M.Carrier ()) (zeroOf M) (oneOf M) (addOf M) (mulOf M) (leOf M) := by
  have b : ∀ x : M.Carrier (), M.adm ι x := fun x => M.base_mem () x
  have ax : ∀ ψ, ψ ∈ axioms → M.models ψ := hM
  refine
    { add_assoc := fun x y z => ax axAddAssoc (by simp [axioms]) x (b x) y (b y) z (b z)
      add_comm := fun x y => ax axAddComm (by simp [axioms]) x (b x) y (b y)
      add_zero := fun x => ax axAddZero (by simp [axioms]) x (b x)
      add_inv := fun x => ?_
      mul_assoc := fun x y z => ax axMulAssoc (by simp [axioms]) x (b x) y (b y) z (b z)
      mul_comm := fun x y => ax axMulComm (by simp [axioms]) x (b x) y (b y)
      mul_one := fun x => ax axMulOne (by simp [axioms]) x (b x)
      mul_inv := fun x hx => ?_
      zero_ne_one := ax axZeroNeOne (by simp [axioms])
      distrib := fun x y z => ax axDistrib (by simp [axioms]) x (b x) y (b y) z (b z)
      le_refl := fun x => ax axLeRefl (by simp [axioms]) x (b x)
      le_antisymm := fun x y => ax axLeAntisymm (by simp [axioms]) x (b x) y (b y)
      le_trans := fun x y z => ax axLeTrans (by simp [axioms]) x (b x) y (b y) z (b z)
      le_total := fun x y => ax axLeTotal (by simp [axioms]) x (b x) y (b y)
      add_mono := fun x y z => ax axAddMono (by simp [axioms]) x (b x) y (b y) z (b z)
      mul_nonneg := fun x y => ax axMulNonneg (by simp [axioms]) x (b x) y (b y)
      complete := fun S hS hB => ?_ }
  · obtain ⟨y, _, hy⟩ := ax axAddInv (by simp [axioms]) x (b x)
    exact ⟨y, hy⟩
  · obtain ⟨y, _, hy⟩ := ax axMulInv (by simp [axioms]) x (b x) hx
    exact ⟨y, hy⟩
  · have hc := ax axComplete (by simp [axioms])
    obtain ⟨x₀, hx₀⟩ := hS
    obtain ⟨b₀, hb₀⟩ := hB
    obtain ⟨l, _, hup, hleast⟩ := hc (fun x => ULift.up (S x)) (full _ _) ⟨x₀, b x₀, hx₀⟩
      ⟨b₀, b b₀, fun x _ hx => hb₀ x hx⟩
    exact ⟨l, fun x hx => hup x (b x) hx, fun c hc' => hleast c (b c) (fun x _ hx => hc' x hx)⟩

end Semantics

/-- **Categoricity** (Huntington 1903). Two full models of the axioms are
isomorphic by a bijection of individuals preserving the five constants. -/
theorem categorical (M : HenkinModel.{0, 0, w} Unit FieldConst)
    (N : HenkinModel.{0, 0, w'} Unit FieldConst) (fullM : M.FullDomains) (fullN : N.FullDomains)
    (hM : ∀ ψ ∈ axioms, M.models ψ) (hN : ∀ ψ ∈ axioms, N.models ψ) :
    ∃ e : M.Carrier () ≃ N.Carrier (), e (zeroOf M) = zeroOf N ∧ e (oneOf M) = oneOf N ∧
      (∀ x y, e (addOf M x y) = addOf N (e x) (e y)) ∧
      (∀ x y, e (mulOf M x y) = mulOf N (e x) (e y)) ∧
      ∀ x y, leOf N (e x) (e y) ↔ leOf M x y :=
  (isCOF_of_models M fullM hM).isomorphic (isCOF_of_models N fullN hN)

/-- Two full models of the axioms satisfy the same sentences. -/
theorem models_iff_of_models (M : HenkinModel.{0, 0, w} Unit FieldConst)
    (N : HenkinModel.{0, 0, w'} Unit FieldConst) (fullM : M.FullDomains) (fullN : N.FullDomains)
    (hM : ∀ ψ ∈ axioms, M.models ψ) (hN : ∀ ψ ∈ axioms, N.models ψ)
    (φ : ClosedFormula FieldConst) : M.models φ ↔ N.models φ := by
  obtain ⟨e, hzero, hone, hadd, hmul, hle⟩ := categorical M N fullM fullN hM hN
  refine (StandardTransport.models_transport M N fullM fullN (fun _ => e) ?_ φ).symm
  intro τ c
  cases c with
  | zero => exact hzero
  | one => exact hone
  | add =>
      funext x y
      change e (addOf M (e.symm x) (e.symm y)) = addOf N x y
      rw [hadd]
      exact congrArg₂ (addOf N) (e.apply_symm_apply x) (e.apply_symm_apply y)
  | mul =>
      funext x y
      change e (mulOf M (e.symm x) (e.symm y)) = mulOf N x y
      rw [hmul]
      exact congrArg₂ (mulOf N) (e.apply_symm_apply x) (e.apply_symm_apply y)
  | le =>
      funext x y
      apply ULift.ext
      change leOf M (e.symm x) (e.symm y) = leOf N x y
      apply propext
      rw [← hle]
      exact Iff.of_eq (congrArg₂ (leOf N) (e.apply_symm_apply x) (e.apply_symm_apply y))

/-- The converse of `isCOF_of_models`: a complete ordered field structure on a
model's operations makes it satisfy the axioms. -/
theorem models_of_isCOF (M : HenkinModel.{0, 0, w} Unit FieldConst)
    (h : IsCOF (M.Carrier ()) (zeroOf M) (oneOf M) (addOf M) (mulOf M) (leOf M)) :
    ∀ ψ ∈ axioms, M.models ψ := by
  intro ψ hψ
  simp only [axioms, Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
  rcases hψ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · intro x _ y _ z _; exact h.add_assoc x y z
  · intro x _ y _; exact h.add_comm x y
  · intro x _; exact h.add_zero x
  · intro x _
    obtain ⟨y, hy⟩ := h.add_inv x
    exact ⟨y, M.base_mem () y, hy⟩
  · intro x _ y _ z _; exact h.mul_assoc x y z
  · intro x _ y _; exact h.mul_comm x y
  · intro x _; exact h.mul_one x
  · intro x _ hx
    obtain ⟨y, hy⟩ := h.mul_inv x hx
    exact ⟨y, M.base_mem () y, hy⟩
  · exact h.zero_ne_one
  · intro x _ y _ z _; exact h.distrib x y z
  · intro x _; exact h.le_refl x
  · intro x _ y _; exact h.le_antisymm x y
  · intro x _ y _ z _; exact h.le_trans x y z
  · intro x _ y _; exact h.le_total x y
  · intro x _ y _ z _; exact h.add_mono x y z
  · intro x _ y _; exact h.mul_nonneg x y
  · intro S _ hne hbdd
    obtain ⟨x, _, hx⟩ := hne
    obtain ⟨b, _, hb⟩ := hbdd
    obtain ⟨l, hup, hleast⟩ := h.complete (fun x => (S x).down) ⟨x, hx⟩
      ⟨b, fun y hy => hb y (M.base_mem () y) hy⟩
    exact ⟨l, M.base_mem () l, fun y _ hy => hup y hy,
      fun c _ hc => hleast c (fun y hy => hc y (M.base_mem () y) hy)⟩

/-- The interpretation of the five constants on the real numbers. -/
def realConstDen : {τ : Ty Unit} → FieldConst τ → Ty.denote.{0, 0} (fun _ => ULift.{1} ℝ) τ
  | _, .zero => (⟨0⟩ : ULift.{1} ℝ)
  | _, .one => (⟨1⟩ : ULift.{1} ℝ)
  | _, .add => fun x y : ULift.{1} ℝ => (⟨x.down + y.down⟩ : ULift.{1} ℝ)
  | _, .mul => fun x y : ULift.{1} ℝ => (⟨x.down * y.down⟩ : ULift.{1} ℝ)
  | _, .le => fun x y : ULift.{1} ℝ => ULift.up (x.down ≤ y.down)

/-- The standard model of the real numbers. -/
def realModel : HenkinModel.{0, 0, 0} Unit FieldConst :=
  HenkinModel.standard (fun _ => ULift.{1} ℝ) realConstDen

theorem realModel_fullDomains : realModel.FullDomains := HenkinModel.fullDomains_standard _ _

/-- The real numbers are a complete ordered field in the five-operation
presentation. -/
theorem real_isCOF :
    IsCOF (realModel.Carrier ()) (zeroOf realModel) (oneOf realModel) (addOf realModel)
      (mulOf realModel) (leOf realModel) := by
  refine
    { add_assoc := fun x y z => ULift.ext _ _ (add_assoc x.down y.down z.down)
      add_comm := fun x y => ULift.ext _ _ (add_comm x.down y.down)
      add_zero := fun x => ULift.ext _ _ (add_zero x.down)
      add_inv := fun x => ⟨⟨-x.down⟩, ULift.ext _ _ (add_neg_cancel x.down)⟩
      mul_assoc := fun x y z => ULift.ext _ _ (mul_assoc x.down y.down z.down)
      mul_comm := fun x y => ULift.ext _ _ (mul_comm x.down y.down)
      mul_one := fun x => ULift.ext _ _ (mul_one x.down)
      mul_inv := fun x hx => ⟨⟨x.down⁻¹⟩, ULift.ext _ _ (mul_inv_cancel₀ fun h0 =>
        hx (ULift.ext _ _ h0))⟩
      zero_ne_one := fun h01 => zero_ne_one (congrArg ULift.down h01)
      distrib := fun x y z => ULift.ext _ _ (mul_add x.down y.down z.down)
      le_refl := fun x => le_refl x.down
      le_antisymm := fun x y hxy hyx => ULift.ext _ _ (le_antisymm hxy hyx)
      le_trans := fun x y z hxy hyz => le_trans (a := x.down) hxy hyz
      le_total := fun x y => le_total x.down y.down
      add_mono := fun x y z hxy => by
        change x.down + z.down ≤ y.down + z.down
        have hxy' : x.down ≤ y.down := hxy
        linarith
      mul_nonneg := fun x y hx hy => mul_nonneg (a := x.down) (b := y.down) hx hy
      complete := fun S hS hB => ?_ }
  obtain ⟨⟨x₀⟩, hx₀⟩ := hS
  obtain ⟨⟨b₀⟩, hb₀⟩ := hB
  obtain ⟨l, hl⟩ := Real.exists_isLUB (s := {r : ℝ | S ⟨r⟩}) ⟨x₀, hx₀⟩
    ⟨b₀, fun r hr => hb₀ ⟨r⟩ hr⟩
  exact ⟨⟨l⟩, fun x hx => hl.1 hx, fun c hc => hl.2 (fun r hr => hc ⟨r⟩ hr)⟩

theorem realModel_models : ∀ ψ ∈ axioms, realModel.models ψ :=
  models_of_isCOF realModel real_isCOF

/-- **Every full model is the real numbers**, up to a bijection preserving the
five constants. -/
theorem full_model_is_real (M : HenkinModel.{0, 0, w} Unit FieldConst) (full : M.FullDomains)
    (hM : ∀ ψ ∈ axioms, M.models ψ) :
    ∃ e : M.Carrier () ≃ realModel.Carrier (), e (zeroOf M) = zeroOf realModel ∧
      e (oneOf M) = oneOf realModel ∧
      (∀ x y, e (addOf M x y) = addOf realModel (e x) (e y)) ∧
      (∀ x y, e (mulOf M x y) = mulOf realModel (e x) (e y)) ∧
      ∀ x y, leOf realModel (e x) (e y) ↔ leOf M x y :=
  categorical M realModel full realModel_fullDomains hM realModel_models

/-- **A primitive inverse breaks categoricity.** Two expansions of the real
numbers by an inverse operation, `0⁻¹ = 0` and `0⁻¹ = 1`, both satisfy
`x ≠ 0 → x · x⁻¹ = 1`, yet no bijection preserves zero and the inverse. -/
theorem inverse_expansions_not_isomorphic :
    (∀ x : ℝ, x ≠ 0 → x * x⁻¹ = 1) ∧
      (∀ x : ℝ, x ≠ 0 → x * (if x = 0 then 1 else x⁻¹) = 1) ∧
      ¬ ∃ e : ℝ ≃ ℝ, e 0 = 0 ∧ ∀ x, e x⁻¹ = if e x = 0 then 1 else (e x)⁻¹ := by
  refine ⟨fun x hx => mul_inv_cancel₀ hx, fun x hx => by simp [hx], ?_⟩
  rintro ⟨e, hzero, hinv⟩
  have := hinv 0
  rw [inv_zero, hzero, if_pos rfl] at this
  exact zero_ne_one this

#print axioms IsCOF.isomorphic
#print axioms isCOF_of_models
#print axioms categorical
#print axioms models_iff_of_models
#print axioms realModel_models
#print axioms full_model_is_real
#print axioms inverse_expansions_not_isomorphic

end Mettapedia.Logic.HOL.SevenVirtues.OrderedField
