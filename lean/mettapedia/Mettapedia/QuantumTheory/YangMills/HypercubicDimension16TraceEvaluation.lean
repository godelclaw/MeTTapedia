import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalInvariantSpace
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Matrix trace evaluation on field-label orbits

A trace permutation decorated by two-by-two matrices is evaluated by the
standard contraction of its matrix indices.  The contraction is unchanged
by simultaneous relabeling of every field, so it descends to the genuine
field-label orbit carrier and extends linearly to its free module.

This is the ordinary matrix semantics of the trace carrier.  No relation is
put into the definition of the evaluation.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16TraceEvaluation

open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16PhysicalInvariantSpace
open V14HypercubicFDCensus
open V14HypercubicQuarticCensus
open SU2LatticeFDCensusNoGo
open HypercubicDimension16SU2TraceRelations
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16IBPTraceRelations

/-! ## Standard index contraction -/

/-- Matrix-index contraction associated with a permutation of the decorated
field labels.  Each field supplies the matrix entry on its outgoing trace
edge. -/
def tracePermutationContraction
    {Label R : Type*} [Fintype Label] [DecidableEq Label]
    [CommSemiring R]
    (matrixAt : Label → Matrix (Fin 2) (Fin 2) R)
    (traceOrder : Equiv.Perm Label) : R :=
  ∑ state : Label → Fin 2,
    ∏ field : Label,
      matrixAt field (state field) (state (traceOrder field))

/-- Relabeling a matrix-index state by a permutation of its field labels. -/
def relabelMatrixIndexState {Label : Type*}
    (rename : Equiv.Perm Label) :
    (Label → Fin 2) ≃ (Label → Fin 2) :=
  Equiv.arrowCongr rename (Equiv.refl _)

@[simp] theorem relabelMatrixIndexState_apply
    {Label : Type*} (rename : Equiv.Perm Label)
    (state : Label → Fin 2) (field : Label) :
    relabelMatrixIndexState rename state field =
      state (rename.symm field) := by
  rfl

/-- The standard trace contraction is unchanged by simultaneous relabeling
of the matrices and conjugation of the trace permutation. -/
theorem tracePermutationContraction_relabel
    {Label R : Type*} [Fintype Label] [DecidableEq Label]
    [CommSemiring R]
    (rename : Equiv.Perm Label)
    (matrixAt : Label → Matrix (Fin 2) (Fin 2) R)
    (traceOrder : Equiv.Perm Label) :
    tracePermutationContraction (matrixAt ∘ rename.symm)
        (rename.symm.trans (traceOrder.trans rename)) =
      tracePermutationContraction matrixAt traceOrder := by
  let summand : (Label → Fin 2) → R := fun state =>
    ∏ field : Label,
      (matrixAt ∘ rename.symm) field
        (state field)
        (state ((rename.symm.trans (traceOrder.trans rename)) field))
  calc
    tracePermutationContraction (matrixAt ∘ rename.symm)
        (rename.symm.trans (traceOrder.trans rename)) =
        ∑ state : Label → Fin 2, summand state := rfl
    _ = ∑ state : Label → Fin 2,
          summand (relabelMatrixIndexState rename state) := by
      exact (Equiv.sum_comp (relabelMatrixIndexState rename) summand).symm
    _ = ∑ state : Label → Fin 2,
          ∏ field : Label,
            matrixAt field (state field) (state (traceOrder field)) := by
      apply Finset.sum_congr rfl
      intro state _
      unfold summand
      simp only [Function.comp_apply, relabelMatrixIndexState_apply,
        Equiv.trans_apply, Equiv.symm_apply_apply]
      change (∏ field : Label,
          matrixAt (rename.symm field)
            (state (rename.symm field))
            (state (traceOrder (rename.symm field)))) =
        ∏ field : Label,
          matrixAt field (state field) (state (traceOrder field))
      exact Equiv.prod_comp rename.symm
        (fun field =>
          matrixAt field (state field) (state (traceOrder field)))
    _ = tracePermutationContraction matrixAt traceOrder := rfl

/-! ## Removing a fixed trace point -/

abbrev AwayFrom {Label : Type*} (pivot : Label) :=
  {field : Label // field ≠ pivot}

/-- Split one matrix-index state into its value at `pivot` and its values on
the complementary labels. -/
def splitMatrixIndexState {Label : Type*} [DecidableEq Label]
    (pivot : Label) :
    (Label → Fin 2) ≃ (Fin 2 × (AwayFrom pivot → Fin 2)) where
  toFun state := (state pivot, fun field => state field.1)
  invFun data field :=
    if h : field = pivot then data.1 else data.2 ⟨field, h⟩
  left_inv state := by
    funext field
    by_cases h : field = pivot
    · subst field
      simp
    · simp [h]
  right_inv data := by
    apply Prod.ext
    · simp
    · funext field
      simp [field.2]

@[simp] theorem splitMatrixIndexState_apply_fst
    {Label : Type*} [DecidableEq Label]
    (pivot : Label) (state : Label → Fin 2) :
    (splitMatrixIndexState pivot state).1 = state pivot := by
  rfl

@[simp] theorem splitMatrixIndexState_apply_snd
    {Label : Type*} [DecidableEq Label]
    (pivot : Label) (state : Label → Fin 2)
    (field : AwayFrom pivot) :
    (splitMatrixIndexState pivot state).2 field = state field.1 := by
  rfl

@[simp] theorem splitMatrixIndexState_symm_apply_pivot
    {Label : Type*} [DecidableEq Label]
    (pivot : Label) (value : Fin 2)
    (rest : AwayFrom pivot → Fin 2) :
    (splitMatrixIndexState pivot).symm (value, rest) pivot = value := by
  simp [splitMatrixIndexState]

@[simp] theorem splitMatrixIndexState_symm_apply_away
    {Label : Type*} [DecidableEq Label]
    (pivot : Label) (value : Fin 2)
    (rest : AwayFrom pivot → Fin 2)
    (field : AwayFrom pivot) :
    (splitMatrixIndexState pivot).symm (value, rest) field.1 = rest field := by
  simp [splitMatrixIndexState, field.2]

/-- A trace permutation fixing `pivot` restricts to its complementary
labels. -/
def fixedPointComplementPerm
    {Label : Type*} [DecidableEq Label]
    (traceOrder : Equiv.Perm Label) (pivot : Label)
    (hfixed : traceOrder pivot = pivot) :
    Equiv.Perm (AwayFrom pivot) where
  toFun field :=
    ⟨traceOrder field.1, by
      intro heq
      apply field.2
      apply traceOrder.injective
      rw [heq, hfixed]⟩
  invFun field :=
    ⟨traceOrder.symm field.1, by
      intro heq
      apply field.2
      have := congrArg traceOrder heq
      simpa [hfixed] using this⟩
  left_inv field := by
    apply Subtype.ext
    exact traceOrder.symm_apply_apply field.1
  right_inv field := by
    apply Subtype.ext
    exact traceOrder.apply_symm_apply field.1

@[simp] theorem fixedPointComplementPerm_apply
    {Label : Type*} [DecidableEq Label]
    (traceOrder : Equiv.Perm Label) (pivot : Label)
    (hfixed : traceOrder pivot = pivot)
    (field : AwayFrom pivot) :
    (fixedPointComplementPerm traceOrder pivot hfixed field).1 =
      traceOrder field.1 :=
  rfl

/-- A fixed one-letter trace factors as the ordinary matrix trace times the
contraction on all remaining trace cycles. -/
theorem tracePermutationContraction_fixedPoint
    {Label R : Type*} [Fintype Label] [DecidableEq Label]
    [CommSemiring R]
    (matrixAt : Label → Matrix (Fin 2) (Fin 2) R)
    (traceOrder : Equiv.Perm Label) (pivot : Label)
    (hfixed : traceOrder pivot = pivot) :
    tracePermutationContraction matrixAt traceOrder =
      Matrix.trace (matrixAt pivot) *
        tracePermutationContraction
          (fun field : AwayFrom pivot => matrixAt field.1)
          (fixedPointComplementPerm traceOrder pivot hfixed) := by
  let summand : (Label → Fin 2) → R := fun state =>
    ∏ field : Label,
      matrixAt field (state field) (state (traceOrder field))
  calc
    tracePermutationContraction matrixAt traceOrder =
        ∑ state : Label → Fin 2, summand state := rfl
    _ = ∑ data : Fin 2 × (AwayFrom pivot → Fin 2),
          summand ((splitMatrixIndexState pivot).symm data) := by
      exact (Equiv.sum_comp (splitMatrixIndexState pivot).symm summand).symm
    _ = ∑ data : Fin 2 × (AwayFrom pivot → Fin 2),
          matrixAt pivot data.1 data.1 *
            (∏ field : AwayFrom pivot,
              matrixAt field.1 (data.2 field)
                (data.2
                  (fixedPointComplementPerm traceOrder pivot hfixed field))) := by
      apply Finset.sum_congr rfl
      rintro ⟨value, rest⟩ _
      unfold summand
      rw [Fintype.prod_eq_mul_prod_subtype_ne _ pivot]
      congr 1
      · simp [hfixed]
      · apply Finset.prod_congr rfl
        intro field _
        rw [splitMatrixIndexState_symm_apply_away pivot value rest field]
        change matrixAt field.1 (rest field)
            ((splitMatrixIndexState pivot).symm (value, rest)
              (fixedPointComplementPerm traceOrder pivot hfixed field).1) =
          matrixAt field.1 (rest field)
            (rest (fixedPointComplementPerm traceOrder pivot hfixed field))
        rw [splitMatrixIndexState_symm_apply_away]
    _ = (∑ value : Fin 2, matrixAt pivot value value) *
          (∑ rest : AwayFrom pivot → Fin 2,
            ∏ field : AwayFrom pivot,
              matrixAt field.1 (rest field)
                (rest
                  (fixedPointComplementPerm traceOrder pivot hfixed field))) := by
      rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
    _ = Matrix.trace (matrixAt pivot) *
          tracePermutationContraction
            (fun field : AwayFrom pivot => matrixAt field.1)
            (fixedPointComplementPerm traceOrder pivot hfixed) := by
      rfl

/-! ## Splitting three distinguished trace sources -/

abbrev AwayFromThree {Label : Type*}
    (first second third : Label) :=
  {field : Label //
    field ≠ first ∧ field ≠ second ∧ field ≠ third}

structure ThreeIndexState {Label : Type*}
    (first second third : Label) where
  atFirst : Fin 2
  atSecond : Fin 2
  atThird : Fin 2
  away : AwayFromThree first second third → Fin 2

def threeIndexStateEquivProd
    {Label : Type*} (first second third : Label) :
    (Fin 2 × Fin 2 × Fin 2 ×
        (AwayFromThree first second third → Fin 2)) ≃
      ThreeIndexState first second third where
  toFun data :=
    { atFirst := data.1
      atSecond := data.2.1
      atThird := data.2.2.1
      away := data.2.2.2 }
  invFun data :=
    (data.atFirst, data.atSecond, data.atThird, data.away)
  left_inv data := by rcases data with ⟨firstValue, secondValue,
    thirdValue, away⟩; rfl
  right_inv data := by rcases data with ⟨firstValue, secondValue,
    thirdValue, away⟩; rfl

noncomputable instance threeIndexStateFintype
    {Label : Type*} [Fintype Label] [DecidableEq Label]
    (first second third : Label) :
    Fintype (ThreeIndexState first second third) :=
  Fintype.ofEquiv
    (Fin 2 × Fin 2 × Fin 2 ×
      (AwayFromThree first second third → Fin 2))
    (threeIndexStateEquivProd first second third)

@[ext] theorem ThreeIndexState.ext
    {Label : Type*} {first second third : Label}
    (left right : ThreeIndexState first second third)
    (hfirst : left.atFirst = right.atFirst)
    (hsecond : left.atSecond = right.atSecond)
    (hthird : left.atThird = right.atThird)
    (haway : left.away = right.away) :
    left = right := by
  cases left
  cases right
  simp_all

/-- Split a state into three selected values and its restriction to the
complement. -/
def splitThreeMatrixIndexState
    {Label : Type*} [DecidableEq Label]
    (first second third : Label)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    (Label → Fin 2) ≃ ThreeIndexState first second third where
  toFun state :=
    { atFirst := state first
      atSecond := state second
      atThird := state third
      away := fun field => state field.1 }
  invFun data field :=
    if hfirst : field = first then data.atFirst
    else if hsecond : field = second then data.atSecond
    else if hthird : field = third then data.atThird
    else data.away ⟨field, hfirst, hsecond, hthird⟩
  left_inv state := by
    funext field
    by_cases hfirst : field = first
    · subst field
      simp
    · by_cases hsecond : field = second
      · subst field
        simp [hfirstSecond.symm]
      · by_cases hthird : field = third
        · subst field
          simp [hfirstThird.symm, hsecondThird.symm]
        · simp [hfirst, hsecond, hthird]
  right_inv data := by
    cases data with
    | mk atFirst atSecond atThird away =>
        apply ThreeIndexState.ext
        · simp
        · simp [hfirstSecond.symm]
        · simp [hfirstThird.symm,
            hsecondThird.symm]
        · funext field
          simp [field.2.1,
            field.2.2.1, field.2.2.2]

@[simp] theorem splitThreeMatrixIndexState_symm_apply_first
    {Label : Type*} [DecidableEq Label]
    (first second third : Label)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (data : ThreeIndexState first second third) :
    (splitThreeMatrixIndexState first second third
      hfirstSecond hfirstThird hsecondThird).symm data first =
        data.atFirst := by
  simp [splitThreeMatrixIndexState]

@[simp] theorem splitThreeMatrixIndexState_symm_apply_second
    {Label : Type*} [DecidableEq Label]
    (first second third : Label)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (data : ThreeIndexState first second third) :
    (splitThreeMatrixIndexState first second third
      hfirstSecond hfirstThird hsecondThird).symm data second =
        data.atSecond := by
  simp [splitThreeMatrixIndexState, hfirstSecond.symm]

@[simp] theorem splitThreeMatrixIndexState_symm_apply_third
    {Label : Type*} [DecidableEq Label]
    (first second third : Label)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (data : ThreeIndexState first second third) :
    (splitThreeMatrixIndexState first second third
      hfirstSecond hfirstThird hsecondThird).symm data third =
        data.atThird := by
  simp [splitThreeMatrixIndexState, hfirstThird.symm,
    hsecondThird.symm]

@[simp] theorem splitThreeMatrixIndexState_symm_apply_away
    {Label : Type*} [DecidableEq Label]
    (first second third : Label)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (data : ThreeIndexState first second third)
    (field : AwayFromThree first second third) :
    (splitThreeMatrixIndexState first second third
      hfirstSecond hfirstThird hsecondThird).symm data field.1 =
        data.away field := by
  simp [splitThreeMatrixIndexState, field.2.1, field.2.2.1,
    field.2.2.2]

/-- A finite commutative product factors into three distinct selected terms
and the product over their complement. -/
theorem fintype_prod_eq_three_mul_away
    {Label M : Type*} [Fintype Label] [DecidableEq Label]
    [CommMonoid M]
    (term : Label → M) (first second third : Label)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    (∏ field : Label, term field) =
      term first * term second * term third *
        ∏ field : AwayFromThree first second third, term field.1 := by
  let rest : Finset Label := Finset.univ.filter fun field =>
    field ≠ first ∧ field ≠ second ∧ field ≠ third
  have huniv :
      (Finset.univ : Finset Label) =
        insert first (insert second (insert third rest)) := by
    ext field
    simp only [Finset.mem_univ, Finset.mem_insert, true_iff]
    by_cases hfirst : field = first
    · exact Or.inl hfirst
    · by_cases hsecond : field = second
      · exact Or.inr (Or.inl hsecond)
      · by_cases hthird : field = third
        · exact Or.inr (Or.inr (Or.inl hthird))
        · exact Or.inr (Or.inr (Or.inr (by
            simp [rest, hfirst, hsecond, hthird])))
  have hfirstRest : first ∉ rest := by simp [rest]
  have hsecondRest : second ∉ rest := by simp [rest]
  have hthirdRest : third ∉ rest := by simp [rest]
  have hsecondInsert : second ∉ insert third rest := by
    simp [hsecondThird, hsecondRest]
  have hfirstInsert : first ∉ insert second (insert third rest) := by
    simp [hfirstSecond, hfirstThird, hfirstRest]
  have hrest :
      (∏ field ∈ rest, term field) =
        ∏ field : AwayFromThree first second third, term field.1 := by
    apply Finset.prod_subtype rest
    intro field
    simp [rest]
  change (∏ field ∈ (Finset.univ : Finset Label), term field) = _
  rw [huniv, Finset.prod_insert hfirstInsert,
    Finset.prod_insert hsecondInsert,
    Finset.prod_insert hthirdRest, hrest]
  ac_rfl

def threeSourceOutsideProduct
    {Label R : Type*} [Fintype Label] [DecidableEq Label]
    [CommSemiring R]
    (matrixAt : Label → Matrix (Fin 2) (Fin 2) R)
    (traceOrder : Equiv.Perm Label)
    (first second third : Label)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (data : ThreeIndexState first second third) : R :=
  ∏ field : AwayFromThree first second third,
    matrixAt field.1 (data.away field)
      ((splitThreeMatrixIndexState first second third
        hfirstSecond hfirstThird hsecondThird).symm data
          (traceOrder field.1))

/-- Expansion of a trace contraction after isolating three distinct outgoing
trace edges. -/
theorem tracePermutationContraction_splitThree
    {Label R : Type*} [Fintype Label] [DecidableEq Label]
    [CommSemiring R]
    (matrixAt : Label → Matrix (Fin 2) (Fin 2) R)
    (traceOrder : Equiv.Perm Label)
    (first second third : Label)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    tracePermutationContraction matrixAt traceOrder =
      ∑ data : ThreeIndexState first second third,
        let state :=
          (splitThreeMatrixIndexState first second third
            hfirstSecond hfirstThird hsecondThird).symm data
        matrixAt first data.atFirst (state (traceOrder first)) *
          matrixAt second data.atSecond (state (traceOrder second)) *
          matrixAt third data.atThird (state (traceOrder third)) *
          threeSourceOutsideProduct matrixAt traceOrder
            first second third hfirstSecond hfirstThird hsecondThird data := by
  let split := splitThreeMatrixIndexState first second third
    hfirstSecond hfirstThird hsecondThird
  let summand : (Label → Fin 2) → R := fun state =>
    ∏ field : Label,
      matrixAt field (state field) (state (traceOrder field))
  calc
    tracePermutationContraction matrixAt traceOrder =
        ∑ state : Label → Fin 2, summand state := rfl
    _ = ∑ data : ThreeIndexState first second third,
          summand (split.symm data) := by
      exact (Equiv.sum_comp split.symm summand).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro data _
      unfold summand threeSourceOutsideProduct
      rw [fintype_prod_eq_three_mul_away _ first second third
        hfirstSecond hfirstThird hsecondThird]
      simp only [split, splitThreeMatrixIndexState_symm_apply_first,
        splitThreeMatrixIndexState_symm_apply_second,
        splitThreeMatrixIndexState_symm_apply_third]
      congr 1
      apply Finset.prod_congr rfl
      intro field _
      rw [splitThreeMatrixIndexState_symm_apply_away]

/-- A target-label rewire is supported on three selected labels. -/
def FixesOutsideThree {Label : Type*}
    (rewire : Equiv.Perm Label) (first second third : Label) : Prop :=
  ∀ target, target ≠ first → target ≠ second → target ≠ third →
    rewire target = target

theorem threeSourceOutsideProduct_trans_rewire
    {Label R : Type*} [Fintype Label] [DecidableEq Label]
    [CommSemiring R]
    (matrixAt : Label → Matrix (Fin 2) (Fin 2) R)
    (traceOrder rewire : Equiv.Perm Label)
    (first second third : Label)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hfix : FixesOutsideThree rewire first second third)
    (data : ThreeIndexState
      (traceOrder.symm first) (traceOrder.symm second)
        (traceOrder.symm third)) :
    threeSourceOutsideProduct matrixAt (traceOrder.trans rewire)
        (traceOrder.symm first) (traceOrder.symm second)
        (traceOrder.symm third)
        (traceOrder.symm.injective.ne hfirstSecond)
        (traceOrder.symm.injective.ne hfirstThird)
        (traceOrder.symm.injective.ne hsecondThird) data =
      threeSourceOutsideProduct matrixAt traceOrder
        (traceOrder.symm first) (traceOrder.symm second)
        (traceOrder.symm third)
        (traceOrder.symm.injective.ne hfirstSecond)
        (traceOrder.symm.injective.ne hfirstThird)
        (traceOrder.symm.injective.ne hsecondThird) data := by
  unfold threeSourceOutsideProduct
  apply Finset.prod_congr rfl
  intro field _
  have hneFirst : traceOrder field.1 ≠ first := by
    intro equality
    apply field.2.1
    simpa using congrArg traceOrder.symm equality
  have hneSecond : traceOrder field.1 ≠ second := by
    intro equality
    apply field.2.2.1
    simpa using congrArg traceOrder.symm equality
  have hneThird : traceOrder field.1 ≠ third := by
    intro equality
    apply field.2.2.2
    simpa using congrArg traceOrder.symm equality
  rw [Equiv.trans_apply, hfix _ hneFirst hneSecond hneThird]

def threeRewireContractionTerm
    {Label R : Type*} [Fintype Label] [DecidableEq Label]
    [CommSemiring R]
    (matrixAt : Label → Matrix (Fin 2) (Fin 2) R)
    (traceOrder rewire : Equiv.Perm Label)
    (first second third : Label)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (data : ThreeIndexState
      (traceOrder.symm first) (traceOrder.symm second)
        (traceOrder.symm third)) : R :=
  let state :=
    (splitThreeMatrixIndexState
      (traceOrder.symm first) (traceOrder.symm second)
        (traceOrder.symm third)
      (traceOrder.symm.injective.ne hfirstSecond)
      (traceOrder.symm.injective.ne hfirstThird)
      (traceOrder.symm.injective.ne hsecondThird)).symm data
  matrixAt (traceOrder.symm first) data.atFirst
      (state (rewire first)) *
    matrixAt (traceOrder.symm second) data.atSecond
      (state (rewire second)) *
    matrixAt (traceOrder.symm third) data.atThird
      (state (rewire third)) *
    threeSourceOutsideProduct matrixAt traceOrder
      (traceOrder.symm first) (traceOrder.symm second)
        (traceOrder.symm third)
      (traceOrder.symm.injective.ne hfirstSecond)
      (traceOrder.symm.injective.ne hfirstThird)
      (traceOrder.symm.injective.ne hsecondThird) data

/-- Rewiring only three target labels changes only the three predecessor
factors in the split contraction. -/
theorem tracePermutationContraction_rewireThree
    {Label R : Type*} [Fintype Label] [DecidableEq Label]
    [CommSemiring R]
    (matrixAt : Label → Matrix (Fin 2) (Fin 2) R)
    (traceOrder rewire : Equiv.Perm Label)
    (first second third : Label)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hfix : FixesOutsideThree rewire first second third) :
    tracePermutationContraction matrixAt (traceOrder.trans rewire) =
      ∑ data : ThreeIndexState
          (traceOrder.symm first) (traceOrder.symm second)
            (traceOrder.symm third),
        threeRewireContractionTerm matrixAt traceOrder rewire
          first second third hfirstSecond hfirstThird hsecondThird data := by
  rw [tracePermutationContraction_splitThree]
  apply Finset.sum_congr rfl
  intro data _
  unfold threeRewireContractionTerm
  simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
  rw [threeSourceOutsideProduct_trans_rewire matrixAt traceOrder rewire
    first second third hfirstSecond hfirstThird hsecondThird hfix]

def threeTargetCycleForward {Label : Type*}
    (first second third : Label) [DecidableEq Label] :
    Equiv.Perm Label :=
  (Equiv.swap second third).trans (Equiv.swap first second)

def threeTargetCycleBackward {Label : Type*}
    (first second third : Label) [DecidableEq Label] :
    Equiv.Perm Label :=
  (Equiv.swap first second).trans (Equiv.swap second third)

@[simp] theorem threeTargetCycleForward_apply_first
    {Label : Type*} [DecidableEq Label]
    (first second third : Label)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) :
    threeTargetCycleForward first second third first = second := by
  rw [threeTargetCycleForward, Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne hfirstSecond hfirstThird]
  exact Equiv.swap_apply_left first second

@[simp] theorem threeTargetCycleForward_apply_second
    {Label : Type*} [DecidableEq Label]
    (first second third : Label)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    threeTargetCycleForward first second third second = third := by
  rw [threeTargetCycleForward, Equiv.trans_apply,
    Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne
    hfirstThird.symm hsecondThird.symm

@[simp] theorem threeTargetCycleForward_apply_third
    {Label : Type*} [DecidableEq Label]
    (first second third : Label) :
    threeTargetCycleForward first second third third = first := by
  rw [threeTargetCycleForward, Equiv.trans_apply,
    Equiv.swap_apply_right, Equiv.swap_apply_right]

@[simp] theorem threeTargetCycleBackward_apply_first
    {Label : Type*} [DecidableEq Label]
    (first second third : Label) :
    threeTargetCycleBackward first second third first = third := by
  rw [threeTargetCycleBackward, Equiv.trans_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_left]

@[simp] theorem threeTargetCycleBackward_apply_second
    {Label : Type*} [DecidableEq Label]
    (first second third : Label)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third) :
    threeTargetCycleBackward first second third second = first := by
  rw [threeTargetCycleBackward, Equiv.trans_apply,
    Equiv.swap_apply_right]
  exact Equiv.swap_apply_of_ne_of_ne hfirstSecond hfirstThird

@[simp] theorem threeTargetCycleBackward_apply_third
    {Label : Type*} [DecidableEq Label]
    (first second third : Label)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    threeTargetCycleBackward first second third third = second := by
  rw [threeTargetCycleBackward, Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne
    hfirstThird.symm hsecondThird.symm]
  exact Equiv.swap_apply_right second third

theorem fixesOutsideThree_one
    {Label : Type*} (first second third : Label) :
    FixesOutsideThree 1 first second third := by
  intro target _ _ _
  rfl

theorem fixesOutsideThree_swap_first_second
    {Label : Type*} [DecidableEq Label]
    (first second third : Label) :
    FixesOutsideThree (Equiv.swap first second) first second third := by
  intro target hfirst hsecond _
  exact Equiv.swap_apply_of_ne_of_ne hfirst hsecond

theorem fixesOutsideThree_swap_first_third
    {Label : Type*} [DecidableEq Label]
    (first second third : Label) :
    FixesOutsideThree (Equiv.swap first third) first second third := by
  intro target hfirst _ hthird
  exact Equiv.swap_apply_of_ne_of_ne hfirst hthird

theorem fixesOutsideThree_swap_second_third
    {Label : Type*} [DecidableEq Label]
    (first second third : Label) :
    FixesOutsideThree (Equiv.swap second third) first second third := by
  intro target _ hsecond hthird
  exact Equiv.swap_apply_of_ne_of_ne hsecond hthird

theorem fixesOutsideThree_cycleForward
    {Label : Type*} [DecidableEq Label]
    (first second third : Label) :
    FixesOutsideThree
      (threeTargetCycleForward first second third)
      first second third := by
  intro target hfirst hsecond hthird
  simp [threeTargetCycleForward, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne hfirst hsecond,
    Equiv.swap_apply_of_ne_of_ne hsecond hthird]

theorem fixesOutsideThree_cycleBackward
    {Label : Type*} [DecidableEq Label]
    (first second third : Label) :
    FixesOutsideThree
      (threeTargetCycleBackward first second third)
      first second third := by
  intro target hfirst hsecond hthird
  simp [threeTargetCycleBackward, Equiv.trans_apply,
    Equiv.swap_apply_of_ne_of_ne hfirst hsecond,
    Equiv.swap_apply_of_ne_of_ne hsecond hthird]

/-- The alternating `3 × 3` scalar minor vanishes when its three column
labels take only two values. -/
theorem fin_two_three_column_alternation
    {R : Type*} [CommRing R]
    (firstRow secondRow thirdRow : Fin 2 → R)
    (firstColumn secondColumn thirdColumn : Fin 2) :
    firstRow firstColumn * secondRow secondColumn * thirdRow thirdColumn -
        firstRow secondColumn * secondRow firstColumn * thirdRow thirdColumn -
        firstRow thirdColumn * secondRow secondColumn * thirdRow firstColumn -
        firstRow firstColumn * secondRow thirdColumn * thirdRow secondColumn +
        firstRow secondColumn * secondRow thirdColumn * thirdRow firstColumn +
        firstRow thirdColumn * secondRow firstColumn * thirdRow secondColumn =
      0 := by
  fin_cases firstColumn <;> fin_cases secondColumn <;>
    fin_cases thirdColumn <;> ring

/-- The six standard rewires of any trace permutation satisfy the fundamental
two-by-two trace identity under ordinary matrix-index contraction. -/
theorem tracePermutationContraction_fundamental_rewire
    {Label R : Type*} [Fintype Label] [DecidableEq Label]
    [CommRing R]
    (matrixAt : Label → Matrix (Fin 2) (Fin 2) R)
    (traceOrder : Equiv.Perm Label)
    (first second third : Label)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third) :
    tracePermutationContraction matrixAt traceOrder -
        tracePermutationContraction matrixAt
          (traceOrder.trans (Equiv.swap first second)) -
        tracePermutationContraction matrixAt
          (traceOrder.trans (Equiv.swap first third)) -
        tracePermutationContraction matrixAt
          (traceOrder.trans (Equiv.swap second third)) +
        tracePermutationContraction matrixAt
          (traceOrder.trans
            (threeTargetCycleForward first second third)) +
        tracePermutationContraction matrixAt
          (traceOrder.trans
            (threeTargetCycleBackward first second third)) =
      0 := by
  have hbase := tracePermutationContraction_rewireThree
    matrixAt traceOrder (1 : Equiv.Perm Label)
    first second third hfirstSecond hfirstThird hsecondThird
    (fixesOutsideThree_one first second third)
  have hfirstSecondSwap := tracePermutationContraction_rewireThree
    matrixAt traceOrder (Equiv.swap first second)
    first second third hfirstSecond hfirstThird hsecondThird
    (fixesOutsideThree_swap_first_second first second third)
  have hfirstThirdSwap := tracePermutationContraction_rewireThree
    matrixAt traceOrder (Equiv.swap first third)
    first second third hfirstSecond hfirstThird hsecondThird
    (fixesOutsideThree_swap_first_third first second third)
  have hsecondThirdSwap := tracePermutationContraction_rewireThree
    matrixAt traceOrder (Equiv.swap second third)
    first second third hfirstSecond hfirstThird hsecondThird
    (fixesOutsideThree_swap_second_third first second third)
  have hforward := tracePermutationContraction_rewireThree
    matrixAt traceOrder (threeTargetCycleForward first second third)
    first second third hfirstSecond hfirstThird hsecondThird
    (fixesOutsideThree_cycleForward first second third)
  have hbackward := tracePermutationContraction_rewireThree
    matrixAt traceOrder (threeTargetCycleBackward first second third)
    first second third hfirstSecond hfirstThird hsecondThird
    (fixesOutsideThree_cycleBackward first second third)
  have hbase' :
      tracePermutationContraction matrixAt traceOrder =
        ∑ data : ThreeIndexState
            (traceOrder.symm first) (traceOrder.symm second)
              (traceOrder.symm third),
          threeRewireContractionTerm matrixAt traceOrder 1
            first second third hfirstSecond hfirstThird hsecondThird data := by
    have htransOne :
        traceOrder.trans (1 : Equiv.Perm Label) = traceOrder := by
      apply Equiv.ext
      intro target
      exact Equiv.Perm.one_apply (traceOrder target)
    rw [htransOne] at hbase
    exact hbase
  rw [hbase', hfirstSecondSwap, hfirstThirdSwap,
    hsecondThirdSwap, hforward, hbackward]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro data _
  unfold threeRewireContractionTerm
  simp only [Equiv.Perm.one_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne hfirstSecond hfirstThird,
    Equiv.swap_apply_of_ne_of_ne hfirstSecond.symm hsecondThird,
    Equiv.swap_apply_of_ne_of_ne hfirstThird.symm hsecondThird.symm,
    threeTargetCycleForward_apply_first first second third
      hfirstSecond hfirstThird,
    threeTargetCycleForward_apply_second first second third
      hfirstThird hsecondThird,
    threeTargetCycleForward_apply_third,
    threeTargetCycleBackward_apply_first,
    threeTargetCycleBackward_apply_second first second third
      hfirstSecond hfirstThird,
    threeTargetCycleBackward_apply_third first second third
      hfirstThird hsecondThird]
  let state :=
    (splitThreeMatrixIndexState
      (traceOrder.symm first) (traceOrder.symm second)
        (traceOrder.symm third)
      (traceOrder.symm.injective.ne hfirstSecond)
      (traceOrder.symm.injective.ne hfirstThird)
      (traceOrder.symm.injective.ne hsecondThird)).symm data
  have hminor := fin_two_three_column_alternation
    (fun column =>
      matrixAt (traceOrder.symm first) data.atFirst column)
    (fun column =>
      matrixAt (traceOrder.symm second) data.atSecond column)
    (fun column =>
      matrixAt (traceOrder.symm third) data.atThird column)
    (state first) (state second) (state third)
  linear_combination
    (threeSourceOutsideProduct matrixAt traceOrder
      (traceOrder.symm first) (traceOrder.symm second)
        (traceOrder.symm third)
      (traceOrder.symm.injective.ne hfirstSecond)
      (traceOrder.symm.injective.ne hfirstThird)
      (traceOrder.symm.injective.ne hsecondThird) data) * hminor

/-- Entrywise trace-context form of the polarized Cayley--Hamilton identity. -/
theorem traceless_fin_two_anticommutator_entry
    {R : Type*} [CommRing R]
    (context left right : Matrix (Fin 2) (Fin 2) R)
    (hleft : Matrix.trace left = 0)
    (hright : Matrix.trace right = 0)
    (source target : Fin 2) :
    (∑ middleLeft : Fin 2,
        ∑ middleRight : Fin 2,
          context source middleLeft *
            left middleLeft middleRight * right middleRight target) +
        (∑ middleRight : Fin 2,
          ∑ middleLeft : Fin 2,
            context source middleRight *
              right middleRight middleLeft * left middleLeft target) -
        (∑ diagonalLeft : Fin 2,
          ∑ diagonalRight : Fin 2,
            context source target *
              left diagonalLeft diagonalRight *
                right diagonalRight diagonalLeft) =
      0 := by
  have hmatrix := congrArg
    (fun value : Matrix (Fin 2) (Fin 2) R =>
      (context * value) source target)
    (traceless_fin_two_anticommutator left right hleft hright)
  simp [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply, Matrix.trace, Matrix.diag_apply,
    Fin.sum_univ_two, smul_eq_mul] at hmatrix
  simp only [Fin.sum_univ_two]
  linear_combination hmatrix

def ThreeIndexState.replaceFirstSecond
    {Label : Type*} {first second third : Label}
    (data : ThreeIndexState first second third)
    (firstValue secondValue : Fin 2) :
    ThreeIndexState first second third :=
  { atFirst := firstValue
    atSecond := secondValue
    atThird := data.atThird
    away := data.away }

@[simp] theorem ThreeIndexState.replaceFirstSecond_atFirst
    {Label : Type*} {first second third : Label}
    (data : ThreeIndexState first second third)
    (firstValue secondValue : Fin 2) :
    (data.replaceFirstSecond firstValue secondValue).atFirst = firstValue :=
  rfl

@[simp] theorem ThreeIndexState.replaceFirstSecond_atSecond
    {Label : Type*} {first second third : Label}
    (data : ThreeIndexState first second third)
    (firstValue secondValue : Fin 2) :
    (data.replaceFirstSecond firstValue secondValue).atSecond = secondValue :=
  rfl

@[simp] theorem ThreeIndexState.replaceFirstSecond_atThird
    {Label : Type*} {first second third : Label}
    (data : ThreeIndexState first second third)
    (firstValue secondValue : Fin 2) :
    (data.replaceFirstSecond firstValue secondValue).atThird = data.atThird :=
  rfl

@[simp] theorem ThreeIndexState.replaceFirstSecond_away
    {Label : Type*} {first second third : Label}
    (data : ThreeIndexState first second third)
    (firstValue secondValue : Fin 2) :
    (data.replaceFirstSecond firstValue secondValue).away = data.away :=
  rfl

theorem splitThreeMatrixIndexState_replaceFirstSecond_apply_of_ne
    {Label : Type*} [DecidableEq Label]
    (first second third : Label)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (data : ThreeIndexState first second third)
    (firstValue secondValue : Fin 2)
    (target : Label) (htargetFirst : target ≠ first)
    (htargetSecond : target ≠ second) :
    (splitThreeMatrixIndexState first second third
      hfirstSecond hfirstThird hsecondThird).symm
        (data.replaceFirstSecond firstValue secondValue) target =
      (splitThreeMatrixIndexState first second third
        hfirstSecond hfirstThird hsecondThird).symm data target := by
  by_cases htargetThird : target = third
  · subst target
    simp
  · let targetAway : AwayFromThree first second third :=
      ⟨target, ⟨htargetFirst, htargetSecond, htargetThird⟩⟩
    rw [show target = targetAway.1 from rfl]
    rw [splitThreeMatrixIndexState_symm_apply_away,
      splitThreeMatrixIndexState_symm_apply_away]
    rfl

theorem threeSourceOutsideProduct_replaceFirstSecond
    {Label R : Type*} [Fintype Label] [DecidableEq Label]
    [CommSemiring R]
    (matrixAt : Label → Matrix (Fin 2) (Fin 2) R)
    (traceOrder : Equiv.Perm Label)
    (first second third : Label)
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (data : ThreeIndexState first second third)
    (firstValue secondValue : Fin 2)
    (houtside : ∀ field : AwayFromThree first second third,
      traceOrder field.1 ≠ first ∧ traceOrder field.1 ≠ second) :
    threeSourceOutsideProduct matrixAt traceOrder
        first second third hfirstSecond hfirstThird hsecondThird
        (data.replaceFirstSecond firstValue secondValue) =
      threeSourceOutsideProduct matrixAt traceOrder
        first second third hfirstSecond hfirstThird hsecondThird data := by
  unfold threeSourceOutsideProduct
  apply Finset.prod_congr rfl
  intro field _
  rw [splitThreeMatrixIndexState_replaceFirstSecond_apply_of_ne
    first second third hfirstSecond hfirstThird hsecondThird]
  · rfl
  · exact (houtside field).1
  · exact (houtside field).2

/-- Reorder the finite state sum so the first two selected indices are the
inner summation variables. -/
def threeIndexStateTailEquiv
    {Label : Type*} (first second third : Label) :
    ((Fin 2 × (AwayFromThree first second third → Fin 2)) ×
        (Fin 2 × Fin 2)) ≃
      ThreeIndexState first second third where
  toFun data :=
    { atFirst := data.2.1
      atSecond := data.2.2
      atThird := data.1.1
      away := data.1.2 }
  invFun data :=
    ((data.atThird, data.away), (data.atFirst, data.atSecond))
  left_inv data := by rcases data with ⟨⟨thirdValue, away⟩,
    ⟨firstValue, secondValue⟩⟩; rfl
  right_inv data := by rcases data with ⟨firstValue, secondValue,
    thirdValue, away⟩; rfl

/-- The adjacent traceless anticommutator rewire vanishes under ordinary
matrix-index contraction. -/
theorem tracePermutationContraction_anticommutator_rewire
    {Label R : Type*} [Fintype Label] [DecidableEq Label]
    [CommRing R]
    (matrixAt : Label → Matrix (Fin 2) (Fin 2) R)
    (htraceless : ∀ field, Matrix.trace (matrixAt field) = 0)
    (traceOrder : Equiv.Perm Label) (left : Label)
    (hcycle : traceOrder (traceOrder left) ≠ left) :
    tracePermutationContraction matrixAt traceOrder +
        tracePermutationContraction matrixAt
          (traceOrder.trans
            (threeTargetCycleForward
              (traceOrder left) (traceOrder (traceOrder left)) left)) -
        tracePermutationContraction matrixAt
          (traceOrder.trans
            (Equiv.swap (traceOrder (traceOrder left)) left)) =
      0 := by
  let right := traceOrder left
  let successor := traceOrder right
  have hrightLeft : right ≠ left := by
    intro equality
    apply hcycle
    change traceOrder right = left
    rw [equality]
    exact equality
  have hsuccessorRight : successor ≠ right := by
    intro equality
    apply hrightLeft
    apply traceOrder.injective
    exact equality
  have hsuccessorLeft : successor ≠ left := by
    exact hcycle
  have hrightSuccessor : right ≠ successor := hsuccessorRight.symm
  have hbase := tracePermutationContraction_rewireThree
    matrixAt traceOrder (1 : Equiv.Perm Label)
    right successor left hrightSuccessor hrightLeft hsuccessorLeft
    (fixesOutsideThree_one right successor left)
  have hforward := tracePermutationContraction_rewireThree
    matrixAt traceOrder (threeTargetCycleForward right successor left)
    right successor left hrightSuccessor hrightLeft hsuccessorLeft
    (fixesOutsideThree_cycleForward right successor left)
  have hsplit := tracePermutationContraction_rewireThree
    matrixAt traceOrder (Equiv.swap successor left)
    right successor left hrightSuccessor hrightLeft hsuccessorLeft
    (fixesOutsideThree_swap_second_third right successor left)
  have htransOne :
      traceOrder.trans (1 : Equiv.Perm Label) = traceOrder := by
    apply Equiv.ext
    intro target
    exact Equiv.Perm.one_apply (traceOrder target)
  rw [htransOne] at hbase
  change tracePermutationContraction matrixAt traceOrder +
        tracePermutationContraction matrixAt
          (traceOrder.trans
            (threeTargetCycleForward right successor left)) -
        tracePermutationContraction matrixAt
          (traceOrder.trans (Equiv.swap successor left)) = 0
  rw [hbase, hforward, hsplit,
    ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  let body : ThreeIndexState
      (traceOrder.symm right) (traceOrder.symm successor)
        (traceOrder.symm left) → R := fun data =>
    threeRewireContractionTerm matrixAt traceOrder 1
        right successor left hrightSuccessor hrightLeft hsuccessorLeft data +
      threeRewireContractionTerm matrixAt traceOrder
        (threeTargetCycleForward right successor left)
        right successor left hrightSuccessor hrightLeft hsuccessorLeft data -
      threeRewireContractionTerm matrixAt traceOrder
        (Equiv.swap successor left)
        right successor left hrightSuccessor hrightLeft hsuccessorLeft data
  change (∑ data, body data) = 0
  rw [← Equiv.sum_comp
    (threeIndexStateTailEquiv
      (traceOrder.symm right) (traceOrder.symm successor)
        (traceOrder.symm left)) body]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  rintro ⟨thirdValue, away⟩ _
  let baseData : ThreeIndexState
      (traceOrder.symm right) (traceOrder.symm successor)
        (traceOrder.symm left) :=
    { atFirst := 0
      atSecond := 0
      atThird := thirdValue
      away := away }
  have houtside : ∀ field : AwayFromThree
      (traceOrder.symm right) (traceOrder.symm successor)
        (traceOrder.symm left),
      traceOrder field.1 ≠ traceOrder.symm right ∧
        traceOrder field.1 ≠ traceOrder.symm successor := by
    intro field
    constructor
    · intro equality
      apply field.2.2.2
      apply traceOrder.injective
      simpa [right] using equality
    · intro equality
      apply field.2.1
      apply traceOrder.injective
      simpa [successor] using equality
  have hsuccessorFirstSource :
      successor ≠ traceOrder.symm right := by
    simpa [right] using hsuccessorLeft
  have hsuccessorSecondSource :
      successor ≠ traceOrder.symm successor := by
    simpa [right, successor] using hsuccessorRight
  have hleftSource : traceOrder.symm right = left := by
    simp [right]
  have hrightSource : traceOrder.symm successor = right := by
    simp [successor]
  let baseState :=
    (splitThreeMatrixIndexState
      (traceOrder.symm right) (traceOrder.symm successor)
        (traceOrder.symm left)
      (traceOrder.symm.injective.ne hrightSuccessor)
      (traceOrder.symm.injective.ne hrightLeft)
      (traceOrder.symm.injective.ne hsuccessorLeft)).symm baseData
  have hreplaceRight (firstValue secondValue : Fin 2) :
      (splitThreeMatrixIndexState
        (traceOrder.symm right) (traceOrder.symm successor)
          (traceOrder.symm left)
        (traceOrder.symm.injective.ne hrightSuccessor)
        (traceOrder.symm.injective.ne hrightLeft)
        (traceOrder.symm.injective.ne hsuccessorLeft)).symm
          (baseData.replaceFirstSecond firstValue secondValue) right =
        secondValue := by
    calc
      _ = (splitThreeMatrixIndexState
          (traceOrder.symm right) (traceOrder.symm successor)
            (traceOrder.symm left)
          (traceOrder.symm.injective.ne hrightSuccessor)
          (traceOrder.symm.injective.ne hrightLeft)
          (traceOrder.symm.injective.ne hsuccessorLeft)).symm
            (baseData.replaceFirstSecond firstValue secondValue)
              (traceOrder.symm successor) :=
        congrArg
          ((splitThreeMatrixIndexState
            (traceOrder.symm right) (traceOrder.symm successor)
              (traceOrder.symm left)
            (traceOrder.symm.injective.ne hrightSuccessor)
            (traceOrder.symm.injective.ne hrightLeft)
            (traceOrder.symm.injective.ne hsuccessorLeft)).symm
              (baseData.replaceFirstSecond firstValue secondValue))
          hrightSource.symm
      _ = (baseData.replaceFirstSecond firstValue secondValue).atSecond :=
        splitThreeMatrixIndexState_symm_apply_second
          (traceOrder.symm right) (traceOrder.symm successor)
            (traceOrder.symm left)
          (traceOrder.symm.injective.ne hrightSuccessor)
          (traceOrder.symm.injective.ne hrightLeft)
          (traceOrder.symm.injective.ne hsuccessorLeft)
          (baseData.replaceFirstSecond firstValue secondValue)
      _ = secondValue := rfl
  have hreplaceLeft (firstValue secondValue : Fin 2) :
      (splitThreeMatrixIndexState
        (traceOrder.symm right) (traceOrder.symm successor)
          (traceOrder.symm left)
        (traceOrder.symm.injective.ne hrightSuccessor)
        (traceOrder.symm.injective.ne hrightLeft)
        (traceOrder.symm.injective.ne hsuccessorLeft)).symm
          (baseData.replaceFirstSecond firstValue secondValue) left =
        firstValue := by
    calc
      _ = (splitThreeMatrixIndexState
          (traceOrder.symm right) (traceOrder.symm successor)
            (traceOrder.symm left)
          (traceOrder.symm.injective.ne hrightSuccessor)
          (traceOrder.symm.injective.ne hrightLeft)
          (traceOrder.symm.injective.ne hsuccessorLeft)).symm
            (baseData.replaceFirstSecond firstValue secondValue)
              (traceOrder.symm right) :=
        congrArg
          ((splitThreeMatrixIndexState
            (traceOrder.symm right) (traceOrder.symm successor)
              (traceOrder.symm left)
            (traceOrder.symm.injective.ne hrightSuccessor)
            (traceOrder.symm.injective.ne hrightLeft)
            (traceOrder.symm.injective.ne hsuccessorLeft)).symm
              (baseData.replaceFirstSecond firstValue secondValue))
          hleftSource.symm
      _ = (baseData.replaceFirstSecond firstValue secondValue).atFirst :=
        splitThreeMatrixIndexState_symm_apply_first
          (traceOrder.symm right) (traceOrder.symm successor)
            (traceOrder.symm left)
          (traceOrder.symm.injective.ne hrightSuccessor)
          (traceOrder.symm.injective.ne hrightLeft)
          (traceOrder.symm.injective.ne hsuccessorLeft)
          (baseData.replaceFirstSecond firstValue secondValue)
      _ = firstValue := rfl
  have hbaseSuccessor :
      (splitThreeMatrixIndexState
        (traceOrder.symm right) (traceOrder.symm successor)
          (traceOrder.symm left)
        (traceOrder.symm.injective.ne hrightSuccessor)
        (traceOrder.symm.injective.ne hrightLeft)
        (traceOrder.symm.injective.ne hsuccessorLeft)).symm
          baseData successor = baseState successor := by
    rfl
  have hentry := traceless_fin_two_anticommutator_entry
    (matrixAt (traceOrder.symm left))
    (matrixAt (traceOrder.symm right))
    (matrixAt (traceOrder.symm successor))
    (htraceless (traceOrder.symm right))
    (htraceless (traceOrder.symm successor))
    thirdValue (baseState successor)
  unfold body threeRewireContractionTerm
  simp only [Equiv.Perm.one_apply,
    threeTargetCycleForward_apply_first right successor left
      hrightSuccessor hrightLeft,
    threeTargetCycleForward_apply_second right successor left
      hrightLeft hsuccessorLeft,
    threeTargetCycleForward_apply_third,
    Equiv.swap_apply_of_ne_of_ne hrightSuccessor hrightLeft,
    Equiv.swap_apply_left, Equiv.swap_apply_right]
  simp_rw [show ∀ firstValue secondValue : Fin 2,
      (threeIndexStateTailEquiv
        (traceOrder.symm right) (traceOrder.symm successor)
          (traceOrder.symm left))
          ((thirdValue, away), (firstValue, secondValue)) =
        baseData.replaceFirstSecond firstValue secondValue by
      intro firstValue secondValue
      rfl]
  simp_rw [threeSourceOutsideProduct_replaceFirstSecond
    matrixAt traceOrder
    (traceOrder.symm right) (traceOrder.symm successor)
      (traceOrder.symm left)
    (traceOrder.symm.injective.ne hrightSuccessor)
    (traceOrder.symm.injective.ne hrightLeft)
    (traceOrder.symm.injective.ne hsuccessorLeft)
    baseData _ _ houtside]
  simp_rw [splitThreeMatrixIndexState_replaceFirstSecond_apply_of_ne
    (traceOrder.symm right) (traceOrder.symm successor)
      (traceOrder.symm left)
    (traceOrder.symm.injective.ne hrightSuccessor)
    (traceOrder.symm.injective.ne hrightLeft)
    (traceOrder.symm.injective.ne hsuccessorLeft)
    baseData _ _ successor hsuccessorFirstSource hsuccessorSecondSource]
  simp_rw [hreplaceRight, hreplaceLeft, hbaseSuccessor]
  simp only [ThreeIndexState.replaceFirstSecond_atFirst,
    ThreeIndexState.replaceFirstSecond_atSecond,
    ThreeIndexState.replaceFirstSecond_atThird,
    hleftSource, hrightSource,
    Fintype.sum_prod_type, Fin.sum_univ_two] at hentry ⊢
  linear_combination
    (threeSourceOutsideProduct matrixAt traceOrder
      (traceOrder.symm right) (traceOrder.symm successor)
        (traceOrder.symm left)
      (traceOrder.symm.injective.ne hrightSuccessor)
      (traceOrder.symm.injective.ne hrightLeft)
      (traceOrder.symm.injective.ne hsuccessorLeft) baseData) * hentry

/-! ## Identification with the physical trace rows -/

/-- The rewire used by the physical adjacent-anticommutator row is exactly
the forward three-target cycle used by the contraction theorem. -/
theorem adjacentForwardRewire_eq_threeTargetCycleForward
    {Label : Type*} [DecidableEq Label]
    (left right successor : Label)
    (hrightSuccessor : right ≠ successor)
    (hrightLeft : right ≠ left)
    (hsuccessorLeft : successor ≠ left) :
    (Equiv.swap right successor).trans (Equiv.swap left right) =
      threeTargetCycleForward right successor left := by
  apply Equiv.ext
  intro target
  by_cases htargetRight : target = right
  · subst target
    rw [Equiv.trans_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne
        hsuccessorLeft hrightSuccessor.symm,
      threeTargetCycleForward_apply_first
        right successor left hrightSuccessor hrightLeft]
  · by_cases htargetSuccessor : target = successor
    · subst target
      rw [Equiv.trans_apply, Equiv.swap_apply_right,
        Equiv.swap_apply_right,
        threeTargetCycleForward_apply_second
          right successor left hrightLeft hsuccessorLeft]
    · by_cases htargetLeft : target = left
      · subst target
        rw [Equiv.trans_apply,
          Equiv.swap_apply_of_ne_of_ne
            hrightLeft.symm hsuccessorLeft.symm,
          Equiv.swap_apply_left,
          threeTargetCycleForward_apply_third]
      · have houtside := fixesOutsideThree_cycleForward
          right successor left target htargetRight
            htargetSuccessor htargetLeft
        rw [Equiv.trans_apply,
          Equiv.swap_apply_of_ne_of_ne htargetRight htargetSuccessor,
          Equiv.swap_apply_of_ne_of_ne htargetLeft htargetRight,
          houtside]

/-- Ordinary matrix contraction annihilates the exact three-term sparse
row constructed by `TraceAnticommutatorSite`. -/
theorem tracePermutationContraction_traceAnticommutatorSite
    {R : Type*} [CommRing R]
    {carrier : RelationCarrier}
    (matrixAt : Fin carrier.1.1 → Matrix (Fin 2) (Fin 2) R)
    (htraceless : ∀ field, Matrix.trace (matrixAt field) = 0)
    (site : TraceAnticommutatorSite carrier) :
    tracePermutationContraction matrixAt carrier.2.trace.traceOrder +
        tracePermutationContraction matrixAt
          (swapAdjacentTraceOrder site) -
        tracePermutationContraction matrixAt
          (splitAdjacentTraceOrder site) = 0 := by
  rw [swapAdjacentTraceOrder, splitAdjacentTraceOrder,
    adjacentForwardRewire_eq_threeTargetCycleForward
      site.left site.right site.successor
      site.successor_ne_right.symm site.right_ne_left
      site.successor_ne_left,
    Equiv.swap_comm site.left site.successor]
  exact tracePermutationContraction_anticommutator_rewire
    matrixAt htraceless carrier.2.trace.traceOrder site.left
      site.cycleLength_ge_three

/-- Ordinary matrix contraction annihilates the exact six-term sparse row
constructed by `FundamentalTraceSite`. -/
theorem tracePermutationContraction_fundamentalTraceSite
    {R : Type*} [CommRing R]
    {carrier : RelationCarrier}
    (matrixAt : Fin carrier.1.1 → Matrix (Fin 2) (Fin 2) R)
    (site : FundamentalTraceSite carrier) :
    tracePermutationContraction matrixAt carrier.2.trace.traceOrder -
        tracePermutationContraction matrixAt
          (carrier.2.trace.traceOrder.trans
            (Equiv.swap site.first site.second)) -
        tracePermutationContraction matrixAt
          (carrier.2.trace.traceOrder.trans
            (Equiv.swap site.first site.third)) -
        tracePermutationContraction matrixAt
          (carrier.2.trace.traceOrder.trans
            (Equiv.swap site.second site.third)) +
        tracePermutationContraction matrixAt
          (carrier.2.trace.traceOrder.trans
            (fundamentalCycleForward site)) +
        tracePermutationContraction matrixAt
          (carrier.2.trace.traceOrder.trans
            (fundamentalCycleBackward site)) = 0 := by
  simpa [fundamentalCycleForward, fundamentalCycleBackward,
    threeTargetCycleForward, threeTargetCycleBackward] using
    tracePermutationContraction_fundamental_rewire
      matrixAt carrier.2.trace.traceOrder
      site.first site.second site.third
      site.first_ne_second site.first_ne_third site.second_ne_third

/-! ## Linear evaluation of the implemented sparse rows -/

/-- A matrix assignment on ordered field-strength index pairs.  Keeping the
ordered pair here makes this a semantics of the pre-antisymmetry relation
carrier itself. -/
abbrev OrderedAxisPairMatrixAssignment :=
  Axis → Axis → Matrix (Fin 2) (Fin 2) ℚ

/-- Ordinary trace evaluation of one basis element of the actual sparse
relation carrier. -/
def relationCarrierTraceEvaluation
    (matrices : OrderedAxisPairMatrixAssignment)
    (carrier : RelationCarrier) : ℚ :=
  tracePermutationContraction
    (fun field => matrices (carrier.2.fieldFirst field)
      (carrier.2.fieldSecond field))
    carrier.2.trace.traceOrder

/-- Linear extension of ordinary matrix trace evaluation to the actual
relation-row module. -/
def relationSpaceTraceEvaluation
    (matrices : OrderedAxisPairMatrixAssignment) :
    RelationSpace →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ
    (relationCarrierTraceEvaluation matrices)

@[simp] theorem relationSpaceTraceEvaluation_single
    (matrices : OrderedAxisPairMatrixAssignment)
    (carrier : RelationCarrier) (coefficient : ℚ) :
    relationSpaceTraceEvaluation matrices
        (Finsupp.single carrier coefficient) =
      coefficient * relationCarrierTraceEvaluation matrices carrier := by
  simp [relationSpaceTraceEvaluation]

/-- Every implemented one-letter trace row lies in the kernel of ordinary
trace evaluation when the field matrices are traceless. -/
theorem relationSpaceTraceEvaluation_tracelessLetterRow
    (matrices : OrderedAxisPairMatrixAssignment)
    (htraceless : ∀ first second,
      Matrix.trace (matrices first second) = 0)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (hsingleton : IsSingletonTrace carrier field) :
    relationSpaceTraceEvaluation matrices
        (tracelessLetterRow carrier field) = 0 := by
  simp only [tracelessLetterRow,
    relationSpaceTraceEvaluation_single, one_mul]
  unfold relationCarrierTraceEvaluation
  rw [tracePermutationContraction_fixedPoint _ _ field hsingleton,
    htraceless]
  simp

/-- Every implemented adjacent-anticommutator sparse row lies in the kernel
of ordinary trace evaluation when the field matrices are traceless. -/
theorem relationSpaceTraceEvaluation_traceAnticommutatorRow
    (matrices : OrderedAxisPairMatrixAssignment)
    (htraceless : ∀ first second,
      Matrix.trace (matrices first second) = 0)
    {carrier : RelationCarrier}
    (site : TraceAnticommutatorSite carrier) :
    relationSpaceTraceEvaluation matrices
        (traceAnticommutatorRow site) = 0 := by
  simp only [traceAnticommutatorRow, map_sub, map_add,
    relationSpaceTraceEvaluation_single, one_mul]
  change tracePermutationContraction
        (fun field => matrices (carrier.2.fieldFirst field)
          (carrier.2.fieldSecond field))
        carrier.2.trace.traceOrder +
      tracePermutationContraction
        (fun field => matrices (carrier.2.fieldFirst field)
          (carrier.2.fieldSecond field))
        (swapAdjacentTraceOrder site) -
      tracePermutationContraction
        (fun field => matrices (carrier.2.fieldFirst field)
          (carrier.2.fieldSecond field))
        (splitAdjacentTraceOrder site) = 0
  exact tracePermutationContraction_traceAnticommutatorSite
    (fun field => matrices (carrier.2.fieldFirst field)
      (carrier.2.fieldSecond field))
    (fun field => htraceless _ _) site

/-- Every implemented six-term fundamental sparse row lies in the kernel of
ordinary trace evaluation. -/
theorem relationSpaceTraceEvaluation_fundamentalTraceRow
    (matrices : OrderedAxisPairMatrixAssignment)
    {carrier : RelationCarrier}
    (site : FundamentalTraceSite carrier) :
    relationSpaceTraceEvaluation matrices
        (fundamentalTraceRow site) = 0 := by
  simp only [fundamentalTraceRow, map_sub, map_add,
    relationSpaceTraceEvaluation_single, one_mul]
  change tracePermutationContraction
        (fun field => matrices (carrier.2.fieldFirst field)
          (carrier.2.fieldSecond field))
        carrier.2.trace.traceOrder -
      tracePermutationContraction
        (fun field => matrices (carrier.2.fieldFirst field)
          (carrier.2.fieldSecond field))
        (carrier.2.trace.traceOrder.trans
          (Equiv.swap site.first site.second)) -
      tracePermutationContraction
        (fun field => matrices (carrier.2.fieldFirst field)
          (carrier.2.fieldSecond field))
        (carrier.2.trace.traceOrder.trans
          (Equiv.swap site.first site.third)) -
      tracePermutationContraction
        (fun field => matrices (carrier.2.fieldFirst field)
          (carrier.2.fieldSecond field))
        (carrier.2.trace.traceOrder.trans
          (Equiv.swap site.second site.third)) +
      tracePermutationContraction
        (fun field => matrices (carrier.2.fieldFirst field)
          (carrier.2.fieldSecond field))
        (carrier.2.trace.traceOrder.trans
          (fundamentalCycleForward site)) +
      tracePermutationContraction
        (fun field => matrices (carrier.2.fieldFirst field)
          (carrier.2.fieldSecond field))
        (carrier.2.trace.traceOrder.trans
          (fundamentalCycleBackward site)) = 0
  exact tracePermutationContraction_fundamentalTraceSite
    (fun field => matrices (carrier.2.fieldFirst field)
      (carrier.2.fieldSecond field)) site

/-! ## Plane-matrix evaluation and descent to field orbits -/

abbrev PlaneMatrixAssignment (R : Type*) :=
  OrientedPlane → Matrix (Fin 2) (Fin 2) R

def labeledPlaneTraceEvaluation
    {R : Type*} [CommSemiring R]
    (matrices : PlaneMatrixAssignment R)
    {fieldCount derivativeCount : ℕ}
    (sector : LabeledLocalWordSector fieldCount derivativeCount) : R :=
  tracePermutationContraction
    (fun field => matrices (sector.decoration.1 field).plane)
    sector.trace

theorem labeledPlaneTraceEvaluation_relabel
    {R : Type*} [CommSemiring R]
    (matrices : PlaneMatrixAssignment R)
    {fieldCount derivativeCount : ℕ}
    (rename : Equiv.Perm (Fin fieldCount))
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    labeledPlaneTraceEvaluation matrices (sector.relabel rename) =
      labeledPlaneTraceEvaluation matrices sector := by
  exact tracePermutationContraction_relabel rename
    (fun field => matrices (sector.decoration.1 field).plane)
    sector.trace

/-- A one-letter trace evaluates to zero when every assigned plane matrix is
traceless. -/
theorem labeledPlaneTraceEvaluation_eq_zero_of_singleton
    {R : Type*} [CommRing R]
    (matrices : PlaneMatrixAssignment R)
    (htraceless : ∀ plane, Matrix.trace (matrices plane) = 0)
    {fieldCount derivativeCount : ℕ}
    (sector : LabeledLocalWordSector fieldCount derivativeCount)
    (field : Fin fieldCount) (hfixed : sector.trace field = field) :
    labeledPlaneTraceEvaluation matrices sector = 0 := by
  unfold labeledPlaneTraceEvaluation
  rw [tracePermutationContraction_fixedPoint _ _ field hfixed,
    htraceless]
  simp

/-- Ordinary matrix evaluation of a genuine field-label orbit. -/
def orbitPlaneTraceEvaluation
    {R : Type*} [CommSemiring R]
    (matrices : PlaneMatrixAssignment R)
    {fieldCount derivativeCount : ℕ} :
    FieldRelabelOrbitCarrier fieldCount derivativeCount → R :=
  Quotient.lift (labeledPlaneTraceEvaluation matrices)
    (fun left right hsame => by
      change MulAction.orbitRel (Equiv.Perm (Fin fieldCount))
        (LabeledLocalWordSector fieldCount derivativeCount)
        left right at hsame
      rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hsame
      rcases hsame with ⟨rename, hrename⟩
      rw [← hrename]
      exact labeledPlaneTraceEvaluation_relabel matrices rename right)

@[simp] theorem orbitPlaneTraceEvaluation_mk
    {R : Type*} [CommSemiring R]
    (matrices : PlaneMatrixAssignment R)
    {fieldCount derivativeCount : ℕ}
    (sector : LabeledLocalWordSector fieldCount derivativeCount) :
    orbitPlaneTraceEvaluation matrices (Quotient.mk _ sector) =
      labeledPlaneTraceEvaluation matrices sector :=
  rfl

/-- Linear extension of matrix trace evaluation to the free orbit module. -/
def orbitPlaneTraceEvaluationLinear
    {R : Type*} [CommSemiring R]
    (matrices : PlaneMatrixAssignment R)
    (fieldCount derivativeCount : ℕ) :
    (FieldRelabelOrbitCarrier fieldCount derivativeCount →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R (orbitPlaneTraceEvaluation matrices)

@[simp] theorem orbitPlaneTraceEvaluationLinear_single
    {R : Type*} [CommSemiring R]
    (matrices : PlaneMatrixAssignment R)
    {fieldCount derivativeCount : ℕ}
    (orbit : FieldRelabelOrbitCarrier fieldCount derivativeCount)
    (coefficient : R) :
    orbitPlaneTraceEvaluationLinear matrices fieldCount derivativeCount
        (Finsupp.single orbit coefficient) =
      coefficient * orbitPlaneTraceEvaluation matrices orbit := by
  simp [orbitPlaneTraceEvaluationLinear]

end HypercubicDimension16TraceEvaluation
end YangMills
end QuantumTheory
end Mettapedia
