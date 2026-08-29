import Mathlib

/-!
Semantic reflection for lattice consequences of active binomial equations.

The certificate format used here contains only oriented uses of source
binomials.  An exponent-balance identity turns it into a polynomial identity
with one common nonzero auxiliary factor.  Cancelling that factor proves the
target binomial, while variables shared by the target monomials may still be
zero.
-/

namespace Krenn.LatticeCombinationReflection

universe u v w

/-- A coefficient-free binomial with sparse natural exponent vectors. -/
structure Binomial (κ : Type u) where
  left : κ →₀ ℕ
  right : κ →₀ ℕ
deriving DecidableEq

/-- One use of a source binomial.  `forward = true` records coefficient `+1`
in the exponent-difference combination; `false` records coefficient `-1`. -/
structure OrientedRelation (ι : Type v) where
  index : ι
  forward : Bool
deriving DecidableEq, Repr

/-- Evaluate a sparse natural exponent vector as a monomial. -/
def monomial {κ R : Type*} [CommMonoid R]
    (values : κ → R) (exponent : κ →₀ ℕ) : R :=
  exponent.prod fun coordinate power => values coordinate ^ power

/-- Exponents placed beside the target's left monomial after rearranging an
integer combination of binomial exponent differences. -/
noncomputable def leftAuxiliaryExponent {κ ι : Type*}
    (relations : ι → Binomial κ) (chain : List (OrientedRelation ι)) : κ →₀ ℕ :=
  (chain.map fun use =>
    if use.forward then (relations use.index).right
    else (relations use.index).left).sum

/-- Exponents placed beside the target's right monomial after rearranging an
integer combination of binomial exponent differences. -/
noncomputable def rightAuxiliaryExponent {κ ι : Type*}
    (relations : ι → Binomial κ) (chain : List (OrientedRelation ι)) : κ →₀ ℕ :=
  (chain.map fun use =>
    if use.forward then (relations use.index).left
    else (relations use.index).right).sum

/-- A signed-relation-chain certificate is a literal equality of natural
exponent vectors.  It is finite, decidable data. -/
def ExponentBalance {κ ι : Type*}
    (relations : ι → Binomial κ) (target : Binomial κ)
    (chain : List (OrientedRelation ι)) : Prop :=
  target.left + leftAuxiliaryExponent relations chain =
  target.right + rightAuxiliaryExponent relations chain

/-- Coordinates used by at least one relation occurrence in a chain. -/
def UsedCoordinate {κ ι : Type*}
    (relations : ι → Binomial κ) (chain : List (OrientedRelation ι))
    (coordinate : κ) : Prop :=
  ∃ use ∈ chain,
    (relations use.index).left coordinate ≠ 0 ∨
      (relations use.index).right coordinate ≠ 0

/-- Monomial evaluation turns exponent addition into multiplication. -/
theorem monomial_add {κ R : Type*} [CommMonoid R]
    (values : κ → R) (first second : κ →₀ ℕ) :
    monomial values (first + second) =
      monomial values first * monomial values second := by
  classical
  apply Finsupp.prod_add_index
  · intro coordinate member
    simp
  · intro coordinate member firstPower secondPower
    exact pow_add (values coordinate) firstPower secondPower

/-- Pushing an exponent vector through a coordinate map preserves monomial
evaluation.  Repeated target coordinates are handled by `mapDomain` adding
their exponents, so injectivity of the coordinate map is not required. -/
theorem monomial_mapDomain {κ μ R : Type*} [DecidableEq κ] [DecidableEq μ]
    [CommMonoid R] (map : κ → μ) (values : μ → R) (exponent : κ →₀ ℕ) :
    monomial (fun coordinate => values (map coordinate)) exponent =
      monomial values (Finsupp.mapDomain map exponent) := by
  classical
  induction exponent using Finsupp.induction with
  | zero => simp [monomial]
  | single_add coordinate power rest _ powerNonzero inductionHypothesis =>
      rw [monomial_add, Finsupp.mapDomain_add, monomial_add,
        Finsupp.mapDomain_single, inductionHypothesis]
      simp [monomial]

/-- Evaluation of a finite sum of exponent vectors. -/
theorem monomial_list_sum {κ R : Type*} [CommMonoid R]
    (values : κ → R) (exponents : List (κ →₀ ℕ)) :
    monomial values exponents.sum =
      (exponents.map (monomial values)).prod := by
  induction exponents with
  | nil => simp [monomial]
  | cons head tail inductionHypothesis =>
      simp [monomial_add, inductionHypothesis]

/-- A sparse monomial is nonzero when all coordinates in its support are
nonzero. -/
theorem monomial_ne_zero_of_support {κ R : Type*}
    [CommMonoidWithZero R] [Nontrivial R] [NoZeroDivisors R]
    (values : κ → R) (exponent : κ →₀ ℕ)
    (coordinatesNonzero : ∀ coordinate ∈ exponent.support,
      values coordinate ≠ 0) :
    monomial values exponent ≠ 0 := by
  classical
  rw [monomial]
  apply Finset.prod_ne_zero_iff.mpr
  intro coordinate member
  exact pow_ne_zero _ (coordinatesNonzero coordinate member)

/-- The two auxiliary monomials evaluate equally because each source
binomial may be used in either orientation. -/
theorem auxiliary_monomials_eq {κ ι R : Type*} [CommMonoid R]
    (relations : ι → Binomial κ) (chain : List (OrientedRelation ι))
    (values : κ → R)
    (relationEq : ∀ index,
      monomial values (relations index).left =
        monomial values (relations index).right) :
    monomial values (leftAuxiliaryExponent relations chain) =
      monomial values (rightAuxiliaryExponent relations chain) := by
  classical
  simp only [leftAuxiliaryExponent, rightAuxiliaryExponent,
    monomial_list_sum]
  induction chain with
  | nil => simp
  | cons use tail inductionHypothesis =>
      simp only [List.map_cons, List.prod_cons, List.map_map] at inductionHypothesis ⊢
      cases use.forward <;>
        simp [relationEq use.index, inductionHypothesis]

/-- Nonvanishing of each used source binomial makes the common auxiliary
factor cancellable.  It is enough to require the left monomial: source
equality transfers nonvanishing to the right one. -/
theorem leftAuxiliary_monomial_ne_zero {κ ι R : Type*}
    [CommMonoidWithZero R] [Nontrivial R] [NoZeroDivisors R]
    (relations : ι → Binomial κ) (chain : List (OrientedRelation ι))
    (values : κ → R)
    (relationEq : ∀ index,
      monomial values (relations index).left =
        monomial values (relations index).right)
    (usedLeftNonzero : ∀ use ∈ chain,
      monomial values (relations use.index).left ≠ 0) :
    monomial values (leftAuxiliaryExponent relations chain) ≠ 0 := by
  classical
  rw [leftAuxiliaryExponent, monomial_list_sum]
  induction chain with
  | nil => simp
  | cons use tail inductionHypothesis =>
      have headLeftNonzero := usedLeftNonzero use (by simp)
      have tailNonzero : ∀ item ∈ tail,
          monomial values (relations item.index).left ≠ 0 := by
        intro item member
        exact usedLeftNonzero item (by simp [member])
      have tailProductNonzero := inductionHypothesis tailNonzero
      cases h : use.forward <;> simp only [List.map_cons, List.prod_cons,
        Bool.false_eq_true, ↓reduceIte, h]
      · exact mul_ne_zero headLeftNonzero tailProductNonzero
      · exact mul_ne_zero (relationEq use.index ▸ headLeftNonzero)
          tailProductNonzero

/-- A checked signed relation chain proves the target binomial.  Notice that
no target coordinate is assumed nonzero: a shared zero factor is harmless,
because cancellation is performed only on the active source relations. -/
theorem target_monomials_eq_of_signed_relation_chain
    {κ ι R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (relations : ι → Binomial κ) (target : Binomial κ)
    (chain : List (OrientedRelation ι)) (values : κ → R)
    (relationEq : ∀ index,
      monomial values (relations index).left =
        monomial values (relations index).right)
    (usedLeftNonzero : ∀ use ∈ chain,
      monomial values (relations use.index).left ≠ 0)
    (balance : ExponentBalance relations target chain) :
    monomial values target.left = monomial values target.right := by
  have exponentEvaluation := congrArg (monomial values) balance
  rw [monomial_add, monomial_add] at exponentEvaluation
  have auxiliaryEq := auxiliary_monomials_eq relations chain values relationEq
  rw [auxiliaryEq] at exponentEvaluation
  have rightAuxiliaryNonzero :
      monomial values (rightAuxiliaryExponent relations chain) ≠ 0 := by
    rw [← auxiliaryEq]
    exact leftAuxiliary_monomial_ne_zero relations chain values relationEq
      usedLeftNonzero
  exact mul_right_cancel₀
    rightAuxiliaryNonzero
    exponentEvaluation

/-- Variable-level interface used by support-stratum certificates.  Only
coordinates appearing in a used source relation must be nonzero; target-only
or target-shared coordinates carry no such assumption. -/
theorem target_monomials_eq_of_active_signed_relation_chain
    {κ ι R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (relations : ι → Binomial κ) (target : Binomial κ)
    (chain : List (OrientedRelation ι)) (values : κ → R)
    (relationEq : ∀ index,
      monomial values (relations index).left =
        monomial values (relations index).right)
    (activeNonzero : ∀ coordinate,
      UsedCoordinate relations chain coordinate → values coordinate ≠ 0)
    (balance : ExponentBalance relations target chain) :
    monomial values target.left = monomial values target.right := by
  apply target_monomials_eq_of_signed_relation_chain relations target chain
    values relationEq
  · intro use member
    apply monomial_ne_zero_of_support
    intro coordinate inSupport
    apply activeNonzero coordinate
    exact ⟨use, member, Or.inl (Finsupp.mem_support_iff.mp inSupport)⟩
  · exact balance

section Sanity

/-- The first sanity certificate transports `x = y` to `x * z = y * z`.
The shared coordinate `z` is deliberately absent from the active relation. -/
noncomputable def sanityRelations : Fin 1 → Binomial (Fin 3)
  | 0 =>
    { left := Finsupp.single 0 1
      right := Finsupp.single 1 1 }

noncomputable def sanityTarget : Binomial (Fin 3) :=
  { left := Finsupp.single 0 1 + Finsupp.single 2 1
    right := Finsupp.single 1 1 + Finsupp.single 2 1 }

def sanityChain : List (OrientedRelation (Fin 1)) :=
  [{ index := 0, forward := true }]

theorem sanityBalance :
    ExponentBalance sanityRelations sanityTarget sanityChain := by
  classical
  ext coordinate
  fin_cases coordinate <;>
    simp [sanityTarget, sanityChain, sanityRelations,
      leftAuxiliaryExponent, rightAuxiliaryExponent]

/-- Concrete mutation guard for the subtle case: the target's shared factor
is zero, but the active relation variables are nonzero. -/
example :
    monomial (fun coordinate : Fin 3 =>
      match coordinate with
      | 0 => (2 : ℚ)
      | 1 => 2
      | 2 => 0) sanityTarget.left =
    monomial (fun coordinate : Fin 3 =>
      match coordinate with
      | 0 => (2 : ℚ)
      | 1 => 2
      | 2 => 0) sanityTarget.right := by
  let values : Fin 3 → ℚ := fun coordinate =>
    match coordinate with
    | 0 => 2
    | 1 => 2
    | 2 => 0
  change monomial values sanityTarget.left = monomial values sanityTarget.right
  apply target_monomials_eq_of_signed_relation_chain sanityRelations
    sanityTarget sanityChain values
  · intro index
    fin_cases index
    simp [sanityRelations, monomial, values]
  · intro use member
    simp [sanityChain] at member
    subst use
    simp [sanityRelations, monomial, values]
  · exact sanityBalance

end Sanity

end Krenn.LatticeCombinationReflection

#print axioms Krenn.LatticeCombinationReflection.target_monomials_eq_of_signed_relation_chain
#print axioms Krenn.LatticeCombinationReflection.target_monomials_eq_of_active_signed_relation_chain
