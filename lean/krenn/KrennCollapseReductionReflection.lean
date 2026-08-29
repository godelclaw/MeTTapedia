import KrennLatticeCombinationReflection

/-!
Reflection bridge from the eighteen gauge-fixed local collapse determinants
to the fourteen reduced binomial relations used by the support-cover proof.

The raw vocabulary has thirty coordinates.  Four linear determinants identify
four of them with chosen representatives; the resulting quotient vocabulary
has twenty-six coordinates.  All data below are explicit, so the inventory
and every substitution can be checked by kernel reduction.
-/

namespace Krenn.CollapseReductionReflection

open Krenn.LatticeCombinationReflection

/-- The fourteen concrete reduced binomials consumed by the support-cover
layer.  This small vocabulary is kept here so the reduction bridge can be
checked independently of the much larger containment-certificate corpus. -/
noncomputable def reducedRelation : Fin 14 → Binomial (Fin 26) := ![
    { left := Finsupp.single 0 1 + Finsupp.single 7 1
      right := Finsupp.single 2 1 + Finsupp.single 5 1 },

    { left := Finsupp.single 0 1 + Finsupp.single 13 1
      right := Finsupp.single 17 1 + Finsupp.single 23 1 },

    { left := Finsupp.single 1 1 + Finsupp.single 8 1
      right := Finsupp.single 3 1 + Finsupp.single 6 1 },

    { left := Finsupp.single 1 1 + Finsupp.single 23 1
      right := Finsupp.single 2 1 + Finsupp.single 22 1 },

    { left := Finsupp.single 3 1 + Finsupp.single 25 1
      right := Finsupp.single 4 1 + Finsupp.single 24 1 },

    { left := Finsupp.single 4 1 + Finsupp.single 20 1
      right := Finsupp.single 8 1 + Finsupp.single 21 1 },

    { left := Finsupp.single 5 1 + Finsupp.single 13 1
      right := Finsupp.single 12 1 + Finsupp.single 19 1 },

    { left := Finsupp.single 6 1 + Finsupp.single 19 1
      right := Finsupp.single 7 1 + Finsupp.single 18 1 },

    { left := Finsupp.single 9 1 + Finsupp.single 16 1
      right := Finsupp.single 11 1 + Finsupp.single 14 1 },

    { left := Finsupp.single 9 1 + Finsupp.single 18 1
      right := Finsupp.single 20 1 },

    { left := Finsupp.single 10 1 + Finsupp.single 17 1
      right := Finsupp.single 12 1 + Finsupp.single 15 1 },

    { left := Finsupp.single 10 1 + Finsupp.single 21 1
      right := Finsupp.single 11 1 },

    { left := Finsupp.single 14 1 + Finsupp.single 22 1
      right := Finsupp.single 24 1 },

    { left := Finsupp.single 15 1 + Finsupp.single 25 1
      right := Finsupp.single 16 1 }
  ]

@[simp] theorem monomial_single_one {κ R : Type*} [CommMonoid R]
    (values : κ → R) (coordinate : κ) :
    monomial values (Finsupp.single coordinate 1) = values coordinate := by
  classical
  simp [monomial]

/-- Quotient map implementing the four explicit substitutions:
`25 ↦ 0`, `9 ↦ 4`, `20 ↦ 5`, and `19 ↦ 13`. -/
def rawToReduced : Fin 30 → Fin 26
  := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 4, 9, 10, 11, 12, 13,
    14, 15, 16, 17, 13, 5, 18, 19, 20, 21, 0, 22, 23, 24, 25]

/-- Chosen representative of every reduced coordinate. -/
def reducedRepresentative : Fin 26 → Fin 30
  := ![0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13,
    14, 15, 16, 17, 18, 21, 22, 23, 24, 26, 27, 28, 29]

theorem rawToReduced_reducedRepresentative (coordinate : Fin 26) :
    rawToReduced (reducedRepresentative coordinate) = coordinate := by
  fin_cases coordinate <;> rfl

/-- The eighteen nonzero gauge-fixed collapse determinants.  Each equation is
stored as equality of its positive and negative monomial.  Entries `0`–`3`
are the four linear identifications. -/
noncomputable def rawDeterminant : Fin 18 → Binomial (Fin 30) := ![

    { left := Finsupp.single 25 1
      right := Finsupp.single 0 1 },

    { left := Finsupp.single 9 1
      right := Finsupp.single 4 1 },

    { left := Finsupp.single 20 1
      right := Finsupp.single 5 1 },

    { left := Finsupp.single 19 1
      right := Finsupp.single 14 1 },

    { left := Finsupp.single 0 1 + Finsupp.single 7 1
      right := Finsupp.single 2 1 + Finsupp.single 5 1 },

    { left := Finsupp.single 1 1 + Finsupp.single 8 1
      right := Finsupp.single 3 1 + Finsupp.single 6 1 },

    { left := Finsupp.single 1 1 + Finsupp.single 27 1
      right := Finsupp.single 2 1 + Finsupp.single 26 1 },

    { left := Finsupp.single 3 1 + Finsupp.single 29 1
      right := Finsupp.single 4 1 + Finsupp.single 28 1 },

    { left := Finsupp.single 6 1 + Finsupp.single 22 1
      right := Finsupp.single 7 1 + Finsupp.single 21 1 },

    { left := Finsupp.single 8 1 + Finsupp.single 24 1
      right := Finsupp.single 9 1 + Finsupp.single 23 1 },

    { left := Finsupp.single 10 1 + Finsupp.single 17 1
      right := Finsupp.single 12 1 + Finsupp.single 15 1 },

    { left := Finsupp.single 23 1
      right := Finsupp.single 10 1 + Finsupp.single 21 1 },

    { left := Finsupp.single 11 1 + Finsupp.single 18 1
      right := Finsupp.single 13 1 + Finsupp.single 16 1 },

    { left := Finsupp.single 11 1 + Finsupp.single 24 1
      right := Finsupp.single 12 1 },

    { left := Finsupp.single 13 1 + Finsupp.single 22 1
      right := Finsupp.single 14 1 + Finsupp.single 20 1 },

    { left := Finsupp.single 28 1
      right := Finsupp.single 15 1 + Finsupp.single 26 1 },

    { left := Finsupp.single 16 1 + Finsupp.single 29 1
      right := Finsupp.single 17 1 },

    { left := Finsupp.single 18 1 + Finsupp.single 27 1
      right := Finsupp.single 19 1 + Finsupp.single 25 1 }
  ]

/-- Polynomial value of one raw determinant. -/
noncomputable def rawDeterminantValue {R : Type*} [CommRing R]
    (values : Fin 30 → R) (determinant : Fin 18) : R :=
  monomial values (rawDeterminant determinant).left -
    monomial values (rawDeterminant determinant).right

/-- The gauge-fixed local collapse system, stated in its native
determinant-equals-zero form. -/
noncomputable def SatisfiesRawCollapse {R : Type*} [CommRing R]
    (values : Fin 30 → R) : Prop :=
  ∀ determinant, rawDeterminantValue values determinant = 0

theorem raw_binomial_equalities_of_collapse
    {R : Type*} [CommRing R] {values : Fin 30 → R}
    (collapse : SatisfiesRawCollapse values) :
    ∀ determinant,
      monomial values (rawDeterminant determinant).left =
        monomial values (rawDeterminant determinant).right := by
  intro determinant
  exact sub_eq_zero.mp (collapse determinant)

/-- Pull a reduced valuation back along the quotient map. -/
def liftReduced {R : Type*} (values : Fin 26 → R) : Fin 30 → R :=
  fun coordinate => values (rawToReduced coordinate)

/-- Restrict a raw valuation to the chosen quotient representatives. -/
def reduceRaw {R : Type*} (values : Fin 30 → R) : Fin 26 → R :=
  fun coordinate => values (reducedRepresentative coordinate)

theorem reduceRaw_liftReduced {R : Type*} (values : Fin 26 → R) :
    reduceRaw (liftReduced values) = values := by
  funext coordinate
  simp [reduceRaw, liftReduced, rawToReduced_reducedRepresentative]

/-- The four linear determinant equations make a raw valuation equal to the
pullback of its restriction to quotient representatives. -/
theorem raw_eq_liftReduced_reduceRaw
    {R : Type*} [CommMonoid R]
    (values : Fin 30 → R)
    (satisfies : ∀ determinant,
      monomial values (rawDeterminant determinant).left =
        monomial values (rawDeterminant determinant).right) :
    values = liftReduced (reduceRaw values) := by
  have identification0 : values 25 = values 0 := by
    simpa [rawDeterminant, monomial] using satisfies 0
  have identification1 : values 9 = values 4 := by
    simpa [rawDeterminant, monomial] using satisfies 1
  have identification2 : values 20 = values 5 := by
    simpa [rawDeterminant, monomial] using satisfies 2
  have identification3 : values 19 = values 14 := by
    simpa [rawDeterminant, monomial] using satisfies 3
  funext coordinate
  fin_cases coordinate <;>
    simp [liftReduced, reduceRaw, rawToReduced, reducedRepresentative,
      identification0, identification1, identification2, identification3]

/-- Generic finite-substitution seam: after the quotient identifications, the
fourteen non-linear raw determinants are exactly the concrete reduced
relations used below. -/
theorem reduced_relations_of_identified_raw_determinants
    {R : Type*} [CommMonoid R]
    (values : Fin 30 → R)
    (identified : values = liftReduced (reduceRaw values))
    (satisfies : ∀ determinant,
      monomial values (rawDeterminant determinant).left =
        monomial values (rawDeterminant determinant).right) :
    ∀ index,
      monomial (reduceRaw values) (reducedRelation index).left =
        monomial (reduceRaw values) (reducedRelation index).right := by
  have reducedSatisfies : ∀ determinant,
      monomial (liftReduced (reduceRaw values))
          (rawDeterminant determinant).left =
        monomial (liftReduced (reduceRaw values))
          (rawDeterminant determinant).right := by
    intro determinant
    rw [← identified]
    exact satisfies determinant
  intro index
  fin_cases index
  · simpa [reducedRelation, rawDeterminant, monomial_add, monomial_single_one, liftReduced,
      rawToReduced] using reducedSatisfies 4
  · simpa [reducedRelation, rawDeterminant, monomial_add, monomial_single_one, liftReduced,
      rawToReduced, mul_comm] using (reducedSatisfies 17).symm
  · simpa [reducedRelation, rawDeterminant, monomial_add, monomial_single_one, liftReduced,
      rawToReduced] using reducedSatisfies 5
  · simpa [reducedRelation, rawDeterminant, monomial_add, monomial_single_one, liftReduced,
      rawToReduced] using reducedSatisfies 6
  · simpa [reducedRelation, rawDeterminant, monomial_add, monomial_single_one, liftReduced,
      rawToReduced] using reducedSatisfies 7
  · simpa [reducedRelation, rawDeterminant, monomial_add, monomial_single_one, liftReduced,
      rawToReduced, mul_comm] using (reducedSatisfies 9).symm
  · simpa [reducedRelation, rawDeterminant, monomial_add, monomial_single_one, liftReduced,
      rawToReduced, mul_comm] using (reducedSatisfies 14).symm
  · simpa [reducedRelation, rawDeterminant, monomial_add, monomial_single_one, liftReduced,
      rawToReduced] using reducedSatisfies 8
  · simpa [reducedRelation, rawDeterminant, monomial_add, monomial_single_one, liftReduced,
      rawToReduced] using reducedSatisfies 10
  · simpa [reducedRelation, rawDeterminant, monomial_add, monomial_single_one, liftReduced,
      rawToReduced, mul_comm] using (reducedSatisfies 11).symm
  · simpa [reducedRelation, rawDeterminant, monomial_add, monomial_single_one, liftReduced,
      rawToReduced] using reducedSatisfies 12
  · simpa [reducedRelation, rawDeterminant, monomial_add, monomial_single_one, liftReduced,
      rawToReduced] using reducedSatisfies 13
  · simpa [reducedRelation, rawDeterminant, monomial_add, monomial_single_one, liftReduced,
      rawToReduced, mul_comm] using (reducedSatisfies 15).symm
  · simpa [reducedRelation, rawDeterminant, monomial_add, monomial_single_one, liftReduced,
      rawToReduced] using reducedSatisfies 16

/-- Main connector: the eighteen raw local collapse determinants imply every
reduced relation, with the four substitutions derived from the first four
determinants rather than assumed. -/
theorem reduced_relations_of_raw_determinants
    {R : Type*} [CommMonoid R]
    (values : Fin 30 → R)
    (satisfies : ∀ determinant,
      monomial values (rawDeterminant determinant).left =
        monomial values (rawDeterminant determinant).right) :
    ∀ index,
      monomial (reduceRaw values) (reducedRelation index).left =
        monomial (reduceRaw values) (reducedRelation index).right := by
  apply reduced_relations_of_identified_raw_determinants values
  · exact raw_eq_liftReduced_reduceRaw values satisfies
  · exact satisfies

/-- Native determinant-zero form of the connector theorem. -/
theorem reduced_relations_of_raw_collapse
    {R : Type*} [CommRing R]
    (values : Fin 30 → R) (collapse : SatisfiesRawCollapse values) :
    ∀ index,
      monomial (reduceRaw values) (reducedRelation index).left =
        monomial (reduceRaw values) (reducedRelation index).right :=
  reduced_relations_of_raw_determinants values
    (raw_binomial_equalities_of_collapse collapse)

end Krenn.CollapseReductionReflection

#print axioms Krenn.CollapseReductionReflection.reduced_relations_of_raw_collapse
