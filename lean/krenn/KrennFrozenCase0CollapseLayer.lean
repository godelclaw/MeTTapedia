import KrennCollapseReductionReflection
import KrennCollapseStratumSound
import KrennFrozenCase0System
import KrennSparseCertificate

/-!
The frozen C6 case-0 system contains the eighteen collapse determinants as
polynomials in its 75 coordinates.  This file makes their coordinate map
explicit and proves that this frozen layer implies the abstract 30-coordinate
collapse layer used by the support-cover connector.

It deliberately stops at that interface: the separate full-system bridge must
still establish that these eighteen concrete equations occur among the 747
normalized case-0 equations.
-/

namespace Krenn.FrozenCase0CollapseLayer

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.LatticeCombinationReflection
open Krenn.CollapseReductionReflection
open Krenn.CollapseSupportCover
open Krenn.CollapseSupportCover.Semantic
open Krenn.CollapseSupportCover.GlobalFormula
open Krenn.CollapseFeasibility
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData

/-- The thirty off-diagonal collapse coordinates inside the frozen
75-coordinate C6 case-0 system. -/
def rawCoordinate : Fin 30 → Fin 75 := ![
  10, 11, 13, 14, 15,
  18, 19, 21, 22, 23,
  26, 27, 29, 30, 31,
  34, 35, 37, 38, 39,
  54, 55, 57, 58, 59,
  62, 63, 65, 66, 67
]

/-- Restrict a frozen case-0 valuation to the raw collapse vocabulary. -/
def rawValues {R : Type*} (full : Fin 75 → R) : Fin 30 → R :=
  fun coordinate => full (rawCoordinate coordinate)

/-- The frozen map uses thirty distinct source coordinates. -/
theorem rawCoordinate_injective : Function.Injective rawCoordinate := by
  intro left right equal
  fin_cases left <;> fin_cases right <;> simp [rawCoordinate] at equal ⊢

/-- The eighteen frozen collapse equations.  They are stored in exactly the
same sign convention as `rawDeterminantValue`. -/
noncomputable def frozenCollapseEquation : Fin 18 → SparsePoly (Fin 75) := ![
  [{ coefficient := 1, powers := [(62, 1)] },
   { coefficient := -1, powers := [(10, 1)] }],
  [{ coefficient := 1, powers := [(23, 1)] },
   { coefficient := -1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(54, 1)] },
   { coefficient := -1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(39, 1)] },
   { coefficient := -1, powers := [(31, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (21, 1)] },
   { coefficient := -1, powers := [(13, 1), (18, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (22, 1)] },
   { coefficient := -1, powers := [(14, 1), (19, 1)] }],
  [{ coefficient := 1, powers := [(11, 1), (65, 1)] },
   { coefficient := -1, powers := [(13, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(14, 1), (67, 1)] },
   { coefficient := -1, powers := [(15, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(19, 1), (57, 1)] },
   { coefficient := -1, powers := [(21, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (59, 1)] },
   { coefficient := -1, powers := [(23, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (37, 1)] },
   { coefficient := -1, powers := [(29, 1), (34, 1)] }],
  [{ coefficient := 1, powers := [(58, 1)] },
   { coefficient := -1, powers := [(26, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (38, 1)] },
   { coefficient := -1, powers := [(30, 1), (35, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (59, 1)] },
   { coefficient := -1, powers := [(29, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (57, 1)] },
   { coefficient := -1, powers := [(31, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(66, 1)] },
   { coefficient := -1, powers := [(34, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(35, 1), (67, 1)] },
   { coefficient := -1, powers := [(37, 1)] }],
  [{ coefficient := 1, powers := [(38, 1), (65, 1)] },
   { coefficient := -1, powers := [(39, 1), (62, 1)] }]
]

noncomputable def frozenCollapseValue {R : Type*} [CommRing R]
    (full : Fin 75 → R) (determinant : Fin 18) : R :=
  eval₂Hom (Int.castRingHom R) full
    (frozenCollapseEquation determinant).toPoly

/-- The frozen subset of the case-0 equations used by the collapse bridge. -/
noncomputable def FrozenCollapseLayer {R : Type*} [CommRing R]
    (full : Fin 75 → R) : Prop :=
  ∀ determinant, frozenCollapseValue full determinant = 0

/-- Positions of the eighteen collapse equations in the frozen 747-equation
case-0 source system.  The positions are zero-based source indices. -/
def collapseSourceIndex : Fin 18 → Fin 747 :=
  ![0, 1, 2, 3, 4, 6, 7, 21, 33, 34, 35, 36, 37, 38, 39, 41, 42, 43]

/-- The recorded source positions are pairwise distinct, so the collapse
layer does not accidentally reuse one equation under two labels. -/
theorem collapseSourceIndex_injective : Function.Injective collapseSourceIndex := by
  intro left right equal
  fin_cases left <;> fin_cases right <;> simp [collapseSourceIndex] at equal ⊢

/- Each frozen collapse polynomial agrees, as a polynomial rather than just
as a textual term list, with the indicated equation in the complete frozen
case-0 system. -/
set_option maxRecDepth 100000 in
theorem frozenCollapsePolynomial_eq_source
    (determinant : Fin 18) :
    (frozenCollapseEquation determinant).toPoly =
      (Krenn.FrozenCase0System.equations
        (collapseSourceIndex determinant)).toPoly := by
  fin_cases determinant <;>
    simp [frozenCollapseEquation, collapseSourceIndex,
      Krenn.FrozenCase0System.equations, SparsePoly.toPoly,
      SparseTerm.toPoly] <;>
    ring

/-- Evaluating a frozen collapse polynomial is exactly evaluating its raw
counterpart after restricting to the thirty recorded coordinates. -/
theorem frozenCollapseValue_eq_rawDeterminantValue
    {R : Type*} [CommRing R] (full : Fin 75 → R) (determinant : Fin 18) :
    frozenCollapseValue full determinant =
      rawDeterminantValue (rawValues full) determinant := by
  fin_cases determinant <;>
    simp [frozenCollapseValue, frozenCollapseEquation, rawDeterminantValue,
      rawDeterminant, rawValues, rawCoordinate, SparsePoly.toPoly,
      SparseTerm.toPoly, monomial_add, monomial_single_one] <;>
    ring

/-- A common zero of the complete frozen case-0 system satisfies its eighteen
recorded collapse equations. -/
theorem frozen_layer_of_base_common_zero
    {R : Type*} [CommRing R] (full : Fin 75 → R)
    (base : Krenn.FrozenCase0System.CommonZero full) :
    FrozenCollapseLayer full := by
  intro determinant
  change eval₂Hom (Int.castRingHom R) full
    (frozenCollapseEquation determinant).toPoly = 0
  rw [frozenCollapsePolynomial_eq_source]
  simpa [Krenn.FrozenCase0System.CommonZero] using
    base (collapseSourceIndex determinant)

/-- The explicit frozen case-0 collapse layer entails the abstract raw
collapse hypothesis consumed by the reduction and support-cover theorems. -/
theorem raw_collapse_of_frozen_layer
    {R : Type*} [CommRing R] (full : Fin 75 → R)
    (collapse : FrozenCollapseLayer full) :
    SatisfiesRawCollapse (rawValues full) := by
  intro determinant
  rw [← frozenCollapseValue_eq_rawDeterminantValue]
  exact collapse determinant

/-- The full frozen C6 case-0 equation system reaches the abstract raw
collapse premise used by the kernel-checked support-cover connector. -/
theorem raw_collapse_of_base_common_zero
    {R : Type*} [CommRing R] (full : Fin 75 → R)
    (base : Krenn.FrozenCase0System.CommonZero full) :
    SatisfiesRawCollapse (rawValues full) :=
  raw_collapse_of_frozen_layer full (frozen_layer_of_base_common_zero full base)

/-- The full frozen C6 case-0 system reaches the kernel-checked support-cover
conclusion: some certified component contains its reduced collapse valuation.
This is membership only; component-specific full-system refutations remain a
separate bridge obligation. -/
theorem base_common_zero_stratum_sound
    {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (full : Fin 75 → R) (base : Krenn.FrozenCase0System.CommonZero full) :
    ∃ stratum ∈ strata,
      Covers stratum (supportPattern (reduceRaw (rawValues full))) ∧
        ∀ generator ∈ componentGenerators stratum.component,
          generatorEval (reduceRaw (rawValues full)) generator = 0 := by
  exact Krenn.CollapseStratumSound.raw_collapse_stratum_sound
    (rawValues full) (raw_collapse_of_base_common_zero full base)

end Krenn.FrozenCase0CollapseLayer

#print axioms Krenn.FrozenCase0CollapseLayer.base_common_zero_stratum_sound
