import KrennFrozenCase0NoncollapseAssembly

/-!
The first strict pivot-chart closure for physical non-collapse type 01.

For slot `(vertex 0, colour 1)`, the two adjugate P-kills are linear in the
three priority pivots `w_23_11`, `w_12_11`, and `w_13_11`.  This file proves
the exhaustive four-way pivot cover and closes the third chart:

* `w_23_11 = 0`,
* `w_12_11 = 0`, and
* `w_13_11 != 0`.

The nonzero pivot turns the two P-kills into `w_25_11 = w_24_11 = 0`.
Three exact frozen amplitude rows then force the slot determinant to vanish,
contradicting the non-collapse hypothesis.  The polynomial identity is the
four-generator identity independently found and strictly replayed over Q;
here Lean checks it directly against the canonical 747-row source.
-/

namespace Krenn.FrozenCase0NoncollapseType01Pivot

open Krenn.FrozenCase0AdjugateLayer
open Krenn.SparseCertificate

def sourceSystemSHA256 : String :=
  "d3aad8dda7e6e2acd6bf5ecacd780d5850418e7f74b924367e8e936746ea76bc"

def fullProfileSystemSHA256 : String :=
  "24b5c399b58c53c7e387208875748722e455372bc34fc8ef9f0644e6cda8b126"

def pivotInventorySHA256 : String :=
  "e61dccd89b333de06a7fd81e772c30a1ab73742ac9fc40194cde448ba9e1ed47"

def chart2CertificateSHA256 : String :=
  "7bcefc6d86dafce36c48eb003ccfc9e9ba25a9946f93b0a31e7979fbe2058416"

/-- The three amplitude rows in the canonical frozen source. -/
def amplitudeSourceIndex : Fin 3 → Fin 747 := ![295, 299, 360]

theorem amplitude_source_not_determinant
    (index : Fin 3) (slot : Fin 18) :
    determinantSourceIndex slot ≠ amplitudeSourceIndex index := by
  fin_cases index <;> fin_cases slot <;>
    simp [determinantSourceIndex, amplitudeSourceIndex]

/- The exact factor identity exposed by the strict four-generator
certificate.  No solver result is trusted here: all three source rows are
expanded from the canonical frozen system and the equality is normalized by
the kernel-checked `ring` tactic. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem affine_factor_identity {R : Type*} [CommRing R]
    (values : Fin 75 → R) :
    -sourceValue values 295 + sourceValue values 299
        + values 25 * sourceValue values 360 =
      slotDeterminant values 1
        + (values 25 + values 33)
          * (values 23 * values 51 + values 15 * values 56) := by
  simp [sourceValue, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2]
  ring

def factorL {R : Type*} [CommRing R] (values : Fin 75 → R) : R :=
  values 25 + values 33

def factorGa {R : Type*} [CommRing R] (values : Fin 75 → R) : R :=
  values 23 * values 64 + values 15 * values 70

def factorGb {R : Type*} [CommRing R] (values : Fin 75 → R) : R :=
  values 23 * values 51 + values 15 * values 56

def factorGu {R : Type*} [CommRing R] (values : Fin 75 → R) : R :=
  values 23 * values 42 + values 15 * values 45

/- The reflected exact factor identity.  It is the image of
`affine_factor_identity` under the case-0 reflection `(2 3)(4 5)`, but is
checked directly against the canonical frozen rows here. -/
set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem reflected_factor_identity {R : Type*} [CommRing R]
    (values : Fin 75 → R) :
    -sourceValue values 299 + sourceValue values 295
        + values 33 * sourceValue values 360 =
      -slotDeterminant values 1 + factorL values * factorGa values := by
  simp [sourceValue, Krenn.FrozenCase0System.equations,
    SparsePoly.toPoly, SparseTerm.toPoly,
    slotDeterminant, slotA1, slotB1, slotA2, slotB2,
    factorL, factorGa]
  ring

/- At any non-collapse common zero, the two reflected factor identities make
the factor geometry rigid: `L`, `Gb`, and `Ga` are nonzero up to sign, with
`Ga = -Gb`. -/
theorem noncollapse_factor_geometry
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0) :
    factorL values ≠ 0 ∧ factorGb values ≠ 0 ∧
      factorGa values = -factorGb values := by
  have amplitude0 : sourceValue values 295 = 0 :=
    base (amplitudeSourceIndex 0)
      (fun slot => amplitude_source_not_determinant 0 slot)
  have amplitude1 : sourceValue values 299 = 0 :=
    base (amplitudeSourceIndex 1)
      (fun slot => amplitude_source_not_determinant 1 slot)
  have amplitude2 : sourceValue values 360 = 0 :=
    base (amplitudeSourceIndex 2)
      (fun slot => amplitude_source_not_determinant 2 slot)
  have original := affine_factor_identity values
  have reflected := reflected_factor_identity values
  rw [amplitude0, amplitude1, amplitude2] at original reflected
  have hOriginal :
      slotDeterminant values 1 + factorL values * factorGb values = 0 := by
    simpa [factorL, factorGb] using original.symm
  have hReflected :
      -slotDeterminant values 1 + factorL values * factorGa values = 0 := by
    simpa using reflected.symm
  have hL : factorL values ≠ 0 := by
    intro h
    apply hdet
    simpa [h] using hOriginal
  have hGb : factorGb values ≠ 0 := by
    intro h
    apply hdet
    simpa [h] using hOriginal
  have hProduct : factorL values * (factorGa values + factorGb values) = 0 := by
    calc
      factorL values * (factorGa values + factorGb values) =
          (-slotDeterminant values 1 + factorL values * factorGa values) +
            (slotDeterminant values 1 + factorL values * factorGb values) := by
              ring
      _ = 0 := by rw [hReflected, hOriginal]; ring
  have hSum : factorGa values + factorGb values = 0 :=
    (mul_eq_zero.mp hProduct).resolve_left hL
  exact ⟨hL, hGb, by simpa only [eq_neg_iff_add_eq_zero] using hSum⟩

/- If the first P-kill pivot `w_23_11` vanishes, the other two coefficients
must agree.  This reduces pivot chart 1 to `w_13_11 = w_12_11` and is also
consistent with the fully zero fourth chart. -/
theorem equal_coefficients_of_w23_zero
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (h23 : values 48 = 0) : values 36 = values 28 := by
  have leftZero : slotLeft values 1 = 0 :=
    (left_kill_or_collapse values base 1).resolve_left hdet
  have rightZero : slotRight values 1 = 0 :=
    (right_kill_or_collapse values base 1).resolve_left hdet
  obtain ⟨_hL, hGb, hGa⟩ := noncollapse_factor_geometry values base hdet
  have aggregate :
      values 28 * factorGa values + values 36 * factorGb values +
        values 48 * factorGu values = 0 := by
    calc
      values 28 * factorGa values + values 36 * factorGb values +
          values 48 * factorGu values =
        values 15 * slotLeft values 1 + values 23 * slotRight values 1 := by
          simp [factorGa, factorGb, factorGu, slotLeft, slotRight]
          ring
      _ = 0 := by rw [leftZero, rightZero]; ring
  have hProduct : (values 36 - values 28) * factorGb values = 0 := by
    rw [h23, hGa] at aggregate
    have reduced :
        -(values 28 * factorGb values) +
          values 36 * factorGb values = 0 := by
      simpa only [mul_neg, zero_mul, add_zero] using aggregate
    calc
      (values 36 - values 28) * factorGb values =
          -(values 28 * factorGb values) +
            values 36 * factorGb values := by ring
      _ = 0 := reduced
  have hDifference : values 36 - values 28 = 0 :=
    (mul_eq_zero.mp hProduct).resolve_right hGb
  exact sub_eq_zero.mp hDifference

def PivotChart0 {R : Type*} [Zero R] (values : Fin 75 → R) : Prop :=
  values 48 ≠ 0

def PivotChart1 {R : Type*} [Zero R] (values : Fin 75 → R) : Prop :=
  values 48 = 0 ∧ values 28 ≠ 0

def PivotChart2 {R : Type*} [Zero R] (values : Fin 75 → R) : Prop :=
  values 48 = 0 ∧ values 28 = 0 ∧ values 36 ≠ 0

def PivotChart3 {R : Type*} [Zero R] (values : Fin 75 → R) : Prop :=
  values 48 = 0 ∧ values 28 = 0 ∧ values 36 = 0

/-- Priority pivoting on `(w_23_11,w_12_11,w_13_11)` is exhaustive. -/
theorem pivot_cover {R : Type*} [Zero R] (values : Fin 75 → R) :
    PivotChart0 values ∨ PivotChart1 values ∨
      PivotChart2 values ∨ PivotChart3 values := by
  by_cases h23 : values 48 = 0
  · by_cases h12 : values 28 = 0
    · by_cases h13 : values 36 = 0
      · exact Or.inr (Or.inr (Or.inr ⟨h23, h12, h13⟩))
      · exact Or.inr (Or.inr (Or.inl ⟨h23, h12, h13⟩))
    · exact Or.inr (Or.inl ⟨h23, h12⟩)
  · exact Or.inl h23

/-- The third pivot chart of physical non-collapse type 01 is impossible. -/
theorem refutes_slot1_pivot_chart2
    {R : Type*} [Field R] [CharZero R]
    (values : Fin 75 → R) (base : BaseCommonZero values)
    (hdet : slotDeterminant values 1 ≠ 0)
    (chart : PivotChart2 values) : False := by
  rcases chart with ⟨h23, h12, h13⟩
  have leftZero : slotLeft values 1 = 0 :=
    (left_kill_or_collapse values base 1).resolve_left hdet
  have rightZero : slotRight values 1 = 0 :=
    (right_kill_or_collapse values base 1).resolve_left hdet
  have h25 : values 56 = 0 := by
    have productZero : values 36 * values 56 = 0 := by
      simpa [slotLeft, h23, h12] using leftZero
    exact (mul_eq_zero.mp productZero).resolve_left h13
  have h24 : values 51 = 0 := by
    have productZero : values 36 * values 51 = 0 := by
      simpa [slotRight, h23, h12] using rightZero
    exact (mul_eq_zero.mp productZero).resolve_left h13
  have amplitude0 : sourceValue values 295 = 0 :=
    base (amplitudeSourceIndex 0)
      (fun slot => amplitude_source_not_determinant 0 slot)
  have amplitude1 : sourceValue values 299 = 0 :=
    base (amplitudeSourceIndex 1)
      (fun slot => amplitude_source_not_determinant 1 slot)
  have amplitude2 : sourceValue values 360 = 0 :=
    base (amplitudeSourceIndex 2)
      (fun slot => amplitude_source_not_determinant 2 slot)
  have factor := affine_factor_identity values
  rw [amplitude0, amplitude1, amplitude2, h24, h25] at factor
  apply hdet
  simpa using factor.symm

#print axioms affine_factor_identity
#print axioms reflected_factor_identity
#print axioms noncollapse_factor_geometry
#print axioms equal_coefficients_of_w23_zero
#print axioms pivot_cover
#print axioms refutes_slot1_pivot_chart2

end Krenn.FrozenCase0NoncollapseType01Pivot
