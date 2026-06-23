import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mettapedia.GraphTheory.FourColor.ColorAlgebra
import Mettapedia.GraphTheory.FourColor.BoundaryChainPeel

open scoped BigOperators

namespace Mettapedia.GraphTheory.FourColor

/-- The coordinatewise `𝔽₂` dot product on `𝔽₂²`. -/
def colorDot (x y : Color) : F2 :=
  x.1 * y.1 + x.2 * y.2

@[simp] theorem colorDot_zero_left (x : Color) : colorDot 0 x = 0 := by
  simp [colorDot]

@[simp] theorem colorDot_zero_right (x : Color) : colorDot x 0 = 0 := by
  simp [colorDot]

theorem colorDot_comm (x y : Color) : colorDot x y = colorDot y x := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp [colorDot, mul_comm]

theorem colorDot_add_left (x y z : Color) :
    colorDot (x + y) z = colorDot x z + colorDot y z := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  rcases z with ⟨z₁, z₂⟩
  simp [colorDot, add_mul, add_assoc, add_left_comm]

theorem colorDot_add_right (x y z : Color) :
    colorDot x (y + z) = colorDot x y + colorDot x z := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  rcases z with ⟨z₁, z₂⟩
  simp [colorDot, mul_add, add_assoc, add_left_comm]

@[simp] theorem colorDot_red_right (x : Color) : colorDot x red = x.1 := by
  simp [colorDot, red]

@[simp] theorem colorDot_blue_right (x : Color) : colorDot x blue = x.2 := by
  simp [colorDot, blue]

@[simp] theorem colorDot_purple_right (x : Color) : colorDot x purple = x.1 + x.2 := by
  simp [colorDot, purple]

theorem eq_zero_or_eq_red_or_eq_blue_or_eq_purple (c : Color) :
    c = 0 ∨ c = red ∨ c = blue ∨ c = purple := by
  rcases c with ⟨x, y⟩
  fin_cases x <;> fin_cases y <;> simp [red, blue, purple]

theorem eq_red_or_eq_blue_or_eq_purple_of_ne_zero (c : Color) (hc : c ≠ 0) :
    c = red ∨ c = blue ∨ c = purple := by
  rcases eq_zero_or_eq_red_or_eq_blue_or_eq_purple c with h0 | hr | hb | hp
  · exact False.elim (hc h0)
  · exact Or.inl hr
  · exact Or.inr <| Or.inl hb
  · exact Or.inr <| Or.inr hp

/-- Every nonzero color has a color-dual witness with dot product `1`. -/
theorem exists_colorDot_one_of_ne_zero (c : Color) (hc : c ≠ 0) :
    ∃ w : Color, colorDot c w = 1 := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl
  · exact ⟨red, by simp [colorDot, red]⟩
  · exact ⟨blue, by simp [colorDot, blue]⟩
  · exact ⟨red, by simp [colorDot, purple, red]⟩

/-- A color that annihilates both nonzero colors different from `d` must vanish. This is the local
`𝔽₂²` algebra used in the leaf-elimination step of Theorem 4.9. -/
theorem eq_zero_of_colorDot_eq_zero_for_all_nonzero_ne {z d : Color} (hd : d ≠ 0)
    (horth : ∀ γ, γ ≠ 0 → γ ≠ d → colorDot z γ = 0) :
    z = 0 := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero d hd with rfl | rfl | rfl
  · rcases z with ⟨x, y⟩
    have hy : y = 0 := by
      simpa [colorDot, blue] using horth blue blue_ne_zero (by decide)
    have hxy : x + y = 0 := by
      simpa [colorDot, purple] using horth purple purple_ne_zero (by decide)
    have hx : x = 0 := by simpa [hy] using hxy
    simp [hx, hy]
  · rcases z with ⟨x, y⟩
    have hx : x = 0 := by
      simpa [colorDot, red] using horth red red_ne_zero (by decide)
    have hxy : x + y = 0 := by
      simpa [colorDot, purple] using horth purple purple_ne_zero (by decide)
    have hy : y = 0 := by simpa [hx] using hxy
    simp [hx, hy]
  · rcases z with ⟨x, y⟩
    have hx : x = 0 := by
      simpa [colorDot, red] using horth red red_ne_zero (by decide)
    have hy : y = 0 := by
      simpa [colorDot, blue] using horth blue blue_ne_zero (by decide)
    simp [hx, hy]

/-- Dot product of two color chains restricted to a finite edge set. -/
def chainDot {E : Type*} [DecidableEq E] (S : Finset E) (x y : E → Color) : F2 :=
  Finset.sum S fun e => colorDot (x e) (y e)

/-- If a chain is nonzero on an edge in `S`, then some test chain pairs with it to `1` on `S`. -/
theorem exists_chainDot_one_of_mem_ne_zero {E : Type*} [DecidableEq E]
    {S : Finset E} {x : E → Color} {e : E} (he : e ∈ S) (hx : x e ≠ 0) :
    ∃ z : E → Color, chainDot S x z = 1 := by
  obtain ⟨w, hw⟩ := exists_colorDot_one_of_ne_zero (x e) hx
  refine ⟨Pi.single e w, ?_⟩
  unfold chainDot
  rw [Finset.sum_eq_single e]
  · simpa using hw
  · intro e' _he' hne
    simp [Pi.single_eq_of_ne hne]
  · intro hnot
    exact False.elim (hnot he)

theorem chainDot_comm {E : Type*} [DecidableEq E] (S : Finset E) (x y : E → Color) :
    chainDot S x y = chainDot S y x := by
  unfold chainDot
  apply Finset.sum_congr rfl
  intro e _he
  exact colorDot_comm (x e) (y e)

@[simp] theorem chainDot_zero_left {E : Type*} [DecidableEq E] (S : Finset E)
    (y : E → Color) :
    chainDot S (zeroChain : E → Color) y = 0 := by
  simp [chainDot, zeroChain]

@[simp] theorem chainDot_zero_right {E : Type*} [DecidableEq E] (S : Finset E)
    (x : E → Color) :
    chainDot S x (zeroChain : E → Color) = 0 := by
  simp [chainDot, zeroChain]

theorem chainDot_add_left {E : Type*} [DecidableEq E] (S : Finset E)
    (x y z : E → Color) :
    chainDot S (x + y) z = chainDot S x z + chainDot S y z := by
  unfold chainDot
  simp [colorDot_add_left, Finset.sum_add_distrib]

theorem chainDot_add_right {E : Type*} [DecidableEq E] (S : Finset E)
    (x y z : E → Color) :
    chainDot S x (y + z) = chainDot S x y + chainDot S x z := by
  unfold chainDot
  simp [colorDot_add_right, Finset.sum_add_distrib]

theorem chainDot_sum_left {E ι : Type*} [DecidableEq E] [DecidableEq ι]
    (S : Finset E) (T : Finset ι) (f : ι → E → Color) (y : E → Color) :
    chainDot S (∑ i ∈ T, f i) y = ∑ i ∈ T, chainDot S (f i) y := by
  classical
  induction T using Finset.induction with
  | empty =>
      simpa [zeroChain] using chainDot_zero_left S y
  | insert i T hi ih =>
      calc
        chainDot S (∑ j ∈ insert i T, f j) y
            = chainDot S (f i + ∑ j ∈ T, f j) y := by simp [Finset.sum_insert hi]
        _ = chainDot S (f i) y + chainDot S (∑ j ∈ T, f j) y := by
              rw [chainDot_add_left]
        _ = chainDot S (f i) y + ∑ j ∈ T, chainDot S (f j) y := by
              rw [ih]
        _ = ∑ j ∈ insert i T, chainDot S (f j) y := by simp [Finset.sum_insert hi]

theorem chainDot_sum_right {E ι : Type*} [DecidableEq E] [DecidableEq ι]
    (S : Finset E) (x : E → Color) (T : Finset ι) (f : ι → E → Color) :
    chainDot S x (∑ i ∈ T, f i) = ∑ i ∈ T, chainDot S x (f i) := by
  classical
  induction T using Finset.induction with
  | empty =>
      simpa [zeroChain] using chainDot_zero_right S x
  | insert i T hi ih =>
      calc
        chainDot S x (∑ j ∈ insert i T, f j)
            = chainDot S x (f i + ∑ j ∈ T, f j) := by simp [Finset.sum_insert hi]
        _ = chainDot S x (f i) + chainDot S x (∑ j ∈ T, f j) := by
              rw [chainDot_add_right]
        _ = chainDot S x (f i) + ∑ j ∈ T, chainDot S x (f j) := by
              rw [ih]
        _ = ∑ j ∈ insert i T, chainDot S x (f j) := by simp [Finset.sum_insert hi]

theorem chainDot_sum_left_vanish {E ι : Type*} [DecidableEq E] [DecidableEq ι]
    (S : Finset E) (T : Finset ι) (f : ι → E → Color) (y : E → Color)
    (h : ∀ i ∈ T, chainDot S (f i) y = 0) :
    chainDot S (∑ i ∈ T, f i) y = 0 := by
  rw [chainDot_sum_left]
  exact Finset.sum_eq_zero h

theorem chainDot_sum_right_vanish {E ι : Type*} [DecidableEq E] [DecidableEq ι]
    (S : Finset E) (x : E → Color) (T : Finset ι) (f : ι → E → Color)
    (h : ∀ i ∈ T, chainDot S x (f i) = 0) :
    chainDot S x (∑ i ∈ T, f i) = 0 := by
  rw [chainDot_sum_right]
  exact Finset.sum_eq_zero h

/-- If a chain vanishes on every edge of `S` except `e`, the chain-dot with an indicator chain on
`S` reduces to the single contribution at `e`. -/
theorem chainDot_indicatorChain_eq_colorDot_of_erase_zero {E : Type*} [DecidableEq E]
    (γ : Color) {S : Finset E} {x : E → Color} {e : E}
    (he : e ∈ S) (hzero : ∀ e' ∈ S.erase e, x e' = 0) :
    chainDot S x (indicatorChain γ S) = colorDot (x e) γ := by
  unfold chainDot
  have hsplit :
      Finset.sum S (fun e' => colorDot (x e') (indicatorChain γ S e')) =
        Finset.sum (S.erase e) (fun e' => colorDot (x e') (indicatorChain γ S e')) +
          colorDot (x e) (indicatorChain γ S e) := by
    simpa using
      (Finset.sum_erase_add
        (s := S)
        (a := e)
        (f := fun e' => colorDot (x e') (indicatorChain γ S e'))
        he).symm
  rw [hsplit]
  have hrest : Finset.sum (S.erase e) (fun e' => colorDot (x e') (indicatorChain γ S e')) = 0 := by
    apply Finset.sum_eq_zero
    intro e' he'
    have hx0 : x e' = 0 := hzero e' he'
    have hmemS : e' ∈ S := Finset.mem_of_mem_erase he'
    simp [hx0, indicatorChain_apply_of_mem γ hmemS]
  rw [hrest, zero_add, indicatorChain_apply_of_mem γ he]

/-- Local annihilator step for Theorem 4.9: if `z` is orthogonal to the indicator chains supported
on the two nonzero colors different from `d`, and those supports contain no other nonzero
contribution of `z`, then `z` vanishes on the distinguished edge `e`. -/
theorem edge_eq_zero_of_annihilates_other_nonzero_colors {E : Type*} [DecidableEq E]
    (support : Color → Finset E) (z : E → Color) {e : E} {d : Color}
    (hd : d ≠ 0)
    (hmem : ∀ γ, γ ≠ 0 → γ ≠ d → e ∈ support γ)
    (hzero : ∀ γ, γ ≠ 0 → γ ≠ d → ∀ e' ∈ (support γ).erase e, z e' = 0)
    (horth : ∀ γ, γ ≠ 0 → γ ≠ d →
      chainDot (support γ) z (indicatorChain γ (support γ)) = 0) :
    z e = 0 := by
  have hdot : ∀ γ, γ ≠ 0 → γ ≠ d → colorDot (z e) γ = 0 := by
    intro γ hγ0 hγd
    rw [← chainDot_indicatorChain_eq_colorDot_of_erase_zero γ
      (hmem γ hγ0 hγd) (hzero γ hγ0 hγd)]
    exact horth γ hγ0 hγd
  exact eq_zero_of_colorDot_eq_zero_for_all_nonzero_ne hd hdot

/-- Orthogonality of two chains when both are restricted to the same finite support. -/
def IsOrthogonalOn {E : Type*} [DecidableEq E] (S : Finset E) (x y : E → Color) : Prop :=
  chainDot S x y = 0

namespace IsOrthogonalOn

theorem symm {E : Type*} [DecidableEq E] {S : Finset E} {x y : E → Color}
    (h : IsOrthogonalOn S x y) :
    IsOrthogonalOn S y x := by
  unfold IsOrthogonalOn at *
  rwa [chainDot_comm]

@[simp] theorem zero_left {E : Type*} [DecidableEq E] (S : Finset E) (y : E → Color) :
    IsOrthogonalOn S (zeroChain : E → Color) y := by
  unfold IsOrthogonalOn
  exact chainDot_zero_left S y

@[simp] theorem zero_right {E : Type*} [DecidableEq E] (S : Finset E) (x : E → Color) :
    IsOrthogonalOn S x (zeroChain : E → Color) := by
  unfold IsOrthogonalOn
  exact chainDot_zero_right S x

theorem add_left {E : Type*} [DecidableEq E] {S : Finset E} {x y z : E → Color}
    (hx : IsOrthogonalOn S x z) (hy : IsOrthogonalOn S y z) :
    IsOrthogonalOn S (x + y) z := by
  unfold IsOrthogonalOn at *
  rw [chainDot_add_left, hx, hy, zero_add]

theorem add_right {E : Type*} [DecidableEq E] {S : Finset E} {x y z : E → Color}
    (hy : IsOrthogonalOn S x y) (hz : IsOrthogonalOn S x z) :
    IsOrthogonalOn S x (y + z) := by
  unfold IsOrthogonalOn at *
  rw [chainDot_add_right, hy, hz, zero_add]

end IsOrthogonalOn

/-- Chains that annihilate every chain in a set on a finite support. -/
def AnnihilatorOn {E : Type*} [DecidableEq E] (S : Finset E) (A : Set (E → Color)) :
    Set (E → Color) :=
  {y | ∀ x ∈ A, IsOrthogonalOn S x y}

/-- The finite-support double orthogonal. -/
def DoubleOrthogonalOn {E : Type*} [DecidableEq E] (S : Finset E) (A : Set (E → Color)) :
    Set (E → Color) :=
  AnnihilatorOn S (AnnihilatorOn S A)

theorem faceBoundarySpan_orthogonal_on_of_generators {E : Type*} [DecidableEq E]
    {S : Finset E} {γ : Color} {faces : Finset (Finset E)} {y : E → Color}
    (h : ∀ f ∈ faces, IsOrthogonalOn S (faceBoundaryChain γ f) y) :
    ∀ x ∈ faceBoundarySpan γ faces, IsOrthogonalOn S x y := by
  intro x hx
  rcases hx with ⟨T, hT, rfl⟩
  unfold IsOrthogonalOn
  exact chainDot_sum_left_vanish S T (fun f => faceBoundaryChain γ f) y
    (fun f hf => h f (hT hf))

/-- The color-chain generator set associated to a finite family of face
boundaries. -/
def faceBoundaryGeneratorSet {E : Type*} [DecidableEq E]
    (γ : Color) (faces : Finset (Finset E)) : Set (E → Color) :=
  {x | ∃ f ∈ faces, x = faceBoundaryChain γ f}

theorem mem_faceBoundaryGeneratorSet_iff {E : Type*} [DecidableEq E]
    (γ : Color) (faces : Finset (Finset E)) {x : E → Color} :
    x ∈ faceBoundaryGeneratorSet γ faces ↔
      ∃ f ∈ faces, x = faceBoundaryChain γ f :=
  Iff.rfl

/-- A finite face-boundary span is contained in the finite-support double
orthogonal of its face-boundary generators. -/
theorem faceBoundarySpan_subset_doubleOrthogonalOn {E : Type*} [DecidableEq E]
    (S : Finset E) {γ : Color} (faces : Finset (Finset E)) :
    faceBoundarySpan γ faces ⊆ DoubleOrthogonalOn S (faceBoundaryGeneratorSet γ faces) := by
  intro x hx y hy
  unfold AnnihilatorOn at hy
  exact IsOrthogonalOn.symm <|
    faceBoundarySpan_orthogonal_on_of_generators
      (S := S) (γ := γ) (faces := faces) (y := y)
      (fun f hf => hy (faceBoundaryChain γ f) ⟨f, hf, rfl⟩)
      x hx

/-- If a chain annihilates the face-boundary generators, then every chain in
the finite face-boundary span is orthogonal to it. -/
theorem faceBoundarySpan_orthogonal_on_of_mem_annihilator {E : Type*} [DecidableEq E]
    (S : Finset E) {γ : Color} {faces : Finset (Finset E)} {y : E → Color}
    (hy : y ∈ AnnihilatorOn S (faceBoundaryGeneratorSet γ faces)) :
    ∀ x ∈ faceBoundarySpan γ faces, IsOrthogonalOn S x y := by
  intro x hx
  exact IsOrthogonalOn.symm <|
    faceBoundarySpan_subset_doubleOrthogonalOn S faces hx y hy

namespace BoundaryChainSinglePeelData

variable {V E : Type*} [Fintype E] [DecidableEq E]

/-- The face-boundary generator set associated to a single-face peel
interface. -/
def faceBoundaryGeneratorSet
    (data : BoundaryChainSinglePeelData V E) : Set (E → Color) :=
  Mettapedia.GraphTheory.FourColor.faceBoundaryGeneratorSet data.gamma data.internalFaces

theorem mem_faceBoundaryGeneratorSet_iff
    (data : BoundaryChainSinglePeelData V E) {x : E → Color} :
    x ∈ data.faceBoundaryGeneratorSet ↔
      ∃ f ∈ data.internalFaces, x = faceBoundaryChain data.gamma f :=
  Iff.rfl

theorem zeroBoundarySet_orthogonal_on_of_faceBoundary_generators
    (data : BoundaryChainSinglePeelData V E) {S : Finset E} {y : E → Color}
    (h : ∀ f ∈ data.internalFaces,
      IsOrthogonalOn S (faceBoundaryChain data.gamma f) y) :
    ∀ x ∈ data.zero.zeroBoundarySet, IsOrthogonalOn S x y := by
  intro x hx
  exact faceBoundarySpan_orthogonal_on_of_generators h x
    (data.zeroBoundarySet_subset_faceBoundarySpan hx)

theorem zeroBoundarySet_subset_doubleOrthogonalOn
    (data : BoundaryChainSinglePeelData V E) (S : Finset E) :
    data.zero.zeroBoundarySet ⊆ DoubleOrthogonalOn S data.faceBoundaryGeneratorSet :=
  data.zeroBoundarySet_subset_faceBoundarySpan.trans <| by
    simpa [faceBoundaryGeneratorSet] using
      faceBoundarySpan_subset_doubleOrthogonalOn S data.internalFaces

theorem zeroBoundarySet_orthogonal_on_of_mem_annihilator
    (data : BoundaryChainSinglePeelData V E) {S : Finset E} {y : E → Color}
    (hy : y ∈ AnnihilatorOn S data.faceBoundaryGeneratorSet) :
    ∀ x ∈ data.zero.zeroBoundarySet, IsOrthogonalOn S x y := by
  intro x hx
  exact IsOrthogonalOn.symm <|
    data.zeroBoundarySet_subset_doubleOrthogonalOn S hx y hy

end BoundaryChainSinglePeelData

namespace BoundaryChainAggregatePeelData

variable {V E : Type*} [Fintype E] [DecidableEq E]

/-- The face-boundary generator set associated to an aggregate-face peel
interface. -/
def faceBoundaryGeneratorSet
    (data : BoundaryChainAggregatePeelData V E) : Set (E → Color) :=
  Mettapedia.GraphTheory.FourColor.faceBoundaryGeneratorSet data.gamma data.internalFaces

theorem mem_faceBoundaryGeneratorSet_iff
    (data : BoundaryChainAggregatePeelData V E) {x : E → Color} :
    x ∈ data.faceBoundaryGeneratorSet ↔
      ∃ f ∈ data.internalFaces, x = faceBoundaryChain data.gamma f :=
  Iff.rfl

theorem zeroBoundarySet_orthogonal_on_of_faceBoundary_generators
    (data : BoundaryChainAggregatePeelData V E) {S : Finset E} {y : E → Color}
    (h : ∀ f ∈ data.internalFaces,
      IsOrthogonalOn S (faceBoundaryChain data.gamma f) y) :
    ∀ x ∈ data.zero.zeroBoundarySet, IsOrthogonalOn S x y := by
  intro x hx
  exact faceBoundarySpan_orthogonal_on_of_generators h x
    (data.zeroBoundarySet_subset_faceBoundarySpan hx)

theorem zeroBoundarySet_subset_doubleOrthogonalOn
    (data : BoundaryChainAggregatePeelData V E) (S : Finset E) :
    data.zero.zeroBoundarySet ⊆ DoubleOrthogonalOn S data.faceBoundaryGeneratorSet :=
  data.zeroBoundarySet_subset_faceBoundarySpan.trans <| by
    simpa [faceBoundaryGeneratorSet] using
      faceBoundarySpan_subset_doubleOrthogonalOn S data.internalFaces

theorem zeroBoundarySet_orthogonal_on_of_mem_annihilator
    (data : BoundaryChainAggregatePeelData V E) {S : Finset E} {y : E → Color}
    (hy : y ∈ AnnihilatorOn S data.faceBoundaryGeneratorSet) :
    ∀ x ∈ data.zero.zeroBoundarySet, IsOrthogonalOn S x y := by
  intro x hx
  exact IsOrthogonalOn.symm <|
    data.zeroBoundarySet_subset_doubleOrthogonalOn S hx y hy

end BoundaryChainAggregatePeelData

namespace BoundaryChainSinglePeelData

variable {V E : Type*} [Fintype E] [DecidableEq E]

@[simp]
theorem toBoundaryChainAggregatePeelData_faceBoundaryGeneratorSet
    (data : BoundaryChainSinglePeelData V E) :
    data.toBoundaryChainAggregatePeelData.faceBoundaryGeneratorSet =
      data.faceBoundaryGeneratorSet :=
  rfl

end BoundaryChainSinglePeelData

end Mettapedia.GraphTheory.FourColor
