import Mettapedia.GraphTheory.FourColor.RungTwo

/-!
# The closed form of the thickness-2 rung's relation

The rung accepts boundary words `(x, y)` iff its five interior edges can be
coloured with nonzero colours so that the three colours at each of the six
vertices are pairwise distinct (`accepts_iff`).
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab
namespace RungTwo

open GoertzelV24OpenTangleComposition

/-- three pairwise distinct colours -/
def Distinct3 (a b c : Color) : Prop := a ≠ b ∧ a ≠ c ∧ b ≠ c

/-- the closed-form validity of edge colours `c` for boundary words `x`, `y` -/
structure Valid (x y : Port → Color) (c : Fin 5 → Color) : Prop where
  x_ne_zero : ∀ i, x i ≠ 0
  y_ne_zero : ∀ i, y i ≠ 0
  c_ne_zero : ∀ j, c j ≠ 0
  v0 : Distinct3 (x 0) (c 0) (y 0)
  v1 : Distinct3 (c 0) (c 1) (x 1)
  v2 : Distinct3 (c 1) (c 2) (y 1)
  v3 : Distinct3 (c 2) (c 3) (x 2)
  v4 : Distinct3 (c 3) (c 4) (y 2)
  v5 : Distinct3 (c 4) (x 3) (y 3)

/-- the colouring determined by edge colours and boundary words -/
def coloringOf (x y : Port → Color) (c : Fin 5 → Color) : D → Color
  | Sum.inl (j, _) => c j
  | Sum.inr (Sum.inl i) => x i
  | Sum.inr (Sum.inr i) => y i

theorem vertOf_eq (d : D) :
    rung.vertOf d = twoSidedOpenTangleVertOf interiorVert leftVert rightVert d := rfl

theorem coloringOf_isTait (x y : Port → Color) (c : Fin 5 → Color) (hV : Valid x y c) :
    rung.IsTaitColoring (coloringOf x y c) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨j, b⟩; cases b <;> rfl
  · intro d d' hv hne
    rw [vertOf_eq, vertOf_eq] at hv
    obtain ⟨hx, hy, hc, ⟨h01, h02, h12⟩, ⟨h10, h11, h12'⟩, ⟨h20, h21, h22⟩, ⟨h30, h31, h32⟩,
      ⟨h40, h41, h42⟩, ⟨h50, h51, h52⟩⟩ := hV
    rcases d with ⟨j, b⟩ | i | i <;> rcases d' with ⟨j', b'⟩ | i' | i' <;>
      (try fin_cases j) <;> (try fin_cases j') <;> (try fin_cases i) <;> (try fin_cases i') <;>
      (try cases b) <;> (try cases b') <;>
      first
      | exact absurd hv (by decide)
      | exact absurd rfl hne
      | (simp only [coloringOf]; first
          | exact h01 | exact h01.symm | exact h02 | exact h02.symm | exact h12 | exact h12.symm
          | exact h10 | exact h10.symm | exact h11 | exact h11.symm | exact h12' | exact h12'.symm
          | exact h20 | exact h20.symm | exact h21 | exact h21.symm | exact h22 | exact h22.symm
          | exact h30 | exact h30.symm | exact h31 | exact h31.symm | exact h32 | exact h32.symm
          | exact h40 | exact h40.symm | exact h41 | exact h41.symm | exact h42 | exact h42.symm
          | exact h50 | exact h50.symm | exact h51 | exact h51.symm | exact h52 | exact h52.symm)
  · rintro (⟨j, b⟩ | i | i)
    · exact hV.c_ne_zero j
    · exact hV.x_ne_zero i
    · exact hV.y_ne_zero i

/-- **Closed form of the rung's relation.** -/
theorem accepts_iff (x y : Port → Color) :
    rung.AcceptsBoundaryWords x y ↔ ∃ c : Fin 5 → Color, Valid x y c := by
  constructor
  · rintro ⟨col, ⟨halpha, hvert, hnz⟩, hl, hr⟩
    have hx : ∀ i, col (Sum.inr (Sum.inl i)) = x i := fun i => congrFun hl i
    have hy : ∀ i, col (Sum.inr (Sum.inr i)) = y i := fun i => congrFun hr i
    have ha : ∀ j, col (Sum.inl (j, true)) = col (Sum.inl (j, false)) := fun j =>
      halpha (j, false)
    let c : Fin 5 → Color := fun j => col (Sum.inl (j, false))
    have hv : ∀ (d d' : D), rung.vertOf d = rung.vertOf d' → d ≠ d' → col d ≠ col d' :=
      fun _ _ h1 h2 => hvert h1 h2
    refine ⟨c, ⟨fun i => hx i ▸ hnz _, fun i => hy i ▸ hnz _, fun j => hnz _,
      ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · refine ⟨?_, ?_, ?_⟩
      · have := hv (Sum.inr (Sum.inl 0)) (Sum.inl (0, false)) (by decide) (by decide)
        rwa [hx] at this
      · have := hv (Sum.inr (Sum.inl 0)) (Sum.inr (Sum.inr 0)) (by decide) (by decide)
        rwa [hx, hy] at this
      · have := hv (Sum.inl (0, false)) (Sum.inr (Sum.inr 0)) (by decide) (by decide)
        rwa [hy] at this
    · refine ⟨?_, ?_, ?_⟩
      · have := hv (Sum.inl (0, true)) (Sum.inl (1, false)) (by decide) (by decide)
        rwa [ha] at this
      · have := hv (Sum.inl (0, true)) (Sum.inr (Sum.inl 1)) (by decide) (by decide)
        rwa [ha, hx] at this
      · have := hv (Sum.inl (1, false)) (Sum.inr (Sum.inl 1)) (by decide) (by decide)
        rwa [hx] at this
    · refine ⟨?_, ?_, ?_⟩
      · have := hv (Sum.inl (1, true)) (Sum.inl (2, false)) (by decide) (by decide)
        rwa [ha] at this
      · have := hv (Sum.inl (1, true)) (Sum.inr (Sum.inr 1)) (by decide) (by decide)
        rwa [ha, hy] at this
      · have := hv (Sum.inl (2, false)) (Sum.inr (Sum.inr 1)) (by decide) (by decide)
        rwa [hy] at this
    · refine ⟨?_, ?_, ?_⟩
      · have := hv (Sum.inl (2, true)) (Sum.inl (3, false)) (by decide) (by decide)
        rwa [ha] at this
      · have := hv (Sum.inl (2, true)) (Sum.inr (Sum.inl 2)) (by decide) (by decide)
        rwa [ha, hx] at this
      · have := hv (Sum.inl (3, false)) (Sum.inr (Sum.inl 2)) (by decide) (by decide)
        rwa [hx] at this
    · refine ⟨?_, ?_, ?_⟩
      · have := hv (Sum.inl (3, true)) (Sum.inl (4, false)) (by decide) (by decide)
        rwa [ha] at this
      · have := hv (Sum.inl (3, true)) (Sum.inr (Sum.inr 2)) (by decide) (by decide)
        rwa [ha, hy] at this
      · have := hv (Sum.inl (4, false)) (Sum.inr (Sum.inr 2)) (by decide) (by decide)
        rwa [hy] at this
    · refine ⟨?_, ?_, ?_⟩
      · have := hv (Sum.inl (4, true)) (Sum.inr (Sum.inl 3)) (by decide) (by decide)
        rwa [ha, hx] at this
      · have := hv (Sum.inl (4, true)) (Sum.inr (Sum.inr 3)) (by decide) (by decide)
        rwa [ha, hy] at this
      · have := hv (Sum.inr (Sum.inl 3)) (Sum.inr (Sum.inr 3)) (by decide) (by decide)
        rwa [hx, hy] at this
  · rintro ⟨c, hV⟩
    exact ⟨coloringOf x y c, coloringOf_isTait x y c hV, funext fun _ => rfl, funext fun _ => rfl⟩

end RungTwo
end TubeSlab
end Mettapedia.GraphTheory.FourColor
