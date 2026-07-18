import Mettapedia.GraphTheory.FourColor.CAP5BoundaryWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutCap

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ThreeEdgeCutColor

open RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The three edges of an exact three-edge cut receive the three distinct
nonzero Tait colors. -/
theorem threeEdgeCut_isTaitColorTriple
    (RS : RotationSystem V E) (hCubic : RS.IsCubic)
    (C : RS.EdgeColoring Color) (hC : RS.IsTaitEdgeColoring C)
    (side : Finset V) {first second third : E}
    (hfirstSecond : first ≠ second)
    (hfirstThird : first ≠ third)
    (hsecondThird : second ≠ third)
    (hboundary : RS.vertexSideEdgeBoundary side =
      {first, second, third}) :
    IsTaitColorTriple (C first) (C second) (C third) := by
  have hsum :=
    RS.vertexSideEdgeBoundary_colorSum_eq_zero_of_isTaitEdgeColoring
      hCubic C hC side
  have hsumThree : C first + C second + C third = 0 := by
    rw [hboundary] at hsum
    simpa [hfirstSecond, hfirstThird, hsecondThird, add_assoc] using hsum
  refine ⟨hC first, hC second, hC third, ?_, ?_, ?_⟩
  · intro hcolors
    have hthirdZero : C third = 0 := by
      simpa [hcolors, color_add_self] using hsumThree
    exact hC third hthirdZero
  · intro hcolors
    have hsecondZero : C second = 0 := by
      have hsum' : C first + C second + C first = 0 := by
        simpa [hcolors] using hsumThree
      abel_nf at hsum'
      simpa [two_mul] using hsum'
    exact hC second hsecondZero
  · intro hcolors
    have hfirstZero : C first = 0 := by
      have hsum' : C first + C second + C second = 0 := by
        simpa [hcolors] using hsumThree
      abel_nf at hsum'
      simpa [two_mul] using hsum'
    exact hC first hfirstZero

/-- The zero-fixing color equivalence that sends the standard ordered Tait
triple `(red, blue, purple)` to a specified ordered Tait triple. -/
def taitTripleColorEquiv {first second third : Color}
    (h : IsTaitColorTriple first second third) : Color ≃ Color where
  toFun color :=
    if color = 0 then 0
    else if color = red then first
    else if color = blue then second
    else third
  invFun color :=
    if color = 0 then 0
    else if color = first then red
    else if color = second then blue
    else purple
  left_inv := by
    intro color
    rcases h with ⟨hfirst, hsecond, hthird,
      hfirstSecond, hfirstThird, hsecondThird⟩
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero first hfirst with
      rfl | rfl | rfl <;>
      rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero second hsecond with
        rfl | rfl | rfl <;>
        rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero third hthird with
          rfl | rfl | rfl <;>
          rcases color with ⟨redCoordinate, blueCoordinate⟩ <;>
          fin_cases redCoordinate <;> fin_cases blueCoordinate <;>
          simp [red, blue, purple] at hfirstSecond hfirstThird hsecondThird
    all_goals decide
  right_inv := by
    intro color
    rcases h with ⟨hfirst, hsecond, hthird,
      hfirstSecond, hfirstThird, hsecondThird⟩
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero first hfirst with
      rfl | rfl | rfl <;>
      rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero second hsecond with
        rfl | rfl | rfl <;>
        rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero third hthird with
          rfl | rfl | rfl <;>
          rcases color with ⟨redCoordinate, blueCoordinate⟩ <;>
          fin_cases redCoordinate <;> fin_cases blueCoordinate <;>
          simp [red, blue, purple] at hfirstSecond hfirstThird hsecondThird
    all_goals decide

@[simp]
theorem taitTripleColorEquiv_zero {first second third : Color}
    (h : IsTaitColorTriple first second third) :
    taitTripleColorEquiv h 0 = 0 := by
  simp [taitTripleColorEquiv]

@[simp]
theorem taitTripleColorEquiv_red {first second third : Color}
    (h : IsTaitColorTriple first second third) :
    taitTripleColorEquiv h red = first := by
  simp [taitTripleColorEquiv]

@[simp]
theorem taitTripleColorEquiv_blue {first second third : Color}
    (h : IsTaitColorTriple first second third) :
    taitTripleColorEquiv h blue = second := by
  simp [taitTripleColorEquiv, red_ne_blue.symm]

@[simp]
theorem taitTripleColorEquiv_purple {first second third : Color}
    (h : IsTaitColorTriple first second third) :
    taitTripleColorEquiv h purple = third := by
  simp [taitTripleColorEquiv, red_ne_purple.symm,
    blue_ne_purple.symm]

/-- The canonical zero-fixing equivalence aligning one ordered Tait triple
with another. -/
def alignTaitTripleColorEquiv
    {sourceFirst sourceSecond sourceThird : Color}
    {targetFirst targetSecond targetThird : Color}
    (hsource : IsTaitColorTriple
      sourceFirst sourceSecond sourceThird)
    (htarget : IsTaitColorTriple
      targetFirst targetSecond targetThird) : Color ≃ Color :=
  (taitTripleColorEquiv hsource).symm.trans
    (taitTripleColorEquiv htarget)

@[simp]
theorem alignTaitTripleColorEquiv_zero
    {sourceFirst sourceSecond sourceThird : Color}
    {targetFirst targetSecond targetThird : Color}
    (hsource : IsTaitColorTriple
      sourceFirst sourceSecond sourceThird)
    (htarget : IsTaitColorTriple
      targetFirst targetSecond targetThird) :
    alignTaitTripleColorEquiv hsource htarget 0 = 0 := by
  change taitTripleColorEquiv htarget
      ((taitTripleColorEquiv hsource).symm 0) = 0
  have hsourceInverse :
      (taitTripleColorEquiv hsource).symm 0 = 0 := by
    simpa using (taitTripleColorEquiv hsource).symm_apply_apply 0
  rw [hsourceInverse]
  exact taitTripleColorEquiv_zero htarget

@[simp]
theorem alignTaitTripleColorEquiv_first
    {sourceFirst sourceSecond sourceThird : Color}
    {targetFirst targetSecond targetThird : Color}
    (hsource : IsTaitColorTriple
      sourceFirst sourceSecond sourceThird)
    (htarget : IsTaitColorTriple
      targetFirst targetSecond targetThird) :
    alignTaitTripleColorEquiv hsource htarget sourceFirst = targetFirst := by
  change taitTripleColorEquiv htarget
      ((taitTripleColorEquiv hsource).symm sourceFirst) = targetFirst
  have hsourceInverse :
      (taitTripleColorEquiv hsource).symm sourceFirst = red := by
    simpa using (taitTripleColorEquiv hsource).symm_apply_apply red
  rw [hsourceInverse]
  exact taitTripleColorEquiv_red htarget

@[simp]
theorem alignTaitTripleColorEquiv_second
    {sourceFirst sourceSecond sourceThird : Color}
    {targetFirst targetSecond targetThird : Color}
    (hsource : IsTaitColorTriple
      sourceFirst sourceSecond sourceThird)
    (htarget : IsTaitColorTriple
      targetFirst targetSecond targetThird) :
    alignTaitTripleColorEquiv hsource htarget sourceSecond = targetSecond := by
  change taitTripleColorEquiv htarget
      ((taitTripleColorEquiv hsource).symm sourceSecond) = targetSecond
  have hsourceInverse :
      (taitTripleColorEquiv hsource).symm sourceSecond = blue := by
    simpa using (taitTripleColorEquiv hsource).symm_apply_apply blue
  rw [hsourceInverse]
  exact taitTripleColorEquiv_blue htarget

@[simp]
theorem alignTaitTripleColorEquiv_third
    {sourceFirst sourceSecond sourceThird : Color}
    {targetFirst targetSecond targetThird : Color}
    (hsource : IsTaitColorTriple
      sourceFirst sourceSecond sourceThird)
    (htarget : IsTaitColorTriple
      targetFirst targetSecond targetThird) :
    alignTaitTripleColorEquiv hsource htarget sourceThird = targetThird := by
  change taitTripleColorEquiv htarget
      ((taitTripleColorEquiv hsource).symm sourceThird) = targetThird
  have hsourceInverse :
      (taitTripleColorEquiv hsource).symm sourceThird = purple := by
    simpa using (taitTripleColorEquiv hsource).symm_apply_apply purple
  rw [hsourceInverse]
  exact taitTripleColorEquiv_purple htarget

end

end GoertzelV24ThreeEdgeCutColor

end Mettapedia.GraphTheory.FourColor
