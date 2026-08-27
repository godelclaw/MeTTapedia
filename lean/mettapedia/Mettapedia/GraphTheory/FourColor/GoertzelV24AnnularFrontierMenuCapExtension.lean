import Mettapedia.GraphTheory.FourColor.CAP5BoundaryWord

/-!
# The pentagonal cap extension is unique

The source's Menu-B predicate is not read off the open tangle.  It restores the
pentagonal cap and counts components of the *composed* pairing.  Before that
composition can be defined as a function of the finite boundary profile, the
restored cap colouring itself has to be a function of the boundary word.

That is what this file proves, and it holds for every CAP5 word rather than
only for the good ones.  Two facts do all the work.

First, properness at cap vertex `i` says `{w i, x (i-1), x i}` is a Tait triple,
and three distinct nonzero Klein colours sum to zero, so `x i = w i + x (i-1)`.
The internal colouring is therefore a forced walk once any single value is
fixed.

Second, suppose two extensions `x` and `y` exist and put `d = x i + y i`.  The
forced recursion makes `d` independent of `i`.  If `d` were nonzero then every
`x i` would avoid both `0` and `d`, leaving only two available colours, while
properness forces `x i ≠ x (i-1)` at each of the five vertices.  An alternation
of length five around an odd cycle is impossible, so `d = 0`.

The odd cycle is the whole reason.  On a cap of even length the argument fails
and the extension genuinely is not unique.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierMenuCapExtension

variable {w : CAP5BoundaryWord} {x y : CAP5InternalCycleColoring}

/-- Three distinct nonzero Klein colours sum to zero, so the third is the sum
of the other two. -/
theorem third_eq_add {a b c : Color} (h : IsTaitColorTriple a b c) :
    c = a + b := by
  have key : ∀ p q r : Color, p ≠ 0 → q ≠ 0 → r ≠ 0 → p ≠ q → p ≠ r → q ≠ r →
      r = p + q := by decide
  exact key a b c h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2

/-- Adding a common colour to both sides cancels, since the Klein group has
characteristic two. -/
private theorem add_common (p a b : Color) : (p + a) + (p + b) = a + b := by
  revert p a b; decide

/-- If two colours sum to `d` and the second is nonzero, the first is not `d`. -/
private theorem ne_of_add_eq {a b d : Color} (h : a + b = d) (hb : b ≠ 0) :
    a ≠ d := by
  revert h hb; revert a b d; decide

/-- **The cap colouring is a forced walk.**  Each internal edge colour is the
sum of the boundary colour at its vertex and the previous internal edge. -/
theorem step (h : CAP5ExtendsAcrossCycleWith w x) :
    x 0 = w 0 + x 4 ∧ x 1 = w 1 + x 0 ∧ x 2 = w 2 + x 1 ∧
      x 3 = w 3 + x 2 ∧ x 4 = w 4 + x 3 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  exact ⟨third_eq_add h0, third_eq_add h1, third_eq_add h2, third_eq_add h3,
    third_eq_add h4⟩

/-- Consecutive internal cap edges differ, since they meet at a proper cap
vertex. -/
theorem ne_prev (h : CAP5ExtendsAcrossCycleWith w x) :
    x 4 ≠ x 0 ∧ x 0 ≠ x 1 ∧ x 1 ≠ x 2 ∧ x 2 ≠ x 3 ∧ x 3 ≠ x 4 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  exact ⟨h0.2.2.2.2.2, h1.2.2.2.2.2, h2.2.2.2.2.2, h3.2.2.2.2.2, h4.2.2.2.2.2⟩

/-- Every internal cap edge carries a genuine Tait colour. -/
theorem ne_zero (h : CAP5ExtendsAcrossCycleWith w x) :
    x 0 ≠ 0 ∧ x 1 ≠ 0 ∧ x 2 ≠ 0 ∧ x 3 ≠ 0 ∧ x 4 ≠ 0 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  exact ⟨h0.2.2.1, h1.2.2.1, h2.2.2.1, h3.2.2.1, h4.2.2.1⟩

set_option synthInstance.maxSize 2000 in
/-- Only two Klein colours avoid both `0` and a fixed nonzero `d`, so a chain of
three consecutive distinct such colours must return to where it started. -/
private theorem eq_of_avoiding {a b c d : Color} (hd : d ≠ 0)
    (ha : a ≠ 0) (had : a ≠ d) (hb : b ≠ 0) (hbd : b ≠ d)
    (hc : c ≠ 0) (hcd : c ≠ d) (hab : a ≠ b) (hbc : b ≠ c) : a = c := by
  have key : ∀ p q r e : Color, e ≠ 0 → p ≠ 0 → p ≠ e → q ≠ 0 → q ≠ e →
      r ≠ 0 → r ≠ e → p ≠ q → q ≠ r → p = r := by decide
  exact key a b c d hd ha had hb hbd hc hcd hab hbc

/-- **At most one pentagonal cap extension.**  Uniqueness needs no goodness
hypothesis: the five-cycle's odd length rules out the alternating difference. -/
theorem unique (hx : CAP5ExtendsAcrossCycleWith w x)
    (hy : CAP5ExtendsAcrossCycleWith w y) : x = y := by
  obtain ⟨sx0, sx1, sx2, sx3, sx4⟩ := step hx
  obtain ⟨sy0, sy1, sy2, sy3, sy4⟩ := step hy
  -- the difference is constant around the cap
  have d0 : x 0 + y 0 = x 4 + y 4 := by rw [sx0, sy0, add_common]
  have d1 : x 1 + y 1 = x 0 + y 0 := by rw [sx1, sy1, add_common]
  have d2 : x 2 + y 2 = x 1 + y 1 := by rw [sx2, sy2, add_common]
  have d3 : x 3 + y 3 = x 2 + y 2 := by rw [sx3, sy3, add_common]
  have h0 : x 0 + y 0 = x 4 + y 4 := d0
  have h1 : x 1 + y 1 = x 4 + y 4 := by rw [d1, d0]
  have h2 : x 2 + y 2 = x 4 + y 4 := by rw [d2, d1, d0]
  have h3 : x 3 + y 3 = x 4 + y 4 := by rw [d3, d2, d1, d0]
  have h4 : x 4 + y 4 = x 4 + y 4 := rfl
  -- if the difference were nonzero, every cap colour would avoid `0` and `d`
  have hzero : x 4 + y 4 = 0 := by
    by_contra hdne
    obtain ⟨z0, z1, z2, z3, z4⟩ := ne_zero hx
    obtain ⟨n40, n01, n12, n23, n34⟩ := ne_prev hx
    obtain ⟨u0, u1, u2, u3, u4⟩ := ne_zero hy
    have a0 : x 0 ≠ x 4 + y 4 := ne_of_add_eq h0 u0
    have a1 : x 1 ≠ x 4 + y 4 := ne_of_add_eq h1 u1
    have a2 : x 2 ≠ x 4 + y 4 := ne_of_add_eq h2 u2
    have a3 : x 3 ≠ x 4 + y 4 := ne_of_add_eq h3 u3
    have a4 : x 4 ≠ x 4 + y 4 := ne_of_add_eq h4 u4
    -- three consecutive values collapse, so the alternation closes up
    have e0 : x 4 = x 1 := eq_of_avoiding hdne z4 a4 z0 a0 z1 a1 n40 n01
    have e2 : x 1 = x 3 := eq_of_avoiding hdne z1 a1 z2 a2 z3 a3 n12 n23
    exact n34 (by rw [← e2, ← e0])
  have key : ∀ {a b : Color}, a + b = 0 → a = b := fun {a b} h =>
    (add_eq_zero_iff_eq a b).mp h
  funext i
  fin_cases i
  · exact key (h0.trans hzero)
  · exact key (h1.trans hzero)
  · exact key (h2.trans hzero)
  · exact key (h3.trans hzero)
  · exact key hzero

end GoertzelV24AnnularFrontierMenuCapExtension

end Mettapedia.GraphTheory.FourColor
