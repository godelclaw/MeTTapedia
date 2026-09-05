import Mettapedia.GraphTheory.FourColor.PresentedTangle

/-!
# The closed form of a presented tangle's relation, once for all shapes

The tangle of a valid presentation accepts boundary words `(x, y)` iff some
nonzero colouring of the interior edges makes the three slot colours at every
vertex pairwise distinct (`Pres.accepts_iff`).  This replaces the per-shape
case splits of `ZigzagRingTangle` and `RungTwoRelation`.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab
namespace Presented
namespace Pres

open GoertzelV24OpenTangleComposition

variable {V N k : Nat} [NeZero k] (P : Pres V N k)

/-- the colour at a position, given edge colours and boundary words -/
def colAt (c : Fin N → Color) (x y : Fin k → Color) (p : Pos V) : Color :=
  match P.slotAt p with
  | Slot.edge e => c e
  | Slot.inp i => x i
  | Slot.out i => y i

/-- the closed form: nonzero colours, pairwise distinct at every vertex -/
structure ValidColoring (c : Fin N → Color) (x y : Fin k → Color) : Prop where
  c_ne_zero : ∀ e, c e ≠ 0
  x_ne_zero : ∀ i, x i ≠ 0
  y_ne_zero : ∀ i, y i ≠ 0
  distinct : ∀ v : Fin V, ∀ s s' : Fin 3, s ≠ s' →
    P.colAt c x y (v, s) ≠ P.colAt c x y (v, s')

theorem toTangle_vertOf (hP : P.Valid) (d : D (N := N) (k := k)) :
    (P.toTangle hP).vertOf d = (P.pos d).1 := by
  rcases d with ⟨e, b⟩ | i | i <;> rfl

theorem colAt_endPos (hP : P.Valid) (c : Fin N → Color) (x y : Fin k → Color) (e : Fin N)
    (b : Bool) : P.colAt c x y (P.endPos e b) = c e := by
  simp [colAt, hP.1 e b]

theorem colAt_inPos (hP : P.Valid) (c : Fin N → Color) (x y : Fin k → Color) (i : Fin k) :
    P.colAt c x y (P.inPos i) = x i := by
  simp [colAt, hP.2.2.1 i]

theorem colAt_outPos (hP : P.Valid) (c : Fin N → Color) (x y : Fin k → Color) (i : Fin k) :
    P.colAt c x y (P.outPos i) = y i := by
  simp [colAt, hP.2.2.2.1 i]

theorem pos_injective (hP : P.Valid) : Function.Injective (P.pos (N := N) (k := k)) :=
  (P.posEquiv hP).injective

/-- **the closed form** -/
theorem accepts_iff (hP : P.Valid) (x y : Fin k → Color) :
    (P.toTangle hP).AcceptsBoundaryWords x y ↔ ∃ c, P.ValidColoring c x y := by
  constructor
  · rintro ⟨col, ⟨halpha, hvert, hnz⟩, hl, hr⟩
    let c : Fin N → Color := fun e => col (Sum.inl (e, false))
    have hx : ∀ i, col (Sum.inr (Sum.inl i)) = x i := fun i => congrFun hl i
    have hy : ∀ i, col (Sum.inr (Sum.inr i)) = y i := fun i => congrFun hr i
    have ha : ∀ e, col (Sum.inl (e, true)) = col (Sum.inl (e, false)) := fun e =>
      halpha (e, false)
    -- every dart's colour is the colour at its position
    have hcol : ∀ d : D (N := N) (k := k), col d = P.colAt c x y (P.pos d) := by
      rintro (⟨e, b⟩ | i | i)
      · simp only [pos, colAt_endPos P hP]
        cases b
        · rfl
        · exact ha e
      · simp only [pos, colAt_inPos P hP]; exact hx i
      · simp only [pos, colAt_outPos P hP]; exact hy i
    refine ⟨c, ⟨fun e => hnz _, fun i => hx i ▸ hnz _, fun i => hy i ▸ hnz _, ?_⟩⟩
    intro v s s' hss'
    have h1 := P.pos_dartAt hP (v, s)
    have h2 := P.pos_dartAt hP (v, s')
    have hne : P.dartAt (v, s) ≠ P.dartAt (v, s') := by
      intro h
      have := congrArg P.pos h
      rw [h1, h2] at this
      exact hss' (Prod.mk.inj this).2
    have hv : (P.toTangle hP).vertOf (P.dartAt (v, s)) = (P.toTangle hP).vertOf (P.dartAt (v, s')) := by
      rw [toTangle_vertOf, toTangle_vertOf, h1, h2]
    have := hvert hv hne
    rwa [hcol, hcol, h1, h2] at this
  · rintro ⟨c, hV⟩
    refine ⟨fun d => P.colAt c x y (P.pos d), ⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · rintro ⟨e, b⟩
      show P.colAt c x y (P.endPos e (!b)) = P.colAt c x y (P.endPos e b)
      rw [colAt_endPos P hP, colAt_endPos P hP]
    · intro d d' hv hne
      rw [toTangle_vertOf, toTangle_vertOf] at hv
      have hs : (P.pos d).2 ≠ (P.pos d').2 := by
        intro h
        apply hne
        apply P.pos_injective hP
        exact Prod.ext hv h
      have := hV.distinct (P.pos d).1 (P.pos d).2 (P.pos d').2 hs
      have e2 : P.pos d' = ((P.pos d).1, (P.pos d').2) := by rw [hv]
      show P.colAt c x y (P.pos d) ≠ P.colAt c x y (P.pos d')
      rw [e2]
      exact this
    · rintro (⟨e, b⟩ | i | i)
      · show P.colAt c x y (P.endPos e b) ≠ 0
        rw [colAt_endPos P hP]; exact hV.c_ne_zero e
      · show P.colAt c x y (P.inPos i) ≠ 0
        rw [colAt_inPos P hP]; exact hV.x_ne_zero i
      · show P.colAt c x y (P.outPos i) ≠ 0
        rw [colAt_outPos P hP]; exact hV.y_ne_zero i
    · funext i
      show P.colAt c x y (P.inPos i) = x i
      exact colAt_inPos P hP c x y i
    · funext i
      show P.colAt c x y (P.outPos i) = y i
      exact colAt_outPos P hP c x y i

end Pres
end Presented
end TubeSlab
end Mettapedia.GraphTheory.FourColor
