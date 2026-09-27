import Mettapedia.GraphTheory.FourColor.GoertzelV24SerialOpenTangleCountSupport

/-!
# The zigzag tube ring as a two-sided open tangle

A `(k,0)` zigzag ring has vertices `d i` and `e i`, interior edges
`a i = d i — e i` and `b i = e i — d (i+1)`, an in-port at every `d i` and an
out-port at every `e i`.  It is a `TwoSidedOpenTangleData` with left boundary
`Fin k` (in-ports) and right boundary `Fin k` (out-ports).

The closed form of its support: a Tait colouring with in-word `x` is
determined by the colour `a i` of the `a`-edges, subject to `a i ∉ {0, x i}`;
the `b`-edge colour is then forced, `b i = x (i+1) + a (i+1)`, the colouring is
proper iff `a i ≠ b i`, and the out-word is `y i = a i + b i`
(`accepts_iff`).  Colours are the Klein group `F2 × F2`, so "third colour"
is addition.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace ZigzagRing

open GoertzelV24OpenTangleComposition

variable (k : Nat) [NeZero k]

/-- vertices: `Sum.inl i = d i`, `Sum.inr i = e i` -/
abbrev Vtx := Fin k ⊕ Fin k

/-- interior darts: `Sum.inl (i, false)` is `a i` at `d i`, `Sum.inl (i, true)` is `a i`
at `e i`, `Sum.inr (i, false)` is `b i` at `e i`, `Sum.inr (i, true)` is `b i` at `d (i+1)` -/
abbrev Dart := (Fin k × Bool) ⊕ (Fin k × Bool)

def interiorVert : Dart k → Vtx k
  | Sum.inl (i, false) => Sum.inl i
  | Sum.inl (i, true) => Sum.inr i
  | Sum.inr (i, false) => Sum.inr i
  | Sum.inr (i, true) => Sum.inl (i + 1)

/-- flip the end of an interior dart -/
def flip : Dart k → Dart k
  | Sum.inl (i, b) => Sum.inl (i, !b)
  | Sum.inr (i, b) => Sum.inr (i, !b)

omit [NeZero k] in
theorem flip_flip (d : Dart k) : flip k (flip k d) = d := by
  rcases d with ⟨i, b⟩ | ⟨i, b⟩ <;> simp [flip]

def interiorAlpha : Equiv.Perm (Dart k) where
  toFun := flip k
  invFun := flip k
  left_inv := flip_flip k
  right_inv := flip_flip k

/-- all darts -/
abbrev AllDart := Dart k ⊕ (Fin k ⊕ Fin k)

/-- the rotation: at `d i` the cycle `in i ↦ a i ↦ b (i-1) ↦ in i`,
at `e i` the cycle `a i ↦ b i ↦ out i ↦ a i` -/
def rhoFun : AllDart k → AllDart k
  | Sum.inr (Sum.inl i) => Sum.inl (Sum.inl (i, false))
  | Sum.inl (Sum.inl (i, false)) => Sum.inl (Sum.inr (i - 1, true))
  | Sum.inl (Sum.inr (i, true)) => Sum.inr (Sum.inl (i + 1))
  | Sum.inl (Sum.inl (i, true)) => Sum.inl (Sum.inr (i, false))
  | Sum.inl (Sum.inr (i, false)) => Sum.inr (Sum.inr i)
  | Sum.inr (Sum.inr i) => Sum.inl (Sum.inl (i, true))

def rhoInv : AllDart k → AllDart k
  | Sum.inl (Sum.inl (i, false)) => Sum.inr (Sum.inl i)
  | Sum.inl (Sum.inr (i, true)) => Sum.inl (Sum.inl (i + 1, false))
  | Sum.inr (Sum.inl i) => Sum.inl (Sum.inr (i - 1, true))
  | Sum.inl (Sum.inr (i, false)) => Sum.inl (Sum.inl (i, true))
  | Sum.inr (Sum.inr i) => Sum.inl (Sum.inr (i, false))
  | Sum.inl (Sum.inl (i, true)) => Sum.inr (Sum.inr i)

theorem rhoInv_rhoFun (d : AllDart k) : rhoInv k (rhoFun k d) = d := by
  rcases d with (⟨i, _ | _⟩ | ⟨i, _ | _⟩) | (i | i) <;>
    simp [rhoFun, rhoInv, sub_add_cancel, add_sub_cancel_right]

theorem rhoFun_rhoInv (d : AllDart k) : rhoFun k (rhoInv k d) = d := by
  rcases d with (⟨i, _ | _⟩ | ⟨i, _ | _⟩) | (i | i) <;>
    simp [rhoFun, rhoInv, sub_add_cancel, add_sub_cancel_right]

def rho : Equiv.Perm (AllDart k) where
  toFun := rhoFun k
  invFun := rhoInv k
  left_inv := rhoInv_rhoFun k
  right_inv := rhoFun_rhoInv k

/-- the ring tangle -/
def ring : TwoSidedOpenTangleData (Vtx k) (Dart k) (Fin k) (Fin k) where
  interiorVert := interiorVert k
  leftVert := Sum.inl
  rightVert := Sum.inr
  interiorAlpha := interiorAlpha k
  interiorAlpha_involutive := flip_flip k
  interiorAlpha_fixfree := by
    rintro (⟨i, _ | _⟩ | ⟨i, _ | _⟩) <;> simp [interiorAlpha, flip]
  rho := rho k
  vert_rho := by
    rintro ((⟨i, _ | _⟩ | ⟨i, _ | _⟩) | (i | i)) <;>
      simp [rho, rhoFun, twoSidedOpenTangleVertOf, interiorVert, sub_add_cancel]
  interior_no_self_loops := by
    rintro (⟨i, _ | _⟩ | ⟨i, _ | _⟩) <;> simp [interiorAlpha, flip, interiorVert]
  outer := Sum.inr (Sum.inl 0)

/-! ## The closed form of the ring's support -/

/-- three pairwise distinct nonzero colours: the third is the sum of the other two -/
theorem third_eq_add {p q r : Color} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : r = p + q := by
  revert p q r; decide

/-- the forced colour of `b i` -/
def bColor (x a : Fin k → Color) (i : Fin k) : Color := x (i + 1) + a (i + 1)

/-- the out-word -/
def outWord (x a : Fin k → Color) (i : Fin k) : Color := a i + bColor k x a i

/-- the closed-form validity of a choice `a` for in-word `x` -/
structure Valid (x a : Fin k → Color) : Prop where
  x_ne_zero : ∀ i, x i ≠ 0
  a_ne_zero : ∀ i, a i ≠ 0
  a_ne_x : ∀ i, a i ≠ x i
  a_ne_b : ∀ i, a i ≠ bColor k x a i

theorem Valid.b_ne_zero {x a : Fin k → Color} (h : Valid k x a) (i : Fin k) :
    bColor k x a i ≠ 0 :=
  add_ne_zero_of_ne (h.a_ne_x (i + 1)).symm

theorem Valid.out_ne_zero {x a : Fin k → Color} (h : Valid k x a) (i : Fin k) :
    outWord k x a i ≠ 0 :=
  add_ne_zero_of_ne (h.a_ne_b i)

/-- the colouring determined by `x` and `a` -/
def coloringOf (x a : Fin k → Color) : AllDart k → Color
  | Sum.inl (Sum.inl (i, _)) => a i
  | Sum.inl (Sum.inr (i, _)) => bColor k x a i
  | Sum.inr (Sum.inl i) => x i
  | Sum.inr (Sum.inr i) => outWord k x a i

theorem vertOf_apply (d : AllDart k) :
    (ring k).vertOf d = twoSidedOpenTangleVertOf (interiorVert k) Sum.inl Sum.inr d := rfl

theorem coloringOf_isTait (x a : Fin k → Color) (hV : Valid k x a) :
    (ring k).IsTaitColoring (coloringOf k x a) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro (⟨i, _ | _⟩ | ⟨i, _ | _⟩) <;> simp [ring, interiorAlpha, flip, coloringOf]
  · rintro ((⟨i, _ | _⟩ | ⟨i, _ | _⟩) | (i | i)) ((⟨j, _ | _⟩ | ⟨j, _ | _⟩) | (j | j)) hv hne <;>
      simp only [vertOf_apply, twoSidedOpenTangleVertOf, interiorVert, Sum.inl.injEq,
        Sum.inr.injEq, reduceCtorEq] at hv <;>
      simp only [coloringOf, ne_eq, Prod.mk.injEq, and_true, not_false_eq_true,
        Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at hne ⊢ <;>
      (first | subst hv | (have hij := add_right_cancel hv; subst hij)) <;>
      first
      | exact absurd rfl hne
      | exact (hV.a_ne_x _)
      | exact (hV.a_ne_x _).symm
      | exact (hV.a_ne_b _)
      | exact (hV.a_ne_b _).symm
      | (simp only [bColor, outWord] at hne ⊢;
         first
         | exact absurd rfl hne
         | exact (hV.a_ne_x _)
         | exact (hV.a_ne_x _).symm
         | exact (hV.a_ne_b _)
         | exact (hV.a_ne_b _).symm
         | exact (add_ne_left_of_ne_zero (hV.a_ne_zero _)).symm
         | exact (add_ne_left_of_ne_zero (hV.a_ne_zero _))
         | exact (add_ne_right_of_ne_zero (hV.x_ne_zero _)).symm
         | exact (add_ne_right_of_ne_zero (hV.x_ne_zero _))
         | exact (add_ne_left_of_ne_zero (add_ne_zero_of_ne (hV.a_ne_x _).symm)).symm
         | exact (add_ne_left_of_ne_zero (add_ne_zero_of_ne (hV.a_ne_x _).symm))
         | exact (add_ne_right_of_ne_zero (hV.a_ne_zero _)).symm
         | exact (add_ne_right_of_ne_zero (hV.a_ne_zero _)))
  · rintro ((⟨i, _ | _⟩ | ⟨i, _ | _⟩) | (i | i)) <;> simp only [coloringOf]
    · exact hV.a_ne_zero i
    · exact hV.a_ne_zero i
    · exact Valid.b_ne_zero k hV i
    · exact Valid.b_ne_zero k hV i
    · exact hV.x_ne_zero i
    · exact Valid.out_ne_zero k hV i

/-- **Closed form of the ring support.** -/
theorem accepts_iff (x y : Fin k → Color) :
    (ring k).AcceptsBoundaryWords x y ↔ ∃ a, Valid k x a ∧ y = outWord k x a := by
  constructor
  · rintro ⟨col, ⟨halpha, hvert, hnz⟩, hl, hr⟩
    have hx : ∀ i, col (Sum.inr (Sum.inl i)) = x i := fun i => congrFun hl i
    have hy : ∀ i, col (Sum.inr (Sum.inr i)) = y i := fun i => congrFun hr i
    have ha1 : ∀ i, col (Sum.inl (Sum.inl (i, true))) = col (Sum.inl (Sum.inl (i, false))) :=
      fun i => by simpa [ring, interiorAlpha, flip] using halpha (Sum.inl (i, false))
    have hb1 : ∀ i, col (Sum.inl (Sum.inr (i, true))) = col (Sum.inl (Sum.inr (i, false))) :=
      fun i => by simpa [ring, interiorAlpha, flip] using halpha (Sum.inr (i, false))
    -- vertex d i carries in i, a i, b (i-1)
    have hd : ∀ i, col (Sum.inl (Sum.inr (i - 1, false))) =
        x i + col (Sum.inl (Sum.inl (i, false))) := fun i => by
      have h1 := hvert (first := Sum.inr (Sum.inl i)) (second := Sum.inl (Sum.inl (i, false)))
        (by simp [vertOf_apply, twoSidedOpenTangleVertOf, interiorVert]) (by simp)
      have h2 := hvert (first := Sum.inr (Sum.inl i)) (second := Sum.inl (Sum.inr (i - 1, true)))
        (by simp [vertOf_apply, twoSidedOpenTangleVertOf, interiorVert, sub_add_cancel]) (by simp)
      have h3 := hvert (first := Sum.inl (Sum.inl (i, false)))
        (second := Sum.inl (Sum.inr (i - 1, true)))
        (by simp [vertOf_apply, twoSidedOpenTangleVertOf, interiorVert, sub_add_cancel]) (by simp)
      rw [hb1] at h2 h3
      rw [hx] at h1 h2
      exact third_eq_add (hx i ▸ hnz _) (hnz _) (hnz _) h1 h2 h3
    -- vertex e i carries a i, b i, out i
    have he : ∀ i, y i = col (Sum.inl (Sum.inl (i, false))) + col (Sum.inl (Sum.inr (i, false))) ∧
        col (Sum.inl (Sum.inl (i, false))) ≠ col (Sum.inl (Sum.inr (i, false))) := fun i => by
      have h1 := hvert (first := Sum.inl (Sum.inl (i, true))) (second := Sum.inl (Sum.inr (i, false)))
        (by simp [vertOf_apply, twoSidedOpenTangleVertOf, interiorVert]) (by simp)
      have h2 := hvert (first := Sum.inl (Sum.inl (i, true))) (second := Sum.inr (Sum.inr i))
        (by simp [vertOf_apply, twoSidedOpenTangleVertOf, interiorVert]) (by simp)
      have h3 := hvert (first := Sum.inl (Sum.inr (i, false))) (second := Sum.inr (Sum.inr i))
        (by simp [vertOf_apply, twoSidedOpenTangleVertOf, interiorVert]) (by simp)
      rw [ha1] at h1 h2
      rw [hy] at h2 h3
      exact ⟨third_eq_add (hnz _) (hnz _) (hy i ▸ hnz _) h1 h2 h3, h1⟩
    refine ⟨fun i => col (Sum.inl (Sum.inl (i, false))), ⟨fun i => hx i ▸ hnz _,
      fun i => hnz _, ?_, ?_⟩, ?_⟩
    · intro i h
      have h1 := hvert (first := Sum.inr (Sum.inl i)) (second := Sum.inl (Sum.inl (i, false)))
        (by simp [vertOf_apply, twoSidedOpenTangleVertOf, interiorVert]) (by simp)
      exact h1 (by rw [hx, h])
    · intro i h
      have hb : bColor k x (fun i => col (Sum.inl (Sum.inl (i, false)))) i =
          col (Sum.inl (Sum.inr (i, false))) := by
        simp only [bColor]
        have := hd (i + 1)
        rw [add_sub_cancel_right] at this
        exact this.symm
      exact (he i).2 (by rw [h, hb])
    · funext i
      simp only [outWord]
      have hb : bColor k x (fun i => col (Sum.inl (Sum.inl (i, false)))) i =
          col (Sum.inl (Sum.inr (i, false))) := by
        simp only [bColor]
        have := hd (i + 1)
        rw [add_sub_cancel_right] at this
        exact this.symm
      rw [hb]
      exact (he i).1
  · rintro ⟨a, hV, rfl⟩
    refine ⟨coloringOf k x a, coloringOf_isTait k x a hV, ?_, ?_⟩
    · funext i; rfl
    · funext i; rfl

end ZigzagRing
end Mettapedia.GraphTheory.FourColor
