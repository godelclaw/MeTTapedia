import Mettapedia.GraphTheory.FourColor.CyclicColourAvoidance
import Mathlib.Data.Fin.VecNotation

/-!
# A cycle cap with a three-vertex collar and one zigzag ring

Each sector has eight actual vertices. Three concentric cycles have lengths
`m`, `3m`, and `4m`; the outer cycle exposes two ports per sector. Internal
edge identities and all cyclic vertex stars are retained explicitly.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap

open GoertzelV24OpenTangleComposition

variable (m : ℕ) [NeZero m]

abbrev Vertex := Fin m × Fin 8
abbrev Interior := Fin m × (Fin 11 × Bool)
abbrev Boundary := Fin m × Bool
abbrev Dart := Interior m ⊕ (Empty ⊕ Boundary m)
abbrev Position := Fin m × (Fin 8 × Fin 3)

def position : Dart m → Position m
  | .inl (i, (e, false)) =>
      (i, ![(0,1), (3,1), (7,1), (0,2), (1,2), (2,1),
        (2,2), (3,2), (4,2), (5,1), (6,2)] e)
  | .inl (i, (e, true)) =>
      (if e.val < 3 then i + 1 else i,
        ![(0,0), (1,0), (4,0), (1,1), (2,0), (3,0),
          (4,1), (6,1), (5,0), (6,0), (7,0)] e)
  | .inr (.inl e) => nomatch e
  | .inr (.inr (i, false)) => (i, (5, 2))
  | .inr (.inr (i, true)) => (i, (7, 2))

def star (p : Position m) : Dart m :=
  let i := p.1
  ![![.inl (i-1,(0,true)), .inl (i,(0,false)), .inl (i,(3,false))],
    ![.inl (i-1,(1,true)), .inl (i,(3,true)), .inl (i,(4,false))],
    ![.inl (i,(4,true)), .inl (i,(5,false)), .inl (i,(6,false))],
    ![.inl (i,(5,true)), .inl (i,(1,false)), .inl (i,(7,false))],
    ![.inl (i-1,(2,true)), .inl (i,(6,true)), .inl (i,(8,false))],
    ![.inl (i,(8,true)), .inl (i,(9,false)), .inr (.inr (i,false))],
    ![.inl (i,(9,true)), .inl (i,(7,true)), .inl (i,(10,false))],
    ![.inl (i,(10,true)), .inl (i,(2,false)), .inr (.inr (i,true))]] p.2.1 p.2.2

theorem position_star (p : Position m) : position m (star m p) = p := by
  rcases p with ⟨i, v, s⟩
  fin_cases v <;> fin_cases s <;> first
    | rfl
    | (change (i-1+1, _) = (i, _); rw [sub_add_cancel]; rfl)

theorem star_position (d : Dart m) : star m (position m d) = d := by
  rcases d with ⟨i,e,b⟩ | (e | ⟨i,b⟩)
  · fin_cases e <;> cases b <;> first
      | rfl
      | (change Sum.inl (i+1-1, _) = Sum.inl (i, _); rw [add_sub_cancel_right]; rfl)
  · exact nomatch e
  · cases b <;> rfl

def coordinates : Dart m ≃ Position m where
  toFun := position m
  invFun := star m
  left_inv := star_position m
  right_inv := position_star m

def vertexOf (d : Dart m) : Vertex m := ((position m d).1, (position m d).2.1)

def flip (d : Interior m) : Interior m := (d.1, (d.2.1, !d.2.2))

def alpha : Equiv.Perm (Interior m) where
  toFun := flip m
  invFun := flip m
  left_inv := by rintro ⟨i,e,b⟩; simp [flip]
  right_inv := by rintro ⟨i,e,b⟩; simp [flip]

def rotatePosition : Equiv.Perm (Position m) :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.prodCongr (Equiv.refl _) (Equiv.addRight 1))

def rotation : Equiv.Perm (Dart m) :=
  ((coordinates m).trans (rotatePosition m)).trans (coordinates m).symm

/-- The full literal cap, with `8m` vertices and `2m` ordered outer ports. -/
def tangle (hm : 2 ≤ m) :
    TwoSidedOpenTangleData (Vertex m) (Interior m) Empty (Boundary m) where
  interiorVert := fun d => vertexOf m (.inl d)
  leftVert := Empty.elim
  rightVert := fun b => vertexOf m (.inr (.inr b))
  interiorAlpha := alpha m
  interiorAlpha_involutive := by rintro ⟨i,e,b⟩; simp [alpha, flip]
  interiorAlpha_fixfree := by rintro ⟨i,e,b⟩; cases b <;> simp [alpha, flip]
  rho := rotation m
  vert_rho := by
    intro d
    have hv (d : Dart m) :
        twoSidedOpenTangleVertOf (fun d => vertexOf m (.inl d)) Empty.elim
          (fun b => vertexOf m (.inr (.inr b))) d = vertexOf m d := by
      rcases d with d | (e | b) <;> first | rfl | exact nomatch e
    simp only [hv]
    change vertexOf m ((coordinates m).symm (rotatePosition m (coordinates m d))) = _
    simp [vertexOf, coordinates, position_star, rotatePosition]
  interior_no_self_loops := by
    have hstep (i : Fin m) : i ≠ i + 1 := by
      intro h
      have he : (0 : Fin m) = 1 := add_left_cancel (a := i) (by simpa only [add_zero] using h)
      have := congrArg Fin.val he
      simp [Nat.mod_eq_of_lt (show 1 < m by omega)] at this
    rintro ⟨i,e,b⟩
    fin_cases e <;> cases b <;>
      simp [vertexOf, position, alpha, flip, hstep, (hstep i).symm]
  outer := .inr (.inr (0,false))

@[simp] theorem vertOf_star (hm : 2 ≤ m) (p : Position m) :
    (tangle m hm).vertOf (star m p) = (p.1,p.2.1) := by
  have hv (d : Dart m) : (tangle m hm).vertOf d = vertexOf m d := by
    rcases d with d | (e | b) <;> first | rfl | exact nomatch e
  simp [hv, vertexOf, position_star]

omit [NeZero m] in
theorem vertex_card : Fintype.card (Vertex m) = 8*m := by simp [Vertex]; omega

omit [NeZero m] in
theorem boundary_card : Fintype.card (Boundary m) = 2*m := by simp [Boundary]; omega

end Mettapedia.GraphTheory.FourColor.PaddedCycleCap
