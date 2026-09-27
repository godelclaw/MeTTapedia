import Mettapedia.GraphTheory.FourColor.ZigzagRingTangle

/-!
# A cycle cap as a literal open tangle

There is one boundary spoke at each vertex of a cycle. The internal edge
coloured `a i` joins vertices `i - 1` and `i`, so the spoke at `i` has colour
`a i + a (i + 1)`. The empty input makes the cap directly composable with
two-sided annular tangles.
-/

namespace Mettapedia.GraphTheory.FourColor.CycleCap

open GoertzelV24OpenTangleComposition

variable (k : Nat) [NeZero k]

abbrev Dart := Fin k × Bool
abbrev AllDart := Dart k ⊕ (Empty ⊕ Fin k)

def interiorVert : Dart k → Fin k
  | (i, false) => i
  | (i, true) => i - 1

def flip (d : Dart k) : Dart k := (d.1, !d.2)

omit [NeZero k] in
theorem flip_flip (d : Dart k) : flip k (flip k d) = d := by
  rcases d with ⟨i, b⟩
  simp [flip]

def interiorAlpha : Equiv.Perm (Dart k) where
  toFun := flip k
  invFun := flip k
  left_inv := flip_flip k
  right_inv := flip_flip k

def rhoFun : AllDart k → AllDart k
  | Sum.inr (Sum.inl e) => nomatch e
  | Sum.inr (Sum.inr i) => Sum.inl (i, false)
  | Sum.inl (i, false) => Sum.inl (i + 1, true)
  | Sum.inl (i, true) => Sum.inr (Sum.inr (i - 1))

def rhoInv : AllDart k → AllDart k
  | Sum.inr (Sum.inl e) => nomatch e
  | Sum.inl (i, false) => Sum.inr (Sum.inr i)
  | Sum.inl (i, true) => Sum.inl (i - 1, false)
  | Sum.inr (Sum.inr i) => Sum.inl (i + 1, true)

def rho : Equiv.Perm (AllDart k) where
  toFun := rhoFun k
  invFun := rhoInv k
  left_inv := by
    rintro (⟨i, _ | _⟩ | (e | i)) <;>
      first | exact nomatch e | simp [rhoFun, rhoInv]
  right_inv := by
    rintro (⟨i, _ | _⟩ | (e | i)) <;>
      first | exact nomatch e | simp [rhoFun, rhoInv]

/-- The cycle with one outward spoke per vertex. -/
def cap (hk : 2 ≤ k) : TwoSidedOpenTangleData (Fin k) (Dart k) Empty (Fin k) where
  interiorVert := interiorVert k
  leftVert := Empty.elim
  rightVert := id
  interiorAlpha := interiorAlpha k
  interiorAlpha_involutive := flip_flip k
  interiorAlpha_fixfree := by
    rintro ⟨i, _ | _⟩ <;> simp [interiorAlpha, flip]
  rho := rho k
  vert_rho := by
    rintro (⟨i, _ | _⟩ | (e | i)) <;>
      first | exact nomatch e |
        simp [rho, rhoFun, twoSidedOpenTangleVertOf, interiorVert]
  interior_no_self_loops := by
    have hone : (1 : Fin k) ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      simp only [Fin.val_one'] at hv
      change 1 % k = 0 at hv
      rw [Nat.mod_eq_of_lt (by omega)] at hv
      omega
    rintro ⟨i, _ | _⟩ <;> simp only [interiorAlpha, Equiv.coe_fn_mk, flip, interiorVert]
    · intro h
      exact hone ((sub_eq_self.mp h.symm))
    · intro h
      exact hone (sub_eq_self.mp h)
  outer := Sum.inr (Sum.inr 0)

/-- Internal cycle edges are nonzero and adjacent edges have different colours. -/
def Valid (a : Fin k → Color) : Prop :=
  (∀ i, a i ≠ 0) ∧ ∀ i, a i ≠ a (i + 1)

def spokes (a : Fin k → Color) (i : Fin k) : Color := a i + a (i + 1)

def coloringOf (a : Fin k → Color) : AllDart k → Color
  | Sum.inl (i, _) => a i
  | Sum.inr (Sum.inl e) => nomatch e
  | Sum.inr (Sum.inr i) => spokes k a i

theorem coloringOf_isTait (hk : 2 ≤ k) {a : Fin k → Color} (ha : Valid k a) :
    (cap k hk).IsTaitColoring (coloringOf k a) := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨i, _ | _⟩ <;> rfl
  · rintro (⟨i, _ | _⟩ | (e | i)) (⟨j, _ | _⟩ | (f | j)) hv hne <;>
      first | exact nomatch e | exact nomatch f |
        simp only [TwoSidedOpenTangleData.vertOf, cap, twoSidedOpenTangleVertOf,
          interiorVert, id_eq] at hv
    all_goals simp only [coloringOf, spokes] at *
    all_goals first
      | (subst j; exact absurd rfl hne)
      | (have hij : i = j := by simpa using congrArg (fun t : Fin k => t + 1) hv
         subst j; exact absurd rfl hne)
      | (subst i; simpa using ha.2 (j - 1))
      | (subst j; simpa using (ha.2 (i - 1)).symm)
      | (subst j; exact add_ne_left_of_ne_zero (ha.1 (i + 1)))
      | (subst i; exact (add_ne_left_of_ne_zero (ha.1 (j + 1))).symm)
      | (subst j; simpa using
          (add_ne_right_of_ne_zero (b := a i) (ha.1 (i - 1))).symm)
      | (subst i; simpa using add_ne_right_of_ne_zero (b := a j) (ha.1 (j - 1)))
  · rintro (⟨i, _ | _⟩ | (e | i))
    · exact ha.1 i
    · exact ha.1 i
    · exact nomatch e
    · exact add_ne_zero_of_ne (ha.2 i)

/-- Every proper internal cycle colouring gives an actual cap colouring. -/
theorem accepts_spokes (hk : 2 ≤ k) {a : Fin k → Color} (ha : Valid k a) :
    (cap k hk).AcceptsBoundaryWords Empty.elim (spokes k a) :=
  ⟨coloringOf k a, coloringOf_isTait k hk ha, funext (fun e => nomatch e), rfl⟩

end Mettapedia.GraphTheory.FourColor.CycleCap
