import Mettapedia.GraphTheory.FourColor.GoertzelV24MapEulerBound

/-!
# Presenting an involution as an edge list

The Euler bound of `GoertzelV24MapEulerBound` is stated over a *list* of
transpositions, because its proof is an induction over that list.  A map,
however, carries its edges as a single involution `α`.  This module bridges
the two: every involution is the product of an explicit list of pairwise
disjoint transpositions, one per two-cycle.

The construction is the obvious one --- repeatedly strip a two-cycle --- and
the only delicate point is termination, handled here by an explicit fuel
argument rather than well-founded recursion, so that the defining equations
stay usable by `simp` and the arithmetic stays visible.

Stripping the two-cycle through `a` means passing from `α` to
`Equiv.swap a (α a) * α`, which fixes both `a` and `α a` and agrees with `α`
elsewhere.  That is the same surgery the bridge argument performs on a
single edge, so the two developments share their one move.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24InvolutionEdgeList

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24WordReachability
open GoertzelV24MapEulerBound

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The points actually moved by a permutation. -/
def movedFinset (α : Perm D) : Finset D :=
  Finset.univ.filter fun x => α x ≠ x

@[simp] theorem mem_movedFinset {α : Perm D} {x : D} :
    x ∈ movedFinset α ↔ α x ≠ x := by
  simp [movedFinset]

omit [Fintype D] in
/-- Stripping a two-cycle fixes both of its points. -/
theorem strip_apply_left (α : Perm D) (a : D) :
    (Equiv.swap a (α a) * α) a = a := by
  simp [Perm.mul_apply, Equiv.swap_apply_right]

omit [Fintype D] in
theorem strip_apply_right (α : Perm D) (a : D) (hinv : Function.Involutive α) :
    (Equiv.swap a (α a) * α) (α a) = α a := by
  have hback : α (α a) = a := hinv a
  rw [Perm.mul_apply, hback, Equiv.swap_apply_left]

omit [Fintype D] in
/-- Stripping a two-cycle leaves the other moved points alone. -/
theorem strip_apply_of_ne (α : Perm D) (a x : D)
    (hinv : Function.Involutive α) (hxa : x ≠ a) (hxb : x ≠ α a) :
    (Equiv.swap a (α a) * α) x = α x := by
  have h1 : α x ≠ a := by
    intro hEq
    apply hxb
    have himg : α (α x) = α a := by rw [hEq]
    rwa [hinv x] at himg
  have h2 : α x ≠ α a := fun hEq => hxa (α.injective hEq)
  rw [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne h1 h2]

/-- Stripping a two-cycle strictly shrinks the moved set. -/
theorem movedFinset_strip_ssubset (α : Perm D) {a : D} (ha : α a ≠ a)
    (hinv : Function.Involutive α) :
    movedFinset (Equiv.swap a (α a) * α) ⊂ movedFinset α := by
  have hsubset : movedFinset (Equiv.swap a (α a) * α) ⊆ movedFinset α := by
    intro x hx
    simp only [mem_movedFinset] at hx ⊢
    by_cases hxa : x = a
    · subst hxa
      exact absurd (strip_apply_left α x) hx
    by_cases hxb : x = α a
    · subst hxb
      exact absurd (strip_apply_right α a hinv) hx
    · rwa [strip_apply_of_ne α a x hinv hxa hxb] at hx
  refine (Finset.ssubset_iff_of_subset hsubset).mpr ⟨a, ?_, ?_⟩
  · exact mem_movedFinset.mpr ha
  · simp only [mem_movedFinset, not_not]
    exact strip_apply_left α a

/-- The edge list of an involution, built by stripping two-cycles.  The
first argument is fuel; `Fintype.card D` always suffices. -/
noncomputable def edgeListAux : ℕ → Perm D → List (D × D)
  | 0, _ => []
  | fuel + 1, α =>
      if h : ∃ x, α x ≠ x then
        (h.choose, α h.choose) ::
          edgeListAux fuel (Equiv.swap h.choose (α h.choose) * α)
      else []

/-- **The presentation theorem.**  With enough fuel, the constructed list
multiplies back to the involution. -/
theorem swapProduct_edgeListAux (fuel : ℕ) :
    ∀ α : Perm D, Function.Involutive α →
      (movedFinset α).card ≤ fuel →
      swapProduct (edgeListAux fuel α) = α := by
  induction fuel with
  | zero =>
      intro α hinv hcard
      have hempty : movedFinset α = ∅ := Finset.card_eq_zero.mp (by omega)
      ext x
      have : α x = x := by
        by_contra hx
        have : x ∈ movedFinset α := mem_movedFinset.mpr hx
        simp [hempty] at this
      simp [edgeListAux, this]
  | succ fuel ih =>
      intro α hinv hcard
      by_cases h : ∃ x, α x ≠ x
      · have ha : α h.choose ≠ h.choose := h.choose_spec
        have hsub := movedFinset_strip_ssubset α ha hinv
        have hcard' : (movedFinset (Equiv.swap h.choose (α h.choose) * α)).card
            ≤ fuel := by
          have := Finset.card_lt_card hsub
          omega
        have hinv' : Function.Involutive
            (Equiv.swap h.choose (α h.choose) * α) := by
          intro x
          by_cases hxa : x = h.choose
          · rw [hxa, strip_apply_left α h.choose, strip_apply_left α h.choose]
          by_cases hxb : x = α h.choose
          · rw [hxb, strip_apply_right α h.choose hinv,
              strip_apply_right α h.choose hinv]
          · rw [strip_apply_of_ne α h.choose x hinv hxa hxb]
            have h1 : α x ≠ h.choose := fun hEq => hxb (by rw [← hEq, hinv x])
            have h2 : α x ≠ α h.choose := fun hEq => hxa (α.injective hEq)
            rw [strip_apply_of_ne α h.choose (α x) hinv h1 h2, hinv x]
        have hrec := ih _ hinv' hcard'
        rw [show edgeListAux (fuel + 1) α
            = (h.choose, α h.choose) ::
                edgeListAux fuel (Equiv.swap h.choose (α h.choose) * α) by
          rw [edgeListAux, dif_pos h]]
        rw [swapProduct_cons, hrec, ← mul_assoc, Equiv.swap_mul_self, one_mul]
      · simp only [not_exists, not_not] at h
        have hid : α = 1 := by ext x; simp [h x]
        have hnone : ¬ ∃ x, α x ≠ x := fun hex => hex.choose_spec (h hex.choose)
        have hnil : edgeListAux (fuel + 1) α = [] := by
          rw [edgeListAux, dif_neg hnone]
        rw [hnil, swapProduct_nil, hid]

/-- The edge list of an involution. -/
noncomputable def edgeList (α : Perm D) : List (D × D) :=
  edgeListAux (Fintype.card D) α

theorem swapProduct_edgeList (α : Perm D) (hinv : Function.Involutive α) :
    swapProduct (edgeList α) = α :=
  swapProduct_edgeListAux _ α hinv
    (le_trans (Finset.card_le_univ _) (le_of_eq (Finset.card_univ)))

/-- **Euler's inequality for a map given by an involution.**  With the edge
flip presented as its own edge list, the bound of
`orbitCount_add_orbitCount_mul_swapProduct_le` reads in map form: vertices
plus faces is at most edges plus twice the components.

The side hypothesis says each constructed pair is a genuine two-cycle; it
holds by construction, since every pair is emitted only from a moved point.
-/
theorem orbitCount_add_orbitCount_mul_le (σ α : Perm D)
    (hinv : Function.Involutive α)
    (hne : ∀ edge ∈ edgeList α, edge.1 ≠ edge.2) :
    orbitCount σ + orbitCount (σ * α) ≤
      (edgeList α).length +
        2 * wordOrbitCount (σ :: swapGenerators (edgeList α)) := by
  have key : σ * α = σ * swapProduct (edgeList α) := by
    rw [swapProduct_edgeList α hinv]
  rw [key]
  exact orbitCount_add_orbitCount_mul_swapProduct_le σ (edgeList α) hne

/-- Every emitted pair is a genuine two-cycle: a pair is produced only from
a moved point.  No involutivity is needed for this. -/
theorem edgeListAux_fst_ne_snd (fuel : ℕ) :
    ∀ (α : Perm D), ∀ edge ∈ edgeListAux fuel α, edge.1 ≠ edge.2 := by
  induction fuel with
  | zero =>
      intro α edge hedge
      simp [edgeListAux] at hedge
  | succ fuel ih =>
      intro α edge hedge
      by_cases h : ∃ x, α x ≠ x
      · rw [edgeListAux, dif_pos h] at hedge
        rcases List.mem_cons.mp hedge with heq | htail
        · subst heq
          exact Ne.symm h.choose_spec
        · exact ih _ edge htail
      · rw [edgeListAux, dif_neg h] at hedge
        simp at hedge

theorem edgeList_fst_ne_snd (α : Perm D) :
    ∀ edge ∈ edgeList α, edge.1 ≠ edge.2 :=
  edgeListAux_fst_ne_snd _ α

/-- **Euler's inequality for a map, unconditionally.**  The side condition of
`orbitCount_add_orbitCount_mul_le` is discharged by construction. -/
theorem orbitCount_add_orbitCount_mul_le' (σ α : Perm D)
    (hinv : Function.Involutive α) :
    orbitCount σ + orbitCount (σ * α) ≤
      (edgeList α).length +
        2 * wordOrbitCount (σ :: swapGenerators (edgeList α)) :=
  orbitCount_add_orbitCount_mul_le σ α hinv (edgeList_fst_ne_snd α)

end GoertzelV24InvolutionEdgeList

end Mettapedia.GraphTheory.FourColor
