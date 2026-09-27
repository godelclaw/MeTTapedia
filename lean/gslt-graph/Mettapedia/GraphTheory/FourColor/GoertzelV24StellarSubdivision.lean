import Mettapedia.GraphTheory.FourColor.GoertzelV24PermutationOrbitSurgery

/-!
# Stellar subdivision on darts

The subdivision that triangulates a map is a substitution on darts.  A map is
a triple `(D, σ, α)` with face permutation `φ = σ * α`; for each face orbit
`(d_0, …, d_{k-1})` one adjoins `2k` fresh darts `a_i` and `b_i` and sets

    α' a_i = b_i,  σ' (α d_i) = a_i,  σ' a_i = d_{i+1},  σ' b_i = b_{i-1},

leaving `σ` and `α` unchanged elsewhere.

Both families of new darts are indexed by the old darts — one `a` and one `b`
per dart of the face — so no face indexing is needed to carry the
construction: the new dart set is three copies of `D`, and the four clauses
become four total functions.  Writing the clauses that way also removes the
side condition that distinct faces name distinct darts, since the face orbits
partition `D` and the index is the dart itself.

Concretely, with `old`, `apex` and `rim` the three injections:

    α' (old d) = old (α d),   α' (apex d) = rim d,      α' (rim d) = apex d,
    σ' (old e) = apex (α e),  σ' (apex d) = old (φ d),  σ' (rim d) = rim (φ⁻¹ d).

The first `σ'` clause is the source's `σ' (α d_i) = a_i` with `e = α d_i`; it
is total precisely because `α` is a bijection.  That `σ'` is a permutation is
then immediate and needs no hypothesis on `α` at all.

The face permutation of the subdivision comes out as

    φ' (old d) = apex d,   φ' (apex d) = rim (φ⁻¹ d),   φ' (rim d) = old (φ d),

so `φ'` cubes to the identity and moves every dart, and every face orbit is
the three-element set `{old d, apex d, rim (φ⁻¹ d)}`.  Each new face therefore
contains exactly one old dart, which is what makes the two-sidedness argument
a one-liner: the two old darts of an old edge are distinct because `α` is
fixed-point-free, and the two new darts `apex d`, `rim d` of a new edge lie on
the faces indexed by `d` and by `φ d`, which are distinct exactly when `φ`
fixes no dart.

This module carries the face structure and two-sidedness.  The Euler counts
and the graph-level statements are separate.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24StellarSubdivision

open Equiv Equiv.Perm

variable {D : Type*}

/-- The dart set of the subdivision: the old darts, one apex dart per old
dart, and one rim dart per old dart. -/
abbrev StellarDart (D : Type*) := D ⊕ D ⊕ D

/-- The old dart. -/
abbrev old (d : D) : StellarDart D := Sum.inl d

/-- The apex dart `a_d` of the source's construction. -/
abbrev apex (d : D) : StellarDart D := Sum.inr (Sum.inl d)

/-- The rim dart `b_d` of the source's construction. -/
abbrev rim (d : D) : StellarDart D := Sum.inr (Sum.inr d)

/-! ## The two permutations -/

/-- The subdivided edge flip: old edges are untouched, and each apex dart is
paired with the rim dart of the same index. -/
def stellarFlip (α : Perm D) : Perm (StellarDart D) where
  toFun := fun x => match x with
    | Sum.inl d => old (α d)
    | Sum.inr (Sum.inl d) => rim d
    | Sum.inr (Sum.inr d) => apex d
  invFun := fun x => match x with
    | Sum.inl d => old (α.symm d)
    | Sum.inr (Sum.inl d) => rim d
    | Sum.inr (Sum.inr d) => apex d
  left_inv := by rintro (d | d | d) <;> simp [old, apex, rim]
  right_inv := by rintro (d | d | d) <;> simp [old, apex, rim]

/-- The subdivided vertex rotation.  The apex dart is spliced into the
rotation between `α d` and `φ d`, where the old rotation went directly; the
rim darts of one old face form a single new cycle. -/
def stellarRotation (σ α : Perm D) : Perm (StellarDart D) where
  toFun := fun x => match x with
    | Sum.inl e => apex (α e)
    | Sum.inr (Sum.inl d) => old (σ (α d))
    | Sum.inr (Sum.inr d) => rim ((σ * α)⁻¹ d)
  invFun := fun x => match x with
    | Sum.inl x => apex ((σ * α)⁻¹ x)
    | Sum.inr (Sum.inl y) => old (α.symm y)
    | Sum.inr (Sum.inr d) => rim ((σ * α) d)
  left_inv := by
    rintro (d | d | d) <;>
      simp [old, apex, rim, Equiv.Perm.mul_apply]
  right_inv := by
    rintro (d | d | d) <;>
      simp [old, apex, rim, Equiv.Perm.mul_apply]

@[simp] theorem stellarFlip_old (α : Perm D) (d : D) :
    stellarFlip α (old d) = old (α d) := rfl

@[simp] theorem stellarFlip_apex (α : Perm D) (d : D) :
    stellarFlip α (apex d) = rim d := rfl

@[simp] theorem stellarFlip_rim (α : Perm D) (d : D) :
    stellarFlip α (rim d) = apex d := rfl

@[simp] theorem stellarRotation_old (σ α : Perm D) (e : D) :
    stellarRotation σ α (old e) = apex (α e) := rfl

@[simp] theorem stellarRotation_apex (σ α : Perm D) (d : D) :
    stellarRotation σ α (apex d) = old (σ (α d)) := rfl

@[simp] theorem stellarRotation_rim (σ α : Perm D) (d : D) :
    stellarRotation σ α (rim d) = rim ((σ * α)⁻¹ d) := rfl

/-! ## The subdivided flip is again an edge flip -/

/-- The subdivided flip is an involution whenever the original is. -/
theorem stellarFlip_involutive {α : Perm D} (hinv : ∀ d, α (α d) = d) :
    ∀ x : StellarDart D, stellarFlip α (stellarFlip α x) = x := by
  rintro (d | d | d)
  · exact congrArg old (hinv d)
  · rfl
  · rfl

/-- The subdivided flip is fixed-point-free whenever the original is: the new
darts are exchanged in pairs across different summands. -/
theorem stellarFlip_ne {α : Perm D} (hfree : ∀ d, α d ≠ d) :
    ∀ x : StellarDart D, stellarFlip α x ≠ x := by
  rintro (d | d | d)
  · exact fun h => hfree d (Sum.inl_injective h)
  · exact fun h => by cases h
  · exact fun h => by cases h

/-! ## The face permutation of the subdivision -/

/-- The face permutation of the subdivision. -/
def stellarFace (σ α : Perm D) : Perm (StellarDart D) :=
  stellarRotation σ α * stellarFlip α

@[simp] theorem stellarFace_old {σ α : Perm D} (hinv : ∀ d, α (α d) = d)
    (d : D) : stellarFace σ α (old d) = apex d := by
  simp [stellarFace, Equiv.Perm.mul_apply, hinv]

@[simp] theorem stellarFace_apex (σ α : Perm D) (d : D) :
    stellarFace σ α (apex d) = rim ((σ * α)⁻¹ d) := by
  simp [stellarFace, Equiv.Perm.mul_apply]

@[simp] theorem stellarFace_rim (σ α : Perm D) (d : D) :
    stellarFace σ α (rim d) = old ((σ * α) d) := by
  simp [stellarFace, Equiv.Perm.mul_apply]

/-- **Every face of the subdivision is a three-cycle.**  The face permutation
cubes to the identity. -/
theorem stellarFace_cube {σ α : Perm D} (hinv : ∀ d, α (α d) = d) :
    ∀ x : StellarDart D,
      stellarFace σ α (stellarFace σ α (stellarFace σ α x)) = x := by
  rintro (d | d | d)
  · rw [stellarFace_old hinv, stellarFace_apex, stellarFace_rim]
    simp
  · rw [stellarFace_apex, stellarFace_rim, stellarFace_old hinv]
    simp
  · rw [stellarFace_rim, stellarFace_old hinv, stellarFace_apex]
    simp

/-- The face permutation moves every dart, so no face orbit is shorter than
three. -/
theorem stellarFace_ne {σ α : Perm D} (hinv : ∀ d, α (α d) = d) :
    ∀ x : StellarDart D, stellarFace σ α x ≠ x := by
  rintro (d | d | d)
  · rw [stellarFace_old hinv]; exact fun h => by cases h
  · rw [stellarFace_apex]; exact fun h => by cases h
  · rw [stellarFace_rim]; exact fun h => by cases h

/-! ## The face orbits, explicitly -/

/-- The face of the subdivision through an old dart: the three-element set
`{old d, apex d, rim (φ⁻¹ d)}`. -/
def stellarFaceSet (σ α : Perm D) (d : D) : Set (StellarDart D) :=
  {old d, apex d, rim ((σ * α)⁻¹ d)}

theorem old_mem_stellarFaceSet (σ α : Perm D) (d : D) :
    old d ∈ stellarFaceSet σ α d := Or.inl rfl

theorem apex_mem_stellarFaceSet (σ α : Perm D) (d : D) :
    apex d ∈ stellarFaceSet σ α d := Or.inr (Or.inl rfl)

/-- The face set is invariant under the face permutation. -/
theorem stellarFaceSet_apply {σ α : Perm D} (hinv : ∀ d, α (α d) = d)
    (d : D) {x : StellarDart D} (hx : x ∈ stellarFaceSet σ α d) :
    stellarFace σ α x ∈ stellarFaceSet σ α d := by
  rcases hx with hx | hx | hx <;> subst hx
  · rw [stellarFace_old hinv]; exact Or.inr (Or.inl rfl)
  · rw [stellarFace_apex]; exact Or.inr (Or.inr rfl)
  · rw [stellarFace_rim]
    have hself : (σ * α) ((σ * α)⁻¹ d) = d := by simp
    rw [hself]
    exact Or.inl rfl

/-- Cubing to the identity turns the inverse into the square. -/
theorem stellarFace_inv_apply {σ α : Perm D} (hinv : ∀ d, α (α d) = d)
    (x : StellarDart D) :
    (stellarFace σ α)⁻¹ x = stellarFace σ α (stellarFace σ α x) := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  exact (stellarFace_cube hinv x).symm

theorem stellarFaceSet_inv_apply {σ α : Perm D} (hinv : ∀ d, α (α d) = d)
    (d : D) {x : StellarDart D} (hx : x ∈ stellarFaceSet σ α d) :
    (stellarFace σ α)⁻¹ x ∈ stellarFaceSet σ α d := by
  rw [stellarFace_inv_apply hinv]
  exact stellarFaceSet_apply hinv d (stellarFaceSet_apply hinv d hx)

theorem stellarFaceSet_zpow_apply {σ α : Perm D} (hinv : ∀ d, α (α d) = d)
    (d : D) (power : ℤ) {x : StellarDart D}
    (hx : x ∈ stellarFaceSet σ α d) :
    ((stellarFace σ α) ^ power) x ∈ stellarFaceSet σ α d := by
  induction power using Int.induction_on with
  | zero => simpa using hx
  | succ step ih =>
      have hrw : ((step : ℤ) + 1) = 1 + (step : ℤ) := by ring
      rw [hrw, zpow_add, zpow_one, Equiv.Perm.mul_apply]
      exact stellarFaceSet_apply hinv d ih
  | pred step ih =>
      have hrw : (-(step : ℤ) - 1) = -1 + -(step : ℤ) := by ring
      rw [hrw, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]
      exact stellarFaceSet_inv_apply hinv d ih

/-- **The faces are exactly the displayed three-cycles.**  A dart lies on the
face through `old d` precisely when it is one of `old d`, `apex d`, or
`rim (φ⁻¹ d)`. -/
theorem stellarFace_sameCycle_old_iff {σ α : Perm D} (hinv : ∀ d, α (α d) = d)
    (d : D) (x : StellarDart D) :
    (stellarFace σ α).SameCycle (old d) x ↔ x ∈ stellarFaceSet σ α d := by
  constructor
  · rintro ⟨power, rfl⟩
    exact stellarFaceSet_zpow_apply hinv d power (old_mem_stellarFaceSet σ α d)
  · rintro (hx | hx | hx) <;> subst hx
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simpa using stellarFace_old hinv d⟩
    · refine ⟨2, ?_⟩
      have hsquare : ((stellarFace σ α) ^ (2 : ℤ)) (old d) =
          stellarFace σ α (stellarFace σ α (old d)) := by
        rw [show (2 : ℤ) = (2 : ℕ) by rfl, zpow_natCast]
        simp [pow_succ, Equiv.Perm.mul_apply]
      rw [hsquare, stellarFace_old hinv, stellarFace_apex]

/-! ## Two-sidedness -/

/-- A fixed point of the face permutation puts both darts of an old edge at
one vertex: the edge is a loop. -/
theorem sameCycle_of_faceFixed {σ α : Perm D} {d : D} (hfixed : (σ * α) d = d) :
    σ.SameCycle (α d) d :=
  ⟨1, by simpa [Equiv.Perm.mul_apply] using hfixed⟩

/-- Looplessness, in the source's sense that the two darts of an edge are at
different vertices, makes the face permutation fixed-point-free. -/
theorem faceFixedFree_of_loopless {σ α : Perm D}
    (hloopless : ∀ d, ¬ σ.SameCycle d (α d)) :
    ∀ d, (σ * α) d ≠ d :=
  fun d hfixed => hloopless d (sameCycle_of_faceFixed hfixed).symm

/-- **Old edges are two-sided.**  Each face of the subdivision contains
exactly one old dart, so the two old darts of an old edge lie on distinct
faces; they are distinct because the flip is fixed-point-free. -/
theorem not_sameCycle_old {σ α : Perm D} (hinv : ∀ d, α (α d) = d)
    (hfree : ∀ d, α d ≠ d) (d : D) :
    ¬ (stellarFace σ α).SameCycle (old d) (old (α d)) := by
  intro hsame
  rcases (stellarFace_sameCycle_old_iff hinv d _).1 hsame with hx | hx | hx
  · exact hfree d (Sum.inl_injective hx)
  · cases hx
  · cases hx

/-- **New edges are two-sided.**  The apex and rim darts of one index lie on
the faces through `old d` and `old (φ d)`, which are distinct exactly when the
face permutation moves `d` — that is, by the previous lemma, when the old edge
at `d` is not a loop. -/
theorem not_sameCycle_apex_rim {σ α : Perm D} (hinv : ∀ d, α (α d) = d)
    (hfaceFree : ∀ d, (σ * α) d ≠ d) (d : D) :
    ¬ (stellarFace σ α).SameCycle (apex d) (rim d) := by
  intro hsame
  have hold : (stellarFace σ α).SameCycle (old d) (apex d) :=
    (stellarFace_sameCycle_old_iff hinv d _).2 (apex_mem_stellarFaceSet σ α d)
  rcases (stellarFace_sameCycle_old_iff hinv d _).1 (hold.trans hsame) with
    hx | hx | hx
  · cases hx
  · cases hx
  · have hd : d = (σ * α)⁻¹ d := Sum.inr_injective (Sum.inr_injective hx)
    refine hfaceFree d ?_
    conv_lhs => rw [hd]
    simp

/-- **Two-sidedness of the subdivision, packaged.**  In the subdivision of a
loopless map with fixed-point-free flip, the two darts of every edge lie on
distinct faces. -/
theorem stellar_two_sided {σ α : Perm D} (hinv : ∀ d, α (α d) = d)
    (hfree : ∀ d, α d ≠ d) (hloopless : ∀ d, ¬ σ.SameCycle d (α d)) :
    ∀ x : StellarDart D,
      ¬ (stellarFace σ α).SameCycle x (stellarFlip α x) := by
  have hfaceFree := faceFixedFree_of_loopless hloopless
  rintro (d | d | d)
  · exact not_sameCycle_old hinv hfree d
  · exact not_sameCycle_apex_rim hinv hfaceFree d
  · intro hsame
    exact not_sameCycle_apex_rim hinv hfaceFree d hsame.symm

end GoertzelV24StellarSubdivision

end Mettapedia.GraphTheory.FourColor
