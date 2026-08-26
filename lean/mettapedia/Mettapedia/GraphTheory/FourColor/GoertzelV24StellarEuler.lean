import Mettapedia.GraphTheory.FourColor.GoertzelV24StellarSubdivision
import Mettapedia.GraphTheory.FourColor.GoertzelV24PermutationOrbitSurgery

/-!
# The counts of the stellar subdivision

The subdivision replaces the dart set by three copies of itself, so every
count below is read off a single fact: an orbit count times the common orbit
size is the size of the carrier.

* The edge flip of a map has all orbits of size two, so `|D| = 2E`.  The same
  applies to the subdivided flip, and `|D'| = 3|D|`, giving `E' = 3E`.
* The face permutation of the subdivision has all orbits of size three, so
  `|D'| = 3F'`, giving `F' = |D| = 2E`.

The fibre lemma that carries all of this is `card_eq_mul_orbitCount`: if every
class of a permutation's cycle relation has exactly `k` elements, the carrier
has `k` times as many elements as there are classes.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24StellarEuler

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24StellarSubdivision

variable {D : Type*} [Fintype D] [DecidableEq D]

/-! ## Counting a carrier by constant orbit size -/

/-- If every cycle class of `π` is a supplied finite set of `k` elements, the
carrier has `k` times as many elements as `π` has orbits.  The class is passed
in rather than filtered out, so no decidability of the cycle relation is
needed. -/
theorem card_eq_mul_orbitCount {π : Perm D} {k : ℕ} (fibre : D → Finset D)
    (hmem : ∀ d x : D, x ∈ fibre d ↔ π.SameCycle x d)
    (hcard : ∀ d : D, (fibre d).card = k) :
    Fintype.card D = k * orbitCount π := by
  classical
  have hpart : (Finset.univ : Finset D).card
      = ∑ q : Quotient (Equiv.Perm.SameCycle.setoid π),
          (Finset.univ.filter
            (fun x : D => (Quotient.mk _ x : Quotient _) = q)).card :=
    Finset.card_eq_sum_card_fiberwise (fun x _ => Finset.mem_univ _)
  have hconst : ∀ q : Quotient (Equiv.Perm.SameCycle.setoid π),
      (Finset.univ.filter
        (fun x : D => (Quotient.mk _ x : Quotient _) = q)).card = k := by
    intro q
    have hiff : ∀ x : D,
        ((Quotient.mk _ x : Quotient (Equiv.Perm.SameCycle.setoid π)) = q) ↔
          x ∈ fibre q.out := by
      intro x
      rw [hmem q.out x]
      conv_lhs => rw [← Quotient.out_eq q]
      exact Quotient.eq
    have hset :
        (Finset.univ.filter
            (fun x : D => (Quotient.mk _ x : Quotient _) = q)) = fibre q.out := by
      ext x
      simp [hiff x]
    rw [hset]
    exact hcard q.out
  rw [Finset.card_univ] at hpart
  rw [hpart]
  simp only [hconst, Finset.sum_const, smul_eq_mul, Finset.card_univ]
  rw [orbitCount, Nat.mul_comm]

/-! ## The flip has orbits of size two -/

/-- For an involution the cycle class of a dart is the two-element set formed
by the dart and its image. -/
theorem sameCycle_involutive_iff {α : Perm D} (hinv : ∀ d, α (α d) = d)
    (d x : D) : α.SameCycle x d ↔ x = d ∨ x = α d := by
  have hmulOne : α * α = 1 := by ext z; simpa using hinv z
  have hinvEq : α⁻¹ = α := by
    rw [← mul_one α⁻¹, ← hmulOne, ← mul_assoc, inv_mul_cancel, one_mul]
  have hclosed : ∀ y : D, (y = d ∨ y = α d) → (α y = d ∨ α y = α d) := by
    rintro y (rfl | rfl)
    · exact Or.inr rfl
    · exact Or.inl (hinv d)
  have hmem : ∀ p : ℤ, ((α ^ p) d = d ∨ (α ^ p) d = α d) := by
    intro p
    induction p using Int.induction_on with
    | zero => exact Or.inl (by simp)
    | succ step ih =>
        have hrw : ((step : ℤ) + 1) = 1 + (step : ℤ) := by ring
        rw [hrw, zpow_add, zpow_one, Equiv.Perm.mul_apply]
        exact hclosed _ ih
    | pred step ih =>
        have hrw : (-(step : ℤ) - 1) = -1 + -(step : ℤ) := by ring
        rw [hrw, zpow_add, zpow_neg_one, hinvEq, Equiv.Perm.mul_apply]
        exact hclosed _ ih
  constructor
  · intro hsame
    obtain ⟨power, hpow⟩ := hsame.symm
    rcases hmem power with hcase | hcase
    · exact Or.inl (hpow.symm.trans hcase)
    · exact Or.inr (hpow.symm.trans hcase)
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simpa using hinv d⟩

/-- **`|D| = 2E`.**  The dart count is twice the edge count: the classes of a
fixed-point-free involution are the two-element edges. -/
theorem card_eq_two_mul_orbitCount_flip {α : Perm D} (hinv : ∀ d, α (α d) = d)
    (hfree : ∀ d, α d ≠ d) :
    Fintype.card D = 2 * orbitCount α := by
  classical
  refine card_eq_mul_orbitCount (fun d => ({d, α d} : Finset D)) ?_ ?_
  · intro d x
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact (sameCycle_involutive_iff hinv d x).symm
  · intro d
    exact Finset.card_pair (fun h => hfree d h.symm)

/-! ## The subdivision's counts -/

section Stellar

variable {σ α : Perm D}

/-- The old dart indexing the face of the subdivision that a given new dart
lies on. -/
def faceIndex (σ α : Perm D) : StellarDart D → D
  | Sum.inl d => d
  | Sum.inr (Sum.inl d) => d
  | Sum.inr (Sum.inr d) => (σ * α) d

/-- Every dart of the subdivision lies on the face through the old dart that
indexes it. -/
theorem sameCycle_old_faceIndex (hinv : ∀ d, α (α d) = d)
    (x : StellarDart D) :
    (stellarFace σ α).SameCycle (old (faceIndex σ α x)) x := by
  rcases x with d | d | d
  · exact Equiv.Perm.SameCycle.refl _ _
  · exact (stellarFace_sameCycle_old_iff hinv d _).2
      (apex_mem_stellarFaceSet σ α d)
  · refine (stellarFace_sameCycle_old_iff hinv ((σ * α) d) _).2 ?_
    have hcancel : (σ * α)⁻¹ ((σ * α) d) = d := by simp
    simp [stellarFaceSet, hcancel]

/-- The face of the subdivision through an old dart, as a finite set. -/
def stellarFaceFinset (σ α : Perm D) (d : D) : Finset (StellarDart D) :=
  {old d, apex d, rim ((σ * α)⁻¹ d)}

theorem mem_stellarFaceFinset (σ α : Perm D) (d : D) (x : StellarDart D) :
    x ∈ stellarFaceFinset σ α d ↔ x ∈ stellarFaceSet σ α d := by
  simp [stellarFaceFinset, stellarFaceSet]

theorem card_stellarFaceFinset (σ α : Perm D) (d : D) :
    (stellarFaceFinset σ α d).card = 3 := by
  classical
  rw [stellarFaceFinset,
    Finset.card_insert_of_notMem (by simp [old, apex, rim]),
    Finset.card_insert_of_notMem (by simp [apex, rim]),
    Finset.card_singleton]

/-- **`F' = |D|`.**  Every face of the subdivision has exactly three darts, so
the face count is the old dart count. -/
theorem orbitCount_stellarFace (hinv : ∀ d, α (α d) = d) :
    orbitCount (stellarFace σ α) = Fintype.card D := by
  classical
  have hcount : Fintype.card (StellarDart D) = 3 * orbitCount (stellarFace σ α) := by
    refine card_eq_mul_orbitCount
      (fun x => stellarFaceFinset σ α (faceIndex σ α x)) ?_ ?_
    · intro x y
      rw [mem_stellarFaceFinset]
      rw [← stellarFace_sameCycle_old_iff hinv]
      constructor
      · intro hy
        exact hy.symm.trans (sameCycle_old_faceIndex hinv x)
      · intro hy
        exact (sameCycle_old_faceIndex hinv x).trans hy.symm
    · intro x
      exact card_stellarFaceFinset σ α _
  have hcard : Fintype.card (StellarDart D) = 3 * Fintype.card D := by
    simp [StellarDart, Fintype.card_sum]
    ring
  omega

/-- **`|D'| = 3|D|`.** -/
theorem card_stellarDart : Fintype.card (StellarDart D) = 3 * Fintype.card D := by
  simp [StellarDart, Fintype.card_sum]
  ring

/-- **`E' = 3E`.**  The subdivided flip is again a fixed-point-free
involution, so its orbits have two darts, and there are three times as many
darts. -/
theorem orbitCount_stellarFlip (hinv : ∀ d, α (α d) = d) (hfree : ∀ d, α d ≠ d) :
    orbitCount (stellarFlip α) = 3 * orbitCount α := by
  classical
  have hnew : Fintype.card (StellarDart D) = 2 * orbitCount (stellarFlip α) :=
    card_eq_two_mul_orbitCount_flip (stellarFlip_involutive hinv)
      (stellarFlip_ne hfree)
  have hold : Fintype.card D = 2 * orbitCount α :=
    card_eq_two_mul_orbitCount_flip hinv hfree
  have hcard : Fintype.card (StellarDart D) = 3 * Fintype.card D :=
    card_stellarDart
  omega

/-- **`F' = 2E`.**  Combining the face count with the edge count of the
original map. -/
theorem orbitCount_stellarFace_eq_two_mul (hinv : ∀ d, α (α d) = d)
    (hfree : ∀ d, α d ≠ d) :
    orbitCount (stellarFace σ α) = 2 * orbitCount α := by
  rw [orbitCount_stellarFace hinv]
  exact card_eq_two_mul_orbitCount_flip hinv hfree

end Stellar

/-! ## The vertex count

The subdivided rotation splits the new darts into two invariant parts.  On the
old and apex darts its square is the original rotation, so those classes are
the vertices of the original map; on the rim darts it is the inverse face
permutation, so those classes are the faces.  Hence `V' = V + F`. -/

/-- One forward step of an integer power. -/
theorem zpow_succ_apply {β : Type*} (π : Perm β) (m : ℤ) (x : β) :
    (π ^ (m + 1)) x = π ((π ^ m) x) := by
  rw [show m + 1 = 1 + m by ring, zpow_add, zpow_one, Equiv.Perm.mul_apply]

/-- One backward step of an integer power. -/
theorem zpow_pred_apply {β : Type*} (π : Perm β) (m : ℤ) (x : β) :
    (π ^ (m - 1)) x = π⁻¹ ((π ^ m) x) := by
  rw [show m - 1 = -1 + m by ring, zpow_add, zpow_neg_one, Equiv.Perm.mul_apply]

section Vertices

variable {σ α : Perm D}

/-- Two steps of the subdivided rotation carry an old dart to its image under
the original rotation: the apex dart is spliced in between. -/
theorem stellarRotation_sq_old (hinv : ∀ d, α (α d) = d) (x : D) :
    stellarRotation σ α (stellarRotation σ α (old x)) = old (σ x) := by
  simp [hinv]

theorem stellarRotation_pow_old (hinv : ∀ d, α (α d) = d) (d : D) :
    ∀ n : ℕ, ((stellarRotation σ α) ^ (2 * n)) (old d) = old ((σ ^ n) d) := by
  intro n
  induction n with
  | zero => simp
  | succ step ih =>
      have hrw : 2 * (step + 1) = 2 + 2 * step := by ring
      rw [hrw, pow_add, Equiv.Perm.mul_apply, ih]
      have hsq : ((stellarRotation σ α) ^ 2) (old ((σ ^ step) d))
          = old (σ ((σ ^ step) d)) := by
        simpa [pow_succ, Equiv.Perm.mul_apply] using
          stellarRotation_sq_old (σ := σ) hinv ((σ ^ step) d)
      rw [hsq, pow_succ', Equiv.Perm.mul_apply]

theorem stellarRotation_pow_rim (d : D) :
    ∀ n : ℕ, ((stellarRotation σ α) ^ n) (rim d)
      = rim ((((σ * α)⁻¹) ^ n) d) := by
  intro n
  induction n with
  | zero => simp
  | succ step ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, stellarRotation_rim,
        pow_succ', Equiv.Perm.mul_apply]

/-- The set of darts on the vertex of the subdivision carrying an old dart. -/
def stellarVertexSet (σ α : Perm D) (d : D) : Set (StellarDart D) :=
  {x | ∃ n : ℤ, x = old ((σ ^ n) d) ∨ x = apex (α ((σ ^ n) d))}

theorem old_mem_stellarVertexSet (σ α : Perm D) (d : D) :
    old d ∈ stellarVertexSet σ α d := ⟨0, Or.inl (by simp)⟩

theorem stellarVertexSet_apply (hinv : ∀ d, α (α d) = d) (d : D)
    {x : StellarDart D} (hx : x ∈ stellarVertexSet σ α d) :
    stellarRotation σ α x ∈ stellarVertexSet σ α d := by
  obtain ⟨n, hn | hn⟩ := hx <;> subst hn
  · exact ⟨n, Or.inr rfl⟩
  · refine ⟨n + 1, Or.inl ?_⟩
    rw [stellarRotation_apex, hinv, zpow_succ_apply]

theorem stellarVertexSet_inv_apply (hinv : ∀ d, α (α d) = d) (d : D)
    {x : StellarDart D} (hx : x ∈ stellarVertexSet σ α d) :
    (stellarRotation σ α)⁻¹ x ∈ stellarVertexSet σ α d := by
  have hinvEq : α⁻¹ = α := by
    have hmulOne : α * α = 1 := by ext z; simpa using hinv z
    rw [← mul_one α⁻¹, ← hmulOne, ← mul_assoc, inv_mul_cancel, one_mul]
  obtain ⟨n, hn | hn⟩ := hx <;> subst hn
  · refine ⟨n - 1, Or.inr ?_⟩
    have hval : (stellarRotation σ α)⁻¹ (old ((σ ^ n) d))
        = apex ((σ * α)⁻¹ ((σ ^ n) d)) := rfl
    rw [hval, zpow_pred_apply]
    congr 1
    rw [mul_inv_rev, Equiv.Perm.mul_apply, hinvEq]
  · refine ⟨n, Or.inl ?_⟩
    have hval : (stellarRotation σ α)⁻¹ (apex (α ((σ ^ n) d)))
        = old (α.symm (α ((σ ^ n) d))) := rfl
    rw [hval]
    congr 1
    simp

theorem stellarVertexSet_zpow (hinv : ∀ d, α (α d) = d) (d : D) (power : ℤ)
    {x : StellarDart D} (hx : x ∈ stellarVertexSet σ α d) :
    ((stellarRotation σ α) ^ power) x ∈ stellarVertexSet σ α d := by
  induction power using Int.induction_on with
  | zero => simpa using hx
  | succ step ih =>
      rw [zpow_succ_apply]
      exact stellarVertexSet_apply hinv d ih
  | pred step ih =>
      rw [zpow_pred_apply]
      exact stellarVertexSet_inv_apply hinv d ih

/-- **Old darts share a vertex of the subdivision exactly when they shared one
before.** -/
theorem stellarRotation_sameCycle_old_iff (hinv : ∀ d, α (α d) = d) (d e : D) :
    (stellarRotation σ α).SameCycle (old d) (old e) ↔ σ.SameCycle d e := by
  constructor
  · rintro ⟨power, hpow⟩
    have hmem := stellarVertexSet_zpow hinv d power (old_mem_stellarVertexSet σ α d)
    rw [hpow] at hmem
    obtain ⟨n, hn | hn⟩ := hmem
    · exact ⟨n, (Sum.inl_injective hn).symm⟩
    · exact absurd hn (by simp [old, apex])
  · intro hsame
    obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq hsame
    refine ⟨(2 * n : ℕ), ?_⟩
    rw [zpow_natCast, stellarRotation_pow_old hinv, hn]

/-- Old and rim darts never share a vertex of the subdivision. -/
theorem not_stellarRotation_sameCycle_old_rim (hinv : ∀ d, α (α d) = d)
    (d e : D) : ¬ (stellarRotation σ α).SameCycle (old d) (rim e) := by
  rintro ⟨power, hpow⟩
  have hmem := stellarVertexSet_zpow hinv d power (old_mem_stellarVertexSet σ α d)
  rw [hpow] at hmem
  obtain ⟨n, hn | hn⟩ := hmem
  · exact absurd hn (by simp [old, rim])
  · exact absurd hn (by simp [apex, rim])

/-- An apex dart shares its vertex with the old dart that splices it in. -/
theorem stellarRotation_sameCycle_old_apex (hinv : ∀ d, α (α d) = d) (y : D) :
    (stellarRotation σ α).SameCycle (old (α y)) (apex y) :=
  ⟨1, by simpa using congrArg apex (hinv y)⟩

/-- The set of darts on the vertex created inside an old face. -/
def stellarRimSet (σ α : Perm D) (d : D) : Set (StellarDart D) :=
  {x | ∃ n : ℤ, x = rim (((σ * α) ^ n) d)}

theorem rim_mem_stellarRimSet (σ α : Perm D) (d : D) :
    rim d ∈ stellarRimSet σ α d := ⟨0, by simp⟩

theorem stellarRimSet_apply (d : D) {x : StellarDart D}
    (hx : x ∈ stellarRimSet σ α d) :
    stellarRotation σ α x ∈ stellarRimSet σ α d := by
  obtain ⟨n, hn⟩ := hx
  subst hn
  exact ⟨n - 1, by rw [stellarRotation_rim, zpow_pred_apply]⟩

theorem stellarRimSet_inv_apply (d : D) {x : StellarDart D}
    (hx : x ∈ stellarRimSet σ α d) :
    (stellarRotation σ α)⁻¹ x ∈ stellarRimSet σ α d := by
  obtain ⟨n, hn⟩ := hx
  subst hn
  refine ⟨n + 1, ?_⟩
  have hval : (stellarRotation σ α)⁻¹ (rim (((σ * α) ^ n) d))
      = rim ((σ * α) (((σ * α) ^ n) d)) := rfl
  rw [hval, zpow_succ_apply]

theorem stellarRimSet_zpow (d : D) (power : ℤ) {x : StellarDart D}
    (hx : x ∈ stellarRimSet σ α d) :
    ((stellarRotation σ α) ^ power) x ∈ stellarRimSet σ α d := by
  induction power using Int.induction_on with
  | zero => simpa using hx
  | succ step ih =>
      rw [zpow_succ_apply]
      exact stellarRimSet_apply d ih
  | pred step ih =>
      rw [zpow_pred_apply]
      exact stellarRimSet_inv_apply d ih

/-- **Rim darts share a vertex exactly when their indices share a face.** -/
theorem stellarRotation_sameCycle_rim_iff (d e : D) :
    (stellarRotation σ α).SameCycle (rim d) (rim e) ↔ (σ * α).SameCycle d e := by
  constructor
  · rintro ⟨power, hpow⟩
    have hmem := stellarRimSet_zpow d power (rim_mem_stellarRimSet σ α d)
    rw [hpow] at hmem
    obtain ⟨n, hn⟩ := hmem
    exact ⟨n, (Sum.inr_injective (Sum.inr_injective hn)).symm⟩
  · intro hsame
    obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq hsame.symm
    refine ⟨(n : ℕ), ?_⟩
    rw [zpow_natCast, stellarRotation_pow_rim]
    congr 1
    rw [inv_pow, ← hn]
    simp

/-- The classification of the subdivision's vertices: a vertex of the original
map gives the vertex carrying its old darts, and a face of the original map
gives the vertex created inside it. -/
noncomputable def stellarVertexMap (hinv : ∀ d, α (α d) = d) :
    Quotient (Equiv.Perm.SameCycle.setoid σ) ⊕
      Quotient (Equiv.Perm.SameCycle.setoid (σ * α)) →
      Quotient (Equiv.Perm.SameCycle.setoid (stellarRotation σ α)) :=
  Sum.elim
    (Quotient.map old
      (fun d e h => (stellarRotation_sameCycle_old_iff hinv d e).2 h))
    (Quotient.map rim (fun d e h => (stellarRotation_sameCycle_rim_iff d e).2 h))

theorem stellarVertexMap_bijective (hinv : ∀ d, α (α d) = d) :
    Function.Bijective (stellarVertexMap (σ := σ) (α := α) hinv) := by
  constructor
  · rintro (a | a) (b | b) heq
    · obtain ⟨da, rfl⟩ := Quotient.exists_rep a
      obtain ⟨db, rfl⟩ := Quotient.exists_rep b
      exact congrArg Sum.inl (Quotient.sound
        ((stellarRotation_sameCycle_old_iff hinv da db).1 (Quotient.exact heq)))
    · obtain ⟨da, rfl⟩ := Quotient.exists_rep a
      obtain ⟨db, rfl⟩ := Quotient.exists_rep b
      exact absurd (Quotient.exact heq)
        (not_stellarRotation_sameCycle_old_rim hinv da db)
    · obtain ⟨da, rfl⟩ := Quotient.exists_rep a
      obtain ⟨db, rfl⟩ := Quotient.exists_rep b
      exact absurd (Quotient.exact heq).symm
        (not_stellarRotation_sameCycle_old_rim hinv db da)
    · obtain ⟨da, rfl⟩ := Quotient.exists_rep a
      obtain ⟨db, rfl⟩ := Quotient.exists_rep b
      exact congrArg Sum.inr (Quotient.sound
        ((stellarRotation_sameCycle_rim_iff da db).1 (Quotient.exact heq)))
  · intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    rcases x with d | y | d
    · exact ⟨Sum.inl (Quotient.mk _ d), rfl⟩
    · exact ⟨Sum.inl (Quotient.mk _ (α y)),
        Quotient.sound (stellarRotation_sameCycle_old_apex hinv y)⟩
    · exact ⟨Sum.inr (Quotient.mk _ d), rfl⟩

/-- **`V' = V + F`.**  The vertices of the subdivision are the vertices of the
original map together with one new vertex per old face. -/
theorem orbitCount_stellarRotation (hinv : ∀ d, α (α d) = d) :
    orbitCount (stellarRotation σ α) = orbitCount σ + orbitCount (σ * α) := by
  classical
  have hcard := Fintype.card_congr
    (Equiv.ofBijective _ (stellarVertexMap_bijective (σ := σ) (α := α) hinv))
  rw [Fintype.card_sum] at hcard
  exact hcard.symm

/-- **The subdivision has the same Euler characteristic.**  Stated additively
to stay inside the naturals: `V' + F' + E = V + F + E'`.  With `V' = V + F`,
`F' = 2E` and `E' = 3E` both sides are `V + F + 3E`. -/
theorem stellar_euler (hinv : ∀ d, α (α d) = d) (hfree : ∀ d, α d ≠ d) :
    orbitCount (stellarRotation σ α) + orbitCount (stellarFace σ α)
        + orbitCount α =
      orbitCount σ + orbitCount (σ * α) + orbitCount (stellarFlip α) := by
  have hvertex := orbitCount_stellarRotation (σ := σ) (α := α) hinv
  have hface := orbitCount_stellarFace_eq_two_mul (σ := σ) hinv hfree
  have hedge := orbitCount_stellarFlip (α := α) hinv hfree
  omega

end Vertices

end GoertzelV24StellarEuler

end Mettapedia.GraphTheory.FourColor
