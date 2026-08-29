import Mathlib

/-!
# Orbit normalization for finite group actions

A property invariant under a group action, failing on a transversal of the
orbits, fails everywhere.  This is the abstract content of every argument that
reduces a problem to a list of representatives: the reduction is sound exactly
when the representatives meet every orbit and the property respects the action.

The second half builds a transversal from an arbitrary key function: order each
orbit by the key, and call a point canonical when it realises the least key in
its own orbit.  Because the orbit of `g • a` is the orbit of `a`, the canonical
points form a transversal automatically, with no enumeration.
-/

namespace OrbitNormalization

variable {G α : Type*} [Group G] [MulAction G α]

/-- `R` meets every orbit: every point can be moved into `R`. -/
def IsTransversal (R : Set α) : Prop := ∀ a : α, ∃ g : G, g • a ∈ R

/-- A property respected by the action. -/
def Invariant (P : α → Prop) : Prop := ∀ (g : G) (a : α), P (g • a) ↔ P a

/-- **Orbit normalisation.**  An invariant property that fails on a transversal
fails at every point. -/
theorem forall_not_of_transversal {R : Set α} (hR : IsTransversal (G := G) R)
    {P : α → Prop} (hP : Invariant (G := G) P) (hrep : ∀ a ∈ R, ¬ P a) :
    ∀ a, ¬ P a := by
  intro a ha
  obtain ⟨g, hg⟩ := hR a
  exact hrep _ hg ((hP g a).mpr ha)

/-- The same reduction stated positively: an invariant property holding on a
transversal holds everywhere. -/
theorem forall_of_transversal {R : Set α} (hR : IsTransversal (G := G) R)
    {P : α → Prop} (hP : Invariant (G := G) P) (hrep : ∀ a ∈ R, P a) :
    ∀ a, P a := by
  intro a
  obtain ⟨g, hg⟩ := hR a
  exact (hP g a).mp (hrep _ hg)

section Canonical

variable [Fintype G] [DecidableEq α]

/-- The orbit of `a`, as a finite set. -/
def orbitFinset (a : α) : Finset α := Finset.image (fun g : G => g • a) Finset.univ

lemma mem_orbitFinset_self (a : α) : a ∈ orbitFinset (G := G) a :=
  Finset.mem_image.mpr ⟨1, Finset.mem_univ _, one_smul _ _⟩

lemma orbitFinset_nonempty (a : α) : (orbitFinset (G := G) a).Nonempty :=
  ⟨a, mem_orbitFinset_self a⟩

/-- An orbit is determined by any of its points. -/
lemma orbitFinset_smul (g : G) (a : α) :
    orbitFinset (G := G) (g • a) = orbitFinset (G := G) a := by
  ext x
  simp only [orbitFinset, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h * g, by rw [mul_smul]⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h * g⁻¹, by rw [mul_smul, inv_smul_smul]⟩

variable (key : α → ℕ)

/-- The least key attained on the orbit of `a`. -/
def canonKey (a : α) : WithTop ℕ := ((orbitFinset (G := G) a).image key).min

lemma canonKey_smul (g : G) (a : α) :
    canonKey (G := G) key (g • a) = canonKey (G := G) key a := by
  unfold canonKey
  rw [orbitFinset_smul]

/-- A point is canonical when it realises the least key in its orbit. -/
def IsCanonical (a : α) : Prop := canonKey (G := G) key a = (key a : WithTop ℕ)

/-- The canonical points form a transversal, for any key whatsoever. -/
theorem isTransversal_isCanonical :
    IsTransversal (G := G) {a : α | IsCanonical (G := G) key a} := by
  intro a
  have hne : (((orbitFinset (G := G) a).image key)).Nonempty :=
    (orbitFinset_nonempty a).image key
  obtain ⟨n, hn⟩ := Finset.min_of_nonempty hne
  obtain ⟨b, hb, hbk⟩ := Finset.mem_image.mp (Finset.mem_of_min hn)
  obtain ⟨g, -, hg⟩ := Finset.mem_image.mp hb
  refine ⟨g, ?_⟩
  show canonKey (G := G) key (g • a) = ((key (g • a) : ℕ) : WithTop ℕ)
  rw [canonKey_smul, hg, hbk]
  exact hn

/-- **Normalisation by canonical form.**  An invariant property that fails at
every canonical point fails everywhere — no transversal need be exhibited. -/
theorem forall_not_of_canonical {P : α → Prop} (hP : Invariant (G := G) P)
    (hrep : ∀ a : α, IsCanonical (G := G) key a → ¬ P a) :
    ∀ a, ¬ P a :=
  forall_not_of_transversal (isTransversal_isCanonical key) hP hrep

end Canonical

end OrbitNormalization
