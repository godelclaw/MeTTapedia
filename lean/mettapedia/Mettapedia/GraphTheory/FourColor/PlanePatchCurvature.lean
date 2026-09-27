import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCurvatureBulk
import Mathlib.Data.Finset.Card

/-!
# Boundary degree imbalance of an actual plane patch

A patch is a connected spherical rotation system with a simple outer facial
walk, degree two or three on that walk, and degree three elsewhere. Face
lengths count dart occurrences. The signed curvature of its inner faces is
`6 - n₂ + n₃`, where `n₂` and `n₃` count its boundary vertices of each degree.
In particular an alternating boundary requires inner curvature six. When
the curvature is smaller than six, the actual outer walk has two consecutive
degree-two vertices; when it is larger, it has two consecutive degree-three
vertices.

The pentagon/hexagon specialization is the familiar patch identity; see
Brinkmann and Coppens, MATCH 62 (2009), 209–220, Lemma 1. The proof here uses
the literal rotation-system incidences and Euler equation. No pentagon census
or boundary-degree balance is assumed. `FaceRegionPatch` derives these
hypotheses from complete facial contours in the original spherical map.
-/

namespace Mettapedia.GraphTheory.FourColor.PlanePatchCurvature

open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

def outerFace : OrbitFace RS := dartOrbitFace RS RS.outer

def outerDarts : Finset RS.D := orbitFaceDarts RS (outerFace RS)

def boundaryVertices : Finset V := (outerDarts RS).image RS.vertOf

def degreeTwo : Finset V := Finset.univ.filter fun v => (RS.dartsAt v).card = 2

def boundaryThree : Finset V :=
  (boundaryVertices RS).filter fun v => (RS.dartsAt v).card = 3

def innerFaces : Finset (OrbitFace RS) := Finset.univ.erase (outerFace RS)

def curvature : ℤ :=
  ∑ f ∈ innerFaces RS, (6 - ((orbitFaceDarts RS f).card : ℤ))

/-- Geometric patch hypotheses. Simplicity concerns occurrences on the
outer face, rather than merely a list of distinct boundary edge labels. -/
structure Patch : Prop where
  connected : (rotationPrimalGraph RS).Connected
  rotationCyclic : VertexRotationCyclic RS
  euler : (Fintype.card V : ℤ) - Fintype.card E + Fintype.card (OrbitFace RS) = 2
  outer_simple : Set.InjOn RS.vertOf (outerDarts RS : Set RS.D)
  boundary_degree : ∀ v ∈ boundaryVertices RS,
    (RS.dartsAt v).card = 2 ∨ (RS.dartsAt v).card = 3
  interior_degree : ∀ v ∉ boundaryVertices RS, (RS.dartsAt v).card = 3

variable {RS}

theorem outer_phi_iff (d : RS.D) : RS.phi d ∈ outerDarts RS ↔ d ∈ outerDarts RS := by
  simp only [outerDarts, mem_orbitFaceDarts_iff, dartOrbitFace_phi_eq]

theorem Patch.degreeTwo_boundary (h : Patch RS) : degreeTwo RS ⊆ boundaryVertices RS := by
  intro v hv
  by_contra hn
  have ht : (RS.dartsAt v).card = 2 := (Finset.mem_filter.mp hv).2
  have := h.interior_degree v hn
  omega

theorem Patch.degree_cases (h : Patch RS) (v : V) :
    (RS.dartsAt v).card = 2 ∨ (RS.dartsAt v).card = 3 := by
  by_cases hv : v ∈ boundaryVertices RS
  · exact h.boundary_degree v hv
  · exact Or.inr (h.interior_degree v hv)

theorem Patch.boundary_partition (h : Patch RS) :
    (boundaryVertices RS).card = (degreeTwo RS).card + (boundaryThree RS).card := by
  have hu : degreeTwo RS ∪ boundaryThree RS = boundaryVertices RS := by
    ext v
    simp only [Finset.mem_union, boundaryThree, Finset.mem_filter]
    constructor
    · rintro (hv | ⟨hv, _⟩)
      · exact h.degreeTwo_boundary hv
      · exact hv
    · intro hv
      rcases h.boundary_degree v hv with ht | ht
      · exact Or.inl (by simp [degreeTwo, ht])
      · exact Or.inr ⟨hv, ht⟩
  have hd : Disjoint (degreeTwo RS) (boundaryThree RS) := by
    apply Finset.disjoint_left.mpr
    intro v ht hh
    have h2 : (RS.dartsAt v).card = 2 := (Finset.mem_filter.mp ht).2
    have h3 : (RS.dartsAt v).card = 3 := (Finset.mem_filter.mp hh).2
    omega
  rw [← hu, Finset.card_union_of_disjoint hd]

theorem Patch.outer_length (h : Patch RS) :
    (outerDarts RS).card = (degreeTwo RS).card + (boundaryThree RS).card := by
  have hc : (boundaryVertices RS).card = (outerDarts RS).card :=
    Finset.card_image_of_injOn h.outer_simple
  rw [← hc, h.boundary_partition]

theorem sum_degrees : ∑ v : V, (RS.dartsAt v).card = Fintype.card RS.D := by
  symm
  change (Finset.univ : Finset RS.D).card = _
  rw [Finset.card_eq_sum_card_fiberwise (f := RS.vertOf) (t := Finset.univ) (by simp)]
  rfl

theorem Patch.degree_sum (h : Patch RS) :
    Fintype.card RS.D + (degreeTwo RS).card = 3 * Fintype.card V := by
  have hs : (∑ v : V, ((RS.dartsAt v).card + if v ∈ degreeTwo RS then 1 else 0)) =
      ∑ _v : V, 3 := by
    apply Finset.sum_congr rfl
    intro v _
    rcases h.degree_cases v with hv | hv <;> simp [degreeTwo, hv]
  simpa [Finset.sum_add_distrib, sum_degrees, Nat.mul_comm] using hs

/-- The signed inner-face curvature is computed from actual boundary
degrees. The formula is valid with arbitrary inner face sizes. -/
theorem Patch.curvature_eq (h : Patch RS) :
    curvature RS = 6 - (degreeTwo RS).card + (boundaryThree RS).card := by
  have hfaces := sum_card_orbitFaceDarts_eq_card_darts RS
  have hsum : (∑ f : OrbitFace RS, (6 - ((orbitFaceDarts RS f).card : ℤ))) =
      6 * Fintype.card (OrbitFace RS) - Fintype.card RS.D := by
    rw [Finset.sum_sub_distrib]
    have hf : (∑ f : OrbitFace RS, ((orbitFaceDarts RS f).card : ℤ)) =
        Fintype.card RS.D := by exact_mod_cast hfaces
    rw [hf]
    simp [mul_comm]
  have he := RS.card_darts_eq_twice_card_edges
  have hv := h.degree_sum
  have ho := h.outer_length
  have hx := Finset.sum_erase_add (Finset.univ : Finset (OrbitFace RS))
    (fun f => (6 - ((orbitFaceDarts RS f).card : ℤ))) (Finset.mem_univ (outerFace RS))
  change curvature RS + (6 - ((outerDarts RS).card : ℤ)) = _ at hx
  rw [hsum] at hx
  have he' : (Fintype.card RS.D : ℤ) = 2 * Fintype.card E := by exact_mod_cast he
  have hv' : (Fintype.card RS.D : ℤ) + (degreeTwo RS).card = 3 * Fintype.card V := by
    exact_mod_cast hv
  have ho' : ((outerDarts RS).card : ℤ) = (degreeTwo RS).card + (boundaryThree RS).card := by
    exact_mod_cast ho
  linarith [h.euler]

/-- Interior pentagons, distinguished from the outer face even when its
boundary also has length five. -/
def pentagons (RS : RotationSystem V E) : Finset (OrbitFace RS) :=
  (innerFaces RS).filter fun f => (orbitFaceDarts RS f).card = 5

theorem curvature_eq_pentagons
    (hfaces : ∀ f ∈ innerFaces RS,
      (orbitFaceDarts RS f).card = 5 ∨ (orbitFaceDarts RS f).card = 6) :
    curvature RS = (pentagons RS).card := by
  unfold curvature
  calc
    _ = ∑ f ∈ innerFaces RS, if (orbitFaceDarts RS f).card = 5 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro f hf
      rcases hfaces f hf with he | he <;> simp [he]
    _ = (pentagons RS).card := by simp [pentagons]

theorem Patch.pentagon_balance (h : Patch RS)
    (hfaces : ∀ f ∈ innerFaces RS,
      (orbitFaceDarts RS f).card = 5 ∨ (orbitFaceDarts RS f).card = 6) :
    ((degreeTwo RS).card : ℤ) - (boundaryThree RS).card = 6 - (pentagons RS).card := by
  have hc := h.curvature_eq
  rw [curvature_eq_pentagons hfaces] at hc
  linarith

/-- Boundary occurrences of one degree, retaining their actual cyclic order. -/
def degreeDarts (RS : RotationSystem V E) (n : ℕ) : Finset RS.D :=
  (outerDarts RS).filter fun d => (RS.dartsAt (RS.vertOf d)).card = n

theorem Patch.card_degreeDarts (h : Patch RS) (n : ℕ) :
    (degreeDarts RS n).card =
      ((boundaryVertices RS).filter fun v => (RS.dartsAt v).card = n).card := by
  have himage : (degreeDarts RS n).image RS.vertOf =
      (boundaryVertices RS).filter (fun v => (RS.dartsAt v).card = n) := by
    ext v
    simp only [degreeDarts, boundaryVertices, Finset.mem_image, Finset.mem_filter]
    constructor
    · rintro ⟨d, ⟨hd, hn⟩, rfl⟩
      exact ⟨⟨d, hd, rfl⟩, hn⟩
    · rintro ⟨⟨d, hd, rfl⟩, hn⟩
      exact ⟨d, ⟨hd, hn⟩, rfl⟩
  rw [← himage, Finset.card_image_of_injOn]
  exact h.outer_simple.mono (Finset.filter_subset _ _)

theorem Patch.card_degreeDarts_two (h : Patch RS) :
    (degreeDarts RS 2).card = (degreeTwo RS).card := by
  rw [h.card_degreeDarts]
  congr 1
  ext v
  simp only [Finset.mem_filter, degreeTwo, Finset.mem_univ, true_and]
  exact ⟨And.right, fun hv => ⟨h.degreeTwo_boundary (by simp [degreeTwo, hv]), hv⟩⟩

theorem Patch.card_degreeDarts_three (h : Patch RS) :
    (degreeDarts RS 3).card = (boundaryThree RS).card := h.card_degreeDarts 3

/-- If an occurrence of degree `a` is never followed by degree `a`,
the face permutation injects all such occurrences into those of degree `b`.
This argument needs only the actual two-valued boundary code. -/
theorem card_degreeDarts_le_of_no_consecutive (a b : ℕ)
    (hcases : ∀ d ∈ outerDarts RS,
      (RS.dartsAt (RS.vertOf d)).card = a ∨ (RS.dartsAt (RS.vertOf d)).card = b)
    (hn : ¬ ∃ d ∈ outerDarts RS, (RS.dartsAt (RS.vertOf d)).card = a ∧
      (RS.dartsAt (RS.vertOf (RS.phi d))).card = a) :
    (degreeDarts RS a).card ≤ (degreeDarts RS b).card := by
  apply Finset.card_le_card_of_injOn RS.phi
  · intro d hd
    obtain ⟨hd, ha⟩ := Finset.mem_filter.mp hd
    have hp := (outer_phi_iff d).mpr hd
    refine Finset.mem_filter.mpr ⟨hp, ?_⟩
    exact (hcases _ hp).resolve_left (fun hh => hn ⟨d, hd, ha, hh⟩)
  · exact fun _ _ _ _ he => RS.phi.injective he

theorem Patch.boundary_dart_degree (h : Patch RS) (d : RS.D) (hd : d ∈ outerDarts RS) :
    (RS.dartsAt (RS.vertOf d)).card = 2 ∨ (RS.dartsAt (RS.vertOf d)).card = 3 :=
  h.boundary_degree _ (Finset.mem_image.mpr ⟨d, hd, rfl⟩)

/-- Curvature below six forces an outward bend in the literal boundary
walk. The two occurrences are consecutive under the original face map. -/
theorem Patch.consecutive_two_of_curvature_lt (h : Patch RS) (hc : curvature RS < 6) :
    ∃ d ∈ outerDarts RS, (RS.dartsAt (RS.vertOf d)).card = 2 ∧
      (RS.dartsAt (RS.vertOf (RS.phi d))).card = 2 := by
  by_contra hn
  have hh := card_degreeDarts_le_of_no_consecutive 2 3 h.boundary_dart_degree hn
  rw [h.card_degreeDarts_two, h.card_degreeDarts_three] at hh
  rw [h.curvature_eq] at hc
  omega

/-- Curvature above six forces the opposite boundary bend. -/
theorem Patch.consecutive_three_of_six_lt_curvature (h : Patch RS) (hc : 6 < curvature RS) :
    ∃ d ∈ outerDarts RS, (RS.dartsAt (RS.vertOf d)).card = 3 ∧
      (RS.dartsAt (RS.vertOf (RS.phi d))).card = 3 := by
  by_contra hn
  have hh := card_degreeDarts_le_of_no_consecutive 3 2
    (fun d hd => (h.boundary_dart_degree d hd).symm) hn
  rw [h.card_degreeDarts_two, h.card_degreeDarts_three] at hh
  rw [h.curvature_eq] at hc
  omega

/-- Alternation is about successive vertices in the physical outer face,
not just equal cardinalities of two arbitrarily chosen port sets. -/
def BoundaryAlternates (RS : RotationSystem V E) : Prop :=
  ∀ d ∈ outerDarts RS,
    (RS.dartsAt (RS.vertOf d)).card ≠ (RS.dartsAt (RS.vertOf (RS.phi d))).card

theorem Patch.curvature_eq_six_of_alternates (h : Patch RS) (ha : BoundaryAlternates RS) :
    curvature RS = 6 := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with hc | hc
  · obtain ⟨d, hd, h2, h2'⟩ := h.consecutive_two_of_curvature_lt hc
    exact ha d hd (h2.trans h2'.symm)
  · obtain ⟨d, hd, h3, h3'⟩ := h.consecutive_three_of_six_lt_curvature hc
    exact ha d hd (h3.trans h3'.symm)

/-- A pentagon/hexagon cap with a zigzag boundary has exactly six
pentagons. This is necessary, and does not assert a converse. -/
theorem Patch.six_pentagons_of_alternates (h : Patch RS)
    (hfaces : ∀ f ∈ innerFaces RS,
      (orbitFaceDarts RS f).card = 5 ∨ (orbitFaceDarts RS f).card = 6)
    (ha : BoundaryAlternates RS) : (pentagons RS).card = 6 := by
  have hc := h.curvature_eq_six_of_alternates ha
  rw [curvature_eq_pentagons hfaces] at hc
  exact_mod_cast hc

theorem Patch.consecutive_two_of_fewer_than_six_pentagons (h : Patch RS)
    (hfaces : ∀ f ∈ innerFaces RS,
      (orbitFaceDarts RS f).card = 5 ∨ (orbitFaceDarts RS f).card = 6)
    (hp : (pentagons RS).card < 6) :
    ∃ d ∈ outerDarts RS, (RS.dartsAt (RS.vertOf d)).card = 2 ∧
      (RS.dartsAt (RS.vertOf (RS.phi d))).card = 2 := by
  apply h.consecutive_two_of_curvature_lt
  rw [curvature_eq_pentagons hfaces]
  exact_mod_cast hp

end
end Mettapedia.GraphTheory.FourColor.PlanePatchCurvature
