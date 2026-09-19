import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkProjection

/-!
# A fork needs only its child and parent interfaces

The projected fork law in `GoertzelV24ForkProjection` completes a child state
to a function on *all* ambient vertices before checking compatibility. That
description is semantically exact, but it hides the finite local shape of a
transition. At a fork of disjoint edge shores, two realized child profiles can
clash only at a vertex belonging to both child middle sets. Moreover a vertex
on the parent middle set receives a contribution from a child only when it is
on that child's middle set. Both facts follow from the definition of a middle
set, without planarity or cubicity.

The theorem below replaces the all-vertex test and output formula by these
local interface operations. Cubicity is used only to identify the completed
states with realized full profiles, as in the preceding projection theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24ForkLocality

open GoertzelV24ForkInterfaceSupport GoertzelV24ForkProjection

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

private theorem mem_mid_of_two_incident_edges (inc : E → Finset V)
    (S : Finset E) {v : V} {e f : E}
    (he : e ∈ S) (hve : v ∈ inc e) (hf : f ∉ S) (hvf : v ∈ inc f) :
    v ∈ mid inc S := by
  classical
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, ?_⟩
  · exact ⟨e, Finset.mem_filter.mpr ⟨he, hve⟩⟩
  · exact ⟨f, Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hf, hvf⟩⟩

/-- If a vertex is on the parent interface but not a child's interface,
that child has no incident edge there. -/
theorem child_incidence_empty_of_parent_mid (inc : E → Finset V)
    (A B : Finset E) {v : V}
    (hparent : v ∈ mid inc (A ∪ B)) (hchild : v ∉ mid inc A) :
    (A.filter fun e => v ∈ inc e) = ∅ := by
  classical
  by_contra hne
  obtain ⟨e, he⟩ : (A.filter fun e => v ∈ inc e).Nonempty :=
    Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨f, hf⟩ := (Finset.mem_filter.mp hparent).2.2
  have hfnot : f ∉ A := by
    intro hfA
    exact (Finset.mem_compl.mp (Finset.mem_filter.mp hf).1)
      (Finset.mem_union_left _ hfA)
  exact hchild (mem_mid_of_two_incident_edges inc A
    (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
    hfnot (Finset.mem_filter.mp hf).2)

/-- Lift a boundary assignment by zero outside its own middle set. -/
def lift (inc : E → Finset V) (S : Finset E)
    (b : Boundary inc S) (v : V) : Finset (Fin 3) :=
  if h : v ∈ mid inc S then b ⟨v, h⟩ else ∅

/-- At a parent boundary vertex, completion of a child assignment is exactly
zero-extension from the child boundary. This is true even for unrealized
assignments. -/
theorem complete_eq_lift_on_parent (inc : E → Finset V)
    (A B : Finset E) (b : Boundary inc A) {v : V}
    (hparent : v ∈ mid inc (A ∪ B)) :
    complete inc A b v = lift inc A b v := by
  classical
  by_cases hchild : v ∈ mid inc A
  · simp [complete, lift, hchild]
  · have hempty := child_incidence_empty_of_parent_mid inc A B hparent hchild
    simp [complete, lift, hchild, hempty]

/-- At a vertex of the parent interface, the fork's output uses only the
two child boundary assignments. -/
theorem restrict_merge_complete_eq_local (inc : E → Finset V)
    (A B : Finset E) (bA : Boundary inc A) (bB : Boundary inc B) :
    restrict inc (A ∪ B)
      (merge (complete inc A bA) (complete inc B bB)) =
    (fun v : mid inc (A ∪ B) =>
      lift inc A bA v.1 ∪ lift inc B bB v.1) := by
  funext v
  have hA := complete_eq_lift_on_parent inc A B bA v.2
  have hB : complete inc B bB v.1 = lift inc B bB v.1 := by
    have hswap : v.1 ∈ mid inc (B ∪ A) := by simp [Finset.union_comm, v.2]
    exact complete_eq_lift_on_parent inc B A bB hswap
  simp only [restrict, merge, hA, hB]

/-- Compatibility tested only at shared child middle vertices. -/
def LocalCompatible (inc : E → Finset V) (A B : Finset E)
    (bA : Boundary inc A) (bB : Boundary inc B) : Prop :=
  ∀ (v : V) (hA : v ∈ mid inc A) (hB : v ∈ mid inc B),
    Disjoint (bA ⟨v, hA⟩) (bB ⟨v, hB⟩)

private theorem compatible_profiles_iff_local (inc : E → Finset V)
    (A B : Finset E) (hAB : Disjoint A B)
    (cA cB : E → Fin 3) :
    Compatible (profile inc A cA) (profile inc B cB) ↔
      LocalCompatible inc A B (restrict inc A (profile inc A cA))
        (restrict inc B (profile inc B cB)) := by
  constructor
  · intro h v hA hB
    exact h v
  · intro h v
    apply Finset.disjoint_left.mpr
    intro colour hcolourA hcolourB
    obtain ⟨e, he, _⟩ := Finset.mem_image.mp hcolourA
    obtain ⟨f, hf, _⟩ := Finset.mem_image.mp hcolourB
    have heA : e ∈ A := (Finset.mem_filter.mp he).1
    have hfB : f ∈ B := (Finset.mem_filter.mp hf).1
    have hfnotA : f ∉ A := Finset.disjoint_right.mp hAB hfB
    have henotB : e ∉ B := Finset.disjoint_left.mp hAB heA
    have hvA : v ∈ mid inc A :=
      mem_mid_of_two_incident_edges inc A heA (Finset.mem_filter.mp he).2
        hfnotA (Finset.mem_filter.mp hf).2
    have hvB : v ∈ mid inc B :=
      mem_mid_of_two_incident_edges inc B hfB (Finset.mem_filter.mp hf).2
        henotB (Finset.mem_filter.mp he).2
    exact (Finset.disjoint_left.mp (h v hvA hvB) hcolourA) hcolourB

/-- For realized child states, the all-vertex compatibility test is exactly
the shared-middle-vertex test. -/
theorem compatible_complete_iff_local (inc : E → Finset V)
    (hcubic : ∀ v : V, (Finset.univ.filter fun e => v ∈ inc e).card = 3)
    (A B : Finset E) (hAB : Disjoint A B)
    {bA : Boundary inc A} {bB : Boundary inc B}
    (hbA : bA ∈ boundarySupport inc A)
    (hbB : bB ∈ boundarySupport inc B) :
    Compatible (complete inc A bA) (complete inc B bB) ↔
      LocalCompatible inc A B bA bB := by
  obtain ⟨cA, hcA, rfl⟩ := (mem_boundarySupport inc A).mp hbA
  obtain ⟨cB, hcB, rfl⟩ := (mem_boundarySupport inc B).mp hbB
  rw [complete_restrict_profile inc hcubic A hcA,
    complete_restrict_profile inc hcubic B hcB]
  exact compatible_profiles_iff_local inc A B hAB cA cB

private instance localCompatibleDecidable (inc : E → Finset V)
    (A B : Finset E) :
    DecidablePred (fun pq : Boundary inc A × Boundary inc B =>
      LocalCompatible inc A B pq.1 pq.2) := by
  intro pq
  unfold LocalCompatible
  infer_instance

/-- The fork transfer written only in terms of the child and parent
interfaces: clash at common middle vertices, then union zero-extended child
assignments at each parent middle vertex. -/
def localForkTransition (inc : E → Finset V) (A B : Finset E)
    (left : Finset (Boundary inc A)) (right : Finset (Boundary inc B)) :
    Finset (Boundary inc (A ∪ B)) :=
  ((left ×ˢ right).filter fun pq => LocalCompatible inc A B pq.1 pq.2).image
    (fun pq v => lift inc A pq.1 v.1 ∪ lift inc B pq.2 v.1)

/-- The interface-local operation is semantically exact on realized child
states. The global completion in the earlier transition is eliminable. -/
theorem localForkTransition_exact (inc : E → Finset V)
    (hcubic : ∀ v : V, (Finset.univ.filter fun e => v ∈ inc e).card = 3)
    (A B : Finset E) (hAB : Disjoint A B) :
    boundarySupport inc (A ∪ B) =
      localForkTransition inc A B (boundarySupport inc A)
        (boundarySupport inc B) := by
  rw [forkTransition_exact inc hcubic A B hAB]
  ext b
  simp only [forkTransition, localForkTransition, Finset.mem_image,
    Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨⟨bA, bB⟩, ⟨⟨hbA, hbB⟩, hcompat⟩, rfl⟩
    refine ⟨(bA, bB), ⟨⟨hbA, hbB⟩,
      (compatible_complete_iff_local inc hcubic A B hAB hbA hbB).mp hcompat⟩, ?_⟩
    exact (restrict_merge_complete_eq_local inc A B bA bB).symm
  · rintro ⟨⟨bA, bB⟩, ⟨⟨hbA, hbB⟩, hlocal⟩, rfl⟩
    refine ⟨(bA, bB), ⟨⟨hbA, hbB⟩,
      (compatible_complete_iff_local inc hcubic A B hAB hbA hbB).mpr hlocal⟩, ?_⟩
    exact restrict_merge_complete_eq_local inc A B bA bB

end Mettapedia.GraphTheory.FourColor.GoertzelV24ForkLocality
