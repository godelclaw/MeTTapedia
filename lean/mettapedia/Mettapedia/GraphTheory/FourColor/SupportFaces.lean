import Mettapedia.GraphTheory.FiniteRelation
import Mettapedia.GraphTheory.FourColor.RotationDiskData

namespace Mettapedia.GraphTheory.FourColor

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

namespace RotationDiskData

/-- Internal faces that meet the current first-coordinate color support.
This ports the clean support-face selector from the old dynamic-forest attempt,
without importing its unproved peel witness. -/
def facesTouchingSupport (G : RotationDiskData V E) (x : E → Color) : Finset (Finset E) :=
  G.rotation.internalFaces.filter fun f => (f ∩ support₁ x).Nonempty

theorem mem_facesTouchingSupport_iff (G : RotationDiskData V E)
    (x : E → Color) {f : Finset E} :
    f ∈ G.facesTouchingSupport x ↔
      f ∈ G.rotation.internalFaces ∧ (f ∩ support₁ x).Nonempty := by
  simp [facesTouchingSupport]

/-- A face selected by `facesTouchingSupport` is an internal face. -/
theorem internalFace_of_mem_facesTouchingSupport (G : RotationDiskData V E)
    {x : E → Color} {f : Finset E} (hf : f ∈ G.facesTouchingSupport x) :
    f ∈ G.rotation.internalFaces :=
  (G.mem_facesTouchingSupport_iff x).1 hf |>.1

/-- A face selected by `facesTouchingSupport` really meets the current support. -/
theorem support_inter_nonempty_of_mem_facesTouchingSupport (G : RotationDiskData V E)
    {x : E → Color} {f : Finset E} (hf : f ∈ G.facesTouchingSupport x) :
    (f ∩ support₁ x).Nonempty :=
  (G.mem_facesTouchingSupport_iff x).1 hf |>.2

/-- The old dynamic-forest induced dual adjacency, now stated over a chosen
finite face set and the modern `RotationDiskData.dualAdjacent`. -/
def supportDualAdjOn (G : RotationDiskData V E) (S : Finset (Finset E))
    (f g : Finset E) : Prop :=
  f ∈ S ∧ g ∈ S ∧ G.dualAdjacent f g

/-- Degree of a face in the induced support-dual relation on `S`. -/
noncomputable def supportDualDegreeOn (G : RotationDiskData V E) (S : Finset (Finset E))
    (f : Finset E) : Nat :=
  by
    classical
    exact ((S.erase f).filter fun g => G.dualAdjacent f g).card

theorem dualAdjacent_comm (G : RotationDiskData V E) {f g : Finset E}
    (h : G.dualAdjacent f g) : G.dualAdjacent g f := by
  rcases h with ⟨hf, hg, hne, e, heInterior, hef, heg⟩
  exact ⟨hg, hf, hne.symm, e, heInterior, heg, hef⟩

theorem supportDualAdjOn_comm (G : RotationDiskData V E) {S : Finset (Finset E)}
    {f g : Finset E} (h : G.supportDualAdjOn S f g) :
    G.supportDualAdjOn S g f := by
  exact ⟨h.2.1, h.1, G.dualAdjacent_comm h.2.2⟩

theorem left_mem_of_supportDualAdjOn (G : RotationDiskData V E)
    {S : Finset (Finset E)} {f g : Finset E} (h : G.supportDualAdjOn S f g) :
    f ∈ S :=
  h.1

theorem right_mem_of_supportDualAdjOn (G : RotationDiskData V E)
    {S : Finset (Finset E)} {f g : Finset E} (h : G.supportDualAdjOn S f g) :
    g ∈ S :=
  h.2.1

theorem dualAdjacent_of_supportDualAdjOn (G : RotationDiskData V E)
    {S : Finset (Finset E)} {f g : Finset E} (h : G.supportDualAdjOn S f g) :
    G.dualAdjacent f g :=
  h.2.2

/-- The support-dual adjacency as a generic finite relation on face edge-sets.
This lets the old dynamic-forest degree/leaf vocabulary reuse the shared
finite-relation infrastructure instead of maintaining a local graph API. -/
noncomputable def supportDualRelation (G : RotationDiskData V E) :
    Mettapedia.GraphTheory.FiniteRelation (Finset E) where
  adj := G.dualAdjacent
  symm := by
    intro f g hfg
    exact G.dualAdjacent_comm hfg
  irrefl := by
    intro f hff
    exact hff.2.2.1 rfl
  decidable_adj := by
    classical
    infer_instance

@[simp]
theorem supportDualRelation_adj
    (G : RotationDiskData V E) (f g : Finset E) :
    G.supportDualRelation.adj f g = G.dualAdjacent f g :=
  rfl

theorem supportDualDegreeOn_eq_relation_degreeOn
    (G : RotationDiskData V E) (S : Finset (Finset E)) (f : Finset E) :
    G.supportDualDegreeOn S f =
      G.supportDualRelation.degreeOn S f := by
  rfl

/-- Every nonempty finite face subset has a member of minimum induced
support-dual degree. -/
theorem exists_min_supportDualDegree
    (G : RotationDiskData V E) {S : Finset (Finset E)} (hS : S.Nonempty) :
    ∃ f ∈ S, ∀ g ∈ S,
      G.supportDualDegreeOn S f ≤ G.supportDualDegreeOn S g := by
  classical
  rcases G.supportDualRelation.exists_min_degree S hS with
    ⟨f, hf, hmin⟩
  refine ⟨f, hf, ?_⟩
  intro g hg
  simpa [supportDualDegreeOn_eq_relation_degreeOn] using hmin g hg

/-- The honest weak leaf fact available without a spanning-tree theorem:
every nonempty finite face subset contains a singleton induced subfamily whose
support-dual degree is at most one. -/
theorem exists_singleton_supportDualLeaf_subset
    (G : RotationDiskData V E) {S : Finset (Finset E)} (hS : S.Nonempty) :
    ∃ T ⊆ S, ∃ f ∈ T, G.supportDualDegreeOn T f ≤ 1 := by
  classical
  rcases G.supportDualRelation.exists_singleton_leaf_subset S hS with
    ⟨T, hT, f, hfT, hleaf⟩
  refine ⟨T, hT, f, hfT, ?_⟩
  simpa [supportDualDegreeOn_eq_relation_degreeOn] using hleaf

end RotationDiskData

end Mettapedia.GraphTheory.FourColor
