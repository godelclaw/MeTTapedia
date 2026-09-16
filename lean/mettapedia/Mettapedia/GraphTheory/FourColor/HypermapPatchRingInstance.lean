import Mettapedia.GraphTheory.FourColor.HypermapPatchRing

/-!
# A patch with a nonempty ring, written out

`HypermapPatchRing` defines what it is for a hypermap to be the gluing of two
hypermaps along a ring, and derives genus additivity from it.  A definition
with that many conditions is worth nothing until one knows the conditions can
all hold *at once, with a ring that is not empty* — the empty-ring case is the
disjoint union, and that was already proved.

This module writes out one patch in full and checks every condition by
evaluation, so the satisfiability claim is machine-checked rather than
asserted.

## The example

`triangleMap` is the map of a triangle: three vertices, three edges, six darts,
two faces, and genus zero.  Darts are numbered so that `0,1` is one edge, `2,3`
the next and `4,5` the last; the vertices are `{0,5}`, `{1,2}` and `{3,4}`.

It is cut along the two darts `{2,5}`.  The disk keeps the two vertices `{0,5}`
and `{1,2}` — four darts, two of them interior — and the remainder keeps the
darts `{2,3,4,5}`, again with two interior.  So neither side is the whole map
and neither is a single ring: both embeddings are proper, and the ring has two
darts.

Every field of `Patch` is checked by `decide`, and the orbit counts of all
three maps are computed independently of the general theorems (by exhibiting a
complete invariant for each permutation, and a connecting walk for each map).
The five counting identities can then be read off and compared with what
`HypermapPatchRing` proves.
-/

namespace Mettapedia.GraphTheory.FourColor

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability
open Mettapedia.GraphTheory.OrbitCountSplitting

namespace HypermapPatchRingInstance

/-! ## The three maps -/

/-- The triangle's edge permutation: `(0 1)(2 3)(4 5)`. -/
def gEdge : Perm (Fin 6) := Equiv.swap 0 1 * (Equiv.swap 2 3 * Equiv.swap 4 5)

/-- The triangle's node permutation: `(0 5)(1 2)(3 4)`. -/
def gNode : Perm (Fin 6) := Equiv.swap 0 5 * (Equiv.swap 1 2 * Equiv.swap 3 4)

/-- The triangle: three vertices, three edges, two faces, six darts. -/
def triangleMap : Hypermap (Fin 6) where
  edge := gEdge
  node := gNode
  face := gNode * gEdge
  cancel3 := by decide

/-- The disk's edge permutation: `(0 1)(2 3)`, with `{2,3}` the border. -/
def dEdge : Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

/-- The disk's node permutation: `(0 3)(1 2)`. -/
def dNode : Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2

/-- The disk: the two triangle vertices kept inside the cut. -/
def diskMap : Hypermap (Fin 4) where
  edge := dEdge
  node := dNode
  face := dNode * dEdge
  cancel3 := by decide

/-- The remainder's edge permutation: `(0 1)(2 3)`. -/
def rEdge : Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

/-- The remainder's node permutation: `(0 3)(1 2)`, with `{0,3}` the border. -/
def rNode : Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2

/-- The remainder: the triangle darts left outside the cut. -/
def remMap : Hypermap (Fin 4) where
  edge := rEdge
  node := rNode
  face := rNode * rEdge
  cancel3 := by decide

/-! ## The two embeddings and the two borders -/

/-- The disk's embedding: its four darts are the triangle darts `0,1,2,5`. -/
def hdEx : Fin 4 → Fin 6 := ![0, 1, 2, 5]

/-- The remainder's embedding: its four darts are the triangle darts
`2,3,4,5`. -/
def hrEx : Fin 4 → Fin 6 := ![2, 3, 4, 5]

/-- The disk border: one edge orbit of the disk. -/
def bdEx : Set (Fin 4) := fun x => x = 2 ∨ x = 3

/-- The remainder border: one node orbit of the remainder. -/
def brEx : Set (Fin 4) := fun x => x = 0 ∨ x = 3

instance : ∀ x, Decidable (x ∈ bdEx) :=
  fun x => inferInstanceAs (Decidable (x = 2 ∨ x = 3))

instance : ∀ x, Decidable (x ∈ brEx) :=
  fun x => inferInstanceAs (Decidable (x = 0 ∨ x = 3))

instance : ∀ x : Fin 6, Decidable (x ∈ hdEx '' bdEx) :=
  fun x => inferInstanceAs (Decidable (∃ a, a ∈ bdEx ∧ hdEx a = x))

instance : ∀ x : Fin 6, Decidable (x ∈ hrEx '' brEx) :=
  fun x => inferInstanceAs (Decidable (∃ a, a ∈ brEx ∧ hrEx a = x))

/-! ## The ring is not empty, and neither side is everything -/

theorem bdEx_nonempty : bdEx.Nonempty := ⟨2, Or.inl rfl⟩

theorem bdEx_ncard : bdEx.ncard = 2 := by
  have h : bdEx = ({2, 3} : Set (Fin 4)) := by
    ext x
    exact Iff.rfl
  rw [h]
  exact Set.ncard_pair (by decide)

/-- The disk misses two darts of the triangle: the embedding is proper. -/
theorem hdEx_not_surjective : ¬ Function.Surjective hdEx := by decide

/-- The remainder misses two darts of the triangle: so is that one. -/
theorem hrEx_not_surjective : ¬ Function.Surjective hrEx := by decide

/-- Two of the disk's darts are off its border: the disk is more than a ring. -/
theorem bdEx_ne_univ : bdEx ≠ (Set.univ : Set (Fin 4)) := by
  intro h
  have : (0 : Fin 4) ∈ bdEx := h ▸ Set.mem_univ 0
  revert this
  decide

/-- And two of the remainder's are off its border. -/
theorem brEx_ne_univ : brEx ≠ (Set.univ : Set (Fin 4)) := by
  intro h
  have : (1 : Fin 4) ∈ brEx := h ▸ Set.mem_univ 1
  revert this
  decide

/-! ## The patch

Every condition is checked by evaluation. -/

theorem patch_triangle :
    Hypermap.Patch triangleMap diskMap remMap hdEx hrEx bdEx brEx where
  injd := by decide
  injr := by decide
  edgeCycle_d := by decide
  nodeCycle_r := by decide
  simple_d := by decide
  cover := by decide
  ring_eq := by
    ext x
    revert x
    decide
  ring_rev := by decide
  edge_d := by decide
  node_d := by decide
  edge_r := by decide
  node_r := by decide

/-! ## The orbit counts, computed independently

Nothing below uses `HypermapPatchRing`: each permutation gets a complete
invariant, and each map a connecting walk.  These are the numbers the five
counting identities must reproduce. -/

section Counts

variable {D : Type*} [Fintype D]

private theorem count_of_invariant {n : ℕ} {σ : Perm D} (f : D → Fin n)
    (hsep : ∀ x y : D, σ.SameCycle x y ↔ f x = f y) (hsurj : Function.Surjective f) :
    orbitCount σ = n := by
  rw [orbitCount_eq_card_of_completeInvariant f hsep hsurj, Nat.card_eq_fintype_card,
    Fintype.card_fin]

private theorem comp_of_connected [Nonempty D] {L : List (Perm D)}
    (h : ∀ x y : D, WordReachable L x y) : wordOrbitCount L = 1 := by
  have := wordOrbitCount_eq_card_of_completeInvariant (L := L) (fun _ => (0 : Fin 1))
    (fun x y => ⟨fun _ => rfl, fun _ => h x y⟩) (fun a => ⟨Classical.arbitrary D, Subsingleton.elim _ a⟩)
  rw [this, Nat.card_eq_fintype_card, Fintype.card_fin]

end Counts

theorem orbitCount_gEdge : orbitCount triangleMap.edge = 3 :=
  count_of_invariant ![0, 0, 1, 1, 2, 2] (by decide) (by decide)

theorem orbitCount_gNode : orbitCount triangleMap.node = 3 :=
  count_of_invariant ![0, 1, 1, 2, 2, 0] (by decide) (by decide)

theorem orbitCount_gFace : orbitCount triangleMap.face = 2 :=
  count_of_invariant ![0, 1, 0, 1, 0, 1] (by decide) (by decide)

theorem orbitCount_dEdge : orbitCount diskMap.edge = 2 :=
  count_of_invariant ![0, 0, 1, 1] (by decide) (by decide)

theorem orbitCount_dNode : orbitCount diskMap.node = 2 :=
  count_of_invariant ![0, 1, 1, 0] (by decide) (by decide)

theorem orbitCount_dFace : orbitCount diskMap.face = 2 :=
  count_of_invariant ![0, 1, 0, 1] (by decide) (by decide)

theorem orbitCount_rEdge : orbitCount remMap.edge = 2 :=
  count_of_invariant ![0, 0, 1, 1] (by decide) (by decide)

theorem orbitCount_rNode : orbitCount remMap.node = 2 :=
  count_of_invariant ![0, 1, 1, 0] (by decide) (by decide)

theorem orbitCount_rFace : orbitCount remMap.face = 2 :=
  count_of_invariant ![0, 1, 0, 1] (by decide) (by decide)

/-! ### Connectivity

Each map is connected, by a walk that visits every dart. -/

section Walks

variable {D : Type*} [Fintype D] [DecidableEq D]

omit [Fintype D] [DecidableEq D] in
private theorem reach_of_eq {L : List (Perm D)} {g : Perm D} (hg : g ∈ L) {u v : D}
    (h : g u = v) : WordReachable L u v := h ▸ wordReachable_step hg u

omit [DecidableEq D] in
private theorem conn_of_base {L : List (Perm D)} {z : D}
    (h : ∀ x : D, WordReachable L z x) : ∀ x y : D, WordReachable L x y :=
  fun x y => (h x).symm.trans (h y)

end Walks

theorem compCount_triangle : Hypermap.compCount triangleMap = 1 := by
  refine comp_of_connected (conn_of_base (z := (0 : Fin 6)) ?_)
  have he : triangleMap.edge ∈ [triangleMap.edge, triangleMap.node, triangleMap.face] :=
    List.mem_cons_self
  have hf : triangleMap.face ∈ [triangleMap.edge, triangleMap.node, triangleMap.face] :=
    List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have h01 : WordReachable _ (0 : Fin 6) 1 := reach_of_eq he (by decide)
  have h02 : WordReachable _ (0 : Fin 6) 2 := reach_of_eq hf (by decide)
  have h24 : WordReachable _ (2 : Fin 6) 4 := reach_of_eq hf (by decide)
  have h15 : WordReachable _ (1 : Fin 6) 5 := reach_of_eq hf (by decide)
  have h53 : WordReachable _ (5 : Fin 6) 3 := reach_of_eq hf (by decide)
  intro x
  fin_cases x
  · exact WordReachable.refl _ _
  · exact h01
  · exact h02
  · exact (h01.trans h15).trans h53
  · exact h02.trans h24
  · exact h01.trans h15

/-- The two pieces are connected too; their generator families have the same
shape, so one walk does for both. -/
private theorem compCount_four (H : Hypermap (Fin 4))
    (h01 : H.edge 0 = 1) (h12 : H.node 1 = 2) (h23 : H.edge 2 = 3) :
    Hypermap.compCount H = 1 := by
  refine comp_of_connected (conn_of_base (z := (0 : Fin 4)) ?_)
  have he : H.edge ∈ [H.edge, H.node, H.face] := List.mem_cons_self
  have hn : H.node ∈ [H.edge, H.node, H.face] :=
    List.mem_cons_of_mem _ List.mem_cons_self
  have r01 : WordReachable _ (0 : Fin 4) 1 := reach_of_eq he h01
  have r12 : WordReachable _ (1 : Fin 4) 2 := reach_of_eq hn h12
  have r23 : WordReachable _ (2 : Fin 4) 3 := reach_of_eq he h23
  intro x
  fin_cases x
  · exact WordReachable.refl _ _
  · exact r01
  · exact r01.trans r12
  · exact (r01.trans r12).trans r23

theorem compCount_disk : Hypermap.compCount diskMap = 1 :=
  compCount_four diskMap (by decide) (by decide) (by decide)

theorem compCount_rem : Hypermap.compCount remMap = 1 :=
  compCount_four remMap (by decide) (by decide) (by decide)

/-! ## The five counting identities, read off the numbers

Each of these is stated with its two sides computed by hand from the
independent counts above, and is therefore a check on the general theorems of
`HypermapPatchRing` rather than a consequence of them.  Every one of them
matches. -/

/-- Dart count: `4 + 4 = 2 + 6`. -/
theorem check_card :
    Fintype.card (Fin 4) + Fintype.card (Fin 4) = bdEx.ncard + Fintype.card (Fin 6) := by
  rw [bdEx_ncard]
  simp

/-- Edge orbits: `2 + 2 = 1 + 3`. -/
theorem check_edge :
    orbitCount diskMap.edge + orbitCount remMap.edge
      = Hypermap.Patch.borderMult bdEx + orbitCount triangleMap.edge := by
  rw [orbitCount_dEdge, orbitCount_rEdge, orbitCount_gEdge,
    Hypermap.Patch.borderMult_pos bdEx_nonempty]

/-- Node orbits: `2 + 2 = 1 + 3`. -/
theorem check_node :
    orbitCount diskMap.node + orbitCount remMap.node
      = Hypermap.Patch.borderMult bdEx + orbitCount triangleMap.node := by
  rw [orbitCount_dNode, orbitCount_rNode, orbitCount_gNode,
    Hypermap.Patch.borderMult_pos bdEx_nonempty]

/-- Face orbits: `2 + 2 = 2 + 2`, the ring length on the right. -/
theorem check_face :
    orbitCount diskMap.face + orbitCount remMap.face
      = bdEx.ncard + orbitCount triangleMap.face := by
  rw [orbitCount_dFace, orbitCount_rFace, orbitCount_gFace, bdEx_ncard]

/-- Components: `1 + 1 = 1 + 1`. -/
theorem check_comp :
    Hypermap.compCount diskMap + Hypermap.compCount remMap
      = Hypermap.Patch.borderMult bdEx + Hypermap.compCount triangleMap := by
  rw [compCount_disk, compCount_rem, compCount_triangle,
    Hypermap.Patch.borderMult_pos bdEx_nonempty]

/-- All three maps are planar, so genus additivity reads `0 = 0 + 0` here. -/
theorem genus_triangle : Hypermap.genus triangleMap = 0 := by
  have h := Hypermap.even_genus triangleMap
  rw [Hypermap.eulerRhs_eq_card_add_two_mul_compCount,
    Hypermap.eulerLhs_eq_orbit_sum, compCount_triangle, orbitCount_gEdge,
    orbitCount_gNode, orbitCount_gFace] at h
  simp only [Fintype.card_fin] at h
  omega

theorem genus_disk : Hypermap.genus diskMap = 0 := by
  have h := Hypermap.even_genus diskMap
  rw [Hypermap.eulerRhs_eq_card_add_two_mul_compCount,
    Hypermap.eulerLhs_eq_orbit_sum, compCount_disk, orbitCount_dEdge,
    orbitCount_dNode, orbitCount_dFace] at h
  simp only [Fintype.card_fin] at h
  omega

theorem genus_rem : Hypermap.genus remMap = 0 := by
  have h := Hypermap.even_genus remMap
  rw [Hypermap.eulerRhs_eq_card_add_two_mul_compCount,
    Hypermap.eulerLhs_eq_orbit_sum, compCount_rem, orbitCount_rEdge,
    orbitCount_rNode, orbitCount_rFace] at h
  simp only [Fintype.card_fin] at h
  omega

/-! ## The general theorems, against the numbers

Each statement below is the corresponding theorem of `HypermapPatchRing`,
instantiated at this patch and with every count replaced by the value computed
independently above.  The numbers have to balance for the file to compile, so a
general statement whose border or ring contribution sat on the wrong side, or
counted the wrong thing, would be caught here. -/

/-- The dart identity, run backwards: it forces the ring to have two darts,
which is what `bdEx_ncard` says independently. -/
theorem ringLength_from_card : bdEx.ncard = 2 := by
  have h := patch_triangle.card_patch
  simp only [Fintype.card_fin] at h
  omega

/-- The edge identity forces the border to absorb exactly one edge orbit. -/
theorem borderMult_from_edge : Hypermap.Patch.borderMult bdEx = 1 := by
  have h := patch_triangle.orbitCount_edge_add
  rw [orbitCount_dEdge, orbitCount_rEdge, orbitCount_gEdge] at h
  omega

/-- The node identity forces the same, from the other side. -/
theorem borderMult_from_node : Hypermap.Patch.borderMult bdEx = 1 := by
  have h := patch_triangle.orbitCount_node_add
  rw [orbitCount_dNode, orbitCount_rNode, orbitCount_gNode] at h
  omega

/-- The face identity forces the ring length, not the border multiplicity: the
two would differ if the ring had any length other than one, and here it does —
the ring has two darts and the faces still balance. -/
theorem ringLength_from_face : bdEx.ncard = 2 := by
  have h := patch_triangle.orbitCount_face_add
  rw [orbitCount_dFace, orbitCount_rFace, orbitCount_gFace] at h
  omega

/-- The component identity forces the border multiplicity again. -/
theorem borderMult_from_comp : Hypermap.Patch.borderMult bdEx = 1 := by
  have h := patch_triangle.compCount_add
  rw [compCount_disk, compCount_rem, compCount_triangle] at h
  omega

/-- All four routes agree with the direct computation. -/
theorem borderMult_agrees : Hypermap.Patch.borderMult bdEx = 1 :=
  Hypermap.Patch.borderMult_pos bdEx_nonempty

theorem ringLength_agrees : ringLength_from_card = bdEx_ncard := rfl

/-- Genus additivity for this patch. -/
theorem genus_additive :
    Hypermap.genus triangleMap = Hypermap.genus diskMap + Hypermap.genus remMap :=
  patch_triangle.genus_patch

/-- And the triangle is planar exactly because both its pieces are. -/
theorem planar_here : Hypermap.Planar triangleMap :=
  patch_triangle.planar_patch.2
    ⟨(Hypermap.planar_iff_genus_eq_zero diskMap).2 genus_disk,
      (Hypermap.planar_iff_genus_eq_zero remMap).2 genus_rem⟩

/-! ## Bridges

The bridgelessness transfer has one hypothesis beyond the two pieces being
bridgeless — that the border has no chords — so that hypothesis needs a
witness too.  Here all three are checked by evaluation, and the glued map's
bridgelessness is then obtained twice: directly, and through the general
theorem. -/

theorem bridgeless_disk : Hypermap.Patch.Bridgeless diskMap := by
  show ∀ x : Fin 4, ¬ diskMap.face.SameCycle x (diskMap.edge x)
  decide

theorem bridgeless_rem : Hypermap.Patch.Bridgeless remMap := by
  show ∀ x : Fin 4, ¬ remMap.face.SameCycle x (remMap.edge x)
  decide

/-- The border of this disk has no chords, so the hypothesis of
`bridgeless_patch` is satisfiable alongside everything else. -/
theorem chordless_bd : Hypermap.Patch.Chordless diskMap bdEx := by
  show ∀ x ∈ bdEx, ∀ y ∈ bdEx,
    (∃ z : Fin 4, diskMap.face.SameCycle x z ∧ diskMap.face.SameCycle (diskMap.edge z) y) →
      y = diskMap.edge x ∨ y = diskMap.edge.symm x
  decide

/-- Computed directly. -/
theorem bridgeless_triangle : Hypermap.Patch.Bridgeless triangleMap := by
  show ∀ x : Fin 6, ¬ triangleMap.face.SameCycle x (triangleMap.edge x)
  decide

/-- Obtained from the two pieces through the general theorem; it has to be the
same statement. -/
theorem bridgeless_triangle_from_patch : Hypermap.Patch.Bridgeless triangleMap :=
  patch_triangle.bridgeless_patch bridgeless_disk bridgeless_rem chordless_bd

/-- And the converse transfer, in the other direction. -/
theorem bridgeless_parts_here :
    Hypermap.Patch.Bridgeless diskMap ∧ Hypermap.Patch.Bridgeless remMap :=
  patch_triangle.bridgeless_parts bridgeless_triangle

end HypermapPatchRingInstance

end Mettapedia.GraphTheory.FourColor
