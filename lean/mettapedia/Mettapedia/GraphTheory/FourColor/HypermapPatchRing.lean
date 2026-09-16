import Mettapedia.GraphTheory.FourColor.HypermapSymmetry
import Mettapedia.GraphTheory.OrbitCountSplitting

/-!
# Patching along a ring: genus additivity with a nonempty border

`HypermapPatch` proves the arithmetic core of genus additivity,
`genus_add_of_orbit_counts`, from five counting statements, and supplies those
statements only in the degenerate case of an empty border, where the gluing is
a disjoint union.  This module supplies them in general.

A **patch** presents a hypermap `G` as two hypermaps glued along a ring.  The
two sides are not symmetric.  The inner side — the *disk* `Hd` — carries the
ring as one of its **edge** orbits; the outer side — the *remainder* `Hr` —
carries it as one of its **node** orbits.  The two embeddings `hd` and `hr`
cover `G` and meet exactly on the ring, each preserving the structure it does
not use to present the border: `hd` is a node morphism everywhere and an edge
morphism off the ring, `hr` an edge morphism everywhere and a node morphism off
its own ring.  One further condition ties the two borders together: they run in
opposite directions, which is `Patch.ring_rev`.

Beyond those, exactly one geometric condition is needed, and it is the one that
makes the disk a disk: the border must be **simple** — no two of its darts lie
on a common face of `Hd`.  It is what forces a face excursion that leaves the
remainder into the disk to come all the way back, and it is used nowhere else.

## What is proved

* `Patch.genus_patch` — `genus G = genus Hd + genus Hr`, for any border,
  empty or not;
* `Patch.planar_patch` — `G` is planar exactly when both pieces are;
* `Patch.bridgeless_of_patch` — a bridgeless glued map has bridgeless pieces.

The five counting identities are proved as `Patch.card_patch`,
`Patch.orbitCount_edge_add`, `Patch.orbitCount_node_add`,
`Patch.orbitCount_face_add` and `Patch.compCount_add`, in exactly the shape
`genus_add_of_orbit_counts` consumes, with `b` the number of border orbits
absorbed (one for a genuine ring) and `r` the ring length.

## How the counting is done

Each identity is one application of each of the two instruments of
`Mettapedia.GraphTheory.OrbitCountSplitting`: **Tool A**
(`classCountOn_add_compl` and its specialisations) splits an orbit count over
a region and its complement, and **Tool B** (`classCountOn_preimage` and its
specialisations) transports a count along a map that is equivariant only over
the region.  The edge and node identities are immediate.  The face and
component identities are not, because there `hr` is *not* equivariant over the
region: a face of `G` that meets the remainder can dive into the disk at the
ring and come back.

Both are handled by the same device, and it replaces the path inductions this
argument is usually written with.  For the faces, `Patch.Over x wr` says that
the `G`-dart `x` sits over the remainder dart `wr`: either it *is* `hr wr`, or
it lies in the disk, on the face of the border dart over `hr wr`.
`Patch.Over.face_step` says this relation is carried by one `G`-face step to
the same relation over `wr` or over `Hr.face wr` — so the whole face walk of
`G` is a face walk of `Hr` with excursions, and reading off the endpoint gives
`Patch.sameCycle_face_r`, that `hr` reflects the face relation.  For the
components, `Patch.diskComp` and `Patch.remComp` play the same role with all
three permutations instead of the face alone.
-/

namespace Mettapedia.GraphTheory.FourColor

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery GoertzelV24WordReachability
open Mettapedia.GraphTheory.OrbitCountSplitting

namespace Hypermap

variable {Dg Dd Dr : Type*} [Fintype Dg] [DecidableEq Dg] [Fintype Dd] [DecidableEq Dd]
  [Fintype Dr] [DecidableEq Dr]

/-- **A patch: `G` is the gluing of the disk `Hd` and the remainder `Hr` along
a ring.**

`bd` is the border of the disk, one edge orbit of `Hd`; `br` is the border of
the remainder, one node orbit of `Hr`; the two have the same image in `G`, with
opposite orientations (`ring_rev`), and that common image is exactly where the
two embeddings meet (`cover`).  `simple_d` is the disk condition: distinct
border darts lie on distinct faces of the disk. -/
structure Patch (G : Hypermap Dg) (Hd : Hypermap Dd) (Hr : Hypermap Dr)
    (hd : Dd → Dg) (hr : Dr → Dg) (bd : Set Dd) (br : Set Dr) : Prop where
  /-- the disk embeds. -/
  injd : Function.Injective hd
  /-- the remainder embeds. -/
  injr : Function.Injective hr
  /-- the disk border is a single edge orbit of the disk. -/
  edgeCycle_d : ∀ x y : Dd, x ∈ bd → (Hd.edge.SameCycle x y ↔ y ∈ bd)
  /-- the remainder border is a single node orbit of the remainder. -/
  nodeCycle_r : ∀ x y : Dr, x ∈ br → (Hr.node.SameCycle x y ↔ y ∈ br)
  /-- the disk border is simple: no face of the disk meets it twice. -/
  simple_d : ∀ x ∈ bd, ∀ y ∈ bd, Hd.face.SameCycle x y → x = y
  /-- the two images cover `G`, and meet exactly along the ring. -/
  cover : ∀ x : Dg, x ∈ Set.range hr ↔ (x ∉ Set.range hd ∨ x ∈ hd '' bd)
  /-- the two borders have the same image. -/
  ring_eq : hr '' br = hd '' bd
  /-- the two borders run in opposite directions. -/
  ring_rev : ∀ (xd : Dd) (xr : Dr), hd (Hd.edge xd) = hr xr ↔ hd xd = hr (Hr.node xr)
  /-- off its border the disk embedding preserves edges. -/
  edge_d : ∀ x : Dd, x ∉ bd → hd (Hd.edge x) = G.edge (hd x)
  /-- the disk embedding preserves nodes everywhere. -/
  node_d : ∀ x : Dd, hd (Hd.node x) = G.node (hd x)
  /-- the remainder embedding preserves edges everywhere. -/
  edge_r : ∀ x : Dr, hr (Hr.edge x) = G.edge (hr x)
  /-- off its border the remainder embedding preserves nodes. -/
  node_r : ∀ x : Dr, x ∉ br → hr (Hr.node x) = G.node (hr x)

namespace Patch

variable {G : Hypermap Dg} {Hd : Hypermap Dd} {Hr : Hypermap Dr}
  {hd : Dd → Dg} {hr : Dr → Dg} {bd : Set Dd} {br : Set Dr}

/-! ## The ring, and where the two sides meet -/

theorem ring_subset_range_r (P : Patch G Hd Hr hd hr bd br) :
    hd '' bd ⊆ Set.range hr := fun _ hx => (P.cover _).2 (Or.inr hx)

/-- A disk dart is in the remainder's image exactly when it is a border dart. -/
theorem mem_bd_iff (P : Patch G Hd Hr hd hr bd br) (xd : Dd) :
    hd xd ∈ Set.range hr ↔ xd ∈ bd := by
  constructor
  · intro hx
    rcases (P.cover _).1 hx with h | h
    · exact absurd (Set.mem_range_self xd) h
    · obtain ⟨y, hy, hxy⟩ := h
      exact P.injd hxy ▸ hy
  · exact fun hx => P.ring_subset_range_r ⟨xd, hx, rfl⟩

/-- A remainder dart is in the disk's image exactly when it is a border dart. -/
theorem mem_br_iff (P : Patch G Hd Hr hd hr bd br) (xr : Dr) :
    hr xr ∈ Set.range hd ↔ xr ∈ br := by
  constructor
  · intro hx
    have h := (P.cover (hr xr)).1 (Set.mem_range_self xr)
    rcases h with h | h
    · exact absurd hx h
    · rw [← P.ring_eq] at h
      obtain ⟨y, hy, hxy⟩ := h
      exact P.injr hxy ▸ hy
  · intro hx
    have : hr xr ∈ hr '' br := ⟨xr, hx, rfl⟩
    rw [P.ring_eq] at this
    obtain ⟨y, _, hy⟩ := this
    exact ⟨y, hy⟩

/-- The two images cover `G`. -/
theorem mem_range_or (P : Patch G Hd Hr hd hr bd br) (x : Dg) :
    x ∈ Set.range hd ∨ x ∈ Set.range hr := by
  by_cases h : x ∈ Set.range hd
  · exact Or.inl h
  · exact Or.inr ((P.cover x).2 (Or.inl h))

theorem range_inter (P : Patch G Hd Hr hd hr bd br) :
    Set.range hd ∩ Set.range hr = hd '' bd := by
  ext x
  constructor
  · rintro ⟨⟨y, rfl⟩, h2⟩
    exact ⟨y, (P.mem_bd_iff y).1 h2, rfl⟩
  · rintro h
    exact ⟨(Set.image_subset_range _ _) h, P.ring_subset_range_r h⟩

/-! ## The two borders are closed under the permutations that present them -/

theorem mem_bd_edge_iff (P : Patch G Hd Hr hd hr bd br) (x : Dd) :
    Hd.edge x ∈ bd ↔ x ∈ bd := by
  constructor
  · intro hx
    exact (P.edgeCycle_d _ x hx).1 ⟨-1, by simp⟩
  · intro hx
    exact (P.edgeCycle_d x _ hx).1 ⟨1, by simp⟩

theorem mem_br_node_iff (P : Patch G Hd Hr hd hr bd br) (x : Dr) :
    Hr.node x ∈ br ↔ x ∈ br := by
  constructor
  · intro hx
    exact (P.nodeCycle_r _ x hx).1 ⟨-1, by simp⟩
  · intro hx
    exact (P.nodeCycle_r x _ hx).1 ⟨1, by simp⟩

/-- Every dart of the remainder border is matched by a dart of the disk border. -/
theorem exists_bd_of_br (P : Patch G Hd Hr hd hr bd br) {xr : Dr} (hx : xr ∈ br) :
    ∃ ud ∈ bd, hd ud = hr xr := by
  have : hr xr ∈ hd '' bd := P.ring_eq ▸ ⟨xr, hx, rfl⟩
  obtain ⟨ud, hud, h⟩ := this
  exact ⟨ud, hud, h⟩

/-- Every dart of the disk border is matched by a dart of the remainder border. -/
theorem exists_br_of_bd (P : Patch G Hd Hr hd hr bd br) {ud : Dd} (hu : ud ∈ bd) :
    ∃ xr ∈ br, hr xr = hd ud := by
  have : hd ud ∈ hr '' br := P.ring_eq ▸ ⟨ud, hu, rfl⟩
  obtain ⟨xr, hxr, h⟩ := this
  exact ⟨xr, hxr, h⟩

/-- A disk dart whose image is a remainder dart's image is a border dart. -/
theorem mem_bd_of_eq (P : Patch G Hd Hr hd hr bd br) {ud : Dd} {xr : Dr}
    (h : hd ud = hr xr) : ud ∈ bd :=
  (P.mem_bd_iff ud).1 ⟨xr, h.symm⟩

/-- A remainder dart whose image is a disk dart's image is a border dart. -/
theorem mem_br_of_eq (P : Patch G Hd Hr hd hr bd br) {ud : Dd} {xr : Dr}
    (h : hd ud = hr xr) : xr ∈ br :=
  (P.mem_br_iff xr).1 ⟨ud, h⟩

/-! ## Face morphism laws

Neither embedding is a face morphism at the ring; both are one away from it.
The two proofs are the same: solve the composite law for the face, and use the
morphism laws that do hold at that point. -/

/-- Off the border the disk embedding preserves faces. -/
theorem face_d (P : Patch G Hd Hr hd hr bd br) {x : Dd} (hx : x ∉ bd) :
    hd (Hd.face x) = G.face (hd x) := by
  have hnode : Hd.node (Hd.face x) ∉ bd := by
    intro hcon
    apply hx
    have h := (P.mem_bd_edge_iff (Hd.node (Hd.face x))).2 hcon
    rwa [Hd.edge_node_face] at h
  have hx' : hd x = G.edge (G.node (hd (Hd.face x))) := by
    conv_lhs => rw [← Hd.edge_node_face x]
    rw [P.edge_d _ hnode, P.node_d]
  rw [hx', G.face_edge_node]

/-- Where its own face image misses the border, the remainder embedding
preserves faces. -/
theorem face_r (P : Patch G Hd Hr hd hr bd br) {x : Dr} (hx : Hr.face x ∉ br) :
    hr (Hr.face x) = G.face (hr x) := by
  have hx' : hr x = G.edge (G.node (hr (Hr.face x))) := by
    conv_lhs => rw [← Hr.edge_node_face x]
    rw [P.edge_r, P.node_r _ hx]
  rw [hx', G.face_edge_node]

/-- **The face step at the ring.**  When the next face dart of the remainder is
a border dart, the `G`-face walk does not follow it: it turns into the disk, at
the face successor of the matching disk border dart.

This is the one place where `ring_rev` is used, and it is what makes the two
borders' opposite orientations matter. -/
theorem face_step_ring (P : Patch G Hd Hr hd hr bd br) {xr : Dr} {ud : Dd}
    (h : hd ud = hr (Hr.face xr)) : G.face (hr xr) = hd (Hd.face ud) := by
  set wd : Dd := Hd.edge.symm ud with hwd
  have hedge : Hd.edge wd = ud := Hd.edge.apply_symm_apply ud
  have h1 : hd (Hd.edge wd) = hr (Hr.face xr) := by rw [hedge]; exact h
  have h2 : hd wd = hr (Hr.node (Hr.face xr)) := (P.ring_rev wd (Hr.face xr)).1 h1
  have h3 : hr xr = G.edge (hd wd) := by
    conv_lhs => rw [← Hr.edge_node_face xr]
    rw [P.edge_r, h2]
  have h4 : hd wd = G.node (hd (Hd.face ud)) := by
    conv_lhs => rw [← Hd.cancel3 wd, hedge]
    rw [P.node_d]
  rw [h3, h4, G.face_edge_node]

/-! ## The disk carries whole faces

The border being simple is what makes this work: a disk face through a border
dart meets the border only there, so walking it once returns to the start
without ever meeting a point where `hd` fails to be a face morphism. -/

omit [Fintype Dg] [DecidableEq Dg] [Fintype Dd] [DecidableEq Dd] [Fintype Dr]
  [DecidableEq Dr] in
private theorem sameCycle_apply' (σ : Perm Dd) (x : Dd) : σ.SameCycle x (σ x) :=
  ⟨1, by simp⟩

/-- **The disk embedding never leaves a `G`-face.**  Off the border this is one
face step; at a border dart it is the whole disk face, walked once. -/
theorem sameCycle_face_d_step (P : Patch G Hd Hr hd hr bd br) (x : Dd) :
    G.face.SameCycle (hd x) (hd (Hd.face x)) := by
  classical
  by_cases hx : x ∉ bd
  · rw [P.face_d hx]
    exact ⟨1, by simp⟩
  rw [not_not] at hx
  -- the first return of the disk face walk to `x`
  have hex : ∃ m : ℕ, 0 < m ∧ (Hd.face ^ m) x = x :=
    ⟨orderOf Hd.face, orderOf_pos _, by rw [pow_orderOf_eq_one]; rfl⟩
  set m : ℕ := Nat.find hex with hm
  obtain ⟨hmpos, hmfix⟩ : 0 < m ∧ (Hd.face ^ m) x = x := Nat.find_spec hex
  -- nothing strictly inside that walk is a border dart
  have hoff : ∀ j : ℕ, 0 < j → j < m → (Hd.face ^ j) x ∉ bd := by
    intro j hj hjm hmem
    have hcyc : Hd.face.SameCycle x ((Hd.face ^ j) x) := ⟨j, by simp⟩
    have := P.simple_d x hx _ hmem hcyc
    exact absurd ⟨hj, this.symm⟩ (Nat.find_min hex hjm)
  -- so the walk is a `G`-face walk from the first step onwards
  have hwalk : ∀ j : ℕ, j + 1 ≤ m →
      hd ((Hd.face ^ (j + 1)) x) = (G.face ^ j) (hd (Hd.face x)) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
        intro hle
        have hstep : (Hd.face ^ (j + 1 + 1)) x = Hd.face ((Hd.face ^ (j + 1)) x) := by
          rw [pow_succ', Perm.mul_apply]
        rw [hstep, P.face_d (hoff (j + 1) (Nat.succ_pos j) (by omega)), ih (by omega)]
        rw [pow_succ', Perm.mul_apply]
  obtain ⟨k, hk⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hfin := hwalk k (by omega)
  rw [← hk, hmfix] at hfin
  exact ⟨-(k : ℤ), by rw [zpow_neg, zpow_natCast, hfin]; simp⟩

/-- **The disk embedding preserves the face relation.** -/
theorem sameCycle_face_d (P : Patch G Hd Hr hd hr bd br) {x y : Dd}
    (h : Hd.face.SameCycle x y) : G.face.SameCycle (hd x) (hd y) := by
  obtain ⟨n, rfl⟩ := exists_nat_pow_apply_eq h
  clear h
  induction n with
  | zero => simpa using SameCycle.refl G.face (hd x)
  | succ n ih =>
      have hstep : (Hd.face ^ (n + 1)) x = Hd.face ((Hd.face ^ n) x) := by
        rw [pow_succ', Perm.mul_apply]
      rw [hstep]
      exact ih.trans (P.sameCycle_face_d_step _)

/-- **The remainder embedding never leaves a `G`-face either.**  Where the face
step would cross the ring, the `G`-face dives into the disk and comes back. -/
theorem sameCycle_face_r_step (P : Patch G Hd Hr hd hr bd br) (x : Dr) :
    G.face.SameCycle (hr x) (hr (Hr.face x)) := by
  by_cases hx : Hr.face x ∈ br
  · obtain ⟨ud, hud, hu⟩ := P.exists_bd_of_br hx
    have h1 : G.face.SameCycle (hr x) (hd (Hd.face ud)) := by
      refine ⟨1, ?_⟩
      rw [zpow_one, P.face_step_ring hu]
    rw [← hu]
    exact h1.trans (P.sameCycle_face_d_step ud).symm
  · rw [P.face_r hx]
    exact ⟨1, by simp⟩

/-- **The remainder embedding preserves the face relation.** -/
theorem sameCycle_face_r_of (P : Patch G Hd Hr hd hr bd br) {x y : Dr}
    (h : Hr.face.SameCycle x y) : G.face.SameCycle (hr x) (hr y) := by
  obtain ⟨n, rfl⟩ := exists_nat_pow_apply_eq h
  clear h
  induction n with
  | zero => simpa using SameCycle.refl G.face (hr x)
  | succ n ih =>
      have hstep : (Hr.face ^ (n + 1)) x = Hr.face ((Hr.face ^ n) x) := by
        rw [pow_succ', Perm.mul_apply]
      rw [hstep]
      exact ih.trans (P.sameCycle_face_r_step _)

end Patch

/-- **Sitting over a remainder dart.**  The `G`-dart `x` lies over `wr` when it
is `hr wr` itself, or when it lies in the disk on the face of the border dart
matching `hr wr`.

This is the invariant that runs the `G`-face walk: one face step of `G` moves
it from `wr` to `wr` or to `Hr.face wr`, and never anywhere else. -/
def Patch.Over (Hd : Hypermap Dd) (hd : Dd → Dg) (hr : Dr → Dg) (bd : Set Dd)
    (x : Dg) (wr : Dr) : Prop :=
  x = hr wr ∨
    ∃ ud ∈ bd, hd ud = hr wr ∧ ∃ xd : Dd, x = hd xd ∧ Hd.face.SameCycle xd ud

namespace Patch

variable {G : Hypermap Dg} {Hd : Hypermap Dd} {Hr : Hypermap Dr}
  {hd : Dd → Dg} {hr : Dr → Dg} {bd : Set Dd} {br : Set Dr}

omit [Fintype Dg] [DecidableEq Dg] [Fintype Dr] [DecidableEq Dr] in
theorem over_self (Hd : Hypermap Dd) (hd : Dd → Dg) (hr : Dr → Dg) (bd : Set Dd)
    (wr : Dr) : Over Hd hd hr bd (hr wr) wr := Or.inl rfl

/-- One `G`-face step out of a remainder dart lands over its remainder face
successor — inside the remainder if the ring is not in the way, in the disk if
it is. -/
theorem over_face_hr (P : Patch G Hd Hr hd hr bd br) (wr : Dr) :
    Over Hd hd hr bd (G.face (hr wr)) (Hr.face wr) := by
  by_cases hx : Hr.face wr ∈ br
  · obtain ⟨ud, hud, hu⟩ := P.exists_bd_of_br hx
    exact Or.inr ⟨ud, hud, hu, Hd.face ud, P.face_step_ring hu, (sameCycle_apply' _ _).symm⟩
  · exact Or.inl (P.face_r hx).symm

/-- **The walk invariant.**  A `G`-face step carries `Over _ wr` to `Over _ wr`
or to `Over _ (Hr.face wr)`. -/
theorem Over.face_step (P : Patch G Hd Hr hd hr bd br) {x : Dg} {wr : Dr}
    (h : Over Hd hd hr bd x wr) :
    Over Hd hd hr bd (G.face x) wr ∨ Over Hd hd hr bd (G.face x) (Hr.face wr) := by
  rcases h with rfl | ⟨ud, hud, hu, xd, rfl, hcyc⟩
  · exact Or.inr (P.over_face_hr wr)
  by_cases hxd : xd ∈ bd
  · have hxu : xd = ud := P.simple_d xd hxd ud hud hcyc
    subst hxu
    rw [hu]
    exact Or.inr (P.over_face_hr wr)
  · refine Or.inl (Or.inr ⟨ud, hud, hu, Hd.face xd, (P.face_d hxd).symm, ?_⟩)
    exact (sameCycle_apply' Hd.face xd).symm.trans hcyc

/-- Iterating the walk invariant: after any number of `G`-face steps the dart
still sits over a remainder dart on the same remainder face. -/
theorem Over.face_iter (P : Patch G Hd Hr hd hr bd br) {x : Dg} {wr : Dr}
    (h : Over Hd hd hr bd x wr) (n : ℕ) :
    ∃ wr' : Dr, Hr.face.SameCycle wr wr' ∧ Over Hd hd hr bd ((G.face ^ n) x) wr' := by
  induction n with
  | zero => exact ⟨wr, SameCycle.refl _ _, by simpa using h⟩
  | succ n ih =>
      obtain ⟨wr', hcyc, hover⟩ := ih
      have hstep : (G.face ^ (n + 1)) x = G.face ((G.face ^ n) x) := by
        rw [pow_succ', Perm.mul_apply]
      rw [hstep]
      rcases hover.face_step P with h' | h'
      · exact ⟨wr', hcyc, h'⟩
      · exact ⟨Hr.face wr', hcyc.trans (sameCycle_apply' _ _), h'⟩

/-- A remainder dart sits over only itself. -/
theorem eq_of_over_hr (P : Patch G Hd Hr hd hr bd br) {yr wr : Dr}
    (h : Over Hd hd hr bd (hr yr) wr) : yr = wr := by
  rcases h with h | ⟨ud, hud, hu, xd, hx, hcyc⟩
  · exact P.injr h
  · have hxd : xd ∈ bd := P.mem_bd_of_eq hx.symm
    have : xd = ud := P.simple_d xd hxd ud hud hcyc
    subst this
    exact P.injr (hx.trans hu)

/-- **The remainder embedding reflects the face relation.**  Two remainder
darts share a `G`-face exactly when they share a remainder face: the `G`-face
walk through the disk always returns to the ring where it left it. -/
theorem sameCycle_face_r (P : Patch G Hd Hr hd hr bd br) (xr yr : Dr) :
    Hr.face.SameCycle xr yr ↔ G.face.SameCycle (hr xr) (hr yr) := by
  refine ⟨fun h => P.sameCycle_face_r_of h, fun h => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_pow_apply_eq h
  obtain ⟨wr', hcyc, hover⟩ :=
    (over_self Hd hd hr bd xr).face_iter (P := P) n
  rw [hn] at hover
  rw [P.eq_of_over_hr hover]
  exact hcyc

/-! ## Two pieces of generic bookkeeping

Both are about the complement of an invariant region, and about a region that
is a single class; neither mentions a patch. -/

section Generic

variable {D : Type*} [Fintype D]

/-- The complement of an invariant set is invariant: on a finite carrier a
permutation that maps a set into itself maps it onto itself. -/
theorem invariant_compl {σ : Perm D} {S : Set D} (hS : ∀ x ∈ S, σ x ∈ S) :
    ∀ x ∈ Sᶜ, σ x ∈ Sᶜ :=
  fun x hx => (saturated_sameCycle_of_invariant hS).compl (sameCycle_apply' σ x) hx

/-- The same for a family of generators. -/
theorem word_invariant_compl {L : List (Perm D)} {S : Set D}
    (hS : ∀ g ∈ L, ∀ x ∈ S, g x ∈ S) : ∀ g ∈ L, ∀ x ∈ Sᶜ, g x ∈ Sᶜ :=
  fun _ hg x hx =>
    (saturated_wordReachable_of_invariant hS).compl (wordReachable_step hg x) hx

omit [Fintype D] in
/-- A region that is exactly one class contributes one to the count. -/
theorem classCountOn_eq_one {s : Setoid D} {S : Set D} {x₀ : D} (hx₀ : x₀ ∈ S)
    (h : ∀ y, y ∈ S ↔ s x₀ y) : classCountOn s S = 1 := by
  have hcl : classesOn s S = {Quotient.mk s x₀} := by
    ext q
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Quotient.sound ((h y).1 hy)).symm
    · rintro rfl
      exact ⟨x₀, hx₀, rfl⟩
  rw [classCountOn, hcl, Set.ncard_singleton]

omit [Fintype D] in
theorem classCountOn_empty (s : Setoid D) : classCountOn s (∅ : Set D) = 0 := by
  rw [classCountOn, classesOn, Set.image_empty, Set.ncard_empty]

end Generic

/-! ## The face band of the disk, and the outer region of `G` -/

/-- The disk darts whose face meets the border. -/
def faceBand (Hd : Hypermap Dd) (bd : Set Dd) : Set Dd :=
  {x | ∃ u ∈ bd, Hd.face.SameCycle x u}

/-- The `G`-darts sitting over some remainder dart: the union of the `G`-faces
that meet the remainder's image. -/
def faceOuter (Hd : Hypermap Dd) (hd : Dd → Dg) (hr : Dr → Dg) (bd : Set Dd) : Set Dg :=
  {x | ∃ wr : Dr, Over Hd hd hr bd x wr}

omit [Fintype Dg] [DecidableEq Dg] [Fintype Dr] [DecidableEq Dr] in
theorem bd_subset_faceBand (Hd : Hypermap Dd) (bd : Set Dd) : bd ⊆ faceBand Hd bd :=
  fun x hx => ⟨x, hx, SameCycle.refl _ _⟩

omit [Fintype Dg] [DecidableEq Dg] [Fintype Dr] [DecidableEq Dr] in
theorem faceBand_invariant (Hd : Hypermap Dd) (bd : Set Dd) :
    ∀ x ∈ faceBand Hd bd, Hd.face x ∈ faceBand Hd bd := by
  rintro x ⟨u, hu, hcyc⟩
  exact ⟨u, hu, (sameCycle_apply' Hd.face x).symm.trans hcyc⟩

omit [Fintype Dg] [DecidableEq Dg] [Fintype Dr] [DecidableEq Dr] in
theorem range_hr_subset_faceOuter (Hd : Hypermap Dd) (hd : Dd → Dg) (hr : Dr → Dg)
    (bd : Set Dd) : Set.range hr ⊆ faceOuter Hd hd hr bd := by
  rintro _ ⟨y, rfl⟩
  exact ⟨y, Or.inl rfl⟩

theorem faceOuter_invariant (P : Patch G Hd Hr hd hr bd br) :
    ∀ x ∈ faceOuter Hd hd hr bd, G.face x ∈ faceOuter Hd hd hr bd := by
  rintro x ⟨wr, hover⟩
  rcases hover.face_step P with h | h
  · exact ⟨wr, h⟩
  · exact ⟨Hr.face wr, h⟩

theorem mem_range_hd_of_not_faceOuter (P : Patch G Hd Hr hd hr bd br) {x : Dg}
    (hx : x ∉ faceOuter Hd hd hr bd) : x ∈ Set.range hd := by
  rcases P.mem_range_or x with h | h
  · exact h
  · exact absurd (range_hr_subset_faceOuter Hd hd hr bd h) hx

/-- A disk dart is in the outer region exactly when its face meets the border. -/
theorem mem_faceOuter_hd_iff (P : Patch G Hd Hr hd hr bd br) (xd : Dd) :
    hd xd ∈ faceOuter Hd hd hr bd ↔ xd ∈ faceBand Hd bd := by
  constructor
  · rintro ⟨wr, h | ⟨ud, hud, hu, xd', hxd', hcyc⟩⟩
    · exact bd_subset_faceBand Hd bd (P.mem_bd_of_eq h)
    · exact ⟨ud, hud, (P.injd hxd') ▸ hcyc⟩
  · rintro ⟨u, hu, hcyc⟩
    obtain ⟨wr, _, hwr⟩ := P.exists_br_of_bd hu
    exact ⟨wr, Or.inr ⟨u, hu, hwr.symm, xd, rfl, hcyc⟩⟩

theorem preimage_faceOuter (P : Patch G Hd Hr hd hr bd br) :
    hd ⁻¹' faceOuter Hd hd hr bd = faceBand Hd bd := by
  ext xd
  exact P.mem_faceOuter_hd_iff xd

/-- Every dart of the outer region shares its `G`-face with a remainder dart. -/
theorem sameCycle_hr_of_mem_faceOuter (P : Patch G Hd Hr hd hr bd br) {x : Dg}
    (hx : x ∈ faceOuter Hd hd hr bd) : ∃ wr : Dr, G.face.SameCycle x (hr wr) := by
  obtain ⟨wr, h | ⟨ud, _, hu, xd, rfl, hcyc⟩⟩ := hx
  · exact ⟨wr, h ▸ SameCycle.refl _ _⟩
  · exact ⟨wr, hu ▸ P.sameCycle_face_d hcyc⟩

/-! ## The face count -/

/-- **The outer region has one `G`-face per remainder face.**  Tool B, with the
functor law supplied by `sameCycle_face_r`: `hr` is not equivariant at the
ring, but it still reflects and preserves the face relation. -/
theorem orbitCountOn_face_outer (P : Patch G Hd Hr hd hr bd br) :
    orbitCountOn G.face (faceOuter Hd hd hr bd) = orbitCount Hr.face := by
  have hpre : hr ⁻¹' faceOuter Hd hd hr bd = (Set.univ : Set Dr) := by
    ext y
    exact iff_of_true (range_hr_subset_faceOuter Hd hd hr bd ⟨y, rfl⟩) (Set.mem_univ y)
  have hmain := classCountOn_preimage (s := SameCycle.setoid G.face)
    (s' := SameCycle.setoid Hr.face) (h := hr) (S := faceOuter Hd hd hr bd)
    (saturated_sameCycle_of_invariant P.faceOuter_invariant)
    (fun _ hx => P.sameCycle_hr_of_mem_faceOuter hx)
    (fun x y _ => P.sameCycle_face_r x y)
  rw [orbitCountOn, hmain, hpre, classCountOn_univ, orbitCount, Nat.card_eq_fintype_card]

/-- **Off the outer region the disk is `G`.**  Tool B in its strict form: away
from the band `hd` is a genuine face morphism. -/
theorem orbitCountOn_face_outer_compl (P : Patch G Hd Hr hd hr bd br) :
    orbitCountOn G.face (faceOuter Hd hd hr bd)ᶜ = orbitCountOn Hd.face (faceBand Hd bd)ᶜ := by
  have hmain := orbitCountOn_eq_orbitCountOn_of_equivariantOn
    (σ := G.face) (σ' := Hd.face) (h := hd) (S := (faceOuter Hd hd hr bd)ᶜ)
    (invariant_compl P.faceOuter_invariant) P.injd.injOn
    (fun y hy => P.face_d (fun hcon =>
      hy ((P.mem_faceOuter_hd_iff y).2 (bd_subset_faceBand Hd bd hcon))))
    (fun x hx => ⟨(P.mem_range_hd_of_not_faceOuter hx).choose,
      by rw [(P.mem_range_hd_of_not_faceOuter hx).choose_spec]⟩)
  rw [hmain, Set.preimage_compl, P.preimage_faceOuter]

/-- **The disk's faces through the border are counted by the border.**  This is
the simplicity of the border, and nothing else: the inclusion of the border
enumerates the band's faces without repetition. -/
theorem orbitCountOn_face_band (P : Patch G Hd Hr hd hr bd br) :
    orbitCountOn Hd.face (faceBand Hd bd) = bd.ncard := by
  have hmain := classCountOn_eq_card_of_section (s := SameCycle.setoid Hd.face)
    (S := faceBand Hd bd) (A := {x : Dd // x ∈ bd}) (fun a => (a : Dd))
    (saturated_sameCycle_of_invariant (faceBand_invariant Hd bd))
    (fun a => bd_subset_faceBand Hd bd a.2)
    (fun x hx => by
      obtain ⟨u, hu, hcyc⟩ := hx
      exact ⟨⟨u, hu⟩, hcyc⟩)
    (fun a b => ⟨fun h => Subtype.ext (P.simple_d a a.2 b b.2 h),
      fun h => h ▸ SameCycle.refl _ _⟩)
  rw [orbitCountOn, hmain, Nat.card_coe_set_eq]

/-- **The face identity.**  The ring's darts are exactly the disk faces that
the gluing absorbs. -/
theorem orbitCount_face_add (P : Patch G Hd Hr hd hr bd br) :
    orbitCount Hd.face + orbitCount Hr.face = bd.ncard + orbitCount G.face := by
  have hd' := orbitCount_eq_orbitCountOn_add_compl Hd.face (faceBand_invariant Hd bd)
  have hg := orbitCount_eq_orbitCountOn_add_compl G.face P.faceOuter_invariant
  rw [P.orbitCountOn_face_band] at hd'
  rw [P.orbitCountOn_face_outer, P.orbitCountOn_face_outer_compl] at hg
  omega

/-! ## The edge and node counts

These need no walk analysis: each embedding is a genuine morphism for the
permutation the *other* side uses to present the border. -/

theorem orbitCountOn_edge_range_r (P : Patch G Hd Hr hd hr bd br) :
    orbitCountOn G.edge (Set.range hr) = orbitCount Hr.edge :=
  orbitCountOn_eq_orbitCount_of_equivariantOn
    (fun x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨Hr.edge y, P.edge_r y⟩)
    (fun y => ⟨y, rfl⟩) P.injr P.edge_r
    (fun x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨y, SameCycle.refl _ _⟩)

theorem orbitCountOn_edge_range_r_compl (P : Patch G Hd Hr hd hr bd br) :
    orbitCountOn G.edge (Set.range hr)ᶜ = orbitCountOn Hd.edge bdᶜ := by
  have hinv : ∀ x ∈ Set.range hr, G.edge x ∈ Set.range hr := fun x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨Hr.edge y, P.edge_r y⟩
  have hmain := orbitCountOn_eq_orbitCountOn_of_equivariantOn
    (σ := G.edge) (σ' := Hd.edge) (h := hd) (S := (Set.range hr)ᶜ)
    (invariant_compl hinv) P.injd.injOn
    (fun y hy => P.edge_d y (fun hcon => hy (P.ring_subset_range_r ⟨y, hcon, rfl⟩)))
    (fun x hx => by
      rcases P.mem_range_or x with ⟨y, rfl⟩ | h
      · exact ⟨y, SameCycle.refl _ _⟩
      · exact absurd h hx)
  rw [hmain]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_compl_iff]
  exact not_congr (P.mem_bd_iff y)

theorem orbitCountOn_node_range_d (P : Patch G Hd Hr hd hr bd br) :
    orbitCountOn G.node (Set.range hd) = orbitCount Hd.node :=
  orbitCountOn_eq_orbitCount_of_equivariantOn
    (fun x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨Hd.node y, P.node_d y⟩)
    (fun y => ⟨y, rfl⟩) P.injd P.node_d
    (fun x hx => by
      obtain ⟨y, rfl⟩ := hx
      exact ⟨y, SameCycle.refl _ _⟩)

theorem orbitCountOn_node_range_d_compl (P : Patch G Hd Hr hd hr bd br) :
    orbitCountOn G.node (Set.range hd)ᶜ = orbitCountOn Hr.node brᶜ := by
  have hinv : ∀ x ∈ Set.range hd, G.node x ∈ Set.range hd := fun x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨Hd.node y, P.node_d y⟩
  have hmain := orbitCountOn_eq_orbitCountOn_of_equivariantOn
    (σ := G.node) (σ' := Hr.node) (h := hr) (S := (Set.range hd)ᶜ)
    (invariant_compl hinv) P.injr.injOn
    (fun y hy => P.node_r y (fun hcon => hy ((P.mem_br_iff y).2 hcon)))
    (fun x hx => by
      rcases P.mem_range_or x with h | ⟨y, rfl⟩
      · exact absurd h hx
      · exact ⟨y, SameCycle.refl _ _⟩)
  rw [hmain]
  congr 1
  ext y
  simp only [Set.mem_preimage, Set.mem_compl_iff]
  exact not_congr (P.mem_br_iff y)

/-! ## The border contributes exactly one orbit to each side -/

open scoped Classical in
/-- The number of border orbits the gluing absorbs: one for a genuine ring,
none for an empty one. -/
noncomputable def borderMult (bd : Set Dd) : ℕ := if bd.Nonempty then 1 else 0

omit [Fintype Dd] [DecidableEq Dd] in
open scoped Classical in
theorem borderMult_pos (h : bd.Nonempty) : borderMult bd = 1 := if_pos h

omit [Fintype Dd] [DecidableEq Dd] in
open scoped Classical in
theorem borderMult_empty (h : ¬ bd.Nonempty) : borderMult bd = 0 := if_neg h

theorem orbitCountOn_edge_bd (P : Patch G Hd Hr hd hr bd br) :
    orbitCountOn Hd.edge bd = borderMult bd := by
  by_cases h : bd.Nonempty
  · obtain ⟨x₀, hx₀⟩ := h
    rw [borderMult_pos ⟨x₀, hx₀⟩]
    exact classCountOn_eq_one hx₀ (fun y => (P.edgeCycle_d x₀ y hx₀).symm)
  · rw [borderMult_empty h, Set.not_nonempty_iff_eq_empty.1 h]
    exact classCountOn_empty _

theorem br_nonempty_iff (P : Patch G Hd Hr hd hr bd br) : br.Nonempty ↔ bd.Nonempty := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨ud, hud, _⟩ := P.exists_bd_of_br hx
    exact ⟨ud, hud⟩
  · rintro ⟨x, hx⟩
    obtain ⟨wr, hwr, _⟩ := P.exists_br_of_bd hx
    exact ⟨wr, hwr⟩

theorem orbitCountOn_node_br (P : Patch G Hd Hr hd hr bd br) :
    orbitCountOn Hr.node br = borderMult bd := by
  by_cases h : bd.Nonempty
  · obtain ⟨x₀, hx₀⟩ := P.br_nonempty_iff.2 h
    rw [borderMult_pos h]
    exact classCountOn_eq_one hx₀ (fun y => (P.nodeCycle_r x₀ y hx₀).symm)
  · rw [borderMult_empty h, Set.not_nonempty_iff_eq_empty.1
      (fun hcon => h (P.br_nonempty_iff.1 hcon))]
    exact classCountOn_empty _

/-- **The edge identity.** -/
theorem orbitCount_edge_add (P : Patch G Hd Hr hd hr bd br) :
    orbitCount Hd.edge + orbitCount Hr.edge = borderMult bd + orbitCount G.edge := by
  have hinvr : ∀ x ∈ Set.range hr, G.edge x ∈ Set.range hr := fun x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨Hr.edge y, P.edge_r y⟩
  have hd' := orbitCount_eq_orbitCountOn_add_compl Hd.edge
    (fun x hx => (P.mem_bd_edge_iff x).2 hx)
  have hg := orbitCount_eq_orbitCountOn_add_compl G.edge hinvr
  rw [P.orbitCountOn_edge_bd] at hd'
  rw [P.orbitCountOn_edge_range_r, P.orbitCountOn_edge_range_r_compl] at hg
  omega

/-- **The node identity.** -/
theorem orbitCount_node_add (P : Patch G Hd Hr hd hr bd br) :
    orbitCount Hd.node + orbitCount Hr.node = borderMult bd + orbitCount G.node := by
  have hinvd : ∀ x ∈ Set.range hd, G.node x ∈ Set.range hd := fun x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨Hd.node y, P.node_d y⟩
  have hr' := orbitCount_eq_orbitCountOn_add_compl Hr.node
    (fun x hx => (P.mem_br_node_iff x).2 hx)
  have hg := orbitCount_eq_orbitCountOn_add_compl G.node hinvd
  rw [P.orbitCountOn_node_br] at hr'
  rw [P.orbitCountOn_node_range_d, P.orbitCountOn_node_range_d_compl] at hg
  omega

/-! ## The dart count -/

/-- **The dart identity.**  The two sides cover `G` and overlap exactly on the
ring, so they have `#G` darts between them with the ring counted twice. -/
theorem card_patch (P : Patch G Hd Hr hd hr bd br) :
    Fintype.card Dd + Fintype.card Dr = bd.ncard + Fintype.card Dg := by
  have hu : Set.range hd ∪ Set.range hr = (Set.univ : Set Dg) := by
    ext x
    exact iff_of_true (P.mem_range_or x) (Set.mem_univ x)
  have hkey := Set.ncard_union_add_ncard_inter (Set.range hd) (Set.range hr)
    (Set.toFinite _) (Set.toFinite _)
  rw [hu, P.range_inter, Set.ncard_univ, Set.ncard_range_of_injective P.injd,
    Set.ncard_range_of_injective P.injr,
    Set.ncard_image_of_injective bd P.injd] at hkey
  simp only [Nat.card_eq_fintype_card] at hkey
  omega

/-! ## Connectivity

The component count is the only remaining identity, and it needs the same two
things the face count did: that each embedding carries connectivity forward,
and that each reflects it where the other side is out of reach. -/

section Gens

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem mem_gens_edge (H : Hypermap D) : H.edge ∈ [H.edge, H.node, H.face] :=
  List.mem_cons_self

theorem mem_gens_node (H : Hypermap D) : H.node ∈ [H.edge, H.node, H.face] :=
  List.mem_cons_of_mem _ List.mem_cons_self

theorem mem_gens_face (H : Hypermap D) : H.face ∈ [H.edge, H.node, H.face] :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

omit [DecidableEq D] in
/-- A cycle of one generator is a walk of the family. -/
theorem wordReachable_of_sameCycle {L : List (Perm D)} {g : Perm D} (hg : g ∈ L)
    {x y : D} (h : g.SameCycle x y) : WordReachable L x y := by
  obtain ⟨n, rfl⟩ := exists_nat_pow_apply_eq h
  exact wordReachable_pow hg x n

end Gens

/-- **The disk embedding carries connectivity forward**, one generator at a
time.  The edge step is the only one that needs an argument: the composite law
turns it into a face step followed by a node step. -/
theorem wordReachable_hd_step (P : Patch G Hd Hr hd hr bd br) (xd : Dd) {g : Perm Dd}
    (hg : g ∈ [Hd.edge, Hd.node, Hd.face]) :
    WordReachable [G.edge, G.node, G.face] (hd xd) (hd (g xd)) := by
  rcases List.mem_cons.mp hg with rfl | hg1
  · -- the edge step
    have hback : hd xd = G.node (hd (Hd.face (Hd.edge xd))) := by
      conv_lhs => rw [← Hd.cancel3 xd]
      rw [P.node_d]
    have h1 : WordReachable [G.edge, G.node, G.face] (hd (Hd.edge xd))
        (hd (Hd.face (Hd.edge xd))) :=
      wordReachable_of_sameCycle (mem_gens_face G) (P.sameCycle_face_d_step _)
    have h2 : WordReachable [G.edge, G.node, G.face] (hd (Hd.face (Hd.edge xd))) (hd xd) := by
      rw [hback]
      exact wordReachable_step (mem_gens_node G) _
    exact (h1.trans h2).symm
  rcases List.mem_cons.mp hg1 with rfl | hg2
  · rw [P.node_d]
    exact wordReachable_step (mem_gens_node G) _
  rcases List.mem_cons.mp hg2 with rfl | hg3
  · exact wordReachable_of_sameCycle (mem_gens_face G) (P.sameCycle_face_d_step _)
  · simp at hg3

theorem wordReachable_hd (P : Patch G Hd Hr hd hr bd br) {xd yd : Dd}
    (h : WordReachable [Hd.edge, Hd.node, Hd.face] xd yd) :
    WordReachable [G.edge, G.node, G.face] (hd xd) (hd yd) := by
  induction h with
  | refl => exact WordReachable.refl _ _
  | tail _ hstep ih =>
      obtain ⟨g, hg, rfl⟩ := hstep
      exact ih.trans (P.wordReachable_hd_step _ hg)

/-- **The remainder embedding carries connectivity forward.**  Here it is the
node step that the composite law has to reconstruct. -/
theorem wordReachable_hr_step (P : Patch G Hd Hr hd hr bd br) (xr : Dr) {g : Perm Dr}
    (hg : g ∈ [Hr.edge, Hr.node, Hr.face]) :
    WordReachable [G.edge, G.node, G.face] (hr xr) (hr (g xr)) := by
  rcases List.mem_cons.mp hg with rfl | hg1
  · rw [P.edge_r]
    exact wordReachable_step (mem_gens_edge G) _
  rcases List.mem_cons.mp hg1 with rfl | hg2
  · -- the node step
    have hback : Hr.face (Hr.edge (Hr.node xr)) = xr := Hr.face_edge_node xr
    have h1 : WordReachable [G.edge, G.node, G.face] (hr (Hr.node xr))
        (hr (Hr.edge (Hr.node xr))) := by
      rw [P.edge_r]
      exact wordReachable_step (mem_gens_edge G) _
    have h2 : WordReachable [G.edge, G.node, G.face] (hr (Hr.edge (Hr.node xr))) (hr xr) := by
      have := P.sameCycle_face_r_step (Hr.edge (Hr.node xr))
      rw [hback] at this
      exact wordReachable_of_sameCycle (mem_gens_face G) this
    exact (h1.trans h2).symm
  rcases List.mem_cons.mp hg2 with rfl | hg3
  · exact wordReachable_of_sameCycle (mem_gens_face G) (P.sameCycle_face_r_step _)
  · simp at hg3

theorem wordReachable_hr (P : Patch G Hd Hr hd hr bd br) {xr yr : Dr}
    (h : WordReachable [Hr.edge, Hr.node, Hr.face] xr yr) :
    WordReachable [G.edge, G.node, G.face] (hr xr) (hr yr) := by
  induction h with
  | refl => exact WordReachable.refl _ _
  | tail _ hstep ih =>
      obtain ⟨g, hg, rfl⟩ := hstep
      exact ih.trans (P.wordReachable_hr_step _ hg)

/-- Any two border darts of the disk are connected in the disk. -/
theorem wordReachable_bd (P : Patch G Hd Hr hd hr bd br) {u v : Dd} (hu : u ∈ bd)
    (hv : v ∈ bd) : WordReachable [Hd.edge, Hd.node, Hd.face] u v :=
  wordReachable_of_sameCycle (mem_gens_edge Hd) ((P.edgeCycle_d u v hu).2 hv)

/-- Any two border darts of the remainder are connected in the remainder. -/
theorem wordReachable_br (P : Patch G Hd Hr hd hr bd br) {u v : Dr} (hu : u ∈ br)
    (hv : v ∈ br) : WordReachable [Hr.edge, Hr.node, Hr.face] u v :=
  wordReachable_of_sameCycle (mem_gens_node Hr) ((P.nodeCycle_r u v hu).2 hv)

/-- The `G`-darts connected to the remainder's image. -/
def compOuter (G : Hypermap Dg) (hr : Dr → Dg) : Set Dg :=
  {x | ∃ wr : Dr, WordReachable [G.edge, G.node, G.face] x (hr wr)}

omit [Fintype Dr] [DecidableEq Dr] in
theorem range_hr_subset_compOuter (G : Hypermap Dg) (hr : Dr → Dg) :
    Set.range hr ⊆ compOuter G hr := by
  rintro _ ⟨y, rfl⟩
  exact ⟨y, WordReachable.refl _ _⟩

omit [Fintype Dr] [DecidableEq Dr] in
theorem compOuter_invariant (G : Hypermap Dg) (hr : Dr → Dg) :
    ∀ g ∈ [G.edge, G.node, G.face], ∀ x ∈ compOuter G hr, g x ∈ compOuter G hr := by
  rintro g hg x ⟨wr, hwr⟩
  exact ⟨wr, (wordReachable_step hg x).symm.trans hwr⟩

theorem mem_range_hd_of_not_compOuter (P : Patch G Hd Hr hd hr bd br) {x : Dg}
    (hx : x ∉ compOuter G hr) : x ∈ Set.range hd := by
  rcases P.mem_range_or x with h | h
  · exact h
  · exact absurd (range_hr_subset_compOuter G hr h) hx

/-- **Out of reach of the remainder, the disk is `G`.**  A `G`-walk starting at
a disk dart that cannot reach the remainder never leaves the disk's image, and
never meets a point where `hd` fails to be a morphism. -/
theorem wordReachable_hd_iff (P : Patch G Hd Hr hd hr bd br) {xd : Dd}
    (hx : hd xd ∉ compOuter G hr) (yd : Dd) :
    WordReachable [Hd.edge, Hd.node, Hd.face] xd yd ↔
      WordReachable [G.edge, G.node, G.face] (hd xd) (hd yd) := by
  refine ⟨fun h => P.wordReachable_hd h, fun h => ?_⟩
  have key : ∀ u : Dg, WordReachable [G.edge, G.node, G.face] (hd xd) u →
      ∃ zd : Dd, u = hd zd ∧ WordReachable [Hd.edge, Hd.node, Hd.face] xd zd := by
    intro u hu
    induction hu with
    | refl => exact ⟨xd, rfl, WordReachable.refl _ _⟩
    | tail huv hstep ih =>
        obtain ⟨zd, rfl, hzd⟩ := ih
        obtain ⟨g, hg, rfl⟩ := hstep
        have hzout : hd zd ∉ compOuter G hr := by
          rintro ⟨wr, hwr⟩
          exact hx ⟨wr, huv.trans hwr⟩
        have hzb : zd ∉ bd := fun hcon =>
          hzout (range_hr_subset_compOuter G hr (P.ring_subset_range_r ⟨zd, hcon, rfl⟩))
        rcases List.mem_cons.mp hg with rfl | hg1
        · exact ⟨Hd.edge zd, (P.edge_d zd hzb).symm,
            hzd.trans (wordReachable_step (mem_gens_edge Hd) zd)⟩
        rcases List.mem_cons.mp hg1 with rfl | hg2
        · exact ⟨Hd.node zd, (P.node_d zd).symm,
            hzd.trans (wordReachable_step (mem_gens_node Hd) zd)⟩
        rcases List.mem_cons.mp hg2 with rfl | hg3
        · exact ⟨Hd.face zd, (P.face_d hzb).symm,
            hzd.trans (wordReachable_step (mem_gens_face Hd) zd)⟩
        · simp at hg3
  obtain ⟨zd, hzd, hwalk⟩ := key _ h
  exact (P.injd hzd) ▸ hwalk

/-- **The remainder reflects connectivity.**  A `G`-walk between remainder
darts can cross into the disk, but only through the ring, and the ring is one
`Hr`-component's worth of darts — so the walk is a remainder walk. -/
theorem wordReachable_hr_reflect (P : Patch G Hd Hr hd hr bd br) {xr yr : Dr}
    (h : WordReachable [G.edge, G.node, G.face] (hr xr) (hr yr)) :
    WordReachable [Hr.edge, Hr.node, Hr.face] xr yr := by
  -- the invariant region: remainder darts connected to `xr`, plus the disk
  -- faces hanging off a ring dart that is
  have hB : ∀ g ∈ [G.edge, G.node, G.face],
      ∀ x ∈ {x : Dg | (∃ wr : Dr, hr wr = x ∧ WordReachable [Hr.edge, Hr.node, Hr.face] wr xr)
        ∨ ((∃ vr ∈ br, WordReachable [Hr.edge, Hr.node, Hr.face] vr xr) ∧
            ∃ xd : Dd, hd xd = x ∧
              ∃ ud ∈ bd, WordReachable [Hd.edge, Hd.node, Hd.face] xd ud)},
      g x ∈ {x : Dg | (∃ wr : Dr, hr wr = x ∧ WordReachable [Hr.edge, Hr.node, Hr.face] wr xr)
        ∨ ((∃ vr ∈ br, WordReachable [Hr.edge, Hr.node, Hr.face] vr xr) ∧
            ∃ xd : Dd, hd xd = x ∧
              ∃ ud ∈ bd, WordReachable [Hd.edge, Hd.node, Hd.face] xd ud)} := by
    -- the remainder half of the step analysis, done once
    have hstepr : ∀ g ∈ [G.edge, G.node, G.face], ∀ wr : Dr,
        WordReachable [Hr.edge, Hr.node, Hr.face] wr xr →
        (∃ vr : Dr, hr vr = g (hr wr) ∧ WordReachable [Hr.edge, Hr.node, Hr.face] vr xr)
          ∨ ((∃ vr ∈ br, WordReachable [Hr.edge, Hr.node, Hr.face] vr xr) ∧
              ∃ xd : Dd, hd xd = g (hr wr) ∧
                ∃ ud ∈ bd, WordReachable [Hd.edge, Hd.node, Hd.face] xd ud) := by
      intro g hg wr hwr
      rcases List.mem_cons.mp hg with rfl | hg1
      · exact Or.inl ⟨Hr.edge wr, P.edge_r wr,
          (wordReachable_step (mem_gens_edge Hr) wr).symm.trans hwr⟩
      rcases List.mem_cons.mp hg1 with rfl | hg2
      · by_cases hb : wr ∈ br
        · obtain ⟨ud, hud, hu⟩ := P.exists_bd_of_br hb
          refine Or.inr ⟨⟨wr, hb, hwr⟩, Hd.node ud, ?_, ud, hud,
            (wordReachable_step (mem_gens_node Hd) ud).symm⟩
          rw [P.node_d, hu]
        · exact Or.inl ⟨Hr.node wr, P.node_r wr hb,
            (wordReachable_step (mem_gens_node Hr) wr).symm.trans hwr⟩
      rcases List.mem_cons.mp hg2 with rfl | hg3
      · by_cases hb : Hr.face wr ∈ br
        · obtain ⟨ud, hud, hu⟩ := P.exists_bd_of_br hb
          refine Or.inr ⟨⟨Hr.face wr, hb,
            (wordReachable_step (mem_gens_face Hr) wr).symm.trans hwr⟩,
            Hd.face ud, (P.face_step_ring hu).symm, ud, hud,
            (wordReachable_step (mem_gens_face Hd) ud).symm⟩
        · exact Or.inl ⟨Hr.face wr, P.face_r hb,
            (wordReachable_step (mem_gens_face Hr) wr).symm.trans hwr⟩
      · simp at hg3
    rintro g hg x (⟨wr, rfl, hwr⟩ | ⟨⟨vr, hvr, hvx⟩, xd, rfl, ud, hud, hwalk⟩)
    · exact hstepr g hg wr hwr
    by_cases hb : xd ∈ bd
    · obtain ⟨wr, hwrb, hwr⟩ := P.exists_br_of_bd hb
      rw [← hwr]
      exact hstepr g hg wr ((P.wordReachable_br hwrb hvr).trans hvx)
    · refine Or.inr ⟨⟨vr, hvr, hvx⟩, ?_⟩
      rcases List.mem_cons.mp hg with rfl | hg1
      · exact ⟨Hd.edge xd, P.edge_d xd hb, ud, hud,
          (wordReachable_step (mem_gens_edge Hd) xd).symm.trans hwalk⟩
      rcases List.mem_cons.mp hg1 with rfl | hg2
      · exact ⟨Hd.node xd, P.node_d xd, ud, hud,
          (wordReachable_step (mem_gens_node Hd) xd).symm.trans hwalk⟩
      rcases List.mem_cons.mp hg2 with rfl | hg3
      · exact ⟨Hd.face xd, P.face_d hb, ud, hud,
          (wordReachable_step (mem_gens_face Hd) xd).symm.trans hwalk⟩
      · simp at hg3
  have hsat := saturated_wordReachable_of_invariant hB
  have hstart : hr xr ∈ {x : Dg |
      (∃ wr : Dr, hr wr = x ∧ WordReachable [Hr.edge, Hr.node, Hr.face] wr xr)
        ∨ ((∃ vr ∈ br, WordReachable [Hr.edge, Hr.node, Hr.face] vr xr) ∧
            ∃ xd : Dd, hd xd = x ∧
              ∃ ud ∈ bd, WordReachable [Hd.edge, Hd.node, Hd.face] xd ud)} :=
    Or.inl ⟨xr, rfl, WordReachable.refl _ _⟩
  rcases hsat h hstart with ⟨wr, hwr, hwalk⟩ | ⟨⟨vr, hvr, hvx⟩, xd, hxd, _⟩
  · exact ((P.injr hwr) ▸ hwalk).symm
  · exact ((P.wordReachable_br (P.mem_br_of_eq hxd) hvr).trans hvx).symm

/-! ### The two component counts -/

theorem wordOrbitCountOn_compOuter (P : Patch G Hd Hr hd hr bd br) :
    wordOrbitCountOn [G.edge, G.node, G.face] (compOuter G hr) = compCount Hr := by
  have hpre : hr ⁻¹' compOuter G hr = (Set.univ : Set Dr) := by
    ext y
    exact iff_of_true (range_hr_subset_compOuter G hr ⟨y, rfl⟩) (Set.mem_univ y)
  have hmain := classCountOn_preimage (s := wordSetoid [G.edge, G.node, G.face])
    (s' := wordSetoid [Hr.edge, Hr.node, Hr.face]) (h := hr) (S := compOuter G hr)
    (saturated_wordReachable_of_invariant (compOuter_invariant G hr))
    (fun _ hx => hx)
    (fun x y _ => ⟨fun hxy => P.wordReachable_hr hxy, fun hxy => P.wordReachable_hr_reflect hxy⟩)
  rw [wordOrbitCountOn, hmain, hpre, classCountOn_univ, compCount, wordOrbitCount,
    Nat.card_eq_fintype_card]

theorem wordOrbitCountOn_compOuter_compl (P : Patch G Hd Hr hd hr bd br) :
    wordOrbitCountOn [G.edge, G.node, G.face] (compOuter G hr)ᶜ =
      wordOrbitCountOn [Hd.edge, Hd.node, Hd.face] (hd ⁻¹' (compOuter G hr)ᶜ) :=
  classCountOn_preimage (s := wordSetoid [G.edge, G.node, G.face])
    (s' := wordSetoid [Hd.edge, Hd.node, Hd.face]) (h := hd) (S := (compOuter G hr)ᶜ)
    (saturated_wordReachable_of_invariant (word_invariant_compl (compOuter_invariant G hr)))
    (fun x hx => ⟨(P.mem_range_hd_of_not_compOuter hx).choose, by
      rw [(P.mem_range_hd_of_not_compOuter hx).choose_spec]⟩)
    (fun x _ hx => P.wordReachable_hd_iff hx _)

/-- **The disk attaches to the remainder along exactly the border.**  The disk
darts whose image can reach the remainder are precisely those connected to the
border inside the disk. -/
theorem preimage_compOuter (P : Patch G Hd Hr hd hr bd br) {x₀ : Dd} (hx₀ : x₀ ∈ bd) :
    hd ⁻¹' compOuter G hr = {xd : Dd | WordReachable [Hd.edge, Hd.node, Hd.face] xd x₀} := by
  -- the region: disk darts connected to the border, together with the remainder
  have hAr : ∀ g ∈ [G.edge, G.node, G.face], ∀ wr : Dr,
      g (hr wr) ∈ {x : Dg | (∃ xd : Dd, hd xd = x ∧
        WordReachable [Hd.edge, Hd.node, Hd.face] xd x₀) ∨ x ∈ Set.range hr} := by
    intro g hg wr
    rcases List.mem_cons.mp hg with rfl | hg1
    · exact Or.inr ⟨Hr.edge wr, P.edge_r wr⟩
    rcases List.mem_cons.mp hg1 with rfl | hg2
    · by_cases hb : wr ∈ br
      · obtain ⟨ud, hud, hu⟩ := P.exists_bd_of_br hb
        refine Or.inl ⟨Hd.node ud, by rw [P.node_d, hu], ?_⟩
        exact (wordReachable_step (mem_gens_node Hd) ud).symm.trans (P.wordReachable_bd hud hx₀)
      · exact Or.inr ⟨Hr.node wr, P.node_r wr hb⟩
    rcases List.mem_cons.mp hg2 with rfl | hg3
    · by_cases hb : Hr.face wr ∈ br
      · obtain ⟨ud, hud, hu⟩ := P.exists_bd_of_br hb
        refine Or.inl ⟨Hd.face ud, (P.face_step_ring hu).symm, ?_⟩
        exact (wordReachable_step (mem_gens_face Hd) ud).symm.trans (P.wordReachable_bd hud hx₀)
      · exact Or.inr ⟨Hr.face wr, P.face_r hb⟩
    · simp at hg3
  have hA : ∀ g ∈ [G.edge, G.node, G.face],
      ∀ x ∈ {x : Dg | (∃ xd : Dd, hd xd = x ∧
          WordReachable [Hd.edge, Hd.node, Hd.face] xd x₀) ∨ x ∈ Set.range hr},
      g x ∈ {x : Dg | (∃ xd : Dd, hd xd = x ∧
          WordReachable [Hd.edge, Hd.node, Hd.face] xd x₀) ∨ x ∈ Set.range hr} := by
    rintro g hg x (⟨xd, rfl, hxd⟩ | ⟨wr, rfl⟩)
    · by_cases hb : xd ∈ bd
      · obtain ⟨wr, _, hwr⟩ := P.exists_br_of_bd hb
        rw [← hwr]
        exact hAr g hg wr
      · refine Or.inl ?_
        rcases List.mem_cons.mp hg with rfl | hg1
        · exact ⟨Hd.edge xd, P.edge_d xd hb,
            (wordReachable_step (mem_gens_edge Hd) xd).symm.trans hxd⟩
        rcases List.mem_cons.mp hg1 with rfl | hg2
        · exact ⟨Hd.node xd, P.node_d xd,
            (wordReachable_step (mem_gens_node Hd) xd).symm.trans hxd⟩
        rcases List.mem_cons.mp hg2 with rfl | hg3
        · exact ⟨Hd.face xd, P.face_d hb,
            (wordReachable_step (mem_gens_face Hd) xd).symm.trans hxd⟩
        · simp at hg3
    · exact hAr g hg wr
  have hsat := saturated_wordReachable_of_invariant hA
  ext xd
  constructor
  · rintro ⟨wr, hwr⟩
    rcases hsat hwr.symm (Or.inr ⟨wr, rfl⟩) with ⟨xd', hxd', hwalk⟩ | hmem
    · exact (P.injd hxd') ▸ hwalk
    · exact P.wordReachable_bd ((P.mem_bd_iff xd).1 hmem) hx₀
  · intro hwalk
    obtain ⟨wr, _, hwr⟩ := P.exists_br_of_bd hx₀
    exact ⟨wr, by rw [hwr]; exact P.wordReachable_hd hwalk⟩

theorem preimage_compOuter_of_empty (P : Patch G Hd Hr hd hr bd br) (h : ¬ bd.Nonempty) :
    hd ⁻¹' compOuter G hr = (∅ : Set Dd) := by
  have hbr : ∀ wr : Dr, wr ∉ br := by
    intro wr hwr
    obtain ⟨ud, hud, _⟩ := P.exists_bd_of_br hwr
    exact h ⟨ud, hud⟩
  have hinv : ∀ g ∈ [G.edge, G.node, G.face], ∀ x ∈ Set.range hr, g x ∈ Set.range hr := by
    rintro g hg x ⟨wr, rfl⟩
    rcases List.mem_cons.mp hg with rfl | hg1
    · exact ⟨Hr.edge wr, P.edge_r wr⟩
    rcases List.mem_cons.mp hg1 with rfl | hg2
    · exact ⟨Hr.node wr, P.node_r wr (hbr wr)⟩
    rcases List.mem_cons.mp hg2 with rfl | hg3
    · exact ⟨Hr.face wr, P.face_r (x := wr) (hbr (Hr.face wr))⟩
    · simp at hg3
  have hsat := saturated_wordReachable_of_invariant hinv
  ext xd
  simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
  rintro ⟨wr, hwr⟩
  exact h ⟨xd, (P.mem_bd_iff xd).1 (hsat hwr.symm ⟨wr, rfl⟩)⟩

theorem wordOrbitCountOn_preimage_compOuter (P : Patch G Hd Hr hd hr bd br) :
    wordOrbitCountOn [Hd.edge, Hd.node, Hd.face] (hd ⁻¹' compOuter G hr) = borderMult bd := by
  by_cases h : bd.Nonempty
  · obtain ⟨x₀, hx₀⟩ := h
    rw [borderMult_pos ⟨x₀, hx₀⟩, P.preimage_compOuter hx₀]
    exact classCountOn_eq_one (WordReachable.refl _ _) (fun y => ⟨fun hy => hy.symm, fun hy => hy.symm⟩)
  · rw [borderMult_empty h, P.preimage_compOuter_of_empty h]
    exact classCountOn_empty _

/-- **The component identity.** -/
theorem compCount_add (P : Patch G Hd Hr hd hr bd br) :
    compCount Hd + compCount Hr = borderMult bd + compCount G := by
  have hd' := wordOrbitCount_eq_wordOrbitCountOn_add_compl [Hd.edge, Hd.node, Hd.face]
    (S := hd ⁻¹' compOuter G hr)
    (fun g hg x hx => by
      have := P.wordReachable_hd_step x hg
      exact ⟨hx.choose, this.symm.trans hx.choose_spec⟩)
  have hg := wordOrbitCount_eq_wordOrbitCountOn_add_compl [G.edge, G.node, G.face]
    (compOuter_invariant G hr)
  rw [P.wordOrbitCountOn_preimage_compOuter] at hd'
  rw [P.wordOrbitCountOn_compOuter, P.wordOrbitCountOn_compOuter_compl,
    Set.preimage_compl] at hg
  simp only [compCount] at hd' hg ⊢
  omega

/-! ## Genus additivity -/

/-- **Genus additivity under patching.**  The disk and the remainder carry the
whole genus of the glued map between them, for any ring — empty or not. -/
theorem genus_patch (P : Patch G Hd Hr hd hr bd br) :
    genus G = genus Hd + genus Hr :=
  genus_add_of_orbit_counts (b := borderMult bd) (r := bd.ncard) P.card_patch
    P.orbitCount_edge_add P.orbitCount_node_add P.orbitCount_face_add P.compCount_add

/-- **A patched map is planar exactly when both its pieces are.** -/
theorem planar_patch (P : Patch G Hd Hr hd hr bd br) :
    Planar G ↔ Planar Hd ∧ Planar Hr :=
  planar_of_orbit_counts (b := borderMult bd) (r := bd.ncard) P.card_patch
    P.orbitCount_edge_add P.orbitCount_node_add P.orbitCount_face_add P.compCount_add

/-! ## Bridges

A **bridge** is an edge with the same face on both sides — a dart lying on the
same face as its edge image.  Bridgelessness passes down to the two pieces of a
patch for free.  It passes *up* only under one extra condition on the border,
and the condition is genuinely needed: a face of the glued map can enter the
disk and come out somewhere else along the ring, and an edge of the disk whose
two ends reach the ring at two *non-consecutive* border darts would then be a
bridge of the glued map without being one of either piece.  Forbidding exactly
that is what `Chordless` says.

These names live in the `Patch` namespace rather than at hypermap level, so
that a hypermap-level notion of bridgelessness introduced elsewhere does not
collide with them. -/

section BridgeDefs

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- A hypermap has a bridge at `x` when `x` and `edge x` lie on one face.
`Bridgeless` says it has none. -/
def Bridgeless (H : Hypermap D) : Prop := ∀ x : D, ¬ H.face.SameCycle x (H.edge x)

/-- Two darts whose faces share an edge. -/
def FaceAdj (H : Hypermap D) (x y : D) : Prop :=
  ∃ z : D, H.face.SameCycle x z ∧ H.face.SameCycle (H.edge z) y

end BridgeDefs

/-- **The border has no chords.**  Border darts on edge-sharing faces are
consecutive along the border — the border's own edge cycle being the order in
which its darts run. -/
def Chordless (Hd : Hypermap Dd) (bd : Set Dd) : Prop :=
  ∀ x ∈ bd, ∀ y ∈ bd, FaceAdj Hd x y → y = Hd.edge x ∨ y = Hd.edge.symm x

variable {G : Hypermap Dg} {Hd : Hypermap Dd} {Hr : Hypermap Dr}
  {hd : Dd → Dg} {hr : Dr → Dg} {bd : Set Dd} {br : Set Dr}

/-- The `G`-face successor of an edge image is the disk's own. -/
theorem face_edge_hd (P : Patch G Hd Hr hd hr bd br) (xd : Dd) :
    G.face (G.edge (hd xd)) = hd (Hd.face (Hd.edge xd)) := by
  have h : hd xd = G.node (hd (Hd.face (Hd.edge xd))) := by
    conv_lhs => rw [← Hd.cancel3 xd]
    rw [P.node_d]
  rw [h, G.face_edge_node]

/-- Off the outer region the disk embedding reflects the face relation. -/
theorem sameCycle_face_d_iff (P : Patch G Hd Hr hd hr bd br) {xd : Dd}
    (hx : hd xd ∉ faceOuter Hd hd hr bd) (yd : Dd) :
    Hd.face.SameCycle xd yd ↔ G.face.SameCycle (hd xd) (hd yd) :=
  sameCycle_iff_of_equivariantOn (σ := G.face) (σ' := Hd.face) (h := hd)
    (S := (faceOuter Hd hd hr bd)ᶜ)
    (invariant_compl P.faceOuter_invariant) P.injd.injOn
    (fun y hy => P.face_d (fun hcon =>
      hy ((P.mem_faceOuter_hd_iff y).2 (bd_subset_faceBand Hd bd hcon))))
    hx

/-- **Bridgelessness passes to the pieces.**  A bridge of either side is a
bridge of the glued map. -/
theorem bridgeless_parts (P : Patch G Hd Hr hd hr bd br) (h : Bridgeless G) :
    Bridgeless Hd ∧ Bridgeless Hr := by
  constructor
  · intro xd hxd
    refine h (hd xd) ?_
    have h1 : G.face.SameCycle (hd xd) (hd (Hd.edge xd)) := P.sameCycle_face_d hxd
    have h2 : G.face.SameCycle (hd (Hd.edge xd)) (hd (Hd.face (Hd.edge xd))) :=
      P.sameCycle_face_d_step _
    have h3 : G.face.SameCycle (G.edge (hd xd)) (hd (Hd.face (Hd.edge xd))) := by
      refine ⟨1, ?_⟩
      rw [zpow_one, P.face_edge_hd]
    exact (h1.trans h2).trans h3.symm
  · intro xr hxr
    refine h (hr xr) ?_
    rw [← P.edge_r]
    exact P.sameCycle_face_r_of hxr

/-- The border dart matching data: a disk border dart's edge successor and the
dart itself are the images of a remainder dart and its node successor. -/
theorem exists_ring_partner (P : Patch G Hd Hr hd hr bd br) {yd : Dd} (hy : yd ∈ bd) :
    ∃ yr : Dr, hd (Hd.edge yd) = hr yr ∧ hd yd = hr (Hr.node yr) := by
  obtain ⟨yr, _, hyr⟩ := P.exists_br_of_bd ((P.mem_bd_edge_iff yd).2 hy)
  exact ⟨yr, hyr.symm, (P.ring_rev yd yr).1 hyr.symm⟩

/-- **Bridgelessness passes up to the glued map**, given that the border has no
chords.

The argument: a bridge of `G` that misses the remainder's image is a bridge of
the disk, and one that meets it is a bridge of the remainder — unless the
offending `G`-face crosses the ring, in which case the two border darts it
crosses at are face-adjacent, hence consecutive, and then the bridge is a
bridge of the remainder after all. -/
theorem bridgeless_patch (P : Patch G Hd Hr hd hr bd br)
    (hbd : Bridgeless Hd) (hbr : Bridgeless Hr) (hch : Chordless Hd bd) :
    Bridgeless G := by
  intro x hx
  by_cases hxr : x ∈ Set.range hr
  · obtain ⟨xr, rfl⟩ := hxr
    refine hbr xr ?_
    rw [P.sameCycle_face_r xr (Hr.edge xr), P.edge_r]
    exact hx
  obtain ⟨xd, rfl⟩ := (P.mem_range_or x).resolve_right hxr
  have hxb : xd ∉ bd := fun hcon => hxr (P.ring_subset_range_r ⟨xd, hcon, rfl⟩)
  rw [← P.edge_d xd hxb] at hx
  by_cases hout : hd xd ∈ faceOuter Hd hd hr bd
  · -- the offending face reaches the ring on both sides of the edge
    have hout2 : hd (Hd.edge xd) ∈ faceOuter Hd hd hr bd :=
      (saturated_sameCycle_of_invariant P.faceOuter_invariant) hx hout
    obtain ⟨yd, hyd, hxy⟩ := (P.mem_faceOuter_hd_iff xd).1 hout
    obtain ⟨zd, hzd, hez⟩ := (P.mem_faceOuter_hd_iff (Hd.edge xd)).1 hout2
    have hchain : G.face.SameCycle (hd yd) (hd zd) :=
      ((P.sameCycle_face_d hxy).symm.trans hx).trans (P.sameCycle_face_d hez)
    obtain ⟨yr, hyr1, hyr2⟩ := P.exists_ring_partner hyd
    rcases hch yd hyd zd hzd ⟨xd, hxy.symm, hez⟩ with hz | hz
    · -- `zd` is the border successor of `yd`
      subst hz
      rw [hyr1, hyr2] at hchain
      refine hbr (Hr.node yr) ?_
      have hstep : Hr.face.SameCycle (Hr.edge (Hr.node yr)) yr := by
        refine ⟨1, ?_⟩
        rw [zpow_one]
        exact Hr.face_edge_node yr
      exact ((P.sameCycle_face_r _ _).2 hchain).trans hstep.symm
    · -- `zd` is the border predecessor of `yd`
      have hzy : Hd.edge zd = yd := by rw [hz]; exact Hd.edge.apply_symm_apply yd
      have hzr : hd zd = hr (Hr.node (Hr.node yr)) :=
        (P.ring_rev zd (Hr.node yr)).1 (by rw [hzy]; exact hyr2)
      rw [hyr2, hzr] at hchain
      refine hbr (Hr.node (Hr.node yr)) ?_
      have hstep : Hr.face.SameCycle (Hr.edge (Hr.node (Hr.node yr))) (Hr.node yr) := by
        refine ⟨1, ?_⟩
        rw [zpow_one]
        exact Hr.face_edge_node (Hr.node yr)
      exact (((P.sameCycle_face_r _ _).2 hchain).symm).trans hstep.symm
  · exact hbd xd ((P.sameCycle_face_d_iff hout (Hd.edge xd)).2 hx)

end Patch

end Hypermap

end Mettapedia.GraphTheory.FourColor
