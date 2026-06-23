import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Perm.Cycle.Factors
import Mathlib.Tactic.FinCases
import Mettapedia.GraphTheory.PermCycleExtras

namespace Mettapedia.GraphTheory.FourColor

open scoped BigOperators

noncomputable section

/-- A finite combinatorial rotation system. This is the reusable, non-planarity
core of the old standalone FourColor rotation-system file: darts, an edge flip
`alpha`, a vertex rotation `rho`, and a distinguished outer dart. -/
structure RotationSystem (V E : Type*)
    [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] where
  D : Type*
  [instFintypeD : Fintype D]
  [instDecEqD : DecidableEq D]
  edgeOf : D → E
  vertOf : D → V
  alpha : Equiv.Perm D
  rho : Equiv.Perm D
  alpha_involutive : ∀ d, alpha (alpha d) = d
  alpha_fixfree : ∀ d, alpha d ≠ d
  edge_alpha : ∀ d, edgeOf (alpha d) = edgeOf d
  edge_fiber_two : ∀ e : E, (Finset.univ.filter (fun d => edgeOf d = e)).card = 2
  vert_rho : ∀ d, vertOf (rho d) = vertOf d
  outer : D
  no_self_loops : ∀ d : D, vertOf d ≠ vertOf (alpha d)

attribute [instance] RotationSystem.instFintypeD RotationSystem.instDecEqD

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

/-- Face permutation: rotate around the opposite endpoint after crossing an edge. -/
def phi : Equiv.Perm RS.D :=
  RS.rho * RS.alpha

/-- Darts in the same face orbit under `phi`. -/
def faceOrbit (d : RS.D) : Finset RS.D :=
  Finset.univ.filter (fun d' => RS.phi.SameCycle d d')

/-- Edges appearing in a face orbit. -/
def faceEdges (d : RS.D) : Finset E :=
  (RS.faceOrbit d).image RS.edgeOf

/-- Edges on the distinguished outer face. -/
def boundaryEdges : Finset E :=
  RS.faceEdges RS.outer

/-- Internal face edge sets: all face edge sets except the outer one. -/
def internalFaces : Finset (Finset E) :=
  (Finset.univ.image RS.faceEdges).filter (fun f => f ≠ RS.boundaryEdges)

/-- Darts whose underlying edge is `e`. -/
def dartsOn (e : E) : Finset RS.D :=
  Finset.univ.filter (fun d => RS.edgeOf d = e)

/-- Internal faces incident to edge `e`. -/
def facesIncidence (e : E) : Finset (Finset E) :=
  RS.internalFaces.filter (fun f => e ∈ f)

/-- No two distinct internal faces share two distinct interior edges. This is the
rotation-system form of the no-digons condition; it is not a consequence of the
bare rotation-system data. -/
def NoInteriorDigons : Prop :=
  ∀ {f g : Finset E},
    f ∈ RS.internalFaces →
    g ∈ RS.internalFaces →
    f ≠ g →
    ∀ {e₁ e₂ : E},
      e₁ ≠ e₂ →
      e₁ ∉ RS.boundaryEdges →
      e₂ ∉ RS.boundaryEdges →
      e₁ ∈ f → e₁ ∈ g →
      e₂ ∈ f → e₂ ∈ g →
      False

/-- Direct elimination form of `NoInteriorDigons`: two distinct internal faces
cannot share two distinct non-boundary edges. This ports the useful old
`Geometry.NoDigons.faces_share_at_most_one_interior_edge` surface, but keeps
the no-digons property as an explicit hypothesis. -/
theorem faces_share_at_most_one_interior_edge
    (hNoDigons : RS.NoInteriorDigons)
    {f g : Finset E} (hf : f ∈ RS.internalFaces)
    (hg : g ∈ RS.internalFaces) (hfg : f ≠ g)
    {e₁ e₂ : E} (he₁₂ : e₁ ≠ e₂)
    (he₁Interior : e₁ ∉ RS.boundaryEdges)
    (he₂Interior : e₂ ∉ RS.boundaryEdges)
    (he₁f : e₁ ∈ f) (he₁g : e₁ ∈ g)
    (he₂f : e₂ ∈ f) (he₂g : e₂ ∈ g) :
    False :=
  hNoDigons hf hg hfg he₁₂ he₁Interior he₂Interior he₁f he₁g he₂f he₂g

/-- The two local planarity facts needed to turn face-orbit toggle parity into
vertex-incidence parity for internal faces. This is weaker than a full planar
rotation geometry: it deliberately does not assert no-digons, exact two-face
incidence, or a realization by a `SimpleGraph` embedding. -/
structure InteriorFacePlanarity where
  boundary_edge_both_outer :
    ∀ {e : E} {d : RS.D}, RS.edgeOf d = e → e ∈ RS.boundaryEdges →
      RS.faceEdges d = RS.boundaryEdges
  alpha_interior_distinct_faces :
    ∀ {d : RS.D}, RS.edgeOf d ∉ RS.boundaryEdges →
      RS.faceEdges (RS.alpha d) ≠ RS.faceEdges d

/-- A planar rotation-system package, ported from the old standalone
`FourColor.Geometry.RotationSystem.PlanarGeometry` layer. It extends the bare
rotation system with the genuine local planarity facts and the simple-graph
no-parallel-edges condition, without importing the old `DiskGeometry` surface. -/
structure PlanarGeometry (V E : Type*) [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] extends RotationSystem V E where
  /-- Interior edges put alpha-opposite darts on distinct face orbits. -/
  alpha_interior_distinct_faces :
    ∀ {d : toRotationSystem.D},
      toRotationSystem.edgeOf d ∉ toRotationSystem.boundaryEdges →
        toRotationSystem.faceEdges (toRotationSystem.alpha d) ≠
          toRotationSystem.faceEdges d
  /-- Distinct edges have distinct endpoint pairs. -/
  no_parallel_edges :
    ∀ {e e' : E} {d d' : toRotationSystem.D},
      toRotationSystem.edgeOf d = e →
      toRotationSystem.edgeOf d' = e' →
      e ≠ e' →
      ({toRotationSystem.vertOf d,
          toRotationSystem.vertOf (toRotationSystem.alpha d)} : Finset V) ≠
        ({toRotationSystem.vertOf d',
            toRotationSystem.vertOf (toRotationSystem.alpha d')} : Finset V)
  /-- Boundary edges have every dart-side face equal to the distinguished outer
  face. -/
  boundary_edge_both_outer :
    ∀ {e : E} {d : toRotationSystem.D},
      toRotationSystem.edgeOf d = e →
      e ∈ toRotationSystem.boundaryEdges →
        toRotationSystem.faceEdges d = toRotationSystem.boundaryEdges

namespace PlanarGeometry

variable (PG : PlanarGeometry V E)

/-- The local planarity package extracted from a planar rotation geometry. -/
def toInteriorFacePlanarity : PG.toRotationSystem.InteriorFacePlanarity where
  boundary_edge_both_outer := by
    intro e d hde heBoundary
    exact PG.boundary_edge_both_outer hde heBoundary
  alpha_interior_distinct_faces := by
    intro d hInterior
    exact PG.alpha_interior_distinct_faces hInterior

end PlanarGeometry

/-- Each edge has exactly two darts. -/
theorem dartsOn_card_two (e : E) : (RS.dartsOn e).card = 2 := by
  unfold dartsOn
  exact RS.edge_fiber_two e

@[simp]
theorem phi_apply (d : RS.D) : RS.phi d = RS.rho (RS.alpha d) :=
  rfl

@[simp]
theorem vert_phi_eq_vert_alpha (d : RS.D) :
    RS.vertOf (RS.phi d) = RS.vertOf (RS.alpha d) := by
  rw [RotationSystem.phi_apply]
  exact RS.vert_rho (RS.alpha d)

@[simp]
theorem mem_dartsOn {e : E} {d : RS.D} :
    d ∈ RS.dartsOn e ↔ RS.edgeOf d = e := by
  unfold dartsOn
  simp

@[simp]
theorem mem_faceOrbit {d d' : RS.D} :
    d' ∈ RS.faceOrbit d ↔ RS.phi.SameCycle d d' := by
  unfold faceOrbit
  simp

/-- Applying `alpha` preserves the set of darts over an edge. -/
theorem alpha_mem_dartsOn {e : E} {d : RS.D}
    (hd : d ∈ RS.dartsOn e) :
    RS.alpha d ∈ RS.dartsOn e := by
  rw [mem_dartsOn] at hd ⊢
  rw [RS.edge_alpha, hd]

theorem dartsOn_nonempty (e : E) : (RS.dartsOn e).Nonempty := by
  rw [← Finset.card_pos]
  rw [RS.dartsOn_card_two e]
  exact Nat.succ_pos 1

theorem dartsOn_eq_pair_of_mem {e : E} {d : RS.D} (hd : d ∈ RS.dartsOn e) :
    RS.dartsOn e = {d, RS.alpha d} := by
  have halpha : RS.alpha d ∈ RS.dartsOn e := RS.alpha_mem_dartsOn hd
  have hsubset : ({d, RS.alpha d} : Finset RS.D) ⊆ RS.dartsOn e := by
    intro d' hd'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd'
    rcases hd' with rfl | rfl
    · exact hd
    · exact halpha
  have hcard_pair : ({d, RS.alpha d} : Finset RS.D).card = 2 := by
    have hne : d ≠ RS.alpha d := (RS.alpha_fixfree d).symm
    simp [hne]
  have hcard_le : (RS.dartsOn e).card ≤ ({d, RS.alpha d} : Finset RS.D).card := by
    rw [RS.dartsOn_card_two e, hcard_pair]
  exact (Finset.eq_of_subset_of_card_le hsubset hcard_le).symm

/-- The two graph vertices touched by an edge, computed from the two darts over
that edge. This is the modern, rotation-system version of the old
`Geometry.NoDigons.endpoints` helper. -/
def endpoints (e : E) : Finset V :=
  (RS.dartsOn e).image RS.vertOf

@[simp]
theorem mem_endpoints_iff {e : E} {v : V} :
    v ∈ RS.endpoints e ↔ ∃ d : RS.D, d ∈ RS.dartsOn e ∧ RS.vertOf d = v := by
  simp [endpoints]

theorem endpoints_eq_pair_of_mem {e : E} {d : RS.D} (hd : d ∈ RS.dartsOn e) :
    RS.endpoints e = {RS.vertOf d, RS.vertOf (RS.alpha d)} := by
  unfold endpoints
  rw [RS.dartsOn_eq_pair_of_mem hd]
  ext v
  simp

/-- Every edge in the modern rotation-system data has two distinct endpoints.
This uses the old no-self-loop hypothesis and does not assume any planarity
claim. -/
theorem endpoints_card_two (e : E) : (RS.endpoints e).card = 2 := by
  rcases RS.dartsOn_nonempty e with ⟨d, hd⟩
  rw [RS.endpoints_eq_pair_of_mem hd]
  exact Finset.card_pair (RS.no_self_loops d)

/-- Edges incident to vertex `v`, computed directly from darts. -/
def incidentEdges (v : V) : Finset E :=
  Finset.univ.filter (fun e => ∃ d : RS.D, RS.edgeOf d = e ∧ RS.vertOf d = v)

@[simp]
theorem mem_incidentEdges_iff {e : E} {v : V} :
    e ∈ RS.incidentEdges v ↔
      ∃ d : RS.D, RS.edgeOf d = e ∧ RS.vertOf d = v := by
  simp [incidentEdges]

theorem edge_fiber_two_cases {e : E} {d y : RS.D}
    (hd : RS.edgeOf d = e) (hy : RS.edgeOf y = e) :
    y = d ∨ y = RS.alpha d := by
  have hdmem : d ∈ RS.dartsOn e := (RS.mem_dartsOn).2 hd
  have hymem : y ∈ RS.dartsOn e := (RS.mem_dartsOn).2 hy
  have hpair := RS.dartsOn_eq_pair_of_mem hdmem
  have : y ∈ ({d, RS.alpha d} : Finset RS.D) := by
    simpa [hpair] using hymem
  simpa using this

namespace PlanarGeometry

variable (PG : PlanarGeometry V E)

/-- Distinct edges in a planar rotation geometry have distinct endpoint sets.
This ports the clean old `Geometry.NoDigons.endpoints_injective` theorem under
the honest modern `PlanarGeometry` package, because the claim uses the
no-parallel-edges field and is not available from bare `RotationSystem` data. -/
theorem endpoints_injective {e₁ e₂ : E} (hne : e₁ ≠ e₂) :
    PG.toRotationSystem.endpoints e₁ ≠ PG.toRotationSystem.endpoints e₂ := by
  classical
  intro hend
  rcases PG.toRotationSystem.dartsOn_nonempty e₁ with ⟨d₁, hd₁⟩
  rcases PG.toRotationSystem.dartsOn_nonempty e₂ with ⟨d₂, hd₂⟩
  have hd₁edge : PG.toRotationSystem.edgeOf d₁ = e₁ :=
    (PG.toRotationSystem.mem_dartsOn).1 hd₁
  have hd₂edge : PG.toRotationSystem.edgeOf d₂ = e₂ :=
    (PG.toRotationSystem.mem_dartsOn).1 hd₂
  have hpair :
      ({PG.toRotationSystem.vertOf d₁,
          PG.toRotationSystem.vertOf (PG.toRotationSystem.alpha d₁)} : Finset V) =
        ({PG.toRotationSystem.vertOf d₂,
          PG.toRotationSystem.vertOf (PG.toRotationSystem.alpha d₂)} : Finset V) := by
    rw [← PG.toRotationSystem.endpoints_eq_pair_of_mem hd₁,
      ← PG.toRotationSystem.endpoints_eq_pair_of_mem hd₂]
    exact hend
  exact PG.no_parallel_edges hd₁edge hd₂edge hne hpair

end PlanarGeometry

@[simp]
theorem faceEdges_outer : RS.faceEdges RS.outer = RS.boundaryEdges :=
  rfl

@[simp]
theorem mem_boundaryEdges_iff {e : E} :
    e ∈ RS.boundaryEdges ↔ ∃ d ∈ RS.faceOrbit RS.outer, RS.edgeOf d = e := by
  unfold boundaryEdges faceEdges
  simp only [Finset.mem_image]

/-- An edge belongs to a face iff the face orbit contains a dart over that edge. -/
theorem mem_faceEdges_iff {d : RS.D} {e : E} :
    e ∈ RS.faceEdges d ↔ ∃ d' ∈ RS.faceOrbit d, RS.edgeOf d' = e := by
  unfold faceEdges
  simp only [Finset.mem_image]

/-- A face-orbit edge set is internal exactly when it is not the distinguished
outer boundary face. -/
theorem faceEdges_mem_internalFaces_of_ne_boundary (d : RS.D)
    (h : RS.faceEdges d ≠ RS.boundaryEdges) :
    RS.faceEdges d ∈ RS.internalFaces := by
  simp [internalFaces, h]

/-- An explicitly witnessed face is internal when it differs from the outer
boundary face. -/
theorem face_mem_internalFaces_of_witness {f : Finset E}
    (hf : ∃ d : RS.D, RS.faceEdges d = f)
    (hne : f ≠ RS.boundaryEdges) :
    f ∈ RS.internalFaces := by
  rcases hf with ⟨d, rfl⟩
  exact RS.faceEdges_mem_internalFaces_of_ne_boundary d hne

/-- If an explicitly witnessed face contains an edge that is not on the outer
boundary, then that face is internal. This is the witness-carrying replacement
for the old standalone `PlanarityHelpers` lemma; without the face witness the
claim is not available from bare rotation-system data. -/
theorem face_mem_internalFaces_of_mem_interior_edge_of_witness {e : E} {f : Finset E}
    (heInterior : e ∉ RS.boundaryEdges)
    (hf : ∃ d : RS.D, RS.faceEdges d = f)
    (hef : e ∈ f) :
    f ∈ RS.internalFaces := by
  apply RS.face_mem_internalFaces_of_witness hf
  intro hboundary
  exact heInterior (by
    rw [← hboundary]
    exact hef)

/-- Darts in the same `phi` cycle determine the same face edge set. -/
theorem faceEdges_of_sameCycle {d d' : RS.D} (h : RS.phi.SameCycle d d') :
    RS.faceEdges d = RS.faceEdges d' := by
  unfold faceEdges faceOrbit
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact
    ⟨fun hx => Equiv.Perm.SameCycle.trans (Equiv.Perm.SameCycle.symm h) hx,
     fun hx => Equiv.Perm.SameCycle.trans h hx⟩

/-- Darts over an edge whose face is internal, meaning it is not the
distinguished outer boundary face. This is the modern home for the old
`dartsOnInternal` helper from `Geometry/RotationSystem.lean`. -/
def dartsOnInternal (e : E) : Finset RS.D :=
  (RS.dartsOn e).filter (fun d => RS.faceEdges d ≠ RS.boundaryEdges)

@[simp]
theorem mem_dartsOnInternal_iff {e : E} {d : RS.D} :
    d ∈ RS.dartsOnInternal e ↔
      d ∈ RS.dartsOn e ∧ RS.faceEdges d ≠ RS.boundaryEdges := by
  simp [dartsOnInternal]

theorem dartsOnInternal_subset_dartsOn (e : E) :
    RS.dartsOnInternal e ⊆ RS.dartsOn e := by
  intro d hd
  exact (RS.mem_dartsOnInternal_iff).1 hd |>.1

theorem face_witness_of_mem_internalFaces {f : Finset E}
    (hf : f ∈ RS.internalFaces) :
    ∃ d : RS.D, RS.faceEdges d = f := by
  have hf' : (∃ d : RS.D, RS.faceEdges d = f) ∧ f ≠ RS.boundaryEdges := by
    simpa [RotationSystem.internalFaces] using hf
  exact hf'.1

theorem ne_boundaryEdges_of_mem_internalFaces {f : Finset E}
    (hf : f ∈ RS.internalFaces) :
    f ≠ RS.boundaryEdges := by
  have hf' : (∃ d : RS.D, RS.faceEdges d = f) ∧ f ≠ RS.boundaryEdges := by
    simpa [RotationSystem.internalFaces] using hf
  exact hf'.2

theorem facesIncidence_subset_image_faceEdges_of_dartsOnInternal (e : E) :
    RS.facesIncidence e ⊆ (RS.dartsOnInternal e).image RS.faceEdges := by
  intro f hf
  have hfInternal : f ∈ RS.internalFaces := (Finset.mem_filter.1 hf).1
  have heFace : e ∈ f := (Finset.mem_filter.1 hf).2
  rcases RS.face_witness_of_mem_internalFaces hfInternal with ⟨d₀, hd₀⟩
  have heFaceD₀ : e ∈ RS.faceEdges d₀ := by
    simpa [hd₀] using heFace
  rcases (RS.mem_faceEdges_iff).1 heFaceD₀ with ⟨d, hdOrbit, hde⟩
  have hdDarts : d ∈ RS.dartsOn e := (RS.mem_dartsOn).2 hde
  have hdSameFace : RS.faceEdges d = RS.faceEdges d₀ := by
    have hSame : RS.phi.SameCycle d₀ d := (RS.mem_faceOrbit).1 hdOrbit
    exact (RS.faceEdges_of_sameCycle hSame).symm
  have hdInternalFace : RS.faceEdges d ∈ RS.internalFaces := by
    simpa [hdSameFace, hd₀] using hfInternal
  have hdInternal : d ∈ RS.dartsOnInternal e := by
    exact (RS.mem_dartsOnInternal_iff).2
      ⟨hdDarts, RS.ne_boundaryEdges_of_mem_internalFaces hdInternalFace⟩
  exact Finset.mem_image.2 ⟨d, hdInternal, by simp [hdSameFace, hd₀]⟩

/-- Every internal face containing `e` is the face of one of the two darts over
`e`, so the number of internal faces incident to any edge is at most two. This
ports the old `twoIncidence_ofRotationSystem` theorem without importing the old
planarity surface. -/
theorem facesIncidence_card_le_two (e : E) :
    (RS.facesIncidence e).card ≤ 2 := by
  calc
    (RS.facesIncidence e).card
        ≤ ((RS.dartsOnInternal e).image RS.faceEdges).card :=
          Finset.card_le_card
            (RS.facesIncidence_subset_image_faceEdges_of_dartsOnInternal e)
    _ ≤ (RS.dartsOnInternal e).card := Finset.card_image_le
    _ ≤ (RS.dartsOn e).card :=
          Finset.card_le_card (RS.dartsOnInternal_subset_dartsOn e)
    _ = 2 := RS.dartsOn_card_two e

/-- Any non-boundary edge is covered by at least one internal face. -/
theorem interior_edge_covered {e : E} (heInterior : e ∉ RS.boundaryEdges) :
    ∃ f ∈ RS.internalFaces, e ∈ f := by
  rcases RS.dartsOn_nonempty e with ⟨d, hd⟩
  have heFace : e ∈ RS.faceEdges d :=
    (RS.mem_faceEdges_iff).2
      ⟨d, (RS.mem_faceOrbit).2 (Equiv.Perm.SameCycle.refl RS.phi d),
        (RS.mem_dartsOn).1 hd⟩
  exact
    ⟨RS.faceEdges d,
      RS.face_mem_internalFaces_of_mem_interior_edge_of_witness heInterior
        ⟨d, rfl⟩ heFace,
      heFace⟩

/-- A non-boundary edge is incident, in the rotation-system internal-face model,
to exactly the two face edge sets carried by its two darts. The two listed
faces may coincide in a bare rotation system; an `InteriorFacePlanarity`
hypothesis upgrades this to cardinality two. -/
theorem facesIncidence_eq_pair_of_nonboundary_edge {e : E}
    (heInterior : e ∉ RS.boundaryEdges) {d : RS.D} (hd : RS.edgeOf d = e) :
    RS.facesIncidence e = {RS.faceEdges d, RS.faceEdges (RS.alpha d)} := by
  classical
  ext f
  constructor
  · intro hf
    have hsub :=
      RS.facesIncidence_subset_image_faceEdges_of_dartsOnInternal e hf
    rcases Finset.mem_image.1 hsub with ⟨d', hd'internal, hface⟩
    have hd'darts : d' ∈ RS.dartsOn e :=
      (RS.mem_dartsOnInternal_iff).1 hd'internal |>.1
    have hd'edge : RS.edgeOf d' = e := (RS.mem_dartsOn).1 hd'darts
    rcases RS.edge_fiber_two_cases hd hd'edge with hd'eq | hd'eq
    · rw [← hface, hd'eq]
      simp
    · rw [← hface, hd'eq]
      simp
  · intro hf
    have hed : e ∈ RS.faceEdges d :=
      (RS.mem_faceEdges_iff).2
        ⟨d, (RS.mem_faceOrbit).2 (Equiv.Perm.SameCycle.refl RS.phi d), hd⟩
    have hdin : RS.faceEdges d ∈ RS.internalFaces :=
      RS.face_mem_internalFaces_of_mem_interior_edge_of_witness
        heInterior ⟨d, rfl⟩ hed
    have halphaEdge : RS.edgeOf (RS.alpha d) = e := by
      rw [RS.edge_alpha d, hd]
    have healpha : e ∈ RS.faceEdges (RS.alpha d) :=
      (RS.mem_faceEdges_iff).2
        ⟨RS.alpha d,
          (RS.mem_faceOrbit).2 (Equiv.Perm.SameCycle.refl RS.phi (RS.alpha d)),
          halphaEdge⟩
    have halphain : RS.faceEdges (RS.alpha d) ∈ RS.internalFaces :=
      RS.face_mem_internalFaces_of_mem_interior_edge_of_witness
        heInterior ⟨RS.alpha d, rfl⟩ healpha
    rcases Finset.mem_insert.1 hf with hfd | hfa
    · rw [hfd]
      exact Finset.mem_filter.2 ⟨hdin, hed⟩
    · rw [Finset.mem_singleton.1 hfa]
      exact Finset.mem_filter.2 ⟨halphain, healpha⟩

theorem facesIncidence_card_eq_two_of_interiorFacePlanarity
    (P : RS.InteriorFacePlanarity) {e : E}
    (heInterior : e ∉ RS.boundaryEdges) {d : RS.D} (hd : RS.edgeOf d = e) :
    (RS.facesIncidence e).card = 2 := by
  rw [RS.facesIncidence_eq_pair_of_nonboundary_edge heInterior hd]
  have hne : RS.faceEdges d ≠ RS.faceEdges (RS.alpha d) := by
    intro h
    have hdInterior : RS.edgeOf d ∉ RS.boundaryEdges := by
      simpa [hd] using heInterior
    exact P.alpha_interior_distinct_faces hdInterior h.symm
  exact Finset.card_pair hne

namespace PlanarGeometry

variable (PG : PlanarGeometry V E)

theorem facesIncidence_card_eq_two_of_interior_edge {e : E}
    (heInterior : e ∉ PG.toRotationSystem.boundaryEdges) :
    (PG.toRotationSystem.facesIncidence e).card = 2 := by
  rcases PG.toRotationSystem.dartsOn_nonempty e with ⟨d, hdmem⟩
  exact
    PG.toRotationSystem.facesIncidence_card_eq_two_of_interiorFacePlanarity
      PG.toInteriorFacePlanarity heInterior
      ((PG.toRotationSystem.mem_dartsOn).1 hdmem)

/-- Internal faces of a planar rotation geometry contain no boundary edge. This
packages the old `internal_face_disjoint_boundary` lemma in the active
`PlanarGeometry` interface. -/
theorem internal_face_disjoint_boundary {f : Finset E}
    (hf : f ∈ PG.toRotationSystem.internalFaces) :
    Disjoint f PG.toRotationSystem.boundaryEdges := by
  rw [Finset.disjoint_left]
  intro e hef heBoundary
  rcases PG.toRotationSystem.face_witness_of_mem_internalFaces hf with ⟨d, hd⟩
  have hInternal : PG.toRotationSystem.faceEdges d ≠ PG.toRotationSystem.boundaryEdges := by
    rw [hd]
    exact PG.toRotationSystem.ne_boundaryEdges_of_mem_internalFaces hf
  have heFace : e ∈ PG.toRotationSystem.faceEdges d := by
    simpa [hd] using hef
  rcases (PG.toRotationSystem.mem_faceEdges_iff).1 heFace with ⟨d', hd'Face, hd'e⟩
  have hd'Boundary : PG.toRotationSystem.faceEdges d' =
      PG.toRotationSystem.boundaryEdges :=
    PG.boundary_edge_both_outer hd'e heBoundary
  have hSame : PG.toRotationSystem.faceEdges d = PG.toRotationSystem.faceEdges d' :=
    PG.toRotationSystem.faceEdges_of_sameCycle
      ((PG.toRotationSystem.mem_faceOrbit).1 hd'Face)
  exact hInternal (hSame.trans hd'Boundary)

end PlanarGeometry

theorem alpha_not_mem_faceOrbit_of_interior
    (halpha :
      ∀ {d : RS.D}, RS.edgeOf d ∉ RS.boundaryEdges →
        RS.faceEdges (RS.alpha d) ≠ RS.faceEdges d)
    {d d₀ : RS.D} (hInterior : RS.edgeOf d ∉ RS.boundaryEdges)
    (hd : d ∈ RS.faceOrbit d₀) :
    RS.alpha d ∉ RS.faceOrbit d₀ := by
  intro halphaOrbit
  have hSameD₀D : RS.faceEdges d₀ = RS.faceEdges d :=
    RS.faceEdges_of_sameCycle ((RS.mem_faceOrbit).1 hd)
  have hSameD₀Alpha : RS.faceEdges d₀ = RS.faceEdges (RS.alpha d) :=
    RS.faceEdges_of_sameCycle ((RS.mem_faceOrbit).1 halphaOrbit)
  have hSameAlphaD : RS.faceEdges (RS.alpha d) = RS.faceEdges d := by
    rw [← hSameD₀Alpha, hSameD₀D]
  exact halpha hInterior hSameAlphaD

theorem edge_of_internal_face_not_boundary
    (hboundary :
      ∀ {e : E} {d : RS.D}, RS.edgeOf d = e → e ∈ RS.boundaryEdges →
        RS.faceEdges d = RS.boundaryEdges)
    {d₀ : RS.D} {e : E}
    (he : e ∈ RS.faceEdges d₀)
    (hInternal : RS.faceEdges d₀ ≠ RS.boundaryEdges) :
    e ∉ RS.boundaryEdges := by
  intro heBoundary
  rcases (RS.mem_faceEdges_iff).1 he with ⟨d, hdOrbit, hde⟩
  have hdBoundary : RS.faceEdges d = RS.boundaryEdges :=
    hboundary hde heBoundary
  have hSameD₀D : RS.faceEdges d₀ = RS.faceEdges d :=
    RS.faceEdges_of_sameCycle ((RS.mem_faceOrbit).1 hdOrbit)
  exact hInternal (hSameD₀D.trans hdBoundary)

namespace PlanarGeometry

variable (PG : PlanarGeometry V E)

/-- For an internal face of a planar rotation geometry, the face orbit has the
same cardinality as its edge set. Equivalently, `edgeOf` is injective on the
internal face orbit. This ports the remaining clean old
`PlanarityHelpers.card_faceOrbit_eq_card_faceEdges_of_internal` theorem under
the explicit modern `PlanarGeometry` hypotheses. -/
theorem card_faceOrbit_eq_card_faceEdges_of_internal
    {d : PG.toRotationSystem.D}
    (hInternal :
      PG.toRotationSystem.faceEdges d ≠ PG.toRotationSystem.boundaryEdges) :
    (PG.toRotationSystem.faceOrbit d).card =
      (PG.toRotationSystem.faceEdges d).card := by
  classical
  rw [RotationSystem.faceEdges]
  symm
  rw [Finset.card_image_iff]
  intro x hx y hy hxy
  rcases PG.toRotationSystem.edge_fiber_two_cases hxy rfl with h | h
  · exact h.symm
  · have hxEdgeMem :
        PG.toRotationSystem.edgeOf x ∈ PG.toRotationSystem.faceEdges d :=
      (PG.toRotationSystem.mem_faceEdges_iff).2 ⟨x, hx, rfl⟩
    have hxInterior :
        PG.toRotationSystem.edgeOf x ∉ PG.toRotationSystem.boundaryEdges :=
      PG.toRotationSystem.edge_of_internal_face_not_boundary
        PG.boundary_edge_both_outer hxEdgeMem hInternal
    have halphaNot :
        PG.toRotationSystem.alpha x ∉ PG.toRotationSystem.faceOrbit d :=
      PG.toRotationSystem.alpha_not_mem_faceOrbit_of_interior
        PG.alpha_interior_distinct_faces hxInterior hx
    have halphaMem :
        PG.toRotationSystem.alpha x ∈ PG.toRotationSystem.faceOrbit d := by
      simpa [h] using hy
    exact (halphaNot halphaMem).elim

end PlanarGeometry

/-- Darts in the same `phi` cycle determine the same face orbit. -/
theorem faceOrbit_eq_of_sameCycle {d d' : RS.D} (h : RS.phi.SameCycle d d') :
    RS.faceOrbit d = RS.faceOrbit d' := by
  ext x
  rw [RS.mem_faceOrbit, RS.mem_faceOrbit]
  exact
    ⟨fun hx => Equiv.Perm.SameCycle.trans (Equiv.Perm.SameCycle.symm h) hx,
     fun hx => Equiv.Perm.SameCycle.trans h hx⟩

/-- Every dart lies in its own face orbit. -/
theorem mem_faceOrbit_self (d : RS.D) : d ∈ RS.faceOrbit d := by
  unfold faceOrbit
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Equiv.Perm.SameCycle.refl RS.phi d

/-- Membership in a face orbit identifies the orbit. -/
theorem faceOrbit_of_mem {d d' : RS.D} (h : d' ∈ RS.faceOrbit d) :
    RS.faceOrbit d' = RS.faceOrbit d := by
  exact (RS.faceOrbit_eq_of_sameCycle ((RS.mem_faceOrbit).1 h)).symm

theorem phi_mem_faceOrbit {d₀ d : RS.D} (hd : d ∈ RS.faceOrbit d₀) :
    RS.phi d ∈ RS.faceOrbit d₀ := by
  have h : RS.phi.SameCycle d₀ d := (RS.mem_faceOrbit).1 hd
  exact (RS.mem_faceOrbit).2
    (h.trans (Mettapedia.GraphTheory.EquivPermSameCycle.step_right RS.phi d))

theorem phi_symm_mem_faceOrbit {d₀ d : RS.D} (hd : d ∈ RS.faceOrbit d₀) :
    RS.phi.symm d ∈ RS.faceOrbit d₀ := by
  have h : RS.phi.SameCycle d₀ d := (RS.mem_faceOrbit).1 hd
  exact (RS.mem_faceOrbit).2
    (h.trans (Mettapedia.GraphTheory.EquivPermSameCycle.step_right_inv RS.phi d))

theorem phi_mem_faceOrbit_iff {d₀ d : RS.D} :
    RS.phi d ∈ RS.faceOrbit d₀ ↔ d ∈ RS.faceOrbit d₀ := by
  constructor
  · intro h
    exact (RS.mem_faceOrbit).2
      ((Mettapedia.GraphTheory.EquivPermSameCycle.sameCycle_apply_right RS.phi).1
        ((RS.mem_faceOrbit).1 h))
  · exact RS.phi_mem_faceOrbit

theorem faceOrbit_image_phi (d₀ : RS.D) :
    (RS.faceOrbit d₀).image RS.phi = RS.faceOrbit d₀ := by
  classical
  ext d
  constructor
  · intro hd
    rcases Finset.mem_image.1 hd with ⟨d', hd', rfl⟩
    exact RS.phi_mem_faceOrbit hd'
  · intro hd
    exact Finset.mem_image.2 ⟨RS.phi.symm d, RS.phi_symm_mem_faceOrbit hd, by simp⟩

theorem sum_comp_phi_faceOrbit {β : Type*} [AddCommMonoid β]
    (d₀ : RS.D) (g : RS.D → β) :
    ∑ d ∈ RS.faceOrbit d₀, g (RS.phi d) =
      ∑ d ∈ RS.faceOrbit d₀, g d := by
  classical
  refine Finset.sum_bij
    (fun d _hd => RS.phi d)
    (fun _d hd => RS.phi_mem_faceOrbit hd)
    (fun _a _ha _b _hb h => RS.phi.injective h)
    ?surj
    (fun _d _hd => rfl)
  intro d hd
  exact ⟨RS.phi.symm d, RS.phi_symm_mem_faceOrbit hd, by simp⟩

/-- Darts in a face orbit where membership at vertex `v` changes after one
face-permutation step. This is the pure cyclic-toggle object underlying the old
face/vertex parity proof. -/
def togglesOn (v : V) (d₀ : RS.D) : Finset RS.D :=
  (RS.faceOrbit d₀).filter (fun d =>
    decide (RS.vertOf d = v) ≠ decide (RS.vertOf (RS.phi d) = v))

@[simp]
theorem mem_togglesOn_iff {v : V} {d₀ d : RS.D} :
    d ∈ RS.togglesOn v d₀ ↔
      d ∈ RS.faceOrbit d₀ ∧
        decide (RS.vertOf d = v) ≠ decide (RS.vertOf (RS.phi d) = v) := by
  simp [togglesOn]

private theorem zmod2_add_self_local (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> rfl

/-- `ZMod 2` indicator of whether a dart is based at a vertex. -/
private def vertexIndicator (v : V) (d : RS.D) : ZMod 2 :=
  if RS.vertOf d = v then 1 else 0

private theorem vertexIndicator_pair_zero_or_one (v : V) (d : RS.D) :
    RS.vertexIndicator v d + RS.vertexIndicator v (RS.phi d) = 0 ∨
      RS.vertexIndicator v d + RS.vertexIndicator v (RS.phi d) = 1 := by
  unfold vertexIndicator
  by_cases h₁ : RS.vertOf d = v <;>
    by_cases h₂ : RS.vertOf (RS.rho (RS.alpha d)) = v <;>
    simp [RotationSystem.phi_apply, h₁, h₂, zmod2_add_self_local]

private theorem sum_zmod2_eq_card_filter_one {α : Type*} [DecidableEq α]
    (S : Finset α) (g : α → ZMod 2)
    (h01 : ∀ x ∈ S, g x = 0 ∨ g x = 1) :
    ∑ x ∈ S, g x = ((S.filter (fun x => g x = 1)).card : ZMod 2) := by
  classical
  induction S using Finset.induction with
  | empty =>
      simp
  | insert a S ha ih =>
      have h01S : ∀ x ∈ S, g x = 0 ∨ g x = 1 := fun x hx =>
        h01 x (Finset.mem_insert_of_mem hx)
      rcases h01 a (Finset.mem_insert_self a S) with h0 | h1
      · rw [Finset.sum_insert ha, h0, zero_add, Finset.filter_insert,
          if_neg (by simp [h0])]
        exact ih h01S
      · rw [Finset.sum_insert ha, h1, Finset.filter_insert,
          if_pos (by simp [h1])]
        have hnot : a ∉ S.filter (fun x => g x = 1) := by
          simp [ha]
        rw [Finset.card_insert_of_notMem hnot, ih h01S]
        rw [add_comm]
        simp [Nat.cast_add, Nat.cast_one]

/-- A finite face orbit has an even number of vertex-membership toggles. This
ports the pure cyclic parity core of the old rotation-system proof without
claiming the stronger planarity-dependent face-cycle theorem. -/
theorem togglesOn_card_even (d₀ : RS.D) (v : V) :
    Even ((RS.togglesOn v d₀).card) := by
  classical
  have hperm :
      (∑ d ∈ RS.faceOrbit d₀,
        (RS.vertexIndicator v d + RS.vertexIndicator v (RS.phi d) : ZMod 2)) = 0 := by
    have hreindex :=
      RS.sum_comp_phi_faceOrbit (d₀ := d₀) (g := RS.vertexIndicator v)
    have hright :
        (∑ d ∈ RS.faceOrbit d₀, RS.vertexIndicator v (RS.phi d)) =
          ∑ d ∈ RS.faceOrbit d₀, RS.vertexIndicator v d := by
      simpa using hreindex
    calc
      (∑ d ∈ RS.faceOrbit d₀,
        (RS.vertexIndicator v d + RS.vertexIndicator v (RS.phi d) : ZMod 2))
          = (∑ d ∈ RS.faceOrbit d₀, RS.vertexIndicator v d) +
              (∑ d ∈ RS.faceOrbit d₀, RS.vertexIndicator v (RS.phi d)) := by
              simp [Finset.sum_add_distrib]
      _ = (∑ d ∈ RS.faceOrbit d₀, RS.vertexIndicator v d) +
            (∑ d ∈ RS.faceOrbit d₀, RS.vertexIndicator v d) := by
            rw [hright]
      _ = 0 := by exact zmod2_add_self_local _
  have hsum_as_card :
      (∑ d ∈ RS.faceOrbit d₀,
        (RS.vertexIndicator v d + RS.vertexIndicator v (RS.phi d) : ZMod 2)) =
          ((RS.togglesOn v d₀).card : ZMod 2) := by
    have h01 : ∀ d ∈ RS.faceOrbit d₀,
        RS.vertexIndicator v d + RS.vertexIndicator v (RS.phi d) = 0 ∨
          RS.vertexIndicator v d + RS.vertexIndicator v (RS.phi d) = 1 := by
      intro d _hd
      exact RS.vertexIndicator_pair_zero_or_one v d
    have hsum :=
      sum_zmod2_eq_card_filter_one (S := RS.faceOrbit d₀)
        (g := fun d => RS.vertexIndicator v d + RS.vertexIndicator v (RS.phi d))
        h01
    have hfilter :
        (RS.faceOrbit d₀).filter
            (fun d => RS.vertexIndicator v d + RS.vertexIndicator v (RS.phi d) = 1) =
          RS.togglesOn v d₀ := by
      ext d
      by_cases h₁ : RS.vertOf d = v <;>
        by_cases h₂ : RS.vertOf (RS.rho (RS.alpha d)) = v <;>
        simp [togglesOn, vertexIndicator, RotationSystem.phi_apply, h₁, h₂]
    rw [← hfilter]
    exact hsum
  have hzero : (((RS.togglesOn v d₀).card : ZMod 2) = 0) := by
    rw [← hsum_as_card]
    exact hperm
  rw [even_iff_two_dvd]
  exact (ZMod.natCast_eq_zero_iff (RS.togglesOn v d₀).card 2).mp hzero

end RotationSystem

end

end Mettapedia.GraphTheory.FourColor
