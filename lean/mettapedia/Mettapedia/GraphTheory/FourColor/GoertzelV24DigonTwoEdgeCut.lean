import Mettapedia.GraphTheory.FourColor.GoertzelV24DigonPatchDarts
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutCap
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationEdgeBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness

/-!
# A digon is an exact two-edge cut

A parallel pair `e, f` between `u` and `v` in a cubic map, together with the
two exterior edges `outerU`, `outerV`, is an exact two-edge cut: the side
`{u, v}` meets the rest of the map along exactly those two edges.  This file
builds the cut data on a bare rotation system — the multigraph level, since a
graph-backed rotation system cannot even express a parallel pair — and proves
the two facts that are not bookkeeping.

*The far endpoints differ.*  If both exterior edges landed on one vertex `w`,
then `{u, v, w}` would meet the rest of the map along `w`'s third edge alone,
which bridge-freeness forbids.

*The complement is connected.*  Bridge-freeness at `outerU` gives a walk from
`u` to `u'` avoiding `outerU`; it must leave `{u, v}` through `outerV`, so it
contains a `v'`–`u'` walk avoiding `{u, v}`.  Any walk through the digon
region can then be rerouted around it.

Everything is stated with `houter`: the far endpoint of `outerV` is not `u`.
That is the non-theta condition; looplessness supplies the rest.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace RotationSystem

open GoertzelV24RotationEdgeBridge
open GoertzelV24FaceDualConnectedness
open GoertzelV24RotationCutDartDecomposition

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

noncomputable section

namespace DigonPatchData

variable {RS : RotationSystem V E} (D : @DigonPatchData V E)

/-! ## The far endpoints -/

/-- The far endpoint of `outerU`. -/
def uFar (hD : D.WellFormed RS) : V := RS.vertOf (D.a' hD)

/-- The far endpoint of `outerV`. -/
def vFar (hD : D.WellFormed RS) : V := RS.vertOf (D.b' hD)

theorem uFar_ne_u (hD : D.WellFormed RS) : D.uFar hD ≠ D.u := by
  intro h
  apply RS.no_self_loops (D.pₐ hD)
  rw [D.vertOf_pₐ hD, D.alpha_pₐ hD]
  exact h.symm

theorem vFar_ne_v (hD : D.WellFormed RS) : D.vFar hD ≠ D.v := by
  intro h
  apply RS.no_self_loops (D.qᵦ hD)
  rw [D.vertOf_qᵦ hD, D.alpha_qᵦ hD]
  exact h.symm

theorem endpoints_outerU (hD : D.WellFormed RS) :
    RS.endpoints D.outerU = {D.u, D.uFar hD} := by
  have hmem : D.pₐ hD ∈ RS.dartsOn D.outerU := RS.mem_dartsOn.2 (D.edgeOf_pₐ hD)
  rw [RS.endpoints_eq_pair_of_mem hmem, D.vertOf_pₐ hD, D.alpha_pₐ hD]
  rfl

theorem endpoints_outerV (hD : D.WellFormed RS) :
    RS.endpoints D.outerV = {D.v, D.vFar hD} := by
  have hmem : D.qᵦ hD ∈ RS.dartsOn D.outerV := RS.mem_dartsOn.2 (D.edgeOf_qᵦ hD)
  rw [RS.endpoints_eq_pair_of_mem hmem, D.vertOf_qᵦ hD, D.alpha_qᵦ hD]
  rfl

theorem endpoints_e (hD : D.WellFormed RS) : RS.endpoints D.e = {D.u, D.v} := by
  have hmem : D.p₁ hD ∈ RS.dartsOn D.e := RS.mem_dartsOn.2 (D.edgeOf_p₁ hD)
  rw [RS.endpoints_eq_pair_of_mem hmem, D.vertOf_p₁ hD, D.alpha_p₁ hD, D.vertOf_q₁ hD]

theorem endpoints_f (hD : D.WellFormed RS) : RS.endpoints D.f = {D.u, D.v} := by
  have hmem : D.p₂ hD ∈ RS.dartsOn D.f := RS.mem_dartsOn.2 (D.edgeOf_p₂ hD)
  rw [RS.endpoints_eq_pair_of_mem hmem, D.vertOf_p₂ hD, D.alpha_p₂ hD, D.vertOf_q₂ hD]

/-- **The two exterior edges differ**, given the non-theta condition. -/
theorem outerU_ne_outerV (hD : D.WellFormed RS) (houter : D.vFar hD ≠ D.u) :
    D.outerU ≠ D.outerV := by
  intro h
  have hE := D.endpoints_outerU hD
  rw [h, D.endpoints_outerV hD] at hE
  have hu : D.u ∈ ({D.v, D.vFar hD} : Finset V) := by rw [hE]; simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with hu | hu
  · exact hD.1 hu
  · exact houter hu.symm

/-- The far endpoint of `outerU` is not `v` either: otherwise `outerU` would be
a third `u`–`v` edge, forcing `outerU = outerV` and contradicting `houter`. -/
theorem uFar_ne_v (hD : D.WellFormed RS) (hCubic : RS.IsCubic) (houter : D.vFar hD ≠ D.u) :
    D.uFar hD ≠ D.v := by
  intro h
  have hv : D.v ∈ RS.endpoints D.outerU := by rw [D.endpoints_outerU hD, h]; simp
  have hinc : D.outerU ∈ RS.incidentEdges D.v :=
    (RS.mem_endpoints_iff_mem_incidentEdges).1 hv
  rw [hD.2.2.2] at hinc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hinc
  have hne := D.edges_u_pairwise_ne hD hCubic
  rcases hinc with hinc | hinc | hinc
  · exact D.outerU_ne_outerV hD houter hinc
  · exact hne.1 hinc
  · exact hne.2.1 hinc

/-- The far endpoints lie outside the digon side. -/
theorem uFar_not_mem (hD : D.WellFormed RS) (hCubic : RS.IsCubic) (houter : D.vFar hD ≠ D.u) :
    D.uFar hD ∉ ({D.u, D.v} : Finset V) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨D.uFar_ne_u hD, D.uFar_ne_v hD hCubic houter⟩

theorem vFar_not_mem (hD : D.WellFormed RS) (houter : D.vFar hD ≠ D.u) :
    D.vFar hD ∉ ({D.u, D.v} : Finset V) := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨houter, D.vFar_ne_v hD⟩

/-! ## The boundary of the digon side -/

/-- An edge incident to `u` or `v` is one of the four named edges. -/
theorem eq_of_mem_incident (hD : D.WellFormed RS) {g : E}
    (hg : g ∈ RS.incidentEdges D.u ∨ g ∈ RS.incidentEdges D.v) :
    g = D.outerU ∨ g = D.outerV ∨ g = D.e ∨ g = D.f := by
  rcases hg with hg | hg
  · rw [hD.2.2.1] at hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl <;> simp
  · rw [hD.2.2.2] at hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl <;> simp

/-- **The digon side meets the rest of the map along exactly the two exterior
edges.** -/
theorem boundary_eq (hD : D.WellFormed RS) (hCubic : RS.IsCubic) (houter : D.vFar hD ≠ D.u) :
    RS.vertexSideEdgeBoundary ({D.u, D.v} : Finset V) = {D.outerU, D.outerV} := by
  classical
  have huv : D.u ≠ D.v := hD.1
  have huFar := D.uFar_not_mem hD hCubic houter
  have hvFar := D.vFar_not_mem hD houter
  ext g
  rw [RS.mem_vertexSideEdgeBoundary_iff]
  constructor
  · intro hcard
    -- some endpoint lies in the side
    have hne : (RS.endpoints g ∩ {D.u, D.v}).Nonempty := by
      rw [← Finset.card_pos, hcard]; exact Nat.one_pos
    obtain ⟨x, hx⟩ := hne
    rw [Finset.mem_inter] at hx
    have hinc : g ∈ RS.incidentEdges D.u ∨ g ∈ RS.incidentEdges D.v := by
      have hx2 := hx.2
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
      rcases hx2 with rfl | rfl
      · exact Or.inl ((RS.mem_endpoints_iff_mem_incidentEdges).1 hx.1)
      · exact Or.inr ((RS.mem_endpoints_iff_mem_incidentEdges).1 hx.1)
    rcases D.eq_of_mem_incident hD hinc with rfl | rfl | rfl | rfl
    · simp
    · simp
    · exfalso
      rw [D.endpoints_e hD, Finset.inter_self, Finset.card_pair huv] at hcard
      omega
    · exfalso
      rw [D.endpoints_f hD, Finset.inter_self, Finset.card_pair huv] at hcard
      omega
  · intro hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl
    · rw [D.endpoints_outerU hD]
      have : ({D.u, D.uFar hD} : Finset V) ∩ {D.u, D.v} = {D.u} := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hx | hx, hx'⟩
          · exact hx
          · exfalso; apply huFar; rw [← hx]
            simp only [Finset.mem_insert, Finset.mem_singleton]; exact hx'
        · rintro rfl; exact ⟨Or.inl rfl, Or.inl rfl⟩
      rw [this, Finset.card_singleton]
    · rw [D.endpoints_outerV hD]
      have : ({D.v, D.vFar hD} : Finset V) ∩ {D.u, D.v} = {D.v} := by
        ext x
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨hx | hx, hx'⟩
          · exact hx
          · exfalso; apply hvFar; rw [← hx]
            simp only [Finset.mem_insert, Finset.mem_singleton]; exact hx'
        · rintro rfl; exact ⟨Or.inl rfl, Or.inr rfl⟩
      rw [this, Finset.card_singleton]

/-! ## A vertex set with one boundary edge is separated by a bridge -/

/-- Adjacency avoiding the removed edge never leaves a vertex set whose only
boundary edge is that removed edge. -/
theorem mem_of_adj_edgeDeleted (S : Finset V) (g : E)
    (hb : RS.vertexSideEdgeBoundary S = {g}) {x y : V} (hx : x ∈ S)
    (hadj : (edgeDeletedPrimalGraph RS g).Adj x y) : y ∈ S := by
  classical
  obtain ⟨d, hne, hxd, hyd⟩ := hadj
  by_contra hy
  apply hne
  have hmem : RS.edgeOf d ∈ RS.vertexSideEdgeBoundary S := by
    rw [RS.mem_vertexSideEdgeBoundary_iff]
    have hd : d ∈ RS.dartsOn (RS.edgeOf d) := RS.mem_dartsOn.2 rfl
    rw [RS.endpoints_eq_pair_of_mem hd, hxd, hyd]
    have : ({x, y} : Finset V) ∩ S = {x} := by
      ext z
      simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hz⟩
        · rfl
        · exact absurd hz hy
      · rintro rfl; exact ⟨Or.inl rfl, hx⟩
    rw [this, Finset.card_singleton]
  rw [hb] at hmem
  simpa using hmem

theorem mem_of_reachable_edgeDeleted (S : Finset V) (g : E)
    (hb : RS.vertexSideEdgeBoundary S = {g}) {x y : V} (hx : x ∈ S)
    (hreach : (edgeDeletedPrimalGraph RS g).Reachable x y) : y ∈ S := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => exact hx
  | tail _ hadj ih => exact mem_of_adj_edgeDeleted S g hb ih hadj

/-- **A single boundary edge is a bridge.**  So a bridge-free map has no
vertex set whose boundary is one edge with an endpoint outside. -/
theorem not_boundary_singleton_of_edgeBridgeFree (hfree : EdgeBridgeFree RS)
    (S : Finset V) (g : E) (hb : RS.vertexSideEdgeBoundary S = {g}) : False := by
  classical
  have hg : g ∈ RS.vertexSideEdgeBoundary S := by rw [hb]; simp
  rw [RS.mem_vertexSideEdgeBoundary_iff] at hg
  obtain ⟨d, hd⟩ := RS.dartsOn_nonempty g
  have hends := RS.endpoints_eq_pair_of_mem hd
  have hedge : RS.edgeOf d = g := RS.mem_dartsOn.1 hd
  -- exactly one endpoint of `g` lies in `S`; say which
  have hreach := hfree d
  rw [hedge] at hreach
  by_cases hin : RS.vertOf d ∈ S
  · have hout : RS.vertOf (RS.alpha d) ∉ S := by
      intro hcon
      rw [hends] at hg
      have : ({RS.vertOf d, RS.vertOf (RS.alpha d)} : Finset V) ∩ S =
          {RS.vertOf d, RS.vertOf (RS.alpha d)} := by
        rw [Finset.inter_eq_left]
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl <;> assumption
      rw [this, Finset.card_pair (RS.no_self_loops d)] at hg
      omega
    exact hout (mem_of_reachable_edgeDeleted S g hb hin hreach)
  · have hin' : RS.vertOf (RS.alpha d) ∈ S := by
      by_contra hcon
      rw [hends] at hg
      have : ({RS.vertOf d, RS.vertOf (RS.alpha d)} : Finset V) ∩ S = ∅ := by
        rw [Finset.eq_empty_iff_forall_notMem]
        intro z hz
        rw [Finset.mem_inter] at hz
        have hz1 := hz.1
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz1
        rcases hz1 with rfl | rfl
        · exact hin hz.2
        · exact hcon hz.2
      rw [this, Finset.card_empty] at hg
      omega
    exact hin (mem_of_reachable_edgeDeleted S g hb hin' hreach.symm)

/-! ## The far endpoints differ -/

/-- Any dart on `outerU` sits at `u` or at its far endpoint. -/
theorem vertOf_eq_of_edgeOf_eq_outerU (hD : D.WellFormed RS) {d : RS.D}
    (h : RS.edgeOf d = D.outerU) : RS.vertOf d = D.u ∨ RS.vertOf d = D.uFar hD := by
  have hd : d ∈ RS.dartsOn D.outerU := RS.mem_dartsOn.2 h
  have hp : D.pₐ hD ∈ RS.dartsOn D.outerU := RS.mem_dartsOn.2 (D.edgeOf_pₐ hD)
  rw [RS.dartsOn_eq_pair_of_mem hp, D.alpha_pₐ hD] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · exact Or.inl (D.vertOf_pₐ hD)
  · exact Or.inr rfl

theorem vertOf_eq_of_edgeOf_eq_outerV (hD : D.WellFormed RS) {d : RS.D}
    (h : RS.edgeOf d = D.outerV) : RS.vertOf d = D.v ∨ RS.vertOf d = D.vFar hD := by
  have hd : d ∈ RS.dartsOn D.outerV := RS.mem_dartsOn.2 h
  have hq : D.qᵦ hD ∈ RS.dartsOn D.outerV := RS.mem_dartsOn.2 (D.edgeOf_qᵦ hD)
  rw [RS.dartsOn_eq_pair_of_mem hq, D.alpha_qᵦ hD] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl
  · exact Or.inl (D.vertOf_qᵦ hD)
  · exact Or.inr rfl

/-- **The far endpoints differ.**  If both exterior edges met one vertex `w`,
then `{u, v, w}` would meet the rest of the map along `w`'s third edge alone —
a bridge. -/
theorem uFar_ne_vFar (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (hfree : EdgeBridgeFree RS) (houter : D.vFar hD ≠ D.u) :
    D.uFar hD ≠ D.vFar hD := by
  classical
  intro hw
  set w := D.uFar hD with hwdef
  have hwv : w ≠ D.v := D.uFar_ne_v hD hCubic houter
  have hwu : w ≠ D.u := D.uFar_ne_u hD
  have houterUV := D.outerU_ne_outerV hD houter
  -- the two exterior darts at `w` and the third dart there
  have ha' : RS.vertOf (D.a' hD) = w := rfl
  have hb' : RS.vertOf (D.b' hD) = w := hw.symm
  have hab : D.a' hD ≠ D.b' hD := by
    intro h
    apply houterUV
    rw [← D.edgeOf_a' hD, ← D.edgeOf_b' hD, h]
  have hcard : (RS.dartsAt w).card = 3 := hCubic w
  have ha'mem : D.a' hD ∈ RS.dartsAt w := by simp [RotationSystem.dartsAt, ha']
  have hb'mem : D.b' hD ∈ RS.dartsAt w := by simp [RotationSystem.dartsAt, hb']
  obtain ⟨d₃, hd₃mem, hd₃a, hd₃b⟩ : ∃ d₃ ∈ RS.dartsAt w, d₃ ≠ D.a' hD ∧ d₃ ≠ D.b' hD := by
    have hpair : ({D.a' hD, D.b' hD} : Finset RS.D) ⊆ RS.dartsAt w := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    have hlt : ({D.a' hD, D.b' hD} : Finset RS.D).card < (RS.dartsAt w).card := by
      rw [Finset.card_pair hab, hcard]; omega
    obtain ⟨d₃, hd₃, hnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    exact ⟨d₃, hd₃, hnot.1, hnot.2⟩
  have hd₃w : RS.vertOf d₃ = w := by simpa [RotationSystem.dartsAt] using hd₃mem
  set g := RS.edgeOf d₃ with hgdef
  -- `g` is none of the four named edges
  have hgU : g ≠ D.outerU := by
    intro h
    have hd : d₃ ∈ RS.dartsOn D.outerU := RS.mem_dartsOn.2 h
    have hp : D.pₐ hD ∈ RS.dartsOn D.outerU := RS.mem_dartsOn.2 (D.edgeOf_pₐ hD)
    rw [RS.dartsOn_eq_pair_of_mem hp, D.alpha_pₐ hD] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact hwu (by rw [← hd₃w, D.vertOf_pₐ hD])
    · exact hd₃a rfl
  have hgV : g ≠ D.outerV := by
    intro h
    have hd : d₃ ∈ RS.dartsOn D.outerV := RS.mem_dartsOn.2 h
    have hq : D.qᵦ hD ∈ RS.dartsOn D.outerV := RS.mem_dartsOn.2 (D.edgeOf_qᵦ hD)
    rw [RS.dartsOn_eq_pair_of_mem hq, D.alpha_qᵦ hD] at hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact hwv (by rw [← hd₃w, D.vertOf_qᵦ hD])
    · exact hd₃b rfl
  have hwg : w ∈ RS.endpoints g := by
    rw [RS.mem_endpoints_iff]
    exact ⟨d₃, RS.mem_dartsOn.2 rfl, hd₃w⟩
  have hgE : g ≠ D.e := by
    intro h; rw [h, D.endpoints_e hD] at hwg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwg
    rcases hwg with h' | h'
    · exact hwu h'
    · exact hwv h'
  have hgF : g ≠ D.f := by
    intro h; rw [h, D.endpoints_f hD] at hwg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hwg
    rcases hwg with h' | h'
    · exact hwu h'
    · exact hwv h'
  -- the far end of `g` lies outside `{u, v, w}`
  set w'' := RS.vertOf (RS.alpha d₃) with hw''def
  have hw''w : w'' ≠ w := by
    intro h; exact RS.no_self_loops d₃ (by rw [hd₃w]; exact h.symm)
  have hgnot : ¬ (g ∈ RS.incidentEdges D.u ∨ g ∈ RS.incidentEdges D.v) := by
    intro hinc
    rcases D.eq_of_mem_incident hD hinc with h | h | h | h
    · exact hgU h
    · exact hgV h
    · exact hgE h
    · exact hgF h
  have hw''u : w'' ≠ D.u := by
    intro h
    apply hgnot
    left
    rw [← RS.mem_endpoints_iff_mem_incidentEdges, ← h, RS.mem_endpoints_iff]
    exact ⟨RS.alpha d₃, RS.alpha_mem_dartsOn (RS.mem_dartsOn.2 rfl), rfl⟩
  have hw''v : w'' ≠ D.v := by
    intro h
    apply hgnot
    right
    rw [← RS.mem_endpoints_iff_mem_incidentEdges, ← h, RS.mem_endpoints_iff]
    exact ⟨RS.alpha d₃, RS.alpha_mem_dartsOn (RS.mem_dartsOn.2 rfl), rfl⟩
  -- the darts at `w` are exactly the three named ones
  have hdartsAt : RS.dartsAt w = {D.a' hD, D.b' hD, d₃} := by
    have hsub : ({D.a' hD, D.b' hD, d₃} : Finset RS.D) ⊆ RS.dartsAt w := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have hc3 : ({D.a' hD, D.b' hD, d₃} : Finset RS.D).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair hd₃b.symm]
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, hd₃a.symm⟩
    exact (Finset.eq_of_subset_of_card_le hsub (by rw [hcard, hc3])).symm
  -- so `{u, v, w}` has boundary exactly `{g}`
  let S : Finset V := {D.u, D.v, w}
  have hb : RS.vertexSideEdgeBoundary S = {g} := by
    ext h
    rw [RS.mem_vertexSideEdgeBoundary_iff]
    constructor
    · intro hcard1
      have hne : (RS.endpoints h ∩ S).Nonempty := by
        rw [← Finset.card_pos, hcard1]; exact Nat.one_pos
      obtain ⟨x, hx⟩ := hne
      rw [Finset.mem_inter] at hx
      have hxS := hx.2
      simp only [S, Finset.mem_insert, Finset.mem_singleton] at hxS
      -- an edge at `u` or `v` has both ends in `S`
      have hboth : ∀ h' : E, (h' ∈ RS.incidentEdges D.u ∨ h' ∈ RS.incidentEdges D.v) →
          (RS.endpoints h' ∩ S).card ≠ 1 := by
        intro h' hinc hone
        have hsub : RS.endpoints h' ⊆ S := by
          rcases D.eq_of_mem_incident hD hinc with rfl | rfl | rfl | rfl
          · rw [D.endpoints_outerU hD]; intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            simp only [S, Finset.mem_insert, Finset.mem_singleton]
            rcases hz with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inr rfl)
          · rw [D.endpoints_outerV hD]; intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            simp only [S, Finset.mem_insert, Finset.mem_singleton]
            rcases hz with rfl | rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr hw.symm)
          · rw [D.endpoints_e hD]; intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            simp only [S, Finset.mem_insert, Finset.mem_singleton]
            rcases hz with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
          · rw [D.endpoints_f hD]; intro z hz
            simp only [Finset.mem_insert, Finset.mem_singleton] at hz
            simp only [S, Finset.mem_insert, Finset.mem_singleton]
            rcases hz with rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
        rw [Finset.inter_eq_left.2 hsub, RS.endpoints_card_two] at hone
        omega
      rcases hxS with rfl | rfl | rfl
      · exact absurd hcard1 (hboth h (Or.inl ((RS.mem_endpoints_iff_mem_incidentEdges).1 hx.1)))
      · exact absurd hcard1 (hboth h (Or.inr ((RS.mem_endpoints_iff_mem_incidentEdges).1 hx.1)))
      · -- `h` is at `w`, hence one of the three edges there
        have hinc : h ∈ RS.incidentEdges w := (RS.mem_endpoints_iff_mem_incidentEdges).1 hx.1
        rw [RS.mem_incidentEdges_iff] at hinc
        obtain ⟨d, hdh, hdw⟩ := hinc
        have hd : d ∈ RS.dartsAt w := by simp [RotationSystem.dartsAt, hdw]
        rw [hdartsAt] at hd
        simp only [Finset.mem_insert, Finset.mem_singleton] at hd
        rcases hd with rfl | rfl | rfl
        · exfalso
          exact hboth h (Or.inl ((RS.mem_endpoints_iff_mem_incidentEdges).1 (by
            rw [← hdh, D.edgeOf_a' hD, D.endpoints_outerU hD]; simp))) hcard1
        · exfalso
          exact hboth h (Or.inr ((RS.mem_endpoints_iff_mem_incidentEdges).1 (by
            rw [← hdh, D.edgeOf_b' hD, D.endpoints_outerV hD]; simp))) hcard1
        · rw [Finset.mem_singleton, ← hdh]
    · intro hg
      rw [Finset.mem_singleton] at hg
      subst hg
      have hd : d₃ ∈ RS.dartsOn (RS.edgeOf d₃) := RS.mem_dartsOn.2 rfl
      rw [RS.endpoints_eq_pair_of_mem hd, hd₃w]
      have : ({w, w''} : Finset V) ∩ S = {w} := by
        ext z
        simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton, S]
        constructor
        · rintro ⟨rfl | rfl, hz⟩
          · rfl
          · exfalso
            rcases hz with hz | hz | hz
            · exact hw''u hz
            · exact hw''v hz
            · exact hw''w hz
        · rintro rfl
          exact ⟨Or.inl rfl, Or.inr (Or.inr rfl)⟩
      rw [this, Finset.card_singleton]
  exact not_boundary_singleton_of_edgeBridgeFree hfree S g hb

/-! ## The complement is connected -/

/-- Adjacency in the primal graph that stays away from the digon vertices. -/
def Away (D : @DigonPatchData V E) (RS : RotationSystem V E) (x y : V) : Prop :=
  (rotationPrimalGraph RS).Adj x y ∧ x ∉ ({D.u, D.v} : Finset V) ∧ y ∉ ({D.u, D.v} : Finset V)

/-- Reachability away from the digon vertices. -/
def AwayReach (D : @DigonPatchData V E) (RS : RotationSystem V E) : V → V → Prop :=
  Relation.ReflTransGen (Away D RS)

theorem awayReach_symm {x y : V} (h : AwayReach D RS x y) : AwayReach D RS y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
      exact Relation.ReflTransGen.trans
        (Relation.ReflTransGen.single ⟨hstep.1.symm, hstep.2.2, hstep.2.1⟩) ih

/-- A vertex outside the digon adjacent to `u` is the far endpoint of `outerU`,
and the adjacency runs along `outerU`. -/
theorem eq_uFar_of_adj (hD : D.WellFormed RS) (hCubic : RS.IsCubic) {c : V}
    (hc : c ∉ ({D.u, D.v} : Finset V)) {d : RS.D}
    (hdu : RS.vertOf d = D.u) (hdc : RS.vertOf (RS.alpha d) = c) :
    c = D.uFar hD ∧ d = D.pₐ hD := by
  have hd : d ∈ RS.dartsAt D.u := by simp [RotationSystem.dartsAt, hdu]
  rw [D.dartsAt_u_eq hD hCubic] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  rcases hd with rfl | rfl | rfl
  · exfalso; apply hc.2; rw [← hdc, D.alpha_p₁ hD, D.vertOf_q₁ hD]
  · exfalso; apply hc.2; rw [← hdc, D.alpha_p₂ hD, D.vertOf_q₂ hD]
  · refine ⟨?_, rfl⟩
    rw [← hdc, D.alpha_pₐ hD]; rfl

theorem eq_vFar_of_adj (hD : D.WellFormed RS) (hCubic : RS.IsCubic) {c : V}
    (hc : c ∉ ({D.u, D.v} : Finset V)) {d : RS.D}
    (hdv : RS.vertOf d = D.v) (hdc : RS.vertOf (RS.alpha d) = c) :
    c = D.vFar hD ∧ d = D.qᵦ hD := by
  have hd : d ∈ RS.dartsAt D.v := by simp [RotationSystem.dartsAt, hdv]
  rw [D.dartsAt_v_eq hD hCubic] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  rcases hd with rfl | rfl | rfl
  · exfalso; apply hc.1; rw [← hdc, D.alpha_q₁ hD, D.vertOf_p₁ hD]
  · exfalso; apply hc.1; rw [← hdc, D.alpha_q₂ hD, D.vertOf_p₂ hD]
  · refine ⟨?_, rfl⟩
    rw [← hdc, D.alpha_qᵦ hD]; rfl

/-- **The two far endpoints are joined away from the digon.**  Bridge-freeness
at `outerU` gives a walk from `u` back to `u'` avoiding `outerU`; it can only
leave `{u, v}` through `outerV`, so it carries a `v'`–`u'` walk avoiding
`{u, v}`. -/
theorem awayReach_uFar_vFar (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (hfree : EdgeBridgeFree RS) (houter : D.vFar hD ≠ D.u) :
    AwayReach D RS (D.uFar hD) (D.vFar hD) := by
  classical
  have hreach := hfree (D.pₐ hD)
  rw [D.edgeOf_pₐ hD, D.vertOf_pₐ hD, D.alpha_pₐ hD] at hreach
  change (edgeDeletedPrimalGraph RS D.outerU).Reachable D.u (D.uFar hD) at hreach
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  -- invariant: outside the digon we are reachable from `v'`
  have key : ∀ c, Relation.ReflTransGen (edgeDeletedPrimalGraph RS D.outerU).Adj D.u c →
      c ∉ ({D.u, D.v} : Finset V) → AwayReach D RS (D.vFar hD) c := by
    intro c hc
    induction hc with
    | refl => intro h; exact absurd (by simp) h
    | @tail b c _ hadj ih =>
        intro hcnot
        obtain ⟨d, hne, hdb, hdc⟩ := hadj
        by_cases hb : b ∈ ({D.u, D.v} : Finset V)
        · -- leaving the digon: only through `outerV`
          have hb' := hb
          simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
          rcases hb' with rfl | rfl
          · exfalso
            obtain ⟨-, rfl⟩ := D.eq_uFar_of_adj hD hCubic hcnot hdb hdc
            exact hne (D.edgeOf_pₐ hD)
          · obtain ⟨rfl, -⟩ := D.eq_vFar_of_adj hD hCubic hcnot hdb hdc
            exact Relation.ReflTransGen.refl
        · exact (ih hb).tail ⟨(rotationPrimalGraph_adj_iff RS).2 ⟨d, hdb, hdc⟩, hb, hcnot⟩
  exact awayReach_symm D (key _ hreach (D.uFar_not_mem hD hCubic houter))

/-- **Every walk can be rerouted around the digon.** -/
theorem awayReach_of_reachable (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (hfree : EdgeBridgeFree RS) (houter : D.vFar hD ≠ D.u) {x y : V}
    (hx : x ∉ ({D.u, D.v} : Finset V)) (hy : y ∉ ({D.u, D.v} : Finset V))
    (hreach : (rotationPrimalGraph RS).Reachable x y) : AwayReach D RS x y := by
  classical
  have hlink := D.awayReach_uFar_vFar hD hCubic hfree houter
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have key : ∀ c, Relation.ReflTransGen (rotationPrimalGraph RS).Adj x c →
      (c ∉ ({D.u, D.v} : Finset V) → AwayReach D RS x c) ∧
        (c ∈ ({D.u, D.v} : Finset V) →
          AwayReach D RS x (D.uFar hD) ∧ AwayReach D RS x (D.vFar hD)) := by
    intro c hc
    induction hc with
    | refl => exact ⟨fun _ => Relation.ReflTransGen.refl, fun h => absurd h hx⟩
    | @tail b c _ hadj ih =>
        obtain ⟨d, hdb, hdc⟩ := (rotationPrimalGraph_adj_iff RS).1 hadj
        by_cases hb : b ∈ ({D.u, D.v} : Finset V)
        · -- currently inside the digon
          refine ⟨fun hcnot => ?_, fun _ => ih.2 hb⟩
          have hb' := hb
          simp only [Finset.mem_insert, Finset.mem_singleton] at hb'
          rcases hb' with rfl | rfl
          · obtain ⟨rfl, -⟩ := D.eq_uFar_of_adj hD hCubic hcnot hdb hdc
            exact (ih.2 hb).1
          · obtain ⟨rfl, -⟩ := D.eq_vFar_of_adj hD hCubic hcnot hdb hdc
            exact (ih.2 hb).2
        · -- currently outside the digon
          refine ⟨fun hcnot => (ih.1 hb).tail ⟨hadj, hb, hcnot⟩, fun hc => ?_⟩
          have hc' := hc
          simp only [Finset.mem_insert, Finset.mem_singleton] at hc'
          have hadj' := (rotationPrimalGraph_adj_iff RS).1 hadj.symm
          obtain ⟨d', hdc', hdb'⟩ := hadj'
          rcases hc' with rfl | rfl
          · obtain ⟨rfl, -⟩ := D.eq_uFar_of_adj hD hCubic hb hdc' hdb'
            exact ⟨ih.1 hb, (ih.1 hb).trans hlink⟩
          · obtain ⟨rfl, -⟩ := D.eq_vFar_of_adj hD hCubic hb hdc' hdb'
            exact ⟨(ih.1 hb).trans (awayReach_symm D hlink), ih.1 hb⟩
  exact (key y hreach).1 hy

/-- **The complement of the digon is connected**, as an induced subgraph of the
primal graph. -/
theorem complement_connected (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (hfree : EdgeBridgeFree RS) (hconn : (rotationPrimalGraph RS).Connected)
    (houter : D.vFar hD ≠ D.u) :
    ((rotationPrimalGraph RS).induce {vertex | vertex ∈ ({D.u, D.v} : Finset V)ᶜ}).Connected := by
  classical
  have hmem : ∀ z : V, z ∈ {vertex | vertex ∈ ({D.u, D.v} : Finset V)ᶜ} ↔
      z ∉ ({D.u, D.v} : Finset V) := fun z => by simp
  haveI : Nonempty {vertex // vertex ∈ {vertex | vertex ∈ ({D.u, D.v} : Finset V)ᶜ}} :=
    ⟨⟨D.uFar hD, (hmem _).2 (D.uFar_not_mem hD hCubic houter)⟩⟩
  refine ⟨?_⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩
  have hx' := (hmem x).1 hx
  have hy' := (hmem y).1 hy
  have haway := D.awayReach_of_reachable hD hCubic hfree houter hx' hy' (hconn x y)
  -- transport an away-reachability to the induced subgraph
  have key : ∀ z, AwayReach D RS x z → ∀ hz : z ∉ ({D.u, D.v} : Finset V),
      ((rotationPrimalGraph RS).induce {vertex | vertex ∈ ({D.u, D.v} : Finset V)ᶜ}).Reachable
        ⟨x, hx⟩ ⟨z, (hmem z).2 hz⟩ := by
    intro z hz
    induction hz with
    | refl => intro _; exact SimpleGraph.Reachable.refl _
    | @tail b c _ hstep ih =>
        intro hc
        refine (ih hstep.2.1).trans (SimpleGraph.Adj.reachable ?_)
        exact (SimpleGraph.comap_adj).2 hstep.1
  exact key y haway hy'

/-! ## The exact two-edge cut -/

/-- The digon side. -/
def side (D : @DigonPatchData V E) : Finset V := {D.u, D.v}

theorem side_card (hD : D.WellFormed RS) : (D.side).card = 2 :=
  Finset.card_pair hD.1

/-- **A digon is an exact two-edge cut** with the two exterior edges as its
crossing edges. -/
def twoEdgeCut (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (hfree : EdgeBridgeFree RS) (houter : D.vFar hD ≠ D.u) :
    RS.TwoEdgeCutPairData where
  side := D.side
  leftEdge := D.outerU
  rightEdge := D.outerV
  edges_ne := D.outerU_ne_outerV hD houter
  boundary_eq := D.boundary_eq hD hCubic houter
  sideRetainedEndpointsDistinct := by
    intro left right hleft hright
    have hl := D.vertOf_eq_of_edgeOf_eq_outerU hD hleft
    have hr := D.vertOf_eq_of_edgeOf_eq_outerV hD hright
    have hlmem : RS.vertOf left.1.1 ∈ D.side := left.1.2
    have hrmem : RS.vertOf right.1.1 ∈ D.side := right.1.2
    rcases hl with hl | hl
    · rcases hr with hr | hr
      · rw [hl, hr]; exact hD.1
      · exfalso; rw [hr] at hrmem; exact D.vFar_not_mem hD houter hrmem
    · exfalso; rw [hl] at hlmem; exact D.uFar_not_mem hD hCubic houter hlmem
  complementRetainedEndpointsDistinct := by
    intro left right hleft hright
    have hl := D.vertOf_eq_of_edgeOf_eq_outerU hD hleft
    have hr := D.vertOf_eq_of_edgeOf_eq_outerV hD hright
    have hlmem : RS.vertOf left.1.1 ∈ D.sideᶜ := left.1.2
    have hrmem : RS.vertOf right.1.1 ∈ D.sideᶜ := right.1.2
    rw [Finset.mem_compl] at hlmem hrmem
    rcases hl with hl | hl
    · exfalso; apply hlmem; rw [hl]; simp [side]
    · rcases hr with hr | hr
      · exfalso; apply hrmem; rw [hr]; simp [side]
      · rw [hl, hr]; exact D.uFar_ne_vFar hD hCubic hfree houter

/-- The digon side is connected: `u` and `v` are adjacent. -/
theorem side_connected (hD : D.WellFormed RS) :
    ((rotationPrimalGraph RS).induce {vertex | vertex ∈ D.side}).Connected := by
  have hadj : (rotationPrimalGraph RS).Adj D.u D.v :=
    (rotationPrimalGraph_adj_iff RS).2 ⟨D.p₁ hD, D.vertOf_p₁ hD, by
      rw [D.alpha_p₁ hD, D.vertOf_q₁ hD]⟩
  have : {vertex | vertex ∈ D.side} = ({D.u, D.v} : Set V) := by
    ext z; simp [side]
  rw [this]
  exact SimpleGraph.induce_pair_connected_of_adj hadj

end DigonPatchData

end

end RotationSystem

end Mettapedia.GraphTheory.FourColor
