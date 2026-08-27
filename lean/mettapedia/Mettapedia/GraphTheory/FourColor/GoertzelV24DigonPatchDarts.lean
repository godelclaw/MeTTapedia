import Mettapedia.GraphTheory.FourColor.GoertzelV24DigonFaceLocal
import Mettapedia.GraphTheory.FourColor.GoertzelV24DigonProfile
import Mettapedia.GraphTheory.FourColor.GoertzelV24InducedHexCorridorTypes

/-!
# Canonical darts of a cubic digon patch

`DigonPatchData` names the two parallel edges, the two exterior edges, and
their two endpoint vertices.  Face surgery needs actual darts.  This file
provides a proof-irrelevant canonical dart at a named edge endpoint and uses
it to expose the eight darts of a digon and its two attachments.

No planarity statement occurs here.  The only substantive endpoint fact is
that the opposite dart of either parallel edge is based at the other named
digon vertex; this follows from the common two-element endpoint set.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace RotationSystem

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A canonical dart of `edge` based at a specified endpoint. -/
def dartAtEndpoint (RS : RotationSystem V E) (edge : E) (vertex : V)
    (hvertex : vertex ∈ RS.endpoints edge) : RS.D :=
  Classical.choose ((RS.mem_endpoints_iff).1 hvertex)

theorem dartAtEndpoint_mem_dartsOn
    (RS : RotationSystem V E) (edge : E) (vertex : V)
    (hvertex : vertex ∈ RS.endpoints edge) :
    RS.dartAtEndpoint edge vertex hvertex ∈ RS.dartsOn edge :=
  (Classical.choose_spec ((RS.mem_endpoints_iff).1 hvertex)).1

@[simp]
theorem dartAtEndpoint_edgeOf
    (RS : RotationSystem V E) (edge : E) (vertex : V)
    (hvertex : vertex ∈ RS.endpoints edge) :
    RS.edgeOf (RS.dartAtEndpoint edge vertex hvertex) = edge :=
  (RS.mem_dartsOn).1 (RS.dartAtEndpoint_mem_dartsOn edge vertex hvertex)

@[simp]
theorem dartAtEndpoint_vertOf
    (RS : RotationSystem V E) (edge : E) (vertex : V)
    (hvertex : vertex ∈ RS.endpoints edge) :
    RS.vertOf (RS.dartAtEndpoint edge vertex hvertex) = vertex :=
  (Classical.choose_spec ((RS.mem_endpoints_iff).1 hvertex)).2

namespace DigonPatchData

variable {RS : RotationSystem V E} (D : @DigonPatchData V E)

theorem e_mem_incident_u (hD : D.WellFormed RS) :
    D.e ∈ RS.incidentEdges D.u := by
  rw [hD.2.2.1]
  simp

theorem f_mem_incident_u (hD : D.WellFormed RS) :
    D.f ∈ RS.incidentEdges D.u := by
  rw [hD.2.2.1]
  simp

theorem outerU_mem_incident_u (hD : D.WellFormed RS) :
    D.outerU ∈ RS.incidentEdges D.u := by
  rw [hD.2.2.1]
  simp

theorem e_mem_incident_v (hD : D.WellFormed RS) :
    D.e ∈ RS.incidentEdges D.v := by
  rw [hD.2.2.2]
  simp

theorem f_mem_incident_v (hD : D.WellFormed RS) :
    D.f ∈ RS.incidentEdges D.v := by
  rw [hD.2.2.2]
  simp

theorem outerV_mem_incident_v (hD : D.WellFormed RS) :
    D.outerV ∈ RS.incidentEdges D.v := by
  rw [hD.2.2.2]
  simp

noncomputable def p₁ (hD : D.WellFormed RS) : RS.D :=
  RS.dartAtEndpoint D.e D.u
    ((RS.mem_endpoints_iff_mem_incidentEdges).2 (D.e_mem_incident_u hD))

noncomputable def p₂ (hD : D.WellFormed RS) : RS.D :=
  RS.dartAtEndpoint D.f D.u
    ((RS.mem_endpoints_iff_mem_incidentEdges).2 (D.f_mem_incident_u hD))

noncomputable def pₐ (hD : D.WellFormed RS) : RS.D :=
  RS.dartAtEndpoint D.outerU D.u
    ((RS.mem_endpoints_iff_mem_incidentEdges).2 (D.outerU_mem_incident_u hD))

noncomputable def q₁ (hD : D.WellFormed RS) : RS.D :=
  RS.alpha (D.p₁ hD)

noncomputable def q₂ (hD : D.WellFormed RS) : RS.D :=
  RS.alpha (D.p₂ hD)

noncomputable def a' (hD : D.WellFormed RS) : RS.D :=
  RS.alpha (D.pₐ hD)

noncomputable def qᵦ (hD : D.WellFormed RS) : RS.D :=
  RS.dartAtEndpoint D.outerV D.v
    ((RS.mem_endpoints_iff_mem_incidentEdges).2 (D.outerV_mem_incident_v hD))

noncomputable def b' (hD : D.WellFormed RS) : RS.D :=
  RS.alpha (D.qᵦ hD)

@[simp] theorem edgeOf_p₁ (hD : D.WellFormed RS) :
    RS.edgeOf (D.p₁ hD) = D.e := by simp [p₁]

@[simp] theorem edgeOf_p₂ (hD : D.WellFormed RS) :
    RS.edgeOf (D.p₂ hD) = D.f := by simp [p₂]

@[simp] theorem edgeOf_pₐ (hD : D.WellFormed RS) :
    RS.edgeOf (D.pₐ hD) = D.outerU := by simp [pₐ]

@[simp] theorem edgeOf_qᵦ (hD : D.WellFormed RS) :
    RS.edgeOf (D.qᵦ hD) = D.outerV := by simp [qᵦ]

@[simp] theorem edgeOf_q₁ (hD : D.WellFormed RS) :
    RS.edgeOf (D.q₁ hD) = D.e := by
  rw [q₁, RS.edge_alpha, D.edgeOf_p₁ hD]

@[simp] theorem edgeOf_q₂ (hD : D.WellFormed RS) :
    RS.edgeOf (D.q₂ hD) = D.f := by
  rw [q₂, RS.edge_alpha, D.edgeOf_p₂ hD]

@[simp] theorem edgeOf_a' (hD : D.WellFormed RS) :
    RS.edgeOf (D.a' hD) = D.outerU := by
  rw [a', RS.edge_alpha, D.edgeOf_pₐ hD]

@[simp] theorem edgeOf_b' (hD : D.WellFormed RS) :
    RS.edgeOf (D.b' hD) = D.outerV := by
  rw [b', RS.edge_alpha, D.edgeOf_qᵦ hD]

@[simp] theorem vertOf_p₁ (hD : D.WellFormed RS) :
    RS.vertOf (D.p₁ hD) = D.u := by simp [p₁]

@[simp] theorem vertOf_p₂ (hD : D.WellFormed RS) :
    RS.vertOf (D.p₂ hD) = D.u := by simp [p₂]

@[simp] theorem vertOf_pₐ (hD : D.WellFormed RS) :
    RS.vertOf (D.pₐ hD) = D.u := by simp [pₐ]

@[simp] theorem vertOf_qᵦ (hD : D.WellFormed RS) :
    RS.vertOf (D.qᵦ hD) = D.v := by simp [qᵦ]

@[simp] theorem alpha_p₁ (hD : D.WellFormed RS) :
    RS.alpha (D.p₁ hD) = D.q₁ hD := rfl

@[simp] theorem alpha_p₂ (hD : D.WellFormed RS) :
    RS.alpha (D.p₂ hD) = D.q₂ hD := rfl

@[simp] theorem alpha_pₐ (hD : D.WellFormed RS) :
    RS.alpha (D.pₐ hD) = D.a' hD := rfl

@[simp] theorem alpha_qᵦ (hD : D.WellFormed RS) :
    RS.alpha (D.qᵦ hD) = D.b' hD := rfl

@[simp] theorem alpha_q₁ (hD : D.WellFormed RS) :
    RS.alpha (D.q₁ hD) = D.p₁ hD := RS.alpha_involutive _

@[simp] theorem alpha_q₂ (hD : D.WellFormed RS) :
    RS.alpha (D.q₂ hD) = D.p₂ hD := RS.alpha_involutive _

@[simp] theorem alpha_a' (hD : D.WellFormed RS) :
    RS.alpha (D.a' hD) = D.pₐ hD := RS.alpha_involutive _

@[simp] theorem alpha_b' (hD : D.WellFormed RS) :
    RS.alpha (D.b' hD) = D.qᵦ hD := RS.alpha_involutive _

/-- The opposite dart of the first parallel edge is based at the other
digon vertex. -/
@[simp] theorem vertOf_q₁ (hD : D.WellFormed RS) :
    RS.vertOf (D.q₁ hD) = D.v := by
  have hv : D.v ∈ RS.endpoints D.e :=
    (RS.mem_endpoints_iff_mem_incidentEdges).2 (D.e_mem_incident_v hD)
  have hpMem : D.p₁ hD ∈ RS.dartsOn D.e := by
    apply RS.mem_dartsOn.mpr
    exact D.edgeOf_p₁ hD
  rw [RS.endpoints_eq_pair_of_mem hpMem] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hvu | hvq
  · exfalso
    apply hD.1
    rw [← D.vertOf_p₁ hD]
    exact hvu.symm
  · exact hvq.symm

/-- The opposite dart of the second parallel edge is based at the other
digon vertex. -/
@[simp] theorem vertOf_q₂ (hD : D.WellFormed RS) :
    RS.vertOf (D.q₂ hD) = D.v := by
  have hv : D.v ∈ RS.endpoints D.f :=
    (RS.mem_endpoints_iff_mem_incidentEdges).2 (D.f_mem_incident_v hD)
  have hpMem : D.p₂ hD ∈ RS.dartsOn D.f := by
    apply RS.mem_dartsOn.mpr
    exact D.edgeOf_p₂ hD
  rw [RS.endpoints_eq_pair_of_mem hpMem] at hv
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hvu | hvq
  · exfalso
    apply hD.1
    rw [← D.vertOf_p₂ hD]
    exact hvu.symm
  · exact hvq.symm

/-- Cubicity forces the three named incident edges at `u` to be distinct. -/
theorem edges_u_pairwise_ne (hD : D.WellFormed RS) (hCubic : RS.IsCubic) :
    D.outerU ≠ D.e ∧ D.outerU ≠ D.f ∧ D.e ≠ D.f := by
  have hcard : ({D.outerU, D.e, D.f} : Finset E).card = 3 := by
    rw [← hD.2.2.1]
    exact RS.incidentEdges_card_eq_three_of_isCubic hCubic D.u
  constructor
  · intro h
    have hle : ({D.e, D.f} : Finset E).card ≤ 2 := Finset.card_le_two
    have : ({D.e, D.f} : Finset E).card = 3 := by simpa [h] using hcard
    omega
  constructor
  · intro h
    have hle : ({D.e, D.f} : Finset E).card ≤ 2 := Finset.card_le_two
    have : ({D.e, D.f} : Finset E).card = 3 := by
      simpa [h, Finset.pair_comm] using hcard
    omega
  · exact hD.2.1.1

/-- Cubicity forces the three named incident edges at `v` to be distinct. -/
theorem edges_v_pairwise_ne (hD : D.WellFormed RS) (hCubic : RS.IsCubic) :
    D.outerV ≠ D.e ∧ D.outerV ≠ D.f ∧ D.e ≠ D.f := by
  have hcard : ({D.outerV, D.e, D.f} : Finset E).card = 3 := by
    rw [← hD.2.2.2]
    exact RS.incidentEdges_card_eq_three_of_isCubic hCubic D.v
  constructor
  · intro h
    have hle : ({D.e, D.f} : Finset E).card ≤ 2 := Finset.card_le_two
    have : ({D.e, D.f} : Finset E).card = 3 := by simpa [h] using hcard
    omega
  constructor
  · intro h
    have hle : ({D.e, D.f} : Finset E).card ≤ 2 := Finset.card_le_two
    have : ({D.e, D.f} : Finset E).card = 3 := by
      simpa [h, Finset.pair_comm] using hcard
    omega
  · exact hD.2.1.1

theorem p₁_ne_p₂ (hD : D.WellFormed RS) : D.p₁ hD ≠ D.p₂ hD := by
  intro h
  exact hD.2.1.1 (by simpa using congrArg RS.edgeOf h)

theorem q₁_ne_q₂ (hD : D.WellFormed RS) : D.q₁ hD ≠ D.q₂ hD := by
  intro h
  exact hD.2.1.1 (by simpa using congrArg RS.edgeOf h)

/-- The three selected darts are exactly the cubic star at `u`. -/
theorem dartsAt_u_eq (hD : D.WellFormed RS) (hCubic : RS.IsCubic) :
    RS.dartsAt D.u = {D.p₁ hD, D.p₂ hD, D.pₐ hD} := by
  have hne := D.edges_u_pairwise_ne hD hCubic
  have hp₁p₂ : D.p₁ hD ≠ D.p₂ hD := D.p₁_ne_p₂ hD
  have hp₁pₐ : D.p₁ hD ≠ D.pₐ hD := by
    intro h
    exact hne.1 (by simpa using (congrArg RS.edgeOf h).symm)
  have hp₂pₐ : D.p₂ hD ≠ D.pₐ hD := by
    intro h
    exact hne.2.1 (by simpa using (congrArg RS.edgeOf h).symm)
  have hsubset : ({D.p₁ hD, D.p₂ hD, D.pₐ hD} : Finset RS.D) ⊆
      RS.dartsAt D.u := by
    intro dart hdart
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdart
    rcases hdart with rfl | rfl | rfl <;>
      simp [RotationSystem.dartsAt]
  have hcardTriple :
      ({D.p₁ hD, D.p₂ hD, D.pₐ hD} : Finset RS.D).card = 3 := by
    simp [hp₁p₂, hp₁pₐ, hp₂pₐ]
  apply (Finset.eq_of_subset_of_card_le hsubset ?_).symm
  rw [hCubic D.u, hcardTriple]

/-- The three selected darts are exactly the cubic star at `v`. -/
theorem dartsAt_v_eq (hD : D.WellFormed RS) (hCubic : RS.IsCubic) :
    RS.dartsAt D.v = {D.q₁ hD, D.q₂ hD, D.qᵦ hD} := by
  have hne := D.edges_v_pairwise_ne hD hCubic
  have hq₁q₂ : D.q₁ hD ≠ D.q₂ hD := D.q₁_ne_q₂ hD
  have hq₁qᵦ : D.q₁ hD ≠ D.qᵦ hD := by
    intro h
    exact hne.1 (by simpa using (congrArg RS.edgeOf h).symm)
  have hq₂qᵦ : D.q₂ hD ≠ D.qᵦ hD := by
    intro h
    exact hne.2.1 (by simpa using (congrArg RS.edgeOf h).symm)
  have hsubset : ({D.q₁ hD, D.q₂ hD, D.qᵦ hD} : Finset RS.D) ⊆
      RS.dartsAt D.v := by
    intro dart hdart
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdart
    rcases hdart with rfl | rfl | rfl <;>
      simp [RotationSystem.dartsAt]
  have hcardTriple :
      ({D.q₁ hD, D.q₂ hD, D.qᵦ hD} : Finset RS.D).card = 3 := by
    simp [hq₁q₂, hq₁qᵦ, hq₂qᵦ]
  apply (Finset.eq_of_subset_of_card_le hsubset ?_).symm
  rw [hCubic D.v, hcardTriple]

/-- The cyclic rotation at the first digon vertex has one of the two
possible orientations on its three named darts. -/
theorem rho_orientation_u
    (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (hrotation : GoertzelV24FaceDualConnectedness.VertexRotationCyclic RS) :
    (RS.rho (D.p₁ hD) = D.p₂ hD ∧
        RS.rho (D.p₂ hD) = D.pₐ hD ∧
        RS.rho (D.pₐ hD) = D.p₁ hD) ∨
      (RS.rho (D.p₂ hD) = D.p₁ hD ∧
        RS.rho (D.p₁ hD) = D.pₐ hD ∧
        RS.rho (D.pₐ hD) = D.p₂ hD) := by
  have hp₁p₂ : D.p₁ hD ≠ D.p₂ hD := D.p₁_ne_p₂ hD
  have hp₁pₐ : D.p₁ hD ≠ D.pₐ hD := by
    intro h
    exact (D.edges_u_pairwise_ne hD hCubic).1
      (by simpa using (congrArg RS.edgeOf h).symm)
  have hp₂pₐ : D.p₂ hD ≠ D.pₐ hD := by
    intro h
    exact (D.edges_u_pairwise_ne hD hCubic).2.1
      (by simpa using (congrArg RS.edgeOf h).symm)
  have hrhoMem : RS.rho (D.p₁ hD) ∈ RS.dartsAt D.u := by
    simp only [RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact (RS.vert_rho (D.p₁ hD)).trans (D.vertOf_p₁ hD)
  rw [D.dartsAt_u_eq hD hCubic] at hrhoMem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hrhoMem
  rcases hrhoMem with hfixed | hforward | hreverse
  · have hsame := hrotation (D.p₁ hD) (D.p₂ hD) (by simp)
    exact False.elim (hp₁p₂ (hsame.eq_of_left hfixed))
  · have hsame := hrotation (D.p₁ hD) (D.pₐ hD) (by simp)
    have hcube :=
      GoertzelV24InducedHexCorridorTypes.rho_cube_apply_of_isCubic
        RS hCubic hrotation (D.p₁ hD)
    have hcarrier :
        RS.rho (D.p₂ hD) = D.p₁ hD ∨
          RS.rho (D.p₂ hD) = D.p₂ hD ∨
          RS.rho (D.p₂ hD) = D.pₐ hD := by
      have hmem : RS.rho (D.p₂ hD) ∈ RS.dartsAt D.u := by
        simp only [RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact (RS.vert_rho (D.p₂ hD)).trans (D.vertOf_p₂ hD)
      rw [D.dartsAt_u_eq hD hCubic] at hmem
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
    have hcomplete := GoertzelV24DigonFaceLocal.complete_threeCycle
      RS.rho (D.p₁ hD) (D.p₂ hD) (D.pₐ hD)
      hp₁p₂ hp₁pₐ hp₂pₐ hsame hcube hforward hcarrier
    exact Or.inl ⟨hforward, hcomplete.1, hcomplete.2⟩
  · have hsame := hrotation (D.p₁ hD) (D.p₂ hD) (by simp)
    have hcube :=
      GoertzelV24InducedHexCorridorTypes.rho_cube_apply_of_isCubic
        RS hCubic hrotation (D.p₁ hD)
    have hcarrier :
        RS.rho (D.pₐ hD) = D.p₁ hD ∨
          RS.rho (D.pₐ hD) = D.pₐ hD ∨
          RS.rho (D.pₐ hD) = D.p₂ hD := by
      have hmem : RS.rho (D.pₐ hD) ∈ RS.dartsAt D.u := by
        simp only [RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ,
          true_and]
        exact (RS.vert_rho (D.pₐ hD)).trans (D.vertOf_pₐ hD)
      rw [D.dartsAt_u_eq hD hCubic] at hmem
      simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
      exact hmem.elim Or.inl (fun h => h.elim (Or.inr ∘ Or.inr) (Or.inr ∘ Or.inl))
    have hcomplete := GoertzelV24DigonFaceLocal.complete_threeCycle
      RS.rho (D.p₁ hD) (D.pₐ hD) (D.p₂ hD)
      hp₁pₐ hp₁p₂ hp₂pₐ.symm hsame hcube hreverse hcarrier
    exact Or.inr ⟨hcomplete.2, hreverse, hcomplete.1⟩

/-- At `v`, the successor of `q₂` is one of the other two named darts. -/
theorem rho_q₂_eq_q₁_or_qᵦ
    (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (hrotation : GoertzelV24FaceDualConnectedness.VertexRotationCyclic RS) :
    RS.rho (D.q₂ hD) = D.q₁ hD ∨ RS.rho (D.q₂ hD) = D.qᵦ hD := by
  have hmem : RS.rho (D.q₂ hD) ∈ RS.dartsAt D.v := by
    simp only [RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact (RS.vert_rho (D.q₂ hD)).trans (D.vertOf_q₂ hD)
  rw [D.dartsAt_v_eq hD hCubic] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hfirst | hfixed | hthird
  · exact Or.inl hfirst
  · have hsame := hrotation (D.q₂ hD) (D.q₁ hD) (by simp)
    exact False.elim (D.q₁_ne_q₂ hD (hsame.eq_of_left hfixed).symm)
  · exact Or.inr hthird

/-- At `v`, the successor of `q₁` is one of the other two named darts. -/
theorem rho_q₁_eq_q₂_or_qᵦ
    (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    (hrotation : GoertzelV24FaceDualConnectedness.VertexRotationCyclic RS) :
    RS.rho (D.q₁ hD) = D.q₂ hD ∨ RS.rho (D.q₁ hD) = D.qᵦ hD := by
  have hmem : RS.rho (D.q₁ hD) ∈ RS.dartsAt D.v := by
    simp only [RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ,
      true_and]
    exact (RS.vert_rho (D.q₁ hD)).trans (D.vertOf_q₁ hD)
  rw [D.dartsAt_v_eq hD hCubic] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hfixed | hsecond | hthird
  · have hsame := hrotation (D.q₁ hD) (D.q₂ hD) (by simp)
    exact False.elim (D.q₁_ne_q₂ hD (hsame.eq_of_left hfixed))
  · exact Or.inl hsecond
  · exact Or.inr hthird

/-- Away from the two attachment darts, crossing an edge cannot carry an
exterior dart into either digon vertex.  This is the exact locality fact
needed by the two-door facial-walk argument. -/
theorem alpha_exterior_of_exterior_of_ne_attachments
    (hD : D.WellFormed RS) (hCubic : RS.IsCubic)
    {x : RS.D} (hxa : x ≠ D.a' hD) (hxb : x ≠ D.b' hD)
    (hx : RS.vertOf x ≠ D.u ∧ RS.vertOf x ≠ D.v) :
    RS.vertOf (RS.alpha x) ≠ D.u ∧
      RS.vertOf (RS.alpha x) ≠ D.v := by
  constructor
  · intro halphaU
    have hmem : RS.alpha x ∈ RS.dartsAt D.u := by
      simp only [RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact halphaU
    rw [D.dartsAt_u_eq hD hCubic] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hp₁ | hp₂ | hpₐ
    · have hxq₁ : x = D.q₁ hD := by
        calc
          x = RS.alpha (RS.alpha x) := (RS.alpha_involutive x).symm
          _ = RS.alpha (D.p₁ hD) := congrArg RS.alpha hp₁
          _ = D.q₁ hD := D.alpha_p₁ hD
      exact hx.2 (by rw [hxq₁, D.vertOf_q₁ hD])
    · have hxq₂ : x = D.q₂ hD := by
        calc
          x = RS.alpha (RS.alpha x) := (RS.alpha_involutive x).symm
          _ = RS.alpha (D.p₂ hD) := congrArg RS.alpha hp₂
          _ = D.q₂ hD := D.alpha_p₂ hD
      exact hx.2 (by rw [hxq₂, D.vertOf_q₂ hD])
    · have hxa' : x = D.a' hD := by
        calc
          x = RS.alpha (RS.alpha x) := (RS.alpha_involutive x).symm
          _ = RS.alpha (D.pₐ hD) := congrArg RS.alpha hpₐ
          _ = D.a' hD := D.alpha_pₐ hD
      exact hxa hxa'
  · intro halphaV
    have hmem : RS.alpha x ∈ RS.dartsAt D.v := by
      simp only [RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ,
        true_and]
      exact halphaV
    rw [D.dartsAt_v_eq hD hCubic] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with hq₁ | hq₂ | hqᵦ
    · have hxp₁ : x = D.p₁ hD := by
        calc
          x = RS.alpha (RS.alpha x) := (RS.alpha_involutive x).symm
          _ = RS.alpha (D.q₁ hD) := congrArg RS.alpha hq₁
          _ = D.p₁ hD := D.alpha_q₁ hD
      exact hx.1 (by rw [hxp₁, D.vertOf_p₁ hD])
    · have hxp₂ : x = D.p₂ hD := by
        calc
          x = RS.alpha (RS.alpha x) := (RS.alpha_involutive x).symm
          _ = RS.alpha (D.q₂ hD) := congrArg RS.alpha hq₂
          _ = D.p₂ hD := D.alpha_q₂ hD
      exact hx.1 (by rw [hxp₂, D.vertOf_p₂ hD])
    · have hxb' : x = D.b' hD := by
        calc
          x = RS.alpha (RS.alpha x) := (RS.alpha_involutive x).symm
          _ = RS.alpha (D.qᵦ hD) := congrArg RS.alpha hqᵦ
          _ = D.b' hD := D.alpha_qᵦ hD
      exact hxb hxb'

end DigonPatchData

end

end RotationSystem

end Mettapedia.GraphTheory.FourColor
