import Mettapedia.GraphTheory.FourColor.FaceRegionConnectivity
import Mettapedia.GraphTheory.FourColor.PlanePatchCurvature

/-!
# Boundary occurrences of a retained facial region

Selected faces keep exactly their original dart orbits. The remaining darts
are exterior-oriented cut edges, with at most one such dart at each cubic
vertex. These facts identify the local boundary of the literal retained map
without a boundary word, planar drawing, or degree pattern as extra data.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceRegionBoundary

open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open PhysicalForkCodeFaces PhysicalForkCodeCut
open FaceRegionDegree EdgeShoreRotation PlanePatchCurvature

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem V E} {R : Finset (OrbitFace RS)}
variable (outer : Dart RS (edges RS R))

theorem selected_full {d : RS.D} (hd : dartOrbitFace RS d ∈ R)
    (e : RS.D) (he : RS.phi.SameCycle d e) : RS.edgeOf e ∈ edges RS R := by
  apply (edge_mem_iff RS R e).mpr
  left
  have hf : dartOrbitFace RS d = dartOrbitFace RS e := Quotient.sound he
  rwa [← hf]

/-- Selected faces have neither extra nor missing occurrences after
restriction. This is an equivalence of actual facial orbits. -/
theorem selected_sameCycle_iff (d e : Dart RS (edges RS R))
    (hd : dartOrbitFace RS d.val ∈ R) :
    (toMap RS (edges RS R) outer).phi.SameCycle d e ↔ RS.phi.SameCycle d.val e.val := by
  constructor
  · intro he
    obtain ⟨n, hn⟩ := he.exists_nat_pow_eq
    have hp := phi_pow_of_full_face outer d (selected_full hd) n
    rw [hn] at hp
    exact ⟨(n : ℤ), by simpa using hp.symm⟩
  · intro he
    obtain ⟨n, hn⟩ := he.exists_nat_pow_eq
    have hp := phi_pow_of_full_face outer d (selected_full hd) n
    have heq : ((toMap RS (edges RS R) outer).phi ^ n) d = e :=
      Subtype.ext (hp.trans hn)
    exact ⟨(n : ℤ), by simpa using heq⟩

theorem outside_of_sameCycle (d e : Dart RS (edges RS R))
    (hd : dartOrbitFace RS d.val ∉ R)
    (he : (toMap RS (edges RS R) outer).phi.SameCycle d e) :
    dartOrbitFace RS e.val ∉ R := by
  intro hs
  have hh := (selected_sameCycle_iff outer e d hs).mp he.symm
  have hf : dartOrbitFace RS e.val = dartOrbitFace RS d.val := Quotient.sound hh
  exact hd (hf ▸ hs)

theorem outside_phi_iff (d : Dart RS (edges RS R)) :
    dartOrbitFace RS ((toMap RS (edges RS R) outer).phi d).val ∉ R ↔
      dartOrbitFace RS d.val ∉ R := by
  have hh : (toMap RS (edges RS R) outer).phi.SameCycle
      d ((toMap RS (edges RS R) outer).phi d) :=
    (Equiv.Perm.sameCycle_apply_right).mpr (Equiv.Perm.SameCycle.refl _ d)
  exact ⟨fun h => outside_of_sameCycle outer _ _ h hh.symm,
    fun h => outside_of_sameCycle outer _ _ h hh⟩

/-- At a cubic vertex there is at most one retained dart whose face is
unselected. This remains true when incident quotient faces repeat. -/
theorem outside_vertex_injective (hC : Cubic3 RS)
    (d e : Dart RS (edges RS R))
    (hd : dartOrbitFace RS d.val ∉ R) (he : dartOrbitFace RS e.val ∉ R)
    (hv : RS.vertOf d.val = RS.vertOf e.val) : d = e := by
  have hdr : dartOrbitFace RS (RS.rho d.val) ∈ R :=
    (edge_mem_iff_sectors RS R d.val).mp d.property |>.resolve_left hd
  have her : dartOrbitFace RS (RS.rho e.val) ∈ R :=
    (edge_mem_iff_sectors RS R e.val).mp e.property |>.resolve_left he
  rcases hC.fiber d.val e.val hv.symm with h | h | h
  · exact Subtype.ext h.symm
  · exact (he (h ▸ hdr)).elim
  · rw [h, hC.cube] at her
    exact (hd her).elim

/-- A mixed vertex has an exterior-oriented retained occurrence based at
that same vertex, rather than at the other end of a cut edge. -/
theorem exists_outside_at_vertex (hC : Cubic3 RS) (v : V)
    (hin : ∃ d, RS.vertOf d = v ∧ dartOrbitFace RS d ∈ R)
    (hout : ∃ e, RS.vertOf e = v ∧ dartOrbitFace RS e ∉ R) :
    ∃ d : Dart RS (edges RS R), RS.vertOf d.val = v ∧ dartOrbitFace RS d.val ∉ R := by
  obtain ⟨d, hd, hdf⟩ := hin
  obtain ⟨e, he, hef⟩ := hout
  by_cases hnext : dartOrbitFace RS (RS.rho e) ∈ R
  · exact ⟨⟨e, (edge_mem_iff_sectors RS R e).mpr (Or.inr hnext)⟩, he, hef⟩
  · have hh : dartOrbitFace RS (RS.rho (RS.rho e)) ∈ R := by
      rcases hC.fiber e d (hd.trans he.symm) with h | h | h
      · exact (hef (h ▸ hdf)).elim
      · exact (hnext (h ▸ hdf)).elim
      · exact h ▸ hdf
    exact ⟨⟨RS.rho e, (edge_mem_iff_sectors RS R _).mpr (Or.inr hh)⟩,
      (RS.vert_rho e).trans he, hnext⟩

theorem outside_at_vertex_of_degree_two (hC : Cubic3 RS) (hcubic : RS.IsCubic)
    (v : Vertex RS (edges RS R))
    (hdegree : ((toMap RS (edges RS R) outer).dartsAt v).card = 2) :
    ∃ d : Dart RS (edges RS R), RS.vertOf d.val = v.val ∧ dartOrbitFace RS d.val ∉ R := by
  apply exists_outside_at_vertex hC v.val ((touched_iff _ _ _).mp v.property)
  by_contra! h
  have heq : sectors RS R v.val = RS.dartsAt v.val := by
    apply Finset.filter_eq_self.mpr
    intro d hd
    exact h d (Finset.mem_filter.mp hd).2
  have hcount := (degree_two_iff_one_sector hC outer v).mp hdegree
  rw [heq, hcubic] at hcount
  omega

theorem outer_dart_outside (ho : dartOrbitFace RS outer.val ∉ R)
    {d : Dart RS (edges RS R)} (hd : d ∈ outerDarts (toMap RS (edges RS R) outer)) :
    dartOrbitFace RS d.val ∉ R := by
  have he : dartOrbitFace (toMap RS (edges RS R) outer) d =
      dartOrbitFace (toMap RS (edges RS R) outer) outer :=
    (mem_orbitFaceDarts_iff _ _ _).mp hd
  exact outside_of_sameCycle outer outer d ho (Quotient.exact he.symm)

/-- Every exterior facial orbit of the retained map is simple at vertices.
Showing there is only one such orbit is a separate global statement. -/
theorem outer_simple (hC : Cubic3 RS) (ho : dartOrbitFace RS outer.val ∉ R) :
    Set.InjOn (toMap RS (edges RS R) outer).vertOf
      (outerDarts (toMap RS (edges RS R) outer) : Set _) := by
  intro d hd e he hv
  exact outside_vertex_injective hC d e (outer_dart_outside outer ho hd)
    (outer_dart_outside outer ho he) (congrArg Subtype.val hv)

end
end Mettapedia.GraphTheory.FourColor.FaceRegionBoundary
