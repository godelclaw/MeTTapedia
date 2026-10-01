import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationCycleSpace

/-!
# Face potentials for conserved edge fields

On a two-sided spherical rotation multigraph with connected primal and
facial dual, a Klein-valued edge field whose sum at every vertex is zero
is the difference of face potentials.
The construction uses the existing equality of facial boundaries and the
literal cycle space. It preserves each edge, including parallel edges.
Cubicity and nonzero colours are not needed for this integration theorem.
-/

namespace Mettapedia.GraphTheory.FourColor.RotationConservedFacePotential

open GoertzelV24FaceBoundaryLinearAlgebra GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCycleSpace
open scoped BigOperators

noncomputable section

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

/-- Conservation is imposed on the actual incident edge identifiers. -/
def Conserved (RS : RotationSystem V E) (omega : E → Color) : Prop :=
  ∀ v, ∑ e ∈ RS.incidentEdges v, omega e = 0

/-- Exact reconstruction from the two faces incident to each literal edge. -/
def IsFacePotential (RS : RotationSystem V E) (omega : E → Color)
    (p : OrbitFace RS → Color) : Prop :=
  ∀ d, p (dartOrbitFace RS d) + p (dartOrbitFace RS (RS.alpha d)) = omega (RS.edgeOf d)

theorem scalar_mem_cycleSpace (RS : RotationSystem V E) (omega : E → F2)
    (h : ∀ v, ∑ e ∈ RS.incidentEdges v, omega e = 0) :
    omega ∈ cycleSpace RS := by
  classical
  rw [cycleSpace, LinearMap.mem_ker]
  funext v
  simpa only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, incidenceMatrix,
    ite_mul, one_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter, Pi.zero_apply] using h v

/-- Integrate a conserved scalar field without identifying parallel edges. -/
theorem exists_scalar_potential
    (RS : RotationSystem V E) (htwo : OrbitFacesTwoSided RS)
    (hdual : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card E +
      Fintype.card (OrbitFace RS) = 2)
    (omega : E → F2) (h : ∀ v, ∑ e ∈ RS.incidentEdges v, omega e = 0) :
    ∃ p : OrbitFace RS → F2,
      ∀ d, p (dartOrbitFace RS d) + p (dartOrbitFace RS (RS.alpha d)) =
        omega (RS.edgeOf d) := by
  have hc := scalar_mem_cycleSpace RS omega h
  rw [← range_faceBoundaryLinearMap_eq_cycleSpace RS htwo hdual hconnected heuler] at hc
  obtain ⟨p, hp⟩ := hc
  exact ⟨p, fun d => (orbitFaceBoundaryLinearMap_apply_edgeOf RS htwo p d).symm.trans
    (congrFun hp (RS.edgeOf d))⟩

/-- Both coordinates use the same actual face carrier and reconstruct the
complete joint edge field, not only its nonzero support. -/
theorem exists_facePotential
    (RS : RotationSystem V E) (htwo : OrbitFacesTwoSided RS)
    (hdual : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card E +
      Fintype.card (OrbitFace RS) = 2)
    (omega : E → Color) (h : Conserved RS omega) :
    ∃ p, IsFacePotential RS omega p := by
  obtain ⟨p, hp⟩ := exists_scalar_potential RS htwo hdual hconnected heuler
    (fun e => (omega e).1) (fun v => by
      have hs := map_sum (AddMonoidHom.fst F2 F2) omega (RS.incidentEdges v)
      rw [h v, map_zero] at hs
      simpa only [AddMonoidHom.coe_fst] using hs.symm)
  obtain ⟨q, hq⟩ := exists_scalar_potential RS htwo hdual hconnected heuler
    (fun e => (omega e).2) (fun v => by
      have hs := map_sum (AddMonoidHom.snd F2 F2) omega (RS.incidentEdges v)
      rw [h v, map_zero] at hs
      simpa only [AddMonoidHom.coe_snd] using hs.symm)
  exact ⟨fun f => (p f, q f), fun d => Prod.ext (hp d) (hq d)⟩

/-- Tait colourings supply the conservation hypothesis automatically. -/
theorem conserved_of_tait (RS : RotationSystem V E) (hcubic : RS.IsCubic)
    (c : RS.EdgeColoring Color) (hc : RS.IsTaitEdgeColoring c) : Conserved RS c :=
  RS.vertexColorSum_eq_zero_of_isCubic_of_isTaitEdgeColoring hcubic c hc

/-- The only freedom in a reconstructed potential is one common colour
shift on all faces. Separate regions cannot choose incompatible shifts. -/
theorem potentials_differ_by_constant
    (RS : RotationSystem V E) (htwo : OrbitFacesTwoSided RS)
    (hdual : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected)
    (omega : E → Color) {p q : OrbitFace RS → Color}
    (hp : IsFacePotential RS omega p) (hq : IsFacePotential RS omega q)
    (root : OrbitFace RS) : ∀ f, p f + q f = p root + q root := by
  have coordinate (project : Color →+ F2) :
      ∀ f, project (p f) + project (q f) = project (p root) + project (q root) := by
    have hk : (fun f => project (p f) + project (q f)) ∈
        LinearMap.ker (orbitFaceBoundaryLinearMap RS) := by
      rw [LinearMap.mem_ker]
      funext e
      obtain ⟨d, hd⟩ := RS.dartsOn_nonempty e
      rw [← RS.mem_dartsOn.mp hd, orbitFaceBoundaryLinearMap_apply_edgeOf RS htwo]
      have he := congrArg project ((hp d).trans (hq d).symm)
      simp only [map_add] at he
      change (project (p (dartOrbitFace RS d)) + project (q (dartOrbitFace RS d))) +
        (project (p (dartOrbitFace RS (RS.alpha d))) +
          project (q (dartOrbitFace RS (RS.alpha d)))) = 0
      calc
        _ = (project (p (dartOrbitFace RS d)) + project (p (dartOrbitFace RS (RS.alpha d)))) +
            (project (q (dartOrbitFace RS d)) + project (q (dartOrbitFace RS (RS.alpha d)))) := by abel
        _ = 0 := by rw [he]; simp
    exact fun f => (mem_ker_orbitFaceBoundaryLinearMap_iff_constant RS htwo hdual _).mp hk f root
  intro f
  exact Prod.ext (coordinate (AddMonoidHom.fst F2 F2) f)
    (coordinate (AddMonoidHom.snd F2 F2) f)

/-- Fixing one face removes that freedom, giving a unique common witness. -/
theorem potential_unique_at_root
    (RS : RotationSystem V E) (htwo : OrbitFacesTwoSided RS)
    (hdual : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected)
    (omega : E → Color) {p q : OrbitFace RS → Color}
    (hp : IsFacePotential RS omega p) (hq : IsFacePotential RS omega q)
    (root : OrbitFace RS) (hr : p root = q root) : p = q := by
  funext f
  have h := potentials_differ_by_constant RS htwo hdual omega hp hq root f
  rw [hr, color_add_self] at h
  exact (add_eq_zero_iff_eq _ _).mp h

end
end Mettapedia.GraphTheory.FourColor.RotationConservedFacePotential
