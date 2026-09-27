import Mettapedia.GraphTheory.FourColor.FaceExposedPath

/-!
# A facial path meets the old patch exactly at its two ends

The two boundary junctions are old vertices. Every other vertex of the
new path is absent from the old patch: two new incident edges would
contradict the cubic incidence law at an already touched vertex.
-/

namespace Mettapedia.GraphTheory.FourColor.FaceExposedEndpoints

open Equiv Equiv.Perm
open GoertzelV24FaceOrbitIncidence GoertzelV24TwoEdgeCutMinimality
open SimpleGraphDartRotation FaceRegionDegree EdgeShoreRotation
open PlanePatchCurvature FaceRegionShelling FaceRegionComplement
open PhysicalForkCodeCut PhysicalForkCodeFaces PermutationSingleExitArc
open FaceExposedBoundary FaceBoundarySplice FaceExposedPath

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (data : Data G)
variable {S R : Region data} (e : Event S R)
variable (ambient : BridgelessSphericalCubicMapData data.toRotationSystem)

include ambient in
theorem new_edges_unique_at_old {v : V}
    (hv : v ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    {x y : G.edgeSet} (hx : x ∈ exposedEdges data e) (hy : y ∈ exposedEdges data e)
    (hvx : v ∈ data.toRotationSystem.endpoints x)
    (hvy : v ∈ data.toRotationSystem.endpoints y) : x = y := by
  obtain ⟨d, hd, hdv⟩ := data.toRotationSystem.mem_endpoints_iff.mp hvx
  obtain ⟨a, ha, hav⟩ := data.toRotationSystem.mem_endpoints_iff.mp hvy
  have hdx := data.toRotationSystem.mem_dartsOn.mp hd
  have hay := data.toRotationSystem.mem_dartsOn.mp ha
  have hda := nonretained_dart_unique
    (cubic3_of _ ambient.spherical.cubic ambient.vertexRotationCyclic) hv hdv hav
    (hdx.symm ▸ (Finset.mem_sdiff.mp hx).2)
    (hay.symm ▸ (Finset.mem_sdiff.mp hy).2)
  exact hdx.symm.trans ((congrArg data.toRotationSystem.edgeOf hda).trans hay)

variable (outer : Dart data.toRotationSystem (edges data.toRotationSystem R.faces))
variable (ho : dartOrbitFace data.toRotationSystem outer.val ∉ R.faces)
variable (b : Arc
  (toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer).phi
  (exposedDarts data e outer))

local notation "New" => toMap data.toRotationSystem (edges data.toRotationSystem R.faces) outer

theorem first_old :
    (path data e outer ambient ho b).first ∈
      touched data.toRotationSystem (edges data.toRotationSystem S.faces) := by
  have hp : (New).phi.symm b.first ∈ outerDarts New := by
    apply (outer_phi_iff (RS := New) _).mp
    simpa using power_on_outer data e outer b 0
  have he : data.toRotationSystem.edgeOf ((New).phi.symm b.first).val ∈
      edges data.toRotationSystem S.faces := by
    by_contra hn
    exact b.before_outside ((exposed_iff_new_edge data e outer _ hp).mpr hn)
  have hv := congrArg
    (fun v : Vertex data.toRotationSystem (edges data.toRotationSystem R.faces) => v.val)
    ((New).vert_phi_eq_vert_alpha ((New).phi.symm b.first))
  simp only [(New).phi.apply_symm_apply] at hv
  change data.toRotationSystem.vertOf b.first.val =
    data.toRotationSystem.vertOf
      (data.toRotationSystem.alpha ((New).phi.symm b.first).val) at hv
  change data.toRotationSystem.vertOf (((New).phi ^ 0) b.first).val ∈ _
  simp only [pow_zero, Perm.one_apply]
  rw [hv]
  exact alpha_touched he

theorem last_old :
    (path data e outer ambient ho b).last ∈
      touched data.toRotationSystem (edges data.toRotationSystem S.faces) := by
  have he : data.toRotationSystem.edgeOf (((New).phi ^ b.length) b.first).val ∈
      edges data.toRotationSystem S.faces := by
    by_contra hn
    exact b.after_outside ((exposed_iff_new_edge data e outer _
      (power_on_outer data e outer b b.length)).mpr hn)
  exact mem_touched.mpr ⟨_, rfl, he⟩

/-- Every internal vertex of the exposed path is new. -/
theorem vertex_old_iff (i : Fin (b.length + 1)) :
    (path data e outer ambient ho b).vertex i ∈
        touched data.toRotationSystem (edges data.toRotationSystem S.faces) ↔
      i.val = 0 ∨ i.val = b.length := by
  let p := path data e outer ambient ho b
  constructor
  · intro hv
    by_contra hn
    have hi0 : 0 < i.val := by omega
    have hin : i.val < b.length := by omega
    let j : Fin b.length := ⟨i.val - 1, by omega⟩
    let k : Fin b.length := ⟨i.val, hin⟩
    have hji : p.vertex j.succ = p.vertex i :=
      congrArg p.vertex (Fin.ext (by dsimp [j]; omega))
    have hki : p.vertex k.castSucc = p.vertex i := congrArg p.vertex (Fin.ext rfl)
    have hvj : p.vertex i ∈ data.toRotationSystem.endpoints (p.edge j).val := by
      rw [p.endpoints j]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr hji.symm)
    have hvk : p.vertex i ∈ data.toRotationSystem.endpoints (p.edge k).val := by
      rw [p.endpoints k]
      exact Finset.mem_insert.mpr (Or.inl hki.symm)
    have heq := new_edges_unique_at_old data e ambient hv
      (p.edge j).property (p.edge k).property hvj hvk
    have hidx := congrArg Fin.val (p.edge.injective (Subtype.ext heq))
    change i.val - 1 = i.val at hidx
    omega
  · rintro (hz | hn)
    · have heq : i = 0 := Fin.ext hz
      subst i
      exact first_old data e ambient outer ho b
    · have heq : i = Fin.last b.length := Fin.ext hn
      subst i
      exact last_old data e ambient outer ho b

/-- Only the endpoints can carry compatibility constraints with old edges. -/
theorem shared_vertex {v : V}
    (hv : v ∈ touched data.toRotationSystem (edges data.toRotationSystem S.faces))
    {x : G.edgeSet} (hx : x ∈ exposedEdges data e)
    (hvx : v ∈ data.toRotationSystem.endpoints x) :
    v = (path data e outer ambient ho b).first ∨
      v = (path data e outer ambient ho b).last := by
  let p := path data e outer ambient ho b
  obtain ⟨i, hi⟩ := p.edge.surjective ⟨x, hx⟩
  have he : (p.edge i).val = x := congrArg Subtype.val hi
  rw [← he, p.endpoints, Finset.mem_insert, Finset.mem_singleton] at hvx
  have endpoint (j : Fin (b.length + 1)) (hvj : v = p.vertex j) :
      v = p.first ∨ v = p.last := by
    have hj := (vertex_old_iff data e ambient outer ho b j).mp (hvj ▸ hv)
    rcases hj with hz | hn
    · left
      rw [hvj, show j = 0 from Fin.ext hz]
      rfl
    · right
      rw [hvj, show j = Fin.last b.length from Fin.ext hn]
      rfl
  exact hvx.elim (endpoint i.castSucc) (endpoint i.succ)

end
end Mettapedia.GraphTheory.FourColor.FaceExposedEndpoints
