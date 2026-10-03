import MettapediaFourColor.InducedGraphFaces
import MettapediaFourColor.ThreeBlockDiskDeletion
import MettapediaFourColor.ThreeBlockDiskStars

/-! # Every remaining exterior face is triangular

A retained edge whose ambient face meets the deleted core must be a source
boundary edge in the prescribed orientation. Every other face step survives
unchanged under first return. No ambient size bound or planarity is used.
-/

namespace FourColor.ThreeBlockDiskBoundary

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open FiveTriangleCollapseObstruction ExceptionalOverlap InducedGraphRotation

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem core_boundary_turn : ∀ i j k : Fin 18, Turn i j k →
    j.val < 11 → k.val < 11 → k.val = (j.val + 1) % 11 := by decide +kernel

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}
  (r : Reading data) (tri : Triangular data) (cyclic : data.IsVertexwiseCyclic)

include tri cyclic

theorem core_face_boundary (d : G.Dart) (hu : d.fst ∈ keep r) (hv : d.snd ∈ keep r)
    (deleted : (data.toRotationSystem.phi d).snd ∉ keep r) :
    ∃ j, d = includeDart (keep r) (boundaryDart r j) := by
  classical
  change ¬ ¬ (data.toRotationSystem.phi d).snd ∈
    r.hom '' {i : Fin 18 | 11 ≤ i.val} at deleted
  obtain ⟨i, hi, hiw⟩ := not_not.mp deleted
  let q : G.Dart := data.vertexRotation d.symm
  have qfst : q.fst = d.snd := data.vertexRotation_fst _
  have wi : r.hom i = q.snd := hiw
  have edge : G.Adj (r.hom i) d.snd := by
    rw [wi, ← qfst]
    exact q.adj.symm
  obtain ⟨j, hj, hij⟩ := core_stars r cyclic i hi d.snd edge
  obtain ⟨k, hik, turn⟩ := core_predecessor i j hi hij
  obtain ⟨_, _, step⟩ := r.turn i k j turn
  have qsymm : q.symm = (⟨(r.hom i, r.hom j), r.hom.map_rel hij⟩ : G.Dart) := by
    apply Dart.ext
    exact Prod.ext wi.symm (qfst.trans hj.symm)
  have back : (data.vertexRotation q.symm).snd = d.fst := by
    have h := congrArg (fun a : G.Dart => a.fst) (tri d)
    rw [data.vertexRotation_fst] at h
    exact h
  have hk : r.hom k = d.fst := by
    rw [qsymm] at back
    rw [step] at back
    exact back
  have jl : j.val < 11 := (keep_point r j).mp (hj ▸ hv)
  have kl : k.val < 11 := (keep_point r k).mp (hk ▸ hu)
  let b : Fin 11 := ⟨k.val, kl⟩
  have bk : b.castAdd 7 = k := Fin.ext rfl
  have bj : (b + 1).castAdd 7 = j :=
    Fin.ext (core_boundary_turn i k j turn kl jl).symm
  refine ⟨b, Dart.ext _ _ ?_⟩
  change (d.fst, d.snd) = (r.hom (b.castAdd 7), r.hom ((b + 1).castAdd 7))
  rw [bk, bj, hk, hj]

/-- Only the new boundary can have an ambient successor entering the core. -/
theorem successor_retained (d : (G.induce (keep r)).Dart) (hd : d ∉ outsideRing r) :
    retained (keep r) (data.toRotationSystem.phi (includeDart (keep r) d)) := by
  classical
  constructor
  · change (data.vertexRotation (includeDart (keep r) d).symm).fst ∈ keep r
    rw [data.vertexRotation_fst]
    exact d.snd.property
  · by_contra h
    obtain ⟨j, hj⟩ := core_face_boundary r tri cyclic (includeDart (keep r) d)
      d.fst.property d.snd.property h
    apply hd
    have eq := includeDart_injective (keep r) hj
    rw [eq]
    exact List.mem_ofFn.mpr ⟨j, rfl⟩

omit cyclic in
theorem successor_off_boundary (d : (G.induce (keep r)).Dart)
    (hd : d ∉ outsideRing r) :
    (outsideRotation r).toRotationSystem.phi d ∉ outsideRing r := by
  intro h
  obtain ⟨j, hj⟩ := List.mem_ofFn.mp h
  apply hd
  apply List.mem_ofFn.mpr
  refine ⟨j - 1, (outsideRotation r).toRotationSystem.phi.injective ?_⟩
  simpa using (boundary_step r tri (j - 1)).trans (by simpa using hj)

theorem surviving_face_step (d : (G.induce (keep r)).Dart) (hd : d ∉ outsideRing r) :
    includeDart (keep r) ((outsideRotation r).toRotationSystem.phi d) =
      data.toRotationSystem.phi (includeDart (keep r) d) :=
  phi_of_retained (keep r) data (boundaryDart r 0) d (successor_retained r tri cyclic d hd)

/-- Every nonboundary face retains its three original darts and face steps. -/
theorem outside_triangular (d : (G.induce (keep r)).Dart) (hd : d ∉ outsideRing r) :
    (outsideRotation r).toRotationSystem.phi
      ((outsideRotation r).toRotationSystem.phi
        ((outsideRotation r).toRotationSystem.phi d)) = d := by
  have h1 := successor_off_boundary r tri d hd
  have h2 := successor_off_boundary r tri _ h1
  apply includeDart_injective (keep r)
  rw [surviving_face_step r tri cyclic _ h2, surviving_face_step r tri cyclic _ h1,
    surviving_face_step r tri cyclic d hd]
  exact tri (includeDart (keep r) d)

end
end FourColor.ThreeBlockDiskBoundary
