import MettapediaFourColor.PatchDiskBoundary
import MettapediaFourColor.InducedGraphFaces

/-! # Remaining faces and connectedness after core deletion

Every ambient face that enters the core is read from its complete cyclic
star. It therefore meets the prescribed boundary. All other faces remain
triangular. The retained boundary walk connects every attachment to the core,
including when some boundary vertices coincide.
-/

namespace FourColor.PatchDisk.Reading

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalOverlap InducedGraphRotation

noncomputable section

variable {c b : ℕ} [NeZero b] {s : Source c b}
  {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}
  (r : Reading s data) (tri : Triangular data) (cyclic : data.IsVertexwiseCyclic)

include tri cyclic

theorem core_face_boundary (d : G.Dart) (hu : d.fst ∈ keep r) (hv : d.snd ∈ keep r)
    (deleted : (data.toRotationSystem.phi d).snd ∉ keep r) :
    ∃ j, d = includeDart (keep r) (boundaryDart r j) := by
  classical
  change ¬ ¬ (data.toRotationSystem.phi d).snd ∈
    r.hom '' {i : Fin (b + c) | b ≤ i.val} at deleted
  obtain ⟨i, hi, hiw⟩ := not_not.mp deleted
  let q : G.Dart := data.vertexRotation d.symm
  have qfst : q.fst = d.snd := data.vertexRotation_fst _
  have wi : r.hom i = q.snd := hiw
  have edge : G.Adj (r.hom i) d.snd := by
    rw [wi, ← qfst]
    exact q.adj.symm
  obtain ⟨j, hj, hij⟩ := core_stars r cyclic i hi d.snd edge
  obtain ⟨k, hik, turn⟩ := s.core_predecessor i j hi hij
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
  have jl : j.val < b := (keep_point r j).mp (hj ▸ hv)
  have kl : k.val < b := (keep_point r k).mp (hk ▸ hu)
  let p : Fin b := ⟨k.val, kl⟩
  have bk : p.castAdd c = k := Fin.ext rfl
  have bj : (p + 1).castAdd c = j := by
    apply Fin.ext
    change (k.val + 1 % b) % b = j.val
    rw [Nat.mod_eq_of_lt (show 1 < b by have := s.boundary_size; omega)]
    exact (s.core_boundary_turn i k j turn kl jl).symm
  refine ⟨p, Dart.ext _ _ ?_⟩
  change (d.fst, d.snd) = (r.hom (p.castAdd c), r.hom ((p + 1).castAdd c))
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

omit tri cyclic

theorem ports_reachable (j : Fin b) :
    (G.induce (keep r)).Reachable (port r 0) (port r j) := by
  have reach : ∀ n (hn : n < b),
      (G.induce (keep r)).Reachable (port r 0) (port r ⟨n, hn⟩) := by
    intro n
    induction n with
    | zero => intro _; exact .refl _
    | succ n ih =>
      intro hn
      have add : (⟨n, by omega⟩ : Fin b) + 1 = ⟨n + 1, hn⟩ := by
        apply Fin.ext
        have one : (1 : Fin b).val = 1 := by
          change 1 % b = 1
          exact Nat.mod_eq_of_lt (by have := s.boundary_size; omega)
        simp only [Fin.val_add, one, Nat.mod_eq_of_lt hn]
      have edge := (boundaryDart r ⟨n, by omega⟩).adj.reachable
      rw [show (boundaryDart r ⟨n, by omega⟩).snd =
        port r (⟨n, by omega⟩ + 1) from rfl, add] at edge
      exact (ih (by omega)).trans edge
  exact reach j.val j.isLt

theorem boundary_neighbor (cyclic : data.IsVertexwiseCyclic)
    {u v : V} (hu : u ∈ keep r) (hv : v ∉ keep r) (edge : G.Adj u v) :
    ∃ j : Fin b, (port r j).val = u := by
  classical
  change ¬ ¬ v ∈ r.hom '' {i : Fin (b + c) | b ≤ i.val} at hv
  obtain ⟨i, hi, rfl⟩ := not_not.mp hv
  obtain ⟨j, hj, _⟩ := core_stars r cyclic i hi u edge.symm
  have low : j.val < b := (keep_point r j).mp (hj ▸ hu)
  exact ⟨⟨j.val, low⟩, hj⟩

theorem outside_connected (cyclic : data.IsVertexwiseCyclic) (conn : G.Connected) :
    (G.induce (keep r)).Connected := by
  classical
  let f (v : V) : keep r := if h : v ∈ keep r then ⟨v, h⟩ else port r 0
  have fixed (v : keep r) : f v.val = v := by simp [f, v.property]
  have edge : ∀ u v, G.Adj u v → (G.induce (keep r)).Reachable (f u) (f v) := by
    intro u v huv
    by_cases hu : u ∈ keep r <;> by_cases hv : v ∈ keep r
    · simpa only [f, dite_eq_left hu, dite_eq_left hv] using
        (show (G.induce (keep r)).Adj ⟨u, hu⟩ ⟨v, hv⟩ from huv).reachable
    · obtain ⟨j, hj⟩ := boundary_neighbor r cyclic hu hv huv
      have eq : (⟨u, hu⟩ : keep r) = port r j := Subtype.ext hj.symm
      simpa only [f, dite_eq_left hu, dite_eq_right hv, eq] using (ports_reachable r j).symm
    · obtain ⟨j, hj⟩ := boundary_neighbor r cyclic hv hu huv.symm
      have eq : (⟨v, hv⟩ : keep r) = port r j := Subtype.ext hj.symm
      simpa only [f, dite_eq_right hu, dite_eq_left hv, eq] using ports_reachable r j
    · simp only [f, dite_eq_right hu, dite_eq_right hv]
      exact .refl _
  have walk : ∀ {u v}, G.Walk u v → (G.induce (keep r)).Reachable (f u) (f v) := by
    intro u v p
    induction p with
    | nil => exact .refl _
    | cons h p ih => exact (edge _ _ h).trans ih
  let : Nonempty (keep r) := ⟨port r 0⟩
  refine ⟨?_⟩
  intro u v
  obtain ⟨p⟩ := conn u.val v.val
  simpa only [fixed] using walk p

end
end FourColor.PatchDisk.Reading
