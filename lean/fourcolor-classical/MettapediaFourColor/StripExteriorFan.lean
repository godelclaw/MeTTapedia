import MettapediaFourColor.StripComplementaryRepair
import MettapediaFourColor.FacialStarCompletion
import Mettapedia.GraphTheory.Kempe.PhaseBoundary

/-! # A missing colour forces an exterior neighbour path

The two interior neighbours of port one occur consecutively after port two.
The complementary rotation arc from port zero to port two therefore stays
outside the core. Triangular faces turn that arc into an actual exterior
walk. If colour two is missing at port one, the walk uses only zero and
three, so those two boundary ports cannot be changed independently by any
phase of that pair.
-/

namespace FourColor.StripExteriorFan

open SimpleGraph Color Mettapedia.GraphTheory.FourColor
open SimpleGraphDartRotation StripSixBarrierGeometry

variable {V W : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} {data : Data G}

/-- The interior block at port one, expressed in actual ambient darts. -/
structure InteriorBlock (s : StripSixBarrierGeometry.Patch data) : Prop where
  first : data.vertexRotation (s.dart 1 2 (by decide +kernel)) =
    s.dart 1 16 (by decide +kernel)
  second : data.vertexRotation (s.dart 1 16 (by decide +kernel)) =
    s.dart 1 18 (by decide +kernel)
  only : ∀ i : Fin 19, 11 ≤ i.val → G.Adj (s.point 1) (s.point i) →
    i = 16 ∨ i = 18

noncomputable section

variable (s : StripSixBarrierGeometry.Patch data) (block : InteriorBlock s)
  (cyclic : data.IsVertexwiseCyclic) (tri : ExceptionalOverlap.Triangular data)
  (e : ExteriorReading s H)
  (complete : ∀ v, s.Exterior v → G.Adj (s.point 1) v →
    ∃ w, e.embedding w = v)

include block cyclic tri complete in
/-- The exterior arc is derived from the rotation, not supplied as a path
hypothesis. Completeness is needed only for exterior neighbours of port one. -/
theorem neighbour_path : ∃ p : H.Walk (e.ports 0) (e.ports 2),
    ∀ v ∈ p.support, H.Adj (e.ports 1) v := by
  classical
  let base := s.dart 1 0 (by decide +kernel)
  let target := s.dart 1 2 (by decide +kernel)
  let orbit (k : ℕ) := (data.vertexRotation ^ k) base
  have first (k : ℕ) : (orbit k).fst = s.point 1 :=
    FacialStarCompletion.pow_fst data base k
  have next (k : ℕ) : orbit (k + 1) = data.vertexRotation (orbit k) := by
    simp [orbit,pow_succ',Equiv.Perm.mul_apply]
  obtain ⟨k,_,hk⟩ := FacialStarCompletion.covers data cyclic base target rfl
  have existsTarget : ∃ n, orbit n = target := ⟨k,hk⟩
  let n := Nat.find existsTarget
  have endpoint : orbit n = target := Nat.find_spec existsTarget
  have earlier (j : ℕ) (hj : j < n) : orbit j ≠ target :=
    Nat.find_min existsTarget hj
  have dart_eq (j : ℕ) (i : Fin 19) (edge : TriangleStripAnchors.input0099.graph.Adj 1 i)
      (h : (orbit j).snd = s.point i) : orbit j = s.dart 1 i edge := by
    apply Dart.ext
    exact Prod.ext (first j) h
  have avoid16 (j : ℕ) (hj : j ≤ n) : (orbit j).snd ≠ s.point 16 := by
    intro h
    cases j with
    | zero => exact (by decide : (0 : Fin 19) ≠ 16) (s.injective h)
    | succ j =>
      have eq := dart_eq _ 16 (by decide +kernel) h
      rw [next,← block.first] at eq
      exact earlier j (by omega) (data.vertexRotation.injective eq)
  have avoid18 (j : ℕ) (hj : j ≤ n) : (orbit j).snd ≠ s.point 18 := by
    intro h
    cases j with
    | zero => exact (by decide : (0 : Fin 19) ≠ 18) (s.injective h)
    | succ j =>
      have eq := dart_eq _ 18 (by decide +kernel) h
      rw [next,← block.second] at eq
      exact avoid16 j (by omega)
        (congrArg (fun d : G.Dart => d.snd) (data.vertexRotation.injective eq))
  have adjacent (j : ℕ) : G.Adj (s.point 1) (orbit j).snd := by
    simpa only [first] using (orbit j).adj
  have outside (j : ℕ) (hj : j ≤ n) : s.Exterior (orbit j).snd := by
    intro i hi eq
    have edge := adjacent j
    rw [eq] at edge
    rcases block.only i hi edge with rfl | rfl
    · exact avoid16 j hj eq
    · exact avoid18 j hj eq
  let point (j : ℕ) : W := if hj : j ≤ n then
    Classical.choose (complete _ (outside j hj) (adjacent j)) else e.ports 0
  have image (j : ℕ) (hj : j ≤ n) : e.embedding (point j) = (orbit j).snd := by
    simp only [point,dite_eq_left hj]
    exact Classical.choose_spec (complete _ (outside j hj) (adjacent j))
  have root : point 0 = e.ports 0 := by
    apply e.embedding.injective
    rw [image 0 (Nat.zero_le _),e.boundary]
    rfl
  have last : point n = e.ports 2 := by
    apply e.embedding.injective
    rw [image n le_rfl,endpoint,e.boundary]
    rfl
  have star (j : ℕ) (hj : j ≤ n) : H.Adj (e.ports 1) (point j) := by
    apply e.embedding.map_adj_iff.mp
    rw [e.boundary,image j hj]
    exact adjacent j
  have step (j : ℕ) (hj : j + 1 ≤ n) : H.Adj (point j) (point (j + 1)) := by
    apply e.embedding.map_adj_iff.mp
    rw [image j (by omega),image (j + 1) hj,next]
    exact ExceptionalOverlap.consecutive_adjacent data tri (orbit j)
  have paths (j : ℕ) (hj : j ≤ n) : ∃ p : H.Walk (point 0) (point j),
      ∀ v ∈ p.support, H.Adj (e.ports 1) v := by
    induction j with
    | zero => exact ⟨.nil,by intro v hv; simpa using (List.mem_singleton.mp hv) ▸ star 0 hj⟩
    | succ j ih =>
      obtain ⟨p,hp⟩ := ih (by omega)
      refine ⟨p.append (.cons (step j hj) .nil),?_⟩
      intro v hv
      rw [Walk.mem_support_append_iff] at hv
      rcases hv with hv | hv
      · exact hp v hv
      · change v ∈ [point j,point (j+1)] at hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
        rcases hv with rfl | rfl
        · exact star j (by omega)
        · exact star (j+1) hj
  obtain ⟨p,hp⟩ := paths n le_rfl
  exact ⟨p.copy root last,by simpa only [Walk.support_copy] using hp⟩

include block cyclic tri complete in
/-- The missing colour forces a bichromatic route around the boundary vertex. -/
theorem bichromatic_path (C : H.Coloring Color)
    (one : C (e.ports 1) = c1)
    (missing : ∀ v, H.Adj (e.ports 1) v → C v ≠ c2) :
    ∃ p : H.Walk (e.ports 0) (e.ports 2),
      ∀ v ∈ p.support, C v = c0 ∨ C v = c3 := by
  obtain ⟨p,hp⟩ := neighbour_path s block cyclic tri e complete
  refine ⟨p,?_⟩
  intro v hv
  have notOne : C v ≠ c1 := fun h => C.valid (hp v hv) (one.trans h.symm)
  have notTwo := missing v (hp v hv)
  cases h : C v <;> simp_all

include block cyclic tri complete in
/-- No proper partial zero/three transposition can change port two while
fixing port zero. In particular, a phase of that pair cannot prepare the
complementary-repair boundary word. -/
theorem no_independent_change (C D : H.Coloring Color)
    (one : C (e.ports 1) = c1)
    (missing : ∀ v, H.Adj (e.ports 1) v → C v ≠ c2)
    (update : ∀ v, D v = C v ∨ D v = Equiv.swap c0 c3 (C v))
    (fixed : D (e.ports 0) = C (e.ports 0)) :
    D (e.ports 2) = C (e.ports 2) := by
  obtain ⟨p,hp⟩ := bichromatic_path s block cyclic tri e complete C one missing
  by_contra changed
  exact (KempeRouteProjection.changed_along_walk C D c0 c3 update p.reverse
    (fun v hv => hp v (by simpa using hv)) changed) fixed

include block cyclic tri complete in
theorem no_preparation (C D : H.Coloring Color)
    (initial : ∀ i, C (e.ports i) = StripSixConnection.input true i)
    (missing : ∀ v, H.Adj (e.ports 1) v → C v ≠ c2)
    (phase : Relation.ReflTransGen (KempePairHistory.Step c0 c3) C D) :
    ¬ ∀ i, D (e.ports i) = StripComplementaryRepair.input i := by
  intro prepared
  have eq := no_independent_change s block cyclic tri e complete C D (initial 1)
    missing (KempePairHistory.pointwise phase) ((prepared 0).trans (initial 0).symm)
  rw [prepared 2,initial 2] at eq
  cases eq

end
end FourColor.StripExteriorFan
