import MettapediaFourColor.ThreeBlockDiskBoundary

/-! # Ordered boundary supply under deletion of the D0092 core

The first-return rotation is on the actual induced graph. The source's
eleven short fan arcs derive its facial boundary in the source port order;
this order is not a hypothesis. Planarity and connectedness of the exterior
remain separate obligations.
-/

namespace FourColor.ThreeBlockDiskBoundary

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open FiveTriangleCollapseObstruction ExceptionalCoreOrientation ExceptionalOverlap
open GoertzelV24OrderedCutFaceReturnProfile PermutationFirstReturnRestriction

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}
  (r : Reading data)

def keep : Set V := (r.hom '' {i : Fin 18 | 11 ≤ i.val})ᶜ

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem keep_point (i : Fin 18) : r.hom i ∈ keep r ↔ i.val < 11 := by
  change (¬ ∃ j : Fin 18, 11 ≤ j.val ∧ r.hom j = r.hom i) ↔ i.val < 11
  simp only [r.injective.eq_iff, exists_eq_right, not_le]

def port (j : Fin 11) : keep r := ⟨r.hom (j.castAdd 7), (keep_point r _).mpr j.isLt⟩

def boundaryDart (j : Fin 11) : (G.induce (keep r)).Dart :=
  ⟨(port r j, port r (j + 1)), r.hom.map_rel (boundary_adjacent j)⟩

def outsideRotation : Data (G.induce (keep r)) :=
  InducedGraphRotation.rotation (keep r) data (boundaryDart r 0)

theorem outside_cyclic (cyclic : data.IsVertexwiseCyclic) :
    (outsideRotation r).IsVertexwiseCyclic :=
  InducedGraphRotation.cyclic (keep r) data cyclic _

def fanDart (j : Fin 11) (i : Fin (fan j).length) : G.Dart :=
  ⟨(r.hom (j.castAdd 7), r.hom ((fan j).get i)), r.hom.map_rel (fan_adjacent j i)⟩

variable (tri : Triangular data)
include tri

theorem fan_step (j : Fin 11) (n : ℕ) (hn : n + 1 < (fan j).length) :
    data.vertexRotation (fanDart r j ⟨n, by omega⟩) =
      fanDart r j ⟨n + 1, hn⟩ := by
  obtain ⟨_, _, h⟩ := corner r tri ((List.isChain_iff_getElem.mp (fan_chain j)) n hn)
  exact h

theorem fan_power (j : Fin 11) : ∀ n (hn : n < (fan j).length),
    (data.vertexRotation ^ n) (fanDart r j ⟨0, by have := fan_size j; omega⟩) =
      fanDart r j ⟨n, hn⟩ := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
    exact fan_step r tri j n hn

theorem boundary_arc (j : Fin 11) :
    ReturnArc data.vertexRotation (InducedGraphRotation.retained (keep r))
      (InducedGraphRotation.darts (keep r) (boundaryDart r (j - 1)).symm).val
      (InducedGraphRotation.darts (keep r) (boundaryDart r j)).val
      ((fan j).length - 1) := by
  have size := fan_size j
  have start : (InducedGraphRotation.darts (keep r) (boundaryDart r (j - 1)).symm).val =
      fanDart r j ⟨0, by omega⟩ := by
    apply Dart.ext
    simp [InducedGraphRotation.darts, boundaryDart, port, fanDart]
    simpa only [List.get_eq_getElem] using congrArg r.hom (fan_first j).symm
  have finish : (InducedGraphRotation.darts (keep r) (boundaryDart r j)).val =
      fanDart r j ⟨(fan j).length - 1, by omega⟩ := by
    apply Dart.ext
    simp [InducedGraphRotation.darts, boundaryDart, port, fanDart]
    simpa only [List.get_eq_getElem] using congrArg r.hom (fan_last j).symm
  rw [start, finish]
  refine ⟨by omega, fan_power r tri j _ (by omega), ?_⟩
  intro i hi hil hkeep
  have hil' : i < (fan j).length := by omega
  rw [fan_power r tri j i hil'] at hkeep
  have low := (keep_point r ((fan j).get ⟨i, hil'⟩)).mp hkeep.2
  have high := fan_internal j ⟨i, hil'⟩ hi (by dsimp; omega)
  omega

/-- Deletion turns every source fan into exactly one boundary face step. -/
theorem boundary_step (j : Fin 11) :
    (outsideRotation r).toRotationSystem.phi (boundaryDart r j) =
      boundaryDart r (j + 1) := by
  have h := InducedGraphRotation.next_of_arc (keep r) data (boundaryDart r 0)
    (boundaryDart r j).symm (boundaryDart r (j + 1))
    (by simpa using boundary_arc r tri (j + 1))
  exact h

def outsideRing : List (G.induce (keep r)).Dart := List.ofFn (boundaryDart r)

theorem outside_boundary : IsCyclicChain
    (fun a b => b = (outsideRotation r).toRotationSystem.phi a) (outsideRing r) := by
  change IsCyclicChain (fun a b : (G.induce (keep r)).Dart =>
    b = (outsideRotation r).vertexRotation a.symm) (List.ofFn (boundaryDart r))
  apply Hypermap.isCyclicChain_of_rel_getElem
  intro i k hi hk hik
  have hi' : i < 11 := by simpa only [List.length_ofFn] using hi
  have hk' : k < 11 := by simpa only [List.length_ofFn] using hk
  have idx : (⟨k, hk'⟩ : Fin 11) = ⟨i, hi'⟩ + 1 := by
    apply Fin.ext
    exact hik
  have step : boundaryDart r (⟨i, hi'⟩ + 1) =
      (outsideRotation r).vertexRotation (boundaryDart r ⟨i, hi'⟩).symm :=
    (boundary_step r tri ⟨i, hi'⟩).symm
  simpa only [List.getElem_ofFn, idx] using step

omit tri in
theorem port_injective : Function.Injective (port r) := by
  intro a b h
  have h' := r.injective (congrArg Subtype.val h)
  exact Fin.ext (congrArg (fun i : Fin 18 => i.val) h')

omit tri in
theorem outside_distinct : (outsideRing r).Nodup := by
  apply List.nodup_ofFn.mpr
  intro a b h
  exact port_injective r (congrArg (fun d => d.fst) h)

omit tri in
theorem outside_order : (outsideRing r).map (fun d => d.fst) = List.ofFn (port r) := by
  simp only [outsideRing, List.map_ofFn]
  rfl

end
end FourColor.ThreeBlockDiskBoundary
