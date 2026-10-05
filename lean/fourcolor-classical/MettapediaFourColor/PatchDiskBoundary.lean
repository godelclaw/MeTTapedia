import MettapediaFourColor.PatchDiskSource

/-! # Ordered exterior boundary from short source fans

Deleting the actual core induces the first-return rotation. Facial source
fans prove every boundary step. Core and local neighbour injectivity make
boundary darts distinct even when boundary vertices coincide.
-/

namespace FourColor.PatchDisk.Reading

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCoreOrientation ExceptionalOverlap
open GoertzelV24OrderedCutFaceReturnProfile PermutationFirstReturnRestriction

noncomputable section

variable {c b : ℕ} [NeZero b] {s : Source c b}
  {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}
  (r : Reading s data)

def keep : Set V := (r.hom '' {i : Fin (b + c) | b ≤ i.val})ᶜ

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem keep_point (i : Fin (b + c)) : r.hom i ∈ keep r ↔ i.val < b := by
  constructor
  · intro h
    by_contra low
    exact h ⟨i, show b ≤ i.val from Nat.le_of_not_gt low, rfl⟩
  · intro low
    exact r.no_capture i (by omega)

def port (j : Fin b) : keep r := ⟨r.hom (j.castAdd c), (keep_point r _).mpr j.isLt⟩

def boundaryDart (j : Fin b) : (G.induce (keep r)).Dart :=
  ⟨(port r j, port r (j + 1)), r.hom.map_rel (s.boundary_adjacent j)⟩

def outsideRotation : Data (G.induce (keep r)) :=
  InducedGraphRotation.rotation (keep r) data (boundaryDart r 0)

theorem outside_cyclic (cyclic : data.IsVertexwiseCyclic) :
    (outsideRotation r).IsVertexwiseCyclic :=
  InducedGraphRotation.cyclic (keep r) data cyclic _

def fanDart (j : Fin b) (i : Fin (s.fan j).length) : G.Dart :=
  ⟨(r.hom (j.castAdd c), r.hom ((s.fan j).get i)), r.hom.map_rel (s.fan_adjacent j i)⟩

variable (tri : Triangular data)
include tri

theorem fan_step (j : Fin b) (n : ℕ) (hn : n + 1 < (s.fan j).length) :
    data.vertexRotation (fanDart r j ⟨n, by omega⟩) =
      fanDart r j ⟨n + 1, hn⟩ := by
  obtain ⟨_, _, h⟩ := corner r tri ((List.isChain_iff_getElem.mp (s.fan_chain j)) n hn)
  exact h

theorem fan_power (j : Fin b) : ∀ n (hn : n < (s.fan j).length),
    (data.vertexRotation ^ n) (fanDart r j ⟨0, by have := s.fan_size j; omega⟩) =
      fanDart r j ⟨n, hn⟩ := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    rw [pow_succ', Equiv.Perm.mul_apply, ih (by omega)]
    exact fan_step r tri j n hn

theorem boundary_arc (j : Fin b) :
    ReturnArc data.vertexRotation (InducedGraphRotation.retained (keep r))
      (InducedGraphRotation.darts (keep r) (boundaryDart r (j - 1)).symm).val
      (InducedGraphRotation.darts (keep r) (boundaryDart r j)).val
      ((s.fan j).length - 1) := by
  have size := s.fan_size j
  have start : (InducedGraphRotation.darts (keep r) (boundaryDart r (j - 1)).symm).val =
      fanDart r j ⟨0, by omega⟩ := by
    apply Dart.ext
    simp [InducedGraphRotation.darts, boundaryDart, port, fanDart]
    simpa only [List.get_eq_getElem] using congrArg r.hom (s.fan_first j).symm
  have finish : (InducedGraphRotation.darts (keep r) (boundaryDart r j)).val =
      fanDart r j ⟨(s.fan j).length - 1, by omega⟩ := by
    apply Dart.ext
    simp [InducedGraphRotation.darts, boundaryDart, port, fanDart]
    simpa only [List.get_eq_getElem] using congrArg r.hom (s.fan_last j).symm
  rw [start, finish]
  refine ⟨by omega, fan_power r tri j _ (by omega), ?_⟩
  intro i hi hil hkeep
  have hil' : i < (s.fan j).length := by omega
  rw [fan_power r tri j i hil'] at hkeep
  have low := (keep_point r ((s.fan j).get ⟨i, hil'⟩)).mp hkeep.2
  have high := s.fan_internal j ⟨i, hil'⟩ hi (by dsimp; omega)
  omega

/-- Deletion turns every source s.fan into exactly one boundary face step. -/
theorem boundary_step (j : Fin b) :
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
  have hi' : i < b := by simpa only [List.length_ofFn] using hi
  have hk' : k < b := by simpa only [List.length_ofFn] using hk
  have idx : (⟨k, hk'⟩ : Fin b) = ⟨i, hi'⟩ + 1 := by
    apply Fin.ext
    have one : (1 : Fin b).val = 1 := by
      change 1 % b = 1
      apply Nat.mod_eq_of_lt
      have := s.boundary_size
      omega
    simpa only [List.length_ofFn, Fin.val_add, one] using hik
  have step : boundaryDart r (⟨i, hi'⟩ + 1) =
      (outsideRotation r).vertexRotation (boundaryDart r ⟨i, hi'⟩).symm :=
    (boundary_step r tri ⟨i, hi'⟩).symm
  simpa only [List.getElem_ofFn, idx] using step

/-- Distinct directed boundary edges do not require distinct boundary vertices. -/
theorem boundaryDart_injective : Function.Injective (boundaryDart r) := by
  intro a b h
  have first : r.hom (a.castAdd c) = r.hom (b.castAdd c) :=
    congrArg (fun d => d.fst.val) h
  have second : r.hom ((a + 1).castAdd c) = r.hom ((b + 1).castAdd c) :=
    congrArg (fun d => d.snd.val) h
  obtain ⟨ab,adja,stepa⟩ := (r.turn _ _ _ (s.tip_turn a)).rotate data tri
  obtain ⟨bb,bt,stepb⟩ := (r.turn _ _ _ (s.tip_turn b)).rotate data tri
  have same : (⟨(r.hom ((a + 1).castAdd c), r.hom (a.castAdd c)),ab⟩ : G.Dart) =
      ⟨(r.hom ((b + 1).castAdd c), r.hom (b.castAdd c)),bb⟩ :=
    Dart.ext _ _ (Prod.ext second first)
  have tips : r.hom (s.tip a) = r.hom (s.tip b) :=
    congrArg (fun d => d.snd)
      (stepa.symm.trans ((congrArg data.vertexRotation same).trans stepb))
  have source_tips := r.core_injective (s.tip_core a) (s.tip_core b) tips
  have right : s.graph.Adj (s.tip a) (b.castAdd c) := source_tips.symm ▸ s.tip_adjacent b
  have ports := r.local_injective (s.tip a) (s.tip_core a)
    (s.tip_adjacent a) right first
  have values := congrArg (fun i => i.val) ports
  exact Fin.ext values

theorem outside_distinct : (outsideRing r).Nodup :=
  List.nodup_ofFn.mpr (boundaryDart_injective r tri)

omit tri in
theorem outside_order : (outsideRing r).map (fun d => d.fst) = List.ofFn (port r) := by
  simp only [outsideRing, List.map_ofFn]
  rfl

end
end FourColor.PatchDisk.Reading
