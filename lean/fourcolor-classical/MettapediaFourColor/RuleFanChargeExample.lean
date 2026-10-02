import MettapediaFourColor.RuleFanCharge
import MettapediaFourColor.ChainBoundaryGeometry

/-! A nonempty instance of the twelve-unit fan budget. Two replayed edge
flips of the retained spherical example leave the fan intact and make every
neighbour of its seven-valent receiver low. The cyclic geometry and the
positive charge conclusion are kernel checked. Global sphericality is
independently replayed from the saved flips. -/

namespace FourColor.RuleFanChargeExample

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation

set_option maxRecDepth 65536

def rowSource (v : Fin 162) : String :=
  match v.val with
  | 6 => "72 76 148 75 73 123\n"
  | 30 => "63 64 139 75 148 144\n"
  | 72 => "6 123 50 19 124 76\n"
  | 73 => "6 75 74 130 22 123\n"
  | 75 => "6 148 30 139 74 73\n"
  | 123 => "6 73 22 119 117 50 72\n"
  | 139 => "26 74 75 30 64 137 135\n"
  | 148 => "6 76 146 144 30 75\n"
  | _ => ChainBoundaryExample.rowSource v

def star (v : Fin 162) : List (Fin 162) :=
  ((NearLinearDiamondData.rows (rowSource v)).headD []).map fun n => ⟨n % 162, by omega⟩

set_option maxHeartbeats 0 in
-- Replay the complete finite local observation in the kernel.
private theorem symmetric : ∀ u v : Fin 162, v ∈ star u → u ∈ star v := by
  have rows : ∀ u : Fin 162, (star u).all (fun v => decide (u ∈ star v)) = true := by
    intro u
    fin_cases u <;> decide +kernel
  intro u v hv
  exact of_decide_eq_true ((List.all_eq_true.mp (rows u)) v hv)
set_option maxHeartbeats 0 in
-- Replay the complete finite local observation in the kernel.
private theorem loopless : ∀ v : Fin 162, v ∉ star v := by
  intro v
  fin_cases v <;> decide +kernel

def graph : SimpleGraph (Fin 162) where
  Adj u v := v ∈ star u
  symm := ⟨symmetric⟩
  loopless := ⟨loopless⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ star _))
instance : graph.LocallyFinite := fun v => Subtype.fintype (fun w => graph.Adj v w)

def next (u v : Fin 162) : Fin 162 :=
  (star u).getD (((star u).idxOf v + 1) % (star u).length) 0

def prev (u v : Fin 162) : Fin 162 :=
  (star u).getD (((star u).idxOf v + (star u).length - 1) % (star u).length) 0

set_option maxHeartbeats 0 in
-- Replay the complete finite local observation in the kernel.
theorem step_laws : ∀ u v : Fin 162, graph.Adj u v →
    graph.Adj u (next u v) ∧ graph.Adj u (prev u v) ∧
    prev u (next u v) = v ∧ next u (prev u v) = v := by
  have rows : ∀ u : Fin 162, (star u).all (fun v => decide (
      graph.Adj u (next u v) ∧ graph.Adj u (prev u v) ∧
      prev u (next u v) = v ∧ next u (prev u v) = v)) = true := by
    intro u
    fin_cases u <;> decide +kernel
  intro u v hv
  exact of_decide_eq_true ((List.all_eq_true.mp (rows u)) v hv)

def walk (u : Fin 162) : ℕ → Fin 162 → Fin 162
  | 0, v => v
  | n + 1, v => next u (walk u n v)

set_option maxHeartbeats 0 in
-- Replay the complete finite local observation in the kernel.
theorem reaches : ∀ u : Fin 162,
    (star u).all (fun v => (star u).all (fun w =>
      decide (walk u (((star u).idxOf w + (star u).length - (star u).idxOf v) %
        (star u).length) v = w))) = true := by
  intro u
  fin_cases u <;> decide +kernel

def rotation : Data graph where
  vertexRotation := {
    toFun := fun d => ⟨(d.fst, next d.fst d.snd), (step_laws d.fst d.snd d.adj).1⟩
    invFun := fun d => ⟨(d.fst, prev d.fst d.snd), (step_laws d.fst d.snd d.adj).2.1⟩
    left_inv := fun d => SimpleGraph.Dart.ext (G := graph) _ _
      (Prod.ext rfl (step_laws d.fst d.snd d.adj).2.2.1)
    right_inv := fun d => SimpleGraph.Dart.ext (G := graph) _ _
      (Prod.ext rfl (step_laws d.fst d.snd d.adj).2.2.2) }
  vertexRotation_fst := fun _ => rfl
  outer := ⟨(112, 81), by decide +kernel⟩

private theorem pow_reading (n : ℕ) (d : graph.Dart) :
    ((rotation.vertexRotation ^ n) d).fst = d.fst ∧
    ((rotation.vertexRotation ^ n) d).snd = walk d.fst n d.snd := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply]
    exact ⟨ih.1, by change next _ _ = _; rw [ih.1, ih.2]; rfl⟩

/-- All outgoing darts at each vertex form one rotation cycle. -/
theorem cyclic : rotation.IsVertexwiseCyclic := by
  intro u
  refine ⟨⟨?_, rotation.vertexRotation.injective.injOn, ?_⟩, ?_⟩
  · intro d hd
    exact (rotation.vertexRotation_fst d).trans hd
  · intro d hd
    exact ⟨rotation.vertexRotation.symm d, hd, Equiv.apply_symm_apply _ d⟩
  · intro x hx y hy
    have xmem : x.snd ∈ star u := hx ▸ x.adj
    have ymem : y.snd ∈ star u := hy ▸ y.adj
    have h := (List.all_eq_true.mp ((List.all_eq_true.mp (reaches u)) x.snd xmem))
      y.snd ymem
    let n := ((star u).idxOf y.snd + (star u).length - (star u).idxOf x.snd) %
      (star u).length
    have hn' : walk u n x.snd = y.snd := of_decide_eq_true h
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast]
    apply SimpleGraph.Dart.ext
    exact Prod.ext ((pow_reading n x).1.trans (hx.trans hy.symm))
      ((pow_reading n x).2.trans (by rwa [hx]))

set_option maxHeartbeats 0 in
-- Replay the complete finite local observation in the kernel.
/-- Every facial return closes after the three oriented triangle steps. -/
theorem triangular : ExceptionalOverlap.Triangular rotation := by
  have rows : ∀ u : Fin 162, (star u).all (fun v => decide (
      next (next v u) v = u ∧ next u (next v u) = v)) = true := by
    intro u
    fin_cases u <;> decide +kernel
  intro d
  have h := of_decide_eq_true ((List.all_eq_true.mp (rows d.fst)) d.snd d.adj)
  apply SimpleGraph.Dart.ext
  change (next (next d.snd d.fst) d.snd,
    next (next (next d.snd d.fst) d.snd) (next d.snd d.fst)) = (d.fst, d.snd)
  exact Prod.ext h.1 (by rw [h.1]; exact h.2)

def root : graph.Dart := ⟨(122,76), by decide +kernel⟩

set_option maxHeartbeats 0 in
-- Replay the complete finite local observation in the kernel.
theorem wings : RuleFanCharge.Wings (rotation := rotation) root := by
  constructor <;> decide +kernel

theorem receiver_seven : graph.degree root.snd = 7 := by decide +kernel

set_option maxHeartbeats 0 in
-- Replay the complete finite local observation in the kernel.
theorem neighbors_low : ∀ v, graph.Adj root.snd v →
    5 ≤ graph.degree v ∧ graph.degree v ≤ 6 := by decide +kernel

/-- The general shared-fan law, rather than a table of charges, proves this
example has strictly positive final charge. -/
theorem positive : 2 ≤ NearLinearCharge.finalCharge rotation root.snd :=
  RuleFanCharge.positive_of_low cyclic triangular root wings receiver_seven neighbors_low

end FourColor.RuleFanChargeExample
