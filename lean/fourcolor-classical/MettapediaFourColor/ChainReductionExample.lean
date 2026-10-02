import MettapediaFourColor.NearLinearChainOccurrence
import MettapediaFourColor.NearLinearChainExample

/-! The retained 42-vertex example supplies the complete geometric occurrence
contract. Its rotation is reversed to match the chosen Y/H construction.
Triangularity and cyclicity are certified; global planarity and flatness
remain in the independent program audit. -/

namespace FourColor.ChainReductionExample

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation

set_option maxRecDepth 65536

abbrev graph := NearLinearChainExample.graph
local instance : graph.LocallyFinite := fun v => Subtype.fintype (fun w => graph.Adj v w)

def star (u : Fin 42) := (NearLinearChainExample.star u).reverse

def next (u v : Fin 42) : Fin 42 :=
  (star u).getD (((star u).idxOf v + 1) % (star u).length) 0

def prev (u v : Fin 42) : Fin 42 :=
  (star u).getD (((star u).idxOf v + (star u).length - 1) % (star u).length) 0

theorem step_laws : ∀ u v : Fin 42, graph.Adj u v →
    graph.Adj u (next u v) ∧ graph.Adj u (prev u v) ∧
    prev u (next u v) = v ∧ next u (prev u v) = v := by decide +kernel

def walk (u : Fin 42) : ℕ → Fin 42 → Fin 42
  | 0, v => v
  | n + 1, v => next u (walk u n v)

set_option maxHeartbeats 0 in
-- Explicit finite witnesses for reachability in every star.
theorem reaches : ∀ u : Fin 42,
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
  outer := ⟨(0, 12), by decide +kernel⟩

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
    have xmem : x.snd ∈ star u := List.mem_reverse.mpr (hx ▸ x.adj)
    have ymem : y.snd ∈ star u := List.mem_reverse.mpr (hy ▸ y.adj)
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

set_option maxRecDepth 65536 in
/-- Every facial return closes after the three oriented triangle steps. -/
theorem triangular : ExceptionalOverlap.Triangular rotation := by
  unfold ExceptionalOverlap.Triangular
  decide +kernel

/-- All fields are actual source geometry; no colouring premise occurs. -/
def occurrence : NearLinearChainOccurrence.Occurrence rotation where
  hom := NearLinearChainExample.occurrence
  turn := by decide +kernel
  degree_eq := by decide +kernel
  core_injective := NearLinearChainExample.injective.injOn
  outside := by
    intro p v hp hv eq
    have same := NearLinearChainExample.injective eq
    subst v
    omega

theorem disk_injective : Function.Injective
    (Hypermap.embdd (cfmap NearLinearChainConstruction.config).map
      (DualGraphQuery.map rotation) (cfring NearLinearChainConstruction.config)
      (NearLinearChainOccurrence.reading occurrence)) :=
  NearLinearChainOccurrence.disk_injective occurrence cyclic triangular

end FourColor.ChainReductionExample
