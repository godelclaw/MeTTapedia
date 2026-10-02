import MettapediaFourColor.RulePairExampleData

/-! A nonempty rule-pair consumer with certified triangular and cyclic geometry.
Flat charge and sphericality remain separate program evidence. -/

namespace FourColor.RulePairExample

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation

set_option maxRecDepth 65536

local instance (r : Fin 84) : NeZero (NearLinearRuleData.size r) :=
  ⟨by have := (NearLinearRuleData.headers r).1; omega⟩

/-- The flat encoding has one row per vertex and every label is in range. -/
theorem source_valid :
    (NearLinearDiamondData.parseRows source).isSome = true ∧
    (NearLinearDiamondData.rows source).length = 42 ∧
    (NearLinearDiamondData.rows source).all
      (fun row => row.all (fun n => decide (n < 42))) = true := by decide +kernel

def rotation : Data graph where
  vertexRotation := {
    toFun := fun d => ⟨(d.fst, next d.fst d.snd), (step_laws d.fst d.snd d.adj).1⟩
    invFun := fun d => ⟨(d.fst, prev d.fst d.snd), (step_laws d.fst d.snd d.adj).2.1⟩
    left_inv := fun d => SimpleGraph.Dart.ext (G := graph) _ _
      (Prod.ext rfl (step_laws d.fst d.snd d.adj).2.2.1)
    right_inv := fun d => SimpleGraph.Dart.ext (G := graph) _ _
      (Prod.ext rfl (step_laws d.fst d.snd d.adj).2.2.2) }
  vertexRotation_fst := fun _ => rfl
  outer := ⟨(25, 18), by decide +kernel⟩

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

set_option maxRecDepth 65536 in
/-- Every facial return closes after the three oriented triangle steps. -/
theorem triangular : ExceptionalOverlap.Triangular rotation := by
  unfold ExceptionalOverlap.Triangular
  decide +kernel

def root : graph.Dart := rotation.outer

def leftImages (i : NearLinearRuleData.Vertex 4) : Fin 42 :=
  ([25, 18, 5, 26] : List (Fin 42)).getD i.val 0

def rightImages (i : NearLinearRuleData.Vertex 5) : Fin 42 :=
  ([28, 18, 5, 19, 1] : List (Fin 42)).getD i.val 0

/-- Compute each shared vertex reading once, before checking its constraints. -/
theorem left_candidate : RuleMatcher.candidate rotation 4 root = leftImages := by
  funext i
  fin_cases i <;> decide +kernel

theorem right_candidate : RuleMatcher.candidate rotation 5
    (RulePairDiamond.secondRoot (rotation := rotation) root) = rightImages := by
  funext i
  fin_cases i <;> decide +kernel

set_option maxHeartbeats 0 in
-- The finite tests use the already certified shared vertex readings.
theorem observations :
    RuleMatcher.check rotation 4 root = true ∧
    RuleMatcher.check rotation 5 (RulePairDiamond.secondRoot (rotation := rotation) root) = true ∧
    graph.degree root.fst = 5 ∧
    graph.degree (RuleMatcher.candidate rotation 4 root 2) = 6 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold RuleMatcher.check
    rw [left_candidate]
    decide +kernel
  · unfold RuleMatcher.check
    rw [right_candidate]
    decide +kernel
  · decide +kernel
  · rw [left_candidate]
    decide +kernel

/-- The example consumes the shared structural argument, rather than
independently checking a diamond conclusion. -/
theorem has_mixed : ∃ d : graph.Dart, RulePairDiamond.MixedAt rotation d :=
  RulePairDiamond.mixed_of_checks cyclic triangular root observations.1
    observations.2.1 observations.2.2.1 observations.2.2.2

end FourColor.RulePairExample
