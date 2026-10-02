import MettapediaFourColor.CyclicFanContinuation

/-!
# An extra charge rule closes a reducible triangle chain

The oriented source rule 004_1 retains two successive facial corners at a
low-degree outer vertex. A five-valent sender supplies the third corner
when its second successor is also five. At outer degree five this is a
mixed diamond; at degree six it is the existing eight-port chain.
Both branches use the same actual vertices, rotation and exterior.
-/

namespace FourColor.ExtraChargeReduction

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearRuleData NearLinearCharge ExceptionalOverlap ExceptionalCoreOrientation
open ChainFanRecognition (walk walk_fst walk_next)

local instance (r : Fin 84) : NeZero (size r) :=
  ⟨by have := (headers r).1; omega⟩

variable {V : Type*} [Finite V]
  {G : SimpleGraph V} [G.LocallyFinite]
  (rotation : Data G)

def root (x : Occurrence rotation (5 : Fin 84)) : G.Dart :=
  ⟨(x.vertex 0, x.vertex 1), x.edge 0 1 (by decide +kernel)⟩

def outerRoot (x : Occurrence rotation (5 : Fin 84)) : G.Dart :=
  ⟨(x.vertex 3, x.vertex 4), x.edge 3 4 (by decide +kernel)⟩

def sharedRoot (x : Occurrence rotation (5 : Fin 84)) : G.Dart :=
  ⟨(x.vertex 3, x.vertex 2), x.edge 3 2 (by decide +kernel)⟩

/-- The missing triangle is obtained by closing the sender's actual star. -/
theorem closing (cyclic : rotation.IsVertexwiseCyclic) (tri : Triangular rotation)
    (x : Occurrence rotation (5 : Fin 84)) (sender : G.degree (x.vertex 0) = 5) :
    Corner rotation (x.vertex 3) (x.vertex 0)
      (walk rotation (root rotation x) 2).snd := by
  let e : G.Dart := ⟨(x.vertex 0,x.vertex 3), x.edge 0 3 (by decide +kernel)⟩
  let f : G.Dart := ⟨(x.vertex 0,x.vertex 2), x.edge 0 2 (by decide +kernel)⟩
  have ef : rotation.vertexRotation e = f :=
    x.turn 0 3 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have fr : rotation.vertexRotation f = root rotation x :=
    x.turn 0 2 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have twice : (rotation.vertexRotation ^ 2) e = root rotation x := by
    simp only [pow_succ', pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply, ef, fr]
  have period := FacialStarCompletion.pow_degree rotation cyclic e
  change (rotation.vertexRotation ^ G.degree (x.vertex 0)) e = e at period
  rw [sender] at period
  have close : rotation.vertexRotation (walk rotation (root rotation x) 2) = e := by
    calc
      _ = (rotation.vertexRotation ^ 5) e := by
        rw [walk, ← twice]
        simp only [pow_succ', pow_zero, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
      _ = e := period
  have adj : G.Adj (x.vertex 0) (walk rotation (root rotation x) 2).snd := by
    simpa only [walk_fst, root] using (walk rotation (root rotation x) 2).adj
  have corner : Corner rotation (x.vertex 0)
      (walk rotation (root rotation x) 2).snd (x.vertex 3) := by
    refine ⟨adj, x.edge 0 3 (by decide +kernel), ?_⟩
    have eq : (⟨(x.vertex 0, (walk rotation (root rotation x) 2).snd), adj⟩ : G.Dart) =
        walk rotation (root rotation x) 2 := by
      apply SimpleGraph.Dart.ext
      exact Prod.ext (walk_fst rotation (root rotation x) 2).symm rfl
    rw [eq]
    exact close
  exact Corner.rotate rotation tri (Corner.rotate rotation tri corner)

/-- One star-closing law supplies either of two previously certified repairs. -/
theorem alternatives (cyclic : rotation.IsVertexwiseCyclic) (tri : Triangular rotation)
    (x : Occurrence rotation (5 : Fin 84))
    (sender : G.degree (x.vertex 0) = 5) (shared : G.degree (x.vertex 2) = 6)
    (companion : G.degree (walk rotation (root rotation x) 2).snd = 5) :
    RulePairDiamond.MixedAt rotation (sharedRoot rotation x) ∨
    (G.degree (outerRoot rotation x).fst = 6 ∧
      ∀ n : Fin 4, G.degree (walk rotation (outerRoot rotation x) n.val).snd =
        ChainFanRecognition.word n) := by
  have outer := x.degree 3
  rw [show lower 5 3 = 5 from by decide +kernel,
    show upper 5 3 = 6 from by decide +kernel] at outer
  have tip := x.degree 4
  rw [show lower 5 4 = 5 from by decide +kernel,
    show upper 5 4 = 5 from by decide +kernel] at tip
  have tip5 : G.degree (x.vertex 4) = 5 := by omega
  let d : G.Dart := ⟨(x.vertex 3,x.vertex 2), x.edge 3 2 (by decide +kernel)⟩
  let e : G.Dart := ⟨(x.vertex 3,x.vertex 0), x.edge 3 0 (by decide +kernel)⟩
  have first : rotation.vertexRotation (outerRoot rotation x) = d :=
    x.turn 3 4 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have second : rotation.vertexRotation d = e :=
    x.turn 3 2 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have close := closing rotation cyclic tri x sender
  by_cases five : G.degree (x.vertex 3) = 5
  · refine Or.inl ⟨five, shared, ?_, ?_⟩
    · change G.degree (rotation.vertexRotation d).snd = 5
      rw [second]; exact sender
    · have prev : rotation.vertexRotation.symm d = outerRoot rotation x := by
        rw [← first, Equiv.symm_apply_apply]
      change G.degree (rotation.vertexRotation.symm d).snd = 5
      rw [prev]; exact tip5
  · refine Or.inr ⟨by change G.degree (x.vertex 3) = 6; omega, ?_⟩
    intro n
    fin_cases n
    · exact tip5
    · change G.degree (rotation.vertexRotation (outerRoot rotation x)).snd = 6
      rw [first]; exact shared
    · change G.degree (rotation.vertexRotation (rotation.vertexRotation
        (outerRoot rotation x))).snd = 5
      rw [first, second]; exact sender
    · change G.degree (rotation.vertexRotation (rotation.vertexRotation
        (rotation.vertexRotation (outerRoot rotation x)))).snd = 5
      rw [first, second]
      obtain ⟨_, hp, ht⟩ := close
      change rotation.vertexRotation e = _ at ht
      rw [ht]
      exact companion

theorem mixed_of_five (cyclic : rotation.IsVertexwiseCyclic) (tri : Triangular rotation)
    (x : Occurrence rotation (5 : Fin 84))
    (sender : G.degree (x.vertex 0) = 5) (shared : G.degree (x.vertex 2) = 6)
    (companion : G.degree (walk rotation (root rotation x) 2).snd = 5)
    (outer : G.degree (x.vertex 3) = 5) :
    RulePairDiamond.MixedAt rotation (sharedRoot rotation x) := by
  rcases alternatives rotation cyclic tri x sender shared companion with mixed | ⟨six, _⟩
  · exact mixed
  · change G.degree (x.vertex 3) = 6 at six
    omega

theorem word_of_six (cyclic : rotation.IsVertexwiseCyclic) (tri : Triangular rotation)
    (x : Occurrence rotation (5 : Fin 84))
    (sender : G.degree (x.vertex 0) = 5) (shared : G.degree (x.vertex 2) = 6)
    (companion : G.degree (walk rotation (root rotation x) 2).snd = 5)
    (outer : G.degree (x.vertex 3) = 6) :
    ∀ n : Fin 4, G.degree (walk rotation (outerRoot rotation x) n.val).snd =
      ChainFanRecognition.word n := by
  rcases alternatives rotation cyclic tri x sender shared companion with mixed | ⟨_, word⟩
  · have h := mixed.five
    change G.degree (x.vertex 3) = 5 at h
    omega
  · exact word

/-- The retained fan chooses an actual edge from its shared five to the
first free vertex. The two triangles determine its next two successors. -/
def fanRoot (tri : Triangular rotation) (d : G.Dart) : G.Dart :=
  ⟨((walk rotation d 2).snd, (walk rotation d 3).snd), by
    have h := consecutive_adjacent rotation tri (walk rotation d 2)
    rw [walk_next] at h
    exact h⟩

omit [Finite V] in
theorem fan_companion (tri : Triangular rotation) (d : G.Dart) :
    (walk rotation (fanRoot rotation tri d) 2).snd = (walk rotation d 1).snd := by
  have corner (n : ℕ) : Corner rotation d.fst
      (walk rotation d n).snd (walk rotation d (n+1)).snd := by
    have adj (i : ℕ) : G.Adj d.fst (walk rotation d i).snd := by
      simpa only [walk_fst] using (walk rotation d i).adj
    refine ⟨adj n, adj (n+1), ?_⟩
    have eq (i : ℕ) : (⟨(d.fst,(walk rotation d i).snd),adj i⟩ : G.Dart) =
        walk rotation d i := by
      apply SimpleGraph.Dart.ext
      exact Prod.ext (walk_fst rotation d i).symm rfl
    rw [eq, eq, walk_next]
  obtain ⟨_, hs, first⟩ := Corner.rotate rotation tri (corner 2)
  obtain ⟨_, hp, second⟩ := Corner.rotate rotation tri (Corner.rotate rotation tri (corner 1))
  change rotation.vertexRotation (fanRoot rotation tri d) = _ at first
  change (rotation.vertexRotation (rotation.vertexRotation (fanRoot rotation tri d))).snd = _
  rw [first, second]

end FourColor.ExtraChargeReduction

namespace FourColor.ActualExtraChargeReduction

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality NearLinearCharge
open ActualRulePairDiamond (graph rotation)
open ExtraChargeReduction

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

local instance (r : Fin 84) : NeZero (NearLinearRuleData.size r) :=
  ⟨by have := (NearLinearRuleData.headers r).1; omega⟩

/-- The two alternatives consume genuine reconstruction theorems in the
actual map. No flatness, catalogue query or abstract repair oracle is assumed. -/
theorem not_occurrence (x : Occurrence (rotation original minimal) (5 : Fin 84))
    (sender : (graph original minimal).degree (x.vertex 0) = 5)
    (shared : (graph original minimal).degree (x.vertex 2) = 6)
    (companion : (graph original minimal).degree
      (ChainFanRecognition.walk (rotation original minimal) (root _ x) 2).snd = 5) :
    False := by
  rcases alternatives (rotation original minimal)
      (MinimalExceptionalEmbedding.cyclic original minimal)
      (MinimalExceptionalEmbedding.triangular original minimal) x sender shared companion with
    diamond | ⟨six, word⟩
  · obtain ⟨d', pattern⟩ := ActualRulePairDiamond.face_pattern original minimal _ diamond
    exact MixedDiamondPatch.Tangle.FaceReduction.not_in_minimal_counterexample_of_face_pattern
      original d' pattern minimal
  · exact ChainFanRecognition.not_in_minimal original minimal _ six word

/-- The forbidden source rule is detected on its original marked edge. -/
theorem check_false (d : (graph original minimal).Dart)
    (sender : (graph original minimal).degree d.fst = 5)
    (shared : (graph original minimal).degree
      (RuleMatcher.candidate (rotation original minimal) 5 d 2) = 6)
    (companion : (graph original minimal).degree
      (ChainFanRecognition.walk (rotation original minimal) d 2).snd = 5) :
    RuleMatcher.check (rotation original minimal) 5 d = false := by
  apply Bool.eq_false_iff.mpr
  intro checked
  obtain ⟨x, xs, xt⟩ := (RuleMatcher.check_iff (rotation original minimal) d).mp checked
  have eq : root (rotation original minimal) x = d := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext xs xt
  rw [RuleMatcher.candidate_eq (rotation original minimal) d x xs xt] at shared
  exact not_occurrence original minimal x (xs ▸ sender) shared (eq ▸ companion)

/-- In the single-five residual, the retained source rule cannot supply
extra charge: it would construct the mixed diamond or eight-port chain. -/
theorem residual_check_false (d : (graph original minimal).Dart)
    (fixed : RuleFanSupply.Fixed (rotation original minimal) d)
    (residual : ∀ w, (graph original minimal).Adj
      (RuleFanSupply.firstFree (rotation original minimal) d) w →
      w ≠ (ChainFanRecognition.walk (rotation original minimal) d 2).snd →
      (graph original minimal).degree w = 6) :
    RuleMatcher.check (rotation original minimal) 5
      (fanRoot (rotation original minimal)
        (MinimalExceptionalEmbedding.triangular original minimal) d) = false := by
  let r := rotation original minimal
  let tri := MinimalExceptionalEmbedding.triangular original minimal
  let e := fanRoot r tri d
  have sender : (graph original minimal).degree e.fst = 5 := fixed.second
  have companion : (graph original minimal).degree (ChainFanRecognition.walk r e 2).snd = 5 := by
    rw [fan_companion]
    exact fixed.first
  apply Bool.eq_false_iff.mpr
  intro checked
  obtain ⟨x, xs, xt⟩ := (RuleMatcher.check_iff r e).mp checked
  change x.vertex 0 = e.fst at xs
  change x.vertex 1 = e.snd at xt
  have adj : (graph original minimal).Adj (RuleFanSupply.firstFree r d) (x.vertex 2) := by
    have h := x.edge 1 2 (by decide +kernel)
    rw [xt] at h
    exact h
  have ne : x.vertex 2 ≠ (ChainFanRecognition.walk r d 2).snd := by
    have h := (x.edge 0 2 (by decide +kernel)).ne.symm
    rw [xs] at h
    exact h
  have shared := residual _ adj ne
  have shared' : (graph original minimal).degree (RuleMatcher.candidate r 5 e 2) = 6 := by
    rw [RuleMatcher.candidate_eq r e x xs xt]
    exact shared
  have no := check_false original minimal e sender shared' companion
  rw [checked] at no
  contradiction

/-- The preceding charge classification now carries a certified restriction
on the actual extra-rule observation at its unresolved branch. -/
theorem flat_alternatives (d : (graph original minimal).Dart)
    (fixed : RuleFanSupply.Fixed (rotation original minimal) d)
    (seven : (graph original minimal).degree
      (RuleFanSupply.firstFree (rotation original minimal) d) = 7)
    (flat : NearLinearCharge.finalCharge (rotation original minimal)
      (RuleFanSupply.firstFree (rotation original minimal) d) = 0) :
    (∃ w, w ≠ d.snd ∧ w ≠ RuleFanSupply.firstFree (rotation original minimal) d ∧
      (graph original minimal).Adj (RuleFanSupply.firstFree (rotation original minimal) d) w ∧
      w ∈ LocalCoverageAssembly.closedBall (graph original minimal) d.snd 3 ∧
      7 ≤ (graph original minimal).degree w) ∨
    ((∀ w, (graph original minimal).Adj (RuleFanSupply.firstFree (rotation original minimal) d) w →
      w ≠ (ChainFanRecognition.walk (rotation original minimal) d 2).snd →
      (graph original minimal).degree w = 6) ∧
      RuleMatcher.check (rotation original minimal) 5
        (fanRoot (rotation original minimal)
          (MinimalExceptionalEmbedding.triangular original minimal) d) = false) := by
  rcases ActualCyclicFanContinuation.third_or_single_five original minimal d fixed seven flat with
    high | residual
  · exact Or.inl high
  · exact Or.inr ⟨residual, residual_check_false original minimal d fixed residual⟩

end
end FourColor.ActualExtraChargeReduction
