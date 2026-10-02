import MettapediaFourColor.ExtendedChainCore
import MettapediaFourColor.RulePairDiamond

/-!
# A shared rule fan supplies three reduction patterns

The source rules 002_2 and 003_2 are read on the same directed edge.
At a degree-six sender, a degree-five next neighbour fixes the cyclic
neighbour degrees to `[receiver, 5, 5, a, b, 5]`. If both remaining
degrees lie in 5..6, the same rotation supplies a mixed diamond or one
of the eight- and nine-port chain words. The witnesses retain the actual
root and its rotation; the rules are not combined as independent views.
-/

namespace FourColor.RuleFanSupply

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearRuleData NearLinearCharge ExceptionalOverlap
open ChainFanRecognition (walk walk_fst walk_next)

local instance (r : Fin 84) : NeZero (size r) :=
  ⟨by have := (headers r).1; omega⟩

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] (rotation : Data G)

/-- The two unspecified neighbours are actual positions in the shared star. -/
def firstFree (d : G.Dart) : V := (walk rotation d 3).snd
def secondFree (d : G.Dart) : V := (walk rotation d 4).snd
def start (d : G.Dart) : G.Dart := walk rotation d 2

omit [G.LocallyFinite] in
/-- The complete star observations stay within radius two of the receiver. -/
theorem walk_near (d : G.Dart) (n : ℕ) :
    (walk rotation d n).snd ∈ LocalCoverageAssembly.closedBall G d.snd 2 := by
  have adj : G.Adj d.fst (walk rotation d n).snd := by
    simpa only [walk_fst] using (walk rotation d n).adj
  let tail : G.Walk d.fst (walk rotation d n).snd := .cons adj .nil
  let path : G.Walk d.snd (walk rotation d n).snd := .cons d.adj.symm tail
  simpa [LocalCoverageAssembly.closedBall, path, tail] using path.edist_le

omit [G.LocallyFinite] in
theorem shifted (d : G.Dart) (n : ℕ) :
    walk rotation (start rotation d) n = walk rotation d (n + 2) := by
  simp only [walk, start, ← Equiv.Perm.mul_apply, ← pow_add]

/-- The degrees needed by all three consumers, in one common cyclic order. -/
structure Fixed (d : G.Dart) : Prop where
  center : G.degree d.fst = 6
  first : G.degree (walk rotation d 1).snd = 5
  second : G.degree (walk rotation d 2).snd = 5
  last : G.degree (walk rotation d 5).snd = 5

/-- Three successive fives around the six expose the mixed diamond. -/
theorem mixed (tri : Triangular rotation) (d : G.Dart) (h : Fixed rotation d)
    (ha : G.degree (firstFree rotation d) = 5) :
    RulePairDiamond.MixedAt rotation (start rotation d).symm := by
  have pred : rotation.vertexRotation.symm (start rotation d) = walk rotation d 1 := by
    apply rotation.vertexRotation.injective
    rw [Equiv.apply_symm_apply, walk_next]
    rfl
  refine ⟨h.second, ?_, ?_, ?_⟩
  · change G.degree (walk rotation d 2).fst = 6
    rw [walk_fst]
    exact h.center
  · rw [← FacialStarCompletion.across_edge rotation tri, pred]
    exact h.first
  · rw [FacialStarCompletion.across_edge rotation tri, SimpleGraph.Dart.symm_symm]
    change G.degree (rotation.vertexRotation (walk rotation d 2)).snd = 5
    rw [walk_next]
    exact ha

theorem eight_word (d : G.Dart) (h : Fixed rotation d)
    (ha : G.degree (firstFree rotation d) = 6)
    (hb : G.degree (secondFree rotation d) = 5) :
    ∀ n : Fin 4, G.degree (walk rotation (start rotation d) n.val).snd =
      ChainFanRecognition.word n := by
  intro n
  rw [shifted]
  fin_cases n
  · exact h.second
  · exact ha
  · exact hb
  · exact h.last

theorem nine_word (d : G.Dart) (h : Fixed rotation d)
    (ha : G.degree (firstFree rotation d) = 6)
    (hb : G.degree (secondFree rotation d) = 6) :
    ∀ n : Fin 4, G.degree (walk rotation (start rotation d) n.val).snd =
      ExtendedChainCore.word n := by
  intro n
  rw [shifted]
  fin_cases n
  · exact h.second
  · exact ha
  · exact hb
  · exact h.last

/-- One structural argument covers every low-degree continuation.
The diamond branch does not need a degree observation at the second free vertex. -/
theorem alternatives (tri : Triangular rotation) (d : G.Dart) (h : Fixed rotation d)
    (ha : 5 ≤ G.degree (firstFree rotation d) ∧ G.degree (firstFree rotation d) ≤ 6)
    (hb : 5 ≤ G.degree (secondFree rotation d) ∧ G.degree (secondFree rotation d) ≤ 6) :
    RulePairDiamond.MixedAt rotation (start rotation d).symm ∨
    (∀ n : Fin 4, G.degree (walk rotation (start rotation d) n.val).snd =
      ChainFanRecognition.word n) ∨
    (∀ n : Fin 4, G.degree (walk rotation (start rotation d) n.val).snd =
      ExtendedChainCore.word n) := by
  by_cases a5 : G.degree (firstFree rotation d) = 5
  · exact Or.inl (mixed rotation tri d h a5)
  have a6 : G.degree (firstFree rotation d) = 6 := by omega
  by_cases b5 : G.degree (secondFree rotation d) = 5
  · exact Or.inr (Or.inl (eight_word rotation d h a6 b5))
  · exact Or.inr (Or.inr (nine_word rotation d h a6 (by omega)))

variable [Finite V] [DecidableEq V] [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- The two free positions cannot silently return the original receiver. -/
theorem walk_ne_receiver (cyclic : rotation.IsVertexwiseCyclic) (d : G.Dart)
    (six : G.degree d.fst = 6) (n : ℕ) (pos : 0 < n) (bound : n < 6) :
    (walk rotation d n).snd ≠ d.snd := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let ns : Fin 6 → V := fun i => (walk rotation d i.val).snd
  have adj (i : Fin 6) : G.Adj d.fst (ns i) := by
    simpa only [ns, walk_fst] using (walk rotation d i.val).adj
  have eq (i : Fin 6) : (⟨(d.fst, ns i), adj i⟩ : G.Dart) = walk rotation d i.val := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext (walk_fst rotation d i.val).symm rfl
  have inj : Function.Injective ns := by
    apply ExceptionalCoreLocalInjectivity.corner_chain_injective rotation cyclic d.fst
      (by decide) ns adj
    · intro i hi
      refine ⟨adj ⟨i, by omega⟩, adj ⟨i + 1, hi⟩, ?_⟩
      rw [eq, eq, walk_next]
    · omega
  intro same
  have he : ns ⟨n, bound⟩ = ns 0 := same
  have hn := congrArg Fin.val (inj he)
  simp only [Fin.val_zero] at hn
  omega

/-- The matcher supplies the fixed fan from two readings of the same edge.
The predecessor retained by rule 002_2 becomes position five by cyclic closure. -/
theorem fixed_of_checks (cyclic : rotation.IsVertexwiseCyclic) (d : G.Dart)
    (left : RuleMatcher.check rotation 2 d = true)
    (right : RuleMatcher.check rotation 4 d = true)
    (six : G.degree d.fst = 6)
    (shared : G.degree (RuleMatcher.candidate rotation 4 d 2) = 5) :
    Fixed rotation d := by
  obtain ⟨x, xs, xt⟩ := (RuleMatcher.check_iff rotation d).mp left
  obtain ⟨y, ys, yt⟩ := (RuleMatcher.check_iff rotation d).mp right
  have rx : (⟨(x.vertex 0, x.vertex 1), x.edge 0 1 (by decide +kernel)⟩ : G.Dart) = d := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext xs xt
  have ry : (⟨(y.vertex 0, y.vertex 1), y.edge 0 1 (by decide +kernel)⟩ : G.Dart) = d := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext ys yt
  have next : rotation.vertexRotation d =
      ⟨(y.vertex 0, y.vertex 2), y.edge 0 2 (by decide +kernel)⟩ := by
    rw [← ry]
    exact y.turn 0 1 2 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have twice : rotation.vertexRotation (rotation.vertexRotation d) =
      ⟨(y.vertex 0, y.vertex 3), y.edge 0 3 (by decide +kernel)⟩ := by
    rw [next]
    exact y.turn 0 2 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have prev : rotation.vertexRotation.symm d =
      ⟨(x.vertex 0, x.vertex 2), x.edge 0 2 (by decide +kernel)⟩ := by
    apply rotation.vertexRotation.injective
    rw [Equiv.apply_symm_apply, ← rx]
    exact (x.turn 0 2 1 (by decide +kernel) (by decide +kernel) (by decide +kernel)).symm
  have xfive : G.degree (x.vertex 2) = 5 := by
    have h := x.degree 2
    rw [show lower 2 2 = 5 from by decide +kernel,
      show upper 2 2 = 5 from by decide +kernel] at h
    omega
  have yfive : G.degree (y.vertex 3) = 5 := by
    have h := y.degree 3
    rw [show lower 4 3 = 5 from by decide +kernel,
      show upper 4 3 = 5 from by decide +kernel] at h
    omega
  rw [RuleMatcher.candidate_eq rotation d y ys yt] at shared
  refine ⟨six, ?_, ?_, ?_⟩
  · change G.degree (rotation.vertexRotation d).snd = 5
    rw [next]
    exact shared
  · change G.degree (rotation.vertexRotation (rotation.vertexRotation d)).snd = 5
    rw [twice]
    exact yfive
  · have last := FacialStarCompletion.pow_pred rotation cyclic d
    rw [six] at last
    change walk rotation d 5 = rotation.vertexRotation.symm d at last
    rw [last, prev]
    exact xfive

end FourColor.RuleFanSupply
