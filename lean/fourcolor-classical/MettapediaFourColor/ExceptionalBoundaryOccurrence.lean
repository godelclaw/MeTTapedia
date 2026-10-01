import MettapediaFourColor.ExceptionalBoundaryCompletion

/-!
# Full star coverage and the actual exceptional boundary occurrence

The completed map preserves every cyclic core-star step and accounts for
every ambient edge incident with the core. Inducedness proves that its ring
ports are outside the core. Distinct ring labels are not required to have
distinct ambient images.
-/

namespace FourColor.ExceptionalBoundaryOccurrence

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCore ExceptionalCoreOrientation ExceptionalCoreLocalInjectivity
open ExceptionalBoundaryCompletion ExceptionalOverlap

set_option maxRecDepth 32768

theorem owner_bounds : ∀ p : Fin 11,
    (star (owner p).1).length ≤ (owner p).2 ∧ (owner p).2 < coreDegree (owner p).1 := by
  decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {rotation : Data G}
  [Finite V] (r : JointReading rotation)

/-- All full cyclic source steps are actual ambient corners. -/
theorem full_turn (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 8) (p : Fin (coreDegree i)) :
    Corner rotation (vertex r (i.natAdd 11)) (vertex r (fullSpoke i p))
      (vertex r (fullSpoke i (nextPos i p))) := by
  have adj (q : Fin (coreDegree i)) :
      G.Adj (vertex r (i.natAdd 11)) (vertex r (fullSpoke i q)) := by
    rw [vertex_core, row_agrees r tri cyclic]
    simpa only [around_fst] using (around r i q.val).adj
  have dart_eq (q : Fin (coreDegree i)) :
      (⟨(vertex r (i.natAdd 11), vertex r (fullSpoke i q)), adj q⟩ : G.Dart) =
        around r i q.val := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext ((vertex_core r i).trans (around_fst r i q.val).symm)
      (row_agrees r tri cyclic i q)
  refine ⟨adj p, adj (nextPos i p), ?_⟩
  exact (congrArg rotation.vertexRotation (dart_eq p)).trans
    ((around_next r cyclic i p).trans (dart_eq (nextPos i p)).symm)

/-- No incident edge can escape the completed interface. -/
theorem star_covers (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 8) {v : V} (adj : G.Adj (r.core.map i) v) :
    ∃ p : Fin (coreDegree i), vertex r (fullSpoke i p) = v := by
  let d : G.Dart := ⟨(r.core.map i, v), adj⟩
  obtain ⟨n, hn, he⟩ := FacialStarCompletion.covers rotation cyclic (base r i) d rfl
  change n < G.degree (r.core.map i) at hn
  rw [r.core.degree] at hn
  exact ⟨⟨n, hn⟩, (row_agrees r tri cyclic i ⟨n, hn⟩).trans
    (congrArg (fun e : G.Dart => e.snd) he)⟩

theorem around_injective (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 8) : Function.Injective (fun p : Fin (coreDegree i) => (around r i p.val).snd) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  apply corner_chain_injective rotation cyclic (r.core.map i) (degree_pos i)
  · intro p
    simpa only [around_fst] using (around r i p.val).adj
  · intro n hn
    have h := full_turn r tri cyclic i ⟨n, by omega⟩
    rw [vertex_core, row_agrees r tri cyclic, row_agrees r tri cyclic] at h
    simpa only [nextPos, Nat.mod_eq_of_lt hn] using h
  · rw [r.core.degree]

/-- An exterior port cannot fold back into an induced core. This permits
identifications between different ring ports while excluding core capture. -/
theorem ring_outside_core (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (reflect : ∀ i j, G.Adj (r.core.map i) (r.core.map j) → core.Adj i j)
    (p : Fin 11) (j : Fin 8) : vertex r (p.castAdd 8) ≠ r.core.map j := by
  intro eq
  rw [vertex_ring] at eq
  let i := (owner p).1
  let n := (owner p).2
  obtain ⟨lo, hi⟩ := owner_bounds p
  have adj : G.Adj (r.core.map i) (r.core.map j) := by
    have h := (around r i n).adj
    rw [around_fst, eq] at h
    exact h
  obtain ⟨q, hq⟩ := (star_specs i).2.2 j |>.mp (reflect i j adj)
  have he : (around r i n).snd = (around r i q.val).snd := by
    rw [around_core r tri i q, hq]
    exact eq
  have indices : (⟨n, hi⟩ : Fin (coreDegree i)) =
      ⟨q.val, lt_of_lt_of_le q.isLt (star_specs i).2.1⟩ :=
    around_injective r tri cyclic i he
  have hval := congrArg Fin.val indices
  have hqbound := q.isLt
  change n = q.val at hval
  change (star i).length ≤ n at lo
  omega

noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]
  (original : Data H)
  (minimal : GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample original)

variable (x y : ExceptionalPattern.Occurrence
    (MinimalExceptionalEmbedding.rotation original minimal))
  (aligned : y.vertex 0 = x.vertex 14)

/-- The two aligned actual occurrences construct the entire completion map. -/
def sourceHom : input.graph →g MinimalExceptionalEmbedding.graph original minimal := by
  classical
  let reading : JointReading (MinimalExceptionalEmbedding.rotation original minimal) :=
    jointReading x (MinimalExceptionalEmbedding.triangular original minimal)
      (MinimalExceptionalEmbedding.cyclic original minimal) y aligned
  exact hom reading
    (MinimalExceptionalEmbedding.triangular original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal)

theorem source_core (i : Fin 8) :
    sourceHom original minimal x y aligned (i.natAdd 11) = coreVertex x i := by
  classical
  exact vertex_core _ i

theorem source_ring_outside (p : Fin 11) (i : Fin 8) :
    sourceHom original minimal x y aligned (p.castAdd 8) ≠ coreVertex x i := by
  classical
  apply ring_outside_core _ (MinimalExceptionalEmbedding.triangular original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal)
  intro a b h
  exact (ExceptionalCoreInduced.joint_induced original minimal _ a b).mp h

end
end FourColor.ExceptionalBoundaryOccurrence
