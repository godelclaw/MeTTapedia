import Mettapedia.GraphTheory.FourColor.ProtectedOrderedMesh
import Mettapedia.GraphTheory.FourColor.SeparatedPairDeletion

/-!
# Protected ordered meshes in cubic ambient graphs

A finite set of vertices costs at most three incident edges per vertex.
After r rounds of ambient closed-neighbour expansion, the conservative
loss per mesh dimension is 3 * |S| * 4^r. The output retains complete
ordered row and column paths. It does not declare the regions between
those paths empty, or supply a reduction of their full ambient interfaces.
-/

namespace Mettapedia.GraphTheory.FourColor.ProtectedOrderedMesh

open GoertzelV24RotationMultigraphAdapter
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open SimpleGraph SimpleGraphDartRotation

attribute [-instance]
  GoertzelV24RetainedVertexRotationSplice.retainedVertexFintype
  GoertzelV24SeamFaceArcPartition.hitPointFintype

noncomputable section
universe u v
variable {V : Type u} {E : Type v} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

theorem star_card_le_three (RS : RotationSystem V E) (hc : RS.IsCubic)
    (S : Finset V) : (starEdges (g := toMultigraph RS) S).card ≤ 3 * S.card := by
  have hsub : starEdges (g := toMultigraph RS) S ⊆ S.biUnion RS.incidentEdges := by
    intro e he
    simp only [starEdges, Finset.mem_filter, Finset.mem_univ, true_and] at he
    rcases he with hf | hs
    · apply Finset.mem_biUnion.mpr
      refine ⟨(toMultigraph RS).fst e, hf, ?_⟩
      exact RS.mem_incidentEdges_iff.mpr ⟨someDart RS e, edgeOf_someDart RS e, rfl⟩
    · apply Finset.mem_biUnion.mpr
      refine ⟨(toMultigraph RS).snd e, hs, ?_⟩
      exact RS.mem_incidentEdges_iff.mpr
        ⟨RS.alpha (someDart RS e), by simp [RS.edge_alpha, edgeOf_someDart], rfl⟩
  calc
    (starEdges (g := toMultigraph RS) S).card ≤ (S.biUnion RS.incidentEdges).card :=
      Finset.card_le_card hsub
    _ ≤ ∑ v ∈ S, (RS.incidentEdges v).card := Finset.card_biUnion_le
    _ = 3 * S.card := by simp [RS.incidentEdges_card_eq_three_of_isCubic hc, Nat.mul_comm]

theorem exists_unmarked_submesh (RS : RotationSystem V E) (hc : RS.IsCubic)
    {a b p q : Nat} (M : OrderedInjectiveMesh (toMultigraph RS) a b)
    (S : Finset V) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (ha : p + 3 * S.card ≤ a) (hb : q + 3 * S.card ≤ b) :
    ∃ (r : Fin p ↪o Fin a) (c : Fin q ↪o Fin b),
      AvoidsVertices (restrict M r c) S := by
  apply exists_restriction_avoiding_vertices M S hp hq
  · have := star_card_le_three RS hc S; omega
  · have := star_card_le_three RS hc S; omega

variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The full ambient buffer, including lateral attachments not in the mesh. -/
def buffer (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    Nat → Finset V
  | 0 => S
  | n + 1 => SeparatedPairDeletion.close G (buffer G S n)

theorem card_buffer_le (hdegree : ∀ v, G.degree v ≤ 3) (S : Finset V) (r : Nat) :
    (buffer G S r).card ≤ S.card * 4 ^ r := by
  induction r with
  | zero => simp [buffer]
  | succ r ih =>
    calc
      (buffer G S (r + 1)).card ≤ (buffer G S r).card * 4 :=
        SeparatedPairDeletion.card_close_le 3 hdegree _
      _ ≤ (S.card * 4 ^ r) * 4 := Nat.mul_le_mul_right 4 ih
      _ = S.card * 4 ^ (r + 1) := by rw [pow_succ, Nat.mul_assoc]

theorem subset_buffer (S : Finset V) (r : Nat) : S ⊆ buffer G S r := by
  induction r with
  | zero => exact Finset.Subset.refl _
  | succ r ih => exact ih.trans (SeparatedPairDeletion.subset_close _)

/-- The protected mesh is constructed in the unchanged ambient graph. No
minimality, colouring choice, frozen exterior, or preselected clean carrier
is an input. The index embeddings are ordered but need not be consecutive. -/
theorem exists_buffer_avoiding_submesh (rotation : Data G)
    (hc : rotation.toRotationSystem.IsCubic)
    {a b p q : Nat}
    (M : OrderedInjectiveMesh (toMultigraph rotation.toRotationSystem) a b)
    (S : Finset V) (radius : Nat) (hp : 2 ≤ p) (hq : 2 ≤ q)
    (ha : p + 3 * (S.card * 4 ^ radius) ≤ a)
    (hb : q + 3 * (S.card * 4 ^ radius) ≤ b) :
    ∃ (r : Fin p ↪o Fin a) (c : Fin q ↪o Fin b),
      AvoidsVertices (restrict M r c) (buffer G S radius) := by
  have hdegree (v : V) : G.degree v ≤ 3 :=
    Nat.le_of_eq ((rotation.toRotationSystem_isCubic_iff.mp hc) v)
  have hbuf := card_buffer_le hdegree S radius
  apply exists_unmarked_submesh rotation.toRotationSystem hc M
    (buffer G S radius) hp hq
  · omega
  · omega

end
end Mettapedia.GraphTheory.FourColor.ProtectedOrderedMesh
