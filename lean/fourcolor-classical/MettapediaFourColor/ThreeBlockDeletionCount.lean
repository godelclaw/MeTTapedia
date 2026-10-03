import MettapediaFourColor.ThreeBlockDiskDeletion
import MettapediaFourColor.ThreeBlockDiskStars

/-! # Exact dart count for deleting the seven-vertex core

Complete core stars identify the removed ambient darts with the source
darts incident to its core. The equivalence preserves both endpoints.
It counts 58 removed darts, hence 29 removed undirected edges.
-/

namespace FourColor.ThreeBlockDiskBoundary

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open FiveTriangleCollapseObstruction InducedGraphRotation

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev CoreDart := {d : upper.graph.Dart // 11 ≤ d.fst.val ∨ 11 ≤ d.snd.val}

theorem core_dart_count : Nat.card CoreDart = 58 := by
  let e : CoreDart ≃ {p : Fin 18 × Fin 18 //
      upper.graph.Adj p.1 p.2 ∧ (11 ≤ p.1.val ∨ 11 ≤ p.2.val)} :=
    { toFun := fun d => ⟨d.val.toProd, d.val.adj, d.property⟩
      invFun := fun p => ⟨⟨p.val, p.property.1⟩, p.property.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G}
  (r : Reading data)

def removedDarts := {d : G.Dart // ¬ retained (keep r) d}

def coreDartMap (d : CoreDart) : removedDarts r := by
  refine ⟨r.hom.mapDart d.val, ?_⟩
  rintro ⟨hf, hs⟩
  have a := (keep_point r d.val.fst).mp hf
  have b := (keep_point r d.val.snd).mp hs
  rcases d.property with h | h <;> omega

theorem coreDartMap_injective : Function.Injective (coreDartMap r) := by
  intro a b h
  have eq := congrArg Subtype.val h
  apply Subtype.ext
  apply Dart.ext
  exact Prod.ext (r.injective (congrArg (fun d => d.fst) eq))
    (r.injective (congrArg (fun d => d.snd) eq))

theorem coreDartMap_surjective (cyclic : data.IsVertexwiseCyclic) :
    Function.Surjective (coreDartMap r) := by
  classical
  intro d
  by_cases hu : d.val.fst ∈ keep r
  · have hv : d.val.snd ∉ keep r := fun h => d.property ⟨hu, h⟩
    change ¬ ¬ d.val.snd ∈ r.hom '' {i : Fin 18 | 11 ≤ i.val} at hv
    obtain ⟨i, hi, he⟩ := not_not.mp hv
    have edge : G.Adj (r.hom i) d.val.fst := he ▸ d.val.adj.symm
    obtain ⟨j, hj, hij⟩ := core_stars r cyclic i hi d.val.fst edge
    refine ⟨⟨⟨(j,i),hij.symm⟩, Or.inr hi⟩, ?_⟩
    apply Subtype.ext
    exact Dart.ext _ _ (Prod.ext hj he)
  · change ¬ ¬ d.val.fst ∈ r.hom '' {i : Fin 18 | 11 ≤ i.val} at hu
    obtain ⟨i, hi, he⟩ := not_not.mp hu
    have edge : G.Adj (r.hom i) d.val.snd := he ▸ d.val.adj
    obtain ⟨j, hj, hij⟩ := core_stars r cyclic i hi d.val.snd edge
    refine ⟨⟨⟨(i,j),hij⟩, Or.inl hi⟩, ?_⟩
    apply Subtype.ext
    exact Dart.ext _ _ (Prod.ext he hj)

theorem removed_dart_count (cyclic : data.IsVertexwiseCyclic) :
    Nat.card (removedDarts r) = 58 := by
  have eq := Nat.card_congr (Equiv.ofBijective (coreDartMap r)
    ⟨coreDartMap_injective r, coreDartMap_surjective r cyclic⟩)
  exact eq.symm.trans core_dart_count

theorem deletion_dart_count (cyclic : data.IsVertexwiseCyclic) :
    Nat.card G.Dart = Nat.card (G.induce (keep r)).Dart + 58 := by
  classical
  have eq := Nat.card_congr (Equiv.sumCompl (retained (keep r) (G := G)))
  rw [Nat.card_sum] at eq
  have outside := Nat.card_congr (darts (keep r) (G := G))
  have removed := removed_dart_count r cyclic
  change Nat.card {d : G.Dart // ¬ retained (keep r) d} = 58 at removed
  change Nat.card G.Dart = Nat.card (G.induce (keep r)).Dart + 58
  omega

end
end FourColor.ThreeBlockDiskBoundary
