import MettapediaFourColor.PatchDiskBoundary

/-! # Exact deletion counts with boundary identifications

Core injectivity and injectivity on each core neighbourhood identify the
removed ambient darts with the core-incident source darts. Boundary vertices
may coincide. The vertex count uses only distinct core vertices.
-/

namespace FourColor.PatchDisk.Reading

open SimpleGraph Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open InducedGraphRotation

variable {c b : ℕ} [NeZero b]
abbrev CoreDart (s : Source c b) :=
  {d : s.graph.Dart // b ≤ d.fst.val ∨ b ≤ d.snd.val}

noncomputable section

variable {s : Source c b} {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {data : Data G} (r : Reading s data)

def removedDarts := {d : G.Dart // ¬ retained (keep r) d}

def coreDartMap (d : CoreDart s) : removedDarts r := by
  refine ⟨r.hom.mapDart d.val, ?_⟩
  rintro ⟨hf, hs⟩
  have a := (keep_point r d.val.fst).mp hf
  have b := (keep_point r d.val.snd).mp hs
  rcases d.property with h | h <;> omega

theorem coreDartMap_injective : Function.Injective (coreDartMap r) := by
  intro a d h
  have eq := congrArg Subtype.val h
  have first := congrArg (fun d => d.fst) eq
  have second := congrArg (fun d => d.snd) eq
  apply Subtype.ext
  apply Dart.ext
  rcases a.property with core | core
  · have fst := r.core_eq core first
    have adj : s.graph.Adj a.val.fst d.val.snd := by simpa only [fst] using d.val.adj
    have snd := r.local_injective a.val.fst core a.val.adj adj second
    exact Prod.ext fst snd
  · have snd := r.core_eq core second
    have adj : s.graph.Adj a.val.snd d.val.fst := by simpa only [snd] using d.val.adj.symm
    have fst := r.local_injective a.val.snd core a.val.adj.symm adj first
    exact Prod.ext fst snd

theorem coreDartMap_surjective (cyclic : data.IsVertexwiseCyclic) :
    Function.Surjective (coreDartMap r) := by
  classical
  intro d
  by_cases hu : d.val.fst ∈ keep r
  · have hv : d.val.snd ∉ keep r := fun h => d.property ⟨hu, h⟩
    change ¬ ¬ d.val.snd ∈ r.hom '' {i : Fin (b + c) | b ≤ i.val} at hv
    obtain ⟨i, hi, he⟩ := not_not.mp hv
    have edge : G.Adj (r.hom i) d.val.fst := he ▸ d.val.adj.symm
    obtain ⟨j, hj, hij⟩ := core_stars r cyclic i hi d.val.fst edge
    refine ⟨⟨⟨(j,i),hij.symm⟩, Or.inr hi⟩, ?_⟩
    apply Subtype.ext
    exact Dart.ext _ _ (Prod.ext hj he)
  · change ¬ ¬ d.val.fst ∈ r.hom '' {i : Fin (b + c) | b ≤ i.val} at hu
    obtain ⟨i, hi, he⟩ := not_not.mp hu
    have edge : G.Adj (r.hom i) d.val.snd := he ▸ d.val.adj
    obtain ⟨j, hj, hij⟩ := core_stars r cyclic i hi d.val.snd edge
    refine ⟨⟨⟨(i,j),hij⟩, Or.inl hi⟩, ?_⟩
    apply Subtype.ext
    exact Dart.ext _ _ (Prod.ext he hj)

theorem removed_dart_count (cyclic : data.IsVertexwiseCyclic) :
    Nat.card (removedDarts r) + 6 = 6 * c + 2 * b := by
  have eq := Nat.card_congr (Equiv.ofBijective (coreDartMap r)
    ⟨coreDartMap_injective r, coreDartMap_surjective r cyclic⟩)
  rw [← eq]
  exact s.core_dart_count

theorem deletion_dart_count (cyclic : data.IsVertexwiseCyclic) :
    Nat.card G.Dart + 6 = Nat.card (G.induce (keep r)).Dart + (6 * c + 2 * b) := by
  classical
  have eq := Nat.card_congr (Equiv.sumCompl (retained (keep r) (G := G)))
  rw [Nat.card_sum] at eq
  have outside := Nat.card_congr (darts (keep r) (G := G))
  have removed := removed_dart_count r cyclic
  change Nat.card {d : G.Dart // ¬ retained (keep r) d} + 6 = 6 * c + 2 * b at removed
  omega

/-- The operation deletes exactly the distinct core vertices and adds none. -/
theorem deletion_vertex_count : Nat.card V = Nat.card (keep r) + c := by
  classical
  let assemble : keep r ⊕ Fin c → V := Sum.elim Subtype.val (fun i => r.hom (i.natAdd b))
  have injective : Function.Injective assemble := by
    intro x y h
    cases x with
    | inl w =>
      cases y with
      | inl z => exact congrArg Sum.inl (Subtype.val_injective h)
      | inr j =>
        exact (w.property ⟨j.natAdd b, show b ≤ b + j.val from Nat.le_add_right _ _, h.symm⟩).elim
    | inr i =>
      cases y with
      | inl w =>
        exact (w.property ⟨i.natAdd b, show b ≤ b + i.val from Nat.le_add_right _ _, h⟩).elim
      | inr j =>
        have same := r.core_eq (show b ≤ (i.natAdd b).val from Nat.le_add_right _ _) h
        have values := congrArg Fin.val same
        have ij : i = j := Fin.ext (by simpa using values)
        exact congrArg Sum.inr ij
  have surjective : Function.Surjective assemble := by
    intro v
    by_cases h : v ∈ keep r
    · exact ⟨.inl ⟨v,h⟩,rfl⟩
    · change ¬ ¬ v ∈ r.hom '' {i : Fin (b + c) | b ≤ i.val} at h
      obtain ⟨i,hi,eq⟩ := not_not.mp h
      change b ≤ i.val at hi
      let j : Fin c := ⟨i.val - b, by omega⟩
      have ji : j.natAdd b = i := Fin.ext (by dsimp [j]; omega)
      refine ⟨.inr j, ?_⟩
      change r.hom (j.natAdd b) = v
      rw [ji,eq]
  have cardinal := Nat.card_congr (Equiv.ofBijective assemble ⟨injective,surjective⟩)
  simpa only [Nat.card_sum, Nat.card_fin] using cardinal.symm

end
end FourColor.PatchDisk.Reading
