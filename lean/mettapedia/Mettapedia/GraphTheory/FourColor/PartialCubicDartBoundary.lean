import Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation
import Mettapedia.GraphTheory.FourColor.CyclicFiveBoundary

/-!
# Six unpaired slots are genuine boundary darts

An injectively realized even-sized cubic diagram with six unpaired slots
has at most six outgoing darts. If it has more than four vertices it contains
a cycle. Cyclic five-edge connectivity, three exterior vertices and the
cubic degree identity force exactly six outgoing darts. Hence none of the
unpaired slots can be an unrecorded internal edge.

The argument is independent of the diagram, embedding and colouring system.
-/

namespace Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation.Realization

open _root_.SimpleGraph GoertzelV24CubicSmallBoundaryCycle GoertzelV24MinimalTriangleFree

noncomputable section
variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {P : Diagram W} (F : Realization P G)

local instance boundaryEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

def imageSide (v : V) : Prop := v ∈ Set.range F.vertex
abbrev Unpaired := {d : Dart W // P.flip d = none}

omit [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem dart_injective (hv : Function.Injective F.vertex) : Function.Injective F.dart := by
  rintro ⟨u, s⟩ ⟨v, t⟩ he
  have hh := congrArg (fun d : G.Dart => d.fst) he
  rw [F.fst, F.fst] at hh
  have huv := hv hh
  change u = v at huv
  subst v
  exact Prod.ext rfl (F.slots_injective u he)

def vertexEquiv (hv : Function.Injective F.vertex) : W ≃ {v // F.imageSide v} :=
  Equiv.ofBijective (fun w => ⟨F.vertex w, ⟨w, rfl⟩⟩) ⟨by
    intro a b h
    exact hv (congrArg Subtype.val h), by
    rintro ⟨v, w, rfl⟩
    exact ⟨w, rfl⟩⟩

omit [DecidableEq W] [DecidableEq V] [DecidableRel G.Adj] in
theorem card_imageSide (hv : Function.Injective F.vertex) :
    Fintype.card {v // F.imageSide v} = Fintype.card W := by
  classical
  exact (Fintype.card_congr (F.vertexEquiv hv)).symm

omit [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem crossing_origin (d : CrossingSideDart G F.imageSide) :
    ∃ p : Unpaired (P := P), F.dart p.1 = d.1 := by
  obtain ⟨v, hv⟩ := d.2.1
  obtain ⟨s, hs⟩ := F.slots_surjective v d.1 hv.symm
  have hp : P.flip (v, s) = none := by
    cases he : P.flip (v, s) with
    | none => rfl
    | some e =>
      have hh : F.imageSide d.1.snd := by
        rw [← hs, F.snd_of_flip he]
        exact ⟨e.1, rfl⟩
      exact (d.2.2 hh).elim
  exact ⟨⟨(v, s), hp⟩, hs⟩

def crossingIndex (d : CrossingSideDart G F.imageSide) : Unpaired (P := P) :=
  (F.crossing_origin d).choose

omit [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem crossingIndex_dart (d : CrossingSideDart G F.imageSide) :
    F.dart (F.crossingIndex d).1 = d.1 := (F.crossing_origin d).choose_spec

omit [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem crossingIndex_injective : Function.Injective F.crossingIndex := by
  intro a b he
  apply Subtype.ext
  rw [← F.crossingIndex_dart a, ← F.crossingIndex_dart b, he]

omit [DecidableEq W] [DecidableEq V] in
theorem crossing_card_le :
    Fintype.card (CrossingSideDart G F.imageSide) ≤ Fintype.card (Unpaired (P := P)) := by
  classical
  exact Fintype.card_le_of_injective _ F.crossingIndex_injective

/-- Six possible ports, degree parity and the cyclic cut bound force every
possible port to occur in the actual boundary. -/
theorem unpaired_leaves_of_cyclicallyFive
    (hv : Function.Injective F.vertex)
    (hports : Fintype.card (Unpaired (P := P)) = 6)
    (heven : Even (Fintype.card W)) (hlarge : 4 < Fintype.card W)
    (hspace : Fintype.card W + 3 ≤ Fintype.card V)
    (hcubic : G.IsRegularOfDegree 3) (hcyclic : CyclicallyFiveEdgeConnected G)
    (p : Unpaired (P := P)) : ¬ F.imageSide (F.dart p.1).snd := by
  classical
  have hcard := F.card_imageSide hv
  have hle := F.crossing_card_le
  rw [hports] at hle
  have hcycle := CyclicFiveBoundary.hasCycle_of_boundary_card_lt_card_add_two
    hcubic F.imageSide (Fintype.card_pos_iff.mp (by omega)) (by omega)
  have hpartition := Fintype.card_subtype_compl F.imageSide
  have hfive := CyclicFiveBoundary.five_le_crossing_card hcubic hcyclic F.imageSide
    hcycle (by omega)
  have hdegree := card_crossingEdgeFinset_add_twice_internal_eq_three_mul (G := G)
    (fun v => (degree_instance_independent v _ _).trans (hcubic v)) F.imageSide
  rw [card_crossingEdgeFinset_eq_card_crossingSideDart] at hdegree
  simp only [Nat.card_eq_fintype_card] at hdegree
  obtain ⟨k, hk⟩ := heven
  have hsix : Fintype.card (CrossingSideDart G F.imageSide) = 6 := by omega
  have hsurj : Function.Surjective F.crossingIndex := by
    by_contra hn
    have hlt := Fintype.card_lt_of_injective_not_surjective
      F.crossingIndex F.crossingIndex_injective hn
    omega
  obtain ⟨d, hd⟩ := hsurj p
  have he := F.crossingIndex_dart d
  rw [hd] at he
  exact he.symm ▸ d.2.2

end
end Mettapedia.GraphTheory.FourColor.PartialCubicDartSeparation.Realization
