import Mettapedia.GraphTheory.FourColor.HexagonalCollarNoncollision
import Mettapedia.GraphTheory.FourColor.HexagonalTubeReduction

/-!
# Bounded geometric alternatives while growing hexagonal collars

In a map whose faces are pentagons or hexagons, a recognized row has a
specific next row unless an incident face is pentagonal. Hexagonal seam
geometry excludes candidate-vertex collisions. Repeated construction gives
actual hexagonal tubes and consumes their physical reduction: a least
counterexample must reach a pentagonal seam within three extensions of any
recognized five-port row. The earlier two-alternative API is retained.
-/

namespace Mettapedia.GraphTheory.FourColor.TubeSlab.ZigzagSlab

open ZigzagRing PhysicalForkCodeFaces GoertzelV24TwoEdgeCutMinimality

noncomputable section
universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  {RS : RotationSystem.{u, u, u} V E} {k : ℕ} [NeZero k]
  {inner : V → Prop} (S : ZigzagSlab RS k inner)

/-- These are literal face sizes and equalities of original vertices. -/
def CollarObstruction : Prop :=
  (∃ i : Fin k, (RS.faceOrbit (S.ι (.inr (.inr i)))).card = 5) ∨
    ∃ v w : Vtx k, v ≠ w ∧ S.collarVertex v = S.collarVertex w

variable (hC : Cubic3 RS)
  (hfaces : ∀ d : RS.D, (RS.faceOrbit d).card = 5 ∨ (RS.faceOrbit d).card = 6)

include hfaces in
theorem collarShortFaces_of_all : S.CollarShortFaces := fun _ => hfaces _

include hfaces in
theorem clean_of_no_obstruction (h : ¬ S.CollarObstruction) :
    S.HexagonalSeam ∧ Function.Injective S.collarVertex := by
  constructor
  · intro i
    rcases hfaces (S.ι (.inr (.inr i))) with hp | hh
    · exact (h (Or.inl ⟨i, hp⟩)).elim
    · exact hh
  · intro v w he
    by_contra hn
    exact h (Or.inr ⟨v, w, hn, he⟩)

/-- Inspect this row, then at most `n` canonically constructed successors.
The recursive step retains the exact collar geometry and both interfaces. -/
def StopsWithin : {inner : V → Prop} → (S : ZigzagSlab RS k inner) →
    S.RotationCompatible → ℕ → Prop
  | _, S, _, 0 => S.CollarObstruction
  | _, S, hS, n + 1 => S.CollarObstruction ∨
      ∃ (hh : S.HexagonalSeam) (hv : Function.Injective S.collarVertex),
        StopsWithin (S.nextRow hC hS hh hv (S.collarShortFaces_of_all hfaces))
          (S.nextRow_rotation hC hS hh hv (S.collarShortFaces_of_all hfaces)) n

/-- Failure to meet an obstruction supplies the entire longer tube, rather
than only a sequence of boundary relations. -/
theorem tube_of_not_stops (hS : S.RotationCompatible) (n : ℕ)
    (hn : ¬ StopsWithin hC hfaces S hS n) :
    ∃ t : Tube RS k inner (n + 2), t.Hexagonal := by
  induction n generalizing inner with
  | zero =>
    obtain ⟨hh, hv⟩ := S.clean_of_no_obstruction hfaces hn
    let T := S.nextRow hC hS hh hv (S.collarShortFaces_of_all hfaces)
    have hT : T.RotationCompatible := S.nextRow_rotation hC hS hh hv _
    exact ⟨.cons S (.cons T (.nil _ T.outEquiv)), ⟨hS, hh, hT, rfl, trivial⟩⟩
  | succ n ih =>
    have hbad : ¬ S.CollarObstruction := fun h => hn (Or.inl h)
    obtain ⟨hh, hv⟩ := S.clean_of_no_obstruction hfaces hbad
    let T := S.nextRow hC hS hh hv (S.collarShortFaces_of_all hfaces)
    have hT : T.RotationCompatible := S.nextRow_rotation hC hS hh hv _
    have hnext : ¬ StopsWithin hC hfaces T hT n := fun h => hn (Or.inr ⟨hh, hv, h⟩)
    obtain ⟨t, ht⟩ := ih T hT hnext
    refine ⟨.cons S t, hS, ?_, ht⟩
    cases t
    exact hh

/-- An actual pentagonal face at the current row's output boundary. -/
def PentagonalSeam : Prop :=
  ∃ i : Fin k, (RS.faceOrbit (S.ι (.inr (.inr i)))).card = 5

include hC hfaces in
/-- The old collision alternative adds no obstruction in this face class:
without a pentagon all seam faces are hexagons, hence candidates are distinct. -/
theorem collarObstruction_iff_pentagonalSeam (hS : S.RotationCompatible) :
    S.CollarObstruction ↔ S.PentagonalSeam := by
  constructor
  · rintro (hp | ⟨v, w, hn, he⟩)
    · exact hp
    · by_contra hp
      have hh : S.HexagonalSeam := by
        intro i
        rcases hfaces (S.ι (.inr (.inr i))) with hf | hf
        · exact (hp ⟨i, hf⟩).elim
        · exact hf
      exact hn (S.collarVertex_injective hC hS hh he)
  · exact Or.inl

/-- Reach a pentagonal seam after at most `n` canonically constructed rows.
Only actual hexagonal face checks are needed at intermediate rows. -/
def PentagonWithin : {inner : V → Prop} → (S : ZigzagSlab RS k inner) →
    S.RotationCompatible → ℕ → Prop
  | _, S, _, 0 => S.PentagonalSeam
  | _, S, hS, n + 1 => S.PentagonalSeam ∨
      ∃ (hh : S.HexagonalSeam),
        PentagonWithin (S.hexagonalNextRow hC hS hh (S.collarShortFaces_of_all hfaces))
          (S.hexagonalNextRow_rotation hC hS hh (S.collarShortFaces_of_all hfaces)) n

theorem stopsWithin_iff_pentagonWithin (hS : S.RotationCompatible) (n : ℕ) :
    StopsWithin hC hfaces S hS n ↔ PentagonWithin hC hfaces S hS n := by
  induction n generalizing inner with
  | zero => exact S.collarObstruction_iff_pentagonalSeam hC hfaces hS
  | succ n ih =>
    constructor
    · rintro (hp | ⟨hh, hv, ht⟩)
      · exact Or.inl ((S.collarObstruction_iff_pentagonalSeam hC hfaces hS).mp hp)
      · exact Or.inr ⟨hh, (ih _ _).mp ht⟩
    · rintro (hp | ⟨hh, ht⟩)
      · exact Or.inl (Or.inl hp)
      · exact Or.inr ⟨hh, S.collarVertex_injective hC hS hh, (ih _ _).mpr ht⟩

/-- Growth terminates at an actual pentagonal seam in every finite map of
this face class. This coarse bound requires no counterexample assumption. -/
theorem pentagonWithin_card (hS : S.RotationCompatible) :
    PentagonWithin hC hfaces S hS (Fintype.card V) := by
  by_contra hn
  have hs : ¬ StopsWithin hC hfaces S hS (Fintype.card V) := fun h =>
    hn ((S.stopsWithin_iff_pentagonWithin hC hfaces hS _).mp h)
  obtain ⟨t, ht⟩ := S.tube_of_not_stops hC hfaces hS (Fintype.card V) hs
  obtain ⟨U, _, _, _, _⟩ := t.literalSlab ht
  have hcard := Nat.card_le_card_of_injective U.vtx U.vtx_inj
  change Nat.card (tube k (Fintype.card V + 1)).V ≤ Nat.card V at hcard
  rw [tube_vertex_card, Nat.card_eq_fintype_card] at hcard
  change 2 * k * (Fintype.card V + 2) ≤ Fintype.card V at hcard
  have hk := NeZero.pos k
  have hle := Nat.mul_le_mul_right (Fintype.card V + 2) (show 1 ≤ 2 * k by omega)
  simp only [one_mul] at hle
  omega

variable {G : SimpleGraph V} [DecidableRel G.Adj]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- Every supplied five-port row of a minimal counterexample encounters a
pentagonal seam face or a genuine candidate-vertex collision within three
successful collar extensions. Neither alternative is assumed reducible. -/
theorem stopsWithin_three (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (faces : ∀ d : rotation.toRotationSystem.D,
      (rotation.toRotationSystem.faceOrbit d).card = 5 ∨
      (rotation.toRotationSystem.faceOrbit d).card = 6)
    {inner : V → Prop} (S : ZigzagSlab rotation.toRotationSystem 5 inner)
    (hS : S.RotationCompatible) :
    StopsWithin (cubic3_of _ minimal.spherical.cubic minimal.vertexRotationCyclic)
      faces S hS 3 := by
  by_contra h
  obtain ⟨t, ht⟩ := S.tube_of_not_stops
    (cubic3_of _ minimal.spherical.cubic minimal.vertexRotationCyclic) faces hS 3 h
  have := t.hexagonal_five_length_le_four rotation minimal ht
  omega

/-- An actual pentagonal seam is reached within three successful extensions;
hexagonal collars cannot stop by identifying vertices. -/
theorem pentagonWithin_three (rotation : SimpleGraphDartRotation.Data G)
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (faces : ∀ d : rotation.toRotationSystem.D,
      (rotation.toRotationSystem.faceOrbit d).card = 5 ∨
      (rotation.toRotationSystem.faceOrbit d).card = 6)
    {inner : V → Prop} (S : ZigzagSlab rotation.toRotationSystem 5 inner)
    (hS : S.RotationCompatible) :
    PentagonWithin (cubic3_of _ minimal.spherical.cubic minimal.vertexRotationCyclic)
      faces S hS 3 :=
  (S.stopsWithin_iff_pentagonWithin
    (cubic3_of _ minimal.spherical.cubic minimal.vertexRotationCyclic) faces hS 3).mp
      (S.stopsWithin_three rotation minimal faces hS)

end
end Mettapedia.GraphTheory.FourColor.TubeSlab.ZigzagSlab
