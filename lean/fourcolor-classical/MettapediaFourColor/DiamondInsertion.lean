import MettapediaFourColor.DiamondConfigurations
import Mettapedia.GraphTheory.FourColor.BoundaryTriangleAlternatives

/-!
# Two exact boundary insertions in the diamond family

Configurations 1, 2 and 4 have the same internal diamond. Successive boundary
triangle insertions relate their complete embedded graphs. Both colouring
branches are retained, including the contracted-graph branch with its fresh
colour. The endpoint equivalences produce colourings of the actual reference
configuration hypermaps.

These theorems establish geometry and exact colouring semantics. They do not
assert that arbitrary triangle insertion preserves D- or C-reducibility.
-/

namespace FourColor.DiamondInsertion

open DiamondConfigurations ConfigurationFaceGraph
open Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision

local instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c : V) : DecidableRel (subdivide G a b c).Adj := fun x y => by
  cases x <;> cases y <;> dsimp [subdivide, removed] <;> infer_instance

/-- Insert the new boundary vertex between vertices zero and one. -/
def insert12 : (subdivide graph001 0 1 6) ≃g graph002 where
  toEquiv := (finSuccEquiv' (1 : Fin 11)).symm
  map_rel_iff' := by decide +kernel

/-- Insert the new boundary vertex between vertices four and five. -/
def insert24 : (subdivide graph002 4 5 9) ≃g graph004 where
  toEquiv := (finSuccEquiv' (5 : Fin 12)).symm
  map_rel_iff' := by decide +kernel

/-- The inserted triangle is the actual inner node opposite the boundary edge. -/
theorem triangle12 :
    (22 : Fin 42) ∈ ring001 ∧
    table001.map.edge 22 = 23 ∧
    IsCyclicChain (fun u v => v = table001.map.node u) [23, 31, 24] ∧
    [23, 31, 24].map vertex001 = [1, 6, 0] := by
  unfold IsCyclicChain
  decide +kernel

theorem triangle24 :
    (26 : Fin 46) ∈ ring002 ∧
    table002.map.edge 26 = 27 ∧
    IsCyclicChain (fun u v => v = table002.map.node u) [27, 35, 28] ∧
    [27, 35, 28].map vertex002 = [5, 9, 4] := by
  unfold IsCyclicChain
  decide +kernel

/-- Every cyclic neighbour list changes by precisely the triangle insertion. -/
theorem rotation12 : ∀ v : Option (Fin 10), ∃ shift : Fin 8,
    stars002 (insert12 v) =
      ((triangleStar stars001 0 1 6 v).map insert12).rotate shift.val := by
  decide +kernel

theorem rotation24 : ∀ v : Option (Fin 11), ∃ shift : Fin 8,
    stars004 (insert24 v) =
      ((triangleStar stars002 4 5 9 v).map insert24).rotate shift.val := by
  decide +kernel

/-- The outer ring receives the new vertex in its specified boundary position. -/
theorem boundary12 :
    ((triangleBoundary boundary001.reverse 0).map insert12) =
      boundary002.reverse.rotate 5 := by decide +kernel

theorem boundary24 :
    ((triangleBoundary boundary002.reverse 4).map insert24) =
      boundary004.reverse.rotate 4 := by decide +kernel

/-- The old graph and the equal-endpoint branch exhaust configuration 2. -/
def alternatives12 :
    (graph001.Coloring (Fin 4) ⊕ EqualChoice graph001 0 1 6 (by decide)) ≃
      graph002.Coloring (Fin 4) :=
  (alternativesEquiv graph001 0 1 6 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans
      (SimpleGraph.coloringCongr insert12 (Equiv.refl _))

/-- The old graph and the equal-endpoint branch exhaust configuration 4. -/
def alternatives24 :
    (graph002.Coloring (Fin 4) ⊕ EqualChoice graph002 4 5 9 (by decide)) ≃
      graph004.Coloring (Fin 4) :=
  (alternativesEquiv graph002 4 5 9 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)).trans
      (SimpleGraph.coloringCongr insert24 (Equiv.refl _))

/-- Both alternatives reconstruct colourings of the actual reference map. -/
noncomputable def referenceAlternatives12 :
    (graph001.Coloring (Fin 4) ⊕ EqualChoice graph001 0 1 6 (by decide)) ≃
      {k : (cfmap cf002).Dart → Color // (cfmap cf002).map.Coloring k} :=
  alternatives12.trans coloring002

noncomputable def referenceAlternatives24 :
    (graph002.Coloring (Fin 4) ⊕ EqualChoice graph002 4 5 9 (by decide)) ≃
      {k : (cfmap cf004).Dart → Color // (cfmap cf004).map.Coloring k} :=
  alternatives24.trans coloring004

/-- A complete two-insertion history retains both choices at both stages. -/
noncomputable def referenceAlternatives14 :
    ((graph001.Coloring (Fin 4) ⊕ EqualChoice graph001 0 1 6 (by decide)) ⊕
      EqualChoice graph002 4 5 9 (by decide)) ≃
        {k : (cfmap cf004).Dart → Color // (cfmap cf004).map.Coloring k} :=
  (alternatives12.sumCongr (Equiv.refl _)).trans referenceAlternatives24

/-- An arbitrary predicate on the reference colouring is retained exactly. -/
theorem context12
    (accepts : {k : (cfmap cf002).Dart → Color // (cfmap cf002).map.Coloring k} → Prop) :
    (∃ k, accepts k) ↔
      (∃ k, accepts (referenceAlternatives12 (.inl k))) ∨
      (∃ k, accepts (referenceAlternatives12 (.inr k))) := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨choice, rfl⟩ := referenceAlternatives12.surjective k
    cases choice with
    | inl k => exact Or.inl ⟨k, hk⟩
    | inr k => exact Or.inr ⟨k, hk⟩
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩) <;> exact ⟨_, hk⟩

theorem context24
    (accepts : {k : (cfmap cf004).Dart → Color // (cfmap cf004).map.Coloring k} → Prop) :
    (∃ k, accepts k) ↔
      (∃ k, accepts (referenceAlternatives24 (.inl k))) ∨
      (∃ k, accepts (referenceAlternatives24 (.inr k))) := by
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨choice, rfl⟩ := referenceAlternatives24.surjective k
    cases choice with
    | inl k => exact Or.inl ⟨k, hk⟩
    | inr k => exact Or.inr ⟨k, hk⟩
  · rintro (⟨k, hk⟩ | ⟨k, hk⟩) <;> exact ⟨_, hk⟩

end FourColor.DiamondInsertion
