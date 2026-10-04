import MettapediaFourColor.CorePairHistoryObstruction
import MettapediaFourColor.ThreeBlockReconstruction
import Mettapedia.GraphTheory.Kempe.CliquePhysicalLift
import Mettapedia.GraphTheory.Kempe.HistoryIso

/-! # The physical core repair survives arbitrary clique attachments

The retained graph is the earlier eleven-port exterior. Any properly
coloured hidden patch attached along a retained clique can accompany the
same repair, with no additional physical switches. Both initial boundary
words are covered. The second still needs at least two switches.

The theorem supplies a source colouring agreeing with the repaired
exterior at every port. Occurrence supply and planarity of a chosen
attachment are separate geometric obligations.
-/

namespace FourColor.CoreCliqueRepair

open SimpleGraph CoreProfileSwitchGeometry CoreProfileSwitchObstruction
open FiveTriangleCollapseObstruction
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

variable {V : Type*} {G : SimpleGraph V}
    (X N : Set V) (clique : G.IsClique N)
    (attachment : ∀ x, x ∉ X → ∀ y ∈ X, G.Adj x y → y ∈ N)
    (reading : G.induce X ≃g exterior)

include clique attachment

/-- A source witness and a repaired colouring of the whole enlarged
exterior, reached in one or two actual component switches. -/
theorem repair (b : Bool) (C : G.Coloring Palette)
    (initial : ∀ v : X, C v = CoreProfileSwitchObstruction.initial b (reading v)) :
    ∃ D : G.Coloring Palette, ∃ path : History C D,
      path.length = (if b then 2 else 1) ∧
      ∃ k : upper.graph.Coloring Palette,
        ∀ j : Fin 11, k (j.castAdd 7) = D (reading.symm j).val := by
  obtain ⟨small, length⟩ := KempeHistoryIso.history reading (CoreProfilePreparedRepair.history b)
  have start : C.restrictInduce X =
      KempeHistoryIso.pull reading (CoreProfileSwitchObstruction.initial b) := by
    apply DFunLike.ext
    intro v
    exact initial v
  obtain ⟨D, path, final, count⟩ :=
    KempeCliquePhysicalLift.history_lifts X N clique attachment small C start
  refine ⟨D, path, ?_, repaired.comp hom, ?_⟩
  · rw [count, length]
    cases b <;> rfl
  · intro j
    have h := congrArg (fun E : (G.induce X).Coloring Palette => E (reading.symm j)) final
    change D (reading.symm j).val = switched false (reading (reading.symm j)) at h
    rw [reading.apply_symm_apply] at h
    exact (CoreProfilePreparedRepair.repaired_boundary j).trans h.symm

/-- The two-step upper bound is attained for every supplied starting
colouring in the second boundary class, even when the hidden patch grows. -/
theorem two_steps_optimal (C : G.Coloring Palette)
    (initial : ∀ v : X, C v = CoreProfileSwitchObstruction.initial true (reading v)) :
    (∃ D : G.Coloring Palette, ∃ path : History C D, path.length = 2 ∧
      ∃ k : upper.graph.Coloring Palette,
        ∀ j : Fin 11, k (j.castAdd 7) = D (reading.symm j).val) ∧
    ∀ (D : G.Coloring Palette) (path : History C D) (k : upper.graph.Coloring Palette),
      (∀ j : Fin 11, k (j.castAdd 7) = D (reading.symm j).val) → 2 ≤ path.length := by
  refine ⟨repair X N clique attachment reading true C initial, ?_⟩
  intro D path k boundary
  apply CorePairHistoryObstruction.history_needs_two
    (fun j => (reading.symm j).val) C D _ path k boundary
  intro j
  have h := initial (reading.symm j)
  rw [reading.apply_symm_apply] at h
  exact h

/-- Exact source/exterior incidence turns the lifted repair into a full
ambient colouring. Every exterior vertex is retained and seven source
vertices are reconstructed, regardless of the hidden patch's size. -/
theorem ambient_reconstruction
    {U : Type*} [Fintype U] [DecidableEq U] [Fintype V]
    {A : SimpleGraph U} [DecidableRel A.Adj]
    {data : Mettapedia.GraphTheory.FourColor.SimpleGraphDartRotation.Data A}
    {s : ThreeBlockGeometry.Patch data} (e : ThreeBlockGeometry.ExteriorReading s G)
    (covers : ∀ v, s.Exterior v → ∃ w, e.embedding w = v)
    (stars : ∀ i : Fin 18, 11 ≤ i.val → ∀ v, A.Adj (s.point i) v →
      ∃ j, s.point j = v ∧ upper.graph.Adj i j)
    (aligned : ∀ j, (reading.symm j).val = e.ports j)
    (b : Bool) (C : G.Coloring Palette)
    (initial : ∀ v : X, C v = CoreProfileSwitchObstruction.initial b (reading v)) :
    Fintype.card U = Fintype.card V + 7 ∧
    ∃ D : G.Coloring Palette, ∃ path : History C D,
      path.length = (if b then 2 else 1) ∧
      ∃ K : A.Coloring Palette, ∀ v, K (e.embedding v) = D v := by
  obtain ⟨D, path, length, k, boundary⟩ := repair X N clique attachment reading b C initial
  have agreement : ∀ j : Fin 11, k (j.castAdd 7) = D (e.ports j) := by
    intro j
    simpa only [aligned] using boundary j
  obtain ⟨K, outside, _⟩ := e.reconstruct covers stars D k agreement
  exact ⟨e.exact_decrease covers, D, path, length, K, outside⟩

end FourColor.CoreCliqueRepair
