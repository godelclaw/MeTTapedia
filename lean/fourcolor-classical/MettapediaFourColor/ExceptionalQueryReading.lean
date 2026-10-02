import MettapediaFourColor.DualGraphQuery
import MettapediaFourColor.ExceptionalConstructionRepair
import MettapediaFourColor.MinimalExceptionalEmbedding

/-!
# The exceptional overlap realizes the compiled source query

The query walks actual directed edges of the retained core. Every transition
is obtained from its facial corners, and every observation from its ambient
degree. No occurrence, injectivity or boundary-colouring assumption is added
to the retained pair of exceptional readings.
-/

namespace FourColor.ExceptionalQueryReading

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCore ExceptionalCoreOrientation ExceptionalConstruction

theorem source_walk : table.map.walkqz 84 query = [84, 85, 82, 78, 74, 70, 52, 30] := by
  decide +kernel

theorem source_vertices : (table.map.walkqz 84 query).map vertex =
    [16, 18, 11, 14, 17, 15, 12, 13] := by
  rw [source_walk]
  decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  {rotation : Data G} (r : JointReading rotation)

def dart (a b : Fin 8) (adj : core.Adj a b) : G.Dart :=
  ⟨(r.core.map a, r.core.map b), r.core.map.map_adj adj⟩

def root : G.Dart := dart r 5 7 (by decide +kernel)

theorem walk (tri : ExceptionalOverlap.Triangular rotation) :
    (DualGraphQuery.map rotation).walkqz (root r) query =
      [dart r 5 7 (by decide +kernel), dart r 7 5 (by decide +kernel),
       dart r 0 5 (by decide +kernel), dart r 3 5 (by decide +kernel),
       dart r 6 3 (by decide +kernel), dart r 4 6 (by decide +kernel),
       dart r 1 6 (by decide +kernel), dart r 2 5 (by decide +kernel)] := by
  have turn (a b c : Fin 8) (h : CoreTurn a b c) := joint_preserves_turns r tri a b c h
  have right (a b c : Fin 8) (ab : core.Adj a b) (h : CoreTurn b c a) :
      (DualGraphQuery.map rotation).qstepR (dart r a b ab) = dart r c b h.1.symm :=
    DualGraphQuery.stepR rotation _ (turn b c a h)
  have left (a b c d : Fin 8) (ab : core.Adj a b)
      (h₁ : CoreTurn a c b) (h₂ : CoreTurn a d c) :
      (DualGraphQuery.map rotation).qstepL (dart r a b ab) = dart r d a h₂.1.symm :=
    DualGraphQuery.stepL rotation _ (turn a c b h₁) (turn a d c h₂)
  have e : (DualGraphQuery.map rotation).edge (root r) =
      dart r 7 5 (by decide +kernel) := rfl
  simp only [query, Hypermap.walkqz, Hypermap.walkq]
  rw [e, right 7 5 0 (by decide +kernel) (by decide +kernel),
    right 0 5 3 (by decide +kernel) (by decide +kernel),
    left 3 5 0 6 (by decide +kernel) (by decide +kernel) (by decide +kernel),
    left 6 3 0 4 (by decide +kernel) (by decide +kernel) (by decide +kernel),
    right 4 6 1 (by decide +kernel) (by decide +kernel),
    right 3 5 2 (by decide +kernel) (by decide +kernel)]
  rfl

variable [Finite V]

/-- The exact eight observations follow from the two actual occurrences. -/
theorem fitted (tri : ExceptionalOverlap.Triangular rotation)
    (cyclic : rotation.IsVertexwiseCyclic) :
    (DualGraphQuery.map rotation).Fitqz (root r) (cfquiz config) := by
  rw [compiled_query]
  unfold Hypermap.Fitqz
  rw [walk r tri, query_degrees]
  simp only [List.map_cons, List.map_nil, DualGraphQuery.arity_eq_degree rotation cyclic,
    dart, r.core.degree]
  decide +kernel

include r in
/-- The overlap is excluded under the reference minimality hypothesis on
this exact dual hypermap. Transport from other notions of minimality remains
a separate obligation. -/
theorem not_minimal [Finite G.Dart] (tri : ExceptionalOverlap.Triangular rotation)
    (cyclic : rotation.IsVertexwiseCyclic)
    (minimal : (DualGraphQuery.map rotation).MinimalCounterExample) : False :=
  ExceptionalConstructionRepair.not_fitted minimal (root r) (fitted r tri cyclic)

noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]
  (original : Data H)
  (minimal : GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample original)
  (x y : ExceptionalPattern.Occurrence (MinimalExceptionalEmbedding.rotation original minimal))
  (aligned : y.vertex 0 = x.vertex 14)

local instance : (MinimalExceptionalEmbedding.graph original minimal).LocallyFinite :=
  fun _ => Fintype.ofFinite _

def actualReading : JointReading (MinimalExceptionalEmbedding.rotation original minimal) := by
  classical
  exact jointReading x (MinimalExceptionalEmbedding.triangular original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal) y aligned

/-- Two aligned exceptional occurrences in the actual minimal facial dual
supply every step and observation of the compiled source query. -/
theorem actual_fitted :
    (DualGraphQuery.map (MinimalExceptionalEmbedding.rotation original minimal)).Fitqz
      (root (actualReading original minimal x y aligned)) (cfquiz config) :=
  fitted _ (MinimalExceptionalEmbedding.triangular original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal)

end
end FourColor.ExceptionalQueryReading
