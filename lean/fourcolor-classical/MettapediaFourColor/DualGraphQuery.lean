import MettapediaFourColor.FacialStarCompletion
import FourColor.Quiz

/-!
# Local configuration queries on a graph with cyclic vertex stars

The dual hypermap has the graph's vertex rotation as its face permutation.
Its query observations are exactly graph degrees. Directed corners determine
the two elementary query moves, retaining the actual darts at each branch.
-/

namespace FourColor.DualGraphQuery

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCoreOrientation

variable {V : Type*} {G : SimpleGraph V} (rotation : Data G)

def reversal : Equiv.Perm G.Dart :=
  ⟨SimpleGraph.Dart.symm, SimpleGraph.Dart.symm,
    SimpleGraph.Dart.symm_symm, SimpleGraph.Dart.symm_symm⟩

/-- The exact dual hypermap on actual graph darts. -/
def map : Hypermap G.Dart where
  edge := reversal
  node := reversal * rotation.vertexRotation⁻¹
  face := rotation.vertexRotation
  node_face_edge := by
    apply Equiv.ext
    intro d
    simp [reversal, Equiv.Perm.mul_apply]

@[simp] theorem edge (d : G.Dart) : (map rotation).edge d = d.symm := rfl

theorem stepR {a b c : V} (ab : G.Adj a b)
    (corner : Corner rotation b c a) :
    (map rotation).qstepR ⟨(a, b), ab⟩ =
      ⟨(c, b), corner.choose.symm⟩ := by
  obtain ⟨bc, ba, turn⟩ := corner
  change (rotation.vertexRotation.symm (⟨(b, a), ab.symm⟩ : G.Dart)).symm = _
  rw [← turn, Equiv.symm_apply_apply]
  rfl

theorem stepL {a b c d : V} (ab : G.Adj a b)
    (first : Corner rotation a c b) (second : Corner rotation a d c) :
    (map rotation).qstepL ⟨(a, b), ab⟩ =
      ⟨(d, a), second.choose.symm⟩ := by
  obtain ⟨ac, _, turn₁⟩ := first
  obtain ⟨ad, _, turn₂⟩ := second
  change (rotation.vertexRotation.symm
    (rotation.vertexRotation.symm (⟨(a, b), ab⟩ : G.Dart)).symm.symm).symm = _
  rw [SimpleGraph.Dart.symm_symm, ← turn₁, Equiv.symm_apply_apply,
    ← turn₂, Equiv.symm_apply_apply]
  rfl

variable [G.LocallyFinite] [Finite V]

/-- The query's arity observation is the actual degree, including every
ambient incident edge. -/
theorem arity_eq_degree (cyclic : rotation.IsVertexwiseCyclic) (d : G.Dart) :
    (map rotation).arity d = G.degree d.fst := by
  classical
  let : Fintype V := Fintype.ofFinite V
  let fiber : Finset G.Dart := Finset.univ.filter fun e => e.fst = d.fst
  have hc : rotation.vertexRotation.IsCycleOn (fiber : Set G.Dart) := by
    simpa [fiber] using cyclic d.fst
  have hd : d ∈ fiber := by simp [fiber]
  have hcard : fiber.card = G.degree d.fst := by
    change ({e : G.Dart | e.fst = d.fst} : Finset G.Dart).card = G.degree d.fst
    rw [G.dart_fst_fiber_card_eq_degree]
    exact (SimpleGraph.degree_instance_independent d.fst _ _).symm
  have periods (n : ℕ) :
      Function.minimalPeriod rotation.vertexRotation d ∣ n ↔ G.degree d.fst ∣ n := by
    rw [← Function.isPeriodicPt_iff_minimalPeriod_dvd]
    change rotation.vertexRotation^[n] d = d ↔ _
    rw [Equiv.Perm.iterate_eq_pow, hc.pow_apply_eq hd, hcard]
  exact Nat.dvd_antisymm ((periods _).mpr (dvd_refl _))
    ((periods _).mp (dvd_refl _))

end FourColor.DualGraphQuery
