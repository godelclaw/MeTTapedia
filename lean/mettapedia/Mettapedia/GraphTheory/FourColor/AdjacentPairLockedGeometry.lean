import Mettapedia.GraphTheory.FourColor.AdjacentPairLockedOrbit
import Mathlib.Combinatorics.SimpleGraph.Girth

/-!
# Geometry of the trapped adjacent-pair deletion

The orbit obstruction uses the existing thirty-vertex bridgeless cubic
sphere, whose actual faces have lengths five and six. The retained edges
are the union of a facial region with connected complement. Its next face
adds three edges and leaves a two-edge matching cap. The ambient primal
graph has girth exactly five.
-/

namespace Mettapedia.GraphTheory.FourColor.AdjacentPairLockedGeometry

open GoertzelV24FaceDualConnectedness
open AdjacentPairLockedOrbit
open MatchingCapThreeSwitchGeometry (Face boundary rotation dual connectedRegion)

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def selected : Finset Face := Finset.univ \ {0, 1, 2, 3}
def after : Finset Face := insert 0 selected

theorem connected_sides : connectedRegion selected ∧ connectedRegion selectedᶜ := by
  decide +kernel

theorem connected_after : connectedRegion after ∧ connectedRegion afterᶜ := by
  decide +kernel

theorem retained_edges : selected.biUnion boundary = old := by decide +kernel

theorem exposed_edges : after.biUnion boundary \ old = {0, 2, 3} := by decide +kernel

theorem cap_edges : (after.biUnion boundary)ᶜ = {1, 4} := by decide +kernel

theorem cap_disjoint : Disjoint (inc 1) (inc 4) := by decide +kernel

abbrev primal := rotationPrimalGraph rotation

private def neighbours : Vertex → Finset Vertex :=
  ![{1,2,3}, {0,4,5}, {0,6,7}, {0,8,9}, {1,9,10}, {1,6,11},
    {2,5,12}, {2,8,13}, {3,7,14}, {3,4,15}, {4,16,17}, {5,17,18},
    {6,18,19}, {7,19,20}, {8,20,21}, {9,16,21}, {10,15,22}, {10,11,23},
    {11,12,24}, {12,13,25}, {13,14,26}, {14,15,27}, {16,23,28}, {17,22,24},
    {18,23,29}, {19,26,29}, {20,25,27}, {21,26,28}, {22,27,29}, {24,25,28}]

private theorem adj_iff_mem : ∀ u v, primal.Adj u v ↔ v ∈ neighbours u := by
  decide +kernel

private theorem triangle_certificate : ∀ u v, v ∈ neighbours u →
    Disjoint (neighbours u) (neighbours v) := by decide +kernel

private theorem square_certificate : ∀ u v, u ≠ v →
    ((neighbours u) ∩ (neighbours v)).card ≤ 1 := by decide +kernel

theorem no_triangle {u v w : Vertex} (huv : primal.Adj u v)
    (huw : primal.Adj u w) (hvw : primal.Adj v w) : False :=
  Finset.disjoint_left.mp (triangle_certificate u v ((adj_iff_mem u v).mp huv))
    ((adj_iff_mem u w).mp huw) ((adj_iff_mem v w).mp hvw)

theorem no_square {a b c d : Vertex} (hab : primal.Adj a b)
    (hbc : primal.Adj b c) (hcd : primal.Adj c d) (hda : primal.Adj d a)
    (hac : a ≠ c) (hbd : b ≠ d) : False := by
  apply hbd
  apply Finset.card_le_one.mp (square_certificate a c hac)
  · exact Finset.mem_inter.mpr ⟨(adj_iff_mem a b).mp hab, (adj_iff_mem c b).mp hbc.symm⟩
  · exact Finset.mem_inter.mpr ⟨(adj_iff_mem a d).mp hda.symm, (adj_iff_mem c d).mp hcd⟩

/-- The girth bound concerns every primal cycle, not just the facial ones. -/
theorem cycle_length_ge_five {a : Vertex} (p : primal.Walk a a) (hp : p.IsCycle) :
    5 ≤ p.length := by
  by_contra h
  have h3 := hp.three_le_length
  have hl : p.length = 3 ∨ p.length = 4 := by omega
  rcases hl with hl | hl
  · have h01 := p.adj_getVert_succ (i := 0) (by omega)
    have h12 := p.adj_getVert_succ (i := 1) (by omega)
    have h20 := p.adj_getVert_succ (i := 2) (by omega)
    have hw : p.getVert 3 = p.getVert 0 := by
      rw [← hl, p.getVert_length, p.getVert_zero]
    rw [hw] at h20
    exact no_triangle h01 h20.symm h12
  · have h01 := p.adj_getVert_succ (i := 0) (by omega)
    have h12 := p.adj_getVert_succ (i := 1) (by omega)
    have h23 := p.adj_getVert_succ (i := 2) (by omega)
    have h30 := p.adj_getVert_succ (i := 3) (by omega)
    have hw : p.getVert 4 = p.getVert 0 := by
      rw [← hl, p.getVert_length, p.getVert_zero]
    rw [hw] at h30
    apply no_square h01 h12 h23 h30
    · intro heq
      have : (0 : Nat) = 2 := hp.getVert_injOn' (by simp [hl]) (by simp [hl]) heq
      omega
    · intro heq
      have : (1 : Nat) = 3 := hp.getVert_injOn' (by simp [hl]) (by simp [hl]) heq
      omega

private def pentagon : primal.Walk 0 0 :=
  .cons (show primal.Adj 0 1 by decide)
    (.cons (show primal.Adj 1 4 by decide)
      (.cons (show primal.Adj 4 9 by decide)
        (.cons (show primal.Adj 9 3 by decide)
          (.cons (show primal.Adj 3 0 by decide) .nil))))

private theorem pentagon_cycle : pentagon.IsCycle :=
  { edges_nodup := by decide +kernel
    ne_nil := by simp [pentagon]
    support_nodup := by decide +kernel }

theorem girth_eq_five : primal.girth = 5 := by
  have hlo : 5 ≤ primal.egirth := SimpleGraph.le_egirth.mpr (by
    intro a p hp
    exact_mod_cast cycle_length_ge_five p hp)
  have hhi : primal.egirth ≤ 5 := pentagon_cycle.egirth_le_length
  have he := le_antisymm hhi hlo
  simp [SimpleGraph.girth, he]

/-- The obstruction is transported to the literal endpoints of the sphere rotation. -/
theorem no_history_extension_on_rotation
    {C : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3)}
    (p : KempeChainCertificate.History base C) :
    ¬ ∃ d : Edge → Fin 3,
      GoertzelV24ForkInterfaceSupport.Proper rotation.endpoints Finset.univ d ∧
        ∀ x ∈ old, d x = C x := by
  rw [show rotation.endpoints = inc from funext MatchingCapThreeSwitchGeometry.endpoints_eq]
  exact no_history_extension p

theorem ambient_colourable :
    ∃ d : Edge → Fin 3,
      GoertzelV24ForkInterfaceSupport.Proper rotation.endpoints Finset.univ d := by
  rw [show rotation.endpoints = inc from funext MatchingCapThreeSwitchGeometry.endpoints_eq]
  exact ⟨fullAssignment, full_proper⟩

end Mettapedia.GraphTheory.FourColor.AdjacentPairLockedGeometry
