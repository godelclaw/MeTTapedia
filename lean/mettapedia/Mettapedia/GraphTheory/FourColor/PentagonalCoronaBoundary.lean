import Mettapedia.GraphTheory.FourColor.PentagonalCoronaIncidence
import Mettapedia.GraphTheory.FourColor.SixPortBoundaryConnectivity

/-!
# The six potential ports of a face-derived corona

Before assuming the outer cycle is induced, cubicity confines every outgoing
dart to one of six positions. An additional outer chord consumes two distinct
positions, reducing the actual boundary to at most four darts. All vertices
and darts in the count belong to the original graph.
-/

namespace Mettapedia.GraphTheory.FourColor.PentagonalCoronaGeometry

open SimpleGraph SimpleGraphDartRotation PhysicalForkCodeFaces
open CubicCycleIncidence ElevenLobeSpokeOrder GoertzelV24CubicSmallBoundaryCycle

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance coronaBoundaryEdgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance coronaBoundaryEdgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (rotation : Data G) (root : G.Dart)

/-- The retained vertices, without an inducedness assumption. -/
def tracedSide (v : V) : Prop := v ∈ Set.range (tracedVertex rotation root)

theorem outer_mem_tracedSide (i : Fin 11) : tracedSide rotation root (outerVertex rotation root i) :=
  ⟨.inl i, rfl⟩

theorem inner_mem_tracedSide (i : Fin 5) :
    tracedSide rotation root (center rotation root i).fst := ⟨.inr i, rfl⟩

def outwardSlots : Finset (Fin 11) := {0, 2, 4, 6, 8, 10}

theorem outwardSlots_card : outwardSlots.card = 6 := by decide

theorem outward_or_inward (i : Fin 11) : i ∈ outwardSlots ∨ ∃ j, i = inward j := by
  revert i
  decide

theorem outerStar_inward_snd (j : Fin 5) :
    (outerStar rotation root (inward j) 0).snd = (center rotation root (-j)).fst := by
  fin_cases j <;> change (rotation.vertexRotation _).fst = _ <;>
    exact rotation.vertexRotation_fst _

theorem outerStar_surjective_at (hC : Cubic3 rotation.toRotationSystem)
    (i : Fin 11) (d : G.Dart) (hd : d.fst = outerVertex rotation root i) :
    ∃ j, outerStar rotation root i j = d := by
  have hh : rotation.toRotationSystem.vertOf d =
      rotation.toRotationSystem.vertOf (outerBase rotation root i) := hd
  rcases hC.fiber (outerBase rotation root i) d hh with he | he | he
  · subst d
    cases hb : reverseAt i
    · exact ⟨0, by simp [outerStar, hb]⟩
    · exact ⟨2, by simp [outerStar, hb]⟩
  · change d = rotation.vertexRotation (outerBase rotation root i) at he
    subst d
    exact ⟨1, by simp [outerStar]⟩
  · change d = rotation.vertexRotation (rotation.vertexRotation (outerBase rotation root i)) at he
    subst d
    cases hb : reverseAt i
    · exact ⟨2, by simp [outerStar, hb]⟩
    · exact ⟨0, by simp [outerStar, hb]⟩

variable (hC : Cubic3 rotation.toRotationSystem)
  (hroot : (rotation.toRotationSystem.phi ^ 5) root = root)
  (hn : NeighborPeriods rotation root)
  (hv : Function.Injective (tracedVertex rotation root))
  (hcubic : G.IsRegularOfDegree 3)

include hC hroot hn hv hcubic

/-- Every actual cut dart is an outward spoke. No exterior endpoint
injectivity or outer inducedness is used. -/
theorem crossing_origin (d : CrossingSideDart G (tracedSide rotation root)) :
    ∃ i ∈ outwardSlots, outerStar rotation root i 0 = d.1 := by
  obtain ⟨v, he⟩ := d.2.1
  cases v with
  | inl i =>
    obtain ⟨s, hs⟩ := outerStar_surjective_at rotation root hC i d.1 he.symm
    have hnxt := d.2.2
    rw [← hs] at hnxt
    fin_cases s
    · rcases outward_or_inward i with hi | ⟨j, rfl⟩
      · exact ⟨i, hi, hs⟩
      · change ¬ tracedSide rotation root (outerStar rotation root (inward j) 0).snd at hnxt
        rw [outerStar_inward_snd rotation root j] at hnxt
        exact (hnxt (inner_mem_tracedSide rotation root _)).elim
    · change ¬ tracedSide rotation root (outerStar rotation root i 1).snd at hnxt
      rw [outerStar_prev_snd rotation root hC hroot hn i] at hnxt
      exact (hnxt (outer_mem_tracedSide rotation root _)).elim
    · change ¬ tracedSide rotation root (outerStar rotation root i 2).snd at hnxt
      rw [outerStar_next_snd rotation root hC hroot hn i] at hnxt
      exact (hnxt (outer_mem_tracedSide rotation root _)).elim
  | inr i =>
    let C := innerFrame rotation root hroot hv
    have ha : G.Adj (C.vertex i) d.1.snd := by
      change G.Adj (tracedVertex rotation root (.inr i)) d.1.snd
      rw [he]
      exact d.1.adj
    rcases (C.adjacent_iff (by decide) hcubic i d.1.snd).mp ha with hs | hs | hs
    · apply (d.2.2 ?_).elim
      rw [hs]
      change tracedSide rotation root (rotation.vertexRotation (center rotation root i)).snd
      rw [spoke_at_inward]
      exact outer_mem_tracedSide rotation root _
    · exact (d.2.2 (hs ▸ inner_mem_tracedSide rotation root _)).elim
    · exact (d.2.2 (hs ▸ inner_mem_tracedSide rotation root _)).elim

def crossingIndex (d : CrossingSideDart G (tracedSide rotation root)) : Fin 11 :=
  (crossing_origin rotation root hC hroot hn hv hcubic d).choose

theorem crossingIndex_spec (d : CrossingSideDart G (tracedSide rotation root)) :
    crossingIndex rotation root hC hroot hn hv hcubic d ∈ outwardSlots ∧
    outerStar rotation root (crossingIndex rotation root hC hroot hn hv hcubic d) 0 = d.1 :=
  (crossing_origin rotation root hC hroot hn hv hcubic d).choose_spec

theorem crossingIndex_injective :
    Function.Injective (crossingIndex rotation root hC hroot hn hv hcubic) := by
  intro a b he
  apply Subtype.ext
  rw [← (crossingIndex_spec rotation root hC hroot hn hv hcubic a).2,
    ← (crossingIndex_spec rotation root hC hroot hn hv hcubic b).2, he]

/-- A chosen collection of possible outward positions bounds the entire cut. -/
theorem crossing_card_le_of_slots (slots : Finset (Fin 11))
    (hslots : ∀ d : CrossingSideDart G (tracedSide rotation root),
      crossingIndex rotation root hC hroot hn hv hcubic d ∈ slots) :
    Fintype.card (CrossingSideDart G (tracedSide rotation root)) ≤ slots.card := by
  classical
  let f (d : CrossingSideDart G (tracedSide rotation root)) : slots :=
    ⟨crossingIndex rotation root hC hroot hn hv hcubic d, hslots d⟩
  have hi : Function.Injective f := fun a b he =>
    crossingIndex_injective rotation root hC hroot hn hv hcubic (congrArg Subtype.val he)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hi

theorem crossing_card_le_six :
    Fintype.card (CrossingSideDart G (tracedSide rotation root)) ≤ 6 := by
  rw [← outwardSlots_card]
  exact crossing_card_le_of_slots rotation root hC hroot hn hv hcubic outwardSlots
    (fun d => (crossingIndex_spec rotation root hC hroot hn hv hcubic d).1)

omit hcubic in
/-- An extra outer edge must be the unused spoke at its source. -/
theorem chord_spoke {i j : Fin 11}
    (ha : G.Adj (outerVertex rotation root i) (outerVertex rotation root j))
    (hp : j ≠ i - 1) (hnxt : j ≠ i + 1) :
    i ∈ outwardSlots ∧ (outerStar rotation root i 0).snd = outerVertex rotation root j := by
  let d : G.Dart := ⟨(outerVertex rotation root i, outerVertex rotation root j), ha⟩
  obtain ⟨slot, hs⟩ := outerStar_surjective_at rotation root hC i d rfl
  have hvouter : Function.Injective (outerVertex rotation root) :=
    fun _ _ he => Sum.inl.inj (hv he)
  have hh := congrArg (fun d : G.Dart => d.snd) hs
  change (outerStar rotation root i slot).snd = outerVertex rotation root j at hh
  fin_cases slot
  · change (outerStar rotation root i 0).snd = outerVertex rotation root j at hh
    refine ⟨?_, hh⟩
    rcases outward_or_inward i with hi | ⟨k, rfl⟩
    · exact hi
    · rw [outerStar_inward_snd rotation root k] at hh
      have he := hv (show tracedVertex rotation root (.inr (-k)) =
        tracedVertex rotation root (.inl j) from hh)
      contradiction
  · change (outerStar rotation root i 1).snd = outerVertex rotation root j at hh
    rw [outerStar_prev_snd rotation root hC hroot hn i] at hh
    exact (hp (hvouter hh).symm).elim
  · change (outerStar rotation root i 2).snd = outerVertex rotation root j at hh
    rw [outerStar_next_snd rotation root hC hroot hn i] at hh
    exact (hnxt (hvouter hh).symm).elim

/-- A chord removes two potential ports from the actual cut, including both
ends even when other exterior attachments coincide. -/
theorem crossing_card_le_four_of_chord {i j : Fin 11}
    (ha : G.Adj (outerVertex rotation root i) (outerVertex rotation root j))
    (hp : j ≠ i - 1) (hnxt : j ≠ i + 1) :
    Fintype.card (CrossingSideDart G (tracedSide rotation root)) ≤ 4 := by
  classical
  obtain ⟨hi, his⟩ := chord_spoke rotation root hC hroot hn hv ha hp hnxt
  have hp' : i ≠ j - 1 := by
    intro he
    apply hnxt
    rw [he]
    simp
  have hn' : i ≠ j + 1 := by
    intro he
    apply hp
    rw [he]
    simp
  obtain ⟨hj, hjs⟩ := chord_spoke rotation root hC hroot hn hv ha.symm hp' hn'
  have hij : i ≠ j := fun he => ha.ne (congrArg (outerVertex rotation root) he)
  have hj' : j ∈ outwardSlots.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
  have hcard : ((outwardSlots.erase i).erase j).card = 4 := by
    rw [Finset.card_erase_of_mem hj', Finset.card_erase_of_mem hi, outwardSlots_card]
  rw [← hcard]
  apply crossing_card_le_of_slots rotation root hC hroot hn hv hcubic
  intro d
  have hs := crossingIndex_spec rotation root hC hroot hn hv hcubic d
  have avoids (k : Fin 11) (hk : tracedSide rotation root (outerStar rotation root k 0).snd) :
      crossingIndex rotation root hC hroot hn hv hcubic d ≠ k := by
    intro he
    have hd := hs.2
    rw [he] at hd
    exact d.2.2 ((congrArg (fun d : G.Dart => d.snd) hd) ▸ hk)
  apply Finset.mem_erase.mpr
  refine ⟨avoids j ?_, Finset.mem_erase.mpr ⟨avoids i ?_, hs.1⟩⟩
  · rw [hjs]; exact outer_mem_tracedSide rotation root _
  · rw [his]; exact outer_mem_tracedSide rotation root _

omit hC hroot hn hcubic in
theorem card_tracedSide : Fintype.card {v // tracedSide rotation root v} = 16 := by
  classical
  let e : (Fin 11 ⊕ Fin 5) ≃ {v // tracedSide rotation root v} :=
    Equiv.ofBijective (fun i => ⟨tracedVertex rotation root i, ⟨i, rfl⟩⟩) ⟨by
      intro a b he
      exact hv (congrArg Subtype.val he), by
      rintro ⟨v, i, rfl⟩
      exact ⟨i, rfl⟩⟩
  simpa using (Fintype.card_congr e).symm

omit hC hn in
/-- The central cycle is already present before the outer boundary is known
to be induced. -/
theorem tracedSide_hasCycle : HasCycleOnSide G (tracedSide rotation root) := by
  let C := innerFrame rotation root hroot hv
  have hcycle : HasCycleOnSide G C.keep := by
    apply MatchingBoundaryConnectivity.hasCycle_of_injective_boundary hcubic C.keep C.connected
    intro a b he
    obtain ⟨i, hi⟩ := (C.keep_iff _).mp a.2.1
    obtain ⟨sa, ha⟩ := C.star_surjective_at (by decide) hcubic i a.1 hi
    obtain ⟨sb, hb⟩ := C.star_surjective_at (by decide) hcubic i b.1 (he.symm.trans hi)
    have hsa : sa = 0 := (C.star_boundary_iff i sa).mp (by
      rw [ha]; exact a.2.2)
    have hsb : sb = 0 := (C.star_boundary_iff i sb).mp (by
      rw [hb]; exact b.2.2)
    subst sa; subst sb
    exact Subtype.ext (ha.symm.trans hb)
  apply hcycle.mono
  intro v hv'
  obtain ⟨i, hi⟩ := (C.keep_iff _).mp hv'
  rw [hi]
  exact inner_mem_tracedSide rotation root i

end
end Mettapedia.GraphTheory.FourColor.PentagonalCoronaGeometry
