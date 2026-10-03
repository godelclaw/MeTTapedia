import MettapediaFourColor.ResidualSeedRepairReconstruction
import MettapediaFourColor.PatchBoundaryGluing
import Mettapedia.GraphTheory.FourColor.ComponentDetachExample

/-!
# Exact patch gluing for the retained D0092 occurrence

The source reading has complete core stars. Its complement is exactly the
existing 155-vertex graph, so compatible source and exterior colourings
reconstruct the existing 162-vertex ambient graph. This file does not supply
compatible colourings or assume their existence.
-/

namespace FourColor.ResidualExteriorPatch

open SimpleGraph KempeDetachExample FiveTriangleCollapseObstruction

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def images : List (Fin 162) := [45,42,102,104,18,121,19,48,51,113,15,47,49,50,1,12,105,103]
def point (i : Fin 18) : Fin 162 := images.get i
def sourceIndex (v : Fin 162) : Fin 18 := ⟨images.idxOf v % 18, Nat.mod_lt _ (by decide)⟩
def interior : Set (Fin 18) := {i | 11 ≤ i.val}

theorem point_injective : Function.Injective point := by decide +kernel

theorem mapped_edges : ∀ e ∈ ResidualSeedRepairCertificate.edges,
    ambient.Adj (point e.1) (point e.2) := by
  have h : ResidualSeedRepairCertificate.edges.all
      (fun e => decide (ambient.Adj (point e.1) (point e.2))) = true := by decide +kernel
  exact fun e he => of_decide_eq_true (List.all_eq_true.mp h e he)

def hom : upper.graph →g ambient where
  toFun := point
  map_rel' := by
    intro a b edge
    rcases (ResidualSeedRepairCertificate.source_edges a b).mp edge with h | h
    · exact mapped_edges _ h
    · exact (mapped_edges _ h).symm

def Full (u v : Fin 162) : Prop := ∀ i : Fin 18, 11 ≤ i.val → point i = u →
  upper.graph.Adj i (sourceIndex v) ∧ point (sourceIndex v) = v
instance (u v) : Decidable (Full u v) := inferInstanceAs (Decidable (∀ _i : Fin 18, _))

theorem full_check : ambientEdges.all (fun e => decide (Full e.1 e.2 ∧ Full e.2 e.1)) = true := by
  decide +kernel

theorem covers : ∀ i ∈ interior, ∀ v, ambient.Adj (hom i) v →
    ∃ a, upper.graph.Adj i a ∧ hom a = v := by
  intro i hi v edge
  have h : Full (point i) v := by
    rcases edge with h | h
    · exact (of_decide_eq_true (List.all_eq_true.mp full_check _ h)).1
    · exact (of_decide_eq_true (List.all_eq_true.mp full_check _ h)).2
  exact ⟨sourceIndex v, h i hi rfl⟩

theorem complement_check : ∀ v : Fin 162,
    v ∉ carrier ↔ ∃ i : Fin 18, 11 ≤ i.val ∧ point i = v := by decide +kernel

theorem outside_iff (v : Fin 162) : v ∉ hom '' interior ↔ v ∈ carrier := by
  change (¬ ∃ i : Fin 18, 11 ≤ i.val ∧ point i = v) ↔ v ∈ carrier
  simpa only [not_not] using not_congr (complement_check v).symm

theorem inverse_on_carrier : ∀ v : Fin 162, v ∈ carrier → includeExterior (position v) = v := by
  decide +kernel

theorem boundary_reading : ∀ j : Fin 11,
    point (j.castAdd 7) = includeExterior (ports.get j) := by decide +kernel

/-- The same exterior witness is kept at every retained vertex. -/
theorem reconstruct (k : upper.graph.Coloring Color) (D : graph.Coloring Color)
    (agree : ∀ j : Fin 11, k (j.castAdd 7) = D (ports.get j)) :
    ∃ K : ambient.Coloring Color, (∀ i, K (point i) = k i) ∧
      ∀ w, K (includeExterior w) = D w := by
  have nocapture (i : Fin 18) (hi : i ∉ interior) : hom i ∉ hom '' interior := by
    rintro ⟨j, hj, he⟩
    exact hi (point_injective he ▸ hj)
  have valid {u v : Fin 162} (hu : u ∉ hom '' interior) (hv : v ∉ hom '' interior)
      (adj : ambient.Adj u v) : D (position u) ≠ D (position v) := by
    apply D.valid
    apply (exterior_adj _ _).mp
    rwa [inverse_on_carrier u ((outside_iff u).mp hu),
      inverse_on_carrier v ((outside_iff v).mp hv)]
  obtain ⟨K, inside, outside⟩ := PatchBoundaryGluing.reconstruct hom interior
    point_injective.injOn nocapture covers k (fun v => D (position v)) valid (by
      intro i hi
      have hlt : i.val < 11 := by change ¬ 11 ≤ i.val at hi; omega
      let j : Fin 11 := ⟨i.val, hlt⟩
      have hj : j.castAdd 7 = i := Fin.ext rfl
      change k i = D (position (point i))
      rw [← hj, boundary_reading, position_include]
      exact agree j)
  refine ⟨K, inside, fun w => ?_⟩
  rw [outside _ ((outside_iff _).mpr (include_mem w)), position_include]

end FourColor.ResidualExteriorPatch
