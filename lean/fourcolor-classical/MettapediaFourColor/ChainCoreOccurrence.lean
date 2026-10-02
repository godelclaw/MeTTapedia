import MettapediaFourColor.ChainCoreCompletion
import MettapediaFourColor.NearLinearChainOccurrence

/-!
# The complete occurrence constructed from the chain core

The grown interface has complete core stars. Inducedness prevents an
exterior port from folding into the core while allowing boundary ports to
coincide. These facts discharge the actual reduction's geometric contract.
-/

namespace FourColor.ChainCoreOccurrence

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ChainCoreReading ChainCoreCompletion NearLinearChainData
open ExceptionalCoreOrientation ExceptionalOverlap

set_option maxRecDepth 32768

theorem owner_bounds : ∀ p : Fin 8,
    (star (owner p).1).length ≤ (owner p).2 ∧ (owner p).2 < degree (owner p).1 := by
  decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {rotation : Data G}
  [Finite V] (r : Reading rotation)

/-- All full cyclic source steps are actual ambient corners. -/
theorem full_turn (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) (p : Fin (degree i)) :
    Corner rotation (vertex r (i.natAdd 8)) (vertex r (fullSpoke i p))
      (vertex r (fullSpoke i (nextPos i p))) := by
  have adj (q : Fin (degree i)) :
      G.Adj (vertex r (i.natAdd 8)) (vertex r (fullSpoke i q)) := by
    rw [vertex_core, row_agrees r tri cyclic]
    simpa only [around_fst] using (around r i q.val).adj
  have dart_eq (q : Fin (degree i)) :
      (⟨(vertex r (i.natAdd 8), vertex r (fullSpoke i q)), adj q⟩ : G.Dart) =
        around r i q.val := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext ((vertex_core r i).trans (around_fst r i q.val).symm)
      (row_agrees r tri cyclic i q)
  refine ⟨adj p, adj (nextPos i p), ?_⟩
  exact (congrArg rotation.vertexRotation (dart_eq p)).trans
    ((around_next r cyclic i p).trans (dart_eq (nextPos i p)).symm)

/-- No incident edge can escape the completed interface. -/
theorem star_covers (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) {v : V} (adj : G.Adj (r.map i) v) :
    ∃ p : Fin (degree i), vertex r (fullSpoke i p) = v := by
  let d : G.Dart := ⟨(r.map i, v), adj⟩
  obtain ⟨n, hn, he⟩ := FacialStarCompletion.covers rotation cyclic (base r i) d rfl
  change n < G.degree (r.map i) at hn
  rw [r.degree_eq] at hn
  exact ⟨⟨n, hn⟩, (row_agrees r tri cyclic i ⟨n, hn⟩).trans
    (congrArg (fun e : G.Dart => e.snd) he)⟩

theorem around_injective (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) : Function.Injective (fun p : Fin (degree i) => (around r i p.val).snd) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  apply ExceptionalCoreLocalInjectivity.corner_chain_injective rotation cyclic
    (r.map i) (degree_pos i)
  · intro p
    simpa only [around_fst] using (around r i p.val).adj
  · intro n hn
    have h := full_turn r tri cyclic i ⟨n, by omega⟩
    rw [vertex_core, row_agrees r tri cyclic, row_agrees r tri cyclic] at h
    simpa only [nextPos, Nat.mod_eq_of_lt hn] using h
  · rw [r.degree_eq]

/-- An exterior port cannot fold back into an induced core. This permits
identifications between different ring ports while excluding core capture. -/
theorem ring_outside_core (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (reflect : ∀ i j, G.Adj (r.map i) (r.map j) → core.Adj i j)
    (p : Fin 8) (j : Fin 5) : vertex r (p.castAdd 5) ≠ r.map j := by
  intro eq
  rw [vertex_ring] at eq
  let i := (owner p).1
  let n := (owner p).2
  obtain ⟨lo, hi⟩ := owner_bounds p
  have adj : G.Adj (r.map i) (r.map j) := by
    have h := (around r i n).adj
    rw [around_fst, eq] at h
    exact h
  obtain ⟨q, hq⟩ := (star_specs i).2.2 j |>.mp (reflect i j adj)
  have he : (around r i n).snd = (around r i q.val).snd := by
    rw [around_core r tri i q, hq]
    exact eq
  have indices : (⟨n, hi⟩ : Fin (degree i)) =
      ⟨q.val, lt_trans q.isLt (star_specs i).2.1⟩ :=
    around_injective r tri cyclic i he
  have hval := congrArg Fin.val indices
  have hqbound := q.isLt
  change n = q.val at hval
  change (star i).length ≤ n at lo
  omega

theorem source_degree : ∀ i : Fin 5,
    NearLinearChainConstruction.degree (i.natAdd 8) = degree i := by decide +kernel

theorem source_turn : ∀ d : Fin 56,
    8 ≤ (NearLinearChainConstruction.vertex d).val →
    ∃ (i : Fin 5) (p : Fin (degree i)),
      NearLinearChainConstruction.vertex d = i.natAdd 8 ∧
      NearLinearChainConstruction.vertex (NearLinearChainConstruction.table.map.edge d) =
        fullSpoke i p ∧
      NearLinearChainConstruction.vertex (NearLinearChainConstruction.table.map.face d) =
        i.natAdd 8 ∧
      NearLinearChainConstruction.vertex (NearLinearChainConstruction.table.map.edge
        (NearLinearChainConstruction.table.map.face d)) = fullSpoke i (nextPos i p) := by
  decide +kernel

/-- Core geometry constructs all thirteen source images and every retained
boundary observation needed by the actual reduction. -/
def occurrence (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (reflect : ∀ i j, G.Adj (r.map i) (r.map j) → core.Adj i j) :
    NearLinearChainOccurrence.Occurrence rotation where
  hom := hom r tri cyclic
  turn := by
    intro d hd
    obtain ⟨i, p, hi, hp, hj, hq⟩ := source_turn d hd
    obtain ⟨_, _, h⟩ := full_turn r tri cyclic i p
    simpa only [NearLinearChainOccurrence.dart, hom_apply, hi, hp, hj, hq] using h
  degree_eq := by
    intro v hv
    let i : Fin 5 := ⟨v.val - 8, by omega⟩
    have eq : v = i.natAdd 8 := by apply Fin.ext; dsimp [i]; omega
    change G.degree (vertex r v) = _
    rw [eq, vertex_core, r.degree_eq, source_degree]
  core_injective := by
    intro a ha b hb eq
    change 8 ≤ a.val at ha
    change 8 ≤ b.val at hb
    let i : Fin 5 := ⟨a.val - 8, by omega⟩
    let j : Fin 5 := ⟨b.val - 8, by omega⟩
    have ae : a = i.natAdd 8 := by apply Fin.ext; dsimp [i]; omega
    have be : b = j.natAdd 8 := by apply Fin.ext; dsimp [j]; omega
    change vertex r a = vertex r b at eq
    rw [ae, be, vertex_core, vertex_core] at eq
    rw [ae, be]
    exact congrArg (fun k : Fin 5 => k.natAdd 8) (ChainCoreReading.injective r tri cyclic eq)
  outside := by
    intro p v hp hv
    let i : Fin 5 := ⟨v.val - 8, by omega⟩
    let q : Fin 8 := ⟨p.val, hp⟩
    have ve : v = i.natAdd 8 := by apply Fin.ext; dsimp [i]; omega
    have pe : p = q.castAdd 5 := by apply Fin.ext; rfl
    change vertex r p ≠ vertex r v
    rw [pe, ve, vertex_core]
    exact ring_outside_core r tri cyclic reflect q i

end FourColor.ChainCoreOccurrence
