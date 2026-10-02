import MettapediaFourColor.NearLinearChainConstruction
import MettapediaFourColor.FacialPatchInduced

/-!
# Recognizing the chain from three facial triangles

The five-vertex core is a fan of three triangles. A degree-six centre
retains all four neighbours in one proper interval. Cyclicity forces the
core vertices to be distinct. When every ambient triangle is facial, the
same interval prevents extra edges between core vertices.
-/

namespace FourColor.ChainCoreReading

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCoreOrientation ExceptionalOverlap
open NearLinearChainData

set_option maxRecDepth 32768

def core : SimpleGraph (Fin 5) := input0004.graph.comap (fun i => i.natAdd 8)
instance : DecidableRel core.Adj := by unfold core; infer_instance

def degree : Fin 5 → ℕ := ![5, 6, 5, 6, 5]
def star : Fin 5 → List (Fin 5) := ![[1, 2], [4, 3, 2, 0], [0, 1, 3], [2, 1, 4], [3, 1]]
def spoke (i : Fin 5) (p : Fin (star i).length) := (star i).get p

theorem star_specs : ∀ i : Fin 5,
    0 < (star i).length ∧ (star i).length < degree i ∧
      ∀ j, core.Adj i j ↔ ∃ p, spoke i p = j := by decide +kernel

theorem spoke_injective : ∀ i : Fin 5, Function.Injective (spoke i) := by decide +kernel

theorem center_adj : ∀ i : Fin 5, i ≠ 1 → core.Adj 1 i := by decide +kernel

def first : Fin 3 → Fin 5 := ![4, 3, 2]
def second : Fin 3 → Fin 5 := ![3, 2, 0]

theorem step_partition : ∀ (i : Fin 5) (p q : Fin (star i).length),
    q.val = p.val + 1 → ∃ k : Fin 3,
      (i = 1 ∧ spoke i p = first k ∧ spoke i q = second k) ∨
      (i = first k ∧ spoke i p = second k ∧ spoke i q = 1) ∨
      (i = second k ∧ spoke i p = 1 ∧ spoke i q = first k) := by decide +kernel

theorem star_consecutive_adjacent : ∀ (i : Fin 5) (p q : Fin (star i).length),
    q.val = p.val + 1 → core.Adj (spoke i p) (spoke i q) := by decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]

/-- Seven core edges, five exact degrees and three facial readings suffice.
Neither core injectivity nor a completed boundary is an input. -/
structure Reading (rotation : Data G) where
  map : core →g G
  degree_eq : ∀ i, G.degree (map i) = degree i
  face : ∀ k : Fin 3, Corner rotation (map 1) (map (first k)) (map (second k))

variable {rotation : Data G} (r : Reading rotation)

theorem turns (tri : Triangular rotation) (i : Fin 5) (p q : Fin (star i).length)
    (next : q.val = p.val + 1) :
    Corner rotation (r.map i) (r.map (spoke i p)) (r.map (spoke i q)) := by
  obtain ⟨k, h | h | h⟩ := step_partition i p q next
  · rcases h with ⟨hi, hp, hq⟩
    rw [hp, hq, hi]
    exact r.face k
  · rcases h with ⟨hi, hp, hq⟩
    rw [hp, hq, hi]
    exact Corner.rotate rotation tri (r.face k)
  · rcases h with ⟨hi, hp, hq⟩
    rw [hp, hq, hi]
    exact Corner.rotate rotation tri (Corner.rotate rotation tri (r.face k))

variable [Finite V]

theorem neighbors_injective (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) : Function.Injective (fun p => r.map (spoke i p)) := by
  classical
  let : Fintype V := Fintype.ofFinite V
  apply ExceptionalCoreLocalInjectivity.corner_chain_injective rotation cyclic
    (r.map i) (star_specs i).1
  · intro p
    exact r.map.map_adj ((star_specs i).2.2 _ |>.mpr ⟨p, rfl⟩)
  · intro p hp
    exact turns r tri i _ _ rfl
  · rw [r.degree_eq]
    exact le_of_lt (star_specs i).2.1

theorem injective (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic) :
    Function.Injective r.map := by
  intro i j eq
  by_cases hi : i = 1
  · subst i
    by_cases hj : j = 1
    · exact hj.symm
    · exact ((r.map.map_adj (center_adj j hj)).ne eq).elim
  by_cases hj : j = 1
  · subst j
    exact ((r.map.map_adj (center_adj i hi)).ne eq.symm).elim
  obtain ⟨p, hp⟩ := (star_specs 1).2.2 i |>.mp (center_adj i hi)
  obtain ⟨q, hq⟩ := (star_specs 1).2.2 j |>.mp (center_adj j hj)
  have pq := neighbors_injective r tri cyclic 1
    (show r.map (spoke 1 p) = r.map (spoke 1 q) by rw [hp, hq]; exact eq)
  exact hp.symm.trans ((congrArg (spoke 1) pq).trans hq)

/-- A facial-triangle hypothesis controls every possible extra core edge:
all noncentral vertices share the same proper rotation interval. -/
theorem reflects (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (facial : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a →
      Corner rotation a b c ∨ Corner rotation a c b)
    (i j : Fin 5) (adj : G.Adj (r.map i) (r.map j)) : core.Adj i j := by
  classical
  have ne : i ≠ j := fun eq => adj.ne (congrArg r.map eq)
  by_cases hi : i = 1
  · subst i
    exact center_adj j (Ne.symm ne)
  by_cases hj : j = 1
  · subst j
    exact (center_adj i hi).symm
  obtain ⟨p, rfl⟩ := (star_specs 1).2.2 i |>.mp (center_adj i hi)
  obtain ⟨q, rfl⟩ := (star_specs 1).2.2 j |>.mp (center_adj j hj)
  have successor (p q : Fin (star 1).length)
      (h : Corner rotation (r.map 1) (r.map (spoke 1 p)) (r.map (spoke 1 q))) :
      q.val = p.val + 1 := by
    apply FacialPatchInduced.corner_chain_successor rotation cyclic (r.map 1)
      (star_specs 1).1 (fun s => r.map (spoke 1 s))
    · intro s
      exact r.map.map_adj ((star_specs 1).2.2 _ |>.mpr ⟨s, rfl⟩)
    · intro s hs
      exact turns r tri 1 _ _ rfl
    · rw [r.degree_eq]
      exact (star_specs 1).2.1
    · exact h
  have left := r.map.map_adj (center_adj _ hi)
  have right := r.map.map_adj (center_adj _ hj)
  rcases facial _ _ _ left adj right.symm with h | h
  · exact star_consecutive_adjacent 1 p q (successor p q h)
  · exact (star_consecutive_adjacent 1 q p (successor q p h)).symm

end FourColor.ChainCoreReading
