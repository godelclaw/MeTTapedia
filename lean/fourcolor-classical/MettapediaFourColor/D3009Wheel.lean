import MettapediaFourColor.WheelNeighborhood
import MettapediaFourColor.MinimalExceptionalEmbedding

/-!
# The D3009 wheel from an actual vertex profile

The source is D3009.conf at revision
c2ce7a96e35256201526e2abb51a39d04a588b53 of
https://github.com/near-linear-4ct/reducible-configurations,
copyright 2026 Yuta Inoue, MIT licensed. The original file and licence are
retained in tools/fourcolor/near-linear.

One degree-seven vertex, one degree-five neighbour and six degree-six
neighbours construct the ordered core. All core edges, degrees, facial
triangles, injectivity and inducedness are proved from the actual rotation.
No catalogue reducibility certificate is used.
-/

namespace FourColor.D3009Wheel

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open NearLinearDiamondData ExceptionalCoreOrientation ExceptionalOverlap

set_option maxRecDepth 32768

def input : Input 21 13 where
  source := "21 13\n\
    14 7 15 21 20 19 18 16 17\n\
    15 5 6 21 14 17 5\n\
    16 6 2 3 17 14 18 1\n\
    17 6 4 5 15 14 16 3\n\
    18 6 1 16 14 19 12 13\n\
    19 6 11 12 18 14 20 10\n\
    20 6 9 10 19 14 21 8\n\
    21 6 7 8 20 14 15 6\n"
  valid := by decide +kernel

def core : SimpleGraph (Fin 8) := input.graph.comap (fun i => i.natAdd 13)
instance : DecidableRel core.Adj := by unfold core; infer_instance

def degree (i : Fin 8) : ℕ := (coreRow input.source i.val).getD 1 0
def position : Fin 8 → Option (Fin 7) :=
  ![none, some 0, some 5, some 6, some 4, some 3, some 2, some 1]
def rim : Fin 7 → Fin 8 := ![1, 7, 6, 5, 4, 2, 3]
def next (i : Fin 7) : Fin 7 := WheelNeighborhood.next (by decide) i

def adjacent : Option (Fin 7) → Option (Fin 7) → Prop
  | none, none => False
  | some _, none => True
  | none, some _ => True
  | some i, some j => j = next i ∨ i = next j
instance (a b : Option (Fin 7)) : Decidable (adjacent a b) := by
  unfold adjacent
  split <;> infer_instance

theorem position_injective : Function.Injective position := by decide +kernel
theorem position_rim : ∀ i, position (rim i) = some i := by decide +kernel
theorem core_edges : ∀ i j, core.Adj i j ↔ adjacent (position i) (position j) := by
  decide +kernel
theorem rim_degrees : ∀ i, degree (rim i) = if i = 0 then 5 else 6 := by decide +kernel

def star : Fin 8 → List (Fin 8) :=
  ![[1,7,6,5,4,2,3], [7,0,3], [3,0,4], [1,0,2],
    [2,0,5], [4,0,6], [5,0,7], [6,0,1]]
def spoke (i : Fin 8) (p : Fin (star i).length) := (star i).get p

theorem star_specs : ∀ i : Fin 8,
    0 < (star i).length ∧ (star i).length ≤ degree i ∧
      ∀ j, core.Adj i j ↔ ∃ p, spoke i p = j := by decide +kernel

theorem step_partition : ∀ (i : Fin 8) (p q : Fin (star i).length),
    q.val = p.val + 1 → ∃ k : Fin 7,
      (i = 0 ∧ spoke i p = rim k ∧ spoke i q = rim (next k)) ∨
      (i = rim k ∧ spoke i p = rim (next k) ∧ spoke i q = 0) ∨
      (i = rim (next k) ∧ spoke i p = 0 ∧ spoke i q = rim k) := by decide +kernel

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  (rotation : Data G) (d : G.Dart)

/-- A core reading keeps one shared map for all seven triangles. -/
structure Reading (rotation : Data G) where
  map : core →g G
  degree_eq : ∀ i, G.degree (map i) = degree i
  face : ∀ k : Fin 7, Corner rotation (map 0) (map (rim k)) (map (rim (next k)))

theorem reading_turns (r : Reading rotation) (tri : Triangular rotation)
    (i : Fin 8) (p q : Fin (star i).length) (step : q.val = p.val + 1) :
    Corner rotation (r.map i) (r.map (spoke i p)) (r.map (spoke i q)) := by
  obtain ⟨k, h | h | h⟩ := step_partition i p q step
  · rcases h with ⟨hi,hp,hq⟩
    rw [hp,hq,hi]
    exact r.face k
  · rcases h with ⟨hi,hp,hq⟩
    rw [hp,hq,hi]
    exact Corner.rotate rotation tri (r.face k)
  · rcases h with ⟨hi,hp,hq⟩
    rw [hp,hq,hi]
    exact Corner.rotate rotation tri (Corner.rotate rotation tri (r.face k))

def vertex (i : Fin 8) : V := WheelNeighborhood.vertex rotation d (position i)

omit [G.LocallyFinite] in
theorem vertex_center : vertex rotation d 0 = d.fst := rfl
omit [G.LocallyFinite] in
theorem vertex_rim (i : Fin 7) :
    vertex rotation d (rim i) = WheelNeighborhood.neighbor rotation d i := by
  simp only [vertex, position_rim, WheelNeighborhood.vertex, Option.elim_some]

variable [Finite V]

theorem edge_iff (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (seven : G.degree d.fst = 7)
    (facial : ∀ a b c, G.Adj a b → G.Adj b c → G.Adj c a →
      Corner rotation a b c ∨ Corner rotation a c b) (i j : Fin 8) :
    G.Adj (vertex rotation d i) (vertex rotation d j) ↔ core.Adj i j := by
  rw [core_edges]
  unfold vertex
  generalize position i = a
  generalize position j = b
  cases a with
  | none =>
    cases b with
    | none => simp [WheelNeighborhood.vertex, adjacent]
    | some b => exact iff_of_true (WheelNeighborhood.adjacent rotation d b) trivial
  | some a =>
    cases b with
    | none => exact iff_of_true (WheelNeighborhood.adjacent rotation d a).symm trivial
    | some b =>
      exact WheelNeighborhood.rim_adj_iff rotation d tri cyclic seven (by decide) facial a b

/-- The source edges follow triangular rotation, even without faciality of
all ambient triangles. Faciality is needed only for reflection. -/
def hom (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (seven : G.degree d.fst = 7) : core →g G where
  toFun := vertex rotation d
  map_rel' := by
    intro i j h
    rw [core_edges] at h
    unfold vertex
    generalize position i = a at *
    generalize position j = b at *
    cases a with
    | none =>
      cases b with
      | none => exact h.elim
      | some b => exact WheelNeighborhood.adjacent rotation d b
    | some a =>
      cases b with
      | none => exact (WheelNeighborhood.adjacent rotation d a).symm
      | some b =>
        rcases h with h | h
        · subst b
          exact (Corner.rotate rotation tri
            (WheelNeighborhood.corner rotation d cyclic seven (by decide) a)).choose
        · subst a
          exact (Corner.rotate rotation tri
            (WheelNeighborhood.corner rotation d cyclic seven (by decide) b)).choose.symm

theorem injective (cyclic : rotation.IsVertexwiseCyclic) (seven : G.degree d.fst = 7) :
    Function.Injective (vertex rotation d) :=
  (WheelNeighborhood.vertex_injective rotation d cyclic seven (by decide)).comp position_injective

theorem degrees (cyclic : rotation.IsVertexwiseCyclic) (seven : G.degree d.fst = 7)
    (five : G.degree d.snd = 5)
    (six : ∀ w, G.Adj d.fst w → w ≠ d.snd → G.degree w = 6) :
    ∀ i, G.degree (vertex rotation d i) = degree i := by
  have nz (i : Fin 7) (hi : i ≠ 0) : WheelNeighborhood.neighbor rotation d i ≠ d.snd := by
    intro eq
    have hj : WheelNeighborhood.neighbor rotation d (0 : Fin 7) = d.snd := rfl
    exact hi (WheelNeighborhood.neighbor_injective rotation d cyclic seven (by decide)
      (eq.trans hj.symm))
  have hr (i : Fin 7) : G.degree (vertex rotation d (rim i)) = degree (rim i) := by
    rw [vertex_rim, rim_degrees]
    split_ifs with hi
    · subst i; exact five
    · exact six _ (WheelNeighborhood.adjacent rotation d i) (nz i hi)
  intro i
  have cases : i = 0 ∨ ∃ j, i = rim j := by revert i; decide +kernel
  rcases cases with rfl | ⟨j, rfl⟩
  · exact seven
  · exact hr j

theorem face (cyclic : rotation.IsVertexwiseCyclic) (seven : G.degree d.fst = 7)
    (i : Fin 7) : Corner rotation (vertex rotation d 0)
      (vertex rotation d (rim i)) (vertex rotation d (rim (next i))) := by
  rw [vertex_center, vertex_rim, vertex_rim]
  exact WheelNeighborhood.corner rotation d cyclic seven (by decide) i

theorem turns (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (seven : G.degree d.fst = 7) (i : Fin 8) (p q : Fin (star i).length)
    (step : q.val = p.val + 1) :
    Corner rotation (vertex rotation d i) (vertex rotation d (spoke i p))
      (vertex rotation d (spoke i q)) := by
  obtain ⟨k, h | h | h⟩ := step_partition i p q step
  · rcases h with ⟨hi,hp,hq⟩
    rw [hp,hq,hi]
    exact face rotation d cyclic seven k
  · rcases h with ⟨hi,hp,hq⟩
    rw [hp,hq,hi]
    exact Corner.rotate rotation tri (face rotation d cyclic seven k)
  · rcases h with ⟨hi,hp,hq⟩
    rw [hp,hq,hi]
    exact Corner.rotate rotation tri (Corner.rotate rotation tri (face rotation d cyclic seven k))

/-- Degrees and an actual directed edge construct the reading; its geometric
fields are conclusions rather than hypotheses on an abstract patch. -/
def reading (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (seven : G.degree d.fst = 7) (five : G.degree d.snd = 5)
    (six : ∀ w, G.Adj d.fst w → w ≠ d.snd → G.degree w = 6) : Reading rotation :=
  ⟨hom rotation d tri cyclic seven, degrees rotation d cyclic seven five six,
    face rotation d cyclic seven⟩

end FourColor.D3009Wheel
