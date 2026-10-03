import MettapediaFourColor.ThreeTriangleFan
import MettapediaFourColor.FacialBoundaryScheme

/-!
# The three-triangle fan uses the common facial boundary law

The fan layout supplies the core-interval and seam data. Its eight-port and
nine-port consumers retain the same interface while sharing geometric
completion with the four-triangle fan and tripod.
-/

namespace FourColor.FanBoundaryScheme

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ThreeTriangleFan ExceptionalCoreOrientation ExceptionalOverlap

def coreLayout : FacialBoundaryScheme.Core 5 where
  graph := core
  star := star
  positive := fun i => (star_specs i).1
  adjacent := fun i => (star_specs i).2
  seam := by decide +kernel

def firstNeighbor : Fin 5 → Fin 5 := FacialBoundaryScheme.firstNeighbor coreLayout

theorem first_edge : ∀ i, core.Adj i (firstNeighbor i) :=
  FacialBoundaryScheme.first_edge coreLayout

theorem first_spoke : ∀ i,
    spoke i ⟨0, (star_specs i).1⟩ = firstNeighbor i := by decide +kernel

theorem seam_last : ∀ i : Fin 5,
    spoke (firstNeighbor i)
      ⟨(star (firstNeighbor i)).length - 1, by
        have := (star_specs (firstNeighbor i)).1; omega⟩ = i := by decide +kernel

abbrev Scheme (ports : ℕ) := FacialBoundaryScheme.Scheme coreLayout ports

variable {ports : ℕ} (s : Scheme ports)

theorem degree_pos (i : Fin 5) : 0 < s.degree i :=
  FacialBoundaryScheme.degree_pos coreLayout s i

abbrev nextPos := FacialBoundaryScheme.nextPos coreLayout s

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] {rotation : Data G}

structure Reading (s : Scheme ports) (rotation : Data G)
    extends ThreeTriangleFan.Reading rotation where
  degree_eq : ∀ i, G.degree (map i) = s.degree i

variable {s} (r : Reading s rotation)

def completedReading (tri : Triangular rotation) :
    FacialBoundaryScheme.Reading coreLayout s rotation where
  map := r.map
  turns := ThreeTriangleFan.turns r.toReading tri
  degree_eq := r.degree_eq

def base (i : Fin 5) : G.Dart :=
  ⟨(r.map i, r.map (firstNeighbor i)), r.map.map_adj (first_edge i)⟩

def around (i : Fin 5) (n : ℕ) : G.Dart := (rotation.vertexRotation ^ n) (base r i)

theorem around_fst (i : Fin 5) (n : ℕ) : (around r i n).fst = r.map i :=
  FacialStarCompletion.pow_fst rotation (base r i) n

theorem around_step (i : Fin 5) (n : ℕ) :
    rotation.vertexRotation (around r i n) = around r i (n + 1) := by
  simp only [around, pow_succ', Equiv.Perm.mul_apply]

theorem around_core (tri : Triangular rotation) (i : Fin 5) (p : Fin (star i).length) :
    (around r i p.val).snd = r.map (spoke i p) :=
  FacialBoundaryScheme.around_core coreLayout (completedReading r tri) tri i p

def vertex (v : Fin (ports + 5)) : V :=
  if h : v.val < ports then (around r (s.owner ⟨v.val, h⟩).1 (s.owner ⟨v.val, h⟩).2).snd
  else r.map ⟨v.val - ports, by omega⟩

theorem vertex_core (i : Fin 5) : vertex r (i.natAdd ports) = r.map i := by
  simp [vertex, Fin.natAdd]

theorem vertex_ring (b : Fin ports) :
    vertex r (b.castAdd 5) = (around r (s.owner b).1 (s.owner b).2).snd := by
  simp [vertex, b.isLt]

theorem core_near (i : Fin 5) :
    r.map i ∈ LocalCoverageAssembly.closedBall G (r.map 1) 1 := by
  by_cases hi : i = 1
  · subst i
    exact LocalCoverageAssembly.centre_mem G _ _
  · let p : G.Walk (r.map 1) (r.map i) :=
      .cons (r.map.map_adj (center_adj i hi)) .nil
    simpa [LocalCoverageAssembly.closedBall, p] using p.edist_le

theorem vertex_near (v : Fin (ports + 5)) :
    vertex r v ∈ LocalCoverageAssembly.closedBall G (r.map 1) 2 := by
  by_cases hv : v.val < ports
  · let q : Fin ports := ⟨v.val, hv⟩
    have ve : v = q.castAdd 5 := by apply Fin.ext; rfl
    rw [ve, vertex_ring]
    apply LocalCoverageAssembly.ball_recenter G (b := 1) (core_near r (s.owner q).1)
    let p : G.Walk (r.map (s.owner q).1) (around r (s.owner q).1 (s.owner q).2).snd :=
      .cons (by simpa only [around_fst] using (around r (s.owner q).1 (s.owner q).2).adj) .nil
    simpa [LocalCoverageAssembly.closedBall, p] using p.edist_le
  · let i : Fin 5 := ⟨v.val - ports, by omega⟩
    have ve : v = i.natAdd ports := by apply Fin.ext; dsimp [i]; omega
    rw [ve, vertex_core]
    exact LocalCoverageAssembly.ball_mono G (by decide : 1 ≤ 2) (core_near r i)

variable [Finite V]

theorem around_period (cyclic : rotation.IsVertexwiseCyclic) (i : Fin 5) :
    around r i (s.degree i) = around r i 0 := by
  have h := FacialStarCompletion.pow_degree rotation cyclic (base r i)
  change (rotation.vertexRotation ^ G.degree (r.map i)) (base r i) = base r i at h
  rw [r.degree_eq] at h
  exact h

theorem around_previous (cyclic : rotation.IsVertexwiseCyclic) (i : Fin 5) :
    around r i (s.degree i - 1) = rotation.vertexRotation.symm (base r i) := by
  have h := FacialStarCompletion.pow_pred rotation cyclic (base r i)
  change (rotation.vertexRotation ^ (G.degree (r.map i) - 1)) _ = _ at h
  rw [r.degree_eq] at h
  exact h

theorem outer_seam (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) :
    (around r i (s.degree i - 1)).snd =
      (around r (firstNeighbor i) (star (firstNeighbor i)).length).snd :=
  FacialBoundaryScheme.outer_seam coreLayout (completedReading r tri) tri cyclic i

/-- Both chains use the same joint seam theorem as the larger patches. -/
theorem row_agrees (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) (p : Fin (s.degree i)) :
    vertex r (s.row i p.val) = (around r i p.val).snd :=
  FacialBoundaryScheme.row_agrees coreLayout (completedReading r tri) tri cyclic i p

theorem around_next (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) (p : Fin (s.degree i)) :
    rotation.vertexRotation (around r i p.val) = around r i (nextPos s i p).val := by
  rw [around_step]
  by_cases h : p.val + 1 < s.degree i
  · simp only [nextPos, FacialBoundaryScheme.nextPos, Nat.mod_eq_of_lt h]
  · have he : p.val + 1 = s.degree i := by omega
    simp only [nextPos, FacialBoundaryScheme.nextPos, he, Nat.mod_self]
    exact around_period r cyclic i

def hom (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic) : s.graph →g G :=
  FacialBoundaryScheme.hom coreLayout (completedReading r tri) tri cyclic

theorem full_turn (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) (p : Fin (s.degree i)) :
    Corner rotation (vertex r (i.natAdd ports)) (vertex r (s.row i p.val))
      (vertex r (s.row i (nextPos s i p).val)) :=
  FacialBoundaryScheme.full_turn coreLayout (completedReading r tri) tri cyclic i p

theorem around_injective (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (i : Fin 5) : Function.Injective (fun p : Fin (s.degree i) => (around r i p.val).snd) :=
  FacialBoundaryScheme.around_injective coreLayout (completedReading r tri) tri cyclic i

/-- Exterior identifications are permitted, but cannot capture an induced core. -/
theorem ring_outside_core (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (reflect : ∀ i j, G.Adj (r.map i) (r.map j) → core.Adj i j)
    (p : Fin ports) (j : Fin 5) : vertex r (p.castAdd 5) ≠ r.map j :=
  FacialBoundaryScheme.ring_outside_core coreLayout (completedReading r tri) tri cyclic reflect p j

end FourColor.FanBoundaryScheme
