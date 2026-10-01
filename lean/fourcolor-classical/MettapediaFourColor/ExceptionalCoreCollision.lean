import MettapediaFourColor.ExceptionalCoreLocalInjectivity

/-!
# Core injectivity or an actual nonfacial triangle

Local injectivity leaves four possible unordered collisions in the D1774
core. Each closes a three-edge path. The retained source rotation at vertex
4 excludes both facial orientations of the resulting triangle. This yields
an explicit geometric alternative to injectivity, without assuming that a
nonfacial triangle already supplies a separator or a colouring reduction.
-/

namespace FourColor.ExceptionalCoreCollision

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalPattern ExceptionalOverlap ExceptionalCore ExceptionalCoreOrientation
open ExceptionalCoreLocalInjectivity

set_option maxRecDepth 32768

variable {V : Type*} {G : SimpleGraph V} {rotation : Data G}

theorem corner_right_unique {a b c d : V}
    (h : Corner rotation a b c) (k : Corner rotation a b d) : c = d := by
  obtain ⟨hab, hac, h⟩ := h
  obtain ⟨_, had, k⟩ := k
  exact congrArg (fun e : G.Dart => e.snd) (h.symm.trans k)

theorem corner_left_unique {a b c d : V}
    (h : Corner rotation a b c) (k : Corner rotation a d c) : b = d := by
  obtain ⟨hab, hac, h⟩ := h
  obtain ⟨had, _, k⟩ := k
  exact congrArg (fun e : G.Dart => e.snd)
    (rotation.vertexRotation.injective (h.trans k.symm))

/-- Three actual edges exclude repeated vertices in a simple graph. Neither
orientation is a facial corner at the specified vertex. -/
structure NonfacialTriangle (rotation : Data G) (a b c : V) : Prop where
  ab : G.Adj a b
  bc : G.Adj b c
  ca : G.Adj c a
  forward : ¬ Corner rotation a b c
  backward : ¬ Corner rotation a c b

def NonfacialTriangle.walk {a b c : V} (h : NonfacialTriangle rotation a b c) :
    G.Walk a a := .cons h.ab (.cons h.bc (.cons h.ca .nil))

theorem NonfacialTriangle.walk_length {a b c : V}
    (h : NonfacialTriangle rotation a b c) : h.walk.length = 3 := rfl

theorem NonfacialTriangle.walk_isCycle {a b c : V}
    (h : NonfacialTriangle rotation a b c) : h.walk.IsCycle := by
  rw [SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length]
  constructor
  · simp [walk, SimpleGraph.Walk.isPath_def, h.ab.ne, h.bc.ne, h.ca.ne,
      Ne.symm h.ab.ne, Ne.symm h.bc.ne, Ne.symm h.ca.ne]
  · exact Nat.le_refl 3

/-- A triangle through an edge is nonfacial when its third vertex differs
from both neighbours flanking that edge in the actual rotation. -/
theorem nonfacial_of_flanks {a b c l r : V}
    (ab : G.Adj a b) (bc : G.Adj b c) (ca : G.Adj c a)
    (left : Corner rotation a l b) (right : Corner rotation a b r)
    (cl : c ≠ l) (cr : c ≠ r) : NonfacialTriangle rotation a b c := by
  refine ⟨ab, bc, ca, ?_, ?_⟩
  · intro h; exact cr (corner_right_unique h right)
  · intro h; exact cl (corner_left_unique h left)

variable [G.LocallyFinite]

theorem source_corner (x : Occurrence rotation) (i j k : Fin 17)
    (hij : ExceptionalPattern.graph.Adj i j)
    (hik : ExceptionalPattern.graph.Adj i k) (h : Turn i j k) :
    Corner rotation (x.vertex i) (x.vertex j) (x.vertex k) :=
  ⟨x.edge i j hij, x.edge i k hik, x.turn i j k hij hik h⟩

/-- Only these four unordered pairs can escape adjacency and local
injectivity. This checks the decoded graph, not an approximate shape. -/
def CollisionPair (i j : Fin 8) : Prop :=
  (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 5) ∨
    (i = 1 ∧ j = 7) ∨ (i = 2 ∧ j = 4)

instance (i j : Fin 8) : Decidable (CollisionPair i j) := by
  unfold CollisionPair; infer_instance

theorem collision_partition : ∀ i j : Fin 8, i ≠ j →
    core.Adj i j ∨ (∃ k, core.Adj k i ∧ core.Adj k j) ∨
      CollisionPair i j ∨ CollisionPair j i := by decide +kernel

variable (r : JointReading rotation)

/-- A collided length-three path gives three actual ambient edges. -/
theorem collision_triangle {i a b j : Fin 8}
    (ia : core.Adj i a) (ab : core.Adj a b) (bj : core.Adj b j)
    (eq : r.core.map i = r.core.map j) :
    G.Adj (r.core.map a) (r.core.map b) ∧
      G.Adj (r.core.map b) (r.core.map i) ∧
      G.Adj (r.core.map i) (r.core.map a) := by
  refine ⟨r.core.map.map_adj ab, ?_, r.core.map.map_adj ia⟩
  rw [eq]
  exact r.core.map.map_adj bj

/-- Three collision cases use the same central edge and degree argument.
Its two facial third vertices both have degree eight, whereas the collided
endpoint has degree five. -/
theorem central_collision {i j : Fin 8}
    (i6 : core.Adj i 6) (j3 : core.Adj 3 j) (deg : coreDegree i = 5)
    (eq : r.core.map i = r.core.map j) :
    NonfacialTriangle rotation (r.first.vertex 4) (r.first.vertex 5)
      (r.core.map i) := by
  obtain ⟨ab, bc, ca⟩ := collision_triangle r i6 (by decide +kernel) j3 eq
  have ea : r.core.map 6 = r.first.vertex 4 := r.realizes 6
  have eb : r.core.map 3 = r.first.vertex 5 := r.realizes 3
  simp only [ea, eb] at ab bc ca
  apply nonfacial_of_flanks ab bc ca
    (source_corner r.first 4 14 5 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (source_corner r.first 4 5 0 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
  · intro h
    have hd := congrArg (fun v => G.degree v) h
    rw [r.core.degree, deg, r.first.degree] at hd
    exact (by decide +kernel : (5 : ℕ) ≠ prescribed 14) hd
  · intro h
    have hd := congrArg (fun v => G.degree v) h
    rw [r.core.degree, deg, r.first.degree] at hd
    exact (by decide +kernel : (5 : ℕ) ≠ prescribed 0) hd

/-- The fourth case uses the other central edge. One excluded facial
corner has the wrong degree; the other is adjacent to the collided vertex. -/
theorem closing_collision (eq : r.core.map 1 = r.core.map 7) :
    NonfacialTriangle rotation (r.first.vertex 4) (r.first.vertex 14)
      (r.first.vertex 3) := by
  obtain ⟨ab, bc, ca⟩ := collision_triangle r
    (show core.Adj 1 6 by decide +kernel)
    (show core.Adj 6 0 by decide +kernel)
    (show core.Adj 0 7 by decide +kernel) eq
  have ea : r.core.map 6 = r.first.vertex 4 := r.realizes 6
  have eb : r.core.map 0 = r.first.vertex 14 := r.realizes 0
  have ec : r.core.map 1 = r.first.vertex 3 := r.realizes 1
  simp only [ea, eb, ec] at ab bc ca
  apply nonfacial_of_flanks ab bc ca
    (source_corner r.first 4 13 14 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
    (source_corner r.first 4 14 5 (by decide +kernel) (by decide +kernel)
      (by decide +kernel))
  · intro h
    have adj := r.first.edge 3 13 (by decide +kernel)
    rw [h] at adj
    exact G.irrefl adj
  · intro h
    have hd := congrArg (fun v => G.degree v) h
    rw [r.first.degree, r.first.degree] at hd
    exact (by decide +kernel : prescribed 3 ≠ prescribed 5) hd

/-- Every residual pair produces a triangle whose three vertices are
retained source observations, rather than anonymous vertices of a sketch. -/
theorem pair_nonfacial {i j : Fin 8} (pair : CollisionPair i j)
    (eq : r.core.map i = r.core.map j) :
    ∃ a b c : Fin 17, NonfacialTriangle rotation
      (r.first.vertex a) (r.first.vertex b) (r.first.vertex c) := by
  rcases pair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨4, 5, 3, ?_⟩
    have h := central_collision r (by decide +kernel) (by decide +kernel)
      (by decide +kernel) eq
    have ec : r.core.map 1 = r.first.vertex 3 := r.realizes 1
    rwa [ec] at h
  · refine ⟨4, 5, 3, ?_⟩
    have h := central_collision r (by decide +kernel) (by decide +kernel)
      (by decide +kernel) eq
    have ec : r.core.map 1 = r.first.vertex 3 := r.realizes 1
    rwa [ec] at h
  · exact ⟨4, 14, 3, closing_collision r eq⟩
  · refine ⟨4, 5, 13, ?_⟩
    have h := central_collision r (by decide +kernel) (by decide +kernel)
      (by decide +kernel) eq.symm
    have ec : r.core.map 4 = r.first.vertex 13 := r.realizes 4
    rwa [ec] at h

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

theorem collision_nonfacial (tri : Triangular rotation)
    (cyclic : rotation.IsVertexwiseCyclic) {i j : Fin 8} (ne : i ≠ j)
    (eq : r.core.map i = r.core.map j) :
    ∃ a b c : Fin 17, NonfacialTriangle rotation
      (r.first.vertex a) (r.first.vertex b) (r.first.vertex c) := by
  rcases collision_partition i j ne with adj | ⟨k, hi, hj⟩ | pair | pair
  · have h := r.core.map.map_adj adj
    rw [eq] at h
    exact (G.irrefl h).elim
  · exact (ne (joint_neighbor_injective r tri cyclic k i j hi hj eq)).elim
  · exact pair_nonfacial r pair eq
  · exact pair_nonfacial r pair eq.symm

/-- The two checked outcomes retain the same joint reading. The first is
core injectivity, not yet an induced occurrence with a completed ring. The
second is a nonfacial triangle, not yet a certified colouring reduction. -/
theorem injective_or_nonfacial (tri : Triangular rotation)
    (cyclic : rotation.IsVertexwiseCyclic) :
    Function.Injective r.core.map ∨
      ∃ a b c : Fin 17, NonfacialTriangle rotation
        (r.first.vertex a) (r.first.vertex b) (r.first.vertex c) := by
  classical
  by_cases h : Function.Injective r.core.map
  · exact Or.inl h
  · right
    simp only [Function.Injective, not_forall] at h
    obtain ⟨i, j, eq, ne⟩ := h
    exact collision_nonfacial r tri cyclic ne eq

/-- On a domain where all local triangles are facial, the exact core
reading is injective. This hypothesis must be justified geometrically. -/
theorem injective_of_local_triangles_facial (tri : Triangular rotation)
    (cyclic : rotation.IsVertexwiseCyclic)
    (facial : ∀ a b c : Fin 17,
      G.Adj (r.first.vertex a) (r.first.vertex b) →
      G.Adj (r.first.vertex b) (r.first.vertex c) →
      G.Adj (r.first.vertex c) (r.first.vertex a) →
      Corner rotation (r.first.vertex a) (r.first.vertex b) (r.first.vertex c) ∨
      Corner rotation (r.first.vertex a) (r.first.vertex c) (r.first.vertex b)) :
    Function.Injective r.core.map := by
  rcases injective_or_nonfacial r tri cyclic with h | ⟨a, b, c, h⟩
  · exact h
  · rcases facial a b c h.ab h.bc h.ca with hf | hb
    · exact (h.forward hf).elim
    · exact (h.backward hb).elim

/-- Actual source consumer: both aligned exceptional occurrences construct
the reading used above. Every vertex in the collision outcome is within
radius two of the original centre. -/
theorem source_core_alternative (x : Occurrence rotation)
    (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)
    (y : Occurrence rotation) (aligned : y.vertex 0 = x.vertex 14) :
    Function.Injective (coreHom x tri) ∨
      ∃ a b c : V, NonfacialTriangle rotation a b c ∧
        a ∈ LocalCoverageAssembly.closedBall G (x.vertex 0) 2 ∧
        b ∈ LocalCoverageAssembly.closedBall G (x.vertex 0) 2 ∧
        c ∈ LocalCoverageAssembly.closedBall G (x.vertex 0) 2 := by
  rcases injective_or_nonfacial (jointReading x tri cyclic y aligned) tri cyclic with
    h | ⟨a, b, c, h⟩
  · exact Or.inl h
  · exact Or.inr ⟨x.vertex a, x.vertex b, x.vertex c, h,
      x.vertex_near a, x.vertex_near b, x.vertex_near c⟩

end FourColor.ExceptionalCoreCollision
