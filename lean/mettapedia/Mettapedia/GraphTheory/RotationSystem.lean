import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Tactic.Linarith
import Mettapedia.GroupTheory.Perm.CycleCount

/-!
# Rotation systems of simple graphs and their Euler characteristic

A rotation system of a simple graph orders the darts leaving each vertex cyclically.  It
is given here by one permutation `rotation` of the darts that keeps the tail of every dart
and runs through all the darts at a vertex in one cycle.  Crossing an edge to the reversed
dart and then turning once around its tail follows the boundary of a face: the faces are
the cycles of `facePerm = rotation * dartReverse`.

A rotation system of a connected graph describes a cellular embedding of the graph in an
orientable closed surface, whose Euler characteristic is `V - E + F`; the surface is the
sphere, i.e. the graph is drawn in the plane, exactly when this number is `2`
(Heffter–Edmonds–Ringel).  That correspondence with topological surfaces is not
formalized here: `IsSpherical` is its combinatorial side, a checkable certificate of
planarity.

For a cubic graph a spherical rotation system satisfies the curvature identity
`∑ (6 - |f|) = 12` over its faces (`sum_six_sub_faceLength`); in particular a cubic plane
map whose faces all have at least five sides has `12 + ∑_{k ≥ 7} (k - 6) p_k` pentagons.
Face counts of concrete rotation systems are decided through
`Equiv.Perm.cycleCount` (`faceCount_eq_cycleCount`).
-/

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- Reversal of darts, as a permutation of the darts. -/
def dartReverse : Equiv.Perm G.Dart :=
  ⟨Dart.symm, Dart.symm, Dart.symm_involutive, Dart.symm_involutive⟩

@[simp] theorem dartReverse_apply (d : G.Dart) : dartReverse d = d.symm := rfl

variable (G) in
/-- A rotation system of `G`: a cyclic order of the darts at each vertex, given by the
permutation sending a dart to the next dart around its tail. -/
structure RotationSystem where
  /-- The next dart around the common tail. -/
  rotation : Equiv.Perm G.Dart
  fst_rotation : ∀ d, (rotation d).fst = d.fst
  sameCycle_of_fst_eq : ∀ d d', d.fst = d'.fst → rotation.SameCycle d d'

namespace RotationSystem

variable (R : G.RotationSystem)

/-- The face permutation: cross the edge to the reversed dart, then turn once around its
tail.  Its cycles are the faces. -/
def facePerm : Equiv.Perm G.Dart :=
  R.rotation * dartReverse

theorem facePerm_apply (d : G.Dart) : R.facePerm d = R.rotation d.symm := rfl

/-- The face permutation moves every dart: a face of a simple graph is never a single
dart. -/
theorem facePerm_apply_ne (d : G.Dart) : R.facePerm d ≠ d := by
  intro h
  have h₁ := congrArg (fun d : G.Dart => d.fst) h
  simp only [facePerm_apply, R.fst_rotation] at h₁
  exact G.ne_of_adj d.adj (by simpa using h₁.symm)

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The number of faces: the number of cycles of the face permutation. -/
def faceCount : ℕ :=
  R.facePerm.partition.parts.card

/-- The Euler characteristic `V - E + F`. -/
def eulerChar : ℤ :=
  Fintype.card V - G.edgeFinset.card + R.faceCount

/-- A rotation system is spherical when its Euler characteristic is `2`: for a connected
graph it describes a drawing in the plane. -/
def IsSpherical : Prop :=
  R.eulerChar = 2

instance : Decidable R.IsSpherical := by
  unfold IsSpherical
  infer_instance

/-- Face counts are decided by counting cycle minima. -/
theorem faceCount_eq_cycleCount {idx : G.Dart → ℕ} (hidx : Function.Injective idx) :
    R.faceCount = Equiv.Perm.cycleCount idx R.facePerm :=
  (Equiv.Perm.cycleCount_eq_card_parts hidx).symm

/-- The face lengths add up to the number of darts. -/
theorem sum_faceLength : R.facePerm.partition.parts.sum = 2 * G.edgeFinset.card := by
  rw [Nat.Partition.parts_sum, dart_card_eq_twice_card_edges]

/-- **The curvature identity.**  In a spherical rotation system of a cubic graph the
faces satisfy `∑ (6 - |f|) = 12`. -/
theorem sum_six_sub_faceLength (h3 : G.IsRegularOfDegree 3) (hR : R.IsSpherical) :
    (R.facePerm.partition.parts.map fun p : ℕ => (6 - p : ℤ)).sum = 12 := by
  have hdeg : 3 * Fintype.card V = 2 * G.edgeFinset.card := by
    rw [← sum_degrees_eq_twice_card_edges, Finset.sum_congr rfl fun v _ => h3 v,
      Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm]
  have hsum : (R.facePerm.partition.parts.map fun p : ℕ => (p : ℤ)).sum =
      2 * G.edgeFinset.card := by
    rw [← Nat.cast_multiset_sum, R.sum_faceLength]
    push_cast
    ring
  rw [Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, hsum, nsmul_eq_mul]
  have hχ := hR
  unfold IsSpherical eulerChar faceCount at hχ
  have hdeg' : (3 * Fintype.card V : ℤ) = 2 * G.edgeFinset.card := by exact_mod_cast hdeg
  linarith

end RotationSystem

end SimpleGraph
