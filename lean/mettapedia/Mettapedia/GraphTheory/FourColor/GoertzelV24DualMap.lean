import Mettapedia.GraphTheory.FourColor.GoertzelV24PermutationOrbitSurgery
import Mettapedia.GraphTheory.FourColor.GoertzelV24WordReachability
import Mettapedia.GraphTheory.FourColor.GoertzelV24BridgeTwoSided

/-!
# The dual map, as a change of generators

The dual is usually introduced by drawing a vertex inside each face and an
edge across each primal edge, which makes duality look like a statement about
embeddings.  At the level the reduction uses it, it is not: it is a one-line
change of generators.

For a map `(D, σ, α)` with face permutation `φ = σ * α`, the dual is
`(D, φ, α)`.  The darts and the edge flip are unchanged; only the vertex
rotation is replaced by the face permutation.  Everything below is the
displayed computation.

* The flip is literally the same permutation, so it is still a fixed-point-free
  involution and the dual is again a map.  Nothing is to be proved.
* The face permutation of the dual is `φ * α = σ * α * α = σ`.  So the faces of
  the dual are the vertices of the primal: `V* = F`, `E* = E`, `F* = V`.
* The generated subgroups agree, since `φ = σ * α` and `σ = φ * α`.  Hence the
  two maps have the same reachability relation on darts and the same number of
  components; one is connected exactly when the other is.
* `V* + F* = V + F` and `E* = E`, so the dual is spherical exactly when the map
  is.
* The dual of the dual is the map itself, on the nose: the dual of `(D, φ, α)`
  is `(D, φ * α, α) = (D, σ, α)`.  Duality here is an involution up to
  equality, not up to isomorphism, which is what makes it usable without
  transport lemmas.

No plane, curve, or face interior occurs anywhere in this module.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24DualMap

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24BridgeTwoSided
open GoertzelV24MapEulerBound
open GoertzelV24WordReachability

variable {D : Type*}

/-- The vertex rotation of the dual map: the face permutation of the original.
The dart set and the edge flip are unchanged, so the dual is `(D, φ, α)`. -/
def dualRotation (σ α : Perm D) : Perm D := σ * α

/-- **The face permutation of the dual is the vertex rotation of the
original.**  This single computation is both the count transfer `F* = V` and
the involutivity of duality. -/
theorem dualRotation_mul_flip {σ α : Perm D} (hinv : α * α = 1) :
    dualRotation σ α * α = σ := by
  rw [dualRotation, mul_assoc, hinv, mul_one]

/-- **Duality is an involution on the nose.**  The dual of `(D, φ, α)` is
`(D, φ * α, α) = (D, σ, α)`. -/
theorem dualRotation_dualRotation {σ α : Perm D} (hinv : α * α = 1) :
    dualRotation (dualRotation σ α) α = σ :=
  dualRotation_mul_flip hinv

section Counts

variable [Fintype D] [DecidableEq D]

/-- `V* = F`: the vertices of the dual are the faces of the original, by
definition of the dual rotation. -/
theorem orbitCount_dualRotation (σ α : Perm D) :
    orbitCount (dualRotation σ α) = orbitCount (σ * α) := rfl

/-- `F* = V`: the faces of the dual are the vertices of the original. -/
theorem orbitCount_dualRotation_mul_flip {σ α : Perm D} (hinv : α * α = 1) :
    orbitCount (dualRotation σ α * α) = orbitCount σ := by
  rw [dualRotation_mul_flip hinv]

/-- `V* + F* = V + F`, with `E* = E` holding because the flip is unchanged.
So the dual has the same Euler characteristic, and is spherical exactly when
the original is. -/
theorem orbitCount_dualRotation_add {σ α : Perm D} (hinv : α * α = 1) :
    orbitCount (dualRotation σ α) + orbitCount (dualRotation σ α * α) =
      orbitCount σ + orbitCount (σ * α) := by
  rw [orbitCount_dualRotation, orbitCount_dualRotation_mul_flip hinv,
    Nat.add_comm]

end Counts

/-! ## The generated subgroups agree -/

/-- A dual step is two primal steps: `φ u = σ (α u)`. -/
theorem wordReachable_dualRotation_step (σ α : Perm D) (u : D) :
    WordReachable [σ, α] u (dualRotation σ α u) := by
  refine (wordReachable_step (g := α) (by simp) u).trans ?_
  simpa [dualRotation, Equiv.Perm.mul_apply] using
    wordReachable_step (L := [σ, α]) (g := σ) (by simp) (α u)

/-- A primal rotation step is two dual steps: `σ u = φ (α u)`. -/
theorem wordReachable_rotation_step {σ α : Perm D} (hinv : α * α = 1) (u : D) :
    WordReachable [dualRotation σ α, α] u (σ u) := by
  refine (wordReachable_step (g := α) (by simp) u).trans ?_
  have hstep := wordReachable_step (L := [dualRotation σ α, α])
    (g := dualRotation σ α) (by simp) (α u)
  have hvalue : dualRotation σ α (α u) = σ u := by
    have hmul : dualRotation σ α * α = σ := dualRotation_mul_flip hinv
    calc dualRotation σ α (α u)
        = (dualRotation σ α * α) u := (Equiv.Perm.mul_apply _ _ _).symm
      _ = σ u := by rw [hmul]
  rwa [hvalue] at hstep

/-- **The dual has the same reachability relation on darts.**  Both
inclusions are the two displayed substitutions. -/
theorem wordReachable_dualRotation_iff {σ α : Perm D} (hinv : α * α = 1)
    (u v : D) :
    WordReachable [dualRotation σ α, α] u v ↔ WordReachable [σ, α] u v := by
  constructor
  · refine wordReachable_absorb ?_
    intro g hg w
    rcases List.mem_cons.1 hg with rfl | hg
    · exact wordReachable_dualRotation_step σ α w
    · rcases List.mem_cons.1 hg with rfl | hg
      · exact wordReachable_step (by simp) w
      · exact absurd hg (List.not_mem_nil)
  · refine wordReachable_absorb ?_
    intro g hg w
    rcases List.mem_cons.1 hg with rfl | hg
    · exact wordReachable_rotation_step hinv w
    · rcases List.mem_cons.1 hg with rfl | hg
      · exact wordReachable_step (by simp) w
      · exact absurd hg (List.not_mem_nil)

/-- **The dual has the same number of components.**  In particular one map is
connected exactly when the other is. -/
theorem wordOrbitCount_dualRotation [Fintype D] {σ α : Perm D}
    (hinv : α * α = 1) :
    wordOrbitCount [dualRotation σ α, α] = wordOrbitCount [σ, α] := by
  refine Nat.le_antisymm ?_ ?_
  · exact wordOrbitCount_le_of_le
      (fun u v huv => (wordReachable_dualRotation_iff hinv u v).2 huv)
  · exact wordOrbitCount_le_of_le
      (fun u v huv => (wordReachable_dualRotation_iff hinv u v).1 huv)

/-! ## Loops and bridges exchange

The bridge characterisation is stated for a rotation together with an edge
list, the edge under scrutiny sitting at the head.  Applying it to the dual is
therefore literally substituting the dual rotation for the rotation: the dual's
own face permutation is then `φ * α = σ`, so "the two darts lie on a common
face of the dual" is "the two darts lie at a common vertex of the original",
which is what it means for the edge to be a loop.

The sphericity hypothesis is unchanged under the substitution, since it is the
same sum with its two summands exchanged. -/

section LoopBridge

variable [Fintype D] [DecidableEq D]

/-- **A loop of the map is a bridge of the dual.**  The hypothesis `hloop`
says the two darts of the edge lie at one vertex. -/
theorem two_le_wordOrbitCount_dual_of_loop
    (σ α : Perm D) {a b : D} (rest : List (D × D)) (hab : a ≠ b)
    (hflip : α = Equiv.swap a b * swapProduct rest)
    (hinv : α * α = 1)
    (hfixa : swapProduct rest a = a) (hfixb : swapProduct rest b = b)
    (hrest : ∀ edge ∈ rest, edge.1 ≠ edge.2)
    (hsphere : orbitCount σ + orbitCount (σ * α) = rest.length + 3)
    (hloop : σ.SameCycle a b) :
    2 ≤ wordOrbitCount (dualRotation σ α :: swapGenerators rest) := by
  have hcollapse : σ * α * α = σ := by rw [mul_assoc, hinv, mul_one]
  refine two_le_components_of_sameCycle (σ * α) rest hab hfixa hfixb hrest
    ?_ ?_
  · rw [← hflip, hcollapse]
    omega
  · rw [← hflip, hcollapse]
    exact hloop

/-- **A bridge of the dual is a loop of the map.**  This is the converse
direction of the bridge characterisation, read at the dual rotation. -/
theorem sameCycle_of_not_wordReachable_dual
    (σ α : Perm D) {a b : D} (rest : List (D × D))
    (hflip : α = Equiv.swap a b * swapProduct rest)
    (hinv : α * α = 1)
    (hfixa : swapProduct rest a = a) (hfixb : swapProduct rest b = b)
    (hbridge :
      ¬ WordReachable (dualRotation σ α :: swapGenerators rest) a b) :
    σ.SameCycle a b := by
  have hcollapse : σ * α * α = σ := by rw [mul_assoc, hinv, mul_one]
  have hsame :=
    sameCycle_of_not_wordReachable (σ * α) rest hfixa hfixb hbridge
  rwa [← hflip, hcollapse] at hsame

/-- **The dual of a loopless map is bridgeless.**  Contrapositive of the
previous theorem: if the two darts of the edge do not lie at one vertex, then
they remain connected after the edge is scrutinised in the dual. -/
theorem wordReachable_dual_of_not_loop
    (σ α : Perm D) {a b : D} (rest : List (D × D))
    (hflip : α = Equiv.swap a b * swapProduct rest)
    (hinv : α * α = 1)
    (hfixa : swapProduct rest a = a) (hfixb : swapProduct rest b = b)
    (hloopless : ¬ σ.SameCycle a b) :
    WordReachable (dualRotation σ α :: swapGenerators rest) a b := by
  by_contra hbridge
  exact hloopless
    (sameCycle_of_not_wordReachable_dual σ α rest hflip hinv hfixa hfixb
      hbridge)

end LoopBridge

end GoertzelV24DualMap

end Mettapedia.GraphTheory.FourColor
