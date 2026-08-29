import Mettapedia.GraphTheory.FourColor.GoertzelV24MeshIsoperimetry
import Mettapedia.GraphTheory.FourColor.GoertzelV24NormalizedTaitSupport

/-!
# A wall sweep is too short for the raw support pigeonhole

The later source route extracts a long hexagonal corridor and then applies a
finite-state pigeonhole argument to the cumulative boundary support.  A
two-dimensional wall is different from a tube: a bounded cut can move across
only quadratically many wall branch positions.

This file joins the two already checked quantitative statements at their
literal interface:

* a nested width-`k` mesh sweep which acquires a new branch position at every
  step has at most `2 * k^2 + 1` steps; and
* the canonical raw `k`-port Count receipt has exactly `2^(3^k)` states.

For `k >= 1` the first number is strictly smaller than the second.  Thus the
raw support pigeonhole cannot by itself force a repetition along a sweep which
genuinely traverses a wall.  The result does not exclude walls and does not say
that an optimized reachable quotient cannot repeat earlier.  It isolates the
precise failure of the unqualified inference from a long internal ladder path
to the ambient serial cut supply consumed by the descent.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24MeshSupportPigeonholeObstruction

open GoertzelV24GridIsoperimetry
open GoertzelV24BoundaryEssentialGluing
open GoertzelV24MeshIsoperimetry
open GoertzelV24NormalizedTaitSupport
open GoertzelV24RawNooseCountPumping

universe u

variable {Vtx Edg : Type*} [DecidableEq Vtx]
  [Fintype Edg] [DecidableEq Edg] [Nonempty Edg]

/-- A bounded nested sweep which acquires a new mesh branch position at every
step is strictly shorter than the canonical raw support carrier at the same
width.

This is a statement about what cardinality alone can force.  An actual early
state collision is compatible with the theorem, but cannot be deduced merely
from the number of sweep positions. -/
theorem chain_length_lt_card_normalizedSupportType
    {g : Multigraph Vtx Edg} {a b m k : Nat} (M : Mesh g a b)
    (hk : 1 <= k) (hka : k < a) (hkb : k < b)
    (Ss : Fin (m + 1) -> Finset Vtx)
    (hmono : forall i j, i < j -> M.branchIn (Ss i) ⊂ M.branchIn (Ss j))
    (hbd : forall j, (boundaryEdges g (Ss j)).card <= k) :
    m < Fintype.card
      (Finset (CutWord (StandardPort.{u} k))) := by
  have hchain : m <= 2 * (k * k) + 1 :=
    M.chain_length_le hka hkb Ss hmono hbd
  have hgap : 2 * (k * k) + 1 < 2 ^ (3 ^ k) :=
    two_mul_sq_add_one_lt_two_pow_three_pow hk
  rw [card_normalizedSupportType]
  omega

/-- Consequently, a mesh-traversing bounded sweep never meets the numerical
premise of the raw support pigeonhole theorem. -/
theorem not_card_normalizedSupportType_le_chain_length
    {g : Multigraph Vtx Edg} {a b m k : Nat} (M : Mesh g a b)
    (hk : 1 <= k) (hka : k < a) (hkb : k < b)
    (Ss : Fin (m + 1) -> Finset Vtx)
    (hmono : forall i j, i < j -> M.branchIn (Ss i) ⊂ M.branchIn (Ss j))
    (hbd : forall j, (boundaryEdges g (Ss j)).card <= k) :
    ¬ Fintype.card
      (Finset (CutWord (StandardPort.{u} k))) <= m := by
  exact Nat.not_le_of_lt
    (chain_length_lt_card_normalizedSupportType M hk hka hkb Ss hmono hbd)

/-! ## A bounded local cell cannot sweep across a large mesh -/

private theorem slab_arithmetic
    {previous next outside slab bound d total : Nat}
    (hprevious : previous <= bound)
    (houtside : outside <= bound)
    (hslab : slab <= d)
    (hstep : slab + previous = next)
    (hpartition : next + outside = total)
    (hlarge : 2 * bound + d < total) : False := by
  omega

/-- Any nested width-`k` sweep which starts on the small-inside side of a mesh
and finishes on the small-outside side has one consecutive slab containing
more than `d` newly acquired branch positions, provided the mesh has more than
`2*k^2+d` positions.

Unlike `chain_length_lt_card_normalizedSupportType`, this statement does not
require every step to acquire a branch position.  It says that a uniformly
local serial decomposition cannot cross a sufficiently large two-dimensional
mesh: somewhere it must make one nonlocal jump. -/
theorem exists_large_branch_slab_of_bounded_sweep
    {g : Multigraph Vtx Edg} {a b m k d : Nat} (M : Mesh g a b)
    (hka : k < a) (hkb : k < b)
    (Ss : Fin (m + 1) -> Finset Vtx)
    (hmono : forall i j, i < j -> M.branchIn (Ss i) ⊆ M.branchIn (Ss j))
    (hbd : forall j, (boundaryEdges g (Ss j)).card <= k)
    (hstart : (M.branchIn (Ss 0)).card <= k * k)
    (hend : (M.branchOut (Ss (Fin.last m))).card <= k * k)
    (hlarge : 2 * (k * k) + d < a * b) :
    exists i : Fin m,
      d < (M.branchIn (Ss i.succ) \
        M.branchIn (Ss i.castSucc)).card := by
  classical
  let final : Fin (m + 1) := Fin.last m
  let P : Nat -> Prop := fun index =>
    forall hindex : index < m + 1,
      (M.branchIn (Ss ⟨index, hindex⟩)).card <= k * k
  have hPzero : P 0 := by
    intro _hzero
    simpa using hstart
  have hPfinal : ¬ P m := by
    intro hsmall
    have hinside : (M.branchIn (Ss final)).card <= k * k := by
      exact hsmall (Nat.lt_succ_self m)
    have hpartition := M.card_branchIn_add_card_branchOut (Ss final)
    have houtside : (M.branchOut (Ss final)).card <= k * k := by
      simpa [final] using hend
    omega
  obtain ⟨index, hindex, hsmall, hnotsmall⟩ :=
    exists_change P m 0 hPzero (by simpa using hPfinal)
  have hindexPrevious : index < m + 1 :=
    Nat.lt_trans hindex (Nat.lt_succ_self m)
  have hindexNext : index + 1 < m + 1 := Nat.succ_lt_succ hindex
  let selected : Fin m := ⟨index, hindex⟩
  let previous : Fin (m + 1) := selected.castSucc
  let next : Fin (m + 1) := selected.succ
  have hsmall' : P index := by simpa using hsmall
  have hnotsmall' : ¬ P (index + 1) := by simpa [Nat.add_assoc] using hnotsmall
  have hprevious : (M.branchIn (Ss previous)).card <= k * k := by
    simpa [previous, selected] using hsmall' hindexPrevious
  have hnextNot : ¬ (M.branchIn (Ss next)).card <= k * k := by
    intro hnext
    apply hnotsmall'
    intro _hindexNext
    simpa [next, selected] using hnext
  have hout : (M.branchOut (Ss next)).card <= k * k := by
    rcases M.branchIn_card_le_or_branchOut_card_le
        (Ss next) hka hkb (hbd next) with hin | hout
    · exact (hnextNot hin).elim
    · exact hout
  have hsubset : M.branchIn (Ss previous) ⊆ M.branchIn (Ss next) := by
    apply hmono previous next
    simp [previous, next]
  refine ⟨selected, ?_⟩
  have hlargeSdiff :
      d < (M.branchIn (Ss next) \ M.branchIn (Ss previous)).card := by
    by_contra hnotlarge
    have hslab :
        (M.branchIn (Ss next) \ M.branchIn (Ss previous)).card <= d :=
      Nat.le_of_not_gt hnotlarge
    have hcard := Finset.card_sdiff_add_card_eq_card hsubset
    have hpartition := M.card_branchIn_add_card_branchOut (Ss next)
    exact slab_arithmetic hprevious hout hslab hcard hpartition hlarge
  exact hlargeSdiff

/-- Equivalently, if every consecutive slab of such a sweep contains at most
`d` new mesh branch positions, the sweep cannot run from one small side to the
other once `a*b > 2*k^2+d`. -/
theorem not_uniformly_local_bounded_sweep
    {g : Multigraph Vtx Edg} {a b m k d : Nat} (M : Mesh g a b)
    (hka : k < a) (hkb : k < b)
    (Ss : Fin (m + 1) -> Finset Vtx)
    (hmono : forall i j, i < j -> M.branchIn (Ss i) ⊆ M.branchIn (Ss j))
    (hbd : forall j, (boundaryEdges g (Ss j)).card <= k)
    (hstart : (M.branchIn (Ss 0)).card <= k * k)
    (hend : (M.branchOut (Ss (Fin.last m))).card <= k * k)
    (hlocal : forall i : Fin m,
      (M.branchIn (Ss i.succ) \
        M.branchIn (Ss i.castSucc)).card <= d)
    (hlarge : 2 * (k * k) + d < a * b) : False := by
  obtain ⟨i, hi⟩ := exists_large_branch_slab_of_bounded_sweep
    M hka hkb Ss hmono hbd hstart hend hlarge
  exact Nat.not_lt_of_ge (hlocal i) hi

end GoertzelV24MeshSupportPigeonholeObstruction

end Mettapedia.GraphTheory.FourColor
