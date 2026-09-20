import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkFaceOrderObstruction
import Mettapedia.GraphTheory.FourColor.MarkedFaceReturnRewire
import Mettapedia.GraphTheory.FourColor.PermutationFirstReturnRestriction
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitCountCongr

/-!
# A face-return coordinate for a physical edge fork

Scalar face counts cannot compose over a branch fork, even on the tetrahedron.
The first-return permutation on named interface darts retains the missing
cyclic order. Here an edge-leaf fork has an exact transition when the new edge
joins two marked darts: it swaps those marks in the old return permutation.
Restriction to a smaller mark set then forgets vertices internalized by the
fork, by `PermutationFirstReturnRestriction.nextHit_nested`.

This is an exact transition for an edge-leaf fork, not yet a transition for an
arbitrary binary fork of two nontrivial edge subtrees. The latter needs a
gluing law for two child return records, with coherent names for their shared
interface. The K4 control below shows that the return coordinate genuinely
distinguishes the two rotations that scalar child defects fail to distinguish.
-/

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24ForkFaceReturn

open Equiv Equiv.Perm
open GoertzelV24MapEulerBound
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24WordReachability
open GoertzelV24OrbitCountCongr
open GoertzelV24ForkFaceOrderObstruction
open GoertzelV24ForkInterfaceSupport
open GoertzelV24V23ZeroContractionCrossing
open GoertzelV24ConnectedBranchDecompositionForest

noncomputable section
attribute [local instance] Classical.propDecidable

variable {D : Type*} [Fintype D] [DecidableEq D]

/-- The new physical edge uses neither dart of any edge already present.
This is the disjointness condition on a duplicate-free edge presentation,
stated at the dart level where swap commutation is actually valid. -/
def FreshEdge (edge : D × D) (rest : List (D × D)) : Prop :=
  ∀ other ∈ rest,
    edge.1 ≠ other.1 ∧ edge.1 ≠ other.2 ∧
      edge.2 ≠ other.1 ∧ edge.2 ≠ other.2

omit [Fintype D] in
/-- Fresh physical edges commute with the product of previous edge flips.
The fork transition therefore needs no independent commutation assumption
when its edge list really presents distinct graph edges. -/
theorem swap_commutes_swapProduct_of_fresh
    (edge : D × D) (rest : List (D × D))
    (hfresh : FreshEdge edge rest) :
    Equiv.swap edge.1 edge.2 * swapProduct rest =
      swapProduct rest * Equiv.swap edge.1 edge.2 := by
  induction rest with
  | nil => simp [swapProduct]
  | cons other tail ih =>
      have hpair := hfresh other (List.mem_cons_self)
      have htail : FreshEdge edge tail := by
        intro e he
        exact hfresh e (List.mem_cons_of_mem _ he)
      simp only [swapProduct_cons]
      calc
        Equiv.swap edge.1 edge.2 *
            (Equiv.swap other.1 other.2 * swapProduct tail) =
          Equiv.swap other.1 other.2 *
            (Equiv.swap edge.1 edge.2 * swapProduct tail) := by
              rw [← mul_assoc, swap_mul_swap_comm hpair.1 hpair.2.1
                hpair.2.2.1 hpair.2.2.2, mul_assoc]
        _ = (Equiv.swap other.1 other.2 * swapProduct tail) *
            Equiv.swap edge.1 edge.2 := by rw [ih htail, mul_assoc]

/-- Exact face-return update when prepending a physical edge whose two darts
are among the marked boundary darts. The commutation hypothesis is automatic
for a duplicate-free physical edge list, whose transpositions have disjoint
supports. It is stated explicitly so overlapping abstract edge words are not
silently treated as physical ones. -/
theorem nextHitPerm_cons_of_commuting_swap
    (rho : Perm D) (edge : D × D) (rest : List (D × D))
    (hit : D → Prop) (ha : hit edge.1) (hb : hit edge.2)
    (hcomm : Equiv.swap edge.1 edge.2 * swapProduct rest =
      swapProduct rest * Equiv.swap edge.1 edge.2) :
    nextHitPerm (rho * swapProduct (edge :: rest)) hit =
      nextHitPerm (rho * swapProduct rest) hit *
        Equiv.swap (⟨edge.1, ha⟩ : {d // hit d}) ⟨edge.2, hb⟩ := by
  classical
  have hface : rho * swapProduct (edge :: rest) =
      (rho * swapProduct rest) * Equiv.swap edge.1 edge.2 := by
    rw [swapProduct_cons, hcomm, mul_assoc]
  rw [hface]
  have hswap : Equiv.swap edge.1 edge.2 =
      Equiv.Perm.ofSubtype
        (Equiv.swap (⟨edge.1, ha⟩ : {d // hit d}) ⟨edge.2, hb⟩) := by
    exact (Equiv.Perm.ofSubtype_swap_eq
      (⟨edge.1, ha⟩ : {d // hit d}) ⟨edge.2, hb⟩).symm
  rw [hswap]
  exact MarkedFaceReturnRewire.nextHitPerm_rewire
    (rho * swapProduct rest) hit
    (Equiv.swap (⟨edge.1, ha⟩ : {d // hit d}) ⟨edge.2, hb⟩)

/-- Exact face-return update for a genuinely fresh edge, with no caller-
supplied commutation equation. -/
theorem nextHitPerm_cons_of_fresh
    (rho : Perm D) (edge : D × D) (rest : List (D × D))
    (hit : D → Prop) (ha : hit edge.1) (hb : hit edge.2)
    (hfresh : FreshEdge edge rest) :
    nextHitPerm (rho * swapProduct (edge :: rest)) hit =
      nextHitPerm (rho * swapProduct rest) hit *
        Equiv.swap (⟨edge.1, ha⟩ : {d // hit d}) ⟨edge.2, hb⟩ := by
  exact nextHitPerm_cons_of_commuting_swap rho edge rest hit ha hb
    (swap_commutes_swapProduct_of_fresh edge rest hfresh)

/-- The finite edge-fork operation followed by lossless internalization of
boundary marks. `big` names the old boundary, `small` the parent boundary.
The nested restriction is essential: simply dropping the forgotten darts
from the old permutation need not preserve a face's next boundary visit. -/
theorem nextHitPerm_cons_project
    (rho : Perm D) (edge : D × D) (rest : List (D × D))
    (big small : D → Prop) (hsub : ∀ d, small d → big d)
    (ha : big edge.1) (hb : big edge.2)
    (hcomm : Equiv.swap edge.1 edge.2 * swapProduct rest =
      swapProduct rest * Equiv.swap edge.1 edge.2) :
    nextHitPerm
      (nextHitPerm (rho * swapProduct rest) big *
        Equiv.swap (⟨edge.1, ha⟩ : {d // big d}) ⟨edge.2, hb⟩)
      (fun d => small d.1) =
    (PermutationFirstReturnRestriction.nestedMarks small big hsub).permCongr
      (nextHitPerm (rho * swapProduct (edge :: rest)) small) := by
  classical
  rw [← nextHitPerm_cons_of_commuting_swap rho edge rest big ha hb hcomm]
  exact PermutationFirstReturnRestriction.nextHit_nested
    (rho * swapProduct (edge :: rest)) small big hsub

/-- A physical edge-leaf fork can first update the child face-return order and
then forget marks internal to the parent. Distinct edges make the needed
commutation automatic. -/
theorem nextHitPerm_cons_project_of_fresh
    (rho : Perm D) (edge : D × D) (rest : List (D × D))
    (big small : D → Prop) (hsub : ∀ d, small d → big d)
    (ha : big edge.1) (hb : big edge.2)
    (hfresh : FreshEdge edge rest) :
    nextHitPerm
      (nextHitPerm (rho * swapProduct rest) big *
        Equiv.swap (⟨edge.1, ha⟩ : {d // big d}) ⟨edge.2, hb⟩)
      (fun d => small d.1) =
    (PermutationFirstReturnRestriction.nestedMarks small big hsub).permCongr
      (nextHitPerm (rho * swapProduct (edge :: rest)) small) := by
  exact nextHitPerm_cons_project rho edge rest big small hsub ha hb
    (swap_commutes_swapProduct_of_fresh edge rest hfresh)

/-- The handle test for a new edge reads its cofaciality from the finite
return permutation, provided the two queried face positions are marked. This
is the precise structural input to `MapEulerDefect.defect_cons`. -/
theorem createsHandle_iff_return_different_face
    (rho : Perm D) (edge : D × D) (rest : List (D × D))
    (hit : D → Prop) (ha : hit (rho edge.1)) (hb : hit (rho edge.2)) :
    MapEulerDefect.CreatesHandle rho edge rest ↔
      WordReachable (rho :: swapGenerators rest) edge.1 edge.2 ∧
        ¬ (nextHitPerm (rho * swapProduct rest) hit).SameCycle
          (⟨rho edge.1, ha⟩ : {d // hit d}) ⟨rho edge.2, hb⟩ := by
  classical
  unfold MapEulerDefect.CreatesHandle
  rw [nextHitPerm_sameCycle_iff]

/-- In an edge-leaf fork, the scalar Euler defect increment is determined
exactly by component connectivity and the child return record. This is a
consumer of the return coordinate, not an independent Euler formula. -/
theorem defect_cons_via_return
    (rho : Perm D) (edge : D × D) (rest : List (D × D))
    (hit : D → Prop) (ha : hit (rho edge.1)) (hb : hit (rho edge.2))
    (hne : edge.1 ≠ edge.2) :
    MapEulerDefect.defect rho (edge :: rest) =
      MapEulerDefect.defect rho rest +
        if WordReachable (rho :: swapGenerators rest) edge.1 edge.2 ∧
          ¬ (nextHitPerm (rho * swapProduct rest) hit).SameCycle
            (⟨rho edge.1, ha⟩ : {d // hit d}) ⟨rho edge.2, hb⟩
        then 2 else 0 := by
  classical
  rw [MapEulerDefect.defect_cons rho edge rest hne]
  by_cases hc : MapEulerDefect.CreatesHandle rho edge rest
  · have hs := (createsHandle_iff_return_different_face
      rho edge rest hit ha hb).mp hc
    simp [hc, hs]
  · have hs : ¬ (WordReachable (rho :: swapGenerators rest) edge.1 edge.2 ∧
        ¬ (nextHitPerm (rho * swapProduct rest) hit).SameCycle
          (⟨rho edge.1, ha⟩ : {d // hit d}) ⟨rho edge.2, hb⟩) :=
      fun h => hc ((createsHandle_iff_return_different_face
        rho edge rest hit ha hb).mpr h)
    simp [hc, hs]

end

/-! ## A physical edge-leaf fork on K4 -/

/-- A two-level real edge-leaf fork: the left spanning tree, then `ac`,
then `bc`. The `bc` step is the first one whose face behaviour distinguishes
the two rotations. -/
def tetraAfterAc : EdgeLeafTree TetraEdge :=
  .fork (.leaf .ac) leftTree

def tetraAfterBc : EdgeLeafTree TetraEdge :=
  .fork (.leaf .bc) tetraAfterAc

theorem tetraAfterAc_word :
    edgeWord tetraAfterAc = edgeDarts .ac :: edgeWord leftTree := rfl

theorem tetraAfterBc_word :
    edgeWord tetraAfterBc = edgeDarts .bc :: edgeWord tetraAfterAc := rfl

/-- Exact middle-vertex marks for the intermediate piece. Vertex `a` has
become internal, whereas `b`, `c`, and `d` still meet the complement. -/
def tetraHitAfterAc (dart : TetraDart) : Prop :=
  tetraVertOf dart ∈ mid tetraEndpoints tetraAfterAc.shore

theorem tetraHitAfterAc_iff (dart : TetraDart) :
    tetraHitAfterAc dart ↔ tetraVertOf dart ≠ TetraVertex.a := by
  cases dart <;>
    simp [tetraHitAfterAc, mid, tetraAfterAc, leftTree, EdgeLeafTree.shore,
      EdgeLeafTree.leafList, tetraEndpoints, tetraVertOf] <;>
    decide +kernel

theorem tetraHit_bcB : tetraHitAfterAc (tetraRho TetraDart.bcB) := by
  rw [tetraHitAfterAc_iff]
  decide +kernel

theorem tetraHit_bcC : tetraHitAfterAc (tetraRho TetraDart.bcC) := by
  rw [tetraHitAfterAc_iff]
  decide +kernel

def tetraHitAfterBc (dart : TetraDart) : Prop :=
  tetraVertOf dart ∈ mid tetraEndpoints tetraAfterBc.shore

theorem tetraHitAfterBc_iff (dart : TetraDart) :
    tetraHitAfterBc dart ↔
      tetraVertOf dart = TetraVertex.b ∨ tetraVertOf dart = TetraVertex.d := by
  cases dart <;>
    simp [tetraHitAfterBc, mid, tetraAfterBc, tetraAfterAc, leftTree,
      EdgeLeafTree.shore, EdgeLeafTree.leafList, tetraEndpoints, tetraVertOf] <;>
    decide +kernel

theorem tetraHitAfterBc_sub (dart : TetraDart) :
    tetraHitAfterBc dart → tetraHitAfterAc dart := by
  cases dart <;>
    simp [tetraHitAfterBc_iff, tetraHitAfterAc_iff, tetraVertOf]

theorem tetraHit_bcB_dart : tetraHitAfterAc TetraDart.bcB := by
  rw [tetraHitAfterAc_iff]
  decide +kernel

theorem tetraHit_bcC_dart : tetraHitAfterAc TetraDart.bcC := by
  rw [tetraHitAfterAc_iff]
  decide +kernel

/-- The final `bc` edge is new as a pair of physical darts, not just a
different edge name. -/
theorem tetra_bc_fresh :
    FreshEdge (edgeDarts .bc) (edgeWord tetraAfterAc) := by
  simp [FreshEdge, edgeWord, tetraAfterAc, leftTree,
    EdgeLeafTree.leafList, edgeDarts]

theorem tetra_bc_commutes :
    Equiv.swap TetraDart.bcB TetraDart.bcC *
      swapProduct (edgeWord tetraAfterAc) =
    swapProduct (edgeWord tetraAfterAc) *
      Equiv.swap TetraDart.bcB TetraDart.bcC := by
  exact swap_commutes_swapProduct_of_fresh
    (edgeDarts .bc) (edgeWord tetraAfterAc) tetra_bc_fresh

/-- The structural return coordinate genuinely executes on an actual
edge-leaf fork, then projects from the old middle vertices `b,c,d` to the
new middle vertices `b,d`. This is the local operation a branch-tree fold
would use whenever one child is a leaf. -/
theorem tetra_bc_return_fork (rho : Perm TetraDart) :
    nextHitPerm
      (nextHitPerm (rho * swapProduct (edgeWord tetraAfterAc)) tetraHitAfterAc *
        Equiv.swap
          (⟨TetraDart.bcB, tetraHit_bcB_dart⟩ : {d // tetraHitAfterAc d})
          ⟨TetraDart.bcC, tetraHit_bcC_dart⟩)
      (fun d => tetraHitAfterBc d.1) =
    (PermutationFirstReturnRestriction.nestedMarks tetraHitAfterBc
      tetraHitAfterAc tetraHitAfterBc_sub).permCongr
      (nextHitPerm (rho * swapProduct (edgeWord tetraAfterBc)) tetraHitAfterBc) := by
  simpa only [tetraAfterBc_word, edgeDarts] using
    (nextHitPerm_cons_project rho (edgeDarts .bc) (edgeWord tetraAfterAc)
      tetraHitAfterAc tetraHitAfterBc tetraHitAfterBc_sub
      tetraHit_bcB_dart tetraHit_bcC_dart tetra_bc_commutes)

/-- Before attaching `bc`, its two face positions lie on the same face in
the spherical K4 rotation, but on different faces in the twisted rotation.
This is the finite witness that a face-return cycle relation contains
information absent from the common scalar face count (two in each case). -/
theorem planar_bc_same_face :
    (tetraRho * swapProduct (edgeWord tetraAfterAc)).SameCycle
      (tetraRho TetraDart.bcB) (tetraRho TetraDart.bcC) := by
  decide +kernel

theorem twisted_bc_different_face :
    ¬ (twistedRho * swapProduct (edgeWord tetraAfterAc)).SameCycle
      (twistedRho TetraDart.bcB) (twistedRho TetraDart.bcC) := by
  decide +kernel

theorem planar_afterAc_faceCount :
    faceCount tetraRho tetraAfterAc = 2 := by decide +kernel

theorem twisted_afterAc_faceCount :
    faceCount twistedRho tetraAfterAc = 2 := by decide +kernel

theorem planar_afterBc_faceCount :
    faceCount tetraRho tetraAfterBc = 3 := by decide +kernel

theorem twisted_afterBc_faceCount :
    faceCount twistedRho tetraAfterBc = 1 := by decide +kernel

/-- The actual marked return records, unlike the two equal child face
counts, distinguish the two rotations on the *physical* intermediate shore.
The separating observation asks whether the two `bc` face positions share a
return cycle. -/
theorem tetra_return_distinguishes_rotations :
    nextHitPerm (tetraRho * swapProduct (edgeWord tetraAfterAc)) tetraHitAfterAc ≠
      nextHitPerm (twistedRho * swapProduct (edgeWord tetraAfterAc)) tetraHitAfterAc := by
  intro heq
  have hleft := (nextHitPerm_sameCycle_iff
    (tetraRho * swapProduct (edgeWord tetraAfterAc)) tetraHitAfterAc
    ⟨tetraRho TetraDart.bcB, tetraHit_bcB⟩
    ⟨tetraRho TetraDart.bcC, tetraHit_bcC⟩).2 planar_bc_same_face
  have hright :
      (nextHitPerm (twistedRho * swapProduct (edgeWord tetraAfterAc))
        tetraHitAfterAc).SameCycle
          ⟨twistedRho TetraDart.bcB, tetraHit_bcB⟩
          ⟨twistedRho TetraDart.bcC, tetraHit_bcC⟩ := by
    have hpos1 : tetraRho TetraDart.bcB = twistedRho TetraDart.bcB := rfl
    have hpos2 : tetraRho TetraDart.bcC = twistedRho TetraDart.bcC := rfl
    simpa only [heq, hpos1, hpos2] using hleft
  exact twisted_bc_different_face
    ((nextHitPerm_sameCycle_iff
      (twistedRho * swapProduct (edgeWord tetraAfterAc)) tetraHitAfterAc
      ⟨twistedRho TetraDart.bcB, tetraHit_bcB⟩
      ⟨twistedRho TetraDart.bcC, tetraHit_bcC⟩).1 hright)

end Mettapedia.GraphTheory.FourColor.GoertzelV24ForkFaceReturn
