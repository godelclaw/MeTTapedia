import Mettapedia.GraphTheory.FourColor.CAP5BoundaryWord
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCycleSpaceEquality
import Mettapedia.GraphTheory.FourColor.GoertzelV24WalkCycleParity

/-!
# The Klein identity and the vanishing of a Tait colouring on the cycle space

This is the algebraic half of Tait's reduction, formalized as written.

A Tait colouring of the dual is, since primal and dual share an edge set, a
function `omega` from edges to nonzero colours such that the three edges
bounding any primal face receive three pairwise distinct nonzero values.  The
reduction's proof then runs in four steps.  This module carries the first two.

* The Klein identity: the three nonzero elements of `F2 × F2` sum to zero, and
  any three pairwise distinct nonzero elements are all three of them.  The
  colour type here is literally `F2 × F2` and the tree's `IsTaitColorTriple` is
  literally "three pairwise distinct nonzero colours", so both halves are finite
  checks.
* Step 1: `omega` sums to zero over the boundary of every face.  Its three
  edges carry three pairwise distinct nonzero values, which by the Klein
  identity are all three nonzero elements, and those sum to zero.
* Step 2: `omega` sums to zero over every element of the cycle space.
  Summation of `omega` over an edge set is `F2`-linear in that set, applied
  coordinatewise in `F2 × F2`; the facial boundaries span the cycle space, and
  a linear functional vanishing on a spanning set vanishes identically.

* Step 3: potentials exist.  Fix a root; for each vertex sum `omega` along a
  walk from the root.  This is well defined because two such walks differ by an
  element of the cycle space, on which `omega` sums to zero by Step 2, and even
  repetitions cancel in `F2 × F2`.
* Step 4: the potential is a proper colouring.  Appending an edge to a walk
  gives `c u + c v = omega uv`, which is nonzero, so `c u` and `c v` differ.

Step 2 consumes the spanning theorem for facial boundaries, which is already
available, together with its hypothesis of two-sided faces.  Steps 3 and 4
consume the mod-two walk-parity calculus: the incidence boundary of a walk's
parity vector is the sum of its two endpoint indicators, so the combination
used below has zero boundary and therefore lies in the cycle space.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TaitReductionPotential

open GoertzelV24FaceBoundaryLinearAlgebra
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24OrbitFaceCycleSpace
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrbitFaceCycleSpaceEquality
open GoertzelV24PrimalCycleSpace
open GoertzelV24WalkCycleParity
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## The Klein identity -/

/-- **The Klein identity, first half.**  Three pairwise distinct nonzero
elements of `F2 × F2` sum to zero: the group has exponent two and there are
exactly three nonzero elements, so three pairwise distinct ones exhaust them
and `a + b + (a + b) = 0`. -/
theorem klein_sum_eq_zero {first second third : Color}
    (htriple : IsTaitColorTriple first second third) :
    first + second + third = 0 := by
  have key : ∀ a b c : Color, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ≠ b → a ≠ c → b ≠ c →
      a + b + c = 0 := by decide
  exact key first second third htriple.1 htriple.2.1 htriple.2.2.1
    htriple.2.2.2.1 htriple.2.2.2.2.1 htriple.2.2.2.2.2

set_option maxRecDepth 8000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- **The Klein identity, second half.**  Any three pairwise distinct nonzero
elements of `F2 × F2` are all three of them: every nonzero colour is one of
the triple. -/
theorem klein_exhausts {first second third : Color}
    (htriple : IsTaitColorTriple first second third)
    {colour : Color} (hcolour : colour ≠ 0) :
    colour = first ∨ colour = second ∨ colour = third := by
  have hcases : colour = ((1 : F2), (0 : F2)) ∨ colour = ((0 : F2), (1 : F2)) ∨
      colour = ((1 : F2), (1 : F2)) := by
    revert hcolour
    revert colour
    decide
  have key : ∀ a b c : Color, a ≠ 0 → b ≠ 0 → c ≠ 0 → a ≠ b → a ≠ c → b ≠ c →
      (((1 : F2), (0 : F2)) = a ∨ ((1 : F2), (0 : F2)) = b ∨
          ((1 : F2), (0 : F2)) = c) ∧
        (((0 : F2), (1 : F2)) = a ∨ ((0 : F2), (1 : F2)) = b ∨
          ((0 : F2), (1 : F2)) = c) ∧
        (((1 : F2), (1 : F2)) = a ∨ ((1 : F2), (1 : F2)) = b ∨
          ((1 : F2), (1 : F2)) = c) := by decide
  have hkey := key first second third htriple.1 htriple.2.1 htriple.2.2.1
    htriple.2.2.2.1 htriple.2.2.2.2.1 htriple.2.2.2.2.2
  rcases hcases with hc | hc | hc <;> subst hc
  · exact hkey.1
  · exact hkey.2.1
  · exact hkey.2.2

/-! ## Summation of a colouring over an edge set -/

/-- Summation of `omega` over an edge set, as an `F2`-linear functional on the
edge space with values in `F2 × F2`.  Linearity is the content of Step 2's
phrase "applied coordinatewise". -/
def edgeSum (omega : G.edgeSet → Color) :
    (G.edgeSet → F2) →ₗ[F2] Color where
  toFun weights := ∑ edge : G.edgeSet, weights edge • omega edge
  map_add' := by
    intro left right
    simp only [Pi.add_apply, add_smul]
    exact Finset.sum_add_distrib
  map_smul' := by
    intro scalar weights
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
    exact (Finset.smul_sum).symm

omit [DecidableEq V] in
@[simp] theorem edgeSum_apply (omega : G.edgeSet → Color)
    (weights : G.edgeSet → F2) :
    edgeSum omega weights = ∑ edge : G.edgeSet, weights edge • omega edge :=
  rfl

/-- On the indicator of a finite edge set, the functional is the plain sum of
`omega` over that set. -/
theorem edgeSum_indicator (omega : G.edgeSet → Color)
    (edges : Finset G.edgeSet) :
    edgeSum omega (fun edge => if edge ∈ edges then 1 else 0) =
      ∑ edge ∈ edges, omega edge := by
  classical
  simp only [edgeSum_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_mem, Finset.univ_inter]

/-! ## The transported Tait condition -/

/-- A Tait colouring of the dual, read on the shared edge set: the three edges
bounding any face receive three pairwise distinct nonzero values. -/
def FacialTaitColouring (data : Data G) (omega : G.edgeSet → Color) : Prop :=
  ∀ face : OrbitFace data.toRotationSystem,
    ∃ first second third : G.edgeSet,
      orbitFaceBoundary data.toRotationSystem face = {first, second, third} ∧
      IsTaitColorTriple (omega first) (omega second) (omega third)

omit [Fintype V] [DecidableRel G.Adj] in
/-- Distinct colours force distinct edges, so a Tait triple's three edges are
three elements and their sum is the sum of the three colours. -/
theorem sum_over_taitTriple (omega : G.edgeSet → Color)
    {first second third : G.edgeSet}
    (htriple : IsTaitColorTriple (omega first) (omega second) (omega third)) :
    ∑ edge ∈ ({first, second, third} : Finset G.edgeSet), omega edge = 0 := by
  classical
  have hfs : first ≠ second := fun h => htriple.2.2.2.1 (by rw [h])
  have hft : first ≠ third := fun h => htriple.2.2.2.2.1 (by rw [h])
  have hst : second ≠ third := fun h => htriple.2.2.2.2.2 (by rw [h])
  rw [Finset.sum_insert (by simp [hfs, hft]),
    Finset.sum_insert (by simp [hst]), Finset.sum_singleton, ← add_assoc]
  exact klein_sum_eq_zero htriple

/-! ## Step 1 -/

/-- **Step 1.**  A Tait colouring sums to zero over the boundary of every
face: the three boundary edges carry three pairwise distinct nonzero values,
which are all three nonzero elements, and those sum to zero. -/
theorem edgeSum_orbitFaceBoundaryIndicator_eq_zero
    (data : Data G) (omega : G.edgeSet → Color)
    (htait : FacialTaitColouring data omega)
    (face : OrbitFace data.toRotationSystem) :
    edgeSum omega (orbitFaceBoundaryIndicator data face) = 0 := by
  classical
  obtain ⟨first, second, third, hboundary, htriple⟩ := htait face
  have hindicator :
      orbitFaceBoundaryIndicator data face =
        fun edge => if edge ∈ ({first, second, third} : Finset G.edgeSet)
          then 1 else 0 := by
    funext edge
    simp [orbitFaceBoundaryIndicator, hboundary]
  rw [hindicator, edgeSum_indicator]
  exact sum_over_taitTriple omega htriple

/-! ## Step 2 -/

/-- **Step 2.**  A Tait colouring sums to zero over every element of the
`F2` cycle space.  The facial boundaries span it, and the summation functional
is linear, so vanishing on the spanning set is vanishing identically. -/
theorem edgeSum_eq_zero_of_mem_f2CycleSpace
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (omega : G.edgeSet → Color)
    (htait : FacialTaitColouring data omega)
    {weights : G.edgeSet → F2} (hweights : weights ∈ f2CycleSpace G) :
    edgeSum omega weights = 0 := by
  classical
  rw [← range_orbitFaceBoundaryLinearMap_eq_f2CycleSpace data htwoSided hdual
    hconnected hsphere] at hweights
  obtain ⟨coefficients, rfl⟩ := hweights
  rw [orbitFaceBoundaryLinearMap_eq_sum_indicators data coefficients,
    map_sum]
  refine Finset.sum_eq_zero fun face _ => ?_
  rw [map_smul,
    edgeSum_orbitFaceBoundaryIndicator_eq_zero data omega htait face,
    smul_zero]

/-! ## Steps 3 and 4: the potential and the colouring -/

/-- The functional picks out a single edge's colour from its basis vector. -/
theorem edgeSum_single (omega : G.edgeSet → Color) (edge : G.edgeSet) :
    edgeSum omega (Pi.single edge 1) = omega edge := by
  classical
  simp only [edgeSum_apply, Pi.single_apply, ite_smul, one_smul, zero_smul]
  rw [Finset.sum_ite_eq' Finset.univ edge omega]
  simp

/-- **Step 3.**  The potential at a vertex: sum `omega` along a walk from the
fixed root.  Connectedness supplies the walk. -/
noncomputable def potential (omega : G.edgeSet → Color)
    (hconnected : G.Connected) (root vertex : V) : Color :=
  edgeSum omega (walkEdgeParity (hconnected.preconnected root vertex).some)

/-- **Step 4, the cocycle identity.**  For every edge the two endpoint
potentials sum to that edge's colour.

The walk from the root to `u`, the walk from the root to `v`, and the edge
`uv` together have zero incidence boundary — each endpoint indicator occurs
twice — so their combination lies in the cycle space, where `omega` sums to
zero by Step 2.  This is simultaneously the well-definedness of Step 3 and the
computation of Step 4: no choice of walk enters the conclusion. -/
theorem potential_add_potential_eq_omega
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (omega : G.edgeSet → Color)
    (htait : FacialTaitColouring data omega)
    (root : V) {first second : V} (hadj : G.Adj first second) :
    potential omega hconnected root first +
        potential omega hconnected root second =
      omega ⟨s(first, second), (SimpleGraph.mem_edgeSet G).2 hadj⟩ := by
  classical
  set firstWalk := (hconnected.preconnected root first).some with hfirstWalk
  set secondWalk := (hconnected.preconnected root second).some with hsecondWalk
  set edge : G.edgeSet :=
    ⟨s(first, second), (SimpleGraph.mem_edgeSet G).2 hadj⟩ with hedge
  set combination : G.edgeSet → F2 :=
    walkEdgeParity firstWalk + walkEdgeParity secondWalk + Pi.single edge 1
    with hcombination
  have hboundary : combination ∈ f2CycleSpace G := by
    rw [f2CycleSpace, LinearMap.mem_ker, hcombination, map_add, map_add,
      f2IncidenceMatrix_mulVec_walkEdgeParity,
      f2IncidenceMatrix_mulVec_walkEdgeParity,
      f2IncidenceMatrix_mulVec_single_edge hadj]
    funext vertex
    simp only [Pi.add_apply, Pi.zero_apply]
    have hself : ∀ value : F2, value + value = 0 := by decide
    set rootValue : F2 := (Pi.single root (1 : F2) : V → F2) vertex
    set firstValue : F2 := (Pi.single first (1 : F2) : V → F2) vertex
    set secondValue : F2 := (Pi.single second (1 : F2) : V → F2) vertex
    calc
      rootValue + firstValue + (rootValue + secondValue) +
            (firstValue + secondValue)
          = (rootValue + rootValue) + (firstValue + firstValue) +
            (secondValue + secondValue) := by abel
      _ = 0 := by rw [hself, hself, hself]; simp
  have hzero : edgeSum omega combination = 0 :=
    edgeSum_eq_zero_of_mem_f2CycleSpace data htwoSided hdual hconnected hsphere
      omega htait hboundary
  rw [hcombination, map_add, map_add, edgeSum_single] at hzero
  have hchar : ∀ left right : Color, left + right = 0 → left = right := by decide
  exact hchar _ _ hzero

/-- **Step 4.**  Adjacent vertices receive different potentials, because their
potentials sum to a nonzero colour. -/
theorem potential_ne_of_adj
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (omega : G.edgeSet → Color)
    (hnonzero : ∀ edge : G.edgeSet, omega edge ≠ 0)
    (htait : FacialTaitColouring data omega)
    (root : V) {first second : V} (hadj : G.Adj first second) :
    potential omega hconnected root first ≠
      potential omega hconnected root second := by
  intro hequal
  have hsum := potential_add_potential_eq_omega data htwoSided hdual hconnected
    hsphere omega htait root hadj
  rw [hequal] at hsum
  have hself : ∀ value : Color, value + value = 0 := by decide
  exact hnonzero _ (hsum.symm.trans (hself _))

/-- **The four-colouring.**  A Tait colouring of the dual, read on the shared
edge set, yields a proper vertex colouring of the primal graph by the four
elements of `F2 × F2`. -/
theorem colorable_four_of_facialTaitColouring
    (data : Data G)
    (htwoSided : OrbitFacesTwoSided data.toRotationSystem)
    (hdual : (interiorDualGraph
      (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData data.toRotationSystem)
    (omega : G.edgeSet → Color)
    (hnonzero : ∀ edge : G.edgeSet, omega edge ≠ 0)
    (htait : FacialTaitColouring data omega) :
    G.Colorable 4 := by
  classical
  obtain ⟨root⟩ := hconnected.nonempty
  let colouring : G.Coloring Color :=
    SimpleGraph.Coloring.mk (potential omega hconnected root)
      (fun {first second} hadj =>
        potential_ne_of_adj data htwoSided hdual hconnected hsphere omega
          hnonzero htait root hadj)
  have hcard : Fintype.card Color = 4 := by decide
  have := colouring.colorable
  rwa [hcard] at this

end GoertzelV24TaitReductionPotential

end Mettapedia.GraphTheory.FourColor
