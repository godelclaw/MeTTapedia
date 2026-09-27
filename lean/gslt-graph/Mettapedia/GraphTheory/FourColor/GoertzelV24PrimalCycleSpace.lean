import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.LinearAlgebra.Matrix.Rank
import Mettapedia.GraphTheory.FourColor.ColorAlgebra

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PrimalCycleSpace

open scoped BigOperators
open SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable section

/-- The unoriented vertex-edge incidence matrix over `F2`. -/
def f2IncidenceMatrix : Matrix V G.edgeSet F2 :=
  fun vertex edge => if vertex ∈ (edge.1 : Sym2 V) then 1 else 0

omit [DecidableRel G.Adj] in
/-- The transpose incidence map evaluates on an edge as the sum of its two
endpoint potentials. -/
theorem transpose_f2IncidenceMatrix_apply_edge
    (potential : V → F2) {left right : V} (hadj : G.Adj left right) :
    (Matrix.transpose (f2IncidenceMatrix G)).mulVecLin potential
      (⟨s(left, right), (SimpleGraph.mem_edgeSet G).2 hadj⟩ : G.edgeSet) =
        potential left + potential right := by
  classical
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, f2IncidenceMatrix]
  change (∑ vertex : V,
    (if vertex ∈ s(left, right) then 1 else 0) * potential vertex) =
      potential left + potential right
  simp only [Sym2.mem_iff, ite_mul, one_mul, zero_mul]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.univ.filter fun vertex : V =>
        vertex = left ∨ vertex = right) = {left, right} := by
    ext vertex
    simp [eq_comm]
  rw [hfilter]
  simp [hadj.ne]

private theorem f2_add_eq_zero_iff_eq (left right : F2) :
    left + right = 0 ↔ left = right := by
  constructor
  · intro hzero
    calc
      left = left + 0 := by simp
      _ = left + (right + right) := by rw [zmod2_add_self]
      _ = (left + right) + right := by rw [add_assoc]
      _ = right := by rw [hzero]; simp
  · rintro rfl
    exact zmod2_add_self _

/-- On a connected graph, the kernel of the transpose incidence map consists
exactly of constant vertex potentials. -/
theorem mem_ker_transpose_f2IncidenceMatrix_iff_constant
    (hconnected : G.Connected) (potential : V → F2) :
    potential ∈ LinearMap.ker
      (Matrix.transpose (f2IncidenceMatrix G)).mulVecLin ↔
        ∀ left right, potential left = potential right := by
  constructor
  · intro hkernel
    have hzero :
        (Matrix.transpose (f2IncidenceMatrix G)).mulVecLin potential = 0 :=
      (LinearMap.mem_ker).1 hkernel
    have hadjacent : ∀ {left right : V}, G.Adj left right →
        potential left = potential right := by
      intro left right hadj
      have hedgeZero := congrFun hzero
        (⟨s(left, right), (SimpleGraph.mem_edgeSet G).2 hadj⟩ : G.edgeSet)
      rw [Pi.zero_apply,
        transpose_f2IncidenceMatrix_apply_edge G potential hadj] at hedgeZero
      exact (f2_add_eq_zero_iff_eq _ _).1 hedgeZero
    intro left right
    rcases hconnected left right with ⟨walk⟩
    have hwalk : ∀ {start finish : V},
        (path : G.Walk start finish) →
          potential start = potential finish := by
      intro start finish path
      induction path with
      | nil => rfl
      | @cons first second last hadj tail ih =>
          exact (hadjacent hadj).trans ih
    exact hwalk walk
  · intro hconstant
    rw [LinearMap.mem_ker]
    funext edge
    rcases edge with ⟨edge, hedge⟩
    induction edge using Sym2.inductionOn with
    | _ left right =>
        have hadj : G.Adj left right :=
          (SimpleGraph.mem_edgeSet G).1 hedge
        rw [transpose_f2IncidenceMatrix_apply_edge G _ hadj]
        rw [hconstant right left]
        exact zmod2_add_self _

/-- The transpose incidence kernel of a connected finite graph has dimension
one. -/
theorem finrank_ker_transpose_f2IncidenceMatrix_eq_one
    (hconnected : G.Connected) :
    Module.finrank F2 (LinearMap.ker
      (Matrix.transpose (f2IncidenceMatrix G)).mulVecLin) = 1 := by
  let allOnes : LinearMap.ker
      (Matrix.transpose (f2IncidenceMatrix G)).mulVecLin :=
    ⟨fun _ => 1, (mem_ker_transpose_f2IncidenceMatrix_iff_constant
      G hconnected _).2 (fun _ _ => rfl)⟩
  let root : V := Classical.choice hconnected.nonempty
  apply finrank_eq_one allOnes
  · intro hzero
    have hvalue := congrFun (congrArg Subtype.val hzero) root
    change (1 : F2) = 0 at hvalue
    exact one_ne_zero hvalue
  · intro potential
    refine ⟨potential.1 root, ?_⟩
    apply Subtype.ext
    funext vertex
    have hconstant :=
      (mem_ker_transpose_f2IncidenceMatrix_iff_constant
        G hconnected potential.1).1 potential.2
    change potential.1 root * 1 = potential.1 vertex
    rw [mul_one]
    exact hconstant root vertex

/-- A connected finite graph's `F2` incidence matrix has rank `V - 1`. -/
theorem rank_f2IncidenceMatrix_eq_card_vertices_sub_one
    (hconnected : G.Connected) :
    (f2IncidenceMatrix G).rank = Fintype.card V - 1 := by
  have hrankNullity :=
    (Matrix.transpose (f2IncidenceMatrix G)).mulVecLin
      |>.finrank_range_add_finrank_ker
  rw [finrank_ker_transpose_f2IncidenceMatrix_eq_one G hconnected,
    Module.finrank_pi] at hrankNullity
  have htransposeRank :
      (Matrix.transpose (f2IncidenceMatrix G)).rank =
        Fintype.card V - 1 := by
    unfold Matrix.rank
    omega
  rw [Matrix.rank_transpose] at htransposeRank
  exact htransposeRank

/-- The scalar cycle space is the kernel of the unoriented incidence map. -/
def f2CycleSpace : Submodule F2 (G.edgeSet → F2) :=
  LinearMap.ker (f2IncidenceMatrix G).mulVecLin

/-- The `F2` cycle-space dimension of a connected finite graph is
`E - (V - 1)`. -/
theorem finrank_f2CycleSpace_eq
    (hconnected : G.Connected) :
    Module.finrank F2 (f2CycleSpace G) =
      Fintype.card G.edgeSet - (Fintype.card V - 1) := by
  have hrankNullity :=
    (f2IncidenceMatrix G).mulVecLin.finrank_range_add_finrank_ker
  have hrange :
      Module.finrank F2
          (LinearMap.range (f2IncidenceMatrix G).mulVecLin) =
        Fintype.card V - 1 := by
    exact rank_f2IncidenceMatrix_eq_card_vertices_sub_one G hconnected
  rw [hrange, Module.finrank_pi] at hrankNullity
  apply Nat.eq_sub_of_add_eq
  rw [add_comm]
  exact hrankNullity

end

end GoertzelV24PrimalCycleSpace

end Mettapedia.GraphTheory.FourColor
