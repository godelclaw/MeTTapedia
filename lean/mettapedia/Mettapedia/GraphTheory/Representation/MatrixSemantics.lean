import Mettapedia.GraphTheory.Representation.MatrixBridge
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.ZMod.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Relabelling and algorithmic semantics of operational adjacency matrices

The operational Boolean presentation is equivalent to labelled simple graphs
and to lawful standard Boolean matrices. Relabelling acts through Mathlib's
matrix reindexing and constructs actual graph isomorphisms; it need not preserve
equality of matrices at the original vertex labels.

Semiring-valued adjacency matrices retain the same edge data when zero and one
are distinct. Their powers count walks after applying the natural-number map
to the coefficient semiring. Natural coefficients retain counts exactly;
modular coefficients can erase nonzero counts.

A finite frontier recurrence computes length-indexed walk counts. The bounded
Boolean query is correct for existence of walks up to its supplied fuel.
These are exact mathematical matrices and finite sums, not a refinement theorem
for row-major storage, machine arithmetic, memory ownership or physical runtime.
-/

set_option autoImplicit false

namespace Mettapedia.GraphTheory.Representation.MatrixSemantics

open MatrixBridge
open scoped BigOperators

variable {n m k : Nat}

/-- The standard Boolean matrix, with the same simple-graph invariant as the
existing operational bridge, packaged as a mathematical subtype. -/
abbrev LawfulBoolMatrix (n : Nat) :=
  {matrix : Matrix (Fin n) (Fin n) Bool // MatrixBridge.IsSimple matrix}

/-- Both directions use the existing operational bridge rather than a second
definition of admissibility or matrix denotation. -/
def lawfulBoolEquiv (n : Nat) : AdjacencyMatrix.Rep n ≃ LawfulBoolMatrix n where
  toFun graph := ⟨toMatrix graph, toMatrix_isSimple graph⟩
  invFun matrix := ofMatrix matrix.val matrix.property
  left_inv := ofMatrix_toMatrix
  right_inv matrix := Subtype.ext (toMatrix_ofMatrix matrix.val matrix.property)

/-- Construct Boolean cells from graph adjacency. This inverse is mathematical:
it does not supply a physical decision procedure for an arbitrary input graph. -/
noncomputable def ofGraph (graph : SimpleGraph (Fin n)) : AdjacencyMatrix.Rep n := by
  classical
  exact {
    cell := fun source target => decide (graph.Adj source target)
    symmetric := by
      intro source target
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using graph.adj_comm source target
    loopless := by intro vertex; simp }

theorem denote_ofGraph (graph : SimpleGraph (Fin n)) :
    AdjacencyMatrix.denote (ofGraph graph) = graph := by
  classical
  ext source target
  simp [AdjacencyMatrix.denote, ofGraph]

theorem ofGraph_denote (graph : AdjacencyMatrix.Rep n) :
    ofGraph (AdjacencyMatrix.denote graph) = graph := by
  apply toMatrix_injective
  ext source target
  cases cell : graph.cell source target <;>
    simp [toMatrix, ofGraph, AdjacencyMatrix.denote, cell]

/-- Operational Boolean presentations and their labelled graph meanings are
genuinely equivalent; this does not quotient vertex labels by isomorphism. -/
noncomputable def graphEquiv (n : Nat) : AdjacencyMatrix.Rep n ≃ SimpleGraph (Fin n) where
  toFun := AdjacencyMatrix.denote
  invFun := ofGraph
  left_inv := ofGraph_denote
  right_inv := denote_ofGraph

theorem denote_injective : Function.Injective (@AdjacencyMatrix.denote n) :=
  (graphEquiv n).injective

/-- Simultaneously reindex both vertices of the existing Boolean cells. -/
def reindex (vertices : Fin n ≃ Fin m) (graph : AdjacencyMatrix.Rep n) :
    AdjacencyMatrix.Rep m where
  cell := Matrix.reindex vertices vertices (toMatrix graph)
  symmetric source target := graph.symmetric (vertices.symm source) (vertices.symm target)
  loopless vertex := graph.loopless (vertices.symm vertex)

theorem toMatrix_reindex (vertices : Fin n ≃ Fin m) (graph : AdjacencyMatrix.Rep n) :
    toMatrix (reindex vertices graph) = Matrix.reindex vertices vertices (toMatrix graph) := rfl

/-- Relabelling has an inverse at the full operational presentation. -/
def reindexEquiv (vertices : Fin n ≃ Fin m) : AdjacencyMatrix.Rep n ≃ AdjacencyMatrix.Rep m where
  toFun := reindex vertices
  invFun := reindex vertices.symm
  left_inv graph := by
    apply toMatrix_injective
    ext source target
    simp [toMatrix, reindex, Matrix.reindex, Matrix.submatrix]
  right_inv graph := by
    apply toMatrix_injective
    ext source target
    simp [toMatrix, reindex, Matrix.reindex, Matrix.submatrix]

theorem reindex_trans (first : Fin n ≃ Fin m) (second : Fin m ≃ Fin k)
    (graph : AdjacencyMatrix.Rep n) :
    reindex second (reindex first graph) = reindex (first.trans second) graph := by
  apply toMatrix_injective
  rfl

/-- The representation transport commutes with Mathlib's action on graphs. -/
theorem denote_reindex (vertices : Fin n ≃ Fin m) (graph : AdjacencyMatrix.Rep n) :
    AdjacencyMatrix.denote (reindex vertices graph) =
      vertices.simpleGraph (AdjacencyMatrix.denote graph) := by
  ext source target
  rfl

/-- A relabelling constructs the actual graph isomorphism, retaining its
vertex equivalence rather than merely asserting equal query answers. -/
def reindexIso (vertices : Fin n ≃ Fin m) (graph : AdjacencyMatrix.Rep n) :
    AdjacencyMatrix.denote graph ≃g AdjacencyMatrix.denote (reindex vertices graph) where
  __ := vertices
  map_rel_iff' := by
    intro source target
    simp [AdjacencyMatrix.denote, reindex, Matrix.reindex, Matrix.submatrix, toMatrix]

/-- Every graph isomorphism is exactly a simultaneous row/column relabelling
of these operational matrices. -/
theorem isomorphic_iff_reindex (source : AdjacencyMatrix.Rep n)
    (target : AdjacencyMatrix.Rep m) :
    Nonempty (AdjacencyMatrix.denote source ≃g AdjacencyMatrix.denote target) ↔
      ∃ vertices : Fin n ≃ Fin m, reindex vertices source = target := by
  constructor
  · rintro ⟨isomorphism⟩
    refine ⟨isomorphism.toEquiv, ?_⟩
    apply denote_injective
    ext first second
    exact isomorphism.symm.map_rel_iff
  · rintro ⟨vertices, rfl⟩
    exact ⟨reindexIso vertices source⟩

theorem reindex_eq_of_iso {source : AdjacencyMatrix.Rep n} {target : AdjacencyMatrix.Rep m}
    (isomorphism : AdjacencyMatrix.denote source ≃g AdjacencyMatrix.denote target) :
    reindex isomorphism.toEquiv source = target := by
  apply denote_injective
  ext first second
  exact isomorphism.symm.map_rel_iff

/-! ## Standard adjacency matrices with general coefficients -/

local instance (graph : AdjacencyMatrix.Rep n) :
    DecidableRel (AdjacencyMatrix.denote graph).Adj := denoteDecidableRel graph

/-- The same graph can be interpreted in different coefficient carriers.
Only matrix multiplication and walk counts require a semiring. -/
def adjacency (R : Type*) [Zero R] [One R] (graph : AdjacencyMatrix.Rep n) :
    Matrix (Fin n) (Fin n) R :=
  (AdjacencyMatrix.denote graph).adjMatrix R

theorem adjacency_apply (R : Type*) [Zero R] [One R] (graph : AdjacencyMatrix.Rep n)
    (source target : Fin n) :
    adjacency R graph source target = if graph.cell source target = true then 1 else 0 := by
  unfold adjacency
  rw [SimpleGraph.adjMatrix_apply]
  cases cell : graph.cell source target <;> simp [AdjacencyMatrix.denote, cell]

theorem adjacency_nat_eq_existing (graph : AdjacencyMatrix.Rep n) :
    adjacency Nat graph = mathlibAdjacencyMatrix graph := rfl

theorem adjacency_isAdjMatrix (R : Type*) [Zero R] [One R] (graph : AdjacencyMatrix.Rep n) :
    (adjacency R graph).IsAdjMatrix :=
  SimpleGraph.isAdjMatrix_adjMatrix _ _

theorem adjacency_toGraph (R : Type*) [MulZeroOneClass R] [Nontrivial R]
    (graph : AdjacencyMatrix.Rep n) :
    (adjacency_isAdjMatrix R graph).toGraph = AdjacencyMatrix.denote graph :=
  SimpleGraph.toGraph_adjMatrix_eq _ _

/-- Zero/one adjacency matrices over any nontrivial coefficient carrier
recover the full operational presentation, without using matrix powers. -/
theorem adjacency_ofGraph (R : Type*) [MulZeroOneClass R] [Nontrivial R]
    (matrix : Matrix (Fin n) (Fin n) R) (lawful : matrix.IsAdjMatrix) :
    adjacency R (ofGraph lawful.toGraph) = matrix := by
  ext source target
  have edge : (ofGraph lawful.toGraph).cell source target = true ↔
      matrix source target = 1 := by
    change (AdjacencyMatrix.denote (ofGraph lawful.toGraph)).Adj source target ↔ _
    rw [denote_ofGraph]
    rfl
  rcases lawful.zero_or_one source target with zero | one
  · have absent : ¬ (ofGraph lawful.toGraph).cell source target = true := by
      rw [edge, zero]
      exact zero_ne_one
    simp only [adjacency_apply, if_neg absent, zero]
  · simp only [adjacency_apply, if_pos (edge.mpr one), one]

/-- A full standard adjacency-matrix equivalence; nontriviality is required
because the zero coefficient carrier cannot distinguish edges from nonedges. -/
noncomputable def adjacencyEquiv (R : Type*) [MulZeroOneClass R] [Nontrivial R] (n : Nat) :
    AdjacencyMatrix.Rep n ≃
      {matrix : Matrix (Fin n) (Fin n) R // matrix.IsAdjMatrix} where
  toFun graph := ⟨adjacency R graph, adjacency_isAdjMatrix R graph⟩
  invFun matrix := ofGraph matrix.property.toGraph
  left_inv graph := by
    change ofGraph (adjacency_isAdjMatrix R graph).toGraph = graph
    rw [adjacency_toGraph]
    exact ofGraph_denote graph
  right_inv matrix := Subtype.ext (adjacency_ofGraph R matrix.val matrix.property)

theorem adjacency_injective (R : Type*) [MulZeroOneClass R] [Nontrivial R] :
    Function.Injective (adjacency R : AdjacencyMatrix.Rep n → _) := by
  intro first second same
  apply (adjacencyEquiv R n).injective
  exact Subtype.ext same

theorem adjacency_reindex (R : Type*) [Zero R] [One R]
    (vertices : Fin n ≃ Fin m) (graph : AdjacencyMatrix.Rep n) :
    Matrix.reindex vertices vertices (adjacency R graph) = adjacency R (reindex vertices graph) :=
  (reindexIso vertices graph).reindex_adjMatrix R

/-- Equality after a declared simultaneous row/column reindexing is exactly
equality of the transported presentations when zero and one remain distinct. -/
theorem reindex_eq_iff_adjacency_reindex (R : Type*) [MulZeroOneClass R] [Nontrivial R]
    (vertices : Fin n ≃ Fin m) (source : AdjacencyMatrix.Rep n) (target : AdjacencyMatrix.Rep m) :
    reindex vertices source = target ↔
      Matrix.reindex vertices vertices (adjacency R source) = adjacency R target := by
  rw [adjacency_reindex]
  exact (adjacency_injective R).eq_iff.symm

theorem isomorphic_iff_adjacency_reindex (R : Type*) [MulZeroOneClass R] [Nontrivial R]
    (source : AdjacencyMatrix.Rep n) (target : AdjacencyMatrix.Rep m) :
    Nonempty (AdjacencyMatrix.denote source ≃g AdjacencyMatrix.denote target) ↔
      ∃ vertices : Fin n ≃ Fin m,
        Matrix.reindex vertices vertices (adjacency R source) = adjacency R target := by
  rw [isomorphic_iff_reindex]
  exact exists_congr (fun vertices => reindex_eq_iff_adjacency_reindex R vertices source target)

theorem adjacency_map {R S : Type*} [Semiring R] [Semiring S]
    (coefficients : R →+* S) (graph : AdjacencyMatrix.Rep n) :
    (adjacency R graph).map coefficients = adjacency S graph := by
  ext source target
  simp [adjacency_apply, Matrix.map_apply]

/-- Matrix powers commute with the ring-equivalence induced by vertex
relabelling; this reuses Mathlib's multiplicative reindexing construction. -/
theorem power_reindex (R : Type*) [Semiring R] (vertices : Fin n ≃ Fin m)
    (graph : AdjacencyMatrix.Rep n) (length : Nat) :
    Matrix.reindex vertices vertices ((adjacency R graph) ^ length) =
      (adjacency R (reindex vertices graph)) ^ length := by
  calc
    _ = (Matrix.reindex vertices vertices (adjacency R graph)) ^ length :=
      (Matrix.reindexRingEquiv R vertices).map_pow _ _
    _ = _ := congrArg (fun matrix => matrix ^ length) (adjacency_reindex R vertices graph)

theorem power_map {R S : Type*} [Semiring R] [Semiring S]
    (coefficients : R →+* S) (graph : AdjacencyMatrix.Rep n) (length : Nat) :
    ((adjacency R graph) ^ length).map coefficients = (adjacency S graph) ^ length := by
  rw [Matrix.map_pow, adjacency_map]

/-- Mathlib's walk-count theorem applies directly to the operational graph
meaning. In a general semiring the displayed count is a natural-number cast. -/
theorem power_eq_walk_count (R : Type*) [Semiring R] (graph : AdjacencyMatrix.Rep n)
    (length : Nat) (source target : Fin n) :
    (adjacency R graph ^ length) source target =
      (Fintype.card {walk : (AdjacencyMatrix.denote graph).Walk source target |
        walk.length = length} : R) :=
  SimpleGraph.adjMatrix_pow_apply_eq_card_walk _ _ _

/-! ## A finite row-frontier algorithm -/

/-- Successive frontiers count extensions of earlier walks by one adjacent
vertex. This is a finite convolution algorithm, rather than a supplied
walk count or adjacency oracle for the whole query. -/
def frontier (R : Type*) [Semiring R] (graph : AdjacencyMatrix.Rep n) (source : Fin n) :
    Nat → Fin n → R
  | 0, target => if source = target then 1 else 0
  | length + 1, target =>
      ∑ middle, frontier R graph source length middle * adjacency R graph middle target

theorem frontier_eq_power (R : Type*) [Semiring R] (graph : AdjacencyMatrix.Rep n)
    (source : Fin n) (length : Nat) (target : Fin n) :
    frontier R graph source length target = (adjacency R graph ^ length) source target := by
  induction length generalizing target with
  | zero => simp [frontier, Matrix.one_apply]
  | succ length inductionHypothesis =>
      simp only [frontier, pow_succ, Matrix.mul_apply, inductionHypothesis]

theorem frontier_eq_walk_count (R : Type*) [Semiring R] (graph : AdjacencyMatrix.Rep n)
    (source : Fin n) (length : Nat) (target : Fin n) :
    frontier R graph source length target =
      (Fintype.card {walk : (AdjacencyMatrix.denote graph).Walk source target |
        walk.length = length} : R) := by
  rw [frontier_eq_power, power_eq_walk_count]

theorem frontier_reindex (R : Type*) [Semiring R] (vertices : Fin n ≃ Fin m)
    (graph : AdjacencyMatrix.Rep n) (source target : Fin n) (length : Nat) :
    frontier R (reindex vertices graph) (vertices source) length (vertices target) =
      frontier R graph source length target := by
  simp only [frontier_eq_power]
  have natural := congrFun (congrFun (power_reindex R vertices graph length)
    (vertices source)) (vertices target)
  simpa [Matrix.reindex, Matrix.submatrix] using natural.symm

/-- The algorithm respects the specific vertex map of a supplied graph
isomorphism, not merely the existence of some equivalent graph. -/
theorem frontier_iso (R : Type*) [Semiring R]
    {sourceGraph : AdjacencyMatrix.Rep n} {targetGraph : AdjacencyMatrix.Rep m}
    (isomorphism : AdjacencyMatrix.denote sourceGraph ≃g AdjacencyMatrix.denote targetGraph)
    (source target : Fin n) (length : Nat) :
    frontier R targetGraph (isomorphism source) length (isomorphism target) =
      frontier R sourceGraph source length target := by
  have changed := congrFun (congrFun (congrFun
    (congrArg (frontier R) (reindex_eq_of_iso isomorphism))
    (isomorphism source)) length) (isomorphism target)
  exact changed.symm.trans
    (frontier_reindex R isomorphism.toEquiv sourceGraph source target length)

theorem frontier_map {R S : Type*} [Semiring R] [Semiring S]
    (coefficients : R →+* S) (graph : AdjacencyMatrix.Rep n)
    (source target : Fin n) (length : Nat) :
    coefficients (frontier R graph source length target) =
      frontier S graph source length target := by
  simp only [frontier_eq_power]
  exact congrFun (congrFun (power_map coefficients graph length) source) target

/-- Natural counts determine every semiring-coefficient result by the
canonical natural-number map. No injectivity of that map is presumed. -/
theorem frontier_eq_natCast (R : Type*) [Semiring R] (graph : AdjacencyMatrix.Rep n)
    (source target : Fin n) (length : Nat) :
    frontier R graph source length target = (frontier Nat graph source length target : R) := by
  rw [frontier_eq_walk_count, frontier_eq_walk_count, Nat.cast_id]

/-- Characteristic zero is sufficient for a nonzero-coefficient walk test.
It is omitted deliberately from the general counting/transport results. -/
theorem frontier_ne_zero_iff (R : Type*) [Semiring R] [CharZero R]
    (graph : AdjacencyMatrix.Rep n) (source target : Fin n) (length : Nat) :
    frontier R graph source length target ≠ 0 ↔
      ∃ walk : (AdjacencyMatrix.denote graph).Walk source target, walk.length = length := by
  rw [frontier_eq_walk_count]
  simp only [Nat.cast_ne_zero, ← Nat.pos_iff_ne_zero, Fintype.card_pos_iff,
    nonempty_subtype, Set.mem_ofPred_eq]

theorem frontier_positive_iff (graph : AdjacencyMatrix.Rep n)
    (source : Fin n) (length : Nat) (target : Fin n) :
    0 < frontier Nat graph source length target ↔
      ∃ walk : (AdjacencyMatrix.denote graph).Walk source target, walk.length = length := by
  rw [frontier_eq_walk_count]
  simp only [Nat.cast_id]
  rw [Fintype.card_pos_iff]
  exact nonempty_subtype

/-- A bounded graph query computes a frontier for each admitted length. It
includes the length-zero walk, so a vertex is reachable from itself at fuel zero. -/
def reachableWithin (graph : AdjacencyMatrix.Rep n) (source target : Fin n) (fuel : Nat) : Bool :=
  (List.range (fuel + 1)).any (fun length => decide (0 < frontier Nat graph source length target))

theorem reachableWithin_iff (graph : AdjacencyMatrix.Rep n)
    (source target : Fin n) (fuel : Nat) :
    reachableWithin graph source target fuel = true ↔
      ∃ walk : (AdjacencyMatrix.denote graph).Walk source target, walk.length ≤ fuel := by
  simp only [reachableWithin, List.any_eq_true, decide_eq_true_eq, List.mem_range,
    Nat.lt_succ_iff, frontier_positive_iff]
  constructor
  · rintro ⟨length, bound, walk, equal⟩
    exact ⟨walk, equal.le.trans bound⟩
  · rintro ⟨walk, bound⟩
    exact ⟨walk.length, bound, walk, rfl⟩

/-- Any reachable pair in an n-vertex graph has a simple path with at most
n-1 edges. The finite frontier query therefore decides full reachability. -/
theorem reachableWithin_complete (graph : AdjacencyMatrix.Rep n) (source target : Fin n) :
    reachableWithin graph source target (n - 1) = true ↔
      (AdjacencyMatrix.denote graph).Reachable source target := by
  rw [reachableWithin_iff]
  constructor
  · rintro ⟨walk, _⟩
    exact ⟨walk⟩
  · intro reachable
    obtain ⟨walk, path⟩ := reachable.exists_isPath
    refine ⟨walk, ?_⟩
    have bound : walk.length < n := by simpa using path.length_lt
    omega

/-- Increasing fuel retains every previously found witness. -/
theorem reachableWithin_mono (graph : AdjacencyMatrix.Rep n) (source target : Fin n)
    {first second : Nat} (more : first ≤ second)
    (found : reachableWithin graph source target first = true) :
    reachableWithin graph source target second = true := by
  obtain ⟨walk, bound⟩ := (reachableWithin_iff _ _ _ _).1 found
  exact (reachableWithin_iff _ _ _ _).2 ⟨walk, bound.trans more⟩


/-! ## Relabelling and coefficient-loss controls -/

namespace Controls

def path3 : AdjacencyMatrix.Rep 3 :=
  Transformations.toMatrix (EdgeList.presentation 3) EdgeList.Canary.path3

def swapEndpointCenter : Fin 3 ≃ Fin 3 := Equiv.swap 0 1

/-- The changed encoding has a real graph isomorphism, but its original
coordinate names no longer identify the same matrix cells. -/
theorem isomorphic_presentations_have_different_matrices :
    Nonempty (AdjacencyMatrix.denote path3 ≃g
      AdjacencyMatrix.denote (reindex swapEndpointCenter path3)) ∧
      toMatrix path3 ≠ toMatrix (reindex swapEndpointCenter path3) := by
  refine ⟨⟨reindexIso swapEndpointCenter path3⟩, ?_⟩
  intro same
  have cell := congrFun (congrFun same (1 : Fin 3)) (2 : Fin 3)
  have different :
      toMatrix path3 (1 : Fin 3) (2 : Fin 3) ≠
        toMatrix (reindex swapEndpointCenter path3) (1 : Fin 3) (2 : Fin 3) := by decide
  exact different cell

theorem path3_frontier_counts_two_returns : frontier Nat path3 1 2 1 = 2 := by decide

theorem path3_bounded_query_needs_two_steps :
    reachableWithin path3 0 2 1 = false ∧ reachableWithin path3 0 2 2 = true := by decide

/-- Length-zero reachability is reflexive even though adjacency is loopless. -/
theorem zero_length_reachability_is_not_a_self_edge :
    reachableWithin path3 1 1 0 = true ∧ toMatrix path3 1 1 = false := by decide

/-- Four vertices split into two parts; every cross-part pair is adjacent.
There are two distinct length-two walks between vertices 0 and 1. -/
def fourCycle : AdjacencyMatrix.Rep 4 where
  cell source target := decide (source.val < 2) != decide (target.val < 2)
  symmetric := by decide
  loopless := by decide

theorem fourCycle_two_walks : frontier Nat fourCycle 0 2 1 = 2 := by decide

/-- All length-two counts vanish over characteristic two: cross-part pairs
have no such walks, while same-part pairs have exactly two. -/
theorem modular_square_zero : adjacency (ZMod 2) fourCycle ^ 2 = 0 := by decide

theorem modular_later_powers_zero (length : Nat) (later : 2 ≤ length) :
    adjacency (ZMod 2) fourCycle ^ length = 0 := by
  obtain ⟨remaining, rfl⟩ := Nat.exists_eq_add_of_le later
  rw [pow_add, modular_square_zero, zero_mul]

theorem fourCycle_reachable : (AdjacencyMatrix.denote fourCycle).Reachable (0 : Fin 4) 1 := by
  have first : (AdjacencyMatrix.denote fourCycle).Adj (0 : Fin 4) 2 := by decide
  have second : (AdjacencyMatrix.denote fourCycle).Adj (2 : Fin 4) 1 := by decide
  exact ⟨.cons first (.cons second .nil)⟩

/-- A reachable pair of distinct vertices can have zero coefficient count
at every length. General semiring results therefore do not justify a
nonzero-entry reachability test without an additional coefficient hypothesis. -/
theorem modular_all_lengths_erase_a_reachable_pair :
    (AdjacencyMatrix.denote fourCycle).Reachable (0 : Fin 4) 1 ∧
      ∀ length, frontier (ZMod 2) fourCycle 0 length 1 = 0 := by
  refine ⟨fourCycle_reachable, ?_⟩
  intro length
  cases length with
  | zero => decide
  | succ length =>
      cases length with
      | zero => decide
      | succ remaining =>
          rw [frontier_eq_power, modular_later_powers_zero _ (by omega)]
          rfl

end Controls

end Mettapedia.GraphTheory.Representation.MatrixSemantics
