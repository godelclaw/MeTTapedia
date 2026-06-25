import Mettapedia.GraphTheory.FourColor.CAP5BoundaryWord
import Mettapedia.GraphTheory.FourColor.BoundaryChains
import Mettapedia.GraphTheory.FourColor.GoertzelDefinition48

open scoped BigOperators

open SimpleGraph

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*}

/-!
Graph-facing CAP5 boundary bridges.

This file connects the local CAP5 boundary-word layer to the manuscript's Tait edge-coloring
interface, without adding graph geometry assumptions.
-/

/-- A normalized ordered presentation of a five-edge CAP5 boundary support.  The support set is
kept in the type so finite benchmarks can prove once that their selected boundary support is
exactly the five indexed edges, then reuse the graph-facing CAP5 boundary lemmas without
threading the same `Fin 5` image equality through every theorem. -/
structure CAP5BoundaryEdgeEnumeration {E : Type*} [DecidableEq E] (support : Finset E) where
  boundaryEdge : Fin 5 → E
  injective : Function.Injective boundaryEdge
  support_eq : support = Finset.univ.map ⟨boundaryEdge, injective⟩

namespace CAP5BoundaryEdgeEnumeration

variable {E : Type*} [DecidableEq E] {support : Finset E}

@[simp] theorem mem_support_iff (enum : CAP5BoundaryEdgeEnumeration support) {e : E} :
    e ∈ support ↔ ∃ i : Fin 5, enum.boundaryEdge i = e := by
  constructor
  · intro h
    have hmap : e ∈ Finset.univ.map ⟨enum.boundaryEdge, enum.injective⟩ := by
      simpa [enum.support_eq] using h
    simpa using hmap
  · intro h
    have hmap : e ∈ Finset.univ.map ⟨enum.boundaryEdge, enum.injective⟩ := by
      simpa using h
    simpa [enum.support_eq] using hmap

@[simp] theorem card_support (enum : CAP5BoundaryEdgeEnumeration support) :
    support.card = 5 := by
  rw [enum.support_eq]
  simp

theorem incident_eq_map {U : Type*} {D : ZeroBoundaryData U E} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) :
    D.incident v = Finset.univ.map ⟨enum.boundaryEdge, enum.injective⟩ :=
  enum.support_eq

end CAP5BoundaryEdgeEnumeration

/-- Restricting a Tait edge-coloring to five CAP5 boundary edges gives a nonzero CAP5 boundary
word. -/
theorem cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring
    {G : SimpleGraph V} (boundaryEdge : Fin 5 → G.edgeSet)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordOfEdges_isNonzero_of_forall_nonzero boundaryEdge C
    (fun i => hC (boundaryEdge i))

/-- If the five CAP5 boundary edges enumerate a zero-boundary incidence set, the restricted
CAP5 boundary word has zero total color sum.  This is the graph-side cut equation in the
boundary-word language. -/
theorem cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at
    {U E : Type*} {D : ZeroBoundaryData U E} {v : U}
    (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C) :
    (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0 := by
  have hv := hzero v
  rw [hincident] at hv
  simpa [cap5BoundaryWordOfEdges] using hv

/-- Membership in the full zero-boundary set gives the CAP5 cut equation whenever the five
boundary edges enumerate a vertex-incidence set. -/
theorem cap5BoundaryWordOfEdges_sum_eq_zero_of_mem_zeroBoundarySet_at
    {U E : Type*} {D : ZeroBoundaryData U E} {v : U}
    (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : C ∈ D.zeroBoundarySet) :
    (∑ i : Fin 5, cap5BoundaryWordOfEdges boundaryEdge C i) = 0 :=
  cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at boundaryEdge C hinj
    hincident hzero.1

namespace CAP5BoundaryEdgeEnumeration

variable {E : Type*} [DecidableEq E]

/-- Enumeration form of the graph-side CAP5 cut equation. -/
theorem cap5BoundaryWord_sum_eq_zero_of_isZeroBoundary_at
    {U : Type*} {D : ZeroBoundaryData U E} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) (C : E → Color)
    (hzero : D.isZeroBoundary C) :
    (∑ i : Fin 5, cap5BoundaryWordOfEdges enum.boundaryEdge C i) = 0 :=
  cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at enum.boundaryEdge C
    enum.injective enum.incident_eq_map hzero

/-- Enumeration form of the full-zero-boundary-set CAP5 cut equation. -/
theorem cap5BoundaryWord_sum_eq_zero_of_mem_zeroBoundarySet_at
    {U : Type*} {D : ZeroBoundaryData U E} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) (C : E → Color)
    (hzero : C ∈ D.zeroBoundarySet) :
    (∑ i : Fin 5, cap5BoundaryWordOfEdges enum.boundaryEdge C i) = 0 :=
  enum.cap5BoundaryWord_sum_eq_zero_of_isZeroBoundary_at C hzero.1

end CAP5BoundaryEdgeEnumeration

/-- Graph-facing CAP5 parity: a Tait edge coloring whose five CAP5 boundary edges enumerate a
zero-boundary incidence set has odd red/blue/purple boundary counts. -/
theorem cap5BoundaryWordOfEdges_hasOddColorCounts_of_isTaitEdgeColoring_of_isZeroBoundary_at
    {U : Type*} {G : SimpleGraph V} {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C) :
    CAP5BoundaryWordHasOddColorCounts (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordHasOddColorCounts_of_nonzero_of_sum_eq_zero
    (cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC)
    (cap5BoundaryWordOfEdges_sum_eq_zero_of_isZeroBoundary_at boundaryEdge C hinj hincident hzero)

/-- Full-zero-boundary-set variant of the graph-facing CAP5 parity theorem. -/
theorem cap5BoundaryWordOfEdges_hasOddColorCounts_of_isTaitEdgeColoring_of_mem_zeroBoundarySet_at
    {U : Type*} {G : SimpleGraph V} {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet) :
    CAP5BoundaryWordHasOddColorCounts (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordOfEdges_hasOddColorCounts_of_isTaitEdgeColoring_of_isZeroBoundary_at
    boundaryEdge C hC hinj hincident hzero.1

/-- Graph-facing CAP5 block classifier: under the Tait and zero-boundary cut hypotheses, the
induced CAP5 boundary word is either a good `(3,1,1)` block or a bad `(2,1,1,1)` block. -/
theorem cap5BoundaryWordOfEdges_coloredBlock311_or_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    {U : Type*} {G : SimpleGraph V} {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C) :
    CAP5BoundaryWordHasColoredBlock311 (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      CAP5BoundaryWordHasColoredBlock2111 (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_nonzero_of_odd
    (cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC)
    (cap5BoundaryWordOfEdges_hasOddColorCounts_of_isTaitEdgeColoring_of_isZeroBoundary_at
      boundaryEdge C hC hinj hincident hzero)

/-- Full-zero-boundary-set variant of the graph-facing CAP5 block classifier. -/
theorem cap5BoundaryWordOfEdges_coloredBlock311_or_coloredBlock2111_of_isTaitEdgeColoring_of_mem_zeroBoundarySet_at
    {U : Type*} {G : SimpleGraph V} {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet) :
    CAP5BoundaryWordHasColoredBlock311 (cap5BoundaryWordOfEdges boundaryEdge C) ∨
      CAP5BoundaryWordHasColoredBlock2111 (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordOfEdges_coloredBlock311_or_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    boundaryEdge C hC hinj hincident hzero.1

/-- Graph-facing CAP5 nonextension criterion under the manuscript cut hypotheses: failure to
extend is exactly the bad `(2,1,1,1)` case. -/
theorem cap5BoundaryWordOfEdges_not_extendsAcrossCycle_iff_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    {U : Type*} {G : SimpleGraph V} {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : D.isZeroBoundary C) :
    ¬ CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ↔
      CAP5BoundaryWordHasColoredBlock2111 (cap5BoundaryWordOfEdges boundaryEdge C) :=
  not_cap5_extendsAcrossCycle_iff_coloredBlock2111_of_nonzero_of_odd
    (cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC)
    (cap5BoundaryWordOfEdges_hasOddColorCounts_of_isTaitEdgeColoring_of_isZeroBoundary_at
      boundaryEdge C hC hinj hincident hzero)

/-- Full-zero-boundary-set variant of the graph-facing CAP5 nonextension criterion. -/
theorem cap5BoundaryWordOfEdges_not_extendsAcrossCycle_iff_coloredBlock2111_of_isTaitEdgeColoring_of_mem_zeroBoundarySet_at
    {U : Type*} {G : SimpleGraph V} {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hinj : Function.Injective boundaryEdge)
    (hincident : D.incident v = Finset.univ.map ⟨boundaryEdge, hinj⟩)
    (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet) :
    ¬ CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges boundaryEdge C) ↔
      CAP5BoundaryWordHasColoredBlock2111 (cap5BoundaryWordOfEdges boundaryEdge C) :=
  cap5BoundaryWordOfEdges_not_extendsAcrossCycle_iff_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    boundaryEdge C hC hinj hincident hzero.1

/-- If a CAP5 boundary edge is one of the distinguished zero-boundary edges, its boundary-word
color is forced to zero by membership in the full zero-boundary set. -/
theorem cap5BoundaryWordOfEdges_eq_zero_of_mem_zeroBoundarySet_boundaryEdge
    {U E : Type*} {D : ZeroBoundaryData U E}
    (boundaryEdge : Fin 5 → E) (C : E → Color)
    (hzero : C ∈ D.zeroBoundarySet) {i : Fin 5}
    (hi : boundaryEdge i ∈ D.boundaryEdges) :
    cap5BoundaryWordOfEdges boundaryEdge C i = 0 :=
  hzero.2 (boundaryEdge i) hi

/-- A Tait-colored CAP5 boundary cannot put all five boundary edges into the distinguished
zero-boundary edge set. -/
theorem not_forall_boundaryEdge_mem_boundaryEdges_of_isTaitEdgeColoring_of_mem_zeroBoundarySet
    {U : Type*} {G : SimpleGraph V} {D : ZeroBoundaryData U G.edgeSet}
    (boundaryEdge : Fin 5 → G.edgeSet) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C) (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet) :
    ¬ ∀ i : Fin 5, boundaryEdge i ∈ D.boundaryEdges := by
  intro hboundary
  have hzero0 :
      cap5BoundaryWordOfEdges boundaryEdge C 0 = 0 :=
    cap5BoundaryWordOfEdges_eq_zero_of_mem_zeroBoundarySet_boundaryEdge boundaryEdge
      (C : G.edgeSet → Color) hzero (hboundary 0)
  have hnonzero : cap5BoundaryWordOfEdges boundaryEdge C 0 ≠ 0 :=
    cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring boundaryEdge C hC 0
  exact hnonzero hzero0

namespace CAP5BoundaryEdgeEnumeration

/-- Enumeration form of CAP5 boundary nonzero-ness for Tait edge colorings. -/
theorem cap5BoundaryWord_isNonzero_of_isTaitEdgeColoring
    [DecidableEq V] {G : SimpleGraph V} {support : Finset G.edgeSet}
    (enum : CAP5BoundaryEdgeEnumeration support)
    (C : G.EdgeColoring Color) (hC : IsTaitEdgeColoring G C) :
    CAP5BoundaryWordIsNonzero (cap5BoundaryWordOfEdges enum.boundaryEdge C) :=
  cap5BoundaryWordOfEdges_isNonzero_of_isTaitEdgeColoring enum.boundaryEdge C hC

/-- Enumeration form of graph-facing CAP5 parity. -/
theorem cap5BoundaryWord_hasOddColorCounts_of_isTaitEdgeColoring_of_isZeroBoundary_at
    {U : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C) (hzero : D.isZeroBoundary C) :
    CAP5BoundaryWordHasOddColorCounts (cap5BoundaryWordOfEdges enum.boundaryEdge C) :=
  cap5BoundaryWordOfEdges_hasOddColorCounts_of_isTaitEdgeColoring_of_isZeroBoundary_at
    enum.boundaryEdge C hC enum.injective enum.incident_eq_map hzero

/-- Enumeration form of the full-zero-boundary-set CAP5 parity theorem. -/
theorem cap5BoundaryWord_hasOddColorCounts_of_isTaitEdgeColoring_of_mem_zeroBoundarySet_at
    {U : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet) :
    CAP5BoundaryWordHasOddColorCounts (cap5BoundaryWordOfEdges enum.boundaryEdge C) :=
  enum.cap5BoundaryWord_hasOddColorCounts_of_isTaitEdgeColoring_of_isZeroBoundary_at C hC
    hzero.1

/-- Enumeration form of the graph-facing CAP5 block classifier. -/
theorem cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    {U : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C) (hzero : D.isZeroBoundary C) :
    CAP5BoundaryWordHasColoredBlock311 (cap5BoundaryWordOfEdges enum.boundaryEdge C) ∨
      CAP5BoundaryWordHasColoredBlock2111 (cap5BoundaryWordOfEdges enum.boundaryEdge C) :=
  cap5BoundaryWordOfEdges_coloredBlock311_or_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    enum.boundaryEdge C hC enum.injective enum.incident_eq_map hzero

/-- Enumeration form of the full-zero-boundary-set CAP5 block classifier. -/
theorem cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_isTaitEdgeColoring_of_mem_zeroBoundarySet_at
    {U : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet) :
    CAP5BoundaryWordHasColoredBlock311 (cap5BoundaryWordOfEdges enum.boundaryEdge C) ∨
      CAP5BoundaryWordHasColoredBlock2111 (cap5BoundaryWordOfEdges enum.boundaryEdge C) :=
  enum.cap5BoundaryWord_coloredBlock311_or_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    C hC hzero.1

/-- Enumeration form of the graph-facing CAP5 nonextension criterion. -/
theorem cap5BoundaryWord_not_extendsAcrossCycle_iff_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    {U : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C) (hzero : D.isZeroBoundary C) :
    ¬ CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges enum.boundaryEdge C) ↔
      CAP5BoundaryWordHasColoredBlock2111 (cap5BoundaryWordOfEdges enum.boundaryEdge C) :=
  cap5BoundaryWordOfEdges_not_extendsAcrossCycle_iff_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    enum.boundaryEdge C hC enum.injective enum.incident_eq_map hzero

/-- Enumeration form of the full-zero-boundary-set CAP5 nonextension criterion. -/
theorem cap5BoundaryWord_not_extendsAcrossCycle_iff_coloredBlock2111_of_isTaitEdgeColoring_of_mem_zeroBoundarySet_at
    {U : Type*} [DecidableEq V] {G : SimpleGraph V}
    {D : ZeroBoundaryData U G.edgeSet} {v : U}
    (enum : CAP5BoundaryEdgeEnumeration (D.incident v)) (C : G.EdgeColoring Color)
    (hC : IsTaitEdgeColoring G C)
    (hzero : (C : G.edgeSet → Color) ∈ D.zeroBoundarySet) :
    ¬ CAP5WordExtendsAcrossCycle (cap5BoundaryWordOfEdges enum.boundaryEdge C) ↔
      CAP5BoundaryWordHasColoredBlock2111 (cap5BoundaryWordOfEdges enum.boundaryEdge C) :=
  enum.cap5BoundaryWord_not_extendsAcrossCycle_iff_coloredBlock2111_of_isTaitEdgeColoring_of_isZeroBoundary_at
    C hC hzero.1

end CAP5BoundaryEdgeEnumeration

end Mettapedia.GraphTheory.FourColor
