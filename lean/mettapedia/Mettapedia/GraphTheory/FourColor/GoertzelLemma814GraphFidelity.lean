import Mathlib.Tactic.DeriveFintype
import Mettapedia.GraphTheory.EdgeColoring
import Mettapedia.GraphTheory.Kempe
import Mettapedia.GraphTheory.FourColor.GoertzelLemma814

namespace Mettapedia.GraphTheory.FourColor

/-!
# Lemma 8.14 finite incidence and graph semantics

This module proves that the 192 `TauState` color functions are exactly the
proper colorings of the stored tau incidence table. It also defines the actual
simple-graph realization and input-avoiding Kempe-step semantics used to prove
the certificate's graph fidelity.
-/

namespace GoertzelLemma814GraphFidelity

open GoertzelLemma814

deriving instance Fintype for LColor
deriving instance Fintype for TauEdge

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Properness of an arbitrary color function on the stored tau incidence
table, without assuming that it came from `TauState`. -/
def tauIncidenceProperColoringCheck (C : TauEdge → LColor) : Bool :=
  tauVertices.all fun v =>
    match incidentEdges v with
    | [e₀, e₁, e₂] => pairwiseDistinct3 (C e₀) (C e₁) (C e₂)
    | _ => false

/-- The color functions represented by the 192 encoded states. -/
def enumeratedTauColorings : List (TauEdge → LColor) :=
  allTauStates.map TauState.color

/-- Choose the orientation of the two colors other than `x` so that `y` is
first. -/
def swapForFirst (x y : LColor) : Bool :=
  y == (otherPair x).2

theorem pairwiseDistinct3_rotate (x y z : LColor)
    (h : pairwiseDistinct3 x y z = true) :
    pairwiseDistinct3 y z x = true := by
  cases x <;> cases y <;> cases z <;>
    simp_all [pairwiseDistinct3, colorEq]

theorem orderedOtherPair_swapForFirst_eq (x y z : LColor)
    (h : pairwiseDistinct3 y z x = true) :
    orderedOtherPair x (swapForFirst x y) = (y, z) := by
  cases x <;> cases y <;> cases z <;>
    simp_all [pairwiseDistinct3, colorEq, orderedOtherPair, otherPair, swapForFirst]

theorem centralAdjacentChoice (x y z u v : LColor)
    (hxyz : pairwiseDistinct3 x y z = true)
    (hvux : pairwiseDistinct3 v u x = true) :
    (if u == y then y else z) = u ∧
      (if u == y then z else y) = v := by
  cases x <;> cases y <;> cases z <;> cases u <;> cases v <;>
    simp_all [pairwiseDistinct3, colorEq]

theorem f2Triple_mem_f2Triples_of_pairwiseDistinct3 (x y z : LColor)
    (h : pairwiseDistinct3 x y z = true) :
    ({ e02 := x, e23 := y, e24 := z } : F2Triple) ∈ f2Triples := by
  cases x <;> cases y <;> cases z <;>
    simp_all [pairwiseDistinct3, colorEq, f2Triples]

theorem mem_bindList_of_mem {xs : List α} {f : α → List β}
    {x : α} {y : β} (hx : x ∈ xs) (hy : y ∈ f x) :
    y ∈ bindList xs f := by
  induction xs with
  | nil => simp at hx
  | cons head tail ih =>
      simp only [List.mem_cons] at hx
      simp only [bindList, List.foldr_cons, List.mem_append]
      rcases hx with rfl | hx
      · exact Or.inl hy
      · exact Or.inr (ih hx)

theorem bool_mem_bools (value : Bool) : value ∈ bools := by
  cases value <;> simp [bools]

theorem tauState_mem_allTauStates_of_f2_mem
    (f2 : F2Triple) (hf2 : f2 ∈ f2Triples)
    (e10UsesE23 b1b2Swap b3b4Swap f4Swap b5b6Swap : Bool) :
    ({ f2 := f2
       e10UsesE23 := e10UsesE23
       b1b2Swap := b1b2Swap
       b3b4Swap := b3b4Swap
       f4Swap := f4Swap
       b5b6Swap := b5b6Swap } : TauState) ∈ allTauStates := by
  unfold allTauStates
  apply mem_bindList_of_mem hf2
  apply mem_bindList_of_mem (bool_mem_bools e10UsesE23)
  apply mem_bindList_of_mem (bool_mem_bools b1b2Swap)
  apply mem_bindList_of_mem (bool_mem_bools b3b4Swap)
  apply mem_bindList_of_mem (bool_mem_bools f4Swap)
  exact List.mem_map.2 ⟨b5b6Swap, bool_mem_bools b5b6Swap, rfl⟩

/-- Decode the five finite choices from an arbitrary incidence coloring. -/
def decodeTauState (C : TauEdge → LColor) : TauState where
  f2 :=
    { e02 := C TauEdge.F0F2
      e23 := C TauEdge.F2F3
      e24 := C TauEdge.F2F4 }
  e10UsesE23 := C TauEdge.F1F0 == C TauEdge.F2F3
  b1b2Swap := swapForFirst (C TauEdge.F1F0) (C TauEdge.B1)
  b3b4Swap := swapForFirst (C TauEdge.F2F3) (C TauEdge.B3)
  f4Swap := swapForFirst (C TauEdge.F2F4) (C TauEdge.F4F5)
  b5b6Swap := swapForFirst (C TauEdge.F4F5) (C TauEdge.B5)

theorem decodeTauState_mem_allTauStates (C : TauEdge → LColor)
    (hC : tauIncidenceProperColoringCheck C = true) :
    decodeTauState C ∈ allTauStates := by
  unfold tauIncidenceProperColoringCheck at hC
  have hF2 := (List.all_eq_true.mp hC) TauVertex.F2 (by simp [tauVertices])
  change pairwiseDistinct3 (C TauEdge.F0F2) (C TauEdge.F2F3)
    (C TauEdge.F2F4) = true at hF2
  exact tauState_mem_allTauStates_of_f2_mem _
    (f2Triple_mem_f2Triples_of_pairwiseDistinct3 _ _ _ hF2) _ _ _ _ _

theorem decodeTauState_color (C : TauEdge → LColor)
    (hC : tauIncidenceProperColoringCheck C = true) :
    (decodeTauState C).color = C := by
  unfold tauIncidenceProperColoringCheck at hC
  have hAll := List.all_eq_true.mp hC
  have hF0 := hAll TauVertex.F0 (by simp [tauVertices])
  have hF1 := hAll TauVertex.F1 (by simp [tauVertices])
  have hF2 := hAll TauVertex.F2 (by simp [tauVertices])
  have hF3 := hAll TauVertex.F3 (by simp [tauVertices])
  have hF4 := hAll TauVertex.F4 (by simp [tauVertices])
  have hF5 := hAll TauVertex.F5 (by simp [tauVertices])
  change pairwiseDistinct3 (C TauEdge.B0) (C TauEdge.F1F0)
    (C TauEdge.F0F2) = true at hF0
  change pairwiseDistinct3 (C TauEdge.B1) (C TauEdge.B2)
    (C TauEdge.F1F0) = true at hF1
  change pairwiseDistinct3 (C TauEdge.F0F2) (C TauEdge.F2F3)
    (C TauEdge.F2F4) = true at hF2
  change pairwiseDistinct3 (C TauEdge.B3) (C TauEdge.B4)
    (C TauEdge.F2F3) = true at hF3
  change pairwiseDistinct3 (C TauEdge.F2F4) (C TauEdge.F4F5)
    (C TauEdge.B7) = true at hF4
  change pairwiseDistinct3 (C TauEdge.F4F5) (C TauEdge.B5)
    (C TauEdge.B6) = true at hF5
  have hCentral := centralAdjacentChoice _ _ _ _ _ hF2 hF0
  have hPair1 := orderedOtherPair_swapForFirst_eq _ _ _ hF1
  have hPair3 := orderedOtherPair_swapForFirst_eq _ _ _ hF3
  have hPair4 := orderedOtherPair_swapForFirst_eq _ _ _
    (pairwiseDistinct3_rotate _ _ _ hF4)
  have hPair5 := orderedOtherPair_swapForFirst_eq _ _ _
    (pairwiseDistinct3_rotate _ _ _ hF5)
  have hE10 : (decodeTauState C).e10 = C TauEdge.F1F0 := by
    change (if C TauEdge.F1F0 == C TauEdge.F2F3 then
      C TauEdge.F2F3 else C TauEdge.F2F4) = C TauEdge.F1F0
    exact hCentral.1
  have hE45 : (decodeTauState C).e45 = C TauEdge.F4F5 := by
    change (orderedOtherPair (C TauEdge.F2F4)
      (swapForFirst (C TauEdge.F2F4) (C TauEdge.F4F5))).1 = C TauEdge.F4F5
    rw [hPair4]
  funext edge
  cases edge
  · exact hE10
  · rfl
  · rfl
  · rfl
  · exact hE45
  · change (if C TauEdge.F1F0 == C TauEdge.F2F3 then
        C TauEdge.F2F4 else C TauEdge.F2F3) = C TauEdge.B0
    exact hCentral.2
  · change (orderedOtherPair (decodeTauState C).e10
        (swapForFirst (C TauEdge.F1F0) (C TauEdge.B1))).1 = C TauEdge.B1
    rw [hE10, hPair1]
  · change (orderedOtherPair (decodeTauState C).e10
        (swapForFirst (C TauEdge.F1F0) (C TauEdge.B1))).2 = C TauEdge.B2
    rw [hE10, hPair1]
  · change (orderedOtherPair (C TauEdge.F2F3)
        (swapForFirst (C TauEdge.F2F3) (C TauEdge.B3))).1 = C TauEdge.B3
    rw [hPair3]
  · change (orderedOtherPair (C TauEdge.F2F3)
        (swapForFirst (C TauEdge.F2F3) (C TauEdge.B3))).2 = C TauEdge.B4
    rw [hPair3]
  · change (orderedOtherPair (decodeTauState C).e45
        (swapForFirst (C TauEdge.F4F5) (C TauEdge.B5))).1 = C TauEdge.B5
    rw [hE45, hPair5]
  · change (orderedOtherPair (decodeTauState C).e45
        (swapForFirst (C TauEdge.F4F5) (C TauEdge.B5))).2 = C TauEdge.B6
    rw [hE45, hPair5]
  · change (orderedOtherPair (C TauEdge.F2F4)
        (swapForFirst (C TauEdge.F2F4) (C TauEdge.F4F5))).2 = C TauEdge.B7
    rw [hPair4]

/-- Completeness of the finite incidence encoding: every arbitrary color
function proper at all stored cubic incidences is one of the enumerated
states. -/
theorem tauIncidenceProperColoring_mem_enumeratedTauColorings
    (C : TauEdge → LColor)
    (hC : tauIncidenceProperColoringCheck C = true) :
    C ∈ enumeratedTauColorings := by
  exact List.mem_map.2
    ⟨decodeTauState C, decodeTauState_mem_allTauStates C hC,
      decodeTauState_color C hC⟩

/-- The 192 represented color functions all pass the independent incidence
properness test. -/
theorem enumeratedTauColorings_proper_audit :
    enumeratedTauColorings.all tauIncidenceProperColoringCheck = true := by
  decide

/-- Soundness of the same incidence encoding. -/
theorem tauIncidenceProperColoring_of_mem_enumeratedTauColorings
    (C : TauEdge → LColor)
    (hC : C ∈ enumeratedTauColorings) :
    tauIncidenceProperColoringCheck C = true :=
  (List.all_eq_true.mp enumeratedTauColorings_proper_audit) C hC

/-- Exact completeness and soundness of the finite incidence encoding. -/
theorem tauIncidenceProperColoring_iff_mem_enumeratedTauColorings
    (C : TauEdge → LColor) :
    tauIncidenceProperColoringCheck C = true ↔ C ∈ enumeratedTauColorings :=
  ⟨tauIncidenceProperColoring_mem_enumeratedTauColorings C,
    tauIncidenceProperColoring_of_mem_enumeratedTauColorings C⟩

/-- The exact census contains 192 distinct color functions. -/
theorem enumeratedTauColorings_length_and_nodup :
    enumeratedTauColorings.length = 192 ∧ enumeratedTauColorings.Nodup := by
  decide

/-- A certificate move uses a listed unequal color pair and a listed tau edge
as its seed. -/
def certificateMoveInEncodedDomain (move : KempeMove) : Bool :=
  colorPairs.contains (move.a, move.c) && tauEdges.contains move.seed

def certificateRowMovesInEncodedDomain (row : IndexedPathRow) : Bool :=
  row.steps.all fun pathStep => certificateMoveInEncodedDomain pathStep.move

def lemma814CertificateMoveDomainAudit : Bool :=
  lemma814PathCertificate.all certificateRowMovesInEncodedDomain

theorem lemma814CertificateMoveDomainAudit_ok :
    lemma814CertificateMoveDomainAudit = true := by
  decide

/-- Data identifying the encoded tau edges and state colorings with an actual
simple graph.  The compatibility field only identifies colors; it does not
assume any Kempe-connectivity conclusion. -/
structure TauGraphRealization where
  Vertex : Type
  graph : SimpleGraph Vertex
  edgeEquiv : graph.edgeSet ≃ TauEdge
  coloring : TauState → graph.EdgeColoring LColor
  coloring_eq : ∀ state edge,
    coloring state edge = state.color (edgeEquiv edge)

/-- One graph-level Kempe switch whose component avoids the four input edges
identified by the tau edge equivalence. -/
noncomputable def TauGraphRealization.inputAvoidingKempeStep
    (realization : TauGraphRealization) (source target : TauState)
    (move : KempeMove) : Prop :=
  ∃ component :
      ((realization.coloring source).bicoloredSubgraph move.a move.c).ConnectedComponent,
    (∀ edge, realization.edgeEquiv edge ∈ tauInputEdges →
      edge ∉ (realization.coloring source).kempeComponentSet
        move.a move.c component) ∧
    realization.coloring target =
      (realization.coloring source).swapOnKempeComponent
        move.a move.c component

end GoertzelLemma814GraphFidelity

end Mettapedia.GraphTheory.FourColor
