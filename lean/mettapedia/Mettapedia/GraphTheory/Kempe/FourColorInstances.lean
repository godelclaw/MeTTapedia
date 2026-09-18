import Mettapedia.GraphTheory.Kempe.Boundary
import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairKempeSwitchSquare
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarBridgeTarget
import Mettapedia.GraphTheory.FourColor.GoertzelLemma814GraphFidelity

/-!
# Earlier four-colour statements as instances of the boundary layer

* `SimpleGraph.Coloring.kempeStep_symm` and `SimpleGraph.Coloring.mem_kempeClosure_symm`
  are the generic `SimpleGraph.KempeStep.symm` and `SimpleGraph.KempeClosure.mem_symm`;
  the proofs are equated, so the statements cannot drift apart.
* `outerStubAvoidingEdgeKempeStep` is `EdgeKempeStepAvoiding` for the outer stubs,
  and the collar statement `manuscriptS2AllOuterStubsFixedForCollar` is
  `EdgeFibreConnected` for them.
* A certified move of a `TauGraphRealization` (`inputAvoidingKempeStep`) is an
  `EdgeKempeStepAvoiding` step for the edges identified with the four input
  stubs.
-/

namespace Mettapedia.GraphTheory.Kempe.FourColorInstances

open SimpleGraph Relation
open Mettapedia.Combinatorics.Reconfiguration
open Mettapedia.GraphTheory.FourColor

/-! ## Symmetry -/

theorem kempeStep_symm_eq :
    @SimpleGraph.Coloring.kempeStep_symm = @SimpleGraph.KempeStep.symm :=
  rfl

theorem mem_kempeClosure_symm_eq :
    @SimpleGraph.Coloring.mem_kempeClosure_symm = @SimpleGraph.KempeClosure.mem_symm :=
  rfl

/-! ## The collar statement S2 -/

section Collar

open GoertzelLemma814 GoertzelLemma818ClosedCollarBridgeTarget

variable {V : Type} {G : SimpleGraph V}

theorem outerStubAvoidingEdgeKempeStep_iff (outerStubs : Finset G.edgeSet)
    (C D : G.EdgeColoring LColor) :
    outerStubAvoidingEdgeKempeStep outerStubs C D ↔
      G.EdgeKempeStepAvoiding (↑outerStubs : Set G.edgeSet) C D := by
  constructor
  · rintro ⟨c₁, c₂, K, hK, rfl⟩
    exact ⟨c₁, c₂, K, Set.disjoint_right.2 fun e he => hK e he, rfl⟩
  · rintro ⟨c₁, c₂, K, hK, rfl⟩
    exact ⟨c₁, c₂, K, fun e he => Set.disjoint_right.1 hK he, rfl⟩

theorem edgeColoringsAgreeOnOuterStubs_iff (outerStubs : Finset G.edgeSet)
    (C D : G.EdgeColoring LColor) :
    edgeColoringsAgreeOnOuterStubs outerStubs C D ↔
      C.boundaryWord (↑outerStubs : Set G.edgeSet) =
        D.boundaryWord (↑outerStubs : Set G.edgeSet) :=
  Coloring.boundaryWord_eq_iff.symm

/-- **S2 is LKR_in for the outer stubs.** -/
theorem manuscriptS2AllOuterStubsFixedForCollar_iff (outerStubs : Finset G.edgeSet) :
    manuscriptS2AllOuterStubsFixedForCollar outerStubs ↔
      G.EdgeFibreConnected LColor (↑outerStubs : Set G.edgeSet) := by
  have hclosed : ∀ base : G.EdgeColoring LColor, ∀ x y : G.EdgeColoring LColor,
      edgeColoringsAgreeOnOuterStubs outerStubs base x →
      outerStubAvoidingEdgeKempeStep outerStubs x y →
      edgeColoringsAgreeOnOuterStubs outerStubs base y := by
    intro base x y hx hxy
    rw [edgeColoringsAgreeOnOuterStubs_iff] at hx ⊢
    rw [outerStubAvoidingEdgeKempeStep_iff] at hxy
    exact hx.trans hxy.boundaryWord_eq.symm
  constructor
  · intro h C D hCD
    have hpath := h C ⟨C, fun _ _ => rfl⟩
      ⟨D, (edgeColoringsAgreeOnOuterStubs_iff outerStubs C D).2 hCD⟩
    have hpath' := (reflTransGen_subtype_iff (S := edgeColoringsAgreeOnOuterStubs outerStubs C)
      (hclosed C) ⟨C, fun _ _ => rfl⟩
      ⟨D, (edgeColoringsAgreeOnOuterStubs_iff outerStubs C D).2 hCD⟩).1 hpath
    exact hpath'.mono fun a b hab => (outerStubAvoidingEdgeKempeStep_iff outerStubs a b).1 hab
  · intro h base x y
    have hword : x.1.boundaryWord (↑outerStubs : Set G.edgeSet) =
        y.1.boundaryWord (↑outerStubs : Set G.edgeSet) :=
      ((edgeColoringsAgreeOnOuterStubs_iff outerStubs _ _).1 x.2).symm.trans
        ((edgeColoringsAgreeOnOuterStubs_iff outerStubs _ _).1 y.2)
    exact (reflTransGen_subtype_iff (S := edgeColoringsAgreeOnOuterStubs outerStubs base)
      (hclosed base) x y).2 ((h x.1 y.1 hword).mono fun a b hab =>
        (outerStubAvoidingEdgeKempeStep_iff outerStubs a b).2 hab)

end Collar

/-! ## Certified moves of a gadget realization -/

section Tau

open GoertzelLemma814 GoertzelLemma814GraphFidelity

/-- The edges of a realization identified with the four input stubs. -/
def realizationInputEdges (r : TauGraphRealization) : Set r.graph.edgeSet :=
  {e | r.edgeEquiv e ∈ tauInputEdges}

theorem inputAvoidingKempeStep_kempeStepAvoiding (r : TauGraphRealization)
    {s t : TauState} {move : KempeMove} (h : r.inputAvoidingKempeStep s t move) :
    r.graph.EdgeKempeStepAvoiding (realizationInputEdges r) (r.coloring s) (r.coloring t) := by
  obtain ⟨K, hK, heq⟩ := h
  exact ⟨move.a, move.c, K, Set.disjoint_right.2 fun e he => hK e he, heq⟩

end Tau

end Mettapedia.GraphTheory.Kempe.FourColorInstances
