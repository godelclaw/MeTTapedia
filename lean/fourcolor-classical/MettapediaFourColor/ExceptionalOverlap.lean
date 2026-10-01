import MettapediaFourColor.ExceptionalPattern

/-!
# Two actual exceptional occurrences force the extra corner

The source word has two fives on either side of each seven. Applied at the
specified second centre, this forces the degree-five corner in Figure 13 of
arXiv:2603.24880v1. Triangular face closure supplies its second edge.

The resulting degree-preserving graph homomorphism reads the exact internal
graph of D1774. It is not yet an injective occurrence with the eleven-port
ring or a colouring reconstruction theorem. Those obligations are retained.
-/

namespace FourColor.ExceptionalOverlap

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalPattern LocalCoverageAssembly

set_option maxRecDepth 32768

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite] (rotation : Data G)

/-- Three face-successor steps return to the original actual dart. -/
def Triangular : Prop := ∀ d : G.Dart,
  rotation.vertexRotation (rotation.vertexRotation (rotation.vertexRotation d.symm).symm).symm = d

theorem previous_fst (d : G.Dart) :
    (rotation.vertexRotation.symm d).fst = d.fst := by
  have h := rotation.vertexRotation_fst (rotation.vertexRotation.symm d)
  simpa using h.symm

/-- This edge is derived from triangular face closure, not added as a
free adjacency hypothesis about the new corner. -/
theorem consecutive_adjacent (tri : Triangular rotation) (d : G.Dart) :
    G.Adj d.snd (rotation.vertexRotation d).snd := by
  have he := congrArg (fun e : G.Dart => e.fst) (tri d.symm)
  simp only [SimpleGraph.Dart.symm_symm, rotation.vertexRotation_fst] at he
  change (rotation.vertexRotation (rotation.vertexRotation d).symm).snd = d.snd at he
  have ha := (rotation.vertexRotation (rotation.vertexRotation d).symm).adj
  rw [rotation.vertexRotation_fst, he] at ha
  exact ha.symm

variable {rotation} (x : Occurrence rotation)

/-- The missing corner immediately precedes vertex 15 around vertex 14. -/
def closingDart : G.Dart :=
  rotation.vertexRotation.symm (x.dart 14 15 (by decide +kernel))

theorem closing_fst : (closingDart x).fst = x.vertex 14 := previous_fst _ _

theorem closing_edges (tri : Triangular rotation) :
    G.Adj (x.vertex 14) (closingDart x).snd ∧
      G.Adj (x.vertex 15) (closingDart x).snd := by
  constructor
  · simpa [closing_fst] using (closingDart x).adj
  · have h := consecutive_adjacent rotation tri (closingDart x)
    simpa [closingDart, Occurrence.dart] using h.symm

variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- The second occurrence is anchored at the first one's specified vertex;
the same actual dart carries the degree observation across the overlap. -/
theorem closing_degree (cyclic : rotation.IsVertexwiseCyclic)
    (y : Occurrence rotation) (aligned : y.vertex 0 = x.vertex 14) :
    G.degree (closingDart x).snd = 5 := by
  let d := x.dart 14 5 (by decide +kernel)
  have hd : d.fst = y.vertex 0 := aligned.symm
  have h7 : G.degree d.snd = 7 := x.degree 5
  have h := y.seven_previous_two cyclic d hd h7
  have step : rotation.vertexRotation (x.dart 14 15 (by decide +kernel)) = d :=
    x.turn 14 15 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
  have prev : rotation.vertexRotation.symm d = x.dart 14 15 (by decide +kernel) := by
    rw [← step, Equiv.symm_apply_apply]
  have transport := congrArg (fun e : G.Dart =>
    G.degree (rotation.vertexRotation.symm e).snd) prev
  exact transport.symm.trans h

/-- An exact source occurrence centred at an actual vertex. -/
def Centered (rotation : Data G) (c : V) :=
  {x : Occurrence rotation // x.vertex 0 = c}

def Mate (c : V) (x : Centered rotation c) (u : V) : Prop := u = x.val.vertex 14

/-- The `next` field of the coverage scaffold is discharged for the source
pattern, using an actual graph walk and actual prescribed degree. -/
theorem next_centered (c : V) (x : Centered rotation c) :
    ∃ u ∈ closedBall G c 2, G.degree u = 8 ∧ Mate c x u := by
  obtain ⟨hnear, hdegree⟩ := x.val.next_centre
  refine ⟨x.val.vertex 14, ?_, hdegree, rfl⟩
  simpa only [x.property] using hnear

end FourColor.ExceptionalOverlap
