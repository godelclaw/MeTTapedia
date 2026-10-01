import Mettapedia.GraphTheory.FourColor.CappedLadderEndReduction

/-!
# Compatible construction paths for the complete capped-ladder family

One end-insertion law reconstructs every width from the two-vertex,
three-edge base. States retain their genuine source colouring witnesses;
events retain the exact reconstruction. Reversing these structural steps
removes six expanded vertices at a time, terminating at the base.

Coverage here is the literal capped-ladder family. No occurrence claim for
arbitrary spherical maps or reduction of the unavoidable catalogue follows.
-/

namespace Mettapedia.GraphTheory.FourColor.CappedLadderFamilyGSLT

open CappedLadderRotation DualTruncateColoring
open Mettapedia.GSLT Mettapedia.GSLT.Ultrainfinite Mettapedia.GSLT.ProofRelevantPresentation

noncomputable section

/-- The finite base retains all three parallel edge identities. -/
def baseWitness : ThreeVertexColoring (source 1) where
  colour := fun v => ![red,blue] v
  nonzero := by intro v; fin_cases v <;> decide +kernel
  proper := by rintro ⟨v,i⟩; fin_cases v <;> fin_cases i <;> decide +kernel

abbrev State := Σ k : ℕ, ThreeVertexColoring (source (k+1))

def base : State := ⟨0,baseWitness⟩

/-- The original witness supplies both new vertex choices jointly. -/
def grow (s : State) : State := ⟨s.1+1,CappedLadderEndReduction.restored (s.1+1) s.2⟩

abbrev Event (s t : State) : Type := ULift (PLift (t = grow s))

def theory : GSLT where
  Term := State
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun s t => Nonempty (Event s t)
  rewrites_resp_left := by
    intro s s' t equal event
    subst s'
    exact ⟨t,event,rfl⟩
  rewrites_resp_right := by
    intro s t t' event equal
    subst t'
    exact event

def presentation : StepPresentation theory where
  Evidence := Event
  erases_iff := fun _ _ => Iff.rfl

/-- One event preserves the actual shared choices at every retained vertex. -/
theorem grow_retained (s : State) (v : Vertex (s.1+1)) :
    (grow s).2.colour (CappedLadderEndReduction.embed (s.1+1) v) = s.2.colour v :=
  CappedLadderEndReduction.restored_retained _ _ _

theorem event_width {s t : State} (event : Event s t) : t.1 = s.1+1 := by
  rw [event.down.down]
  rfl

/-- A step carries the same exact old-dart sewing as the geometric law. -/
theorem event_operation {s t : State} (event : Event s t) :
    t.1 = s.1+1 ∧
      (∀ d : CappedLadderEndReduction.RetainedDart (s.1+1),
        (CappedLadderEndReduction.sewnAlpha (s.1+1) d).val =
          CappedLadderEndReduction.sewnFlip (s.1+1) d.val) ∧
      Fintype.card (source (s.1+1)).D + 6 = Fintype.card (source (s.1+1+1)).D :=
  ⟨event_width event, (CappedLadderEndReduction.strict_operation (s.1+1)).1,
    CappedLadderEndReduction.target_vertices_removed _⟩

def advance : (s : State) → (steps : ℕ) → Route Event s ((grow^[steps]) s)
  | s, 0 => .refl s
  | s, steps+1 => by
      rw [Function.iterate_succ_apply]
      exact .cons ⟨⟨rfl⟩⟩ (advance (grow s) steps)

theorem advance_length (s : State) (steps : ℕ) : (advance s steps).length = steps := by
  induction steps generalizing s with
  | zero => rfl
  | succ steps ih =>
    change (advance (grow s) steps).length+1 = steps+1
    rw [ih]

def state (k : ℕ) : State := (grow^[k]) base

theorem state_succ (k : ℕ) : state (k+1) = grow (state k) := by
  exact Function.iterate_succ_apply' grow k base

theorem state_width (k : ℕ) : (state k).1 = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [state_succ]; change (state k).1+1 = k+1; rw [ih]

def construction (k : ℕ) : Route Event base (state k) := advance base k

theorem construction_length (k : ℕ) : (construction k).length = k := advance_length base k

/-- Every family member receives its witness from the same authored path. -/
def witness (k : ℕ) : ThreeVertexColoring (source (k+1)) :=
  (state_width k) ▸ (state k).2

theorem target_tait (k : ℕ) : (rotation (source (k+1))).IsTaitEdgeColoring
    (colouring _ (witness k)) := colouring_nonzero _ _

theorem expanded_vertex_count (k : ℕ) : Fintype.card (source (k+1)).D = 6*(k+1) := by
  change Fintype.card (CappedLadderRotation.Dart (k+1)) = _
  simp only [CappedLadderRotation.Dart, Vertex, Fintype.card_prod, Fintype.card_fin]
  omega

/-- The reverse structural route has a strictly decreasing natural rank.
It reaches the six-vertex expanded base after exactly `k` reductions. -/
theorem reduction_rank {s t : State} (event : Event s t) : s.1 < t.1 := by
  rw [event_width event]
  omega

abbrev ReductionEvent (larger smaller : State) := Event smaller larger

def reverse : {s t : State} → Route Event s t → Route ReductionEvent t s
  | _, _, .refl s => .refl s
  | _, _, .cons event rest => (reverse rest).append (.cons event (.refl _))

theorem reverse_length {s t : State} (r : Route Event s t) : (reverse r).length = r.length := by
  induction r with
  | refl => rfl
  | cons event rest ih =>
    simp only [reverse, Route.length_append, Route.length, ih]

def reduction (k : ℕ) : Route ReductionEvent (state k) base := reverse (construction k)

theorem reduction_length (k : ℕ) : (reduction k).length = k :=
  (reverse_length (construction k)).trans (construction_length k)

/-- Every structural reduction decreases the natural width rank, so no
infinite sequence of these reductions is possible. -/
theorem reduction_wellFounded :
    WellFounded (fun smaller larger : State => Nonempty (ReductionEvent larger smaller)) := by
  exact (measure (fun s : State => s.1)).wf.mono (fun _ _ ⟨event⟩ => reduction_rank event)

theorem base_target_count : Fintype.card (source 1).D = 6 := by
  exact expanded_vertex_count 0

theorem unbounded_vertices (bound : ℕ) : ∃ k,
    bound < Fintype.card (source (k+1)).D := by
  refine ⟨bound, ?_⟩
  rw [expanded_vertex_count]
  omega

open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace VertexConstructionGSLT

/-- The constructed witnesses support every complete faithful sweep of
the actual expanded graph, including intermediate boundary constraints. -/
theorem every_complete_sweep (k : ℕ) (order : List (source (k+1)).D)
    (hn : order.Nodup) (he : order ≠ []) (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (VertexConstructionGSLT.route (SourceVertexCodeTrace.encodeClosed
        (DualTruncateColoring.cubic (source (k+1)))
        (DualTruncateConstructionGSLT.rotationCyclic (source (k+1)))
        order hn he hcover).trace) Fin.elim0 Fin.elim0 :=
  DualTruncateConstructionGSLT.supported_encoded_route _ (witness k) order hn he hcover

end
end Mettapedia.GraphTheory.FourColor.CappedLadderFamilyGSLT
