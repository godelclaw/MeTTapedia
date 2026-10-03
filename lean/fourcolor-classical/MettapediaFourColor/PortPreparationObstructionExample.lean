import MettapediaFourColor.PortPreparationObstruction
import Mettapedia.GraphTheory.FourColor.ComponentDetachExample

/-!
# A physical failed preparation and a successful alternative

The existing 155-vertex exterior is reused. Three saturated chains certify
actual component switches: the failed one/two preparation and a different
two-step repair. The alternative reconstructs a colouring of the existing
162-vertex ambient graph. The sphere rotation is checked separately by the
companion program; the adjacency and colouring assertions here are kernel
checked.
-/

namespace FourColor.PortPreparationObstruction.Example

open SimpleGraph Color KempeDetachExample

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def colourData : List Nat := [1775001217671792315281037652807723804282385295955099306113590225642321727963946165080248301356, 1881574104028610998005057220565087663896053604657351086089956897725103258287291006575973512988, 1775001217671792315281038515526016349633836595804444319760725611449641988160768668999358625580, 1775001217671792315281038515526016349633836595804444319760725611444690228003627147899762128684]

def completeData : Nat := 29081619950334645293564535038378252234216184405772901912222644311621913371574366834040155060362428

def trace0 : List (Fin 155) := [97, 82, 28, 66, 28, 82, 63, 55, 128, 61, 117, 108, 102, 144, 102, 108, 111, 23, 49, 151, 84, 124, 80, 101, 47, 146, 21, 32, 99, 16, 99, 71, 51, 71, 99, 32, 21, 146, 47, 101, 80, 124, 103, 153, 2, 153, 10, 59, 74, 59, 10, 148, 152, 90, 85, 149, 86, 127, 140, 145, 140, 127, 86, 149, 85, 90, 152, 148, 10, 153, 103, 124, 84, 151, 49, 23, 111, 50, 83, 22, 48, 38, 48, 22, 77, 81, 134, 81, 77, 22, 129, 22, 83, 50, 111, 108, 117, 61, 128, 55, 63, 82, 97]

def trace1 : List (Fin 155) := [114, 99, 114]

def trace2 : List (Fin 155) := [46]

def palette : Fin 4 → Color := ![c0,c1,c2,c3]
def values (i : Fin 4) (v : Fin 155) : Color :=
  palette ⟨(colourData.get ⟨i.val,i.isLt⟩ >>> (2*v.val)) % 4, Nat.mod_lt _ (by decide)⟩

theorem proper_edges : ∀ i : Fin 4, ∀ e ∈ edges, values i e.1 ≠ values i e.2 := by
  have h : ∀ i : Fin 4, edges.all (fun e => decide (values i e.1 ≠ values i e.2)) = true := by
    decide +kernel
  exact fun i e he => of_decide_eq_true (List.all_eq_true.mp (h i) e he)

def state (i : Fin 4) : graph.Coloring Color := .mk (values i) (by
  intro u v edge
  rcases edge with edge | edge
  · exact proper_edges i _ edge
  · exact (proper_edges i _ edge).symm)

def boundaryPorts (j : Fin 11) : Fin 155 := ports.get j

def before (i : Fin 3) := state (if i = 2 then 2 else 0)
def after (i : Fin 3) := state i.succ
def leftColour (i : Fin 3) : Color := if i = 1 then c0 else c1

def trace (i : Fin 3) : List (Fin 155) :=
  if i = 0 then trace0 else if i = 1 then trace1 else trace2

def root (i : Fin 3) : Fin 155 := ![97,114,46] i

theorem root_mem : ∀ i, root i ∈ trace i := by decide +kernel
theorem connected : ∀ i, (trace i).IsChain graph.Adj := by decide +kernel
theorem active : ∀ i, ∀ v ∈ trace i,
    before i v = leftColour i ∨ before i v = c2 := by decide +kernel

def component (i : Fin 3) : ((before i).bicoloredSubgraph (leftColour i) c2).ConnectedComponent :=
  ((before i).bicoloredSubgraph (leftColour i) c2).connectedComponentMk
    ⟨root i, active i _ (root_mem i)⟩

theorem root_component (i : Fin 3) :
    root i ∈ (before i).kempeComponentSet (leftColour i) c2 (component i) :=
  (before i).mem_kempeComponentSet_self (active i _ (root_mem i))

def ClosedEdge (i : Fin 3) (u v : Fin 155) : Prop :=
  u ∈ trace i → (before i v = leftColour i ∨ before i v = c2) → v ∈ trace i
instance (i u v) : Decidable (ClosedEdge i u v) := inferInstanceAs (Decidable (_ → _ → _))

theorem closed_edges : ∀ i, ∀ e ∈ edges, ClosedEdge i e.1 e.2 ∧ ClosedEdge i e.2 e.1 := by
  have h : ∀ i, edges.all (fun e => decide (ClosedEdge i e.1 e.2 ∧ ClosedEdge i e.2 e.1)) = true := by
    decide +kernel
  exact fun i e he => of_decide_eq_true (List.all_eq_true.mp (h i) e he)

theorem closed (i : Fin 3) : ∀ u ∈ trace i, ∀ v, graph.Adj u v →
    (before i v = leftColour i ∨ before i v = c2) → v ∈ trace i := by
  intro u hu v edge hv
  exact on_edges _ (closed_edges i) u v edge hu hv

theorem component_iff (i : Fin 3) (v : Fin 155) :
    v ∈ (before i).kempeComponentSet (leftColour i) c2 (component i) ↔ v ∈ trace i :=
  (before i).kempe_component_iff_mem_chain _ _ _ _ (connected i) (active i) (closed i)
    (root_mem i) (root_component i) v

theorem next_values : ∀ i v, after i v =
    if v ∈ trace i then Equiv.swap (leftColour i) c2 (before i v) else before i v := by
  decide +kernel

theorem switch_eq (i : Fin 3) :
    (before i).swapOnKempeComponent (leftColour i) c2 (component i) = after i := by
  ext v
  rw [(before i).swap_apply_of_chain _ _ _ _ (connected i) (active i) (closed i)
    (root_mem i) (root_component i), next_values]

theorem physical_step (i : Fin 3) : graph.KempeStep (before i) (after i) :=
  ⟨leftColour i,c2,component i,(switch_eq i).symm⟩

theorem initial_boundary : ∀ j, state 0 (boundaryPorts j) =
    ThreeBlockCore.word false false false j := by decide +kernel

theorem preparing_ports : ∀ j, boundaryPorts j ∈ trace 0 ↔ j = 2 ∨ j = 4 := by
  decide +kernel

theorem prepared_boundary : ∀ j, state 1 (boundaryPorts j) = word false false j := by
  decide +kernel

theorem preparing_component_ports : ∀ j, boundaryPorts j ∈
    (state 0).kempeComponentSet c1 c2 (component 0) ↔ j = 2 ∨ j = 4 := by
  intro j
  exact (component_iff 0 _).trans (preparing_ports j)

def joiningPath : graph.Walk (boundaryPorts 1) (boundaryPorts 6) :=
  (.cons (show graph.Adj 40 43 by decide +kernel)
  (.cons (show graph.Adj 43 79 by decide +kernel)
  (.cons (show graph.Adj 79 107 by decide +kernel)
  (.cons (show graph.Adj 107 154 by decide +kernel)
  (.cons (show graph.Adj 154 2 by decide +kernel)
  (.cons (show graph.Adj 2 4 by decide +kernel)
  (.cons (show graph.Adj 4 51 by decide +kernel)
  (.cons (show graph.Adj 51 30 by decide +kernel)
  (.cons (show graph.Adj 30 47 by decide +kernel)
  (.cons (show graph.Adj 47 137 by decide +kernel)
  (.cons (show graph.Adj 137 21 by decide +kernel)
  (.cons (show graph.Adj 21 68 by decide +kernel)
  (.cons (show graph.Adj 68 99 by decide +kernel)
  (.cons (show graph.Adj 99 17 by decide +kernel) .nil))))))))))))))

theorem joiningPath_active : ∀ v ∈ joiningPath.support, state 1 v = c1 ∨ state 1 v = c3 := by
  decide +kernel

/-- The useful complementary connection survives, but the additional
changed port defeats every following zero/two phase. -/
theorem failed_preparation (E : graph.Coloring Color)
    (history : Relation.ReflTransGen (KempePairHistory.Step c0 c2) (state 1) E)
    (K : FiveTriangleCollapseObstruction.upper.graph.Coloring Color)
    (agree : ∀ j : Fin 11, K (j.castAdd 7) = E (boundaryPorts j)) : False :=
  no_tail_phase (state 1) E boundaryPorts prepared_boundary
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    history K agree

def sourcePoint : Fin 18 → Fin 162 :=
  ![45,42,102,104,18,121,19,48,51,113,15,47,49,50,1,12,105,103]

theorem source_edges : ∀ u v, FiveTriangleCollapseObstruction.upper.graph.Adj u v →
    ambient.Adj (sourcePoint u) (sourcePoint v) := by decide +kernel

theorem source_boundary : ∀ j : Fin 11,
    includeExterior (boundaryPorts j) = sourcePoint (j.castAdd 7) := by decide +kernel

/-- Failure concerns the actual ambient graph, not only an abstract copy
of the patch: every whole colouring would restrict to the rejected core. -/
theorem failed_whole_preparation (E : graph.Coloring Color)
    (history : Relation.ReflTransGen (KempePairHistory.Step c0 c2) (state 1) E)
    (K : ambient.Coloring Color) (agree : ∀ v, K (includeExterior v) = E v) : False := by
  let source : FiveTriangleCollapseObstruction.upper.graph.Coloring Color :=
    .mk (fun i => K (sourcePoint i)) (fun h => K.valid (source_edges _ _ h))
  apply failed_preparation E history source
  intro j
  change K (sourcePoint (j.castAdd 7)) = E (boundaryPorts j)
  rw [← source_boundary]
  exact agree (boundaryPorts j)

def completedValues (v : Fin 162) : Color :=
  palette ⟨(completeData >>> (2*v.val)) % 4, Nat.mod_lt _ (by decide)⟩

theorem completed_edges : ∀ e ∈ ambientEdges, completedValues e.1 ≠ completedValues e.2 := by
  have h : ambientEdges.all (fun e => decide (completedValues e.1 ≠ completedValues e.2)) = true := by
    decide +kernel
  exact fun e he => of_decide_eq_true (List.all_eq_true.mp h e he)

def completed : ambient.Coloring Color := .mk completedValues (by
  intro u v edge
  rcases edge with edge | edge
  · exact completed_edges _ edge
  · exact (completed_edges _ edge).symm)

theorem completed_agrees : ∀ v, completed (includeExterior v) = state 3 v := by decide +kernel

/-- Two different physical switches colour this very same ambient graph. -/
theorem alternative_repair : ∃ D E : graph.Coloring Color,
    graph.KempeStep (state 0) D ∧ graph.KempeStep D E ∧
      ∃ K : ambient.Coloring Color, ∀ v, K (includeExterior v) = E v :=
  ⟨state 2,state 3,physical_step 1,physical_step 2,completed,completed_agrees⟩

end FourColor.PortPreparationObstruction.Example
