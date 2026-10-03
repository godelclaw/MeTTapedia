import Mettapedia.GraphTheory.FourColor.ComponentDetachAudit

/-!
# Two detachments compose into a smaller preparation

The first switch frees one vertex. Recolouring that singleton removes a
separator from another two-colour graph, enabling the final physical switch.
Both newly available components consume the same general detachment law.
The two silent preparations together touch five exterior vertices, and the
final boundary word reconstructs a colouring of the whole 162-vertex graph.
-/

namespace SimpleGraph.KempeCascadingDetach

open KempeDetachExample (graph ambient edges ambientEdges ports on_edges includeExterior)

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def colourData : List Nat := [1929953971212522539515696633843714435840570691384348618095707928955200070651606125604752147292,1929953971212522539515696633843714435840570691384348618095707928955204906354884584121450971996,1685235131629917464964204437402412379287958126336199938436906619131992756387531816296504714076]
def completeData : Nat := 27610892396624567745973525502401124765123737265907227682945205867893845653499802968839992987979132
def trace0 : List (Fin 155) := [126,15,53,115,53,15,126]
def trace1 : List (Fin 155) := [41]
def trace2 : List (Fin 155) := [6,23,111,50,87,22,25,148,105,145,94,90,85,72,124,80,34,51,62,146,47,146,62,51,106,13,27,42,91,42,27,13,106,46,45,46,106,70,118,70,106,51,34,153,104,33,104,153,34,80,124,84,151,84,124,72,85,125,127,75,59,109,59,75,127,125,85,90,94,145,105,148,25,22,48,38,133,24,133,38,48,122,81,120,113,126,9,126,135,19,135,126,113,120,81,122,48,22,87,50,111,92,111,23,6]

def values (i : Fin 3) (v : Fin 155) : Fin 4 :=
  ⟨(colourData.get ⟨i.val, i.isLt⟩ >>> (2 * v.val)) % 4, Nat.mod_lt _ (by decide)⟩

theorem proper_edges : ∀ i, ∀ e ∈ edges, values i e.1 ≠ values i e.2 := by
  have h : ∀ i, edges.all (fun e => decide (values i e.1 ≠ values i e.2)) = true := by decide +kernel
  exact fun i e he => of_decide_eq_true (List.all_eq_true.mp (h i) e he)

def after (i : Fin 3) : graph.Coloring (Fin 4) := .mk (values i) (by
  intro u v edge
  rcases edge with edge | edge
  · exact proper_edges i _ edge
  · exact (proper_edges i _ edge).symm)

def before (i : Fin 3) : graph.Coloring (Fin 4) :=
  if i = 0 then KempeDetachExample.state 0 else if i = 1 then after 0 else after 1

def firstColour (i : Fin 3) : Fin 4 := if i = 0 then 1 else 0
def secondColour (i : Fin 3) : Fin 4 := if i = 1 then 1 else 2
def trace (i : Fin 3) : List (Fin 155) := if i = 0 then trace0 else if i = 1 then trace1 else trace2
def root (i : Fin 3) : Fin 155 := (trace i).head!

theorem root_mem : ∀ i, root i ∈ trace i := by decide +kernel
theorem active : ∀ i, ∀ v ∈ trace i, before i v = firstColour i ∨ before i v = secondColour i := by decide +kernel
theorem connected : ∀ i, (trace i).IsChain graph.Adj := by decide +kernel

def component (i : Fin 3) :
    ((before i).bicoloredSubgraph (firstColour i) (secondColour i)).ConnectedComponent :=
  ((before i).bicoloredSubgraph _ _).connectedComponentMk ⟨root i, active i _ (root_mem i)⟩

theorem root_component (i) :
    root i ∈ (before i).kempeComponentSet (firstColour i) (secondColour i) (component i) :=
  (before i).mem_kempeComponentSet_self (active i _ (root_mem i))

def Closed (i : Fin 3) : Prop :=
  ∀ x ∈ trace i, ∀ y, graph.Adj x y →
    (before i y = firstColour i ∨ before i y = secondColour i) → y ∈ trace i

theorem component_iff (i) (closed : Closed i) (v) :
    v ∈ (before i).kempeComponentSet (firstColour i) (secondColour i) (component i) ↔ v ∈ trace i :=
  (before i).kempe_component_iff_mem_chain _ _ _ _ (connected i) (active i)
    closed (root_mem i) (root_component i) v

theorem next_values : ∀ i v, after i v =
    if v ∈ trace i then Equiv.swap (firstColour i) (secondColour i) (before i v) else before i v := by
  decide +kernel

theorem switch_eq (i) (closed : Closed i) :
    (before i).swapOnKempeComponent (firstColour i) (secondColour i) (component i) = after i := by
  ext v
  rw [(before i).swap_apply_of_chain _ _ _ _ (connected i) (active i)
    closed (root_mem i) (root_component i), next_values]

def FirstClosedEdge (x y : Fin 155) : Prop :=
  x ∈ trace 0 → (before 0 y = 1 ∨ before 0 y = 2) → y ∈ trace 0
instance (x y) : Decidable (FirstClosedEdge x y) := inferInstanceAs (Decidable (_ → _ → _))

theorem first_closed_edges : ∀ e ∈ edges, FirstClosedEdge e.1 e.2 ∧ FirstClosedEdge e.2 e.1 := by
  have h : edges.all (fun e => decide (FirstClosedEdge e.1 e.2 ∧ FirstClosedEdge e.2 e.1)) = true := by decide +kernel
  exact fun e he => of_decide_eq_true (List.all_eq_true.mp h e he)

theorem first_closed : Closed 0 := by
  intro x hx y edge active
  exact on_edges _ first_closed_edges x y edge hx active

/-- Each next region is separated from the old active graph only by vertices
of the preceding component. All observations are made before that switch. -/
def Exits (i : Fin 2) (x y : Fin 155) : Prop :=
  x ∈ trace i.succ → y ∉ trace i.succ →
    (before i.castSucc y = firstColour i.succ ∨ before i.castSucc y = secondColour i.succ) →
    y ∈ trace i.castSucc

def NoEntry (i : Fin 2) (x y : Fin 155) : Prop :=
  x ∈ trace i.succ → y ∈ trace i.castSucc → before i.castSucc y ≠ secondColour i.castSucc

instance (i x y) : Decidable (Exits i x y) := inferInstanceAs (Decidable (_ → _ → _ → _))
instance (i x y) : Decidable (NoEntry i x y) := inferInstanceAs (Decidable (_ → _ → _))

theorem old_exits : ∀ i, ∀ e ∈ edges, Exits i e.1 e.2 ∧ Exits i e.2 e.1 := by
  have h : ∀ i, edges.all (fun e => decide (Exits i e.1 e.2 ∧ Exits i e.2 e.1)) = true := by decide +kernel
  exact fun i e he => of_decide_eq_true (List.all_eq_true.mp (h i) e he)
theorem no_entry : ∀ i, ∀ e ∈ edges, NoEntry i e.1 e.2 ∧ NoEntry i e.2 e.1 := by
  have h : ∀ i, edges.all (fun e => decide (NoEntry i e.1 e.2 ∧ NoEntry i e.2 e.1)) = true := by decide +kernel
  exact fun i e he => of_decide_eq_true (List.all_eq_true.mp (h i) e he)

theorem singleton_detached : Closed 1 := by
  have exits : ∀ x ∈ ({v | v ∈ trace 1} : Set (Fin 155)), ∀ y,
      y ∉ ({v | v ∈ trace 1} : Set (Fin 155)) → graph.Adj x y →
      (before 0 y = 1 ∨ before 0 y = 0) →
      y ∈ (before 0).kempeComponentSet 1 2 (component 0) := by
    intro x hx y hy edge colour
    exact (component_iff 0 first_closed y).mpr
      (on_edges _ (old_exits 0) x y edge hx hy colour.symm)
  have entry : ∀ x ∈ ({v | v ∈ trace 1} : Set (Fin 155)), ∀ y ∈
      (before 0).kempeComponentSet 1 2 (component 0), graph.Adj x y → before 0 y ≠ 2 := by
    intro x hx y hy edge
    exact on_edges _ (no_entry 0) x y edge hx ((component_iff 0 first_closed y).mp hy)
  have closed := KempeComponentDetach.closed_after_swap (before 0) 1 2 0 (component 0)
    {v | v ∈ trace 1} (by decide) (by decide) exits entry
  have first_eq : (before 0).swapOnKempeComponent 1 2 (component 0) = after 0 :=
    switch_eq 0 first_closed
  rw [first_eq] at closed
  intro x hx y edge colour
  exact closed x hx y edge colour.symm

/-- The singleton recolouring exposes the final component by the SAME
detachment theorem. Its closure is not checked independently. -/
theorem final_detached : Closed 2 := by
  have exits : ∀ x ∈ ({v | v ∈ trace 2} : Set (Fin 155)), ∀ y,
      y ∉ ({v | v ∈ trace 2} : Set (Fin 155)) → graph.Adj x y →
      (before 1 y = 0 ∨ before 1 y = 2) →
      y ∈ (before 1).kempeComponentSet 0 1 (component 1) := by
    intro x hx y hy edge colour
    exact (component_iff 1 singleton_detached y).mpr
      (on_edges _ (old_exits 1) x y edge hx hy colour)
  have entry : ∀ x ∈ ({v | v ∈ trace 2} : Set (Fin 155)), ∀ y ∈
      (before 1).kempeComponentSet 0 1 (component 1), graph.Adj x y → before 1 y ≠ 1 := by
    intro x hx y hy edge
    exact on_edges _ (no_entry 1) x y edge hx ((component_iff 1 singleton_detached y).mp hy)
  have closed := KempeComponentDetach.closed_after_swap (before 1) 0 1 2 (component 1)
    {v | v ∈ trace 2} (by decide) (by decide) exits entry
  have second_eq : (before 1).swapOnKempeComponent 0 1 (component 1) = after 1 :=
    switch_eq 1 singleton_detached
  rw [second_eq] at closed
  exact closed

theorem all_closed (i : Fin 3) : Closed i := by
  fin_cases i
  · exact first_closed
  · exact singleton_detached
  · exact final_detached

theorem physical_step (i) : graph.KempeStep (before i) (after i) :=
  ⟨firstColour i, secondColour i, component i, (switch_eq i (all_closed i)).symm⟩

theorem silent_support : ∀ i : Fin 2, ∀ v ∈ trace i.castSucc, v ∉ ports := by decide +kernel

theorem preparation (i : Fin 2) :
    graph.KempeStepAvoiding KempeDetachExample.boundary (before i.castSucc) (after i.castSucc) := by
  refine ⟨firstColour i.castSucc, secondColour i.castSucc, component i.castSucc, ?_,
    (switch_eq i.castSucc (all_closed i.castSucc)).symm⟩
  exact Set.disjoint_left.mpr fun v hv hb =>
    silent_support i v ((component_iff _ (all_closed _) v).mp hv) hb

theorem silent_history : Relation.ReflTransGen (graph.KempeStepAvoiding KempeDetachExample.boundary)
    (KempeDetachExample.state 0) (after 1) :=
  (Relation.ReflTransGen.single (preparation 0)).trans (Relation.ReflTransGen.single (preparation 1))

theorem physical_history : after 2 ∈ graph.KempeClosure (KempeDetachExample.state 0) :=
  ((Relation.ReflTransGen.single (physical_step 0)).trans
    (Relation.ReflTransGen.single (physical_step 1))).trans
    (Relation.ReflTransGen.single (physical_step 2))

theorem preparation_size : (trace0 ++ trace1).toFinset.card = 5 := by decide +kernel

def completeValues (v : Fin 162) : Fin 4 :=
  ⟨(completeData >>> (2 * v.val)) % 4, Nat.mod_lt _ (by decide)⟩
theorem complete_edges : ∀ e ∈ ambientEdges, completeValues e.1 ≠ completeValues e.2 := by
  have h : ambientEdges.all (fun e => decide (completeValues e.1 ≠ completeValues e.2)) = true := by decide +kernel
  exact fun e he => of_decide_eq_true (List.all_eq_true.mp h e he)

def completed : ambient.Coloring (Fin 4) := .mk completeValues (by
  intro u v edge
  rcases edge with edge | edge
  · exact complete_edges _ edge
  · exact (complete_edges _ edge).symm)

theorem reconstructed : ∀ v, completed (includeExterior v) = after 2 v := by decide +kernel

theorem repair_and_reconstruct :
    after 2 ∈ graph.KempeClosure (KempeDetachExample.state 0) ∧
      ∃ F : ambient.Coloring (Fin 4), ∀ v, F (includeExterior v) = after 2 v :=
  ⟨physical_history, completed, reconstructed⟩

theorem gslt_history : Nonempty
    (Mettapedia.GraphTheory.FourColor.KempeChainCertificate.History
      (KempeDetachExample.state 0) (after 2)) :=
  Mettapedia.GraphTheory.FourColor.KempeChainCertificate.nonempty_history_iff.mpr physical_history

end SimpleGraph.KempeCascadingDetach
