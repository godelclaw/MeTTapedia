import Mettapedia.GraphTheory.Kempe.ComponentDetach
import Mettapedia.GraphTheory.Kempe.Chain
import Lean.Util.CollectAxioms

/-!
# Two physical repairs using component detachment

Two different boundary-silent preparations detach two different components
in the same exterior. Each detached component can then be switched without
changing the boundary. A final switch admits an explicit colouring of the
whole graph. The second component's closure is derived from the general
detachment law, using observations before the first switch.

The companion program verifies the spherical embedding, source occurrence,
and exhaustive failure of a single silent preparation followed by one
fixed-pair phase for the specified count potential. Those assertions are
separate from the physical repair and reconstruction proved here.
-/

namespace SimpleGraph.KempeDetachExample

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def edges : List (Fin 155 × Fin 155) := [(0,11),(0,28),(0,40),(0,66),(0,82),(0,97),(0,107),(0,130),(1,24),(1,26),(1,38),(1,48),(1,133),(2,4),(2,34),(2,91),(2,153),(2,154),(3,23),(3,49),(3,88),(3,111),(3,148),(3,151),(3,152),(4,13),(4,27),(4,34),(4,42),(4,51),(4,91),(4,106),(5,35),(5,53),(5,69),(5,115),(5,138),(6,23),(6,31),(6,49),(6,60),(6,80),(6,101),(7,85),(7,90),(7,125),(7,127),(7,150),(8,50),(8,69),(8,87),(8,100),(8,138),(9,15),(9,28),(9,126),(9,131),(9,132),(10,29),(10,59),(10,75),(10,76),(10,89),(10,104),(10,148),(10,153),(11,40),(11,43),(11,79),(11,107),(12,44),(12,52),(12,58),(12,93),(12,139),(12,141),(12,142),(13,27),(13,43),(13,106),(14,72),(14,74),(14,85),(14,109),(14,149),(15,35),(15,53),(15,126),(15,132),(16,64),(16,92),(16,98),(16,99),(16,114),(17,45),(17,67),(17,71),(17,99),(17,114),(17,118),(18,63),(18,82),(18,97),(18,98),(18,102),(18,144),(19,20),(19,39),(19,121),(19,135),(19,136),(20,38),(20,39),(20,48),(20,136),(21,32),(21,62),(21,68),(21,137),(21,146),(22,25),(22,26),(22,48),(22,77),(22,78),(22,83),(22,87),(22,119),(22,129),(23,31),(23,49),(23,64),(23,111),(24,26),(24,41),(24,56),(24,78),(24,121),(24,133),(25,29),(25,83),(25,88),(25,129),(25,148),(26,48),(26,78),(27,42),(27,43),(27,79),(28,57),(28,65),(28,66),(28,82),(28,131),(28,132),(28,142),(29,104),(29,129),(29,148),(30,34),(30,47),(30,51),(30,62),(30,80),(30,101),(30,146),(31,32),(31,47),(31,64),(31,101),(31,137),(32,64),(32,68),(32,99),(32,137),(33,41),(33,78),(33,104),(33,107),(33,130),(33,154),(34,51),(34,54),(34,80),(34,153),(35,53),(35,112),(35,113),(35,126),(35,138),(36,51),(36,70),(36,71),(36,106),(36,118),(37,61),(37,102),(37,108),(37,117),(37,123),(37,128),(37,144),(38,39),(38,48),(38,133),(39,121),(39,133),(40,43),(40,97),(41,56),(41,66),(41,78),(41,126),(41,130),(41,131),(42,79),(42,91),(42,107),(43,79),(44,93),(44,108),(44,117),(44,139),(45,46),(45,67),(45,110),(46,106),(46,110),(47,101),(47,137),(47,146),(48,119),(48,122),(48,136),(49,60),(49,151),(50,69),(50,83),(50,87),(50,88),(50,111),(51,62),(51,71),(51,106),(52,55),(52,63),(52,141),(52,142),(53,57),(53,93),(53,96),(53,115),(53,132),(54,80),(54,103),(54,124),(54,153),(55,63),(55,123),(55,128),(55,141),(56,121),(56,126),(56,135),(57,65),(57,96),(57,132),(58,65),(58,93),(58,96),(58,142),(59,73),(59,74),(59,75),(59,76),(59,109),(60,80),(60,84),(60,124),(60,151),(61,117),(61,128),(61,139),(61,141),(62,68),(62,71),(62,146),(63,82),(63,123),(63,142),(63,144),(64,92),(64,99),(64,111),(65,96),(65,142),(66,130),(66,131),(67,70),(67,110),(67,118),(68,71),(68,99),(69,111),(69,115),(69,138),(70,106),(70,110),(70,118),(71,99),(71,118),(72,74),(72,76),(72,85),(72,103),(72,124),(72,147),(73,75),(73,86),(73,109),(73,127),(74,76),(74,109),(75,89),(75,127),(76,103),(76,153),(77,81),(77,87),(77,119),(77,120),(78,104),(78,129),(79,107),(80,101),(80,124),(81,119),(81,120),(81,122),(81,134),(82,97),(82,142),(83,87),(83,88),(84,95),(84,124),(84,147),(84,151),(85,90),(85,125),(85,147),(85,149),(86,109),(86,125),(86,127),(86,149),(87,100),(87,120),(88,111),(88,148),(89,105),(89,127),(89,140),(89,145),(89,148),(90,94),(90,95),(90,143),(90,147),(90,150),(90,152),(91,107),(91,154),(92,98),(92,102),(92,108),(92,111),(93,96),(93,108),(93,115),(94,140),(94,143),(94,145),(94,150),(95,147),(95,151),(95,152),(97,98),(98,102),(99,114),(100,112),(100,120),(100,138),(102,108),(102,144),(103,124),(103,153),(104,129),(104,153),(104,154),(105,143),(105,145),(105,148),(105,152),(106,110),(107,130),(107,154),(108,111),(108,115),(108,117),(109,149),(111,115),(112,113),(112,120),(112,138),(113,116),(113,120),(113,126),(116,120),(116,126),(116,134),(116,135),(117,139),(119,122),(120,134),(121,133),(121,135),(122,134),(122,136),(123,128),(123,144),(124,147),(125,127),(125,149),(126,131),(126,135),(127,140),(127,150),(128,141),(134,135),(134,136),(135,136),(137,146),(139,141),(140,145),(140,150),(143,145),(143,152),(148,152),(151,152),(153,154)]

def ambientEdges : List (Fin 162 × Fin 162) := [(0,13),(0,30),(0,42),(0,71),(0,87),(0,102),(0,114),(0,137),(1,47),(1,48),(1,49),(1,50),(1,51),(2,26),(2,28),(2,40),(2,53),(2,140),(3,5),(3,36),(3,96),(3,160),(3,161),(4,25),(4,54),(4,93),(4,118),(4,155),(4,158),(4,159),(5,15),(5,29),(5,36),(5,44),(5,56),(5,96),(5,113),(6,37),(6,58),(6,74),(6,122),(6,145),(7,25),(7,33),(7,54),(7,65),(7,85),(7,108),(8,90),(8,95),(8,132),(8,134),(8,157),(9,55),(9,74),(9,92),(9,107),(9,145),(10,17),(10,30),(10,133),(10,138),(10,139),(11,31),(11,64),(11,80),(11,81),(11,94),(11,111),(11,155),(11,160),(12,42),(12,47),(12,49),(12,102),(12,103),(12,104),(13,42),(13,45),(13,84),(13,114),(14,46),(14,57),(14,63),(14,98),(14,146),(14,148),(14,149),(15,29),(15,45),(15,103),(15,105),(15,113),(16,77),(16,79),(16,90),(16,116),(16,156),(17,37),(17,58),(17,133),(17,139),(18,49),(18,69),(18,97),(18,104),(18,106),(18,121),(19,48),(19,50),(19,72),(19,76),(19,106),(19,121),(19,125),(20,68),(20,87),(20,102),(20,104),(20,109),(20,151),(21,22),(21,41),(21,128),(21,142),(21,143),(22,40),(22,41),(22,53),(22,143),(23,34),(23,67),(23,73),(23,144),(23,153),(24,27),(24,28),(24,53),(24,82),(24,83),(24,88),(24,92),(24,126),(24,136),(25,33),(25,54),(25,69),(25,118),(26,28),(26,43),(26,61),(26,83),(26,128),(26,140),(27,31),(27,88),(27,93),(27,136),(27,155),(28,53),(28,83),(29,44),(29,45),(29,84),(30,62),(30,70),(30,71),(30,87),(30,138),(30,139),(30,149),(31,111),(31,136),(31,155),(32,36),(32,52),(32,56),(32,67),(32,85),(32,108),(32,153),(33,34),(33,52),(33,69),(33,108),(33,144),(34,69),(34,73),(34,106),(34,144),(35,43),(35,83),(35,111),(35,114),(35,137),(35,161),(36,56),(36,59),(36,85),(36,160),(37,58),(37,119),(37,120),(37,133),(37,145),(38,56),(38,75),(38,76),(38,113),(38,125),(39,66),(39,109),(39,115),(39,124),(39,130),(39,135),(39,151),(40,41),(40,53),(40,140),(41,128),(41,140),(42,45),(42,102),(42,103),(43,61),(43,71),(43,83),(43,133),(43,137),(43,138),(44,84),(44,96),(44,114),(45,84),(45,103),(46,98),(46,115),(46,124),(46,146),(47,49),(47,51),(47,103),(47,105),(48,50),(48,51),(48,72),(48,117),(49,50),(49,104),(49,121),(50,121),(51,105),(51,113),(51,117),(52,108),(52,144),(52,153),(53,126),(53,129),(53,143),(54,65),(54,158),(55,74),(55,88),(55,92),(55,93),(55,118),(56,67),(56,76),(56,113),(57,60),(57,68),(57,148),(57,149),(58,62),(58,98),(58,101),(58,122),(58,139),(59,85),(59,110),(59,131),(59,160),(60,68),(60,130),(60,135),(60,148),(61,128),(61,133),(61,142),(62,70),(62,101),(62,139),(63,70),(63,98),(63,101),(63,149),(64,78),(64,79),(64,80),(64,81),(64,116),(65,85),(65,89),(65,131),(65,158),(66,124),(66,135),(66,146),(66,148),(67,73),(67,76),(67,153),(68,87),(68,130),(68,149),(68,151),(69,97),(69,106),(69,118),(70,101),(70,149),(71,137),(71,138),(72,75),(72,117),(72,125),(73,76),(73,106),(74,118),(74,122),(74,145),(75,113),(75,117),(75,125),(76,106),(76,125),(77,79),(77,81),(77,90),(77,110),(77,131),(77,154),(78,80),(78,91),(78,116),(78,134),(79,81),(79,116),(80,94),(80,134),(81,110),(81,160),(82,86),(82,92),(82,126),(82,127),(83,111),(83,136),(84,114),(85,108),(85,131),(86,126),(86,127),(86,129),(86,141),(87,102),(87,149),(88,92),(88,93),(89,100),(89,131),(89,154),(89,158),(90,95),(90,132),(90,154),(90,156),(91,116),(91,132),(91,134),(91,156),(92,107),(92,127),(93,118),(93,155),(94,112),(94,134),(94,147),(94,152),(94,155),(95,99),(95,100),(95,150),(95,154),(95,157),(95,159),(96,114),(96,161),(97,104),(97,109),(97,115),(97,118),(98,101),(98,115),(98,122),(99,147),(99,150),(99,152),(99,157),(100,154),(100,158),(100,159),(102,104),(103,105),(104,109),(105,113),(106,121),(107,119),(107,127),(107,145),(109,115),(109,151),(110,131),(110,160),(111,136),(111,160),(111,161),(112,150),(112,152),(112,155),(112,159),(113,117),(114,137),(114,161),(115,118),(115,122),(115,124),(116,156),(118,122),(119,120),(119,127),(119,145),(120,123),(120,127),(120,133),(123,127),(123,133),(123,141),(123,142),(124,146),(126,129),(127,141),(128,140),(128,142),(129,141),(129,143),(130,135),(130,151),(131,154),(132,134),(132,156),(133,138),(133,142),(134,147),(134,157),(135,148),(141,142),(141,143),(142,143),(144,153),(146,148),(147,152),(147,157),(150,152),(150,159),(155,159),(158,159),(160,161)]

def carrier : List (Fin 162) := [0,2,3,4,5,6,7,8,9,10,11,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,48,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,104,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161]

def ports : List (Fin 155) := [43,40,97,98,16,114,17,45,46,106,13]

def colourData : List Nat := [1929953971212522532278692781948038919508330987030319946522696919000269446175464219953306092380,1929953971216316807458821159039678493545095672394855897380220629002714392288235516835591701340,1929444585948280472647013750782421301419310225411257129043684613665516869712326071945927852892,1851526941297154960049655985589055705084352345829982510453688383509469701777760475898278051667,1929953971212522532278692781948034098694270045787971409176655443029359550309464999971152544604,1929444585944960481864401420827231853323056233408943018943581727552361667062717768020103594844,1851526941298103528844688079861970419407652360545458267021567114761202792041820918444344606547]

def completeData : List Nat := [30335417406212586865453563667891089819358090615229828223629159504211429442334252997638902486400335,30335417406228128216591369500458524498831405676370190423260773452195316942951646184316041453632847]

def trace00 : List (Fin 155) := [19,135,19]

def trace01 : List (Fin 155) := [7,85,149,85,7,127,73,59,10,104,129,25,83,87,8,87,77,81,134,81,77,87,83,25,129,104,10,59,74,59,73,127,140,94,143,105,143,94,140,127,7]

def trace02 : List (Fin 155) := [0,40,0,82,18,98,18,144,18,82,142,12,93,96,57,132,9,131,41,56,41,78,129,29,10,76,74,14,149,86,73,86,149,14,74,76,10,89,140,150,7,150,140,89,10,29,129,78,41,130,41,131,9,132,57,96,93,108,111,64,32,68,62,68,32,137,47,101,6,49,151,152,143,152,151,49,6,101,47,137,32,64,111,69,5,35,113,116,134,136,19,39,133,1,48,119,77,119,48,1,133,39,19,136,134,116,113,35,5,69,8,100,8,69,111,88,83,88,111,108,93,12,139,61,128,55,128,61,139,12,142,82,0]

def trace10 : List (Fin 155) := [87,100,87]

def trace11 : List (Fin 155) := [7,85,149,85,7,127,73,59,10,104,129,25,83,25,129,104,10,59,74,59,73,127,140,94,143,105,143,94,140,127,7]

def trace12 : List (Fin 155) := [0,40,0,82,18,98,18,144,18,82,142,12,93,96,57,132,9,131,41,56,135,116,113,35,5,69,111,64,32,68,62,68,32,137,47,101,6,49,151,152,143,152,151,49,6,101,47,137,32,64,111,88,83,87,100,87,83,88,111,108,111,69,5,35,113,116,135,136,48,1,133,39,133,1,48,119,81,119,48,136,135,56,41,78,129,29,10,76,74,14,149,86,73,86,149,14,74,76,10,89,140,150,7,150,140,89,10,29,129,78,41,130,41,131,9,132,57,96,93,12,139,61,128,55,128,61,139,12,142,82,0]

theorem edges_ne : ∀ e ∈ edges, e.1 ≠ e.2 := by
  have h : edges.all (fun e => decide (e.1 ≠ e.2)) = true := by decide +kernel
  exact fun e he => of_decide_eq_true (List.all_eq_true.mp h e he)

def graph : SimpleGraph (Fin 155) where
  Adj u v := (u,v) ∈ edges ∨ (v,u) ∈ edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro v h; rcases h with h | h <;> exact edges_ne _ h rfl⟩
instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

theorem on_edges (P : Fin 155 → Fin 155 → Prop)
    (h : ∀ e ∈ edges, P e.1 e.2 ∧ P e.2 e.1) :
    ∀ u v, graph.Adj u v → P u v := by
  intro u v edge
  rcases edge with edge | edge
  · exact (h _ edge).1
  · exact (h _ edge).2

def values (i : Fin 7) (v : Fin 155) : Fin 4 :=
  ⟨(colourData.get ⟨i.val, i.isLt⟩ >>> (2 * v.val)) % 4, Nat.mod_lt _ (by decide)⟩

theorem proper_edges : ∀ i : Fin 7, ∀ e ∈ edges,
    values i e.1 ≠ values i e.2 := by
  have h : ∀ i : Fin 7, edges.all (fun e => decide (values i e.1 ≠ values i e.2)) = true := by decide +kernel
  exact fun i e he => of_decide_eq_true (List.all_eq_true.mp (h i) e he)

def state (i : Fin 7) : graph.Coloring (Fin 4) := .mk (values i) (by
  intro u v edge
  rcases edge with edge | edge
  · exact proper_edges i _ edge
  · exact (proper_edges i _ edge).symm)

def stage (i : Fin 2) (t : Fin 4) : Fin 7 :=
  if t = 0 then 0 else ⟨i.val * 3 + t.val, by have := i.isLt; have := t.isLt; omega⟩

def before (i : Fin 2) (t : Fin 3) := state (stage i t.castSucc)
def after (i : Fin 2) (t : Fin 3) := state (stage i t.succ)
def other (i : Fin 2) : Fin 4 := if i = 0 then 2 else 3

def secondColour (i : Fin 2) (t : Fin 3) : Fin 4 :=
  if t = 0 then other i else if t = 1 then 1 else 3

def trace (i : Fin 2) (t : Fin 3) : List (Fin 155) :=
  if i = 0 then
    if t = 0 then trace00 else if t = 1 then trace01 else trace02
  else
    if t = 0 then trace10 else if t = 1 then trace11 else trace12

def root (i : Fin 2) (t : Fin 3) : Fin 155 := (trace i t).head!

theorem root_mem : ∀ i t, root i t ∈ trace i t := by decide +kernel
theorem active : ∀ i t, ∀ v ∈ trace i t,
    before i t v = 0 ∨ before i t v = secondColour i t := by decide +kernel
theorem connected : ∀ i t, (trace i t).IsChain graph.Adj := by decide +kernel

def component (i : Fin 2) (t : Fin 3) :
    ((before i t).bicoloredSubgraph 0 (secondColour i t)).ConnectedComponent :=
  ((before i t).bicoloredSubgraph 0 (secondColour i t)).connectedComponentMk
    ⟨root i t, active i t _ (root_mem i t)⟩

theorem root_component (i t) :
    root i t ∈ (before i t).kempeComponentSet 0 (secondColour i t) (component i t) :=
  (before i t).mem_kempeComponentSet_self (active i t _ (root_mem i t))

def Closed (i : Fin 2) (t : Fin 3) : Prop :=
  ∀ x ∈ trace i t, ∀ y, graph.Adj x y →
    (before i t y = 0 ∨ before i t y = secondColour i t) → y ∈ trace i t

def ClosedEdge (i : Fin 2) (t : Fin 3) (x y : Fin 155) : Prop :=
  x ∈ trace i t → (before i t y = 0 ∨ before i t y = secondColour i t) → y ∈ trace i t
instance (i t x y) : Decidable (ClosedEdge i t x y) := inferInstanceAs (Decidable (_ → _ → _))

theorem direct_closed_edges : ∀ i t, t ≠ (1 : Fin 3) → ∀ e ∈ edges,
    ClosedEdge i t e.1 e.2 ∧ ClosedEdge i t e.2 e.1 := by
  have h : ∀ i t, t ≠ (1 : Fin 3) → edges.all
      (fun e => decide (ClosedEdge i t e.1 e.2 ∧ ClosedEdge i t e.2 e.1)) = true := by decide +kernel
  exact fun i t ht e he => of_decide_eq_true (List.all_eq_true.mp (h i t ht) e he)

theorem direct_closed (i t) (ht : t ≠ 1) : Closed i t := by
  intro x hx y edge active
  exact on_edges _ (direct_closed_edges i t ht) x y edge hx active

theorem component_iff (i t) (closed : Closed i t) (v) :
    v ∈ (before i t).kempeComponentSet 0 (secondColour i t) (component i t) ↔ v ∈ trace i t :=
  (before i t).kempe_component_iff_mem_chain _ _ _ _ (connected i t) (active i t)
    closed (root_mem i t) (root_component i t) v

theorem next_values : ∀ i t v, after i t v =
    if v ∈ trace i t then Equiv.swap 0 (secondColour i t) (before i t v) else before i t v := by
  decide +kernel

theorem switch_eq (i t) (closed : Closed i t) :
    (before i t).swapOnKempeComponent 0 (secondColour i t) (component i t) = after i t := by
  ext v
  rw [(before i t).swap_apply_of_chain _ _ _ _ (connected i t) (active i t)
    closed (root_mem i t) (root_component i t), next_values]

def OldExits (i : Fin 2) (x y : Fin 155) : Prop :=
  x ∈ trace i 1 → y ∉ trace i 1 → (before i 0 y = 0 ∨ before i 0 y = 1) → y ∈ trace i 0

def NoEntry (i : Fin 2) (x y : Fin 155) : Prop :=
  x ∈ trace i 1 → y ∈ trace i 0 → before i 0 y ≠ other i

instance (i x y) : Decidable (OldExits i x y) := inferInstanceAs (Decidable (_ → _ → _ → _))
instance (i x y) : Decidable (NoEntry i x y) := inferInstanceAs (Decidable (_ → _ → _))

theorem old_exits : ∀ i, ∀ e ∈ edges, OldExits i e.1 e.2 ∧ OldExits i e.2 e.1 := by
  have h : ∀ i, edges.all (fun e => decide (OldExits i e.1 e.2 ∧ OldExits i e.2 e.1)) = true := by decide +kernel
  exact fun i e he => of_decide_eq_true (List.all_eq_true.mp (h i) e he)
theorem no_entry : ∀ i, ∀ e ∈ edges, NoEntry i e.1 e.2 ∧ NoEntry i e.2 e.1 := by
  have h : ∀ i, edges.all (fun e => decide (NoEntry i e.1 e.2 ∧ NoEntry i e.2 e.1)) = true := by decide +kernel
  exact fun i e he => of_decide_eq_true (List.all_eq_true.mp (h i) e he)

theorem other_ne_zero : ∀ i : Fin 2, other i ≠ 0 := by decide +kernel
theorem other_ne_one : ∀ i : Fin 2, other i ≠ 1 := by decide +kernel

/-- Closure of the middle component follows from old exits and the first
physical switch, rather than a second direct closure check. -/
theorem detached_closed (i : Fin 2) : Closed i 1 := by
  have first := direct_closed i 0 (by decide)
  have exits : ∀ x ∈ ({v | v ∈ trace i 1} : Set (Fin 155)), ∀ y,
      y ∉ ({v | v ∈ trace i 1} : Set (Fin 155)) → graph.Adj x y →
      (before i 0 y = 0 ∨ before i 0 y = 1) →
      y ∈ (before i 0).kempeComponentSet 0 (other i) (component i 0) := by
    intro x hx y hy edge colour
    apply (component_iff i 0 first y).mpr
    exact on_edges _ (old_exits i) x y edge hx hy colour
  have noEntry : ∀ x ∈ ({v | v ∈ trace i 1} : Set (Fin 155)), ∀ y ∈
      (before i 0).kempeComponentSet 0 (other i) (component i 0),
      graph.Adj x y → before i 0 y ≠ other i := by
    intro x hx y hy edge
    exact on_edges _ (no_entry i) x y edge hx ((component_iff i 0 first y).mp hy)
  have closed := KempeComponentDetach.closed_after_swap (before i 0) 0 (other i) 1
    (component i 0) {v | v ∈ trace i 1}
    (other_ne_zero i) (other_ne_one i) exits noEntry
  have first_eq : (before i 0).swapOnKempeComponent 0 (other i) (component i 0) = after i 0 :=
    switch_eq i 0 first
  rw [first_eq] at closed
  exact closed

theorem all_closed (i t) : Closed i t := by
  by_cases ht : t = 1
  · subst t; exact detached_closed i
  · exact direct_closed i t ht

theorem physical_step (i t) : graph.KempeStep (before i t) (after i t) :=
  ⟨0, secondColour i t, component i t, (switch_eq i t (all_closed i t)).symm⟩

def boundary : Set (Fin 155) := {v | v ∈ ports}

theorem silent_support : ∀ i t, t.val < 2 → ∀ v ∈ trace i t, v ∉ ports := by decide +kernel

theorem preparation (i : Fin 2) (t : Fin 3) (ht : t.val < 2) :
    graph.KempeStepAvoiding boundary (before i t) (after i t) := by
  refine ⟨0, secondColour i t, component i t, ?_, (switch_eq i t (all_closed i t)).symm⟩
  exact Set.disjoint_left.mpr fun v hv hb =>
    silent_support i t ht v ((component_iff i t (all_closed i t) v).mp hv) hb

theorem silent_history (i : Fin 2) :
    Relation.ReflTransGen (graph.KempeStepAvoiding boundary) (state 0) (state (stage i 2)) :=
  (Relation.ReflTransGen.single (preparation i 0 (by decide))).trans
    (Relation.ReflTransGen.single (preparation i 1 (by decide)))

theorem physical_history (i : Fin 2) : state (stage i 3) ∈ graph.KempeClosure (state 0) :=
  ((Relation.ReflTransGen.single (physical_step i 0)).trans
    (Relation.ReflTransGen.single (physical_step i 1))).trans
    (Relation.ReflTransGen.single (physical_step i 2))

theorem ambient_edges_ne : ∀ e ∈ ambientEdges, e.1 ≠ e.2 := by
  have h : ambientEdges.all (fun e => decide (e.1 ≠ e.2)) = true := by decide +kernel
  exact fun e he => of_decide_eq_true (List.all_eq_true.mp h e he)

def ambient : SimpleGraph (Fin 162) where
  Adj u v := (u,v) ∈ ambientEdges ∨ (v,u) ∈ ambientEdges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro v h; rcases h with h | h <;> exact ambient_edges_ne _ h rfl⟩

def completedValues (i : Fin 2) (v : Fin 162) : Fin 4 := ⟨(completeData.get ⟨i.val, i.isLt⟩ >>> (2 * v.val)) % 4, Nat.mod_lt _ (by decide)⟩
theorem completed_edges : ∀ i : Fin 2, ∀ e ∈ ambientEdges,
    completedValues i e.1 ≠ completedValues i e.2 := by
  have h : ∀ i : Fin 2, ambientEdges.all (fun e => decide (completedValues i e.1 ≠ completedValues i e.2)) = true := by decide +kernel
  exact fun i e he => of_decide_eq_true (List.all_eq_true.mp (h i) e he)

def completed (i : Fin 2) : ambient.Coloring (Fin 4) := .mk (completedValues i) (by
  intro u v edge
  rcases edge with edge | edge
  · exact completed_edges i _ edge
  · exact (completed_edges i _ edge).symm)

def includeExterior (v : Fin 155) : Fin 162 := carrier.get ⟨v.val, v.isLt⟩
theorem carrier_nodup : carrier.Nodup := by decide +kernel

theorem include_injective : Function.Injective includeExterior := by
  intro u v h
  have eq := carrier_nodup.injective_get h
  exact Fin.ext (congrArg Fin.val eq)

instance : DecidableRel ambient.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def position (v : Fin 162) : Fin 155 := ⟨carrier.idxOf v % 155, Nat.mod_lt _ (by decide)⟩
theorem position_include : ∀ v, position (includeExterior v) = v := by decide +kernel
theorem include_mem (v : Fin 155) : includeExterior v ∈ carrier := List.get_mem _ _

theorem forward_edges : ∀ e ∈ edges, ambient.Adj (includeExterior e.1) (includeExterior e.2) := by
  have h : edges.all (fun e => decide (ambient.Adj (includeExterior e.1) (includeExterior e.2))) = true := by decide +kernel
  exact fun e he => of_decide_eq_true (List.all_eq_true.mp h e he)

theorem reverse_edges : ∀ e ∈ ambientEdges, e.1 ∈ carrier → e.2 ∈ carrier →
    graph.Adj (position e.1) (position e.2) := by
  have h : ambientEdges.all (fun e => decide (e.1 ∈ carrier → e.2 ∈ carrier →
      graph.Adj (position e.1) (position e.2))) = true := by decide +kernel
  exact fun e he => of_decide_eq_true (List.all_eq_true.mp h e he)

theorem exterior_adj (u v : Fin 155) :
    ambient.Adj (includeExterior u) (includeExterior v) ↔ graph.Adj u v := by
  constructor
  · intro edge
    rcases edge with edge | edge
    · simpa only [position_include] using reverse_edges _ edge (include_mem u) (include_mem v)
    · simpa only [position_include] using (reverse_edges _ edge (include_mem v) (include_mem u)).symm
  · intro edge
    rcases edge with edge | edge
    · exact forward_edges _ edge
    · exact (forward_edges _ edge).symm

/-- The exterior is literally an induced subgraph of the whole map. -/
def exteriorEmbedding : graph ↪g ambient where
  toFun := includeExterior
  inj' := include_injective
  map_rel_iff' := exterior_adj _ _

theorem reconstructed : ∀ i v, completed i (includeExterior v) = state (stage i 3) v := by decide +kernel

/-- A physical history repairs the exterior, and its result is the literal
restriction of a genuine colouring of the entire graph. -/
theorem repair_and_reconstruct (i : Fin 2) :
    ∃ D : graph.Coloring (Fin 4), D ∈ graph.KempeClosure (state 0) ∧
      ∃ F : ambient.Coloring (Fin 4), ∀ v, F (includeExterior v) = D v :=
  ⟨_, physical_history i, completed i, reconstructed i⟩

end SimpleGraph.KempeDetachExample
