import Mettapedia.GraphTheory.Kempe.AnchoredChains

/-!
# A boundary-anchored exterior with a visible three-vertex repair

Every two-colour component of the displayed colouring meets its eleven
ports. Thus every history preserving the ports at each step is stationary.
Nevertheless a component of three vertices can be switched, changing only
port six. The source-colouring consumer is in `VisiblePortRepair`.

The companion program checks the spherical embedding, complete D0092 core
stars, and all cycles of length three through five. Those geometric checks
are separate from the kernel-checked component and history statements here.
-/

namespace SimpleGraph.AnchoredBoundaryExample

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def edges : List (Fin 155 × Fin 155) := [(0,11),(0,40),(0,66),(0,82),(0,97),(0,107),(0,130),(1,24),(1,26),(1,38),(1,48),(1,133),(2,4),(2,34),(2,91),(2,153),(2,154),(3,23),(3,49),(3,50),(3,88),(3,111),(3,148),(3,151),(3,152),(4,13),(4,27),(4,34),(4,42),(4,51),(4,91),(4,106),(5,15),(5,35),(5,53),(5,69),(5,115),(5,138),(6,31),(6,49),(6,60),(6,80),(6,101),(7,85),(7,90),(7,125),(7,127),(7,150),(8,50),(8,69),(8,87),(8,88),(8,100),(8,138),(9,15),(9,28),(9,126),(9,131),(9,132),(10,29),(10,75),(10,76),(10,104),(10,105),(11,40),(11,43),(11,79),(11,107),(12,44),(12,52),(12,58),(12,93),(12,142),(13,27),(13,43),(13,106),(14,72),(14,74),(14,85),(14,109),(14,149),(15,35),(15,53),(15,113),(15,126),(15,132),(16,64),(16,92),(16,98),(16,111),(16,114),(17,45),(17,67),(17,99),(17,114),(18,28),(18,63),(18,82),(18,97),(18,102),(18,144),(19,20),(19,39),(19,121),(19,135),(19,136),(20,38),(20,39),(20,48),(20,136),(21,32),(21,62),(21,68),(21,137),(21,146),(22,25),(22,26),(22,78),(22,83),(22,87),(23,31),(23,32),(23,49),(23,64),(23,111),(23,137),(24,26),(24,41),(24,56),(24,78),(24,121),(24,133),(25,29),(25,33),(25,78),(25,83),(25,129),(25,148),(26,48),(26,78),(26,87),(26,119),(27,42),(27,43),(27,79),(28,57),(28,63),(28,65),(28,66),(28,82),(28,131),(28,132),(28,142),(29,104),(29,105),(29,129),(29,148),(30,34),(30,47),(30,51),(30,54),(30,62),(30,80),(30,101),(30,146),(31,47),(31,49),(31,101),(31,137),(32,64),(32,68),(32,71),(32,99),(32,137),(33,41),(33,78),(33,91),(33,107),(33,129),(33,130),(33,154),(34,51),(34,54),(34,153),(35,112),(35,113),(35,138),(36,51),(36,70),(36,71),(36,106),(36,118),(37,61),(37,102),(37,108),(37,117),(37,123),(37,128),(37,144),(38,39),(38,48),(38,133),(39,121),(39,133),(40,43),(40,97),(41,56),(41,66),(41,78),(41,126),(41,130),(41,131),(42,79),(42,91),(42,107),(43,79),(44,52),(44,93),(44,108),(44,117),(44,139),(45,46),(45,67),(45,110),(46,106),(46,110),(47,101),(47,137),(47,146),(48,119),(48,122),(48,136),(49,60),(49,84),(49,151),(50,69),(50,88),(50,111),(51,62),(51,68),(51,71),(51,106),(52,55),(52,139),(52,141),(52,142),(53,57),(53,96),(53,115),(53,132),(54,72),(54,80),(54,103),(54,124),(54,153),(55,123),(55,128),(55,141),(55,142),(56,121),(56,126),(56,135),(57,65),(57,96),(57,132),(58,65),(58,93),(58,96),(58,115),(58,142),(59,73),(59,74),(59,75),(59,76),(59,109),(60,80),(60,84),(60,124),(61,117),(61,128),(61,139),(61,141),(62,68),(62,146),(63,123),(63,142),(63,144),(64,99),(64,111),(64,114),(65,96),(65,142),(66,82),(66,130),(66,131),(67,70),(67,99),(67,110),(67,118),(68,71),(69,111),(69,115),(69,138),(70,106),(70,110),(70,118),(71,99),(71,118),(72,74),(72,76),(72,85),(72,103),(72,124),(72,147),(73,75),(73,86),(73,89),(73,109),(73,127),(74,76),(74,109),(75,76),(75,89),(75,105),(76,103),(76,104),(77,81),(77,87),(77,100),(77,119),(77,120),(79,107),(80,101),(80,124),(81,119),(81,120),(81,122),(81,134),(82,97),(83,87),(83,88),(83,148),(84,95),(84,124),(84,147),(84,151),(85,90),(85,95),(85,125),(85,147),(85,149),(86,109),(86,125),(86,127),(86,149),(87,88),(87,100),(87,119),(88,148),(89,105),(89,127),(89,140),(89,145),(90,94),(90,95),(90,143),(90,150),(90,152),(91,107),(91,154),(92,98),(92,102),(92,108),(92,111),(93,108),(93,115),(94,140),(94,143),(94,145),(94,150),(95,147),(95,151),(95,152),(96,115),(97,98),(97,102),(98,102),(99,114),(99,118),(100,112),(100,120),(100,138),(102,108),(102,144),(103,104),(103,153),(104,129),(104,153),(105,143),(105,145),(105,148),(106,110),(107,130),(108,111),(108,115),(108,117),(109,149),(111,115),(112,113),(112,116),(112,120),(112,138),(113,116),(113,126),(116,120),(116,126),(116,134),(116,135),(117,139),(119,122),(120,134),(121,133),(121,135),(122,134),(122,135),(122,136),(123,128),(123,142),(123,144),(124,147),(125,127),(125,149),(126,131),(126,135),(127,140),(127,150),(128,141),(129,153),(129,154),(134,135),(135,136),(137,146),(139,141),(140,145),(140,150),(143,145),(143,148),(143,152),(148,152),(151,152),(153,154)]
def ports : List (Fin 155) := [43,40,97,98,16,114,17,45,46,106,13]
def colourData : Nat := 1929953971212522532278692781948038919508330987030319946522696919000269446175464219953306092380
def chainData : List (Fin 4 × Fin 4 × List (Fin 155)) := [(0,1,[45,67,118,71,32,21,62,30,34,2,91,107,0,107,91,2,34,30,47,31,6,60,124,60,6,31,47,30,62,21,32,71,118,67,45]),(0,1,[16,111,3,151,95,85,7,127,73,59,74,59,73,127,140,94,143,105,10,104,103,104,129,25,83,87,8,87,26,48,20,48,26,87,77,81,134,135,121,133,121,135,126,9,28,18,102,18,28,57,53,5,53,57,28,142,52,139,117,139,52,142,58,93,58,142,123,128,123,142,28,9,126,41,126,113,112,113,126,135,134,81,77,87,83,25,129,104,10,105,143,94,140,127,7,85,149,85,95,151,3,111,16,114,16]),(0,1,[43,27,43]),(0,1,[106]),(0,2,[13,27,42,91,33,25,22,87,22,25,148,105,75,59,109,59,75,105,145,94,90,85,72,124,80,6,80,124,84,151,84,124,72,85,125,127,125,85,90,94,145,105,148,25,33,41,24,133,38,48,122,81,120,81,122,135,19,135,122,48,38,133,24,41,66,0,11,0,97,18,63,142,65,57,65,142,63,18,97,0,66,41,33,91,42,27,13,106,46,45,46,106,51,34,153,104,153,34,51,62,146,47,146,62,51,106,70,118,99,32,23,111,50,111,92,111,115,5,15,9,15,113,15,5,138,5,115,93,44,139,141,128,37,128,141,139,44,93,115,111,23,32,99,114,99,118,70,106,13]),(0,3,[17,45,110,106,4,27,79,27,4,34,54,124,147,85,14,85,147,124,54,34,4,91,154,91,4,106,36,118,36,106,110,45,17,114,64,32,68,62,68,32,137,47,101,6,49,151,152,151,49,6,101,47,137,32,64,111,69,5,35,113,116,135,56,41,78,25,29,104,76,59,76,104,29,105,89,127,86,127,150,94,150,127,89,105,29,25,78,41,130,0,40,0,82,18,144,18,82,0,130,41,131,9,132,57,96,57,132,9,131,41,56,135,136,48,1,133,39,133,1,48,119,81,119,87,88,87,100,87,119,48,136,135,116,113,35,5,69,111,108,93,12,142,55,128,61,139,61,128,55,142,12,93,108,111,64,114,17]),(0,3,[98]),(1,2,[13,43,11,107,33,129,153,2,153,103,72,74,109,73,75,10,75,73,109,149,125,7,90,95,84,60,80,30,51,71,99,67,70,67,99,71,51,30,146,21,146,30,80,60,84,95,90,143,145,140,145,143,148,3,23,31,23,3,50,8,138,112,120,77,120,134,122,134,120,112,138,8,50,3,148,83,22,26,24,121,19,20,38,20,19,121,24,26,22,83,148,143,90,7,125,149,109,74,72,103,153,129,33,107,42,107,11,43,13]),(1,2,[16,92,102,37,117,44,52,141,52,44,117,37,123,63,28,65,58,115,53,15,126,15,53,115,58,65,28,66,28,63,123,37,102,97,102,92,16]),(1,2,[46]),(1,3,[16,64,16,98,102,108,117,61,117,108,102,144,123,55,52,12,58,96,53,132,28,82,28,131,126,56,121,39,20,136,20,39,121,56,126,116,112,35,112,100,8,69,8,88,3,49,31,101,30,54,103,76,10,29,129,154,2,4,2,154,129,29,10,76,74,14,149,86,73,89,140,150,7,150,140,89,73,86,149,14,74,76,103,54,30,101,31,137,21,68,71,36,71,68,21,137,31,49,60,49,3,152,95,147,95,152,143,152,3,88,83,88,8,100,77,119,26,1,26,78,26,119,77,100,112,116,134,116,126,131,28,132,53,96,58,12,52,55,123,144,102,98,16]),(1,3,[17,67,110,67,17]),(1,3,[40,43,79,107,130,107,79,43,40]),(2,3,[13,4,42,79,11,40,97,82,66,130,33,78,22,78,24,1,38,39,19,136,122,119,122,136,19,39,38,1,24,56,24,78,33,154,153,54,72,14,109,86,125,86,109,14,72,76,75,89,145,89,75,76,72,147,84,49,23,64,99,17,99,64,23,137,146,137,23,49,84,147,72,54,80,101,80,54,153,154,33,130,66,131,66,82,97,98,92,108,37,61,141,55,141,61,37,144,63,144,37,108,44,12,44,108,115,69,50,88,148,29,148,152,90,150,90,152,148,88,50,69,138,35,15,132,15,35,138,100,120,116,120,100,138,69,115,96,65,96,115,108,92,98,97,40,11,79,42,4,51,36,70,110,46,110,70,36,51,68,51,4,13])]

theorem edges_ne : ∀ e ∈ edges, e.1 ≠ e.2 := by
  have h : edges.all (fun e => decide (e.1 ≠ e.2)) = true := by decide +kernel
  exact fun e he => of_decide_eq_true (List.all_eq_true.mp h e he)

def graph : SimpleGraph (Fin 155) where
  Adj u v := (u,v) ∈ edges ∨ (v,u) ∈ edges
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by intro v h; rcases h with h | h <;> exact edges_ne _ h rfl⟩
instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∨ _))

def values (v : Fin 155) : Fin 4 :=
  ⟨(colourData >>> (2*v.val)) % 4, Nat.mod_lt _ (by decide)⟩

theorem proper_edges : ∀ e ∈ edges, values e.1 ≠ values e.2 := by
  have h : edges.all (fun e => decide (values e.1 ≠ values e.2)) = true := by decide +kernel
  exact fun e he => of_decide_eq_true (List.all_eq_true.mp h e he)

def initial : graph.Coloring (Fin 4) := .mk values (by
  intro u v edge
  rcases edge with edge | edge
  · exact proper_edges _ edge
  · exact (proper_edges _ edge).symm)

def row (i : Fin 14) := chainData.get ⟨i.val, i.isLt⟩
def chain (i : Fin 14) := (row i).2.2
def boundary : Set (Fin 155) := {v | v ∈ ports}

theorem connected : ∀ i, (chain i).IsChain graph.Adj := by decide +kernel
theorem active : ∀ i, ∀ v ∈ chain i,
    initial v = (row i).1 ∨ initial v = (row i).2.1 := by decide +kernel
theorem anchors : ∀ i, ∃ w ∈ chain i, w ∈ ports := by decide +kernel
theorem covers : ∀ a b : Fin 4, a ≠ b → ∀ v : Fin 155,
    (initial v = a ∨ initial v = b) → ∃ i : Fin 14,
      ((row i).1 = a ∧ (row i).2.1 = b ∨ (row i).1 = b ∧ (row i).2.1 = a) ∧
      v ∈ chain i := by decide +kernel

/-- Fourteen anchored chains cover all active vertices for all six pairs.
No enumeration of recolouring histories is needed. -/
theorem frozen : initial.IsTransparent boundary := by
  apply initial.isTransparent_of_chains
  intro a b hab v hv
  obtain ⟨i, pair, member⟩ := covers a b hab v hv
  refine ⟨chain i, connected i, ?_, member, anchors i⟩
  intro x hx
  have h := active i x hx
  rcases pair with ⟨ha,hb⟩ | ⟨hb,ha⟩
  · simpa only [ha,hb] using h
  · simpa only [ha,hb,or_comm] using h

theorem silent_history_fixed (D : graph.Coloring (Fin 4))
    (h : Relation.ReflTransGen (graph.KempeStepAvoiding boundary) initial D) : D = initial :=
  frozen.eq_of_reflTransGen subset_rfl h

theorem boundary_fixed_history (D : graph.Coloring (Fin 4))
    (h : Relation.ReflTransGen (fun X Y : graph.Coloring (Fin 4) =>
      graph.KempeStep X Y ∧ Y.boundaryWord boundary = X.boundaryWord boundary) initial D) :
    D = initial := frozen.eq_of_boundary_fixed_history h

def repairTrace : List (Fin 155) := [17,67,110,67,17]
theorem repair_connected : repairTrace.IsChain graph.Adj := by decide +kernel
theorem repair_active : ∀ v ∈ repairTrace, initial v = 1 ∨ initial v = 3 := by decide +kernel

def ClosedEdge (u v : Fin 155) : Prop :=
  u ∈ repairTrace → (initial v = 1 ∨ initial v = 3) → v ∈ repairTrace
instance (u v) : Decidable (ClosedEdge u v) := inferInstanceAs (Decidable (_ → _ → _))

theorem repair_closed_edges : ∀ e ∈ edges, ClosedEdge e.1 e.2 ∧ ClosedEdge e.2 e.1 := by
  have h : edges.all (fun e => decide (ClosedEdge e.1 e.2 ∧ ClosedEdge e.2 e.1)) = true := by
    decide +kernel
  exact fun e he => of_decide_eq_true (List.all_eq_true.mp h e he)

theorem repair_closed : ∀ u ∈ repairTrace, ∀ v, graph.Adj u v →
    (initial v = 1 ∨ initial v = 3) → v ∈ repairTrace := by
  intro u hu v edge hv
  rcases edge with edge | edge
  · exact (repair_closed_edges _ edge).1 hu hv
  · exact (repair_closed_edges _ edge).2 hu hv

def component : (initial.bicoloredSubgraph 1 3).ConnectedComponent :=
  (initial.bicoloredSubgraph 1 3).connectedComponentMk
    ⟨17, repair_active 17 (by decide)⟩

theorem component_iff (v : Fin 155) :
    v ∈ initial.kempeComponentSet 1 3 component ↔ v ∈ repairTrace :=
  initial.kempe_component_iff_mem_chain 1 3 component repairTrace repair_connected
    repair_active repair_closed (by decide : (17 : Fin 155) ∈ repairTrace)
    (initial.mem_kempeComponentSet_self (repair_active 17 (by decide))) v

noncomputable def repaired := initial.swapOnKempeComponent 1 3 component

theorem repaired_apply (v : Fin 155) : repaired v =
    if v ∈ repairTrace then Equiv.swap 1 3 (initial v) else initial v := by
  classical
  change (if v ∈ initial.kempeComponentSet 1 3 component then _ else _) = _
  simp only [component_iff]

theorem physical_repair : graph.KempeStep initial repaired :=
  graph.kempeStep_swapOnKempeComponent initial 1 3 component

theorem changed_port : ∀ j : Fin 11, ports.get j ∈ repairTrace ↔ j = 6 := by
  simp only [ports, repairTrace]
  decide +kernel
theorem repair_support_size : repairTrace.toFinset.card = 3 := by decide +kernel

end SimpleGraph.AnchoredBoundaryExample
