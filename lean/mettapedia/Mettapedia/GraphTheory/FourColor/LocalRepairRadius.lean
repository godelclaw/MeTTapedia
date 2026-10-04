import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Tactic.FinCases

/-! # A repair must leave the radius-two neighbourhood

An explicit graph has a proper colouring after deletion of seven source
vertices. No full colouring can keep all vertices outside the displayed
radius-two neighbourhood fixed. The contradiction has two branching
choices and uses only local triangle constraints. A full colouring fixing
every vertex outside radius three is supplied separately.

The companion program checks the spherical embedding, source occurrence,
degree bounds and short-cycle conditions. Those geometric checks are not
claimed as Lean theorems here. No search procedure or solver is trusted.
The D0092 occurrence uses Yuta Inoue's MIT-licensed catalogue; the
companion fixture pins its source through the existing sphere fixture.
-/

namespace SimpleGraph.LocalRepairRadius

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

abbrev V := Fin 162
abbrev Palette := Fin 4


def edges : List (V × V) := [(0,42),(0,43),(0,45),(0,46),(0,102),(1,47),(1,48),(1,49),(1,50),(1,51),(2,52),(2,53),(2,54),(2,55),(2,56),(2,127),(3,57),(3,58),(3,59),(3,61),(3,128),(3,136),(4,62),(4,63),(4,64),(4,65),(4,66),(4,138),(4,145),(5,67),(5,68),(5,69),(5,70),(5,71),(6,72),(6,73),(6,74),(6,75),(6,76),(7,77),(7,78),(7,79),(7,81),(7,153),(8,82),(8,83),(8,84),(8,85),(8,86),(9,87),(9,88),(9,89),(9,90),(9,91),(10,92),(10,93),(10,94),(10,95),(10,96),(10,159),(11,97),(11,98),(11,99),(11,100),(11,101),(11,161),(12,42),(12,47),(12,49),(12,102),(12,103),(12,104),(13,43),(13,67),(13,102),(13,106),(13,107),(13,108),(14,44),(14,109),(14,110),(14,111),(14,112),(14,114),(15,45),(15,82),(15,103),(15,105),(15,109),(15,113),(16,44),(16,46),(16,97),(16,100),(16,110),(16,115),(16,116),(17,48),(17,52),(17,117),(17,118),(17,119),(17,120),(18,49),(18,68),(18,104),(18,107),(18,121),(19,48),(19,50),(19,117),(19,121),(19,123),(19,124),(20,51),(20,83),(20,113),(20,118),(20,125),(21,53),(21,57),(21,126),(21,127),(21,128),(21,129),(22,53),(22,54),(22,73),(22,119),(22,126),(22,130),(23,84),(23,118),(23,120),(23,125),(23,131),(23,132),(23,134),(24,56),(24,87),(24,127),(24,131),(24,133),(24,134),(25,58),(25,62),(25,135),(25,136),(25,137),(25,138),(25,139),(26,59),(26,74),(26,126),(26,128),(26,130),(26,135),(26,139),(27,60),(27,88),(27,129),(27,140),(27,141),(28,61),(28,92),(28,93),(28,136),(28,142),(28,143),(29,63),(29,69),(29,144),(29,146),(29,147),(30,64),(30,75),(30,137),(30,139),(30,144),(30,148),(31,65),(31,93),(31,138),(31,142),(31,150),(32,66),(32,98),(32,145),(32,147),(32,149),(32,151),(32,152),(33,70),(33,75),(33,76),(33,122),(33,124),(33,146),(33,148),(34,71),(34,97),(34,99),(34,108),(34,115),(34,151),(35,78),(35,85),(35,111),(35,114),(35,153),(35,154),(36,79),(36,89),(36,153),(36,155),(36,156),(36,157),(37,94),(37,155),(37,158),(37,159),(37,160),(38,80),(38,81),(38,100),(38,116),(38,158),(38,161),(39,85),(39,86),(39,90),(39,132),(39,134),(39,154),(39,156),(40,95),(40,141),(40,143),(40,157),(40,159),(41,96),(41,101),(41,150),(41,152),(41,160),(41,161),(42,45),(42,102),(42,103),(43,46),(43,102),(43,106),(44,45),(44,46),(44,109),(44,110),(45,46),(45,103),(45,109),(46,106),(46,115),(47,49),(47,51),(47,103),(47,105),(48,50),(48,51),(48,117),(48,118),(49,50),(49,104),(49,121),(50,121),(51,105),(51,113),(51,118),(52,54),(52,55),(52,119),(52,120),(53,54),(53,126),(53,127),(54,119),(55,56),(55,120),(55,131),(56,127),(56,131),(57,60),(57,61),(57,128),(57,129),(58,59),(58,135),(58,136),(59,128),(59,135),(60,61),(60,129),(60,140),(61,136),(61,140),(61,143),(62,64),(62,137),(62,138),(63,64),(63,144),(63,145),(63,147),(64,137),(64,144),(65,66),(65,138),(65,149),(65,150),(66,145),(66,149),(67,68),(67,71),(67,107),(67,108),(68,70),(68,107),(68,121),(68,122),(69,70),(69,71),(69,146),(69,147),(70,122),(70,146),(71,108),(71,147),(71,151),(72,73),(72,76),(72,123),(72,124),(73,74),(73,119),(73,123),(73,130),(74,75),(74,130),(74,139),(75,76),(75,139),(75,148),(76,124),(77,78),(77,81),(77,111),(77,112),(78,111),(78,153),(79,80),(79,81),(79,153),(79,155),(80,81),(80,155),(80,158),(81,112),(81,116),(82,83),(82,85),(82,109),(82,113),(82,114),(83,84),(83,113),(83,125),(84,86),(84,125),(84,132),(85,86),(85,114),(85,154),(86,132),(87,88),(87,90),(87,133),(87,134),(88,91),(88,129),(88,133),(88,141),(89,90),(89,91),(89,156),(89,157),(90,134),(90,156),(91,141),(91,157),(92,93),(92,95),(92,143),(93,96),(93,142),(93,150),(94,96),(94,159),(94,160),(95,143),(95,159),(96,150),(96,160),(97,99),(97,100),(97,115),(98,99),(98,101),(98,151),(98,152),(99,151),(100,116),(100,161),(101,152),(101,161),(102,104),(102,107),(103,105),(104,107),(105,113),(106,108),(106,115),(108,115),(109,114),(110,112),(110,116),(111,112),(111,114),(112,116),(117,119),(117,123),(118,120),(118,125),(119,123),(120,131),(121,122),(121,124),(122,124),(123,124),(126,128),(126,130),(127,129),(127,133),(129,133),(131,134),(132,134),(135,139),(136,138),(136,142),(137,139),(138,142),(140,141),(140,143),(141,143),(141,157),(144,146),(144,148),(145,147),(146,148),(147,151),(149,150),(149,152),(150,152),(153,154),(153,156),(154,156),(155,157),(155,158),(155,159),(157,159),(158,160),(158,161),(160,161)]

def graph : SimpleGraph V where
  Adj u v := u ≠ v ∧ ((u,v) ∈ edges ∨ (v,u) ∈ edges)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∧ _))


def core : List V := [1,12,47,49,50,103,105]

def ballOne : List V := [1,12,15,18,19,42,45,47,48,49,50,51,102,103,104,105,113,121]

def ballTwo : List V := [0,1,12,13,15,17,18,19,20,42,43,44,45,46,47,48,49,50,51,68,82,83,102,103,104,105,107,109,113,117,118,121,122,123,124]

def ballThree : List V := [0,1,5,8,12,13,14,15,16,17,18,19,20,23,33,42,43,44,45,46,47,48,49,50,51,52,67,68,70,72,73,76,82,83,84,85,102,103,104,105,106,107,108,109,110,113,114,115,117,118,119,120,121,122,123,124,125]

def initialData : List Palette := [3,0,3,3,2,2,0,3,1,0,3,2,0,2,0,1,0,1,3,3,1,2,2,1,3,1,2,2,3,1,3,0,3,3,2,0,3,2,2,1,3,2,1,1,1,0,2,0,2,0,0,3,2,0,1,1,0,1,2,1,0,2,0,0,1,1,0,3,0,3,1,0,3,1,3,2,1,1,2,2,3,0,0,3,0,3,2,2,1,1,3,3,0,2,0,2,1,1,0,3,3,3,0,0,2,0,0,1,1,3,3,3,2,2,1,3,1,0,0,3,3,1,2,2,0,2,1,1,0,3,0,2,3,0,0,3,0,2,3,0,3,0,1,1,2,1,0,2,1,2,3,1,1,1,2,0,0,2,1,1,3,0]

def finalData : List Palette := [2,3,3,3,2,1,0,3,1,0,3,2,3,3,0,1,2,1,3,1,0,2,2,1,3,1,2,2,3,1,3,0,3,3,2,0,3,2,2,1,3,2,1,1,1,0,3,0,2,1,0,1,2,0,1,1,0,1,2,1,0,2,0,0,1,1,0,2,0,3,2,0,3,1,3,2,1,1,2,2,3,0,0,3,0,3,2,2,1,1,3,3,0,2,0,2,1,1,0,3,3,3,0,2,2,3,2,1,1,3,3,3,2,2,1,0,1,3,3,0,0,2,1,2,0,2,1,1,0,3,0,2,3,0,0,3,0,2,3,0,3,0,1,1,2,1,0,2,1,2,3,1,1,1,2,0,0,2,1,1,3,0]

def initial (v : V) : Palette := initialData.get ⟨v.val, by simp [initialData]⟩
def finalColour (v : V) : Palette := finalData.get ⟨v.val, by simp [finalData]⟩


private theorem initial_edges : edges.all (fun e => decide
    (e.1 ∈ core ∨ e.2 ∈ core ∨ initial e.1 ≠ initial e.2)) = true := by decide +kernel

/-- The entire punctured graph is properly coloured. -/
def exteriorColouring : (graph.induce {v | v ∉ core}).Coloring Palette :=
  .mk (fun v => initial v.val) (by
    intro u v h
    rcases h.2 with h | h
    · exact ((of_decide_eq_true (List.all_eq_true.mp initial_edges _ h)).resolve_left u.property).resolve_left v.property
    · exact (((of_decide_eq_true (List.all_eq_true.mp initial_edges _ h)).resolve_left v.property).resolve_left u.property).symm)


private theorem final_edges : edges.all (fun e => decide
    (finalColour e.1 ≠ finalColour e.2)) = true := by decide +kernel

/-- A genuine full endpoint exists when the allowed region is enlarged. -/
def repaired : graph.Coloring Palette := .mk finalColour (by
  intro u v h
  rcases h.2 with h | h
  · exact of_decide_eq_true (List.all_eq_true.mp final_edges _ h)
  · exact (of_decide_eq_true (List.all_eq_true.mp final_edges _ h)).symm)

theorem repaired_fixed : ∀ v : V, v ∉ ballThree → repaired v = initial v := by
  decide +kernel


private theorem triangle_rule {x y z : Palette} {X Y Z O : List Palette}
    (checked : ∀ a ∈ X, ∀ b ∈ Y, ∀ c ∈ Z, a ≠ b → a ≠ c → b ≠ c → a ∈ O)
    (hx : x ∈ X) (hy : y ∈ Y) (hz : z ∈ Z)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : x ∈ O :=
  checked x hx y hy z hz hxy hxz hyz


/-- Radius-two support is insufficient even for arbitrary recolouring,
not just for a prescribed sequence of Kempe moves. -/
theorem no_local_extension (K : graph.Coloring Palette)
    (fixed : ∀ v : V, v ∉ ballTwo → K v = initial v) : False := by
  have edge (u v : V) (h : graph.Adj u v) : K u ≠ K v := K.valid h

  have h0 : K 0 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have h1 : K 1 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have h12 : K 12 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have n13_0 : K 13 ≠ (0 : Palette) := by
    have h := edge 13 106 (by decide +kernel)
    rw [fixed 106 (by decide +kernel)] at h
    exact h

  have n13_1 : K 13 ≠ (1 : Palette) := by
    have h := edge 13 108 (by decide +kernel)
    rw [fixed 108 (by decide +kernel)] at h
    exact h

  have n13_3 : K 13 ≠ (3 : Palette) := by
    have h := edge 13 67 (by decide +kernel)
    rw [fixed 67 (by decide +kernel)] at h
    exact h

  have h13 : K 13 ∈ ([2] : List Palette) :=
    (by decide +kernel : ∀ x : Palette, x ≠ 0 → x ≠ 1 → x ≠ 3 → x ∈ [2]) _ n13_0 n13_1 n13_3

  have h15 : K 15 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have n17_2 : K 17 ≠ (2 : Palette) := by
    have h := edge 17 52 (by decide +kernel)
    rw [fixed 52 (by decide +kernel)] at h
    exact h

  have n17_3 : K 17 ≠ (3 : Palette) := by
    have h := edge 17 119 (by decide +kernel)
    rw [fixed 119 (by decide +kernel)] at h
    exact h

  have h17 : K 17 ∈ ([0,1] : List Palette) :=
    (by decide +kernel : ∀ x : Palette, x ≠ 2 → x ≠ 3 → x ∈ [0,1]) _ n17_2 n17_3

  have h18 : K 18 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have h19 : K 19 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have n20_2 : K 20 ≠ (2 : Palette) := by
    have h := edge 20 125 (by decide +kernel)
    rw [fixed 125 (by decide +kernel)] at h
    exact h

  have h20 : K 20 ∈ ([0,1,3] : List Palette) :=
    (by decide +kernel : ∀ x : Palette, x ≠ 2 → x ∈ [0,1,3]) _ n20_2

  have h42 : K 42 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have n43_0 : K 43 ≠ (0 : Palette) := by
    have h := edge 43 106 (by decide +kernel)
    rw [fixed 106 (by decide +kernel)] at h
    exact h

  have h43 : K 43 ∈ ([1,2,3] : List Palette) :=
    (by decide +kernel : ∀ x : Palette, x ≠ 0 → x ∈ [1,2,3]) _ n43_0

  have n44_0 : K 44 ≠ (0 : Palette) := by
    have h := edge 44 14 (by decide +kernel)
    rw [fixed 14 (by decide +kernel)] at h
    exact h

  have n44_3 : K 44 ≠ (3 : Palette) := by
    have h := edge 44 110 (by decide +kernel)
    rw [fixed 110 (by decide +kernel)] at h
    exact h

  have h44 : K 44 ∈ ([1,2] : List Palette) :=
    (by decide +kernel : ∀ x : Palette, x ≠ 0 → x ≠ 3 → x ∈ [1,2]) _ n44_0 n44_3

  have h45 : K 45 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have n46_0 : K 46 ≠ (0 : Palette) := by
    have h := edge 46 16 (by decide +kernel)
    rw [fixed 16 (by decide +kernel)] at h
    exact h

  have n46_3 : K 46 ≠ (3 : Palette) := by
    have h := edge 46 115 (by decide +kernel)
    rw [fixed 115 (by decide +kernel)] at h
    exact h

  have h46 : K 46 ∈ ([1,2] : List Palette) :=
    (by decide +kernel : ∀ x : Palette, x ≠ 0 → x ≠ 3 → x ∈ [1,2]) _ n46_0 n46_3

  have h47 : K 47 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have h48 : K 48 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have h49 : K 49 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have h50 : K 50 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have h51 : K 51 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have n68_1 : K 68 ≠ (1 : Palette) := by
    have h := edge 68 70 (by decide +kernel)
    rw [fixed 70 (by decide +kernel)] at h
    exact h

  have n68_2 : K 68 ≠ (2 : Palette) := by
    have h := edge 68 5 (by decide +kernel)
    rw [fixed 5 (by decide +kernel)] at h
    exact h

  have n68_3 : K 68 ≠ (3 : Palette) := by
    have h := edge 68 67 (by decide +kernel)
    rw [fixed 67 (by decide +kernel)] at h
    exact h

  have h68 : K 68 ∈ ([0] : List Palette) :=
    (by decide +kernel : ∀ x : Palette, x ≠ 1 → x ≠ 2 → x ≠ 3 → x ∈ [0]) _ n68_1 n68_2 n68_3

  have n82_1 : K 82 ≠ (1 : Palette) := by
    have h := edge 82 8 (by decide +kernel)
    rw [fixed 8 (by decide +kernel)] at h
    exact h

  have n82_3 : K 82 ≠ (3 : Palette) := by
    have h := edge 82 85 (by decide +kernel)
    rw [fixed 85 (by decide +kernel)] at h
    exact h

  have h82 : K 82 ∈ ([0,2] : List Palette) :=
    (by decide +kernel : ∀ x : Palette, x ≠ 1 → x ≠ 3 → x ∈ [0,2]) _ n82_1 n82_3

  have n83_0 : K 83 ≠ (0 : Palette) := by
    have h := edge 83 84 (by decide +kernel)
    rw [fixed 84 (by decide +kernel)] at h
    exact h

  have n83_1 : K 83 ≠ (1 : Palette) := by
    have h := edge 83 8 (by decide +kernel)
    rw [fixed 8 (by decide +kernel)] at h
    exact h

  have n83_2 : K 83 ≠ (2 : Palette) := by
    have h := edge 83 125 (by decide +kernel)
    rw [fixed 125 (by decide +kernel)] at h
    exact h

  have h83 : K 83 ∈ ([3] : List Palette) :=
    (by decide +kernel : ∀ x : Palette, x ≠ 0 → x ≠ 1 → x ≠ 2 → x ∈ [3]) _ n83_0 n83_1 n83_2

  have h102 : K 102 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have h103 : K 103 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have h104 : K 104 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have h105 : K 105 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have n107_3 : K 107 ≠ (3 : Palette) := by
    have h := edge 107 67 (by decide +kernel)
    rw [fixed 67 (by decide +kernel)] at h
    exact h

  have h107 : K 107 ∈ ([0,1,2] : List Palette) :=
    (by decide +kernel : ∀ x : Palette, x ≠ 3 → x ∈ [0,1,2]) _ n107_3

  have n109_0 : K 109 ≠ (0 : Palette) := by
    have h := edge 109 14 (by decide +kernel)
    rw [fixed 14 (by decide +kernel)] at h
    exact h

  have n109_1 : K 109 ≠ (1 : Palette) := by
    have h := edge 109 114 (by decide +kernel)
    rw [fixed 114 (by decide +kernel)] at h
    exact h

  have h109 : K 109 ∈ ([2,3] : List Palette) :=
    (by decide +kernel : ∀ x : Palette, x ≠ 0 → x ≠ 1 → x ∈ [2,3]) _ n109_0 n109_1

  have h113 : K 113 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have n117_3 : K 117 ≠ (3 : Palette) := by
    have h := edge 117 119 (by decide +kernel)
    rw [fixed 119 (by decide +kernel)] at h
    exact h

  have h117 : K 117 ∈ ([0,1,2] : List Palette) :=
    (by decide +kernel : ∀ x : Palette, x ≠ 3 → x ∈ [0,1,2]) _ n117_3

  have n118_1 : K 118 ≠ (1 : Palette) := by
    have h := edge 118 23 (by decide +kernel)
    rw [fixed 23 (by decide +kernel)] at h
    exact h

  have n118_2 : K 118 ≠ (2 : Palette) := by
    have h := edge 118 125 (by decide +kernel)
    rw [fixed 125 (by decide +kernel)] at h
    exact h

  have n118_3 : K 118 ≠ (3 : Palette) := by
    have h := edge 118 120 (by decide +kernel)
    rw [fixed 120 (by decide +kernel)] at h
    exact h

  have h118 : K 118 ∈ ([0] : List Palette) :=
    (by decide +kernel : ∀ x : Palette, x ≠ 1 → x ≠ 2 → x ≠ 3 → x ∈ [0]) _ n118_1 n118_2 n118_3

  have h121 : K 121 ∈ ([0,1,2,3] : List Palette) := (by decide +kernel : ∀ x : Palette, x ∈ [0,1,2,3]) _

  have n122_1 : K 122 ≠ (1 : Palette) := by
    have h := edge 122 70 (by decide +kernel)
    rw [fixed 70 (by decide +kernel)] at h
    exact h

  have n122_3 : K 122 ≠ (3 : Palette) := by
    have h := edge 122 33 (by decide +kernel)
    rw [fixed 33 (by decide +kernel)] at h
    exact h

  have h122 : K 122 ∈ ([0,2] : List Palette) :=
    (by decide +kernel : ∀ x : Palette, x ≠ 1 → x ≠ 3 → x ∈ [0,2]) _ n122_1 n122_3

  have n123_1 : K 123 ≠ (1 : Palette) := by
    have h := edge 123 73 (by decide +kernel)
    rw [fixed 73 (by decide +kernel)] at h
    exact h

  have n123_3 : K 123 ≠ (3 : Palette) := by
    have h := edge 123 72 (by decide +kernel)
    rw [fixed 72 (by decide +kernel)] at h
    exact h

  have h123 : K 123 ∈ ([0,2] : List Palette) :=
    (by decide +kernel : ∀ x : Palette, x ≠ 1 → x ≠ 3 → x ∈ [0,2]) _ n123_1 n123_3

  have n124_1 : K 124 ≠ (1 : Palette) := by
    have h := edge 124 76 (by decide +kernel)
    rw [fixed 76 (by decide +kernel)] at h
    exact h

  have n124_3 : K 124 ≠ (3 : Palette) := by
    have h := edge 124 33 (by decide +kernel)
    rw [fixed 33 (by decide +kernel)] at h
    exact h

  have h124 : K 124 ∈ ([0,2] : List Palette) :=
    (by decide +kernel : ∀ x : Palette, x ≠ 1 → x ≠ 3 → x ∈ [0,2]) _ n124_1 n124_3

  have t1 : K 43 ∈ ([1,3] : List Palette) :=

    triangle_rule (X := [1,2,3]) (Y := [2]) (Z := [0,1,2,3])
      (by decide +kernel) h43 h13 h102
      (edge 43 13 (by decide +kernel)) (edge 43 102 (by decide +kernel))
      (edge 13 102 (by decide +kernel))

  have t2 : K 102 ∈ ([0,1,3] : List Palette) :=

    triangle_rule (X := [0,1,2,3]) (Y := [2]) (Z := [1,3])
      (by decide +kernel) h102 h13 t1
      (edge 102 13 (by decide +kernel)) (edge 102 43 (by decide +kernel))
      (edge 13 43 (by decide +kernel))

  have t3 : K 107 ∈ ([0,1] : List Palette) :=

    triangle_rule (X := [0,1,2]) (Y := [2]) (Z := [0,1,3])
      (by decide +kernel) h107 h13 t2
      (edge 107 13 (by decide +kernel)) (edge 107 102 (by decide +kernel))
      (edge 13 102 (by decide +kernel))

  have t4 : K 17 ∈ ([1] : List Palette) :=

    triangle_rule (X := [0,1]) (Y := [0,1,2,3]) (Z := [0])
      (by decide +kernel) h17 h48 h118
      (edge 17 48 (by decide +kernel)) (edge 17 118 (by decide +kernel))
      (edge 48 118 (by decide +kernel))

  have t5 : K 48 ∈ ([2,3] : List Palette) :=

    triangle_rule (X := [0,1,2,3]) (Y := [1]) (Z := [0])
      (by decide +kernel) h48 t4 h118
      (edge 48 17 (by decide +kernel)) (edge 48 118 (by decide +kernel))
      (edge 17 118 (by decide +kernel))

  have t6 : K 18 ∈ ([2,3] : List Palette) :=

    triangle_rule (X := [0,1,2,3]) (Y := [0]) (Z := [0,1])
      (by decide +kernel) h18 h68 t3
      (edge 18 68 (by decide +kernel)) (edge 18 107 (by decide +kernel))
      (edge 68 107 (by decide +kernel))

  have t7 : K 107 ∈ ([1] : List Palette) :=

    triangle_rule (X := [0,1]) (Y := [2,3]) (Z := [0])
      (by decide +kernel) t3 t6 h68
      (edge 107 18 (by decide +kernel)) (edge 107 68 (by decide +kernel))
      (edge 18 68 (by decide +kernel))

  have t8 : K 121 ∈ ([1,2,3] : List Palette) :=

    triangle_rule (X := [0,1,2,3]) (Y := [2,3]) (Z := [0])
      (by decide +kernel) h121 t6 h68
      (edge 121 18 (by decide +kernel)) (edge 121 68 (by decide +kernel))
      (edge 18 68 (by decide +kernel))

  have t9 : K 104 ∈ ([0,2,3] : List Palette) :=

    triangle_rule (X := [0,1,2,3]) (Y := [2,3]) (Z := [1])
      (by decide +kernel) h104 t6 t7
      (edge 104 18 (by decide +kernel)) (edge 104 107 (by decide +kernel))
      (edge 18 107 (by decide +kernel))

  have t10 : K 19 ∈ ([1,3] : List Palette) :=

    triangle_rule (X := [0,1,2,3]) (Y := [0,2]) (Z := [0,2])
      (by decide +kernel) h19 h123 h124
      (edge 19 123 (by decide +kernel)) (edge 19 124 (by decide +kernel))
      (edge 123 124 (by decide +kernel))

  have t11 : K 20 ∈ ([1,3] : List Palette) :=

    triangle_rule (X := [0,1,3]) (Y := [0,1,2,3]) (Z := [0])
      (by decide +kernel) h20 h51 h118
      (edge 20 51 (by decide +kernel)) (edge 20 118 (by decide +kernel))
      (edge 51 118 (by decide +kernel))

  have t12 : K 51 ∈ ([1,2,3] : List Palette) :=

    triangle_rule (X := [0,1,2,3]) (Y := [1,3]) (Z := [0])
      (by decide +kernel) h51 t11 h118
      (edge 51 20 (by decide +kernel)) (edge 51 118 (by decide +kernel))
      (edge 20 118 (by decide +kernel))

  have t13 : K 20 ∈ ([1] : List Palette) :=

    triangle_rule (X := [1,3]) (Y := [3]) (Z := [0,1,2,3])
      (by decide +kernel) t11 h83 h113
      (edge 20 83 (by decide +kernel)) (edge 20 113 (by decide +kernel))
      (edge 83 113 (by decide +kernel))

  have t14 : K 113 ∈ ([0,2] : List Palette) :=

    triangle_rule (X := [0,1,2,3]) (Y := [1]) (Z := [3])
      (by decide +kernel) h113 t13 h83
      (edge 113 20 (by decide +kernel)) (edge 113 83 (by decide +kernel))
      (edge 20 83 (by decide +kernel))

  have t15 : K 45 ∈ ([0,3] : List Palette) :=

    triangle_rule (X := [0,1,2,3]) (Y := [1,2]) (Z := [1,2])
      (by decide +kernel) h45 h44 h46
      (edge 45 44 (by decide +kernel)) (edge 45 46 (by decide +kernel))
      (edge 44 46 (by decide +kernel))

  have t16 : K 121 ∈ ([1,3] : List Palette) :=

    triangle_rule (X := [1,2,3]) (Y := [0]) (Z := [0,2])
      (by decide +kernel) t8 h68 h122
      (edge 121 68 (by decide +kernel)) (edge 121 122 (by decide +kernel))
      (edge 68 122 (by decide +kernel))

  have t17 : K 122 ∈ ([2] : List Palette) :=

    triangle_rule (X := [0,2]) (Y := [0]) (Z := [1,3])
      (by decide +kernel) h122 h68 t16
      (edge 122 68 (by decide +kernel)) (edge 122 121 (by decide +kernel))
      (edge 68 121 (by decide +kernel))

  have t18 : K 102 ∈ ([0,3] : List Palette) :=

    triangle_rule (X := [0,1,3]) (Y := [0,2,3]) (Z := [1])
      (by decide +kernel) t2 t9 t7
      (edge 102 104 (by decide +kernel)) (edge 102 107 (by decide +kernel))
      (edge 104 107 (by decide +kernel))

  have t19 : K 124 ∈ ([0] : List Palette) :=

    triangle_rule (X := [0,2]) (Y := [1,3]) (Z := [2])
      (by decide +kernel) h124 t16 t17
      (edge 124 121 (by decide +kernel)) (edge 124 122 (by decide +kernel))
      (edge 121 122 (by decide +kernel))

  have t20 : K 15 ∈ ([1,3] : List Palette) :=

    triangle_rule (X := [0,1,2,3]) (Y := [0,2]) (Z := [0,2])
      (by decide +kernel) h15 h82 t14
      (edge 15 82 (by decide +kernel)) (edge 15 113 (by decide +kernel))
      (edge 82 113 (by decide +kernel))

  have t21 : K 117 ∈ ([0,2] : List Palette) :=

    triangle_rule (X := [0,1,2]) (Y := [1]) (Z := [2,3])
      (by decide +kernel) h117 t4 t5
      (edge 117 17 (by decide +kernel)) (edge 117 48 (by decide +kernel))
      (edge 17 48 (by decide +kernel))

  have t22 : K 50 ∈ ([0,2] : List Palette) :=

    triangle_rule (X := [0,1,2,3]) (Y := [1,3]) (Z := [1,3])
      (by decide +kernel) h50 t10 t16
      (edge 50 19 (by decide +kernel)) (edge 50 121 (by decide +kernel))
      (edge 19 121 (by decide +kernel))

  have t23 : K 123 ∈ ([2] : List Palette) :=

    triangle_rule (X := [0,2]) (Y := [1,3]) (Z := [0])
      (by decide +kernel) h123 t10 t19
      (edge 123 19 (by decide +kernel)) (edge 123 124 (by decide +kernel))
      (edge 19 124 (by decide +kernel))

  have t24 : K 51 ∈ ([2,3] : List Palette) :=

    triangle_rule (X := [1,2,3]) (Y := [1]) (Z := [0,2])
      (by decide +kernel) t12 t13 t14
      (edge 51 20 (by decide +kernel)) (edge 51 113 (by decide +kernel))
      (edge 20 113 (by decide +kernel))

  have t25 : K 1 ∈ ([0,1] : List Palette) :=

    triangle_rule (X := [0,1,2,3]) (Y := [2,3]) (Z := [2,3])
      (by decide +kernel) h1 t5 t24
      (edge 1 48 (by decide +kernel)) (edge 1 51 (by decide +kernel))
      (edge 48 51 (by decide +kernel))

  have t26 : K 117 ∈ ([0] : List Palette) :=

    triangle_rule (X := [0,2]) (Y := [1,3]) (Z := [2])
      (by decide +kernel) t21 t10 t23
      (edge 117 19 (by decide +kernel)) (edge 117 123 (by decide +kernel))
      (edge 19 123 (by decide +kernel))

  rcases (show K 45 = 0 ∨ K 45 = 3 by
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using t15) with branch | branch

  · have t27 : K 45 ∈ ([0] : List Palette) := by simp only [List.mem_singleton, branch]

    have t28 : K 0 ∈ ([1,2,3] : List Palette) :=

      triangle_rule (X := [0,1,2,3]) (Y := [0,1,2,3]) (Z := [0])
        (by decide +kernel) h0 h42 t27
        (edge 0 42 (by decide +kernel)) (edge 0 45 (by decide +kernel))
        (edge 42 45 (by decide +kernel))

    have t29 : K 42 ∈ ([1,2,3] : List Palette) :=

      triangle_rule (X := [0,1,2,3]) (Y := [1,2,3]) (Z := [0])
        (by decide +kernel) h42 t28 t27
        (edge 42 0 (by decide +kernel)) (edge 42 45 (by decide +kernel))
        (edge 0 45 (by decide +kernel))

    have t30 : K 103 ∈ ([1,2,3] : List Palette) :=

      triangle_rule (X := [0,1,2,3]) (Y := [1,3]) (Z := [0])
        (by decide +kernel) h103 t20 t27
        (edge 103 15 (by decide +kernel)) (edge 103 45 (by decide +kernel))
        (edge 15 45 (by decide +kernel))

    rcases (show K 48 = 2 ∨ K 48 = 3 by
      simpa only [List.mem_cons, List.not_mem_nil, or_false] using t5) with branch | branch

    · have t31 : K 48 ∈ ([2] : List Palette) := by simp only [List.mem_singleton, branch]

      have t32 : K 1 ∈ ([1] : List Palette) :=

        triangle_rule (X := [0,1]) (Y := [2]) (Z := [0,2])
          (by decide +kernel) t25 t31 t22
          (edge 1 48 (by decide +kernel)) (edge 1 50 (by decide +kernel))
          (edge 48 50 (by decide +kernel))

      have t33 : K 50 ∈ ([0] : List Palette) :=

        triangle_rule (X := [0,2]) (Y := [1]) (Z := [2])
          (by decide +kernel) t22 t32 t31
          (edge 50 1 (by decide +kernel)) (edge 50 48 (by decide +kernel))
          (edge 1 48 (by decide +kernel))

      have t34 : K 51 ∈ ([3] : List Palette) :=

        triangle_rule (X := [2,3]) (Y := [1]) (Z := [2])
          (by decide +kernel) t24 t32 t31
          (edge 51 1 (by decide +kernel)) (edge 51 48 (by decide +kernel))
          (edge 1 48 (by decide +kernel))

      have t35 : K 49 ∈ ([2,3] : List Palette) :=

        triangle_rule (X := [0,1,2,3]) (Y := [1]) (Z := [0])
          (by decide +kernel) h49 t32 t33
          (edge 49 1 (by decide +kernel)) (edge 49 50 (by decide +kernel))
          (edge 1 50 (by decide +kernel))

      have t36 : K 104 ∈ ([0] : List Palette) :=

        triangle_rule (X := [0,2,3]) (Y := [2,3]) (Z := [2,3])
          (by decide +kernel) t9 t6 t35
          (edge 104 18 (by decide +kernel)) (edge 104 49 (by decide +kernel))
          (edge 18 49 (by decide +kernel))

      have t37 : K 121 ∈ ([1] : List Palette) :=

        triangle_rule (X := [1,3]) (Y := [2,3]) (Z := [2,3])
          (by decide +kernel) t16 t6 t35
          (edge 121 18 (by decide +kernel)) (edge 121 49 (by decide +kernel))
          (edge 18 49 (by decide +kernel))

      have t38 : K 19 ∈ ([3] : List Palette) :=

        triangle_rule (X := [1,3]) (Y := [0]) (Z := [1])
          (by decide +kernel) t10 t33 t37
          (edge 19 50 (by decide +kernel)) (edge 19 121 (by decide +kernel))
          (edge 50 121 (by decide +kernel))

      have t39 : K 47 ∈ ([0,1,2] : List Palette) :=

        triangle_rule (X := [0,1,2,3]) (Y := [3]) (Z := [0,1,2,3])
          (by decide +kernel) h47 t34 h105
          (edge 47 51 (by decide +kernel)) (edge 47 105 (by decide +kernel))
          (edge 51 105 (by decide +kernel))

      have t40 : K 105 ∈ ([0,1,2] : List Palette) :=

        triangle_rule (X := [0,1,2,3]) (Y := [0,1,2]) (Z := [3])
          (by decide +kernel) h105 t39 t34
          (edge 105 47 (by decide +kernel)) (edge 105 51 (by decide +kernel))
          (edge 47 51 (by decide +kernel))

      have t41 : K 102 ∈ ([3] : List Palette) :=

        triangle_rule (X := [0,3]) (Y := [0]) (Z := [1])
          (by decide +kernel) t18 t36 t7
          (edge 102 104 (by decide +kernel)) (edge 102 107 (by decide +kernel))
          (edge 104 107 (by decide +kernel))

      have t42 : K 0 ∈ ([1,2] : List Palette) :=

        triangle_rule (X := [1,2,3]) (Y := [1,2,3]) (Z := [3])
          (by decide +kernel) t28 t29 t41
          (edge 0 42 (by decide +kernel)) (edge 0 102 (by decide +kernel))
          (edge 42 102 (by decide +kernel))

      have t43 : K 42 ∈ ([1,2] : List Palette) :=

        triangle_rule (X := [1,2,3]) (Y := [1,2]) (Z := [3])
          (by decide +kernel) t29 t42 t41
          (edge 42 0 (by decide +kernel)) (edge 42 102 (by decide +kernel))
          (edge 0 102 (by decide +kernel))

      have t44 : K 43 ∈ ([3] : List Palette) :=

        triangle_rule (X := [1,3]) (Y := [1,2]) (Z := [1,2])
          (by decide +kernel) t1 t42 h46
          (edge 43 0 (by decide +kernel)) (edge 43 46 (by decide +kernel))
          (edge 0 46 (by decide +kernel))

      have t45 : K 0 ∈ ([] : List Palette) :=

        triangle_rule (X := [1,2]) (Y := [3]) (Z := [3])
          (by decide +kernel) t42 t44 t41
          (edge 0 43 (by decide +kernel)) (edge 0 102 (by decide +kernel))
          (edge 43 102 (by decide +kernel))

      exact List.not_mem_nil t45

    · have t46 : K 48 ∈ ([3] : List Palette) := by simp only [List.mem_singleton, branch]

      have t47 : K 51 ∈ ([2] : List Palette) :=

        triangle_rule (X := [2,3]) (Y := [0,1]) (Z := [3])
          (by decide +kernel) t24 t25 t46
          (edge 51 1 (by decide +kernel)) (edge 51 48 (by decide +kernel))
          (edge 1 48 (by decide +kernel))

      have t48 : K 19 ∈ ([1] : List Palette) :=

        triangle_rule (X := [1,3]) (Y := [3]) (Z := [0,2])
          (by decide +kernel) t10 t46 t22
          (edge 19 48 (by decide +kernel)) (edge 19 50 (by decide +kernel))
          (edge 48 50 (by decide +kernel))

      have t49 : K 121 ∈ ([3] : List Palette) :=

        triangle_rule (X := [1,3]) (Y := [1]) (Z := [0,2])
          (by decide +kernel) t16 t48 t22
          (edge 121 19 (by decide +kernel)) (edge 121 50 (by decide +kernel))
          (edge 19 50 (by decide +kernel))

      have t50 : K 113 ∈ ([0] : List Palette) :=

        triangle_rule (X := [0,2]) (Y := [1]) (Z := [2])
          (by decide +kernel) t14 t13 t47
          (edge 113 20 (by decide +kernel)) (edge 113 51 (by decide +kernel))
          (edge 20 51 (by decide +kernel))

      have t51 : K 47 ∈ ([0,1,3] : List Palette) :=

        triangle_rule (X := [0,1,2,3]) (Y := [2]) (Z := [0,1,2,3])
          (by decide +kernel) h47 t47 h105
          (edge 47 51 (by decide +kernel)) (edge 47 105 (by decide +kernel))
          (edge 51 105 (by decide +kernel))

      have t52 : K 105 ∈ ([0,1,3] : List Palette) :=

        triangle_rule (X := [0,1,2,3]) (Y := [0,1,3]) (Z := [2])
          (by decide +kernel) h105 t51 t47
          (edge 105 47 (by decide +kernel)) (edge 105 51 (by decide +kernel))
          (edge 47 51 (by decide +kernel))

      have t53 : K 49 ∈ ([0,1,2] : List Palette) :=

        triangle_rule (X := [0,1,2,3]) (Y := [0,2]) (Z := [3])
          (by decide +kernel) h49 t22 t49
          (edge 49 50 (by decide +kernel)) (edge 49 121 (by decide +kernel))
          (edge 50 121 (by decide +kernel))

      have t54 : K 105 ∈ ([1,3] : List Palette) :=

        triangle_rule (X := [0,1,3]) (Y := [2]) (Z := [0])
          (by decide +kernel) t52 t47 t50
          (edge 105 51 (by decide +kernel)) (edge 105 113 (by decide +kernel))
          (edge 51 113 (by decide +kernel))

      have t55 : K 82 ∈ ([2] : List Palette) :=

        triangle_rule (X := [0,2]) (Y := [3]) (Z := [0])
          (by decide +kernel) h82 h83 t50
          (edge 82 83 (by decide +kernel)) (edge 82 113 (by decide +kernel))
          (edge 83 113 (by decide +kernel))

      have t56 : K 15 ∈ ([1] : List Palette) :=

        triangle_rule (X := [1,3]) (Y := [2]) (Z := [2,3])
          (by decide +kernel) t20 t55 h109
          (edge 15 82 (by decide +kernel)) (edge 15 109 (by decide +kernel))
          (edge 82 109 (by decide +kernel))

      have t57 : K 109 ∈ ([3] : List Palette) :=

        triangle_rule (X := [2,3]) (Y := [1]) (Z := [2])
          (by decide +kernel) h109 t56 t55
          (edge 109 15 (by decide +kernel)) (edge 109 82 (by decide +kernel))
          (edge 15 82 (by decide +kernel))

      have t58 : K 103 ∈ ([2] : List Palette) :=

        triangle_rule (X := [1,2,3]) (Y := [1]) (Z := [1,3])
          (by decide +kernel) t30 t56 t54
          (edge 103 15 (by decide +kernel)) (edge 103 105 (by decide +kernel))
          (edge 15 105 (by decide +kernel))

      have t59 : K 105 ∈ ([3] : List Palette) :=

        triangle_rule (X := [1,3]) (Y := [1]) (Z := [2])
          (by decide +kernel) t54 t56 t58
          (edge 105 15 (by decide +kernel)) (edge 105 103 (by decide +kernel))
          (edge 15 103 (by decide +kernel))

      have t60 : K 18 ∈ ([2] : List Palette) :=

        triangle_rule (X := [2,3]) (Y := [0,1,2]) (Z := [3])
          (by decide +kernel) t6 t53 t49
          (edge 18 49 (by decide +kernel)) (edge 18 121 (by decide +kernel))
          (edge 49 121 (by decide +kernel))

      have t61 : K 49 ∈ ([0,1] : List Palette) :=

        triangle_rule (X := [0,1,2]) (Y := [2]) (Z := [3])
          (by decide +kernel) t53 t60 t49
          (edge 49 18 (by decide +kernel)) (edge 49 121 (by decide +kernel))
          (edge 18 121 (by decide +kernel))

      have t62 : K 104 ∈ ([0,3] : List Palette) :=

        triangle_rule (X := [0,2,3]) (Y := [2]) (Z := [1])
          (by decide +kernel) t9 t60 t7
          (edge 104 18 (by decide +kernel)) (edge 104 107 (by decide +kernel))
          (edge 18 107 (by decide +kernel))

      have t63 : K 42 ∈ ([1,3] : List Palette) :=

        triangle_rule (X := [1,2,3]) (Y := [0]) (Z := [2])
          (by decide +kernel) t29 t27 t58
          (edge 42 45 (by decide +kernel)) (edge 42 103 (by decide +kernel))
          (edge 45 103 (by decide +kernel))

      have t64 : K 47 ∈ ([0,1] : List Palette) :=

        triangle_rule (X := [0,1,3]) (Y := [2]) (Z := [3])
          (by decide +kernel) t51 t47 t59
          (edge 47 51 (by decide +kernel)) (edge 47 105 (by decide +kernel))
          (edge 51 105 (by decide +kernel))

      have t65 : K 1 ∈ ([] : List Palette) :=

        triangle_rule (X := [0,1]) (Y := [0,1]) (Z := [0,1])
          (by decide +kernel) t25 t64 t61
          (edge 1 47 (by decide +kernel)) (edge 1 49 (by decide +kernel))
          (edge 47 49 (by decide +kernel))

      exact List.not_mem_nil t65

  · have t66 : K 45 ∈ ([3] : List Palette) := by simp only [List.mem_singleton, branch]

    have t67 : K 0 ∈ ([0,1,2] : List Palette) :=

      triangle_rule (X := [0,1,2,3]) (Y := [0,1,2,3]) (Z := [3])
        (by decide +kernel) h0 h42 t66
        (edge 0 42 (by decide +kernel)) (edge 0 45 (by decide +kernel))
        (edge 42 45 (by decide +kernel))

    have t68 : K 42 ∈ ([0,1,2] : List Palette) :=

      triangle_rule (X := [0,1,2,3]) (Y := [0,1,2]) (Z := [3])
        (by decide +kernel) h42 t67 t66
        (edge 42 0 (by decide +kernel)) (edge 42 45 (by decide +kernel))
        (edge 0 45 (by decide +kernel))

    have t69 : K 15 ∈ ([1] : List Palette) :=

      triangle_rule (X := [1,3]) (Y := [3]) (Z := [0,1,2,3])
        (by decide +kernel) t20 t66 h103
        (edge 15 45 (by decide +kernel)) (edge 15 103 (by decide +kernel))
        (edge 45 103 (by decide +kernel))

    have t70 : K 103 ∈ ([0,2] : List Palette) :=

      triangle_rule (X := [0,1,2,3]) (Y := [1]) (Z := [3])
        (by decide +kernel) h103 t69 t66
        (edge 103 15 (by decide +kernel)) (edge 103 45 (by decide +kernel))
        (edge 15 45 (by decide +kernel))

    have t71 : K 109 ∈ ([2] : List Palette) :=

      triangle_rule (X := [2,3]) (Y := [1]) (Z := [3])
        (by decide +kernel) h109 t69 t66
        (edge 109 15 (by decide +kernel)) (edge 109 45 (by decide +kernel))
        (edge 15 45 (by decide +kernel))

    have t72 : K 82 ∈ ([0] : List Palette) :=

      triangle_rule (X := [0,2]) (Y := [1]) (Z := [2])
        (by decide +kernel) h82 t69 t71
        (edge 82 15 (by decide +kernel)) (edge 82 109 (by decide +kernel))
        (edge 15 109 (by decide +kernel))

    have t73 : K 113 ∈ ([2] : List Palette) :=

      triangle_rule (X := [0,2]) (Y := [1]) (Z := [0])
        (by decide +kernel) t14 t69 t72
        (edge 113 15 (by decide +kernel)) (edge 113 82 (by decide +kernel))
        (edge 15 82 (by decide +kernel))

    have t74 : K 105 ∈ ([0,2,3] : List Palette) :=

      triangle_rule (X := [0,1,2,3]) (Y := [1]) (Z := [0,2])
        (by decide +kernel) h105 t69 t70
        (edge 105 15 (by decide +kernel)) (edge 105 103 (by decide +kernel))
        (edge 15 103 (by decide +kernel))

    have t75 : K 105 ∈ ([0,3] : List Palette) :=

      triangle_rule (X := [0,2,3]) (Y := [1]) (Z := [2])
        (by decide +kernel) t74 t69 t73
        (edge 105 15 (by decide +kernel)) (edge 105 113 (by decide +kernel))
        (edge 15 113 (by decide +kernel))

    have t76 : K 51 ∈ ([3] : List Palette) :=

      triangle_rule (X := [2,3]) (Y := [1]) (Z := [2])
        (by decide +kernel) t24 t13 t73
        (edge 51 20 (by decide +kernel)) (edge 51 113 (by decide +kernel))
        (edge 20 113 (by decide +kernel))

    have t77 : K 44 ∈ ([1] : List Palette) :=

      triangle_rule (X := [1,2]) (Y := [3]) (Z := [2])
        (by decide +kernel) h44 t66 t71
        (edge 44 45 (by decide +kernel)) (edge 44 109 (by decide +kernel))
        (edge 45 109 (by decide +kernel))

    have t78 : K 47 ∈ ([1,2] : List Palette) :=

      triangle_rule (X := [0,1,2,3]) (Y := [3]) (Z := [0,3])
        (by decide +kernel) h47 t76 t75
        (edge 47 51 (by decide +kernel)) (edge 47 105 (by decide +kernel))
        (edge 51 105 (by decide +kernel))

    have t79 : K 105 ∈ ([0] : List Palette) :=

      triangle_rule (X := [0,3]) (Y := [1,2]) (Z := [3])
        (by decide +kernel) t75 t78 t76
        (edge 105 47 (by decide +kernel)) (edge 105 51 (by decide +kernel))
        (edge 47 51 (by decide +kernel))

    have t80 : K 47 ∈ ([1] : List Palette) :=

      triangle_rule (X := [1,2]) (Y := [0,2]) (Z := [0])
        (by decide +kernel) t78 t70 t79
        (edge 47 103 (by decide +kernel)) (edge 47 105 (by decide +kernel))
        (edge 103 105 (by decide +kernel))

    have t81 : K 103 ∈ ([2] : List Palette) :=

      triangle_rule (X := [0,2]) (Y := [1]) (Z := [0])
        (by decide +kernel) t70 t80 t79
        (edge 103 47 (by decide +kernel)) (edge 103 105 (by decide +kernel))
        (edge 47 105 (by decide +kernel))

    have t82 : K 48 ∈ ([2] : List Palette) :=

      triangle_rule (X := [2,3]) (Y := [3]) (Z := [0])
        (by decide +kernel) t5 t76 h118
        (edge 48 51 (by decide +kernel)) (edge 48 118 (by decide +kernel))
        (edge 51 118 (by decide +kernel))

    have t83 : K 1 ∈ ([0] : List Palette) :=

      triangle_rule (X := [0,1]) (Y := [1]) (Z := [0,1,2,3])
        (by decide +kernel) t25 t80 h49
        (edge 1 47 (by decide +kernel)) (edge 1 49 (by decide +kernel))
        (edge 47 49 (by decide +kernel))

    have t84 : K 49 ∈ ([2,3] : List Palette) :=

      triangle_rule (X := [0,1,2,3]) (Y := [0]) (Z := [1])
        (by decide +kernel) h49 t83 t80
        (edge 49 1 (by decide +kernel)) (edge 49 47 (by decide +kernel))
        (edge 1 47 (by decide +kernel))

    have t85 : K 1 ∈ ([] : List Palette) :=

      triangle_rule (X := [0]) (Y := [2]) (Z := [0,2])
        (by decide +kernel) t83 t82 t22
        (edge 1 48 (by decide +kernel)) (edge 1 50 (by decide +kernel))
        (edge 48 50 (by decide +kernel))

    exact List.not_mem_nil t85


private theorem closes (S T : List V)
    (checked : edges.all (fun e => decide ((e.1 ∈ S → e.2 ∈ T) ∧
      (e.2 ∈ S → e.1 ∈ T))) = true) :
    ∀ u ∈ S, ∀ v, graph.Adj u v → v ∈ T := by
  intro u hu v h
  rcases h.2 with h | h
  · exact (of_decide_eq_true (List.all_eq_true.mp checked _ h)).1 hu
  · exact (of_decide_eq_true (List.all_eq_true.mp checked _ h)).2 hu

/-- Every changed vertex forced by the obstruction lies beyond two edges
from every deleted source vertex. -/
theorem outside_far (v : V) (outside : v ∉ ballTwo) :
    ∀ r ∈ core, v ≠ r ∧ ¬ graph.Adj r v ∧
      ∀ u, ¬ (graph.Adj r u ∧ graph.Adj u v) := by
  have one := closes core ballOne (by decide +kernel)
  have two := closes ballOne ballTwo (by decide +kernel)
  have inc : ∀ v : V, v ∈ core ∨ v ∈ ballOne → v ∈ ballTwo := by decide +kernel
  intro r hr
  refine ⟨(fun h => outside (h ▸ inc r (Or.inl hr))),
    (fun h => outside (inc v (Or.inr (one r hr v h)))), ?_⟩
  intro u h
  exact outside (two u (one r hr u h.1) v h.2)

/-- Every successful reconstruction changes at least one exterior vertex
farther than two edges from the entire deleted core. -/
theorem reconstruction_changes_far (K : graph.Coloring Palette) :
    ∃ v : V, K v ≠ initial v ∧ ∀ r ∈ core, v ≠ r ∧
      ¬ graph.Adj r v ∧ ∀ u, ¬ (graph.Adj r u ∧ graph.Adj u v) := by
  classical
  have witness : ∃ v : V, v ∉ ballTwo ∧ K v ≠ initial v := by
    by_contra h
    push Not at h
    exact no_local_extension K h
  obtain ⟨v, hv, changed⟩ := witness
  exact ⟨v, changed, outside_far v hv⟩

/-- The observed obstruction also applies in larger graphs that preserve
its incidences and the specified outer colours. -/
theorem transport {W : Type*} {H : SimpleGraph W} (f : graph →g H)
    (K : H.Coloring Palette)
    (fixed : ∀ v : V, v ∉ ballTwo → K (f v) = initial v) : False :=
  no_local_extension (K.comp f) fixed

/-- A displayed route towards the core, used only to verify the positive
endpoint's spatial bound. -/
def parentData : List V := [42,1,52,128,63,68,72,78,82,87,96,97,12,102,109,105,44,48,49,50,51,53,119,118,131,139,74,88,136,69,75,138,147,122,108,85,153,158,100,85,141,161,12,102,45,103,45,47,50,49,50,47,17,22,119,120,131,21,25,26,129,136,64,29,144,4,32,68,18,5,68,5,124,123,73,33,124,111,35,153,81,112,15,113,83,82,8,134,87,90,134,9,143,96,160,40,41,16,151,34,16,11,12,103,49,105,13,18,13,15,44,114,14,105,82,46,16,19,51,117,118,49,121,19,121,20,22,2,126,127,73,23,23,24,23,139,25,30,25,75,27,88,136,141,146,147,70,69,33,32,41,71,32,35,85,36,39,89,38,157,161,100]

def parent (v : V) : V := parentData.get ⟨v.val, by simp [parentData]⟩

def Hop (u v : V) : Prop := u = v ∨ graph.Adj u v
instance (u v) : Decidable (Hop u v) := inferInstanceAs (Decidable (_ ∨ _))

private theorem three_hops_checked : ∀ v : V, v ∈ ballThree →
    parent (parent (parent v)) ∈ core ∧
    Hop (parent (parent (parent v))) (parent (parent v)) ∧
    Hop (parent (parent v)) (parent v) ∧ Hop (parent v) v := by
  decide +kernel

/-- Every change in the positive endpoint is reachable from the deleted
core in at most three edges. `Hop` permits an idle step. -/
theorem repaired_changes_near (v : V) (changed : repaired v ≠ initial v) :
    ∃ r ∈ core, ∃ x y, Hop r x ∧ Hop x y ∧ Hop y v := by
  have inside : v ∈ ballThree := by
    by_contra h
    exact changed (repaired_fixed v h)
  obtain ⟨root, first, second, third⟩ := three_hops_checked v inside
  exact ⟨parent (parent (parent v)), root, parent (parent v), parent v,
    first, second, third⟩

end SimpleGraph.LocalRepairRadius
