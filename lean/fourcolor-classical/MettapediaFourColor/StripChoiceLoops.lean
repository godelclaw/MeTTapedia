import MettapediaFourColor.TriangleStripLists
import Mettapedia.GraphTheory.Kempe.ListImplication

/-!
# Supported local choices with incompatible implication loops

Two proper D0063 boundaries leave nonempty, locally supported lists after
the initial forced colour is propagated. Each choice at core vertex zero
nevertheless implies its opposite around a path of actual core edges.
The shared implication-path theorem proves nonextension without enumerating
full colourings. The obstruction concerns fixed boundary colours; repair by
changing the exterior remains a separate question.

The decoded source and attribution are inherited from
FiveTriangleCollapseObstruction.
-/

namespace FourColor.StripChoiceLoops

open SimpleGraph ColoringListPropagation Color TriangleStripAnchors
open FiveTriangleCollapseObstruction

abbrev Boundary := Fin 10 → Color
abbrev coreGraph : SimpleGraph (Fin 7) := core .d0063

instance : DecidableRel coreGraph.Adj := by
  change DecidableRel (core .d0063).Adj
  infer_instance

def port (i : Fin 10) : Fin 17 := i.castAdd 7
def vertex (i : Fin 7) : Fin 17 := i.natAdd 10

def attachments : Fin 7 → List (Fin 10) :=
  ![[7,8,9],[3,4],[4,5,6],[1],[6,7],[1,2,3],[0,1,9]]

theorem attachments_complete : ∀ v i,
    lower.graph.Adj (vertex v) (port i) ↔ i ∈ attachments v := by decide +kernel

def allowed (b : Boundary) (v : Fin 7) : Finset Color :=
  Finset.univ.filter fun a => ∀ i ∈ attachments v, a ≠ b i

def boundary : Bool → Boundary
  | false => ![c0,c1,c0,c1,c0,c2,c0,c3,c2,c3]
  | true => ![c0,c1,c3,c1,c3,c0,c3,c2,c3,c2]

def ProperBoundary (b : Boundary) : Prop :=
  ∀ i j, lower.graph.Adj (port i) (port j) → b i ≠ b j

instance (b : Boundary) : Decidable (ProperBoundary b) := by
  unfold ProperBoundary
  infer_instance

theorem proper : ∀ s, ProperBoundary (boundary s) := by decide +kernel

/-- This single valid propagation step removes the already forced colour
from its neighbour. It leaves no empty list and no unsupported colour. -/
def stable (s : Bool) := run (allowed (boundary s)) [(6,3)]

theorem propagated_edge : coreGraph.Adj 6 3 := by decide +kernel

theorem supported : ∀ s, Supported coreGraph (stable s) := by
  unfold Supported
  decide +kernel

theorem nonempty : ∀ s v, (stable s v).Nonempty := by decide +kernel

theorem choices : ∀ s a, a ∈ stable s 0 → a = c0 ∨ a = c1 := by decide +kernel

def forwardLength : Bool → ℕ | false => 8 | true => 6

def forward : (s : Bool) → Fin (forwardLength s + 1) → Fin 7 × Color
  | false => ![(0,c0),(3,c3),(5,c2),(1,c3),(2,c1),(4,c2),(5,c3),(3,c0),(0,c1)]
  | true => ![(0,c0),(3,c2),(5,c0),(1,c2),(2,c1),(4,c0),(0,c1)]

def backward : Bool → Fin 6 → Fin 7 × Color
  | false => ![(0,c1),(4,c2),(1,c3),(5,c2),(4,c1),(0,c0)]
  | true => ![(0,c1),(4,c0),(1,c2),(5,c0),(4,c1),(0,c0)]

theorem forward_steps : ∀ s (i : Fin (forwardLength s)),
    Forces coreGraph (stable s) (forward s i.castSucc) (forward s i.succ) := by
  unfold Forces
  intro s
  cases s <;> decide +kernel

theorem backward_steps : ∀ s (i : Fin 5),
    Forces coreGraph (stable s) (backward s i.castSucc) (backward s i.succ) := by
  unfold Forces
  decide +kernel

theorem endpoints : ∀ s,
    forward s 0 = (0,c0) ∧ forward s (Fin.last (forwardLength s)) = (0,c1) ∧
    backward s 0 = (0,c1) ∧ backward s 5 = (0,c0) := by decide +kernel

/-- Both locally supported choices imply their opposite through the same
colouring witness. Independent edge support therefore cannot be glued. -/
theorem no_stable_colouring (s : Bool) :
    ¬ ∃ C : coreGraph.Coloring Color, ∀ v, C v ∈ stable s v := by
  rintro ⟨C,fit⟩
  obtain ⟨f0,fn,b0,bn⟩ := endpoints s
  rcases choices s (C 0) (fit 0) with h | h
  · have start : C (forward s 0).1 = (forward s 0).2 := by simpa only [f0] using h
    have finish := path_forces (stable s) C fit (forward s) (forward_steps s) start
      (Fin.last (forwardLength s))
    have opposite : C 0 = c1 := by simpa only [fn] using finish
    exact (by decide : c0 ≠ c1) (h.symm.trans opposite)
  · have start : C (backward s 0).1 = (backward s 0).2 := by simpa only [b0] using h
    have finish := path_forces (stable s) C fit (backward s) (backward_steps s) start 5
    have opposite : C 0 = c0 := by simpa only [bn] using finish
    exact (by decide : c1 ≠ c0) (h.symm.trans opposite)

theorem no_core (s : Bool) :
    ¬ ∃ C : coreGraph.Coloring Color, ∀ v, C v ∈ allowed (boundary s) v := by
  rintro ⟨C,fit⟩
  apply no_stable_colouring s
  exact ⟨C,run_sound C _ fit [(6,3)] (by simpa using propagated_edge)⟩

/-- The obstruction is in the exact decoded graph with its entire ordered
boundary, not merely in an abstract list instance. -/
theorem no_source (s : Bool) : ¬ ∃ C : lower.graph.Coloring Color,
    ∀ i, C (port i) = boundary s i := by
  rintro ⟨C,hC⟩
  apply no_core s
  let D : coreGraph.Coloring Color := .mk (fun v => C (vertex v))
    (fun {u v} huv => C.valid huv)
  refine ⟨D,fun v => Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  intro i hi
  change C (vertex v) ≠ boundary s i
  rw [← hC i]
  exact C.valid ((attachments_complete v i).mpr hi)

/-- Locally supported nonempty lists do not suffice on these cyclic cores. -/
theorem support_not_sufficient (s : Bool) :
    (∀ v, (stable s v).Nonempty) ∧ Supported coreGraph (stable s) ∧
      ¬ ∃ C : coreGraph.Coloring Color, ∀ v, C v ∈ stable s v :=
  ⟨nonempty s,supported s,no_stable_colouring s⟩

end FourColor.StripChoiceLoops
