import MettapediaFourColor.StripChoiceLoops
import MettapediaFourColor.KempeChromogramMatching
import MettapediaFourColor.GraphTraceAlignment

/-!
# A majority component repairs a source with incompatible choice loops

Five consecutive active ports among eight guarantee an adjacent whole
component. Each of the four adjacent choices satisfies the joint forest
guard on D0063. The general forest theorem supplies the interior colouring;
no table of complete source colourings or matching layouts is stored.

The resulting source and exterior witnesses agree at all ten boundary ports.
The statement retains explicit Kempe closure of the exterior. It concerns
one input boundary, not all-input reducibility or geometric coverage.
-/

namespace FourColor.StripChoiceLoopRepair

open SimpleGraph Color StripChoiceLoops TriangleStripLists
open FiveTriangleCollapseObstruction KempeBoundarySplit
open Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

abbrev Terminal := GraphTrace lower.graph lower.boundary

def complete (b : Boundary) (C : coreGraph.Coloring Color) : Fin 17 → Color :=
  fun v => Fin.addCases (m := 10) (n := 7) (motive := fun _ => Color) b (fun i => C i) v

@[simp] theorem complete_port (b : Boundary) (C : coreGraph.Coloring Color) (i : Fin 10) :
    complete b C (port i) = b i := by simp [complete,port]

@[simp] theorem complete_vertex (b : Boundary) (C : coreGraph.Coloring Color) (i : Fin 7) :
    complete b C (vertex i) = C i := by simp [complete,vertex]

theorem complete_valid (b : Boundary) (C : coreGraph.Coloring Color)
    (proper : ProperBoundary b) (fit : ∀ v, C v ∈ allowed b v) :
    ∀ u v, lower.graph.Adj u v → complete b C u ≠ complete b C v := by
  have crossing (v : Fin 7) (i : Fin 10) (h : lower.graph.Adj (vertex v) (port i)) :
      C v ≠ b i := (Finset.mem_filter.mp (fit v)).2 i ((attachments_complete v i).mp h)
  intro u
  refine Fin.addCases (m := 10) (n := 7)
    (motive := fun u => ∀ v, lower.graph.Adj u v → complete b C u ≠ complete b C v)
    (fun i => ?_) (fun i => ?_) u
  · intro v
    refine Fin.addCases (m := 10) (n := 7)
      (motive := fun v => lower.graph.Adj (port i) v →
        complete b C (port i) ≠ complete b C v) (fun j => ?_) (fun j => ?_) v
    · intro h
      change complete b C (port i) ≠ complete b C (port j)
      simpa only [complete_port] using proper i j h
    · intro h
      change complete b C (port i) ≠ complete b C (vertex j)
      simpa only [complete_port,complete_vertex] using (crossing j i h.symm).symm
  · intro v
    refine Fin.addCases (m := 10) (n := 7)
      (motive := fun v => lower.graph.Adj (vertex i) v →
        complete b C (vertex i) ≠ complete b C v) (fun j => ?_) (fun j => ?_) v
    · intro h
      change complete b C (vertex i) ≠ complete b C (port j)
      simpa only [complete_port,complete_vertex] using crossing i j h
    · intro h
      change complete b C (vertex i) ≠ complete b C (vertex j)
      simpa only [complete_vertex] using C.valid h

theorem guard_trace (b : Boundary) (choice : Fin 2 → Color) (n : ℕ)
    (proper : ProperBoundary b) (guard : Guard .d0063 (allowed b) choice n) :
    Terminal (trace (List.ofFn b)) := by
  obtain ⟨C,fit,_⟩ := guard_colouring .d0063 (allowed b) choice n guard
  let K : lower.graph.Coloring Color :=
    .mk (complete b C) (fun h => complete_valid b C proper fit _ _ h)
  refine ⟨K,?_⟩
  have he : lower.boundary.map K = List.ofFn b := by
    change (List.finRange 10).map (fun i => complete b C (port i)) = _
    rw [← List.ofFn_eq_map]
    congr 1
    funext i
    exact complete_port b C i
  rw [he]

def word : Fin 10 → Color := ![c1,c1,c1,c1,c2,c2,c3,c1,c1,c3]
def colour (i : Fin 10) := EdgePerm.e321 (word i)
def embed : Fin 8 → Fin 10 := ![0,1,2,3,4,5,7,8]
def rank : Fin 10 → Fin 8 := ![0,1,2,3,4,5,0,6,7,0]
def block : Finset (Fin 8) := {1,2,3,4,5}

theorem coordinates : (∀ i, rank (embed i) = i) ∧
    (∀ i, colour i ≠ c1 → embed (rank i) = i) ∧
    (∀ i, colour (embed i) ≠ c1) := by decide +kernel

private instance {n : ℕ} (a b c d : Fin n) : Decidable (ChordsCross a b c d) := by
  unfold ChordsCross
  infer_instance

theorem order : ∀ a b x y,
    ¬ ChordsCross (embed a) (embed x) (embed b) (embed y) →
      ¬ ChordsCross a x b y := by decide +kernel

theorem convex : ∀ a ∈ block, ∀ b ∈ block, ∀ x, a < x → x < b → x ∈ block := by
  decide +kernel

theorem majority : 8 < 2 * block.card := by decide +kernel

def answer (i : Fin 4) : List Color :=
  List.ofFn (KempeIntervalRepair.switch colour ⟨i.val + 1,by omega⟩ ⟨i.val + 2,by omega⟩)

def readBoundary (et : List Color) (i : Fin 10) : Color :=
  (untrace 0 et)[i.val]?.getD 0

/-- Only the two joint anchor values are specified; the forest is rebuilt. -/
def choice : Fin 4 → Fin 2 → Color := ![![c1,c1],![c3,c0],![c0,c0],![c1,c1]]

theorem guarded_answers : ∀ i,
    trace (List.ofFn (readBoundary (answer i))) = answer i ∧
    ProperBoundary (readBoundary (answer i)) ∧
    Guard .d0063 (allowed (readBoundary (answer i))) (choice i) 2 := by
  unfold Guard ColoringListPropagation.Supported
  decide +kernel

theorem adjacent_answers : ∀ a ∈ block, ∀ b ∈ block, b.val = a.val + 1 →
    ∃ i : Fin 4, List.ofFn (KempeIntervalRepair.switch colour (embed a) (embed b)) =
      answer i := by decide +kernel

/-- One structural matching law and one structural reconstruction law
compose through all four possible adjacent component choices. -/
theorem repair : KempeCoclosure Terminal (List.ofFn word) := by
  apply kempeCoclosure_of_map EdgePerm.e321
  change KempeCoclosure Terminal (List.ofFn colour)
  apply KempeChromogramMatching.majority_coclosure colour embed rank
    coordinates.1 coordinates.2.1 coordinates.2.2 order block convex majority
  intro a ha b hb hadj
  obtain ⟨i,hi⟩ := adjacent_answers a ha b hb hadj
  rw [hi]
  intro outside _ held
  obtain ⟨ht,hb,hg⟩ := guarded_answers i
  exact ⟨answer i,ht ▸ guard_trace _ (choice i) 2 hb hg,held⟩

theorem boundary_word : trace (List.ofFn (boundary false)) = List.ofFn word := by
  decide +kernel

/-- Source and exterior are genuine compatible colourings, with the same
exterior predicate retained throughout the component choice. -/
theorem compatible {V : Type*} (H : SimpleGraph V) (ports : Fin 10 → V)
    (closed : KempeClosed (GraphTrace H (List.ofFn ports)))
    (initial : GraphTrace H (List.ofFn ports) (trace (List.ofFn (boundary false)))) :
    ∃ D : H.Coloring Color, ∃ K : lower.graph.Coloring Color,
      ∀ i, K (port i) = D (ports i) := by
  rw [boundary_word] at initial
  obtain ⟨et,⟨K,hK⟩,⟨D,hD⟩⟩ := repair _ closed initial
  have boundary_eq : lower.boundary = List.ofFn port := by decide +kernel
  obtain ⟨aligned,ha⟩ := GraphTraceAlignment.align lower.boundary K ((List.ofFn ports).map D)
    (by rw [boundary_eq]; simp) (hK.symm.trans hD)
  have eq : (fun i => aligned (port i)) = (fun i => D (ports i)) :=
    List.ofFn_injective (by simpa only [boundary_eq,List.map_ofFn,Function.comp_def] using ha)
  exact ⟨D,aligned,fun i => congrFun eq i⟩

end FourColor.StripChoiceLoopRepair
