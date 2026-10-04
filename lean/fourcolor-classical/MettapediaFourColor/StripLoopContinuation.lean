import MettapediaFourColor.StripLoopMatching
import MettapediaFourColor.StripChoiceLoopRepair

/-!
# Composed repair of the second conditional-choice loop

Four intermediate boundaries compose existing balanced and one-short laws
with a majority-cut selector. Every terminal branch consumes the joint
forest reconstruction theorem. Paired switches share the same exterior
matching, and earlier repairs are invoked with that exterior retained.
The four stages do not constitute all-input source reducibility or coverage.
-/

namespace FourColor.StripLoopContinuation

open Color SimpleGraph StripChoiceLoops StripChoiceLoopRepair TriangleStripLists
open KempeIntervalRepair KempeBoundarySplit FiveTriangleCollapseObstruction
open Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

def word : Fin 4 → Fin 10 → Color :=
  ![![c1,c1,c1,c1,c2,c2,c3,c3,c3,c3],
    ![c1,c2,c2,c2,c2,c2,c2,c2,c2,c1],
    ![c1,c2,c2,c2,c3,c3,c2,c2,c2,c1],
    ![c1,c2,c2,c2,c3,c3,c1,c1,c1,c2]]

def palette : Fin 4 → EdgePerm := ![.e321,.e321,.e123,.e321]
def colour (s : Fin 4) (i : Fin 10) := palette s (word s i)

/-- The small joint anchor domain is searched once when proving a source
contract. The resulting theorem reconstructs the entire forest. -/
def Direct (et : List Color) : Prop :=
  trace (List.ofFn (readBoundary et)) = et ∧ ProperBoundary (readBoundary et) ∧
    ∃ a b : Color, Guard .d0063 (allowed (readBoundary et)) ![a,b] 4

instance (et) : Decidable (Direct et) := by
  unfold Direct Guard ColoringListPropagation.Supported
  infer_instance

theorem direct_coclosure {et} (h : Direct et) : KempeCoclosure Terminal et := by
  obtain ⟨ht,hb,a,b,hg⟩ := h
  intro outside _ held
  exact ⟨et,ht ▸ guard_trace _ ![a,b] 4 hb hg,held⟩

def Ready (s : Fin 4) (et : List Color) : Prop :=
  (∃ t : Fin 4, ∃ g : EdgePerm, t.val < s.val ∧ et.map g = List.ofFn (word t)) ∨ Direct et

instance (s et) : Decidable (Ready s et) := by unfold Ready; infer_instance

def balancedStage : Fin 2 → Fin 4 := ![0,2]
def half : Fin 2 → ℕ := ![3,4]
def positions : Fin 2 → List (Fin 10) := ![[0,1,2,3,4,5],[3,4,5,6,7,8,1,2]]
def embed (t : Fin 2) (i : Fin (2 * half t)) : Fin 10 := (positions t)[i.val]?.getD 0
def rank (t : Fin 2) (i : Fin 10) : Fin (2 * half t) :=
  ⟨(positions t).idxOf i % (2 * half t),Nat.mod_lt _ (by fin_cases t <;> decide)⟩

instance (t : Fin 2) : NeZero (2 * half t) := ⟨by fin_cases t <;> decide⟩

def moves : (t : Fin 2) → List (Fin (2 * half t)) | 0 => [2] | 1 => [3]

theorem coordinates : ∀ t,
    (∀ i, rank t (embed t i) = i) ∧
    (∀ i, colour (balancedStage t) i ≠ c1 → embed t (rank t i) = i) ∧
    (∀ i, colour (balancedStage t) (embed t i) ≠ c1) := by decide +kernel

theorem cycles : ∀ t a b c, KempeBalancedBlock.cyclic a b c →
    KempeBalancedBlock.cyclic (embed t a) (embed t b) (embed t c) := by decide +kernel

theorem ears_ready : ∀ t i j, i.val < half t → j.val < half t → j.val = i.val + 1 →
    Ready (balancedStage t) (List.ofFn
      (switch (colour (balancedStage t)) (embed t i) (embed t j))) := by decide +kernel

theorem nested_ready : ∀ t, Ready (balancedStage t) (List.ofFn
    (KempeBalancedBlock.batch (embed t) (moves t) (colour (balancedStage t)))) := by
  decide +kernel

theorem loop_active : ∀ i, colour 1 i ≠ c1 := by decide +kernel

theorem loop_single : ∀ a b, StripLoopMatching.good a b →
    Ready 1 (List.ofFn (switch (colour 1) a b)) := by decide +kernel

theorem loop_paired : Ready 1 (List.ofFn (switch (switch (colour 1) 0 5) 1 2)) := by
  decide +kernel

def shortPositions : Fin 8 → Fin 10 := ![8,9,0,1,2,3,6,7]
def shortRank (i : Fin 10) : Fin 8 :=
  ⟨(List.ofFn shortPositions).idxOf i % 8,Nat.mod_lt _ (by decide)⟩
def shortMoves (t : Fin 7) : List (Option (Fin 6)) :=
  match t.val with
  | 3 => [none] | 4 => [some 0,some 1] | 5 => [none] | _ => [some 1,some 2]

theorem short_coordinates :
    (∀ i, shortRank (shortPositions i) = i) ∧
    (∀ i, colour 3 i ≠ c1 → shortPositions (shortRank i) = i) ∧
    (∀ i, colour 3 (shortPositions i) ≠ c1) := by decide +kernel

theorem short_cycles : ∀ a b c, KempeBalancedBlock.cyclic a b c →
    KempeBalancedBlock.cyclic (shortPositions a) (shortPositions b) (shortPositions c) := by
  decide +kernel

theorem short_ears : ∀ i j : Fin 8, i.val < 3 → j.val < 3 → j.val = i.val + 1 →
    Ready 3 (List.ofFn (switch (colour 3) (shortPositions i) (shortPositions j))) := by
  decide +kernel

theorem punctured_ready : ∀ t : Fin 7, 3 ≤ t.val → Ready 3 (List.ofFn
    (KempeShortBlock.batch (k := 3) shortPositions t (shortMoves t) (colour 3))) := by
  decide +kernel

theorem stages (n : ℕ) : ∀ s : Fin 4, s.val < n →
    KempeCoclosure Terminal (List.ofFn (word s)) := by
  induction n with
  | zero => intro s hs; omega
  | succ n ih =>
    intro s hs
    have finish {et} (h : Ready s et) : KempeCoclosure Terminal et := by
      rcases h with ⟨t,g,ht,hg⟩ | h
      · apply kempeCoclosure_of_map g
        rw [hg]
        exact ih t (by omega)
      · exact direct_coclosure h
    by_cases hb : ∃ t, balancedStage t = s
    · obtain ⟨t,rfl⟩ := hb
      apply kempeCoclosure_of_map (palette (balancedStage t))
      change KempeCoclosure Terminal (List.ofFn (colour (balancedStage t)))
      apply KempeBalancedBlock.coclosure _ (embed t) (rank t)
        (coordinates t).1 (coordinates t).2.1 (coordinates t).2.2
        (KempeBalancedBlock.noncross_of_cyclic _ (cycles t))
      · exact fun i j hi hj hij => finish (ears_ready t i j hi hj hij)
      · exact finish (nested_ready t)
    · have cases : s = 1 ∨ s = 3 := by
        fin_cases s <;> simp_all [balancedStage,Fin.exists_fin_two]
      rcases cases with rfl | rfl
      · apply kempeCoclosure_of_map (palette 1)
        change KempeCoclosure Terminal (List.ofFn (colour 1))
        exact StripLoopMatching.coclosure _ loop_active
          (fun a b h => finish (loop_single a b h)) (finish loop_paired)
      · apply kempeCoclosure_of_map (palette 3)
        change KempeCoclosure Terminal (List.ofFn (colour 3))
        apply KempeShortBlock.coclosure (k := 3) (moves := shortMoves)
          _ shortPositions shortRank short_coordinates.1 short_coordinates.2.1
          short_coordinates.2.2
          (KempeBalancedBlock.noncross_of_cyclic _ short_cycles)
        · exact fun i j hi hj hij => finish (short_ears i j hi hj hij)
        · exact fun t ht => finish (punctured_ready t ht)

theorem source_trace : trace (List.ofFn (boundary true)) = List.ofFn (word 3) := by
  decide +kernel

theorem repair (s : Bool) : KempeCoclosure Terminal (trace (List.ofFn (boundary s))) := by
  cases s with
  | false => rw [boundary_word]; exact StripChoiceLoopRepair.repair
  | true => rw [source_trace]; exact stages 4 3 (by decide)

/-- Both loop inputs now yield genuine source and exterior colourings,
aligned at every ordered port, under the stated exterior closure premise. -/
theorem compatible {V : Type*} (s : Bool) (H : SimpleGraph V) (ports : Fin 10 → V)
    (closed : KempeClosed (GraphTrace H (List.ofFn ports)))
    (initial : GraphTrace H (List.ofFn ports) (trace (List.ofFn (boundary s)))) :
    ∃ D : H.Coloring Color, ∃ K : lower.graph.Coloring Color,
      ∀ i, K (port i) = D (ports i) := by
  obtain ⟨et,⟨K,hK⟩,⟨D,hD⟩⟩ := repair s _ closed initial
  have boundary_eq : lower.boundary = List.ofFn port := by decide +kernel
  obtain ⟨aligned,ha⟩ := GraphTraceAlignment.align lower.boundary K ((List.ofFn ports).map D)
    (by rw [boundary_eq]; simp) (hK.symm.trans hD)
  have eq : (fun i => aligned (port i)) = (fun i => D (ports i)) :=
    List.ofFn_injective (by simpa only [boundary_eq,List.map_ofFn,Function.comp_def] using ha)
  exact ⟨D,aligned,fun i => congrFun eq i⟩

end FourColor.StripLoopContinuation
