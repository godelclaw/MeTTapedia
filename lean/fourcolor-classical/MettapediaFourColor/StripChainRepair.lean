import MettapediaFourColor.KempeAnchorSelection
import MettapediaFourColor.KempeBalancedBlock
import MettapediaFourColor.KempeShortBlock
import MettapediaFourColor.StripCriticalChain
import MettapediaFourColor.GraphTraceAlignment

/-!
# Repairing the two critical-chain boundaries

Eleven local stages use exact symbolic source reconstruction. Seven select
components by the arbitrary-width balanced-block law and three by its
one-short extension. One stage uses the retained-anchor interval criterion.
A stage either extends directly or enters
an earlier stage. Two components chosen together belong to the same matching.

Both initial boundaries obstruct every complete extension while their colours
are fixed. The repair reconstructs a complete source colouring compatible
with a colouring of the same exterior, whose boundary trace must change.
The exterior's Kempe closure is explicit. The finite stage laws do not
establish geometric occurrence supply or a physical recolouring history.
-/

namespace FourColor.StripChainRepair

open Color StripSymbolicRepair KempeIntervalRepair KempeAnchorSelection

def word : Fin 11 → Fin 11 → Color
  | 0 => ![c1,c1,c1,c1,c1,c1,c1,c2,c2,c3,c2]
  | 1 => ![c1,c1,c1,c2,c1,c2,c3,c1,c1,c2,c1]
  | 2 => ![c1,c1,c1,c2,c2,c2,c3,c1,c2,c1,c2]
  | 3 => ![c1,c2,c2,c1,c1,c2,c3,c1,c3,c1,c3]
  | 4 => ![c1,c2,c3,c2,c2,c3,c1,c2,c1,c3,c2]
  | 5 => ![c1,c2,c2,c1,c1,c2,c1,c3,c3,c1,c3]
  | 6 => ![c1,c1,c2,c1,c1,c2,c3,c1,c1,c2,c1]
  | 7 => ![c1,c2,c2,c1,c1,c1,c2,c3,c3,c1,c3]
  | 8 => ![c1,c2,c2,c1,c1,c1,c2,c1,c1,c1,c3]
  | 9 => ![c1,c2,c3,c2,c2,c3,c1,c2,c2,c3,c1]
  | 10 => ![c1,c2,c3,c3,c3,c3,c1,c3,c3,c3,c1]

def anchors : Fin 11 → Fin 3 → Fin 11
  | 0 => ![0,1,0]
  | 1 => ![0,8,0]
  | 2 => ![3,4,3]
  | 3 => ![0,2,0]
  | 4 => ![1,5,1]
  | 5 => ![0,3,0]
  | 6 => ![0,2,5]
  | 7 => ![1,6,1]
  | 8 => ![0,3,0]
  | 9 => ![0,1,0]
  | 10 => ![1,5,1]

def palette : Fin 11 → EdgePerm :=
  ![.e321,.e213,.e123,.e321,.e123,.e213,.e321,.e321,.e213,.e321,.e123]
def colour (s : Fin 11) (i : Fin 11) : Color := palette s (word s i)

def singles : Fin 11 → List (Fin 11 × Fin 11)
  | 0 => [(4,5),(5,6),(6,7),(7,8),(0,7)]
  | 1 => [(4,6),(6,7),(7,8)]
  | 2 => [(3,10),(8,10),(5,10)]
  | 3 => [(3,4),(4,5),(5,7)]
  | 4 => [(3,4),(4,5),(5,7)]
  | 5 => [(6,7),(7,8),(3,7),(7,10)]
  | 6 => [(2,3),(2,5),(0,5)]
  | 7 => [(4,5),(5,6),(1,4),(1,6)]
  | 8 => [(7,8),(8,9),(9,10),(3,9)]
  | 9 => [(0,10),(8,10),(7,8),(4,8)]
  | 10 => [(1,9),(8,9),(3,9),(2,3)]

def doubles : Fin 11 → List (Fin 3 × Fin 3 × Fin 11 × Fin 11)
  | 0 => []
  | 1 => [(0,1,7,10)]
  | 2 => []
  | 3 => [(0,1,5,3)]
  | 4 => [(0,1,4,10)]
  | 5 => []
  | 6 => [(1,2,1,4),(1,2,1,7),(0,2,1,4),(0,2,1,7),(1,2,1,9),(0,2,10,4),(0,2,10,7),(1,2,10,9)]
  | 7 => [(0,1,0,9),(0,1,2,9)]
  | 8 => []
  | 9 => []
  | 10 => [(0,1,2,9)]

def single (s : Fin 11) (i j : Fin 11) : Bool :=
  decide ((i,j) ∈ singles s ∨ (j,i) ∈ singles s)
def double (s : Fin 11) (r t : Fin 3) (p q : Fin 11) : Bool :=
  decide ((r,t,p,q) ∈ doubles s)

def Ready (s : Fin 11) (et : List Color) : Prop :=
  (∃ t : Fin 11, ∃ g : EdgePerm, t.val < s.val ∧ et.map g = List.ofFn (word t)) ∨ Direct et
instance (s et) : Decidable (Ready s et) := by unfold Ready; infer_instance

theorem active_anchors : ∀ s,
    (∀ i, colour s i ≠ 0) ∧ ∀ t, colour s (anchors s t) ≠ c1 := by decide +kernel

def selected (s : Fin 11) (p : Fin 3 → Fin 11) : Bool :=
  (doubles s).any fun (r,t,x,y) => p r == x && p t == y

theorem selected_sound (s p) (h : selected s p = true) : successful (double s) p = true := by
  obtain ⟨⟨r,t,x,y⟩,hm,he⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at he
  simp only [KempeAnchorSelection.successful, decide_eq_true_eq]
  exact ⟨r,t,by simpa only [double, he.1, he.2, decide_eq_true_eq] using hm⟩

/-- Stages whose selection is supplied by the uniform half-block dichotomy. -/
def balancedStage : Fin 7 → Fin 11 := ![0,1,2,3,4,8,9]

/-- Three further stages have a consecutive block one port short of half. -/
def shortStage : Fin 3 → Fin 11 := ![5,7,10]

/-- Only one residual stage replays the joint partner exclusion check. -/
theorem checked : (List.finRange 11).all (fun s =>
    decide (∃ t, balancedStage t = s) ||
    decide (∃ t, shortStage t = s) ||
    (List.finRange 11).all fun p0 =>
      !feasible (colour s) ((anchors s) ∘ ![0]) ![p0] ||
    (List.finRange 11).all fun p1 =>
      !feasible (colour s) ((anchors s) ∘ ![0,1]) ![p0,p1] ||
    (List.finRange 11).all fun p2 =>
      !feasible (colour s) (anchors s) ![p0,p1,p2] || selected s ![p0,p1,p2] ||
        !KempeIntervalMatching.possible (active (colour s))
          (allowed (single s) (anchors s) ![p0,p1,p2]) 0 11) = true := by decide +kernel

/-- Three anchor partners remain jointly constrained by one noncrossing matching. -/
theorem select (s) (residual : ¬ ∃ t, balancedStage t = s)
    (shortResidual : ¬ ∃ t, shortStage t = s) (p : Fin 3 → Fin 11)
    (hf : feasible (colour s) (anchors s) p = true) (h : successful (double s) p = false) :
    KempeIntervalMatching.possible (active (colour s))
      (allowed (single s) (anchors s) p) 0 11 = false := by
  have hp : ![p 0,p 1,p 2] = p := by funext i; fin_cases i <;> rfl
  have hp1 : p ∘ ![(0 : Fin 3)] = ![p 0] := by funext i; fin_cases i; rfl
  have hp2 : p ∘ ![(0 : Fin 3),1] = ![p 0,p 1] := by funext i; fin_cases i <;> rfl
  have hf1 := feasible_reindex (colour s) (anchors s) p ![0] hf
  have hf2 := feasible_reindex (colour s) (anchors s) p ![0,1] hf
  rw [hp1] at hf1
  rw [hp2] at hf2
  have hc := List.all_eq_true.mp checked s (List.mem_finRange s)
  simp only [decide_eq_false residual, decide_eq_false shortResidual, Bool.false_or] at hc
  have hc := List.all_eq_true.mp hc (p 0) (List.mem_finRange (p 0))
  simp only [hf1, Bool.not_true, Bool.false_or] at hc
  have hc := List.all_eq_true.mp hc (p 1) (List.mem_finRange (p 1))
  simp only [hf2, Bool.not_true, Bool.false_or] at hc
  have hc := List.all_eq_true.mp hc (p 2) (List.mem_finRange (p 2))
  rw [hp] at hc
  have hn : selected s p = false := by
    cases hs : selected s p with
    | false => rfl
    | true => have := selected_sound s p hs; simp_all
  simpa [hn, hf] using hc

theorem one_ready : ∀ s i j, single s i j = true →
    Ready s (List.ofFn (switch (colour s) i j)) := by decide +kernel

theorem two_ready : ∀ s r t p q, double s r t p q = true →
    Ready s (List.ofFn (switch (switch (colour s) (anchors s r) p) (anchors s t) q)) := by
  decide +kernel

def half : Fin 7 → ℕ := ![5,4,3,4,4,4,4]

def positions : Fin 7 → List (Fin 11) :=
  ![[4,5,6,7,8,10,0,1,2,3], [4,6,7,8,10,0,1,2],
    [8,10,3,4,5,6], [3,4,5,7,9,0,1,2], [3,4,5,7,9,10,1,2],
    [7,8,9,10,0,3,4,5], [7,8,10,0,1,3,4,6]]

def embed (t : Fin 7) (i : Fin (2 * half t)) : Fin 11 :=
  (positions t)[i.val]?.getD 0

def rank (t : Fin 7) (i : Fin 11) : Fin (2 * half t) :=
  ⟨(positions t).idxOf i % (2 * half t),
    Nat.mod_lt _ (by fin_cases t <;> decide)⟩

instance (t : Fin 7) : NeZero (2 * half t) := ⟨by fin_cases t <;> decide⟩

def moves : (t : Fin 7) → List (Fin (2 * half t))
  | 0 => [6] | 1 => [5,3] | 2 => [4] | 3 => [5,7]
  | 4 => [6,2] | 5 => [5] | 6 => [6]

theorem coordinates : ∀ t,
    (∀ i, rank t (embed t i) = i) ∧
    (∀ i, colour (balancedStage t) i ≠ c1 → embed t (rank t i) = i) ∧
    (∀ i, colour (balancedStage t) (embed t i) ≠ c1) := by decide +kernel

open Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

theorem coordinate_cycles : ∀ t a b c,
    KempeBalancedBlock.cyclic a b c →
      KempeBalancedBlock.cyclic (embed t a) (embed t b) (embed t c) := by decide +kernel

theorem coordinate_order (t a b x y)
    (h : ¬ ChordsCross (embed t a) (embed t x) (embed t b) (embed t y)) :
    ¬ ChordsCross a x b y :=
  KempeBalancedBlock.noncross_of_cyclic (embed t) (coordinate_cycles t) a b x y h

theorem ear_contracts : ∀ t (i j : Fin (2 * half t)),
    i.val < half t → j.val < half t → j.val = i.val + 1 →
      single (balancedStage t) (embed t i) (embed t j) = true := by decide +kernel

/-- The rigid alternative consumes existing component contracts, including
three paired repairs. It does not repeat the source-extension computation. -/
theorem nested_ready : ∀ t, Ready (balancedStage t)
    (List.ofFn (KempeBalancedBlock.batch (embed t) (moves t) (colour (balancedStage t)))) := by
  intro t
  fin_cases t
  · exact one_ready 0 0 7 (by decide)
  · exact two_ready 1 0 1 7 10 (by decide)
  · exact one_ready 2 5 10 (by decide)
  · exact two_ready 3 0 1 5 3 (by decide)
  · exact two_ready 4 0 1 4 10 (by decide)
  · exact one_ready 8 3 9 (by decide)
  · exact one_ready 9 4 8 (by decide)

def shortPositions : Fin 3 → Fin 8 → Fin 11 :=
  ![![6,7,8,9,10,0,3,4], ![4,5,6,9,0,1,2,3], ![8,9,1,2,3,4,5,7]]

def shortRank (u : Fin 3) (i : Fin 11) : Fin 8 :=
  ⟨(List.ofFn (shortPositions u)).idxOf i % 8, Nat.mod_lt _ (by decide)⟩

def shortMoves : Fin 3 → Fin 7 → List (Option (Fin 6))
  | 0, _ => [some 1]
  | 1, 3 => [some 3]
  | 1, 4 => [none, some 2]
  | 1, 5 => [none, some 2]
  | 1, 6 => [some 5]
  | 2, 3 => [none]
  | 2, 4 => [some 2, some 4]
  | 2, 5 => [some 4]
  | 2, 6 => [some 4]
  | _, _ => []

theorem short_coordinates : ∀ u,
    (∀ i, shortRank u (shortPositions u i) = i) ∧
    (∀ i, colour (shortStage u) i ≠ c1 → shortPositions u (shortRank u i) = i) ∧
    (∀ i, colour (shortStage u) (shortPositions u i) ≠ c1) := by decide +kernel

theorem short_cycles : ∀ u a b c,
    KempeBalancedBlock.cyclic a b c →
      KempeBalancedBlock.cyclic (shortPositions u a) (shortPositions u b)
        (shortPositions u c) := by decide +kernel

theorem short_ear_contracts : ∀ u (i j : Fin 8),
    i.val < 3 → j.val < 3 → j.val = i.val + 1 →
      single (shortStage u) (shortPositions u i) (shortPositions u j) = true := by decide +kernel

/-- Each possible outside pair reuses a previously checked source contract. -/
theorem punctured_ready : ∀ u (t : Fin 7), 3 ≤ t.val → Ready (shortStage u)
    (List.ofFn (KempeShortBlock.batch (k := 3) (shortPositions u) t (shortMoves u t)
      (colour (shortStage u)))) := by
  intro u t ht
  fin_cases u <;> fin_cases t <;> norm_num at ht
  · exact one_ready 5 7 3 (by decide)
  · exact one_ready 5 7 3 (by decide)
  · exact one_ready 5 7 10 (by decide)
  · exact one_ready 5 7 10 (by decide)
  · exact one_ready 7 1 6 (by decide)
  · convert two_ready 7 0 1 0 9 (by decide) using 1 <;> decide +kernel
  · exact two_ready 7 0 1 2 9 (by decide)
  · exact one_ready 7 1 4 (by decide)
  · exact one_ready 10 2 3 (by decide)
  · exact two_ready 10 0 1 2 9 (by decide)
  · exact one_ready 10 3 9 (by decide)
  · exact one_ready 10 3 9 (by decide)

/-- The stage index orders the eleven local laws; it does not store a rank
for every possible boundary trace. -/
theorem stages (n : ℕ) : ∀ s : Fin 11, s.val < n →
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
        (coordinates t).1 (coordinates t).2.1 (coordinates t).2.2 (coordinate_order t)
      · intro i j hi hj hij
        exact finish (one_ready _ _ _ (ear_contracts t i j hi hj hij))
      · exact finish (nested_ready t)
    · by_cases hs : ∃ u, shortStage u = s
      · obtain ⟨u,rfl⟩ := hs
        apply kempeCoclosure_of_map (palette (shortStage u))
        change KempeCoclosure Terminal (List.ofFn (colour (shortStage u)))
        apply KempeShortBlock.coclosure (k := 3) (moves := shortMoves u)
          _ (shortPositions u) (shortRank u)
          (short_coordinates u).1 (short_coordinates u).2.1 (short_coordinates u).2.2
          (fun a b x y => KempeBalancedBlock.noncross_of_cyclic _ (short_cycles u) a b x y)
        · intro i j hi hj hij
          exact finish (one_ready _ _ _ (short_ear_contracts u i j hi hj hij))
        · exact fun t ht => finish (punctured_ready u t ht)
      · apply kempeCoclosure_of_map (palette s)
        change KempeCoclosure Terminal (List.ofFn (colour s))
        apply KempeAnchorSelection.coclosure _ (active_anchors s).1 (anchors s)
          (active_anchors s).2 (single s) (double s)
        · exact fun i j h => finish (one_ready s i j h)
        · exact fun r t p q h => finish (two_ready s r t p q h)
        · exact select s hb hs

def input : Bool → Fin 11 := fun s => if s then 10 else 8

theorem source_trace : ∀ s, trace (List.ofFn (StripCriticalChain.boundary s)) =
    List.ofFn (word (input s)) := by decide +kernel

theorem repair (s : Bool) :
    KempeCoclosure Terminal (trace (List.ofFn (StripCriticalChain.boundary s))) := by
  rw [source_trace]
  exact stages 11 (input s) (input s).isLt

theorem nonextension (s : Bool) :
    ¬ Terminal (trace (List.ofFn (StripCriticalChain.boundary s))) :=
  StripResponseSummary.no_trace _ (fun h =>
    StripCriticalChain.no_core s ((StripResponseSummary.terminal_iff _).mp h))

/-- Complete witnesses agree at all eleven ordered ports in the same exterior.
Their trace necessarily changes: the original boundary has no full extension. -/
theorem compatible_changed {V : Type*} (s : Bool) (H : SimpleGraph V) (ports : Fin 11 → V)
    (closed : KempeClosed (KempeBoundarySplit.GraphTrace H (List.ofFn ports)))
    (initial : KempeBoundarySplit.GraphTrace H (List.ofFn ports)
      (trace (List.ofFn (StripCriticalChain.boundary s)))) :
    ∃ D : H.Coloring Color, ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      (∀ i, k (StripResponseSummary.port i) = D (ports i)) ∧
      trace ((List.ofFn ports).map D) ≠ trace (List.ofFn (StripCriticalChain.boundary s)) := by
  obtain ⟨et,⟨k,hk⟩,⟨D,hD⟩⟩ := repair s _ closed initial
  have boundary_eq : TriangleStripAnchors.input0099.boundary =
      List.ofFn StripResponseSummary.port := by decide +kernel
  obtain ⟨aligned,ha⟩ := GraphTraceAlignment.align
    TriangleStripAnchors.input0099.boundary k ((List.ofFn ports).map D)
    (by rw [boundary_eq]; simp) (hk.symm.trans hD)
  have eq : (fun i => aligned (StripResponseSummary.port i)) = (fun i => D (ports i)) :=
    List.ofFn_injective (by simpa only [boundary_eq, List.map_ofFn, Function.comp_def] using ha)
  refine ⟨D,aligned,(fun i => congrFun eq i),?_⟩
  intro h
  exact nonextension s ⟨k, (hD.trans h).symm.trans hk⟩

end FourColor.StripChainRepair
