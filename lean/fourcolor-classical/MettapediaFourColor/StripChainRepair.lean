import MettapediaFourColor.KempeAnchorSelection
import MettapediaFourColor.StripCriticalChain
import MettapediaFourColor.GraphTraceAlignment

/-!
# Repairing the two critical-chain boundaries

Eleven local stages use one retained-matching selection theorem and exact
symbolic source reconstruction. A stage either extends directly or enters
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

def palette : Fin 11 → EdgePerm := ![.e321,.e213,.e123,.e321,.e123,.e213,.e321,.e321,.e213,.e321,.e123]
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

/-- Compact Boolean replay checks partners jointly, without enumerating functions. -/
theorem checked : (List.finRange 11).all (fun s =>
    (List.finRange 11).all fun p0 =>
      !feasible (colour s) ((anchors s) ∘ ![0]) ![p0] ||
    (List.finRange 11).all fun p1 =>
      !feasible (colour s) ((anchors s) ∘ ![0,1]) ![p0,p1] ||
    (List.finRange 11).all fun p2 =>
      !feasible (colour s) (anchors s) ![p0,p1,p2] || selected s ![p0,p1,p2] ||
        !KempeIntervalMatching.possible (active (colour s))
          (allowed (single s) (anchors s) ![p0,p1,p2]) 0 11) = true := by decide +kernel

/-- Three anchor partners remain jointly constrained by one noncrossing matching. -/
theorem select (s) (p : Fin 3 → Fin 11)
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
    apply kempeCoclosure_of_map (palette s)
    change KempeCoclosure Terminal (List.ofFn (colour s))
    apply KempeAnchorSelection.coclosure _ (active_anchors s).1 (anchors s)
      (active_anchors s).2 (single s) (double s)
    · exact fun i j h => finish (one_ready s i j h)
    · exact fun r t p q h => finish (two_ready s r t p q h)
    · exact select s

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
