import MettapediaFourColor.KempeAnchorSelection
import MettapediaFourColor.StripChoiceBarrier
import MettapediaFourColor.GraphTraceAlignment

/-!
# Completing the choice-barrier input by coordinated repairs

Four local stages reuse the same anchor-selection theorem and symbolic
source reconstruction. The initial stage has one possible intermediate;
that intermediate composes with either of two terminal repair stages.
All choices retain the same exterior. Neither the number of available
hole positions nor the number of partial colourings is assumed to grow.
The finite chord contracts remain explicit proof obligations.
-/

namespace FourColor.StripChoiceEscape

open Color StripSymbolicRepair KempeIntervalRepair KempeAnchorSelection

def word : Fin 4 → Fin 11 → Color
  | 0 => ![c1,c1,c2,c1,c2,c1,c1,c3,c1,c2,c1]
  | 1 => ![c1,c2,c3,c2,c3,c1,c1,c1,c2,c3,c1]
  | 2 => ![c1,c1,c2,c1,c2,c3,c3,c1,c3,c2,c1]
  | 3 => ![c1,c1,c2,c1,c2,c3,c2,c1,c2,c2,c1]

def anchors : Fin 4 → Fin 4 → Fin 11
  | 0 => ![0,2,6,9]
  | 1 => ![0,2,4,6]
  | 2 => ![0,1,6,7]
  | 3 => ![2,4,5,6]

def palette : Fin 4 → EdgePerm := ![.e321,.e213,.e213,.e123]
def colour (s : Fin 4) (i : Fin 11) : Color := palette s (word s i)

def singles : Fin 4 → List (Fin 11 × Fin 11)
  | 0 => [(6,8),(0,8)]
  | 1 => [(6,7),(5,6),(4,5)]
  | 2 => [(8,10),(6,7)]
  | 3 => [(8,9),(6,8),(5,6)]

def doubles : Fin 4 → List (Fin 4 × Fin 4 × Fin 11 × Fin 11)
  | 0 => [(1,3,1,8),(0,3,1,8),(0,2,10,5),(0,2,1,5),(2,3,1,8),
          (1,3,8,1),(0,2,5,10),(1,3,8,10),(1,2,1,5)]
  | 1 => [(0,3,5,10)]
  | 2 => [(2,3,10,8),(2,3,5,8),(1,2,8,5),(0,3,10,8)]
  | 3 => []

def single (s : Fin 4) (i j : Fin 11) : Bool :=
  decide ((i,j) ∈ singles s ∨ (j,i) ∈ singles s)
def double (s : Fin 4) (r t : Fin 4) (p q : Fin 11) : Bool :=
  decide ((r,t,p,q) ∈ doubles s)

def Ready (s : Fin 4) (et : List Color) : Prop :=
  (∃ t : Fin 4, ∃ g : EdgePerm, t.val < s.val ∧ et.map g = List.ofFn (word t)) ∨ Direct et
instance (s et) : Decidable (Ready s et) := by unfold Ready; infer_instance

theorem active_anchors : ∀ s,
    (∀ i, colour s i ≠ 0) ∧ ∀ t, colour s (anchors s t) ≠ c1 := by decide +kernel

def selected (s : Fin 4) (p : Fin 4 → Fin 11) : Bool :=
  (doubles s).any fun (r,t,x,y) => p r == x && p t == y

theorem selected_sound (s p) (h : selected s p = true) : successful (double s) p = true := by
  obtain ⟨⟨r,t,x,y⟩,hm,he⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true, beq_iff_eq] at he
  simp only [KempeAnchorSelection.successful, decide_eq_true_eq]
  exact ⟨r,t,by simpa only [double, he.1, he.2, decide_eq_true_eq] using hm⟩

/-- Compact Boolean replay checks partners jointly, without enumerating functions. -/
theorem checked : (List.finRange 4).all (fun s =>
    (List.finRange 11).all fun p0 =>
      !feasible (colour s) ((anchors s) ∘ ![0]) ![p0] ||
    (List.finRange 11).all fun p1 =>
      !feasible (colour s) ((anchors s) ∘ ![0,1]) ![p0,p1] ||
    (List.finRange 11).all fun p2 =>
      !feasible (colour s) ((anchors s) ∘ ![0,1,2]) ![p0,p1,p2] ||
    (List.finRange 11).all fun p3 =>
      !feasible (colour s) (anchors s) ![p0,p1,p2,p3] || selected s ![p0,p1,p2,p3] ||
        !KempeIntervalMatching.possible (active (colour s))
          (allowed (single s) (anchors s) ![p0,p1,p2,p3]) 0 11) = true := by decide +kernel

/-- Four anchor partners remain jointly constrained by one noncrossing matching. -/
theorem select (s) (p : Fin 4 → Fin 11)
    (hf : feasible (colour s) (anchors s) p = true) (h : successful (double s) p = false) :
    KempeIntervalMatching.possible (active (colour s))
      (allowed (single s) (anchors s) p) 0 11 = false := by
  have hp : ![p 0,p 1,p 2,p 3] = p := by funext i; fin_cases i <;> rfl
  have hp1 : p ∘ ![(0 : Fin 4)] = ![p 0] := by funext i; fin_cases i; rfl
  have hp2 : p ∘ ![(0 : Fin 4),1] = ![p 0,p 1] := by funext i; fin_cases i <;> rfl
  have hp3 : p ∘ ![(0 : Fin 4),1,2] = ![p 0,p 1,p 2] := by funext i; fin_cases i <;> rfl
  have hf1 := feasible_reindex (colour s) (anchors s) p ![0] hf
  have hf2 := feasible_reindex (colour s) (anchors s) p ![0,1] hf
  have hf3 := feasible_reindex (colour s) (anchors s) p ![0,1,2] hf
  rw [hp1] at hf1
  rw [hp2] at hf2
  rw [hp3] at hf3
  have hc := List.all_eq_true.mp checked s (List.mem_finRange s)
  have hc := List.all_eq_true.mp hc (p 0) (List.mem_finRange (p 0))
  simp only [hf1, Bool.not_true, Bool.false_or] at hc
  have hc := List.all_eq_true.mp hc (p 1) (List.mem_finRange (p 1))
  simp only [hf2, Bool.not_true, Bool.false_or] at hc
  have hc := List.all_eq_true.mp hc (p 2) (List.mem_finRange (p 2))
  simp only [hf3, Bool.not_true, Bool.false_or] at hc
  have hc := List.all_eq_true.mp hc (p 3) (List.mem_finRange (p 3))
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

/-- The stage index orders the four local laws; it does not store a rank
for every possible boundary trace. -/
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
    apply kempeCoclosure_of_map (palette s)
    change KempeCoclosure Terminal (List.ofFn (colour s))
    apply KempeAnchorSelection.coclosure _ (active_anchors s).1 (anchors s)
      (active_anchors s).2 (single s) (double s)
    · exact fun i j h => finish (one_ready s i j h)
    · exact fun r t p q h => finish (two_ready s r t p q h)
    · exact select s

theorem repair : KempeCoclosure Terminal (List.ofFn StripChoiceBarrier.word) :=
  stages 4 3 (by decide)

/-- The result reconstructs all eight core vertices, with one compatible
colouring of the same exterior at all eleven ordered ports. -/
theorem compatible {V : Type*} (H : SimpleGraph V) (ports : Fin 11 → V)
    (closed : KempeClosed (KempeBoundarySplit.GraphTrace H (List.ofFn ports)))
    (initial : KempeBoundarySplit.GraphTrace H (List.ofFn ports)
      (List.ofFn StripChoiceBarrier.word)) :
    ∃ D : H.Coloring Color, ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      ∀ i, k (StripResponseSummary.port i) = D (ports i) := by
  obtain ⟨et,⟨k,hk⟩,⟨D,hD⟩⟩ := repair _ closed initial
  have boundary_eq : TriangleStripAnchors.input0099.boundary =
      List.ofFn StripResponseSummary.port := by decide +kernel
  obtain ⟨aligned,ha⟩ := GraphTraceAlignment.align
    TriangleStripAnchors.input0099.boundary k ((List.ofFn ports).map D)
    (by rw [boundary_eq]; simp) (hk.symm.trans hD)
  have eq : (fun i => aligned (StripResponseSummary.port i)) = (fun i => D (ports i)) :=
    List.ofFn_injective (by simpa only [boundary_eq, List.map_ofFn, Function.comp_def] using ha)
  exact ⟨D,aligned,fun i => congrFun eq i⟩

end FourColor.StripChoiceEscape
