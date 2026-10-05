import MettapediaFourColor.KempeRetainedMatching
import MettapediaFourColor.StripSixConnection
import MettapediaFourColor.StripSymbolicRepair
import MettapediaFourColor.GraphTraceAlignment

/-!
# Joint matching repair of the two port-six boundary forms

Sixteen local stages retain one exterior matching through each paired choice.
Every selected continuation either reconstructs the eight-vertex core through
its symbolic ear relations or reaches an earlier stage. This gives compatible
colourings of the complete source and the same Kempe-closed exterior for both
boundary forms, without any extra component-separation guard.

The exterior closure is an explicit hypothesis. These local stage laws do not
establish occurrence supply, strict graph reduction or a bound on the number
of physical component switches. No full-colouring table is used.
-/

namespace FourColor.StripSixJointRepair

open Color StripSymbolicRepair KempeIntervalRepair

def word : Fin 16 → Fin 11 → Color
  | 0 => ![c1,c1,c1,c2,c3,c2,c3,c3,c1,c1,c2]
  | 1 => ![c1,c1,c1,c2,c2,c2,c2,c3,c1,c1,c2]
  | 2 => ![c1,c1,c1,c2,c2,c3,c3,c3,c1,c1,c2]
  | 3 => ![c1,c1,c2,c1,c1,c3,c3,c3,c2,c2,c1]
  | 4 => ![c1,c2,c2,c1,c3,c1,c2,c1,c3,c3,c1]
  | 5 => ![c1,c2,c2,c3,c3,c3,c2,c1,c3,c3,c1]
  | 6 => ![c1,c2,c2,c1,c1,c3,c2,c1,c3,c3,c1]
  | 7 => ![c1,c2,c1,c3,c1,c1,c3,c3,c2,c2,c1]
  | 8 => ![c1,c1,c1,c2,c3,c1,c2,c1,c1,c1,c2]
  | 9 => ![c1,c2,c2,c2,c3,c2,c1,c1,c2,c2,c2]
  | 10 => ![c1,c1,c1,c2,c3,c1,c2,c2,c1,c1,c1]
  | 11 => ![c1,c2,c2,c3,c1,c2,c3,c3,c3,c3,c1]
  | 12 => ![c1,c2,c2,c3,c1,c2,c3,c1,c3,c1,c1]
  | 13 => ![c1,c2,c2,c3,c1,c2,c3,c3,c1,c1,c1]
  | 14 => ![c1,c1,c1,c2,c1,c3,c2,c2,c3,c3,c1]
  | _ => ![c1,c1,c2,c1,c1,c3,c2,c2,c3,c3,c1]

def anchors : Fin 16 → Fin 2 → Fin 11
  | 0 => ![0,1]
  | 1 => ![4,5]
  | 2 => ![3,4]
  | 3 => ![0,9]
  | 4 => ![1,2]
  | 5 => ![1,3]
  | 6 => ![0,8]
  | 7 => ![0,3]
  | 8 => ![5,6]
  | 9 => ![0,1]
  | 10 => ![0,10]
  | 11 => ![1,3]
  | 12 => ![1,2]
  | 13 => ![0,3]
  | 14 => ![1,2]
  | _ => ![0,10]

def palette : Fin 16 → EdgePerm :=
  ![.e321,.e321,.e123,.e321,.e123,.e123,.e213,.e213,.e321,.e321,.e321,.e123,.e321,.e213,.e213,.e321]
def colour (s : Fin 16) (i : Fin 11) : Color := palette s (word s i)

def singles : Fin 16 → List (Fin 11 × Fin 11)
  | 0 => [(0,1),(0,10),(1,2),(0,8)]
  | 1 => [(3,4),(6,8),(8,9),(0,8),(3,6)]
  | 2 => [(3,4),(4,5)]
  | 3 => [(0,10),(1,2),(0,1)]
  | 4 => [(1,2),(1,9)]
  | 5 => [(1,9),(8,9),(6,8)]
  | 6 => [(7,8),(4,8),(0,5),(4,10),(4,5),(3,4)]
  | 7 => [(2,3),(3,4),(4,5)]
  | 8 => [(3,5),(7,8),(8,9),(0,8),(3,7)]
  | 9 => [(0,1),(0,10),(9,10),(8,9),(7,8)]
  | 10 => [(0,10),(9,10),(1,5),(7,10),(0,3)]
  | 11 => [(1,9),(8,9),(7,8)]
  | 12 => [(5,7),(7,9),(0,7)]
  | 13 => [(0,6),(0,8),(4,10),(4,8),(8,9),(7,8)]
  | 14 => [(1,2),(5,8),(9,10),(1,5)]
  | _ => [(1,2),(3,4),(6,7),(1,7),(2,3)]

def doubles : Fin 16 → List (Fin 11 × Fin 11)
  | 0 => []
  | 1 => [(8,6)]
  | 2 => [(10,7)]
  | 3 => [(8,10)]
  | 4 => [(6,4)]
  | 5 => [(2,9)]
  | 6 => []
  | 7 => [(2,10)]
  | 8 => [(8,7)]
  | 9 => []
  | 10 => [(1,2),(1,5)]
  | 11 => [(2,9)]
  | 12 => [(0,7),(9,7)]
  | 13 => [(10,9)]
  | 14 => [(0,4),(0,10),(9,8)]
  | _ => [(1,2),(6,7)]

def single (s : Fin 16) (i j : Fin 11) : Bool :=
  decide ((i,j) ∈ singles s ∨ (j,i) ∈ singles s)
def double (s : Fin 16) (p q : Fin 11) : Bool := decide ((p,q) ∈ doubles s)

def Ready (s : Fin 16) (et : List Color) : Prop :=
  (∃ t : Fin 16, ∃ g : EdgePerm, t.val < s.val ∧ et.map g = List.ofFn (word t)) ∨ Direct et
instance (s et) : Decidable (Ready s et) := by unfold Ready; infer_instance

theorem active_anchors : ∀ s,
    (∀ i, colour s i ≠ 0) ∧ ∀ t, colour s (anchors s t) ≠ c1 := by decide +kernel

/-- The interval criterion excludes every matching with no selected continuation. -/
theorem select : ∀ s p q, double s p q = false →
    KempeIntervalMatching.possible (active (colour s))
      (KempeRetainedMatching.allowed (single s) (anchors s 0) p (anchors s 1) q) 0 11 = false := by
  decide +kernel

/-- Each successful single component feeds a symbolic join or an earlier stage. -/
theorem one_ready : ∀ s i j, single s i j = true →
    Ready s (List.ofFn (switch (colour s) i j)) := by decide +kernel

/-- Both anchor components come from the same retained exterior matching. -/
theorem two_ready : ∀ s p q, double s p q = true →
    Ready s (List.ofFn (switch (switch (colour s) (anchors s 0) p) (anchors s 1) q)) := by
  decide +kernel

/-- The stage index decreases at every nonterminal continuation. -/
theorem stages (n : ℕ) : ∀ s : Fin 16, s.val < n →
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
    apply KempeRetainedMatching.two_anchor_coclosure _ (active_anchors s).1
      (anchors s 0) (anchors s 1) ((active_anchors s).2 0) ((active_anchors s).2 1)
      (single s) (double s)
    · exact fun i j h => finish (one_ready s i j h)
    · exact fun p q h => finish (two_ready s p q h)
    · exact select s

def input : Bool → Fin 16 := fun s => if s then 15 else 3
def inputPalette : Bool → EdgePerm := fun s => if s then .e132 else .e123

theorem source_trace : ∀ s,
    (trace (List.ofFn (StripSixConnection.input s))).map (inputPalette s) =
      List.ofFn (word (input s)) := by decide +kernel

theorem repair (s : Bool) :
    KempeCoclosure Terminal (trace (List.ofFn (StripSixConnection.input s))) := by
  apply kempeCoclosure_of_map (inputPalette s)
  rw [source_trace]
  exact stages 16 (input s) (input s).isLt

/-- Both initial boundary forms require recolouring: neither extends directly. -/
theorem no_direct : ∀ s, ¬ ∃ a c, StripResponseSummary.r5 (StripSixConnection.input s) a c := by
  decide +kernel

theorem nonextension (s : Bool) :
    ¬ Terminal (trace (List.ofFn (StripSixConnection.input s))) :=
  StripResponseSummary.no_trace _ (no_direct s)

/-- The reconstructed complete source and the same exterior agree at all eleven
ordered ports. The boundary trace necessarily changes. -/
theorem compatible_changed {V : Type*} (s : Bool) (H : SimpleGraph V) (ports : Fin 11 → V)
    (closed : KempeClosed (KempeBoundarySplit.GraphTrace H (List.ofFn ports)))
    (initial : KempeBoundarySplit.GraphTrace H (List.ofFn ports)
      (trace (List.ofFn (StripSixConnection.input s)))) :
    ∃ D : H.Coloring Color, ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      (∀ i, k (StripResponseSummary.port i) = D (ports i)) ∧
      trace ((List.ofFn ports).map D) ≠ trace (List.ofFn (StripSixConnection.input s)) := by
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

end FourColor.StripSixJointRepair
