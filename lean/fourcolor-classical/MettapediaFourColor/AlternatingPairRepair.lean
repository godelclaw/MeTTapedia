import MettapediaFourColor.KempeChromogramMatching
import MettapediaFourColor.KempeBalancedBlock
import MettapediaFourColor.GraphTraceAlignment

/-!
# Closing two adjacent vertices through a majority block

On the eight-port alternating pattern, five consecutive active ports form
a majority. One adjacent matched pair in that block frees compatible
colours for both inserted vertices. The arbitrary exterior is retained.
The analogous one-component rule fails for an explicit ten-port matching.
-/

namespace FourColor.AlternatingPairRepair

open Color KempeBoundarySplit KempeIntervalRepair

def Fits {n : ℕ} (b : Fin (n+4) → Color) (x y : Color) : Prop :=
  x ≠ b ⟨n+2, by omega⟩ ∧ x ≠ b ⟨n+3, by omega⟩ ∧
  x ≠ b 0 ∧ x ≠ b 1 ∧ y ≠ x ∧
  ∀ i : Fin (n+2), y ≠ b ⟨i.val+1, by omega⟩

instance {n : ℕ} (b : Fin (n+4) → Color) (x y : Color) : Decidable (Fits b x y) := by
  unfold Fits
  infer_instance

def readBoundary (n : ℕ) (et : List Color) (i : Fin (n+4)) : Color :=
  (untrace 0 et)[i.val]?.getD 0

def Direct (n : ℕ) (et : List Color) : Prop :=
  trace (List.ofFn (readBoundary n et)) = et ∧
    ∃ x y, Fits (readBoundary n et) x y

instance (n : ℕ) (et : List Color) : Decidable (Direct n et) := by
  unfold Direct
  infer_instance

def Terminal (n : ℕ) (et : List Color) : Prop :=
  ∃ b : Fin (n+4) → Color, et = trace (List.ofFn b) ∧ ∃ x y, Fits b x y

theorem direct_coclosure {n : ℕ} {et : List Color} (h : Direct n et) :
    KempeCoclosure (Terminal n) et := by
  intro outside _ ho
  exact ⟨et, ⟨readBoundary n et, h.1.symm, h.2⟩, ho⟩

/-- Palette-normalized trace of the alternating eight-port pattern. -/
def word : Fin 8 → Color := ![c3,c2,c2,c2,c2,c2,c3,c2]
def embed : Fin 8 → Fin 8 := ![5,6,7,0,1,2,3,4]
def rank : Fin 8 → Fin 8 := ![3,4,5,6,7,0,1,2]
def block : Finset (Fin 8) := {0,1,2,3,4}

/-- The starting boundary is a genuine joint-colour obstruction. -/
theorem initially_blocked : ∀ x y,
    ¬ Fits (readBoundary 4 (List.ofFn word)) x y := by decide +kernel

theorem initial_trace : trace (List.ofFn (readBoundary 4 (List.ofFn word))) =
    List.ofFn word := by decide +kernel

theorem coordinates : (∀ i, rank (embed i) = i) ∧
    (∀ i, embed (rank i) = i) ∧ (∀ i, word (embed i) ≠ c1) := by decide +kernel

theorem coordinate_cycles : ∀ a b c,
    KempeBalancedBlock.cyclic a b c →
      KempeBalancedBlock.cyclic (embed a) (embed b) (embed c) := by decide +kernel

/-- Four small colour calculations, with no table of component matchings. -/
theorem release : ∀ a ∈ block, ∀ b ∈ block, b.val = a.val+1 →
    Direct 4 (List.ofFn (switch word (embed a) (embed b))) := by decide +kernel

theorem repair : KempeCoclosure (Terminal 4) (List.ofFn word) := by
  apply KempeChromogramMatching.majority_coclosure word embed rank
    coordinates.1 (fun i _ => coordinates.2.1 i) coordinates.2.2
    (fun a b x y => KempeBalancedBlock.noncross_of_cyclic embed coordinate_cycles a b x y)
    block (by decide +kernel) (by decide +kernel)
  exact fun a ha b hb h => direct_coclosure (release a ha b hb h)

/-- Actual graph colourings are aligned on all ports simultaneously. -/
theorem compatible {V : Type*} (G : SimpleGraph V) (ports : Fin 8 → V)
    (closed : KempeClosed (GraphTrace G (List.ofFn ports)))
    (initial : GraphTrace G (List.ofFn ports) (List.ofFn word)) :
    ∃ D : G.Coloring Color, ∃ x y, Fits (fun i => D (ports i)) x y := by
  obtain ⟨et,⟨b,rfl,x,y,fit⟩,⟨D,hD⟩⟩ := repair _ closed initial
  obtain ⟨aligned,ha⟩ := GraphTraceAlignment.align (List.ofFn ports) D (List.ofFn b)
    (by simp) hD.symm
  have eq : (fun i => aligned (ports i)) = b :=
    List.ofFn_injective (by simpa only [List.map_ofFn,Function.comp_def] using ha)
  exact ⟨aligned,x,y,eq.symm ▸ fit⟩

/-- The same repair handles every palette relabelling of the pattern. -/
theorem compatible_mapped {V : Type*} (G : SimpleGraph V) (ports : Fin 8 → V)
    (closed : KempeClosed (GraphTrace G (List.ofFn ports))) (g : EdgePerm)
    (initial : GraphTrace G (List.ofFn ports) ((List.ofFn word).map g)) :
    ∃ D : G.Coloring Color, ∃ x y, Fits (fun i => D (ports i)) x y := by
  apply compatible G ports closed
  simpa [List.map_map,Function.comp_def] using (closed _ initial).1 g⁻¹

def longWord : Fin 10 → Color := ![c3,c2,c2,c2,c2,c2,c2,c2,c3,c2]
def longMate : Fin 10 → Fin 10 := ![3,2,1,0,9,8,7,6,5,4]

/-- At ten ports the same palette has a legitimate noncrossing matching
whose individual component exchanges all fail. No multi-step or physical
impossibility is asserted. -/
theorem long_matching : Function.Involutive longMate ∧
    KempeMatchingChromogram.Noncrossing longMate ∧
    (∀ i, longWord i ≠ 0) ∧ (∀ i, longMate i = i ↔ longWord i = c1) := by
  unfold Function.Involutive
  decide +kernel

theorem long_single_component_fails : ∀ i,
    ¬ Direct 6 (List.ofFn (switch longWord i (longMate i))) := by decide +kernel

theorem long_switch_traces : ∀ i,
    trace (List.ofFn (readBoundary 6 (List.ofFn (switch longWord i (longMate i))))) =
      List.ofFn (switch longWord i (longMate i)) := by decide +kernel

/-- Failure comes from incompatible colours, not a failed trace decoder. -/
theorem long_colours_fail : ∀ i x y,
    ¬ Fits (readBoundary 6 (List.ofFn (switch longWord i (longMate i)))) x y :=
  by decide +kernel

end FourColor.AlternatingPairRepair
