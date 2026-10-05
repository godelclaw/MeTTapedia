import MettapediaFourColor.StripTriangleConsistency
import MettapediaFourColor.StripSymbolicRepair
import MettapediaFourColor.KempeBalancedBlock
import MettapediaFourColor.GraphTraceAlignment

/-!
# A compatible repair of the triangle-support counterexample

The last four active ports form half of a noncrossing matching. An ear in
that block permits direct extension. With no ear the matching is forced,
and its component from port 7 to port 4 permits direct extension instead.
Thus the fixed-boundary obstruction has a repair in the same Kempe-closed
exterior. This is one input, not a universal D0099 repair or occurrence law.
-/

namespace FourColor.StripTriangleConsistencyRepair

open Color StripTriangleConsistency StripSymbolicRepair KempeIntervalRepair

def word : Fin 11 → Color := ![c1,c2,c2,c1,c2,c2,c3,c3,c3,c1,c2]
def embed : Fin 8 → Fin 11 := ![6,7,8,10,1,2,4,5]
def rank : Fin 11 → Fin 8 := ![0,4,5,0,6,7,0,1,2,0,3]
def exchanges : Fin 4 → Fin 11 × Fin 11 := ![(6,7),(7,8),(8,10),(7,4)]

theorem source_trace : trace (List.ofFn boundary) = List.ofFn word := by decide +kernel

theorem coordinates : (∀ i, rank (embed i) = i) ∧
    (∀ i, word i ≠ c1 → embed (rank i) = i) ∧
    (∀ i, word (embed i) ≠ c1) := by decide +kernel

theorem coordinate_cycles : ∀ a b c,
    KempeBalancedBlock.cyclic a b c →
      KempeBalancedBlock.cyclic (embed a) (embed b) (embed c) := by decide +kernel

/-- Four symbolic extension checks; no interior colouring table is stored. -/
theorem release : ∀ s, Direct
    (List.ofFn (switch word (exchanges s).1 (exchanges s).2)) := by decide +kernel

theorem ear_ready (i j : Fin 8) (hi : i.val < 4) (hj : j.val < 4)
    (hij : j.val = i.val + 1) : Direct
      (List.ofFn (switch word (embed i) (embed j))) := by
  have cases : (i.val = 0 ∧ j.val = 1) ∨ (i.val = 1 ∧ j.val = 2) ∨
      (i.val = 2 ∧ j.val = 3) := by omega
  rcases cases with ⟨hi,hj⟩ | ⟨hi,hj⟩ | ⟨hi,hj⟩
  · have hi : i = 0 := Fin.ext hi
    have hj : j = 1 := Fin.ext hj
    subst i; subst j
    exact release 0
  · have hi : i = 1 := Fin.ext hi
    have hj : j = 2 := Fin.ext hj
    subst i; subst j
    exact release 1
  · have hi : i = 2 := Fin.ext hi
    have hj : j = 3 := Fin.ext hj
    subst i; subst j
    exact release 2

/-- The arbitrary-width half-block law chooses a successful component
of the actual retained exterior matching. -/
theorem repair : KempeCoclosure Terminal (trace (List.ofFn boundary)) := by
  rw [source_trace]
  apply KempeBalancedBlock.coclosure (k := 4) word embed rank
    coordinates.1 coordinates.2.1 coordinates.2.2
    (fun a b x y => KempeBalancedBlock.noncross_of_cyclic embed coordinate_cycles a b x y)
    (fun i j hi hj hij => direct_coclosure (ear_ready i j hi hj hij)) [1]
  exact direct_coclosure (release 3)

theorem nonextension : ¬ Terminal (trace (List.ofFn boundary)) :=
  StripResponseSummary.no_trace _ (fun h =>
    no_core ((StripResponseSummary.terminal_iff _).mp h))

/-- Reconstructed colourings agree on every ordered exterior port. -/
theorem compatible_changed {V : Type*} (H : SimpleGraph V) (ports : Fin 11 → V)
    (closed : KempeClosed (KempeBoundarySplit.GraphTrace H (List.ofFn ports)))
    (initial : KempeBoundarySplit.GraphTrace H (List.ofFn ports)
      (trace (List.ofFn boundary))) :
    ∃ D : H.Coloring Color,
    ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      (∀ i, k (StripResponseSummary.port i) = D (ports i)) ∧
      trace ((List.ofFn ports).map D) ≠ trace (List.ofFn boundary) := by
  obtain ⟨et,⟨k,hk⟩,⟨D,hD⟩⟩ := repair _ closed initial
  have boundary_eq : TriangleStripAnchors.input0099.boundary =
      List.ofFn StripResponseSummary.port := by decide +kernel
  obtain ⟨aligned,ha⟩ := GraphTraceAlignment.align
    TriangleStripAnchors.input0099.boundary k ((List.ofFn ports).map D)
    (by rw [boundary_eq]; simp) (hk.symm.trans hD)
  have eq : (fun i => aligned (StripResponseSummary.port i)) = (fun i => D (ports i)) :=
    List.ofFn_injective (by simpa only [boundary_eq, List.map_ofFn, Function.comp_def] using ha)
  refine ⟨D,aligned,(fun i => congrFun eq i),?_⟩
  intro h
  exact nonextension (h ▸ hD ▸ ⟨k,hk⟩)

end FourColor.StripTriangleConsistencyRepair
