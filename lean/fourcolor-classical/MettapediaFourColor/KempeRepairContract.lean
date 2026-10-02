import MettapediaFourColor.KempeBoundarySplit
import FourColor.CfColor

/-!
# From all-proper-trace repair to a valid contraction

A contract whose edge closure avoids the perimeter leaves every boundary
edge properly coloured. Consequently a repair law for all proper traces
supplies the coclosure field of every valid contract on that perimeter.
Geometry and validity of the contraction remain explicit inputs.
-/

namespace FourColor.KempeRepairContract

open Color KempeBoundarySplit

variable {D : Type*} {G : Hypermap D} {k : D → Color}

/-- One interior edge is a valid contract when its two darts lie on distinct
nodes. No colouring assumption is needed for this geometric fact. -/
theorem valid_singleton {r : List D} {d : D}
    (off : d ∉ r) (offEdge : G.edge d ∉ r)
    (separate : ¬ G.CNode d (G.edge d)) : G.ValidContract r [d] := by
  refine ⟨?_, ?_, by simp, by simp, by simp⟩
  · simpa using And.intro off offEdge
  · simpa [Hypermap.Sparse] using separate

private theorem pairmap_nonzero (allowed : List D)
    (proper : ∀ x ∈ allowed, k x ≠ k (G.node x)) :
    ∀ (x : D) (p : List D), (∀ z ∈ x :: p, z ∈ allowed) →
      List.IsChain (fun u v => u = G.node v) (x :: p) →
      (0 : Color) ∉ pairmap (· + ·) (k x) (p.map k) := by
  intro x p
  induction p generalizing x with
  | nil => intro _ _; simp
  | cons y p ih =>
    intro included chain mem
    obtain ⟨xy, rest⟩ := List.isChain_cons_cons.mp chain
    rw [List.map_cons, pairmap_cons] at mem
    rcases List.mem_cons.mp mem with h | h
    · apply proper y (included y (by simp))
      rw [← xy]
      exact (add_eq_zero_iff.mp h.symm).symm
    · exact ih y (fun z hz => included z (List.mem_cons_of_mem x hz)) rest h

private theorem trace_nonzero (r : List D)
    (proper : ∀ x ∈ r, k x ≠ k (G.node x))
    (cycle : IsCyclicChain (fun u v => u = G.node v) r) :
    (0 : Color) ∉ trace (r.map k) := by
  cases r with
  | nil => simp [trace]
  | cons x p =>
    obtain ⟨chain, last⟩ := cycle
    have hl : p.getLastD x = G.node x := last _ (getLast?_cons_eq_some x p) x rfl
    have extended : List.IsChain (fun u v => u = G.node v) ((x :: p) ++ [x]) :=
      isChain_append_cons chain hl (List.IsChain.singleton x)
    have hn := pairmap_nonzero (x :: p) proper x (p ++ [x])
      (by
        intro z hz
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hz ⊢
        rcases hz with hz | hz | hz
        · exact Or.inl hz
        · exact Or.inr hz
        · exact Or.inl hz) extended
    rw [List.map_cons, trace_cons]
    rw [List.map_append] at hn
    simpa using hn

/-- A genuine contract colouring has a proper zero-sum perimeter trace. -/
theorem contract_trace_proper {r cc : List D}
    (cycle : IsCyclicChain (fun x y => y = G.node x) r)
    (off : ∀ x ∈ G.insertE cc, x ∉ r) (et : List Color)
    (h : G.CcRingTrace cc r.reverse et) :
    et.length = r.length ∧ (0 : Color) ∉ et ∧ et.sum = 0 := by
  obtain ⟨k, hk, rfl⟩ := h
  refine ⟨by simp, ?_, sum_trace _⟩
  apply trace_nonzero r.reverse _ cycle.reverse
  intro x hx
  have hnode : G.node x ∈ r := mem_of_isCyclicChain cycle (List.mem_reverse.mp hx)
  have face := hk.face (G.edge (G.node x))
  rw [G.nodeK] at face
  intro equal
  exact off _ ((hk.edge (G.node x)).mp (face.symm.trans equal)) hnode

/-- The same D-repair law serves every geometrically valid contraction. -/
theorem reducible_of_repair {r cc : List D}
    (cycle : IsCyclicChain (fun x y => y = G.node x) r)
    (valid : G.ValidContract r cc)
    (repair : Repairs (G.RingTrace r.reverse) r.length) : G.CReducible r cc := by
  refine ⟨valid, fun et ht => ?_⟩
  obtain ⟨hlen, hzero, hsum⟩ := contract_trace_proper cycle valid.off_ring et ht
  exact repair et hlen hzero hsum

end FourColor.KempeRepairContract
