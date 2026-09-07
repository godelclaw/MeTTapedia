import Mettapedia.GraphTheory.FourColor.IntegralMaxFlow
import Mettapedia.GraphTheory.FourColor.VertexSeparatorBond

/-!
# Vertex splitting: a small integral-flow cut supplies a vertex separator

Every original vertex, including a terminal, receives a unit entry-to-exit
gate. All original adjacencies and terminal connectors have capacity k.
A cut of capacity less than k crosses none of these connectors; its
crossing unit gates therefore meet every terminal-to-terminal walk.
This constructs the separator on the original graph, not a local carrier.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexSplitCut

open IntegralFlow
variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev Node (V : Type*) := Fin 2 ⊕ (V × Bool)
def source : Node V := Sum.inl 0
def sink : Node V := Sum.inl 1
def entry (v : V) : Node V := Sum.inr (v, false)
def exit (v : V) : Node V := Sum.inr (v, true)

variable (G : SimpleGraph V) (A B : Set V) (k : ℕ)

noncomputable def network : Network (Node V) := by
  classical
  exact {
    capacity := fun u v => match u, v with
      | .inr (x, false), .inr (y, true) => if x = y then 1 else 0
      | .inl s, .inr (y, false) => if s = 0 ∧ y ∈ A then k else 0
      | .inr (x, true), .inr (y, false) => if G.Adj x y then k else 0
      | .inr (x, true), .inl t => if t = 1 ∧ x ∈ B then k else 0
      | _, _ => 0
    source := source
    sink := sink
    distinct := by simp [source, sink] }

omit [Fintype V] in
theorem capacity_gate (v : V) : (network G A B k).capacity (entry v) (exit v) = 1 := by
  classical
  simp [network, entry, exit]

omit [Fintype V] in
theorem capacity_start {v : V} (hv : v ∈ A) :
    (network G A B k).capacity source (entry v) = k := by
  classical
  simp [network, source, entry, hv]

omit [Fintype V] in
theorem capacity_finish {v : V} (hv : v ∈ B) :
    (network G A B k).capacity (exit v) sink = k := by
  classical
  simp [network, sink, exit, hv]

omit [Fintype V] in
theorem capacity_adj {u v : V} (h : G.Adj u v) :
    (network G A B k).capacity (exit u) (entry v) = k := by
  classical
  simp [network, entry, exit, h]

noncomputable def cutVertices (S : Finset (Node V)) : Finset V := by
  classical
  exact Finset.univ.filter fun v => entry v ∈ S ∧ exit v ∉ S

/-- Every crossing unit gate contributes its own unit to the full cut. -/
theorem card_cutVertices_le (S : Finset (Node V)) :
    ((cutVertices S).card : ℤ) ≤ Flow.cutCapacity (network G A B k) S := by
  classical
  let X := cutVertices S
  let pairs := X.image fun v => (entry v, exit v)
  have hinj : Function.Injective (fun v : V => (entry v, exit v)) := by
    intro u v h
    have he := congrArg Prod.fst h
    simpa [entry] using he
  have hsub : pairs ⊆ S.product Sᶜ := by
    intro e he
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨_, hi, ho⟩ := Finset.mem_filter.mp hv
    exact Finset.mem_product.mpr ⟨hi, Finset.mem_compl.mpr ho⟩
  have hsum : (X.card : ℤ) = ∑ e ∈ pairs, ((network G A B k).capacity e.1 e.2 : ℤ) := by
    rw [Finset.sum_image (fun _ _ _ _ h => hinj h)]
    simp only [capacity_gate, Nat.cast_one, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hsum]
  change (∑ e ∈ pairs, ((network G A B k).capacity e.1 e.2 : ℤ)) ≤ _
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun e _ _ => Int.natCast_nonneg ((network G A B k).capacity e.1 e.2))
  exact hle.trans_eq (Finset.sum_product S Sᶜ
    (fun e => ((network G A B k).capacity e.1 e.2 : ℤ)))

/-- A low-capacity split cut supplies a separator meeting every ambient walk. -/
theorem separates_of_small_cut (S : Finset (Node V))
    (hs : source ∈ S) (ht : sink ∉ S)
    (hc : Flow.cutCapacity (network G A B k) S < k) :
    VertexSeparatorBond.Separates G A B (cutVertices S : Set V) := by
  classical
  have closed {u v : Node V} (hcap : (network G A B k).capacity u v = k)
      (hu : u ∈ S) : v ∈ S := by
    by_contra hv
    have hle := Flow.capacity_le_cut (network G A B k) S hu hv
    rw [hcap] at hle
    omega
  have gate {u : V} (hu : entry u ∈ S) (hx : u ∉ cutVertices S) : exit u ∈ S := by
    by_contra h
    exact hx (by simp [cutVertices, hu, h])
  have walk_closed {a b : V} (p : G.Walk a b) (ha : entry a ∈ S)
      (hp : ∀ x ∈ p.support, x ∉ cutVertices S) : entry b ∈ S := by
    induction p with
    | nil => exact ha
    | @cons a b c hab p ih =>
      apply ih (closed (capacity_adj G A B k hab) (gate ha (hp a (by simp))))
      intro x hx
      exact hp x (List.mem_cons_of_mem a hx)
  intro a ha b hb p
  by_contra h
  push Not at h
  have hentry := walk_closed p (closed (capacity_start G A B k ha) hs) h
  have hexit := gate hentry (h b p.end_mem_support)
  exact ht (closed (capacity_finish G A B k hb) hexit)

/-- The integral theorem now constructs the small separator branch. The
large branch retains the actual integer flow for subsequent path extraction. -/
theorem exists_large_flow_or_small_separator :
    (∃ f : Flow (network G A B k), (k : ℤ) ≤ f.value) ∨
      ∃ X : Finset V, X.card < k ∧ VertexSeparatorBond.Separates G A B X := by
  classical
  obtain ⟨f, S, hs, ht, heq, _hmax, _hmin⟩ := Flow.exists_max_flow_min_cut (network G A B k)
  by_cases h : (k : ℤ) ≤ f.value
  · exact Or.inl ⟨f, h⟩
  · right
    have hc : Flow.cutCapacity (network G A B k) S < k := by omega
    refine ⟨cutVertices S, ?_, separates_of_small_cut G A B k S hs ht hc⟩
    exact_mod_cast lt_of_le_of_lt (card_cutVertices_le G A B k S) hc

end Mettapedia.GraphTheory.FourColor.VertexSplitCut
