import Mettapedia.GraphTheory.FourColor.VertexSplitCut
import Mettapedia.GraphTheory.FourColor.IntegralFlowDecomposition

/-!
# Decode split-network routes into vertex-disjoint ambient walks

Every allowed route alternates a unit vertex gate with an actual graph
adjacency. Its initial and final connectors certify terminal membership.
Every vertex of the decoded walk uses its gate, including endpoints;
the integral flow capacity bound therefore makes different decoded walks
vertex-disjoint. Together with the low-cut construction this supplies the
finite vertex separator/linkage alternative on the complete original graph.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexSplitCut

open IntegralFlow
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) (A B : Set V) (k : ℕ)

omit [Fintype V] in
theorem allowed_entry {u : V} {q : Node V}
    (h : (network G A B k).Allowed (entry u) q) : q = exit u := by
  classical
  rcases q with t | ⟨v, b⟩
  · simp [Network.Allowed, network, entry] at h
  · cases b
    · simp [Network.Allowed, network, entry] at h
    · have huv : u = v := by
        by_contra hn
        simp [Network.Allowed, network, entry, hn] at h
      subst v
      rfl

omit [Fintype V] in
theorem allowed_exit {u : V} {q : Node V}
    (h : (network G A B k).Allowed (exit u) q) :
    (q = sink ∧ u ∈ B) ∨ ∃ v, q = entry v ∧ G.Adj u v := by
  classical
  rcases q with t | ⟨v, b⟩
  · have ht : t = 1 ∧ u ∈ B := by
      by_contra hn
      simp [Network.Allowed, network, exit, hn] at h
    exact Or.inl ⟨by simp [sink, ht.1], ht.2⟩
  · cases b
    · have huv : G.Adj u v := by
        by_contra hn
        simp [Network.Allowed, network, exit, hn] at h
      exact Or.inr ⟨v, rfl, huv⟩
    · simp [Network.Allowed, network, exit] at h

omit [Fintype V] in
theorem allowed_source {q : Node V}
    (h : (network G A B k).Allowed source q) : ∃ v ∈ A, q = entry v := by
  classical
  rcases q with t | ⟨v, b⟩
  · simp [Network.Allowed, network, source] at h
  · cases b
    · have hv : v ∈ A := by
        by_contra hn
        simp [Network.Allowed, network, source, hn] at h
      exact ⟨v, hv, rfl⟩
    · simp [Network.Allowed, network, source] at h

omit [Fintype V] in
/-- Entry and exit versions are proved together. The exit version has
already passed its first gate; every later vertex still uses a gate. -/
theorem decode_tail {a b : Node V} (p : Route (network G A B k).Allowed a b)
    (hb : b = sink) :
    (∀ u, a = entry u → ∃ v ∈ B, ∃ w : G.Walk u v,
      ∀ x ∈ w.support, p.Uses (entry x) (exit x)) ∧
    (∀ u, a = exit u → ∃ v ∈ B, ∃ w : G.Walk u v,
      ∀ x ∈ w.support, x = u ∨ p.Uses (entry x) (exit x)) := by
  induction p with
  | nil a =>
    subst a
    constructor <;> intro u h <;> simp [entry, exit, sink] at h
  | @cons a b c e p ih =>
    have ih := ih hb
    constructor
    · intro u hu
      subst a
      have heq : b = exit u := allowed_entry G A B k e
      obtain ⟨v, hv, w, hw⟩ := ih.2 u heq
      refine ⟨v, hv, w, fun x hx => ?_⟩
      rcases hw x hx with rfl | hx
      · exact Or.inl ⟨rfl, heq.symm⟩
      · exact Or.inr hx
    · intro u hu
      subst a
      rcases allowed_exit G A B k e with ⟨heq, huB⟩ | ⟨v, heq, huv⟩
      · exact ⟨u, huB, .nil, fun x hx => Or.inl (by simpa using hx)⟩
      · obtain ⟨z, hz, w, hw⟩ := ih.1 v heq
        refine ⟨z, hz, .cons huv w, fun x hx => ?_⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (hw x hx))

omit [Fintype V] in
/-- Decode an entire route and retain a gate witness for every visited vertex. -/
theorem decode_route (p : Route (network G A B k).Allowed source sink) :
    ∃ a ∈ A, ∃ b ∈ B, ∃ w : G.Walk a b,
      ∀ x ∈ w.support, p.Uses (entry x) (exit x) := by
  cases p with
  | @cons a b c e p =>
    obtain ⟨v, hv, heq⟩ := allowed_source G A B k e
    obtain ⟨z, hz, w, hw⟩ := (decode_tail G A B k p rfl).1 v heq
    exact ⟨v, hv, z, hz, w, fun x hx => Or.inr (hw x hx)⟩

/-- Paths are disjoint on every visited vertex, including both endpoints. -/
structure Linkage (G : SimpleGraph V) (A B : Set V) (m : ℕ) where
  start : Fin m → V
  finish : Fin m → V
  start_mem : ∀ i, start i ∈ A
  finish_mem : ∀ i, finish i ∈ B
  walk : ∀ i, G.Walk (start i) (finish i)
  simple : ∀ i, (walk i).IsPath
  disjoint : ∀ i j, i ≠ j → ∀ x, x ∈ (walk i).support → x ∈ (walk j).support → False

omit [Fintype V] [DecidableEq V] in
/-- A separator must meet different linkage paths at different vertices. -/
theorem Linkage.le_separator {m : ℕ} (L : Linkage G A B m) (X : Finset V)
    (hX : VertexSeparatorBond.Separates G A B X) : m ≤ X.card := by
  classical
  have hx (i : Fin m) := hX (L.start i) (L.start_mem i) (L.finish i) (L.finish_mem i) (L.walk i)
  choose x hw hx using hx
  let f : Fin m → X := fun i => ⟨x i, hx i⟩
  have hf : Function.Injective f := by
    intro i j hij
    by_contra hne
    have heq : x i = x j := congrArg Subtype.val hij
    exact L.disjoint i j hne (x i) (hw i) (heq ▸ hw j)
  simpa only [Fintype.card_fin, Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- An actual integer flow supplies actual vertex-disjoint original paths. -/
theorem exists_linkage_of_flow (f : Flow (network G A B k)) (m : ℕ)
    (hm : (m : ℤ) ≤ f.value) : Nonempty (Linkage G A B m) := by
  classical
  obtain ⟨paths, hn, hb⟩ := f.exists_routes m hm
  choose a ha b hb' w hw using fun i => decode_route G A B k (paths i)
  refine ⟨{
    start := a
    finish := b
    start_mem := ha
    finish_mem := hb'
    walk := fun i => (w i).bypass
    simple := fun i => (w i).bypass_isPath
    disjoint := ?_ }⟩
  intro i j hij x hix hjx
  have hi := hw i x ((w i).support_bypass_subset_support hix)
  have hj := hw j x ((w j).support_bypass_subset_support hjx)
  apply Route.unit_gate_disjoint f paths hb hij (capacity_gate G A B k x) ?_
    ((paths i).delta_eq_one_of_uses (hn i) hi) ((paths j).delta_eq_one_of_uses (hn j) hj)
  simp [network, entry, exit]

/-- Finite vertex Menger alternative, with terminal vertices capacity-limited
and separators allowed to meet the terminals. No connectivity is assumed. -/
theorem exists_linkage_or_separator :
    Nonempty (Linkage G A B k) ∨
      ∃ X : Finset V, X.card < k ∧ VertexSeparatorBond.Separates G A B X := by
  rcases exists_large_flow_or_small_separator G A B k with ⟨f, hf⟩ | hX
  · exact Or.inl (exists_linkage_of_flow G A B k f k hf)
  · exact Or.inr hX

end Mettapedia.GraphTheory.FourColor.VertexSplitCut
