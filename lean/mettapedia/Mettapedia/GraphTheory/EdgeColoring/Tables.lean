import Mettapedia.GraphTheory.EdgeColoring.Completion
import Mettapedia.GraphTheory.FiniteReachability

/-!
# Edge colourings of listed graphs, decided by tables

A finite simple graph is given by the list of its edges, together with a table listing,
at each position, the positions of the edges meeting that edge; both are checked
(`Listing`).  An edge colouring is then a table of colours, one per position
(`Listing.coloring`).

A *Kempe block* of a table for the colours `a, b` is a list of positions of edges coloured
`a` or `b` in which every entry after the first meets an earlier entry, and which contains
every edge coloured `a` or `b` that meets one of its entries.  It is exactly one
two-coloured component (`kempeComponentSet_eq`), and switching `a` and `b` on it is the
Kempe switch on that component (`swapOnKempeComponent_eq`).  A family of tables with blocks
covering every two-coloured edge, each switching to a table of the family, is closed under
Kempe switches (`exists_eq_coloring_of_mem_edgeKempeClosure`); edges in different blocks
lie in different two-coloured components (`not_sameKempeComponent`).  This turns
statements about the Kempe classes of concrete edge colourings into finite checks that the
kernel can evaluate.
-/

namespace SimpleGraph

open Mettapedia.Logic.Relation

namespace EdgeTable

variable {V : Type*} [DecidableEq V] [Inhabited V]

/-- The simple graph with the listed edges. -/
def graph (es : List (V × V)) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => (u, v) ∈ es

omit [DecidableEq V] [Inhabited V] in
theorem graph_adj (es : List (V × V)) (u v : V) :
    (graph es).Adj u v ↔ u ≠ v ∧ ((u, v) ∈ es ∨ (v, u) ∈ es) :=
  fromRel_adj (fun u v => (u, v) ∈ es) u v

instance (es : List (V × V)) : DecidableRel (graph es).Adj := fun u v =>
  decidable_of_iff _ (graph_adj es u v).symm

omit [DecidableEq V] [Inhabited V] in
private theorem getD_eq_getElem {β : Type*} {l : List β} {d : β} {k : ℕ} (hk : k < l.length) :
    l.getD k d = l[k] := by
  simp [List.getD_eq_getElem?_getD, hk]

/-- The edge at position `k`. -/
def edgeAt (es : List (V × V)) (k : ℕ) : Sym2 V :=
  s((es.getD k default).1, (es.getD k default).2)

/-- Positions of distinct edges sharing an endpoint. -/
def Meets (es : List (V × V)) (k k' : ℕ) : Prop :=
  k ≠ k' ∧ ((es.getD k default).1 ∈ edgeAt es k' ∨ (es.getD k default).2 ∈ edgeAt es k')

instance (es : List (V × V)) (k k' : ℕ) : Decidable (Meets es k k') := by
  unfold Meets
  infer_instance

/-! ### Colour tables and blocks -/

section Tables

variable {α : Type*} [DecidableEq α] [Inhabited α]

/-- The colour at position `k` of a table. -/
abbrev colourAt (t : List α) (k : ℕ) : α :=
  t.getD k default

/-- Position `k` is coloured `a` or `b`. -/
def Bicoloured (t : List α) (a b : α) (k : ℕ) : Prop :=
  colourAt t k = a ∨ colourAt t k = b

instance (t : List α) (a b : α) (k : ℕ) : Decidable (Bicoloured t a b k) := by
  unfold Bicoloured
  infer_instance

/-- Switch the colours `a` and `b` at the positions of a block. -/
def swapTable (t : List α) (a b : α) (B : List ℕ) : List α :=
  (List.range t.length).map fun i => if i ∈ B then Equiv.swap a b (colourAt t i) else colourAt t i

theorem colourAt_swapTable (t : List α) (a b : α) (B : List ℕ) {i : ℕ} (hi : i < t.length) :
    colourAt (swapTable t a b B) i =
      if i ∈ B then Equiv.swap a b (colourAt t i) else colourAt t i := by
  simp [swapTable, colourAt, List.getD_eq_getElem?_getD, hi]

/-- Every entry after the first meets one of the entries before it (`pre`, reversed). -/
def listedConnected (adj : List (List ℕ)) : List ℕ → List ℕ → Bool
  | _, [] => true
  | pre, k :: ks => pre.any (fun j => k ∈ adj.getD j []) && listedConnected adj (k :: pre) ks

/-- A nonempty list in which every entry after the first meets an earlier entry. -/
def blockConnected (adj : List (List ℕ)) : List ℕ → Bool
  | [] => false
  | k :: ks => listedConnected adj [k] ks

end Tables

/-- A listed simple graph: no loops, no repeated edges, and a correct table of the
positions meeting each position. -/
structure Listing (V : Type*) [DecidableEq V] [Inhabited V] where
  /-- The edges. -/
  edges : List (V × V)
  /-- At each position, the positions of the edges meeting that edge. -/
  adj : List (List ℕ)
  loopless : ∀ p ∈ edges, p.1 ≠ p.2
  nodup : (edges.map fun p => s(p.1, p.2)).Nodup
  adj_lt : ∀ k < edges.length, ∀ k' ∈ adj.getD k [], k' < edges.length
  mem_adj_iff : ∀ k < edges.length, ∀ k' < edges.length, k' ∈ adj.getD k [] ↔ Meets edges k k'

namespace Listing

variable (L : Listing V)

/-- The simple graph of a listing. -/
abbrev graph : SimpleGraph V := EdgeTable.graph L.edges

theorem getD_mem {k : ℕ} (hk : k < L.edges.length) : L.edges.getD k default ∈ L.edges := by
  rw [getD_eq_getElem hk]
  exact List.getElem_mem hk

theorem edgeAt_mem_edgeSet {k : ℕ} (hk : k < L.edges.length) :
    edgeAt L.edges k ∈ L.graph.edgeSet := by
  rw [edgeAt, mem_edgeSet, graph_adj]
  exact ⟨L.loopless _ (L.getD_mem hk), Or.inl (L.getD_mem hk)⟩

theorem exists_edgeAt_eq (e : L.graph.edgeSet) : ∃ k < L.edges.length, edgeAt L.edges k = e := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | _ u v =>
    rw [mem_edgeSet, graph_adj] at he
    rcases he.2 with h | h
    · obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem h
      exact ⟨k, hk, by rw [edgeAt, getD_eq_getElem hk, hkeq]⟩
    · obtain ⟨k, hk, hkeq⟩ := List.getElem_of_mem h
      exact ⟨k, hk, by rw [edgeAt, getD_eq_getElem hk, hkeq]; exact Sym2.eq_swap⟩

theorem edgeAt_injective {k k' : ℕ} (hk : k < L.edges.length) (hk' : k' < L.edges.length)
    (h : edgeAt L.edges k = edgeAt L.edges k') : k = k' := by
  have hget : ∀ j (hj : j < L.edges.length),
      (L.edges.map fun p => s(p.1, p.2))[j]'(by simpa using hj) = edgeAt L.edges j := by
    intro j hj
    rw [List.getElem_map, edgeAt, getD_eq_getElem hj]
  exact (L.nodup.getElem_inj_iff).mp ((hget k hk).trans (h.trans (hget k' hk').symm))

/-- The position of an edge. -/
noncomputable def pos (e : L.graph.edgeSet) : ℕ :=
  (L.exists_edgeAt_eq e).choose

theorem pos_lt (e : L.graph.edgeSet) : L.pos e < L.edges.length :=
  (L.exists_edgeAt_eq e).choose_spec.1

theorem edgeAt_pos (e : L.graph.edgeSet) : edgeAt L.edges (L.pos e) = e :=
  (L.exists_edgeAt_eq e).choose_spec.2

/-- The edge at a position, as an edge of the graph. -/
def edge {k : ℕ} (hk : k < L.edges.length) : L.graph.edgeSet :=
  ⟨edgeAt L.edges k, L.edgeAt_mem_edgeSet hk⟩

theorem pos_edge {k : ℕ} (hk : k < L.edges.length) : L.pos (L.edge hk) = k :=
  L.edgeAt_injective (L.pos_lt _) hk (L.edgeAt_pos _)

theorem edge_pos (e : L.graph.edgeSet) : L.edge (L.pos_lt e) = e :=
  Subtype.ext (L.edgeAt_pos e)

theorem meets_iff {k k' : ℕ} :
    Meets L.edges k k' ↔ k ≠ k' ∧ ∃ v, v ∈ edgeAt L.edges k ∧ v ∈ edgeAt L.edges k' := by
  simp only [Meets, edgeAt, Sym2.mem_iff]
  constructor
  · rintro ⟨hne, h | h⟩
    · exact ⟨hne, _, Or.inl rfl, h⟩
    · exact ⟨hne, _, Or.inr rfl, h⟩
  · rintro ⟨hne, v, hv | hv, h⟩ <;> subst hv
    · exact ⟨hne, Or.inl h⟩
    · exact ⟨hne, Or.inr h⟩

theorem lineGraph_adj_iff {e f : L.graph.edgeSet} :
    L.graph.lineGraph.Adj e f ↔ Meets L.edges (L.pos e) (L.pos f) := by
  rw [lineGraph_adj_iff_exists, L.meets_iff, L.edgeAt_pos, L.edgeAt_pos]
  constructor
  · rintro ⟨hne, hv⟩
    exact ⟨fun h => hne (by rw [← L.edge_pos e, ← L.edge_pos f]; congr 1), hv⟩
  · rintro ⟨hne, hv⟩
    exact ⟨fun h => hne (by rw [h]), hv⟩

theorem mem_adj_iff_adj {e f : L.graph.edgeSet} :
    L.pos f ∈ L.adj.getD (L.pos e) [] ↔ L.graph.lineGraph.Adj e f := by
  rw [L.mem_adj_iff _ (L.pos_lt e) _ (L.pos_lt f), L.lineGraph_adj_iff]

/-- The adjacency table is symmetric. -/
theorem mem_adj_comm {k k' : ℕ} (hk : k < L.edges.length) (hk' : k' ∈ L.adj.getD k []) :
    k ∈ L.adj.getD k' [] := by
  have hk'lt := L.adj_lt k hk k' hk'
  have h := (L.mem_adj_iff_adj (e := L.edge hk) (f := L.edge hk'lt)).mp
    (by rwa [L.pos_edge, L.pos_edge])
  have h' := (L.mem_adj_iff_adj (e := L.edge hk'lt) (f := L.edge hk)).mpr h.symm
  rwa [L.pos_edge, L.pos_edge] at h'

/-! ### Colour tables -/

variable {α : Type*} [DecidableEq α] [Inhabited α]

/-- A table colours every edge, and meeting edges differently. -/
def ProperTable (t : List α) : Prop :=
  t.length = L.edges.length ∧
    ∀ k < L.edges.length, ∀ k' ∈ L.adj.getD k [], colourAt t k ≠ colourAt t k'

instance (t : List α) : Decidable (L.ProperTable t) := by
  unfold ProperTable
  infer_instance

/-- The edge colouring described by a proper table. -/
noncomputable def coloring (t : List α) (ht : L.ProperTable t) : L.graph.EdgeColoring α :=
  Coloring.mk (fun e => colourAt t (L.pos e)) fun {e _} hef =>
    ht.2 _ (L.pos_lt e) _ ((L.mem_adj_iff_adj).mpr hef)

omit [DecidableEq α] in
theorem coloring_apply (t : List α) (ht : L.ProperTable t) (e : L.graph.edgeSet) :
    L.coloring t ht e = colourAt t (L.pos e) := rfl

omit [DecidableEq α] in
theorem mem_bicoloredSet_iff (t : List α) (ht : L.ProperTable t) (a b : α)
    (e : L.graph.edgeSet) :
    e ∈ (L.coloring t ht).bicoloredSet a b ↔ Bicoloured t a b (L.pos e) := Iff.rfl

/-! ### Kempe blocks -/

/-- `B` is one two-coloured component of the table `t` for the colours `a, b`. -/
structure IsKempeBlock (t : List α) (a b : α) (B : List ℕ) : Prop where
  lt : ∀ k ∈ B, k < L.edges.length
  bicoloured : ∀ k ∈ B, Bicoloured t a b k
  connected : blockConnected L.adj B = true
  closed : ∀ k ∈ B, ∀ k' ∈ L.adj.getD k [], Bicoloured t a b k' → k' ∈ B

instance (t : List α) (a b : α) (B : List ℕ) : Decidable (L.IsKempeBlock t a b B) :=
  decidable_of_iff ((∀ k ∈ B, k < L.edges.length) ∧ (∀ k ∈ B, Bicoloured t a b k) ∧
      blockConnected L.adj B = true ∧
      ∀ k ∈ B, ∀ k' ∈ L.adj.getD k [], Bicoloured t a b k' → k' ∈ B)
    ⟨fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩, fun ⟨h₁, h₂, h₃, h₄⟩ => ⟨h₁, h₂, h₃, h₄⟩⟩

/-- The step relation of two-coloured adjacency on positions. -/
def bicolouredStep (t : List α) (a b : α) (k k' : ℕ) : Prop :=
  k' ∈ L.adj.getD k [] ∧ Bicoloured t a b k'

variable {L}

omit [DecidableEq α] in
private theorem listedConnected_reach {t : List α} {a b : α} {r : ℕ} :
    ∀ (ks pre : List ℕ), (∀ j ∈ pre, Relation.ReflTransGen (L.bicolouredStep t a b) r j) →
      (∀ k ∈ ks, Bicoloured t a b k) → listedConnected L.adj pre ks = true →
        ∀ k ∈ ks, Relation.ReflTransGen (L.bicolouredStep t a b) r k := by
  intro ks
  induction ks with
  | nil => intro _ _ _ _ k hk; simp at hk
  | cons k ks ih =>
    intro pre hpre hks hcon
    simp only [listedConnected, Bool.and_eq_true, List.any_eq_true] at hcon
    obtain ⟨⟨j, hj, hjk⟩, hrest⟩ := hcon
    have hk : Relation.ReflTransGen (L.bicolouredStep t a b) r k :=
      (hpre j hj).tail ⟨of_decide_eq_true hjk, hks k List.mem_cons_self⟩
    intro k' hk'
    rcases List.mem_cons.mp hk' with rfl | hk'
    · exact hk
    · exact ih (k :: pre) (by
          intro j hj
          rcases List.mem_cons.mp hj with rfl | hj
          · exact hk
          · exact hpre j hj)
        (fun k'' h => hks k'' (List.mem_cons_of_mem _ h)) hrest k' hk'

omit [DecidableEq α] in
/-- A block is closed under two-coloured adjacency. -/
theorem IsKempeBlock.mem_of_reflTransGen {t : List α} {a b : α} {B : List ℕ}
    (hB : L.IsKempeBlock t a b B) {k k' : ℕ} (hk : k ∈ B)
    (h : Relation.ReflTransGen (L.bicolouredStep t a b) k k') : k' ∈ B := by
  induction h with
  | refl => exact hk
  | tail _ hstep ih => exact hB.closed _ ih _ hstep.1 hstep.2

omit [DecidableEq α] in
/-- Every entry of a block is reached from every other along two-coloured adjacency. -/
theorem IsKempeBlock.reflTransGen {t : List α} {a b : α} {B : List ℕ}
    (hB : L.IsKempeBlock t a b B) {k k' : ℕ} (hk : k ∈ B) (hk' : k' ∈ B) :
    Relation.ReflTransGen (L.bicolouredStep t a b) k k' := by
  cases B with
  | nil => exact absurd hB.connected (by simp [blockConnected])
  | cons r ks =>
    have hfrom : ∀ j ∈ r :: ks, Relation.ReflTransGen (L.bicolouredStep t a b) r j := by
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact .refl
      · exact listedConnected_reach ks [r]
          (fun i hi => (List.mem_singleton.mp hi) ▸ .refl)
          (fun k hk => hB.bicoloured k (List.mem_cons_of_mem _ hk)) hB.connected j hj
    -- two-coloured adjacency between entries of a block is symmetric, so paths reverse
    have hsymm : ∀ j, Relation.ReflTransGen (L.bicolouredStep t a b) r j →
        Relation.ReflTransGen (L.bicolouredStep t a b) j r := by
      intro j hj
      induction hj with
      | refl => exact .refl
      | tail hrx hxy ih =>
        rename_i x y
        have hx : x ∈ r :: ks := hB.mem_of_reflTransGen List.mem_cons_self hrx
        exact Relation.ReflTransGen.head ⟨L.mem_adj_comm (hB.lt x hx) hxy.1, hB.bicoloured x hx⟩ ih
    exact (hsymm k (hfrom k hk)).trans (hfrom k' hk')

variable (L)

omit [DecidableEq α] in
/-- Reachability in the two-coloured subgraph of the line graph is two-coloured adjacency
of positions. -/
theorem reachable_iff (t : List α) (ht : L.ProperTable t) (a b : α)
    (x y : L.graph.edgeSet) (hx : x ∈ (L.coloring t ht).bicoloredSet a b)
    (hy : y ∈ (L.coloring t ht).bicoloredSet a b) :
    ((L.coloring t ht).bicoloredSubgraph a b).Reachable ⟨x, hx⟩ ⟨y, hy⟩ ↔
      Relation.ReflTransGen (L.bicolouredStep t a b) (L.pos x) (L.pos y) := by
  rw [Coloring.bicoloredSubgraph, induce_reachable_iff_reflTransGen]
  constructor
  · intro h
    exact Relation.ReflTransGen.lift L.pos (fun u w huw =>
      ⟨(L.mem_adj_iff_adj).mpr huw.1, huw.2⟩) _ _ h
  · intro h
    suffices key : ∀ k, Relation.ReflTransGen (L.bicolouredStep t a b) (L.pos x) k →
        ∃ hk : k < L.edges.length, Relation.ReflTransGen
          (fun u w => L.graph.lineGraph.Adj u w ∧ w ∈ (L.coloring t ht).bicoloredSet a b)
          x (L.edge hk) by
      obtain ⟨hk, hreach⟩ := key _ h
      rwa [L.edge_pos] at hreach
    intro k hk
    induction hk with
    | refl => exact ⟨L.pos_lt x, by rw [L.edge_pos]⟩
    | tail _ hstep ih =>
      obtain ⟨hlt, hreach⟩ := ih
      have hlt' := L.adj_lt _ hlt _ hstep.1
      refine ⟨hlt', hreach.tail ⟨?_, ?_⟩⟩
      · rw [← L.mem_adj_iff_adj, L.pos_edge, L.pos_edge]
        exact hstep.1
      · rw [mem_bicoloredSet_iff, L.pos_edge]
        exact hstep.2

omit [DecidableEq α] in
/-- **A Kempe block is exactly one two-coloured component.** -/
theorem kempeComponentSet_eq (t : List α) (ht : L.ProperTable t) (a b : α) {B : List ℕ}
    (hB : L.IsKempeBlock t a b B) {k : ℕ} (hk : k ∈ B) :
    (L.coloring t ht).kempeComponentSet a b
        (((L.coloring t ht).bicoloredSubgraph a b).connectedComponentMk
          ⟨L.edge (hB.lt k hk), by
            rw [mem_bicoloredSet_iff, L.pos_edge]; exact hB.bicoloured k hk⟩) =
      {e | L.pos e ∈ B} := by
  ext e
  simp only [Coloring.kempeComponentSet, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨he, hK⟩
    have hreach := (ConnectedComponent.exact hK).symm
    rw [reachable_iff, L.pos_edge] at hreach
    exact hB.mem_of_reflTransGen hk hreach
  · intro he
    have hbic : e ∈ (L.coloring t ht).bicoloredSet a b := by
      rw [mem_bicoloredSet_iff]; exact hB.bicoloured _ he
    refine ⟨hbic, ConnectedComponent.sound ?_⟩
    rw [reachable_iff, L.pos_edge]
    exact hB.reflTransGen he hk

/-- **Switching the colours on a Kempe block is the Kempe switch of its component.** -/
theorem swapOnKempeComponent_eq (t : List α) (ht : L.ProperTable t) (a b : α) {B : List ℕ}
    (hB : L.IsKempeBlock t a b B) {k : ℕ} (hk : k ∈ B) (t' : List α) (ht' : L.ProperTable t')
    (hswap : swapTable t a b B = t') :
    (L.coloring t ht).swapOnKempeComponent a b
        (((L.coloring t ht).bicoloredSubgraph a b).connectedComponentMk
          ⟨L.edge (hB.lt k hk), by
            rw [mem_bicoloredSet_iff, L.pos_edge]; exact hB.bicoloured k hk⟩) =
      L.coloring t' ht' := by
  subst hswap
  refine DFunLike.ext _ _ fun e => ?_
  have hlt : L.pos e < t.length := ht.1 ▸ L.pos_lt e
  rw [coloring_apply, colourAt_swapTable _ _ _ _ hlt]
  have hset := L.kempeComponentSet_eq t ht a b hB hk
  by_cases he : L.pos e ∈ B
  · rw [if_pos he, (L.coloring t ht).swapOnKempeComponent_apply_of_mem
      ((Set.ext_iff.mp hset e).mpr he)]
    rfl
  · rw [if_neg he, (L.coloring t ht).swapOnKempeComponent_apply_of_not_mem
      fun h => he ((Set.ext_iff.mp hset e).mp h)]
    rfl

variable (S : List (List α)) (cert : ℕ → α → α → List (List ℕ × ℕ))

/-- A Kempe certificate for a family `S` of tables: each table is proper, and for every
table `i` and colours `a, b`, the blocks `cert i a b` are Kempe blocks covering every edge
coloured `a` or `b`, each listed with the position in `S` of the table obtained by
switching it. -/
def KempeCertificate : Prop :=
  (∀ i < S.length, L.ProperTable (S.getD i [])) ∧
    (∀ i < S.length, ∀ a b, ∀ k < L.edges.length, Bicoloured (S.getD i []) a b k →
      ∃ blk ∈ cert i a b, k ∈ blk.1) ∧
    ∀ i < S.length, ∀ a b, ∀ blk ∈ cert i a b, L.IsKempeBlock (S.getD i []) a b blk.1 ∧
      blk.2 < S.length ∧ swapTable (S.getD i []) a b blk.1 = S.getD blk.2 []

instance [Fintype α] : Decidable (L.KempeCertificate S cert) := by
  unfold KempeCertificate
  have : ∀ (i : ℕ) (a b : α), Decidable (∀ k < L.edges.length,
      Bicoloured (S.getD i []) a b k → ∃ blk ∈ cert i a b, k ∈ blk.1) :=
    fun _ _ _ => inferInstance
  infer_instance

variable {L S cert}

theorem KempeCertificate.proper (h : L.KempeCertificate S cert) :
    ∀ i < S.length, L.ProperTable (S.getD i []) := h.1

theorem KempeCertificate.cover (h : L.KempeCertificate S cert) :
    ∀ i < S.length, ∀ a b, ∀ k < L.edges.length, Bicoloured (S.getD i []) a b k →
      ∃ blk ∈ cert i a b, k ∈ blk.1 := h.2.1

theorem KempeCertificate.block (h : L.KempeCertificate S cert) :
    ∀ i < S.length, ∀ a b, ∀ blk ∈ cert i a b, L.IsKempeBlock (S.getD i []) a b blk.1 ∧
      blk.2 < S.length ∧ swapTable (S.getD i []) a b blk.1 = S.getD blk.2 [] := h.2.2


/-- **A certified family is closed under Kempe switches**: every colouring reachable from a
member by Kempe switches is described by a table of the family. -/
theorem exists_eq_coloring_of_mem_edgeKempeClosure (hcert : L.KempeCertificate S cert)
    {i₀ : ℕ} (hi₀ : i₀ < S.length) {C : L.graph.EdgeColoring α}
    (hC : C ∈ L.graph.EdgeKempeClosure (L.coloring _ (hcert.proper i₀ hi₀))) :
    ∃ (i : ℕ) (hi : i < S.length), C = L.coloring _ (hcert.proper i hi) := by
  change Relation.ReflTransGen _ _ _ at hC
  induction hC with
  | refl => exact ⟨i₀, hi₀, rfl⟩
  | tail _ hstep ih =>
    obtain ⟨i, hi, rfl⟩ := ih
    obtain ⟨a, b, K, rfl⟩ := hstep
    induction K using ConnectedComponent.ind with
    | h x =>
      obtain ⟨e, hx⟩ := x
      have hk : Bicoloured (S.getD i []) a b (L.pos e) := (mem_bicoloredSet_iff _ _ _ _ _ e).mp hx
      obtain ⟨blk, hblk, hkblk⟩ := hcert.cover i hi a b _ (L.pos_lt e) hk
      obtain ⟨hB, htlt, htgt⟩ := hcert.block i hi a b blk hblk
      refine ⟨blk.2, htlt, ?_⟩
      have hrep : (⟨e, hx⟩ : ↥((L.coloring _ (hcert.proper i hi)).bicoloredSet a b)) =
          ⟨L.edge (hB.lt _ hkblk), by
            rw [mem_bicoloredSet_iff, L.pos_edge]; exact hB.bicoloured _ hkblk⟩ :=
        Subtype.ext (L.edge_pos e).symm
      rw [hrep]
      exact L.swapOnKempeComponent_eq _ _ a b hB hkblk _ _ htgt

/-- **Edges in different blocks lie in different two-coloured components.** -/
theorem not_sameKempeComponent (hcert : L.KempeCertificate S cert) {i : ℕ} (hi : i < S.length)
    {a b : α} {k₁ k₂ : ℕ} (hk₁ : k₁ < L.edges.length) (hk₂ : k₂ < L.edges.length)
    (hsep : ∀ blk ∈ cert i a b, k₁ ∈ blk.1 → k₂ ∉ blk.1) :
    ¬ Coloring.SameKempeComponent (L.coloring _ (hcert.proper i hi)) a b
      (L.edge hk₁) (L.edge hk₂) := by
  intro hsame
  obtain ⟨hx, hy, hreach⟩ := hsame
  have hk : Bicoloured (S.getD i []) a b k₁ := by
    have := (mem_bicoloredSet_iff _ _ _ _ _ _).mp hx
    rwa [L.pos_edge] at this
  obtain ⟨blk, hblk, hk₁blk⟩ := hcert.cover i hi a b k₁ hk₁ hk
  obtain ⟨hB, -, -⟩ := hcert.block i hi a b blk hblk
  have hmem := (Coloring.sameKempeComponent_iff_mem_kempeComponentSet _ a b hx).mp
    ⟨hx, hy, hreach⟩
  rw [L.kempeComponentSet_eq _ _ a b hB hk₁blk] at hmem
  exact hsep blk hblk hk₁blk (by rwa [Set.mem_ofPred_eq, L.pos_edge] at hmem)

/-- **No colouring of a certified family is completable by Kempe switches** across two
edges that no block of the family contains together. -/
theorem not_kempeCompletableAcross (hcert : L.KempeCertificate S cert) {i₀ : ℕ}
    (hi₀ : i₀ < S.length) {k₁ k₂ : ℕ} (hk₁ : k₁ < L.edges.length) (hk₂ : k₂ < L.edges.length)
    (hsep : ∀ i < S.length, ∀ a b, ∀ blk ∈ cert i a b, k₁ ∈ blk.1 → k₂ ∉ blk.1) :
    ¬ EdgeColoring.KempeCompletableAcross (L.coloring _ (hcert.proper i₀ hi₀))
      (L.edge hk₁) (L.edge hk₂) := by
  rintro ⟨C, hC, a, b, hab⟩
  obtain ⟨i, hi, rfl⟩ := exists_eq_coloring_of_mem_edgeKempeClosure hcert hi₀ hC
  exact not_sameKempeComponent hcert hi hk₁ hk₂ (hsep i hi a b) hab

end Listing

end EdgeTable

end SimpleGraph
