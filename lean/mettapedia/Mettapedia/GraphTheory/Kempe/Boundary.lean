import Mettapedia.GraphTheory.Kempe.Symm
import Mettapedia.GraphTheory.EdgeColoring
import Mettapedia.Combinatorics.Reconfiguration.Completability
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Kempe dynamics relative to a boundary

A graph `G` with a set `B` of boundary vertices.  Everything is stated for
vertex colourings of an arbitrary simple graph.  Edge colourings are the
special case of a line graph, with `B` a set of edges; for a tangle whose
stubs are glued into parallel edges (two gadgets in series already produce a
digon), the line graph is still a simple graph on the edges, so the same
definitions apply to it directly.

* `Coloring.boundaryWord C B` — the colours `C` shows on `B`;
* `boundaryFibre G B c` — the colourings with boundary word `c`;
* `KempeStepAvoiding G B` — a Kempe switch on a two-colour component disjoint
  from `B`.  It fixes every colour on `B`, so its closure stays in a fibre;
* `FibreConnected G α B` — local Kempe reachability with fixed input
  (LKR_in): two colourings with the same word on `B` are joined by switches
  avoiding `B`.  It is `Reconfiguration.FibresConnected` for these moves and
  the boundary word;
* `WeaklyCompletable G α ∂ W` — weak completability WC*(G, W): from every
  colouring, a colouring whose word on `∂` lies in `W` is reachable by Kempe
  switches, provided one exists.  It is `Reconfiguration.WeaklyCompletable`;
* `Coloring.IsTransparent C ∂` — no two-colour component of `C` avoids `∂`.

## Transparency

Lemma 8.15 of the v23 manuscript asserts, for the canonical tree gadget, that
each two-colour subgraph is a disjoint union of simple paths whose endpoints are
boundary stubs.  Its two consequences are that no two-colour component lives
in the interior (no interior Kempe cycles), and that a component meeting the
boundary meets it in exactly two stubs.  Only the first makes sense for an
arbitrary graph, and it is the one used downstream: a switch must show on the
boundary.  `IsTransparent` is that first property.  Its consequences proved
here:

* a transparent colouring admits no nontrivial switch avoiding a superset of
  `∂` (`IsTransparent.eq_of_kempeStepAvoiding`), so its fibre closure is a
  single point;
* every nontrivial switch changes the boundary word
  (`IsTransparent.boundaryWord_swap_ne`);
* when every colouring is transparent, LKR_in relative to `∂` holds exactly
  when the boundary word determines the colouring
  (`Transparent.fibreConnected_iff`);
* the manuscript's tree argument, in general form: acyclic two-colour
  subgraphs in which every vertex off `∂` has two two-colour neighbours give
  transparency (`Coloring.isTransparent_of_isAcyclic`).
-/

namespace SimpleGraph

open Relation
open Mettapedia.Combinatorics.Reconfiguration

variable {V α : Type*} {G : SimpleGraph V}

namespace Coloring

/-- The colours a colouring shows on a set of vertices. -/
def boundaryWord (C : G.Coloring α) (B : Set V) : B → α :=
  fun v => C v

@[simp] theorem boundaryWord_apply (C : G.Coloring α) (B : Set V) (v : B) :
    C.boundaryWord B v = C v :=
  rfl

theorem boundaryWord_eq_iff {C D : G.Coloring α} {B : Set V} :
    C.boundaryWord B = D.boundaryWord B ↔ ∀ v ∈ B, C v = D v := by
  constructor
  · intro h v hv
    exact congrFun h ⟨v, hv⟩
  · intro h
    funext v
    exact h v.1 v.2

theorem boundaryWord_eq_of_subset {C D : G.Coloring α} {B B' : Set V} (hBB' : B ⊆ B')
    (h : C.boundaryWord B' = D.boundaryWord B') : C.boundaryWord B = D.boundaryWord B :=
  boundaryWord_eq_iff.2 fun v hv => boundaryWord_eq_iff.1 h v (hBB' hv)

/-- A colouring is **transparent** relative to `∂` when every two-colour Kempe
component, for two distinct colours, meets `∂`: no component lives in the
interior. -/
def IsTransparent (C : G.Coloring α) (bdry : Set V) : Prop :=
  ∀ a b, a ≠ b → ∀ K : (C.bicoloredSubgraph a b).ConnectedComponent,
    (C.kempeComponentSet a b K ∩ bdry).Nonempty

theorem IsTransparent.mono {C : G.Coloring α} {bdry bdry' : Set V} (hsub : bdry ⊆ bdry')
    (h : C.IsTransparent bdry) : C.IsTransparent bdry' :=
  fun a b hab K => (h a b hab K).mono (Set.inter_subset_inter_right _ hsub)

end Coloring

/-- The fibre over a boundary word. -/
def boundaryFibre (G : SimpleGraph V) (B : Set V) (c : B → α) : Set (G.Coloring α) :=
  {C | C.boundaryWord B = c}

/-- Every colouring of `G` with colours `α` is transparent relative to `∂`. -/
def Transparent (G : SimpleGraph V) (α : Type*) (bdry : Set V) : Prop :=
  ∀ C : G.Coloring α, C.IsTransparent bdry

section Avoiding

variable [DecidableEq α]

/-- One Kempe switch on a two-colour component disjoint from `B`. -/
def KempeStepAvoiding (G : SimpleGraph V) (B : Set V) (C C' : G.Coloring α) : Prop :=
  ∃ a b, ∃ K : (C.bicoloredSubgraph a b).ConnectedComponent,
    Disjoint (C.kempeComponentSet a b K) B ∧ C' = C.swapOnKempeComponent a b K

theorem kempeStepAvoiding_swapOnKempeComponent {B : Set V} (C : G.Coloring α) (a b : α)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    (hK : Disjoint (C.kempeComponentSet a b K) B) :
    G.KempeStepAvoiding B C (C.swapOnKempeComponent a b K) :=
  ⟨a, b, K, hK, rfl⟩

namespace KempeStepAvoiding

variable {B B' : Set V} {C C' : G.Coloring α}

theorem kempeStep (h : G.KempeStepAvoiding B C C') : G.KempeStep C C' := by
  obtain ⟨a, b, K, -, rfl⟩ := h
  exact ⟨a, b, K, rfl⟩

theorem mono (hsub : B' ⊆ B) (h : G.KempeStepAvoiding B C C') :
    G.KempeStepAvoiding B' C C' := by
  obtain ⟨a, b, K, hK, rfl⟩ := h
  exact ⟨a, b, K, hK.mono_right hsub, rfl⟩

/-- A boundary-avoiding switch fixes every boundary colour. -/
theorem apply_eq_of_mem (h : G.KempeStepAvoiding B C C') {v : V} (hv : v ∈ B) :
    C' v = C v := by
  obtain ⟨a, b, K, hK, rfl⟩ := h
  exact C.swapOnKempeComponent_apply_of_not_mem (Set.disjoint_right.1 hK hv)

theorem boundaryWord_eq (h : G.KempeStepAvoiding B C C') :
    C'.boundaryWord B = C.boundaryWord B :=
  Coloring.boundaryWord_eq_iff.2 fun _ hv => h.apply_eq_of_mem hv

/-- Boundary-avoiding switches are reversible by boundary-avoiding switches. -/
theorem symm (h : G.KempeStepAvoiding B C C') : G.KempeStepAvoiding B C' C := by
  obtain ⟨a, b, K, hK, rfl⟩ := h
  obtain ⟨L, hL, hinv⟩ := C.exists_swapOnKempeComponent_inverse a b K
  exact ⟨a, b, L, hL ▸ hK, hinv.symm⟩

end KempeStepAvoiding

theorem kempeStepAvoiding_empty :
    G.KempeStepAvoiding (∅ : Set V) = (G.KempeStep : G.Coloring α → G.Coloring α → Prop) := by
  funext C C'
  apply propext
  constructor
  · exact KempeStepAvoiding.kempeStep
  · rintro ⟨a, b, K, rfl⟩
    exact ⟨a, b, K, Set.disjoint_empty _, rfl⟩

theorem reflTransGen_kempeStepAvoiding_boundaryWord {B : Set V} {C C' : G.Coloring α}
    (h : ReflTransGen (G.KempeStepAvoiding B) C C') :
    C'.boundaryWord B = C.boundaryWord B := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact hstep.boundaryWord_eq.trans ih

theorem reflTransGen_kempeStepAvoiding_symm {B : Set V} {C C' : G.Coloring α}
    (h : ReflTransGen (G.KempeStepAvoiding B) C C') :
    ReflTransGen (G.KempeStepAvoiding B) C' C :=
  Mettapedia.GraphTheory.ReflTransGen.reverse_of_symmetric
    (fun _ _ hstep => KempeStepAvoiding.symm hstep) h

/-- **LKR_in**: colourings with the same word on `B` are joined by Kempe
switches avoiding `B`. -/
def FibreConnected (G : SimpleGraph V) (α : Type*) [DecidableEq α] (B : Set V) : Prop :=
  FibresConnected (G.KempeStepAvoiding (α := α) B) (fun C => C.boundaryWord B)

/-- LKR_in as connectivity of the Kempe graph on each fibre: the vertices are
the colourings with a given word, the edges the boundary-avoiding switches. -/
theorem fibreConnected_iff_fibre {B : Set V} :
    G.FibreConnected α B ↔
      ∀ c : B → α, ∀ x y : boundaryFibre G B c,
        ReflTransGen (fun x y : boundaryFibre G B c => G.KempeStepAvoiding B x.1 y.1) x y := by
  have hclosed : ∀ c : B → α, ∀ x y : G.Coloring α, x ∈ boundaryFibre G B c →
      G.KempeStepAvoiding B x y → y ∈ boundaryFibre G B c :=
    fun _ _ _ hx hxy => hxy.boundaryWord_eq.trans hx
  constructor
  · intro h c x y
    exact (reflTransGen_subtype_iff (S := (· ∈ boundaryFibre G B c)) (hclosed c) x y).2
      (h x.1 y.1 (x.2.trans y.2.symm))
  · intro h x y hxy
    exact (reflTransGen_subtype_iff (S := (· ∈ boundaryFibre G B (x.boundaryWord B)))
      (hclosed _) ⟨x, rfl⟩ ⟨y, hxy.symm⟩).1 (h _ _ _)

/-- With the empty boundary, LKR_in says that all colourings form one Kempe
class. -/
theorem fibreConnected_empty_iff :
    G.FibreConnected α ∅ ↔
      Mettapedia.Combinatorics.Reconfiguration.Connected
        (G.KempeStep : G.Coloring α → G.Coloring α → Prop) := by
  rw [FibreConnected, kempeStepAvoiding_empty]
  constructor
  · intro h x y
    exact h x y (funext fun v => absurd v.2 (Set.notMem_empty _))
  · intro h
    exact h.fibresConnected _

/-- **WC***: from every colouring, some colouring whose word on `∂` lies in `W`
is reachable by Kempe switches, provided such a colouring exists. -/
def WeaklyCompletable (G : SimpleGraph V) (α : Type*) [DecidableEq α] (bdry : Set V)
    (W : Set (bdry → α)) : Prop :=
  Mettapedia.Combinatorics.Reconfiguration.WeaklyCompletable
    (G.KempeStep : G.Coloring α → G.Coloring α → Prop) {C | C.boundaryWord bdry ∈ W}

/-- A single Kempe class gives WC* for every boundary and every word set. -/
theorem weaklyCompletable_of_fibreConnected_empty (h : G.FibreConnected α ∅)
    (bdry : Set V) (W : Set (bdry → α)) : G.WeaklyCompletable α bdry W :=
  (fibreConnected_empty_iff.1 h).weaklyCompletable

/-- LKR_in relative to a set of fixed stubs, with every fibre meeting the target
words, gives WC* with the fixed stubs never moved. -/
theorem completable_of_fibreConnected {B bdry : Set V} {W : Set (bdry → α)}
    (h : G.FibreConnected α B)
    (hmeet : ∀ C : G.Coloring α, ∃ D : G.Coloring α,
      D.boundaryWord bdry ∈ W ∧ D.boundaryWord B = C.boundaryWord B) :
    Completable (G.KempeStepAvoiding B) {C : G.Coloring α | C.boundaryWord bdry ∈ W} :=
  FibresConnected.completable h hmeet

/-! ### Edge colourings -/

/-- A Kempe switch of an edge colouring avoiding a set of edges. -/
abbrev EdgeKempeStepAvoiding (G : SimpleGraph V) (B : Set G.edgeSet) :
    G.EdgeColoring α → G.EdgeColoring α → Prop :=
  G.lineGraph.KempeStepAvoiding B

/-- LKR_in for edge colourings with a fixed set of boundary edges. -/
abbrev EdgeFibreConnected (G : SimpleGraph V) (α : Type*) [DecidableEq α]
    (B : Set G.edgeSet) : Prop :=
  G.lineGraph.FibreConnected α B

/-- WC* for edge colourings with boundary edges `∂`. -/
abbrev EdgeWeaklyCompletable (G : SimpleGraph V) (α : Type*) [DecidableEq α]
    (bdry : Set G.edgeSet) (W : Set (bdry → α)) : Prop :=
  G.lineGraph.WeaklyCompletable α bdry W

end Avoiding

/-! ### Transparency -/

section Transparency

namespace Coloring

variable [DecidableEq α]

theorem swapOnKempeComponent_self (C : G.Coloring α) (a : α)
    (K : (C.bicoloredSubgraph a a).ConnectedComponent) :
    C.swapOnKempeComponent a a K = C := by
  ext v
  by_cases hv : v ∈ C.kempeComponentSet a a K
  · rw [C.swapOnKempeComponent_apply_of_mem hv]
    simp
  · rw [C.swapOnKempeComponent_apply_of_not_mem hv]

/-- **A transparent colouring is frozen** under switches avoiding any superset of
the transparency boundary. -/
theorem IsTransparent.eq_of_kempeStepAvoiding {C C' : G.Coloring α} {bdry B : Set V}
    (hC : C.IsTransparent bdry) (hsub : bdry ⊆ B) (h : G.KempeStepAvoiding B C C') :
    C' = C := by
  obtain ⟨a, b, K, hK, rfl⟩ := h
  by_cases hab : a = b
  · subst hab
    exact C.swapOnKempeComponent_self a K
  · obtain ⟨v, hvK, hv⟩ := hC a b hab K
    exact absurd (hsub hv) (Set.disjoint_left.1 hK hvK)

theorem IsTransparent.eq_of_reflTransGen {C C' : G.Coloring α} {bdry B : Set V}
    (hC : C.IsTransparent bdry) (hsub : bdry ⊆ B)
    (h : ReflTransGen (G.KempeStepAvoiding B) C C') : C' = C := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
      subst ih
      exact hC.eq_of_kempeStepAvoiding hsub hstep

/-- **Every nontrivial switch of a transparent colouring shows on the
boundary.** -/
theorem IsTransparent.boundaryWord_swap_ne {C : G.Coloring α} {bdry : Set V}
    (hC : C.IsTransparent bdry) {a b : α} (hab : a ≠ b)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent) :
    (C.swapOnKempeComponent a b K).boundaryWord bdry ≠ C.boundaryWord bdry := by
  intro h
  obtain ⟨v, hvK, hv⟩ := hC a b hab K
  have hcol := boundaryWord_eq_iff.1 h v hv
  rw [C.swapOnKempeComponent_apply_of_mem hvK] at hcol
  rcases C.mem_bicoloredSet_of_mem_kempeComponentSet hvK with hva | hvb
  · rw [hva, Equiv.swap_apply_left] at hcol
    exact hab (hcol.symm)
  · rw [hvb, Equiv.swap_apply_right] at hcol
    exact hab hcol

end Coloring

variable [DecidableEq α]

/-- For a transparent graph, LKR_in relative to the transparency boundary holds
exactly when the boundary word determines the colouring. -/
theorem Transparent.fibreConnected_iff {bdry : Set V} (hT : G.Transparent α bdry) :
    G.FibreConnected α bdry ↔
      ∀ C D : G.Coloring α, C.boundaryWord bdry = D.boundaryWord bdry → C = D := by
  constructor
  · intro h C D hCD
    exact ((hT C).eq_of_reflTransGen subset_rfl (h C D hCD)).symm
  · intro h C D hCD
    rw [h C D hCD]

omit [DecidableEq α] in
/-- **The tree argument of Lemma 8.15, in general form.**  If every two-colour
subgraph of `C` is acyclic, and every two-coloured vertex off `∂` has two
distinct two-coloured neighbours, then `C` is transparent relative to `∂`:
a finite tree has a vertex of degree at most one, which must lie on `∂`. -/
theorem Coloring.isTransparent_of_isAcyclic [Finite V] (C : G.Coloring α) (bdry : Set V)
    (hacyclic : ∀ a b, a ≠ b → (C.bicoloredSubgraph a b).IsAcyclic)
    (hdeg : ∀ a b, a ≠ b → ∀ v : C.bicoloredSet a b, v.1 ∉ bdry →
      ∃ u w, u ≠ w ∧ (C.bicoloredSubgraph a b).Adj v u ∧ (C.bicoloredSubgraph a b).Adj v w) :
    C.IsTransparent bdry := by
  classical
  intro a b hab K
  by_contra hempty
  rw [Set.not_nonempty_iff_eq_empty] at hempty
  let H := C.bicoloredSubgraph a b
  have hoff : ∀ v : K.supp, v.1.1 ∉ bdry := by
    intro v hv
    have hmem : v.1.1 ∈ C.kempeComponentSet a b K := ⟨v.1.2, v.2⟩
    have : v.1.1 ∈ C.kempeComponentSet a b K ∩ bdry := ⟨hmem, hv⟩
    rw [hempty] at this
    exact this
  have htree : K.toSimpleGraph.IsTree :=
    ⟨K.connected_toSimpleGraph,
      (hacyclic a b hab).comap K.toSimpleGraph_hom Subtype.val_injective⟩
  haveI : Fintype K.supp := Fintype.ofFinite _
  -- every vertex of the component has two distinct neighbours inside it
  have htwo : ∀ v : K.supp, 2 ≤ K.toSimpleGraph.degree v := by
    intro v
    obtain ⟨u, w, huw, hu, hw⟩ := hdeg a b hab v.1 (hoff v)
    have hu' : u ∈ K.supp := (K.mem_supp_congr_adj hu).1 v.2
    have hw' : w ∈ K.supp := (K.mem_supp_congr_adj hw).1 v.2
    rw [← card_neighborFinset_eq_degree]
    apply Finset.one_lt_card.2
    refine ⟨⟨u, hu'⟩, ?_, ⟨w, hw'⟩, ?_, ?_⟩
    · rw [mem_neighborFinset]; exact hu
    · rw [mem_neighborFinset]; exact hw
    · intro h; exact huw (congrArg Subtype.val h)
  obtain ⟨v₀⟩ := K.connected_toSimpleGraph.nonempty
  obtain ⟨u, w, huw, hu, -⟩ := hdeg a b hab v₀.1 (hoff v₀)
  have hu' : u ∈ K.supp := (K.mem_supp_congr_adj hu).1 v₀.2
  haveI : Nontrivial K.supp := ⟨⟨v₀, ⟨u, hu'⟩, fun h => hu.ne (congrArg Subtype.val h)⟩⟩
  have hmin := htree.minDegree_eq_one_of_nontrivial
  have hle : 2 ≤ K.toSimpleGraph.minDegree :=
    K.toSimpleGraph.le_minDegree_of_forall_le_degree 2 htwo
  omega

end Transparency

end SimpleGraph
