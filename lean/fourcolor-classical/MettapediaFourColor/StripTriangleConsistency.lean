import MettapediaFourColor.StripSourceExtension

/-!
# Triangle support and compatible strip composition

The decoded D0099 core has six triangles. A nonempty set of colours at each
vertex can support every colour on every incident triangle and still have no
global colouring. The example below survives arbitrary repetition of this
local support test: the displayed domains already satisfy all its constraints.

The two halves instead compose through their common ordered pair of colours.
The equivalence is uniform in the boundary; the counterexample makes the two
halves disagree at a shared vertex. Boundary recolouring remains possible and
is not ruled out by the fixed-boundary obstruction.
-/

namespace FourColor.StripTriangleConsistency

open Color TriangleStripAnchors StripResponseSummary StripSourceExtension

def right0 (b : Boundary) :=
  join (unary b 5) (unary b 6) (unary b 7) (· ≠ ·) (· ≠ ·)
def right1 (b : Boundary) :=
  join (unary b 2) (unary b 6) (unary b 5) (· ≠ ·) (right0 b)
def right2 (b : Boundary) :=
  join (unary b 2) (unary b 4) (unary b 6) (right1 b) (· ≠ ·)

instance (b : Boundary) : DecidableRel (right0 b) := by unfold right0; infer_instance
instance (b : Boundary) : DecidableRel (right1 b) := by unfold right1; infer_instance
instance (b : Boundary) : DecidableRel (right2 b) := by unfold right2; infer_instance

/-- Both halves retain the same colours at core vertices 2 and 4. -/
theorem compose_iff (b : Boundary) :
    (∃ a c, r2 b a c ∧ right2 b a c) ↔ ∃ f, ValidCore b f := by
  constructor
  · rintro ⟨a2,a4,hL,hR⟩
    rcases hL with ⟨h2,h4,h24,a1,h1,hL1,h14⟩
    rcases hL1 with ⟨_,_,h12,a3,h3,hL0,h32⟩
    rcases hL0 with ⟨_,_,h13,a0,h0,h10,h03⟩
    rcases hR with ⟨_,_,_,a6,h6,hR1,h64⟩
    rcases hR1 with ⟨_,_,h26,a5,h5,h25,hR0⟩
    rcases hR0 with ⟨_,_,h56,a7,h7,h57,h76⟩
    refine ⟨![a0,a1,a2,a3,a4,a5,a6,a7], ?_⟩
    simp [ValidCore, edges, Fin.forall_fin_succ, h0,h1,h2,h3,h4,h5,h6,h7,
      h24,h14,h12,h32.symm,h13,h10,h03,h64.symm,h26,h25,h56,h57,h76.symm, ne_comm]
  · rintro ⟨f,hU,hE⟩
    have e {i j : Fin 8} (h : (i,j) ∈ edges) : f i ≠ f j := hE _ h
    refine ⟨f 2, f 4, ?_, ?_⟩
    · refine ⟨hU 2,hU 4,e (by decide),f 1,hU 1,?_,e (by decide)⟩
      refine ⟨hU 1,hU 2,e (by decide),f 3,hU 3,?_,
        (e (i := 2) (j := 3) (by decide)).symm⟩
      exact ⟨hU 1,hU 3,e (by decide),f 0,hU 0,
        (e (i := 0) (j := 1) (by decide)).symm,e (by decide)⟩
    · refine ⟨hU 2,hU 4,e (by decide),f 6,hU 6,?_,
        (e (i := 4) (j := 6) (by decide)).symm⟩
      refine ⟨hU 2,hU 6,e (by decide),f 5,hU 5,e (by decide),?_⟩
      exact ⟨hU 5,hU 6,e (by decide),f 7,hU 7,e (by decide),
        (e (i := 6) (j := 7) (by decide)).symm⟩

/-- Compatible composed halves reconstruct a genuine colouring of the source. -/
theorem source_iff (b : Boundary) (hb : ProperBoundary b) :
    (∃ a c, r2 b a c ∧ right2 b a c) ↔
      ∃ k : input0099.graph.Coloring Color, ∀ i, k (port i) = b i := by
  constructor
  · intro h
    obtain ⟨f,hf⟩ := (compose_iff b).mp h
    exact ⟨colouring b f hb hf, fun i => colour_port b f i⟩
  · rintro ⟨k,hk⟩
    exact (compose_iff b).mpr ⟨_,valid_of_colouring b k hk⟩

def boundary : Boundary := ![c0,c1,c3,c1,c0,c2,c0,c3,c0,c3,c2]

def domains : Fin 8 → Finset Color :=
  ![{c1,c2},{c1,c2,c3},{c2,c3},{c1,c3},{c1,c2},{c0,c2},{c0,c1},{c3}]

def triangles : Fin 6 → Fin 3 → Fin 8 :=
  ![![0,1,3],![1,2,3],![1,2,4],![2,4,6],![2,5,6],![5,6,7]]

/-- Every retained colour has a witness on every incident core triangle. -/
def Supported (D : Fin 8 → Finset Color) : Prop :=
  ∀ t j c, c ∈ D (triangles t j) → ∃ f : Fin 3 → Color,
    (∀ i, f i ∈ D (triangles t i)) ∧ Function.Injective f ∧ f j = c

instance (D : Fin 8 → Finset Color) : Decidable (Supported D) := by
  unfold Supported Function.Injective
  infer_instance

theorem proper : ProperBoundary boundary := by decide +kernel

theorem triangle_edges : ∀ t (i j : Fin 3), i ≠ j →
    (triangles t i, triangles t j) ∈ edges ∨
      (triangles t j, triangles t i) ∈ edges := by decide +kernel

theorem all_edges_covered : ∀ e ∈ edges, ∃ (t : Fin 6) (i j : Fin 3),
    triangles t i = e.1 ∧ triangles t j = e.2 := by decide +kernel

private theorem triangle_cover_checked : (List.finRange 8).all (fun u =>
    (List.finRange 8).all (fun v => (List.finRange 8).all (fun w =>
      !decide (u < v ∧ v < w ∧ (u,v) ∈ edges ∧ (u,w) ∈ edges ∧ (v,w) ∈ edges) ||
      (List.finRange 6).any (fun t => decide
        (triangles t 0 = u ∧ triangles t 1 = v ∧ triangles t 2 = w))))) = true := by
  decide +kernel

theorem triangles_complete : ∀ (u v w : Fin 8), u < v → v < w →
    (u,v) ∈ edges → (u,w) ∈ edges → (v,w) ∈ edges →
    ∃ t, triangles t 0 = u ∧ triangles t 1 = v ∧ triangles t 2 = w := by
  intro u v w huv hvw he1 he2 he3
  have hc := List.all_eq_true.mp triangle_cover_checked u (List.mem_finRange u)
  have hc := List.all_eq_true.mp hc v (List.mem_finRange v)
  have hc := List.all_eq_true.mp hc w (List.mem_finRange w)
  simp only [huv,hvw,he1,he2,he3,and_self,decide_true,Bool.not_true,Bool.false_or] at hc
  obtain ⟨t,_,ht⟩ := List.any_eq_true.mp hc
  exact ⟨t,of_decide_eq_true ht⟩

/-- These domains result from excluding the forced colour at vertex 7
from its neighbours. No extension-compatible colour is discarded. -/
theorem domains_exact : ∀ v c, c ∈ domains v ↔
    unary boundary v c ∧
      (((v,7) ∈ edges ∨ (7,v) ∈ edges) → c ≠ c3) := by decide +kernel

theorem domains_sound (f : Fin 8 → Color) (hf : ValidCore boundary f) :
    ∀ v, f v ∈ domains v := by
  have pin : ∀ c, unary boundary 7 c → c = c3 := by decide +kernel
  have h7 := pin _ (hf.1 7)
  intro v
  refine (domains_exact v (f v)).mpr ⟨hf.1 v,?_⟩
  rintro (h | h)
  · simpa only [h7] using hf.2 (v,7) h
  · simpa only [h7] using (hf.2 (7,v) h).symm

theorem nonempty_domains : ∀ v, (domains v).Nonempty := by decide +kernel
theorem supported_domains : Supported domains := by decide +kernel

/-- The two composed halves require incompatible colours at their common vertex. -/
theorem left_pin : ∀ a c, r2 boundary a c → a = c2 := by decide +kernel
theorem right_pin : ∀ a c, right2 boundary a c → a = c3 := by decide +kernel
theorem left_nonempty : ∃ a c, r2 boundary a c := by decide +kernel
theorem right_nonempty : ∃ a c, right2 boundary a c := by decide +kernel

theorem no_core : ¬ ∃ f, ValidCore boundary f := by
  intro h
  obtain ⟨a,c,hL,hR⟩ := (compose_iff boundary).mpr h
  have impossible : c2 = c3 := (left_pin a c hL).symm.trans (right_pin a c hR)
  cases impossible

theorem no_source : ¬ ∃ k : input0099.graph.Coloring Color,
    ∀ i, k (port i) = boundary i := by
  rintro ⟨k,hk⟩
  exact no_core ⟨_,valid_of_colouring boundary k hk⟩

/-- Nonempty domains at a fixed point of triangle support do not suffice
for source extension, even after the forced endpoint colour is propagated. -/
theorem local_support_not_sufficient : ¬ (∀ b : Boundary,
    ProperBoundary b → ∀ D : Fin 8 → Finset Color,
    (∀ v, (D v).Nonempty) → (∀ v c, c ∈ D v → unary b v c) →
    Supported D → ∃ k : input0099.graph.Coloring Color,
      ∀ i, k (port i) = b i) := by
  intro h
  exact no_source (h boundary proper domains nonempty_domains
    (fun v c hc => ((domains_exact v c).mp hc).1) supported_domains)

end FourColor.StripTriangleConsistency
