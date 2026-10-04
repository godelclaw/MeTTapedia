import Mettapedia.GraphTheory.FourColor.KempeChainCertificate

/-! # Independent physical switches on separated chains

Two saturated chains with no common vertex or edge between them remain
actual components after either is switched. Their physical switches commute,
and both construction orders retain a two-step GSLT history. The graph,
palette and chain lengths are unrestricted.
-/

namespace SimpleGraph.KempeSeparatedChains

open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq V] [DecidableEq α]

/-- A finite connected certificate for a complete physical component.
Repeated vertices in the chain allow branching supports. -/
structure Certificate (C : G.Coloring α) (a b : α) where
  vertices : List V
  root : V
  root_mem : root ∈ vertices
  connected : vertices.IsChain G.Adj
  active : ∀ x ∈ vertices, C x = a ∨ C x = b
  closed : ∀ x ∈ vertices, ∀ y, G.Adj x y → (C y = a ∨ C y = b) → y ∈ vertices

namespace Certificate

variable {C : G.Coloring α} {a b c d : α}

def component (S : Certificate C a b) : (C.bicoloredSubgraph a b).ConnectedComponent :=
  (C.bicoloredSubgraph a b).connectedComponentMk ⟨S.root, S.active _ S.root_mem⟩

omit [DecidableEq V] [DecidableEq α] in
theorem component_mem (S : Certificate C a b) (x : V) :
    x ∈ C.kempeComponentSet a b S.component ↔ x ∈ S.vertices :=
  C.kempe_component_iff_mem_chain a b S.component S.vertices S.connected S.active S.closed
    S.root_mem (C.mem_kempeComponentSet_self (S.active _ S.root_mem)) x

noncomputable def swap (S : Certificate C a b) : G.Coloring α :=
  C.swapOnKempeComponent a b S.component

theorem swap_apply (S : Certificate C a b) (x : V) :
    S.swap x = if x ∈ S.vertices then Equiv.swap a b (C x) else C x :=
  C.swap_apply_of_chain a b S.component S.vertices S.connected S.active S.closed
    S.root_mem (C.mem_kempeComponentSet_self (S.active _ S.root_mem)) x

noncomputable def step (S : Certificate C a b) : Step C S.swap :=
  .switch C a b S.component

/-- Separation preserves every colour inspected by the second component's
closure test. Thus the second command remains an actual physical switch. -/
noncomputable def after (S : Certificate C a b) (T : Certificate C c d)
    (apart : ∀ x ∈ S.vertices, x ∉ T.vertices)
    (noEdge : ∀ x ∈ S.vertices, ∀ y ∈ T.vertices, ¬ G.Adj x y) :
    Certificate S.swap c d where
  vertices := T.vertices
  root := T.root
  root_mem := T.root_mem
  connected := T.connected
  active := by
    intro x hx
    have outside : x ∉ S.vertices := fun hs => apart x hs hx
    simpa only [swap_apply, ite_eq_right outside] using T.active x hx
  closed := by
    intro x hx y edge active
    have outside : y ∉ S.vertices := fun hs => noEdge y hs x hx edge.symm
    apply T.closed x hx y edge
    simpa only [swap_apply, ite_eq_right outside] using active

noncomputable def history (S : Certificate C a b) (T : Certificate C c d)
    (apart : ∀ x ∈ S.vertices, x ∉ T.vertices)
    (noEdge : ∀ x ∈ S.vertices, ∀ y ∈ T.vertices, ¬ G.Adj x y) :
    History C (S.after T apart noEdge).swap :=
  .cons S.step (.cons (S.after T apart noEdge).step (.refl _))

theorem history_length (S : Certificate C a b) (T : Certificate C c d)
    (apart : ∀ x ∈ S.vertices, x ∉ T.vertices)
    (noEdge : ∀ x ∈ S.vertices, ∀ y ∈ T.vertices, ¬ G.Adj x y) :
    (S.history T apart noEdge).length = 2 := rfl

/-- Independent local repairs have the same endpoint in either order,
even when their colour pairs overlap. -/
theorem commute (S : Certificate C a b) (T : Certificate C c d)
    (apart : ∀ x ∈ S.vertices, x ∉ T.vertices)
    (noEdge : ∀ x ∈ S.vertices, ∀ y ∈ T.vertices, ¬ G.Adj x y) :
    (S.after T apart noEdge).swap =
      (T.after S (fun x hx hs => apart x hs hx)
        (fun x hx y hy edge => noEdge y hy x hx edge.symm)).swap := by
  ext x
  simp only [swap_apply, after]
  by_cases hs : x ∈ S.vertices
  · simp only [ite_eq_left hs, ite_eq_right (apart x hs)]
  · by_cases ht : x ∈ T.vertices <;> simp [hs, ht]

theorem fixed_outside (S : Certificate C a b) (T : Certificate C c d)
    (apart : ∀ x ∈ S.vertices, x ∉ T.vertices)
    (noEdge : ∀ x ∈ S.vertices, ∀ y ∈ T.vertices, ¬ G.Adj x y)
    (x : V) (hs : x ∉ S.vertices) (ht : x ∉ T.vertices) :
    S.swap x = C x ∧ (S.after T apart noEdge).swap x = C x := by
  constructor
  · simp only [swap_apply, ite_eq_right hs]
  · rw [swap_apply]
    change (if x ∈ T.vertices then _ else _) = _
    simp only [ite_eq_right ht, swap_apply, ite_eq_right hs]

end Certificate
end SimpleGraph.KempeSeparatedChains
