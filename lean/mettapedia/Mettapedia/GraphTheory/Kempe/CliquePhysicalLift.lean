import Mettapedia.GraphTheory.Kempe.CliqueLift
import Mettapedia.GraphTheory.FourColor.KempeChainCertificate

/-!
# Clique attachments preserve physical switch counts

A hidden patch attached only along a retained clique cannot connect two
different retained components of a two-colour subgraph. A retained
component therefore lifts to one actual component, and a retained history
lifts with exactly the same number of physical switches. No finiteness or
bound on the hidden patch is required. The full initial colouring is given.
-/

namespace SimpleGraph.KempeCliquePhysicalLift

open Mettapedia.GraphTheory.FourColor.KempeChainCertificate
open Mettapedia.GSLT.Ultrainfinite

variable {V α : Type*} {G : SimpleGraph V} [DecidableEq α]
  (X N : Set V) (clique : G.IsClique N)
  (attachment : ∀ x, x ∉ X → ∀ y ∈ X, G.Adj x y → y ∈ N)

include clique attachment

omit [DecidableEq α] in
/-- The full component through a retained root has exactly the original
component as its retained vertices. -/
theorem component_restriction (C : G.Coloring α) (a b : α) (r : X)
    (active : C r = a ∨ C r = b) :
    ∀ v : X,
      v.val ∈ C.kempeComponentSet a b
        ((C.bicoloredSubgraph a b).connectedComponentMk ⟨r.val, active⟩) ↔
      v ∈ (C.restrictInduce X).kempeComponentSet a b
        (((C.restrictInduce X).bicoloredSubgraph a b).connectedComponentMk ⟨r, active⟩) := by
  classical
  let K := ((C.restrictInduce X).bicoloredSubgraph a b).connectedComponentMk ⟨r, active⟩
  let L := (C.bicoloredSubgraph a b).connectedComponentMk ⟨r.val, active⟩
  let S : Set V := {x | (∃ hx : x ∈ X, ⟨x,hx⟩ ∈ (C.restrictInduce X).kempeComponentSet a b K) ∨
    (x ∉ X ∧ ∃ n : X, n.val ∈ N ∧ n ∈ (C.restrictInduce X).kempeComponentSet a b K)}
  have start : r.val ∈ S := Or.inl ⟨r.property,
    (C.restrictInduce X).mem_kempeComponentSet_self active⟩
  have closed : ∀ x ∈ S, ∀ y, G.Adj x y → (C y = a ∨ C y = b) → y ∈ S := by
    intro x hx y edge hy
    rcases hx with ⟨hx, hk⟩ | ⟨hx, n, hn, hk⟩
    · by_cases yX : y ∈ X
      · exact Or.inl ⟨yX, (C.restrictInduce X).mem_kempeComponentSet_of_adj hk edge hy⟩
      · exact Or.inr ⟨yX, ⟨x,hx⟩, attachment y yX x hx edge.symm, hk⟩
    · by_cases yX : y ∈ X
      · have yN := attachment x hx y yX edge
        refine Or.inl ⟨yX, ?_⟩
        by_cases same : n.val = y
        · have equal : n = (⟨y,yX⟩ : X) := Subtype.ext same
          exact equal ▸ hk
        · exact (C.restrictInduce X).mem_kempeComponentSet_of_adj hk
            (clique hn yN same) hy
      · exact Or.inr ⟨yX, n, hn, hk⟩
  have upper := C.kempeComponentSet_subset_of_closed active start (fun x y hx edge hy => closed x hx y edge hy)
  have lower := (C.restrictInduce X).kempeComponentSet_subset_of_closed active
    (show r.val ∈ C.kempeComponentSet a b L from C.mem_kempeComponentSet_self active)
    (fun x y hx edge hy => C.mem_kempeComponentSet_of_adj hx edge hy)
  intro v
  constructor
  · intro hv
    rcases upper hv with ⟨_, hk⟩ | ⟨outside, _⟩
    · exact hk
    · exact (outside v.property).elim
  · exact fun hv => lower hv

/-- One retained physical switch lifts to exactly one full physical switch. -/
theorem step_lifts (C : G.Coloring α) {D : (G.induce X).Coloring α}
    (step : Step (C.restrictInduce X) D) :
    ∃ E : G.Coloring α, Nonempty (Step C E) ∧ E.restrictInduce X = D := by
  cases step with
  | switch a b K =>
      obtain ⟨r, active, rfl⟩ := (C.restrictInduce X).exists_eq_mk_of_kempeComponent K
      let L := (C.bicoloredSubgraph a b).connectedComponentMk ⟨r.val, active⟩
      refine ⟨C.swapOnKempeComponent a b L, ⟨.switch C a b L⟩, ?_⟩
      exact C.restrictInduce_swapOnKempeComponent X L _
        (component_restriction X N clique attachment C a b r active)

/-- Every retained history lifts from the supplied full starting colouring,
with exactly the same length. Hidden endpoints are constructed, not prescribed. -/
theorem history_lifts {C D : (G.induce X).Coloring α} (history : History C D)
    (start : G.Coloring α) (initial : start.restrictInduce X = C) :
    ∃ finish : G.Coloring α, ∃ lifted : History start finish,
      finish.restrictInduce X = D ∧ lifted.length = history.length := by
  induction history generalizing start with
  | refl => exact ⟨start, .refl _, initial, rfl⟩
  | cons step rest ih =>
      cases initial
      obtain ⟨middle, ⟨first⟩, aligned⟩ := step_lifts X N clique attachment start step
      obtain ⟨finish, tail, final, length⟩ := ih middle aligned
      exact ⟨finish, .cons first tail, final, by simpa only [Route.length] using congrArg (· + 1) length⟩

end SimpleGraph.KempeCliquePhysicalLift
