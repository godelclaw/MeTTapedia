import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Rel

open Relation

namespace SimpleGraph

variable {α : Type*} (G : SimpleGraph α)

/-- If a relation `R` is pointwise contained in adjacency, any reflexive-transitive `R` path
has at least one corresponding graph walk. -/
theorem exists_walk_of_rflTransGen_subrel {R : α → α → Prop} {u v : α}
    (hR : ∀ {x y}, R x y → G.Adj x y)
    (h : ReflTransGen R u v) : Nonempty (G.Walk u v) := by
  induction h with
  | refl =>
      exact ⟨Walk.nil⟩
  | tail _ hab ih =>
      rcases ih with ⟨w⟩
      exact ⟨w.concat (hR hab)⟩

/-- Chosen walk associated to a reflexive-transitive relation path whose steps refine
adjacency. -/
noncomputable def walk_of_rflTransGen_subrel {R : α → α → Prop} {u v : α}
    (hR : ∀ {x y}, R x y → G.Adj x y)
    (h : ReflTransGen R u v) : G.Walk u v :=
  Classical.choice (G.exists_walk_of_rflTransGen_subrel hR h)

/-- Specialization of `exists_walk_of_rflTransGen_subrel` to adjacency itself. -/
theorem exists_walk_of_rflTransGen_adj {u v : α}
    (h : ReflTransGen G.Adj u v) : Nonempty (G.Walk u v) :=
  G.exists_walk_of_rflTransGen_subrel (fun {_ _} hxy => hxy) h

/-- Chosen walk associated to a reflexive-transitive adjacency path. -/
noncomputable def walk_of_rflTransGen_adj {u v : α}
    (h : ReflTransGen G.Adj u v) : G.Walk u v :=
  G.walk_of_rflTransGen_subrel (fun {_ _} hxy => hxy) h

/-- The induced-subgraph version of `exists_walk_of_rflTransGen_subrel`. -/
theorem exists_walk_of_rflTransGen_subrel_induce {s : Set α}
    {R : {x // x ∈ s} → {x // x ∈ s} → Prop}
    {u v : {x // x ∈ s}}
    (hR : ∀ {x y}, R x y → (G.induce s).Adj x y)
    (h : ReflTransGen R u v) : Nonempty ((G.induce s).Walk u v) :=
  (G.induce s).exists_walk_of_rflTransGen_subrel hR h

/-- Chosen induced-subgraph walk associated to a reflexive-transitive relation path. -/
noncomputable def walk_of_rflTransGen_subrel_induce {s : Set α}
    {R : {x // x ∈ s} → {x // x ∈ s} → Prop}
    {u v : {x // x ∈ s}}
    (hR : ∀ {x y}, R x y → (G.induce s).Adj x y)
    (h : ReflTransGen R u v) : (G.induce s).Walk u v :=
  (G.induce s).walk_of_rflTransGen_subrel hR h

/-- In an acyclic graph, every edge is a bridge of that graph. -/
theorem edge_is_bridge_in_forest [DecidableEq α]
    (hacyc : G.IsAcyclic) {u v : α} (huv : G.Adj u v) :
    G.IsBridge s(u, v) := by
  rw [SimpleGraph.isAcyclic_iff_forall_adj_isBridge] at hacyc
  exact hacyc huv

end SimpleGraph
