import Mathlib.Tactic

/-!
# Scoped loans during graph transport

The reference copies a finite labelled graph into the destination. The loan
algorithm can retain a closed graph in an explicitly live source arena. It
preserves labels, edge order and duplicate occurrences, while the destination
may remain open over the borrowed arena. Reclamation excludes that arena.

A later transport without loans materializes the graph before source storage is
released. C pointer sharing, closure-bit construction, identity-bearing payloads,
update-cell resolution and native lifetime guards remain correspondence duties.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.ScopedGraphLoan

inductive Graph (A : Type) where
  | node (home : Nat) (label : A) (children : List (Graph A))

inductive View (A : Type) where
  | node (label : A) (children : List (View A))

variable {A : Type}

def Graph.home : Graph A → Nat
  | .node home _ _ => home

mutual
def image : Graph A → View A
  | .node _ label children => .node label (images children)
def images : List (Graph A) → List (View A)
  | [] => []
  | first :: later => image first :: images later
end

theorem images_eq_map (graphs : List (Graph A)) : images graphs = graphs.map image := by
  induction graphs with
  | nil => rfl
  | cons first later ih => simp only [images, List.map_cons, ih]

mutual
/-- Zero names immutable global storage; other homes name arenas. -/
def closedAt (owner : Nat) : Graph A → Bool
  | .node home _ children => (home == 0 || home == owner) && closedChildren owner children
def closedChildren (owner : Nat) : List (Graph A) → Bool
  | [] => true
  | first :: later => closedAt owner first && closedChildren owner later
end

theorem closedChildren_eq_all (owner : Nat) (graphs : List (Graph A)) :
    closedChildren owner graphs = graphs.all (closedAt owner) := by
  induction graphs with
  | nil => rfl
  | cons first later ih => simp only [closedChildren, List.all_cons, ih]

mutual
def transport (destination : Nat) (loans : List Nat) : Graph A → Graph A
  | graph@(.node home label children) =>
      if home ≠ 0 ∧ home ∈ loans ∧ closedAt home graph = true then graph
      else .node destination label (transportChildren destination loans children)
def transportChildren (destination : Nat) (loans : List Nat) :
    List (Graph A) → List (Graph A)
  | [] => []
  | first :: later => transport destination loans first :: transportChildren destination loans later
end

theorem transportChildren_eq_map (destination : Nat) (loans : List Nat)
    (graphs : List (Graph A)) :
    transportChildren destination loans graphs = graphs.map (transport destination loans) := by
  induction graphs with
  | nil => rfl
  | cons first later ih => simp only [transportChildren, List.map_cons, ih]

theorem transport_preserves_values (destination : Nat) (loans : List Nat) (graph : Graph A) :
    image (transport destination loans graph) = image graph := by
  refine Graph.rec
    (motive_1 := fun graph => image (transport destination loans graph) = image graph)
    (motive_2 := fun graphs => ∀ graph ∈ graphs,
      image (transport destination loans graph) = image graph) ?_ ?_ ?_ graph
  · intro home label children ih
    rw [transport]
    split
    · rfl
    · simp only [image, images_eq_map, transportChildren_eq_map, List.map_map]
      congr 1
      exact List.map_congr_left ih
  · intro graph member
    cases member
  · intro first later ihFirst ihLater graph member
    rcases List.mem_cons.mp member with rfl | member
    · exact ihFirst
    · exact ihLater graph member

mutual
def live (released : Nat → Prop) : Graph A → Prop
  | .node home _ children => ¬ released home ∧ liveChildren released children
def liveChildren (released : Nat → Prop) : List (Graph A) → Prop
  | [] => True
  | first :: later => live released first ∧ liveChildren released later
end

theorem liveChildren_iff (released : Nat → Prop) (graphs : List (Graph A)) :
    liveChildren released graphs ↔ ∀ graph ∈ graphs, live released graph := by
  induction graphs with
  | nil => simp [liveChildren]
  | cons first later ih => simp [liveChildren, ih]

/-- The closure fact makes the arena lifetime cover every descendant. -/
theorem closed_graph_survives (released : Nat → Prop) (graph : Graph A) :
    ∀ owner, closedAt owner graph = true → ¬ released owner → ¬ released 0 →
      live released graph := by
  refine Graph.rec
    (motive_1 := fun graph => ∀ owner, closedAt owner graph = true →
      ¬ released owner → ¬ released 0 → live released graph)
    (motive_2 := fun graphs => ∀ graph ∈ graphs, ∀ owner,
      closedAt owner graph = true → ¬ released owner → ¬ released 0 →
        live released graph) ?_ ?_ ?_ graph
  · intro home label children ih owner closed ownerLive globalLive
    simp only [closedAt, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at closed
    constructor
    · rcases closed.1 with rfl | rfl
      · exact globalLive
      · exact ownerLive
    · rw [liveChildren_iff]
      intro child member
      exact ih child member owner
        ((List.all_eq_true.mp (by simpa [closedChildren_eq_all] using closed.2)) child member)
        ownerLive globalLive
  · intro graph member
    cases member
  · intro first later ihFirst ihLater graph member
    rcases List.mem_cons.mp member with rfl | member
    · exact ihFirst
    · exact ihLater graph member

/-- Collection may release its old arenas, but not any arena it borrows. -/
theorem transport_survives (released : Nat → Prop) (destination : Nat) (loans : List Nat)
    (destinationLive : ¬ released destination) (globalLive : ¬ released 0)
    (loansLive : ∀ owner ∈ loans, ¬ released owner) (graph : Graph A) :
    live released (transport destination loans graph) := by
  refine Graph.rec
    (motive_1 := fun graph => live released (transport destination loans graph))
    (motive_2 := fun graphs => ∀ graph ∈ graphs,
      live released (transport destination loans graph)) ?_ ?_ ?_ graph
  · intro home label children ih
    rw [transport]
    split
    · rename_i borrowed
      exact closed_graph_survives released (.node home label children) home borrowed.2.2
        (loansLive home borrowed.2.1) globalLive
    · constructor
      · exact destinationLive
      · rw [liveChildren_iff, transportChildren_eq_map]
        intro child member
        rcases List.mem_map.mp member with ⟨source, inChildren, equal⟩
        subst child
        exact ih source inChildren
  · intro graph member
    cases member
  · intro first later ihFirst ihLater graph member
    rcases List.mem_cons.mp member with rfl | member
    · exact ihFirst
    · exact ihLater graph member

/-- Publication without loans constructs a graph closed over its new owner. -/
theorem materialization_closed (destination : Nat) (graph : Graph A) :
    closedAt destination (transport destination [] graph) = true := by
  refine Graph.rec
    (motive_1 := fun graph => closedAt destination (transport destination [] graph) = true)
    (motive_2 := fun graphs => ∀ graph ∈ graphs,
      closedAt destination (transport destination [] graph) = true) ?_ ?_ ?_ graph
  · intro home label children ih
    simp only [transport, List.not_mem_nil, false_and, and_false, ↓reduceIte,
      closedAt, beq_self_eq_true, Bool.or_true, Bool.true_and]
    rw [closedChildren_eq_all, transportChildren_eq_map, List.all_eq_true]
    intro child member
    rcases List.mem_map.mp member with ⟨source, inChildren, equal⟩
    subst child
    exact ih source inChildren
  · intro graph member
    cases member
  · intro first later ihFirst ihLater graph member
    rcases List.mem_cons.mp member with rfl | member
    · exact ihFirst
    · exact ihLater graph member

/-- After ordinary publication, releasing the borrowed and working arenas is safe. -/
theorem materialized_loan_survives (released : Nat → Prop) (working published : Nat)
    (loans : List Nat) (graph : Graph A) (publishedLive : ¬ released published)
    (globalLive : ¬ released 0) :
    live released (transport published [] (transport working loans graph)) ∧
      image (transport published [] (transport working loans graph)) = image graph := by
  constructor
  · exact closed_graph_survives released _ published
      (materialization_closed published _) publishedLive globalLive
  · rw [transport_preserves_values, transport_preserves_values]

namespace Controls

def borrowed : Graph Nat := .node 2 17 [.node 2 23 []]

theorem loan_does_not_certify_destination :
    transport 1 [2] borrowed = borrowed ∧ closedAt 1 (transport 1 [2] borrowed) = false := by
  simp [borrowed, transport, closedAt, closedChildren]

theorem mixed_parent_requires_traversal :
    let mixed : Graph Nat := .node 2 17 [.node 3 23 []]
    transport 1 [2] mixed = .node 1 17 [.node 1 23 []] := by
  simp [transport, transportChildren, closedAt, closedChildren]

theorem publication_retains_content_after_release :
    live (fun home => home = 1 ∨ home = 2)
      (transport 3 [] (transport 1 [2] borrowed)) ∧
    image (transport 3 [] (transport 1 [2] borrowed)) = image borrowed := by
  simp [borrowed, transport, transportChildren, closedAt, closedChildren,
    live, liveChildren, image, images]

end Controls
end Mettapedia.Machines.Cursor.ScopedGraphLoan

#print axioms Mettapedia.Machines.Cursor.ScopedGraphLoan.transport_preserves_values
#print axioms Mettapedia.Machines.Cursor.ScopedGraphLoan.closed_graph_survives
#print axioms Mettapedia.Machines.Cursor.ScopedGraphLoan.transport_survives
#print axioms Mettapedia.Machines.Cursor.ScopedGraphLoan.materialization_closed
#print axioms Mettapedia.Machines.Cursor.ScopedGraphLoan.materialized_loan_survives
#print axioms Mettapedia.Machines.Cursor.ScopedGraphLoan.Controls.loan_does_not_certify_destination
#print axioms Mettapedia.Machines.Cursor.ScopedGraphLoan.Controls.mixed_parent_requires_traversal
#print axioms Mettapedia.Machines.Cursor.ScopedGraphLoan.Controls.publication_retains_content_after_release
