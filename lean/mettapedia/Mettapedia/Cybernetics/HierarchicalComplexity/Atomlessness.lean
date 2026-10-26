import Mettapedia.Cybernetics.HierarchicalComplexity.Basic

/-!
# The atomicity boundary of simple-action counting

Simple-leaf counting requires a well-founded decomposition. An inhabited
atomless relation has neither simple nodes nor a decreasing ordinal rank.
This marks the boundary of the finite Commons--Pekker model; atomless ambient
systems are not instances of that model.
-/

set_option autoImplicit false

namespace Mettapedia.Cybernetics.HierarchicalComplexity

universe u v

variable {Outcome : Type v}

/-- A decomposition relation points from an immediate child to its parent. -/
structure DecompositionSystem where
  Node : Type u
  Child : Node → Node → Prop

namespace DecompositionSystem

/-- A node is simple when it has no immediate child. -/
def IsSimple (system : DecompositionSystem.{u}) (parent : system.Node) : Prop :=
  ∀ child, ¬ system.Child child parent

/-- An atomless decomposition has a child below every node. -/
def IsAtomless (system : DecompositionSystem.{u}) : Prop :=
  ∀ parent, ∃ child, system.Child child parent

/-- A strict ordinal rank decreases along every decomposition edge. -/
def AdmitsStrictOrdinalRank (system : DecompositionSystem.{u}) : Prop :=
  ∃ rank : system.Node → Ordinal.{u},
    ∀ ⦃child parent⦄, system.Child child parent → rank child < rank parent

theorem IsAtomless.not_isSimple {system : DecompositionSystem.{u}}
    (atomless : system.IsAtomless) (parent : system.Node) :
    ¬ system.IsSimple parent := by
  obtain ⟨child, childOf⟩ := atomless parent
  exact fun simple => simple child childOf

/-- An inhabited atomless child relation is not well-founded. -/
theorem IsAtomless.not_wellFounded {system : DecompositionSystem.{u}}
    [Nonempty system.Node] (atomless : system.IsAtomless) :
    ¬ WellFounded system.Child := by
  intro wellFounded
  obtain ⟨minimal, _, noChild⟩ :=
    wellFounded.has_min Set.univ Set.univ_nonempty
  obtain ⟨child, childOf⟩ := atomless minimal
  exact noChild child (Set.mem_univ child) childOf

/-- An inhabited atomless decomposition has no decreasing ordinal rank. -/
theorem IsAtomless.not_admitsStrictOrdinalRank {system : DecompositionSystem.{u}}
    [Nonempty system.Node] (atomless : system.IsAtomless) :
    ¬ system.AdmitsStrictOrdinalRank := by
  rintro ⟨rank, decreases⟩
  apply atomless.not_wellFounded
  exact (InvImage.wf rank Ordinal.lt_wf).mono
    (fun _ _ childOf => decreases childOf)

/-! ## Positive and negative controls -/

/-- A well-founded predecessor decomposition with `0` as a simple node. -/
def predecessor : DecompositionSystem.{0} where
  Node := Nat
  Child child parent := child + 1 = parent

theorem predecessor_zero_isSimple :
    predecessor.IsSimple (show predecessor.Node from (0 : Nat)) := by
  exact fun _ childOf => Nat.noConfusion childOf

/-- The predecessor decomposition has the expected strict ordinal rank. -/
theorem predecessor_admitsStrictOrdinalRank : predecessor.AdmitsStrictOrdinalRank := by
  refine ⟨fun (n : Nat) => (n : Ordinal), ?_⟩
  rintro child parent rfl
  exact (Nat.cast_lt (α := Ordinal)).mpr (Nat.lt_succ_self child)

/-- A one-node self-decomposition is the smallest atomless negative control. -/
def selfLoop : DecompositionSystem.{0} where
  Node := Unit
  Child _ _ := True

theorem selfLoop_isAtomless : selfLoop.IsAtomless := fun parent => ⟨parent, trivial⟩

theorem selfLoop_no_strictOrdinalRank : ¬ selfLoop.AdmitsStrictOrdinalRank := by
  let : Nonempty selfLoop.Node := ⟨()⟩
  exact selfLoop_isAtomless.not_admitsStrictOrdinalRank

end DecompositionSystem

namespace Action

/-- Well-founded action trees have simple leaves; they do not model atomless ontologies. -/
theorem nonempty_simpleLeaves (action : Action.{u, v} Outcome) :
    Nonempty (SimpleLeaves action) := by
  induction action with
  | simple => exact ⟨PUnit.unit⟩
  | compound Occurrence hasAtLeastTwo child organization inductionHypothesis =>
      obtain ⟨occurrence⟩ := hasAtLeastTwo.nonempty
      exact (inductionHypothesis occurrence).map fun leaf => ⟨occurrence, leaf⟩

theorem simpleLeafCardinal_ne_zero (action : Action.{u, v} Outcome) :
    simpleLeafCardinal action ≠ 0 := Cardinal.mk_ne_zero_iff.mpr (nonempty_simpleLeaves action)

end Action

end Mettapedia.Cybernetics.HierarchicalComplexity
