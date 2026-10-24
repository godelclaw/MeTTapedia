import Mettapedia.Enactive.BooleanPresentation
import Mettapedia.Logic.TheoryModel.Basic

/-!
# Semantic closure and literal completion freedom

World satisfaction asks whether a world belongs to every authored fact.
Completion satisfaction instead asks whether a later statement contains those
facts. The two relations have different consequences: adding an already
entailed fact preserves the worlds but can remove literal completions.

The computable closure below adds all vocabulary facts entailed by the current
statement. It realizes the existing theory/model polarity on finite, realizable
vocabulary statements. Its fixed points canonically represent world meanings;
within each such meaning the closed statement has the fewest completions.
This is a comparison of observations, not a replacement for Bennett's criterion.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.Finite.Layer

universe uWorld
variable {World : Type uWorld} [Fintype World] [DecidableEq World]
variable (layer : Finite.Layer World)

/-- The worlds satisfying the authored facts, rather than the statements
containing them. -/
def worldModels (source : layer.Statement) : Set World :=
  {world | Finite.Realizes world source.val}

/-- The finite realization semantics is the existing model operator at world
satisfaction. Completion satisfaction is a different relation. -/
theorem worldModels_eq_models (source : layer.Statement) :
    layer.worldModels source = Mettapedia.Logic.TheoryModel.models
      (fun (world : World) (fact : Finset World) => world ∈ fact)
      (source.val : Set (Finset World)) := rfl

/-- Consequences restricted to the available vocabulary. This function also
accepts raw fact sets; realizability is required only to package a statement. -/
def semanticClosureFacts (facts : Finset (Finset World)) : Finset (Finset World) :=
  layer.vocabulary.filter fun fact => ∀ world, Finite.Realizes world facts → world ∈ fact

@[simp]
theorem mem_semanticClosureFacts (facts : Finset (Finset World)) (fact : Finset World) :
    fact ∈ layer.semanticClosureFacts facts ↔
      fact ∈ layer.vocabulary ∧ ∀ world, Finite.Realizes world facts → world ∈ fact := by
  simp only [semanticClosureFacts, Finset.mem_filter]

/-- Add the available consequences without inventing a realizing world. -/
def semanticClosure (source : layer.Statement) : layer.Statement :=
  ⟨layer.semanticClosureFacts source.val, layer.mem_statements.mpr ⟨Finset.filter_subset _ _, by
    obtain ⟨world, realized⟩ := (layer.mem_statements.mp source.property).2
    exact ⟨world, fun fact member =>
      (layer.mem_semanticClosureFacts source.val fact).mp member |>.2 world realized⟩⟩⟩

@[simp]
theorem mem_semanticClosure (source : layer.Statement) (fact : Finset World) :
    fact ∈ (layer.semanticClosure source).val ↔
      fact ∈ layer.vocabulary ∧ ∀ world, Finite.Realizes world source.val → world ∈ fact :=
  layer.mem_semanticClosureFacts source.val fact

/-- The independently computed finite closure agrees with semantic entailment. -/
theorem mem_semanticClosure_iff_entails (source : layer.Statement) (fact : Finset World) :
    fact ∈ (layer.semanticClosure source).val ↔ fact ∈ layer.vocabulary ∧
      Mettapedia.Logic.TheoryModel.Entails
        (fun (world : World) (fact : Finset World) => world ∈ fact)
        (source.val : Set (Finset World)) fact := by
  rw [layer.mem_semanticClosure]
  rfl

/-- The concrete finite algorithm is the existing polarity closure, restricted
to the declared vocabulary. -/
theorem coe_semanticClosure_eq_consequences (source : layer.Statement) :
    ((layer.semanticClosure source).val : Set (Finset World)) =
      (layer.vocabulary : Set (Finset World)) ∩
        Mettapedia.Logic.TheoryModel.consequences
          (fun (world : World) (fact : Finset World) => world ∈ fact)
          (source.val : Set (Finset World)) := by
  ext fact
  exact layer.mem_semanticClosure_iff_entails source fact

theorem le_semanticClosure (source : layer.Statement) : source ≤ layer.semanticClosure source := by
  intro fact member
  exact (layer.mem_semanticClosure source fact).mpr
    ⟨(layer.mem_statements.mp source.property).1 member,
      fun _ realized => realized fact member⟩

@[simp]
theorem realizes_semanticClosure_iff (source : layer.Statement) (world : World) :
    Finite.Realizes world (layer.semanticClosure source).val ↔
      Finite.Realizes world source.val :=
  ⟨fun realized fact member => realized fact (layer.le_semanticClosure source member),
    fun realized fact member => (layer.mem_semanticClosure source fact).mp member |>.2 world realized⟩

@[simp]
theorem worldModels_semanticClosure (source : layer.Statement) :
    layer.worldModels (layer.semanticClosure source) = layer.worldModels source :=
  Set.ext fun world => layer.realizes_semanticClosure_iff source world

/-- The restricted consequence adjunction, on realizable vocabulary statements. -/
theorem le_semanticClosure_iff (left right : layer.Statement) :
    left ≤ layer.semanticClosure right ↔ layer.worldModels right ⊆ layer.worldModels left := by
  constructor
  · intro included world realized fact member
    exact (layer.mem_semanticClosure right fact).mp (included member) |>.2 world realized
  · intro included fact member
    exact (layer.mem_semanticClosure right fact).mpr
      ⟨(layer.mem_statements.mp left.property).1 member,
        fun world realized => included realized fact member⟩

theorem semanticClosure_mono : Monotone layer.semanticClosure := by
  intro left right included
  rw [layer.le_semanticClosure_iff]
  intro world realized
  exact (layer.realizes_semanticClosure_iff left world).mpr
    (fun fact member => realized fact (included member))

@[simp]
theorem semanticClosure_idem (source : layer.Statement) :
    layer.semanticClosure (layer.semanticClosure source) = layer.semanticClosure source := by
  apply Subtype.ext
  ext fact
  simp only [mem_semanticClosure, realizes_semanticClosure_iff]

/-- Formal-concept closure bundled with Mathlib's standard order interface. -/
def semanticClosureOperator : ClosureOperator layer.Statement where
  toFun := layer.semanticClosure
  monotone' := layer.semanticClosure_mono
  le_closure' := layer.le_semanticClosure
  idempotent' := layer.semanticClosure_idem

/-- Closed fact sets classify exactly the equality of world meanings. -/
theorem semanticClosure_eq_iff (left right : layer.Statement) :
    layer.semanticClosure left = layer.semanticClosure right ↔
      layer.worldModels left = layer.worldModels right := by
  constructor
  · intro equal
    rw [← layer.worldModels_semanticClosure left, ← layer.worldModels_semanticClosure right, equal]
  · intro equal
    apply Subtype.ext
    ext fact
    rw [layer.mem_semanticClosure, layer.mem_semanticClosure]
    change (fact ∈ layer.vocabulary ∧ layer.worldModels left ⊆ (fact : Set World)) ↔
      (fact ∈ layer.vocabulary ∧ layer.worldModels right ⊆ (fact : Set World))
    rw [equal]

/-- Agreement with the independently defined abstract aspect interpretation. -/
theorem worldModels_toAbstract (source : layer.Statement) :
    source.toAbstract.semanticExtent = layer.worldModels source := by
  ext world
  constructor
  · intro realized fact member
    exact realized (fact : Set World) ⟨fact, member, rfl⟩
  · rintro realized _ ⟨fact, member, rfl⟩
    exact realized fact member

/-- The closed representative contains every statement with the same world meaning. -/
theorem le_semanticClosure_of_worldModels_eq {source other : layer.Statement}
    (same : layer.worldModels other = layer.worldModels source) :
    other ≤ layer.semanticClosure source :=
  (layer.le_semanticClosure_iff other source).mpr same.symm.subset

theorem semanticClosure_isGreatest (source : layer.Statement) :
    IsGreatest {other | layer.worldModels other = layer.worldModels source}
      (layer.semanticClosure source) :=
  ⟨layer.worldModels_semanticClosure source,
    fun _ same => layer.le_semanticClosure_of_worldModels_eq same⟩

/-- Within one semantic class, closure minimizes the number of literal completions. -/
theorem weakness_semanticClosure_minimal {source other : layer.Statement}
    (same : layer.worldModels other = layer.worldModels source) :
    layer.weakness (layer.semanticClosure source) ≤ layer.weakness other :=
  layer.weakness_antitone (layer.le_semanticClosure_of_worldModels_eq same)

/-- That minimum is unique, despite other incomparable statements possibly
having equal completion counts. -/
theorem weakness_semanticClosure_eq_iff {source other : layer.Statement}
    (same : layer.worldModels other = layer.worldModels source) :
    layer.weakness other = layer.weakness (layer.semanticClosure source) ↔
      other = layer.semanticClosure source := by
  constructor
  · intro equal
    apply le_antisymm (layer.le_semanticClosure_of_worldModels_eq same)
    by_contra notBack
    have strict := lt_of_le_not_ge (layer.le_semanticClosure_of_worldModels_eq same) notBack
    exact (layer.weakness_strictAnti strict).ne' equal
  · rintro rfl
    rfl

namespace Canary

open Mettapedia.Enactive.Finite.Canary

/-- Adding the universally true fact preserves world meaning but halves this
statement's literal completion count. -/
theorem semanticClosure_counts :
    boolLayer.weakness trueStatement = 2 ∧
      boolLayer.weakness (boolLayer.semanticClosure trueStatement) = 1 := by decide

theorem semanticClosure_changes_statement : boolLayer.semanticClosure trueStatement ≠ trueStatement := by
  decide

end Canary
end Mettapedia.Enactive.Finite.Layer

namespace Mettapedia.Enactive.Bennett2023.Layer

universe uWorld
variable {World : Type uWorld} [Fintype World] [DecidableEq World]

/-- Closure of translated facts is exactly entailment by the independently
defined Boolean programs, restricted to their original vocabulary. -/
theorem truthSet_mem_semanticClosure_iff (layer : Layer World) (source : layer.Statement)
    (program : Program World) :
    truthSet program ∈ (layer.toFinite.semanticClosure (layer.statementEquiv source)).val ↔
      program ∈ layer.vocabulary ∧ ∀ world, Realizes world source.val → program world = true := by
  rw [Finite.Layer.mem_semanticClosure]
  refine and_congr ?_ ?_
  · change programFactEquiv program ∈ programFactEquiv.finsetCongr layer.vocabulary ↔ _
    simp only [Equiv.finsetCongr_apply, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  · exact forall_congr' fun world =>
      imp_congr (realizes_finsetCongr_iff world source.val) (mem_truthSet program world)

end Mettapedia.Enactive.Bennett2023.Layer
