import Mettapedia.TypeTheory.PositiveInductiveBlock
import Mettapedia.TypeTheory.IndexedContainerInduction
import Mettapedia.TypeTheory.IndexedPolynomialEquivalence

/-!
# Indexed registered containers for positive nested fields

`PositiveInductiveBlock` deliberately began with containers over `Unit`,
which covers `List (F ...)`.  A vector container has a genuine output index:
its recursive-position fibre is `Fin n`.  This module supplies the richer
semantic layer without changing the accepted source grammar prematurely.

A registry entry owns its output-expression language and interpretation.
Nested code therefore retains both the container output and the child-family
index.  The List instance embeds the established unindexed case; the Vector
control proves that lengths two and three expose inequivalent recursive
position fibres.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPositiveContainer

open IndexedContainer
open IndexedPolynomial
open IndexedPolynomial.Description

universe u v

/-- One registered indexed container, including the scoped language used to
compute its output index from constructor data. -/
structure Entry (I : Interface.{u}) where
  Output : Type
  OutputExpr : List I.SortCode → Type
  evalOutput : {context : List I.SortCode} →
    OutputExpr context → Env I.Value context → Output
  container : IndexedContainer.{0, 0, 0} Output

structure Registry (I : Interface.{u}) where
  lookup : String → Option (Entry I)

structure Registry.Finitary {I : Interface.{u}} (registry : Registry I) where
  containerFinitary : ∀ name entry,
    registry.lookup name = some entry → IndexedContainer.Finitary entry.container

/-- A registry whose nested containers expose a selected source order, not
merely finite position fibres. -/
structure Registry.OrderedFinitary {I : Interface.{u}} (registry : Registry I) where
  containerOrdered : ∀ name entry,
    registry.lookup name = some entry →
      IndexedContainer.OrderedFinitary entry.container

def Registry.OrderedFinitary.toFinitary {I : Interface.{u}}
    {registry : Registry I} (ordered : registry.OrderedFinitary) :
    registry.Finitary where
  containerFinitary name entry found :=
    (ordered.containerOrdered name entry found).toFinitary

/-- Recognized positive code. A nested field keeps its container output and
its recursive child's family index as separate expressions. -/
inductive Code (I : Interface.{u}) (registry : Registry I)
    (parameterCount : Nat) : List I.SortCode → Type (u + 2) where
  | result {context} (index : I.IndexExpr context) :
      Code I registry parameterCount context
  | data {context} (sort : I.SortCode)
      (body : Code I registry parameterCount (sort :: context)) :
      Code I registry parameterCount context
  | recursive {context} (index : I.IndexExpr context)
      (rest : Code I registry parameterCount context) :
      Code I registry parameterCount context
  | nested {context} (name : String) (entry : Entry I)
      (registered : registry.lookup name = some entry)
      (output : entry.OutputExpr context) (childIndex : I.IndexExpr context)
      (rest : Code I registry parameterCount context) :
      Code I registry parameterCount context

namespace Code

variable {I : Interface.{u}} {registry : Registry I} {parameterCount : Nat}

def Shape : {context : List I.SortCode} →
    Code I registry parameterCount context →
      Env I.Value context → I.Index → Type (u + 1)
  | _, .result expression, environment, index =>
      ULift.{u + 1, 0} (PLift.{0} (I.evalIndex expression environment = index))
  | _, .data sort body, environment, index =>
      Σ value : I.Value sort, Shape body (value, environment) index
  | _, .recursive _ rest, environment, index => Shape rest environment index
  | _, .nested _ entry _ output _ rest, environment, index =>
      Σ _shape : entry.container.Shape (entry.evalOutput output environment),
        Shape rest environment index

def Position : {context : List I.SortCode} →
    (code : Code I registry parameterCount context) →
    {environment : Env I.Value context} → {index : I.Index} →
      Shape code environment index → Type u
  | _, .result _, _, _, _ => PEmpty
  | _, .data _ body, _, _, shape => Position body shape.2
  | _, .recursive _ rest, _, _, shape => Option (Position rest shape)
  | _, .nested _ entry _ _ _ rest, _, _, shape =>
      Sum (entry.container.Position shape.1) (Position rest shape.2)

def next : {context : List I.SortCode} →
    (code : Code I registry parameterCount context) →
    {environment : Env I.Value context} → {index : I.Index} →
    (shape : Shape code environment index) → Position code shape → I.Index
  | _, .result _, _, _, _, position => PEmpty.elim position
  | _, .data _ body, _, _, shape, position => next body shape.2 position
  | _, .recursive expression rest, environment, _, shape, position =>
      match position with
      | none => I.evalIndex expression environment
      | some prior => next rest shape prior
  | _, .nested _ _ _ _ childIndex rest, environment, _, shape, position =>
      match position with
      | .inl _ => I.evalIndex childIndex environment
      | .inr prior => next rest shape.2 prior

def polynomial {context : List I.SortCode}
    (code : Code I registry parameterCount context) :
    IndexedPolynomial (Env I.Value context) (fun _ => I.Index) where
  Shape := Shape code
  Position := Position code
  next := next code

@[instance_reducible] noncomputable def positionFintype
    (finitary : registry.Finitary) :
    ∀ {context : List I.SortCode}
      (code : Code I registry parameterCount context),
      ∀ {environment : Env I.Value context} {index : I.Index}
        (shape : Shape code environment index), Fintype (Position code shape)
  | _, .result _, _, _, _ => inferInstanceAs (Fintype PEmpty)
  | _, .data _ body, _, _, shape => positionFintype finitary body shape.2
  | _, .recursive _ rest, _, _, shape => by
      letI restFintype := positionFintype finitary rest shape
      change Fintype (Option (Position rest shape))
      infer_instance
  | _, .nested name entry registered _ _ rest, _, _, shape => by
      letI containerFintype :=
        finitary.containerFinitary name entry registered |>.positionFintype shape.1
      letI restFintype := positionFintype finitary rest shape.2
      change Fintype
        (Sum (entry.container.Position shape.1) (Position rest shape.2))
      infer_instance

/-- Enumerate direct positions first, then each registered nested container in
its selected order, then the remaining constructor fields. -/
def orderedPositions
    (ordered : registry.OrderedFinitary) :
    ∀ {context : List I.SortCode}
      (code : Code I registry parameterCount context),
      ∀ {environment : Env I.Value context} {index : I.Index}
        (shape : Shape code environment index), List (Position code shape)
  | _, .result _, _, _, _ => []
  | _, .data _ body, _, _, shape => orderedPositions ordered body shape.2
  | _, .recursive _ rest, _, _, shape =>
      none :: (orderedPositions ordered rest shape).map some
  | _, .nested name entry registered _ _ rest, _, _, shape =>
      ((ordered.containerOrdered name entry registered).positions shape.1).map Sum.inl ++
        (orderedPositions ordered rest shape.2).map Sum.inr

@[simp] theorem mem_orderedPositions
    (ordered : registry.OrderedFinitary) :
    ∀ {context : List I.SortCode}
      (code : Code I registry parameterCount context),
      ∀ {environment : Env I.Value context} {index : I.Index}
        (shape : Shape code environment index) (position : Position code shape),
        position ∈ orderedPositions ordered code shape
  | _, .result _, _, _, _, position => PEmpty.elim position
  | _, .data _ body, _, _, shape, position =>
      mem_orderedPositions ordered body shape.2 position
  | _, .recursive _ rest, _, _, shape, position => by
      cases position with
      | none => exact List.mem_cons_self
      | some prior =>
          exact List.mem_cons_of_mem _ (List.mem_map.mpr
            ⟨prior, mem_orderedPositions ordered rest shape prior, rfl⟩)
  | _, .nested name entry registered _ _ rest, _, _, shape, position => by
      cases position with
      | inl nestedPosition =>
          exact List.mem_append_left _ (List.mem_map.mpr
            ⟨nestedPosition,
              (ordered.containerOrdered name entry registered).positions_complete
                shape.1 nestedPosition,
              rfl⟩)
      | inr prior =>
          exact List.mem_append_right _ (List.mem_map.mpr
            ⟨prior, mem_orderedPositions ordered rest shape.2 prior, rfl⟩)

@[simp] theorem orderedPositions_nodup
    (ordered : registry.OrderedFinitary) :
    ∀ {context : List I.SortCode}
      (code : Code I registry parameterCount context),
      ∀ {environment : Env I.Value context} {index : I.Index}
        (shape : Shape code environment index),
        (orderedPositions ordered code shape).Nodup
  | _, .result _, _, _, _ => by simp [orderedPositions]
  | _, .data _ body, _, _, shape => orderedPositions_nodup ordered body shape.2
  | _, .recursive _ rest, environment, index, shape => by
      change Shape rest environment index at shape
      change (none :: (orderedPositions ordered rest shape).map some).Nodup
      apply List.nodup_cons.mpr
      refine ⟨by simp, ?_⟩
      exact (orderedPositions_nodup ordered rest shape).map
        (Option.some_injective _)
  | _, .nested name entry registered output _ rest, environment, index, shape => by
      change (Σ nestedShape : entry.container.Shape
          (entry.evalOutput output environment), Shape rest environment index) at shape
      change (((ordered.containerOrdered name entry registered).positions shape.1).map
          Sum.inl ++ (orderedPositions ordered rest shape.2).map Sum.inr).Nodup
      have nested :=
        (ordered.containerOrdered name entry registered).positions_nodup shape.1
      have remaining := orderedPositions_nodup ordered rest shape.2
      apply List.nodup_append.mpr
      refine ⟨nested.map Sum.inl_injective, remaining.map Sum.inr_injective, ?_⟩
      intro left leftPresent right rightPresent
      obtain ⟨nestedPosition, _, rfl⟩ := List.mem_map.mp leftPresent
      obtain ⟨prior, _, rfl⟩ := List.mem_map.mp rightPresent
      intro same
      cases same

/-- The traversal cost counts each semantic position exactly once. -/
theorem orderedPositions_length
    (ordered : registry.OrderedFinitary)
    {context : List I.SortCode}
    (code : Code I registry parameterCount context)
    {environment : Env I.Value context} {index : I.Index}
    (shape : Shape code environment index) :
    (orderedPositions ordered code shape).length =
      @Fintype.card (Position code shape)
        (positionFintype ordered.toFinitary code shape) := by
  classical
  let positionFinite := positionFintype ordered.toFinitary code shape
  have complete : (orderedPositions ordered code shape).toFinset = Finset.univ := by
    ext position
    simp [mem_orderedPositions]
  rw [← List.toFinset_card_of_nodup (orderedPositions_nodup ordered code shape),
    complete, Finset.card_univ]

end Code

/-! ## The unindexed registered grammar embeds without changing its signature -/

namespace Unindexed

/-- Retain an established container over `Unit` as an indexed registry entry.
There is no new output information to infer or erase in this embedding. -/
def liftEntry (I : Interface.{u}) (container : PositiveInductiveBlock.Container) :
    Entry I where
  Output := Unit
  OutputExpr := fun _ => PUnit
  evalOutput := fun _ _ => ()
  container := container

def liftRegistry (source : PositiveInductiveBlock.Registry) (I : Interface.{u}) :
    Registry I where
  lookup name := (source.lookup name).map (liftEntry I)

variable {source : PositiveInductiveBlock.Registry} {I : Interface.{u}}
  {parameterCount : Nat}

/-- Embed registry-coherent old code, retaining the registry proof required
by every nested field in the indexed grammar. -/
def liftCode : {context : List I.SortCode} →
    (code : PositiveInductiveBlock.Code source I parameterCount context) →
    PositiveInductiveBlock.RawCode.WellRegistered code →
      Code I (liftRegistry source I) parameterCount context
  | _, .result index, _ => .result index
  | _, .data sort body, registered => .data sort (liftCode body registered)
  | _, .recursive index rest, registered => .recursive index (liftCode rest registered)
  | _, .nested name container index rest, registered =>
      .nested name (liftEntry I container)
        (by simp [liftRegistry, registered.1]) PUnit.unit index
        (liftCode rest registered.2)

/-- Constructor data and output-index equations survive the change of grammar.
The result equation is lifted to the indexed grammar's larger shape universe. -/
def shapeEquiv : {context : List I.SortCode} →
    (code : PositiveInductiveBlock.Code source I parameterCount context) →
    (registered : PositiveInductiveBlock.RawCode.WellRegistered code) →
    ∀ environment index,
      PositiveInductiveBlock.Code.Shape code environment index ≃
        Code.Shape (liftCode code registered) environment index
  | _, .result _, _, _, _ => Equiv.ulift.trans Equiv.ulift.symm
  | _, .data sort body, registered, environment, index =>
      Equiv.sigmaCongrRight fun value : I.Value sort =>
        shapeEquiv body registered (value, environment) index
  | _, .recursive _ rest, registered, environment, index =>
      shapeEquiv rest registered environment index
  | _, .nested _ _ _ rest, registered, environment, index =>
      Equiv.sigmaCongrRight fun _ =>
        shapeEquiv rest registered.2 environment index

/-- Every recursive occurrence has a corresponding occurrence over the
transported shape, including all positions of a nested container. -/
def positionEquiv : {context : List I.SortCode} →
    (code : PositiveInductiveBlock.Code source I parameterCount context) →
    (registered : PositiveInductiveBlock.RawCode.WellRegistered code) →
    ∀ {environment index} (shape : PositiveInductiveBlock.Code.Shape code environment index),
      PositiveInductiveBlock.Code.Position code shape ≃
        Code.Position (liftCode code registered)
          (shapeEquiv code registered environment index shape)
  | _, .result _, _, _, _, _ => Equiv.refl _
  | _, .data _ body, registered, _, _, shape =>
      positionEquiv body registered shape.2
  | _, .recursive _ rest, registered, _, _, shape =>
      Equiv.optionCongr (positionEquiv rest registered shape)
  | _, .nested _ _ _ rest, registered, _, _, shape =>
      Equiv.sumCongr (Equiv.refl _) (positionEquiv rest registered.2 shape.2)

theorem next_preserved :
    ∀ {context : List I.SortCode}
      (code : PositiveInductiveBlock.Code source I parameterCount context)
      (registered : PositiveInductiveBlock.RawCode.WellRegistered code)
      {environment index} (shape : PositiveInductiveBlock.Code.Shape code environment index)
      (position : PositiveInductiveBlock.Code.Position code shape),
      Code.next (liftCode code registered)
          (shapeEquiv code registered environment index shape)
          (positionEquiv code registered shape position) =
        PositiveInductiveBlock.Code.next code shape position
  | _, .result _, _, _, _, _, position => PEmpty.elim position
  | _, .data _ body, registered, _, _, shape, position =>
      next_preserved body registered shape.2 position
  | _, .recursive _ rest, registered, _, _, shape, position => by
      cases position with
      | none => rfl
      | some prior => exact next_preserved rest registered shape prior
  | _, .nested _ _ _ rest, registered, _, _, shape, position => by
      cases position with
      | inl _ => rfl
      | inr prior => exact next_preserved rest registered.2 shape.2 prior

/-- This comparison preserves the complete polynomial signature, rather than
only a count of fields or a bijection between untyped carriers. -/
def signatureEquiv {context : List I.SortCode}
    (code : PositiveInductiveBlock.Code source I parameterCount context)
    (registered : PositiveInductiveBlock.RawCode.WellRegistered code) :
    IndexedPolynomial.SignatureEquiv
      (PositiveInductiveBlock.Code.polynomial code)
      (Code.polynomial (liftCode code registered)) where
  shape := shapeEquiv code registered
  position := positionEquiv code registered
  next_preserved := next_preserved code registered

/-- Preserve a registry's selected traversal evidence under the embedding.
The lookup is inspected before its entry is returned; a printed name does
not introduce a container that was absent from the source registry. -/
def liftOrdered
    (sourceOrder : ∀ name container, source.lookup name = some container →
      IndexedContainer.OrderedFinitary container) :
    (liftRegistry source I).OrderedFinitary where
  containerOrdered name entry found :=
    match looked : source.lookup name with
    | none => by simp [liftRegistry, looked] at found
    | some container =>
        have same : liftEntry I container = entry := by
          simpa [liftRegistry, looked] using found
        same ▸ sourceOrder name container looked

@[simp] theorem liftOrdered_container
    (sourceOrder : ∀ name container, source.lookup name = some container →
      IndexedContainer.OrderedFinitary container)
    (name : String) (container : PositiveInductiveBlock.Container)
    (registered : source.lookup name = some container) :
    (liftOrdered (I := I) sourceOrder).containerOrdered name (liftEntry I container)
        (by simp [liftRegistry, registered]) =
      sourceOrder name container registered := by
  dsimp only [liftOrdered]
  split
  · rename_i absent
    simp [absent] at registered
  · rename_i actual found
    have same : actual = container := Option.some.inj (found.symm.trans registered)
    subst actual
    rfl

/-- Source order on the older constructor grammar: direct children precede
the remaining fields, and a nested field uses its registered order. -/
def sourcePositions
    (sourceOrder : ∀ name container, source.lookup name = some container →
      IndexedContainer.OrderedFinitary container) :
    ∀ {context : List I.SortCode}
      (code : PositiveInductiveBlock.Code source I parameterCount context),
      PositiveInductiveBlock.RawCode.WellRegistered code →
      ∀ {environment index} (shape : PositiveInductiveBlock.Code.Shape code environment index),
        List (PositiveInductiveBlock.Code.Position code shape)
  | _, .result _, _, _, _, _ => []
  | _, .data _ body, registered, _, _, shape =>
      sourcePositions sourceOrder body registered shape.2
  | _, .recursive _ rest, registered, _, _, shape =>
      none :: (sourcePositions sourceOrder rest registered shape).map some
  | _, .nested name container _ rest, registered, _, _, shape =>
      ((sourceOrder name container registered.1).positions shape.1).map Sum.inl ++
        (sourcePositions sourceOrder rest registered.2 shape.2).map Sum.inr

/-- The embedding preserves the selected ordered list occurrence by
occurrence, rather than merely preserving its cardinality or its members. -/
theorem orderedPositions_preserved
    (sourceOrder : ∀ name container, source.lookup name = some container →
      IndexedContainer.OrderedFinitary container) :
    ∀ {context : List I.SortCode}
      (code : PositiveInductiveBlock.Code source I parameterCount context)
      (registered : PositiveInductiveBlock.RawCode.WellRegistered code)
      {environment index} (shape : PositiveInductiveBlock.Code.Shape code environment index),
      (sourcePositions sourceOrder code registered shape).map
          (positionEquiv code registered shape) =
        Code.orderedPositions (liftOrdered sourceOrder) (liftCode code registered)
          (shapeEquiv code registered environment index shape)
  | _, .result _, _, _, _, _ => rfl
  | _, .data _ body, registered, _, _, shape =>
      orderedPositions_preserved sourceOrder body registered shape.2
  | _, .recursive _ rest, registered, _, _, shape => by
      change (none :: (sourcePositions sourceOrder rest registered shape).map some).map
          (Equiv.optionCongr (positionEquiv rest registered shape)) =
        none :: (Code.orderedPositions (liftOrdered sourceOrder)
          (liftCode rest registered) (shapeEquiv rest registered _ _ shape)).map some
      simpa only [List.map_cons, List.map_map, Function.comp_def,
        Equiv.optionCongr_apply, Option.map_none, Option.map_some] using
        congrArg (fun positions => none :: positions.map some)
          (orderedPositions_preserved sourceOrder rest registered shape)
  | _, .nested name container index rest, registered, _, _, shape => by
      change (((sourceOrder name container registered.1).positions shape.1).map Sum.inl ++
          (sourcePositions sourceOrder rest registered.2 shape.2).map Sum.inr).map
            (Equiv.sumCongr (Equiv.refl _) (positionEquiv rest registered.2 shape.2)) =
        (((liftOrdered sourceOrder).containerOrdered name (liftEntry I container)
          (by simp [liftRegistry, registered.1])).positions shape.1).map Sum.inl ++
          (Code.orderedPositions (liftOrdered sourceOrder) (liftCode rest registered.2)
            (shapeEquiv rest registered.2 _ _ shape.2)).map Sum.inr
      rw [liftOrdered_container sourceOrder name container registered.1]
      simp only [List.map_append, List.map_map, Equiv.sumCongr_apply,
        Function.comp_def]
      rw [← orderedPositions_preserved sourceOrder rest registered.2 shape.2]
      simp [List.map_map, Function.comp_def]
      rfl

/-- Observing transported children gives exactly the source's ordered
observations, including repeated values at different positions. -/
theorem ordered_observations_preserved
    (sourceOrder : ∀ name container, source.lookup name = some container →
      IndexedContainer.OrderedFinitary container)
    {context : List I.SortCode}
    (code : PositiveInductiveBlock.Code source I parameterCount context)
    (registered : PositiveInductiveBlock.RawCode.WellRegistered code)
    {environment index} (shape : PositiveInductiveBlock.Code.Shape code environment index)
    {Observation : Type v}
    (observe : PositiveInductiveBlock.Code.Position code shape → Observation) :
    (Code.orderedPositions (liftOrdered sourceOrder) (liftCode code registered)
        (shapeEquiv code registered environment index shape)).map
        (fun position => observe ((positionEquiv code registered shape).symm position)) =
      (sourcePositions sourceOrder code registered shape).map observe := by
  rw [← orderedPositions_preserved sourceOrder code registered shape]
  simp [List.map_map, Function.comp_def]

theorem mem_sourcePositions
    (sourceOrder : ∀ name container, source.lookup name = some container →
      IndexedContainer.OrderedFinitary container)
    {context : List I.SortCode}
    (code : PositiveInductiveBlock.Code source I parameterCount context)
    (registered : PositiveInductiveBlock.RawCode.WellRegistered code)
    {environment index} (shape : PositiveInductiveBlock.Code.Shape code environment index)
    (position : PositiveInductiveBlock.Code.Position code shape) :
    position ∈ sourcePositions sourceOrder code registered shape := by
  have member := Code.mem_orderedPositions (liftOrdered sourceOrder) (liftCode code registered)
    (shapeEquiv code registered environment index shape) (positionEquiv code registered shape position)
  rw [← orderedPositions_preserved sourceOrder code registered shape] at member
  obtain ⟨prior, priorMember, same⟩ := List.mem_map.mp member
  exact (positionEquiv code registered shape).injective same ▸ priorMember

theorem sourcePositions_nodup
    (sourceOrder : ∀ name container, source.lookup name = some container →
      IndexedContainer.OrderedFinitary container)
    {context : List I.SortCode}
    (code : PositiveInductiveBlock.Code source I parameterCount context)
    (registered : PositiveInductiveBlock.RawCode.WellRegistered code)
    {environment index} (shape : PositiveInductiveBlock.Code.Shape code environment index) :
    (sourcePositions sourceOrder code registered shape).Nodup := by
  have distinct := Code.orderedPositions_nodup (liftOrdered sourceOrder) (liftCode code registered)
    (shapeEquiv code registered environment index shape)
  rw [← orderedPositions_preserved sourceOrder code registered shape] at distinct
  exact distinct.of_map _

/-- The source order on all constructor occurrences of a recognized block. -/
def blockSourcePositions
    (sourceOrder : ∀ name container, source.lookup name = some container →
      IndexedContainer.OrderedFinitary container)
    {context : List I.SortCode}
    (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered)
    {environment index} (shape : block.polynomial.Shape environment index) :
    List (block.polynomial.Position shape) :=
  sourcePositions sourceOrder (block.constructors.get shape.1).body
    (registered _ (List.get_mem _ _)) shape.2

theorem mem_blockSourcePositions
    (sourceOrder : ∀ name container, source.lookup name = some container →
      IndexedContainer.OrderedFinitary container)
    {context : List I.SortCode}
    (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered)
    {environment index} (shape : block.polynomial.Shape environment index)
    (position : block.polynomial.Position shape) :
    position ∈ blockSourcePositions sourceOrder block registered shape :=
  mem_sourcePositions sourceOrder _ _ _ position

/-- Retain a constructor occurrence from a complete admitted source block. -/
def blockCode {context : List I.SortCode}
    (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered) (occurrence : Fin block.constructors.length) :
    Code I (liftRegistry source I) parameterCount context :=
  liftCode (block.constructors.get occurrence).body
    (registered _ (List.get_mem _ _))

/-- Indexed constructor semantics for the complete source inventory. The
occurrence ordinal remains part of the shape, so no constructors are merged. -/
def blockPolynomial {context : List I.SortCode}
    (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered) :
    IndexedPolynomial (Env I.Value context) (fun _ => I.Index) where
  Shape := fun environment index =>
    Σ occurrence : Fin block.constructors.length,
      Code.Shape (blockCode block registered occurrence) environment index
  Position := fun shape => Code.Position (blockCode block registered shape.1) shape.2
  next := fun shape position => Code.next (blockCode block registered shape.1) shape.2 position

def blockSignatureEquiv {context : List I.SortCode}
    (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered) :
    IndexedPolynomial.SignatureEquiv block.polynomial (blockPolynomial block registered) where
  shape := fun environment index => Equiv.sigmaCongrRight fun occurrence =>
    shapeEquiv (block.constructors.get occurrence).body
      (registered _ (List.get_mem _ _)) environment index
  position := fun shape => positionEquiv (block.constructors.get shape.1).body
    (registered _ (List.get_mem _ _)) shape.2
  next_preserved := fun shape position => next_preserved (block.constructors.get shape.1).body
    (registered _ (List.get_mem _ _)) shape.2 position

/-- The source block's whole recursive family survives the grammar embedding. -/
noncomputable def blockFamilyEquiv {context : List I.SortCode}
    (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered) (environment : Env I.Value context) (index : I.Index) :
    block.Family environment index ≃
      IndexedPolynomial.Fix (blockPolynomial block registered) environment index :=
  (blockSignatureEquiv block registered).fixEquiv environment index

/-- Generated recursion agrees after translating constructor layers and methods.
The target fold is built over the indexed polynomial, not an alias for the old fold. -/
theorem blockRecursor_preserved {context : List I.SortCode}
    (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered)
    {carrier : Env I.Value context → I.Index → Type v}
    (algebra : IndexedPolynomial.Algebra block.polynomial carrier)
    (environment : Env I.Value context) (index : I.Index)
    (tree : block.Family environment index) :
    IndexedPolynomial.Fix.fold (blockPolynomial block registered)
        ((blockSignatureEquiv block registered).pushAlgebra algebra).act environment index
        (blockFamilyEquiv block registered environment index tree) =
      block.recursor algebra environment index tree := by
  have preserved := (blockSignatureEquiv block registered).fold_fromFix algebra environment index
    ((blockSignatureEquiv block registered).toFix environment index tree)
  rw [IndexedPolynomial.SignatureEquiv.fromFix_toFix] at preserved
  exact preserved.symm

end Unindexed

/-! ## The established List container is retained exactly -/

namespace ListInstance

variable (I : Interface.{u})

def entry : Entry I where
  Output := Unit
  OutputExpr := fun _ => PUnit
  evalOutput := fun _ _ => ()
  container := IndexedContainer.Examples.list

def registry : Registry I where
  lookup name := if name = "List" then some (entry I) else none

def finitary : (registry I).Finitary where
  containerFinitary := by
    intro name foundEntry found
    by_cases same : name = "List"
    · subst name
      simp [registry] at found
      subst foundEntry
      exact IndexedContainer.Examples.listFinitary
    · simp [registry, same] at found

def orderedFinitary : (registry I).OrderedFinitary where
  containerOrdered := by
    intro name foundEntry found
    by_cases same : name = "List"
    · subst name
      simp [registry] at found
      subst foundEntry
      exact IndexedContainer.Examples.listOrderedFinitary
    · simp [registry, same] at found

theorem entry_container_eq : (entry I).container = IndexedContainer.Examples.list :=
  rfl

theorem entry_output_eq {context : List I.SortCode}
    (expression : (entry I).OutputExpr context)
    (environment : Env I.Value context) :
    (entry I).evalOutput expression environment = () :=
  rfl

end ListInstance

/-! ## A genuine indexed Vector control -/

namespace VectorControl

inductive DataSort where
  | payload
  | length
  deriving DecidableEq

def value : DataSort → Type
  | .payload => Bool
  | .length => Nat

def interface : Interface where
  SortCode := DataSort
  Value := value
  Index := Unit
  IndexExpr := fun _ => Unit
  evalIndex := fun _ _ => ()

inductive LengthExpr : List DataSort → Type where
  | here {context} : LengthExpr (.length :: context)
  | there {sort context} : LengthExpr context → LengthExpr (sort :: context)

def evalLength : {context : List DataSort} →
    LengthExpr context → Env value context → Nat
  | _, .here, environment => environment.1
  | _, .there prior, environment => evalLength prior environment.2

def entry : Entry interface where
  Output := Nat
  OutputExpr := LengthExpr
  evalOutput := evalLength
  container := IndexedContainer.Examples.vector

def registry : Registry interface where
  lookup name := if name = "Vector" then some entry else none

def finitary : registry.Finitary where
  containerFinitary := by
    intro name foundEntry found
    by_cases same : name = "Vector"
    · subst name
      simp [registry] at found
      subst foundEntry
      exact IndexedContainer.Examples.vectorFinitary
    · simp [registry, same] at found

def orderedFinitary : registry.OrderedFinitary where
  containerOrdered := by
    intro name foundEntry found
    by_cases same : name = "Vector"
    · subst name
      simp [registry] at found
      subst foundEntry
      exact IndexedContainer.Examples.vectorOrderedFinitary
    · simp [registry, same] at found

abbrev Checked := Code interface registry 0 []

/-- One length field followed by a vector of recursive children at that
length. The outer family itself is unindexed in this control. -/
def code : Checked :=
  .data .length
    (.nested "Vector" entry (by simp [registry]) .here () (.result ()))

def environment : Env interface.Value [] := PUnit.unit

def shapeAt (length : Nat) : Code.Shape code environment () :=
  ⟨length, (), ⟨⟨rfl⟩⟩⟩

def positionEquiv (length : Nat) :
    Code.Position code (shapeAt length) ≃ Fin length := by
  change Sum (Fin length) PEmpty ≃ Fin length
  exact
    { toFun := fun position => match position with
        | .inl value => value
        | .inr impossible => PEmpty.elim impossible
      invFun := Sum.inl
      left_inv := by
        intro position
        cases position with
        | inl value => rfl
        | inr impossible => exact PEmpty.elim impossible
      right_inv := fun _ => rfl }

noncomputable instance positionFintypeAt (length : Nat) :
    Fintype (Code.Position code (shapeAt length)) :=
  Code.positionFintype finitary code (shapeAt length)

theorem position_card (length : Nat) :
    Fintype.card (Code.Position code (shapeAt length)) = length := by
  exact (Fintype.card_congr (positionEquiv length)).trans (Fintype.card_fin length)

theorem two_not_equiv_three :
    ¬ Nonempty (Code.Position code (shapeAt 2) ≃
      Code.Position code (shapeAt 3)) := by
  rintro ⟨equivalent⟩
  have same := Fintype.card_congr equivalent
  rw [position_card, position_card] at same
  omega

/-- The generic indexed-output bundle specializes to exactly one motive
witness at every length-indexed vector position. -/
noncomputable def bundleAt {Element : Type} (motive : Element → Type)
    {length : Nat} (values : Fin length → Element) :
    (IndexedContainer.vectorInductionBundle motive).Bundle
        (output := length) ⟨(), values⟩ ≃
      (∀ position : Fin length, motive (values position)) :=
  (IndexedContainer.vectorInductionBundle motive).exact ⟨(), values⟩

#print axioms position_card
#print axioms two_not_equiv_three
#print axioms bundleAt
#print axioms Code.mem_orderedPositions
#print axioms Code.orderedPositions_nodup
#print axioms Code.orderedPositions_length
#print axioms ListInstance.orderedFinitary
#print axioms VectorControl.orderedFinitary
#print axioms Unindexed.signatureEquiv
#print axioms Unindexed.orderedPositions_preserved
#print axioms Unindexed.ordered_observations_preserved
#print axioms Unindexed.blockFamilyEquiv
#print axioms Unindexed.blockRecursor_preserved

end VectorControl

end Mettapedia.TypeTheory.IndexedPositiveContainer
