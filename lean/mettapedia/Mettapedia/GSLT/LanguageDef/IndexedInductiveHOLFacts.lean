import Mettapedia.GSLT.LanguageDef.IndexedInductiveElimination
import Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVec
import Mettapedia.GSLT.LanguageDef.IndexedInductiveNaturalHOL
import Mettapedia.GSLT.LanguageDef.IndexedInductiveExamples
import Mettapedia.GSLT.LanguageDef.CettaWireEquality
import Mettapedia.TypeTheory.NaturalRepresentations
import Mettapedia.Logic.HOL.Semantics.ModelProperties
import Mathlib.Data.Fintype.Card

/-!
# HOL structural facts selected from admitted indexed families

An admitted indexed family has a fixed-point carrier at every parameter
environment.  A selected HOL interpretation represents the tagged total
family by one simple base type.  This module generates three sharply separated
facts about that representation:

* structural recursion into an arbitrary simple result carrier;
* no-confusion for the complete tagged constructor layer;
* Dedekind infinity only when an explicit witness is supplied.

The first two facts follow from the generated polynomial fixed point.  The
third does not: finite admitted families have the same recursion and
no-confusion facts, but cannot supply the infinity witness.  The formulas are
ordinary HOL formulas interpreted in a full-domain model.  Native proof
emission and per-constructor surface names are separate routes.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.Logic.HOL

universe u

variable {I : Interface.{0}} {context : List I.SortCode}

/-- The tagged total carrier of an admitted indexed family at one parameter
environment.  The index remains data; no dependent fibre is silently erased. -/
abbrev Source (admitted : Admitted I context) (environment : Env I.Value context) :=
  Σ index : I.Index, admitted.Family environment index

/-- One complete source constructor layer, including its result index. -/
abbrev Layer (admitted : Admitted I context) (environment : Env I.Value context) :=
  Σ index : I.Index,
    admitted.polynomial.Extension admitted.Family environment index

/-- The same polynomial layer after every recursive child has been mapped to
one simple result carrier. -/
abbrev MappedLayer (admitted : Admitted I context)
    (environment : Env I.Value context) (Result : Type 1) :=
  Σ index : I.Index,
    admitted.polynomial.Extension (fun _ _ => Result) environment index

/-- A selected HOL representation of the tagged family.  Choosing a carrier
does not add laws: it must be equivalent to the actual admitted fixed point. -/
structure Interpretation (admitted : Admitted I context)
    (environment : Env I.Value context) where
  Carrier : Type 1
  sourceEquiv : Source admitted environment ≃ Carrier

namespace Interpretation

variable {admitted : Admitted I context} {environment : Env I.Value context}

/-- Build a tagged family value from one complete polynomial layer. -/
def constructSource (layer : Layer admitted environment) :
    Source admitted environment :=
  ⟨layer.1, Fix.rollExtension admitted.polynomial layer.2⟩

/-- Expose the complete top layer of a tagged family value. -/
def outSource (source : Source admitted environment) :
    Layer admitted environment :=
  ⟨source.1, Fix.out admitted.polynomial source.2⟩

@[simp] theorem outSource_constructSource (layer : Layer admitted environment) :
    outSource (constructSource layer) = layer := by
  rcases layer with ⟨index, layer⟩
  simp [outSource, constructSource]

@[simp] theorem constructSource_outSource (source : Source admitted environment) :
    constructSource (outSource source) = source := by
  rcases source with ⟨index, value⟩
  simp [outSource, constructSource]

theorem constructSource_injective :
    Function.Injective (constructSource (admitted := admitted) (environment := environment)) :=
  Function.LeftInverse.injective outSource_constructSource

/-- The canonical tagged interpretation keeps the total indexed family itself
as the HOL carrier, lifted only to the semantic universe. -/
def tagged (admitted : Admitted I context) (environment : Env I.Value context) :
    Interpretation admitted environment where
  Carrier := ULift.{1} (Source admitted environment)
  sourceEquiv := Equiv.ulift.symm

/-- Change only the chosen HOL carrier representation.  The admitted family,
its indices and its constructor layers remain unchanged. -/
def transport (interpretation : Interpretation admitted environment)
    {Other : Type 1} (equivalence : interpretation.Carrier ≃ Other) :
    Interpretation admitted environment where
  Carrier := Other
  sourceEquiv := interpretation.sourceEquiv.trans equivalence

/-- Transport along the identity representation leaves the selected
interpretation unchanged. -/
@[simp] theorem transport_refl
    (interpretation : Interpretation admitted environment) :
    interpretation.transport (Equiv.refl interpretation.Carrier) =
      interpretation := by
  rcases interpretation with ⟨Carrier, sourceEquiv⟩
  rfl

/-- Changing carrier twice is the same selected interpretation as changing it
along the composite equivalence.  This is the path-composition law for the
representation vine. -/
@[simp] theorem transport_trans
    (interpretation : Interpretation admitted environment)
    {Middle Other : Type 1}
    (first : interpretation.Carrier ≃ Middle) (second : Middle ≃ Other) :
    (interpretation.transport first).transport second =
      interpretation.transport (first.trans second) := by
  rfl

/-- Changing representation and immediately changing back recovers the
selected interpretation. -/
@[simp] theorem transport_symm
    (interpretation : Interpretation admitted environment)
    {Other : Type 1} (equivalence : interpretation.Carrier ≃ Other) :
    (interpretation.transport equivalence).transport equivalence.symm =
      interpretation := by
  rw [transport_trans]
  simp

/-- The constructor layer in the selected HOL carrier. -/
def construct (interpretation : Interpretation admitted environment)
    (layer : Layer admitted environment) : interpretation.Carrier :=
  interpretation.sourceEquiv (constructSource layer)

@[simp] theorem transport_construct
    (interpretation : Interpretation admitted environment)
    {Other : Type 1} (equivalence : interpretation.Carrier ≃ Other)
    (layer : Layer admitted environment) :
    (interpretation.transport equivalence).construct layer =
      equivalence (interpretation.construct layer) := rfl

theorem construct_injective (interpretation : Interpretation admitted environment) :
    Function.Injective interpretation.construct :=
  interpretation.sourceEquiv.injective.comp constructSource_injective

/-- Different authored constructor occurrences remain disjoint after the
selected carrier representation. -/
theorem construct_ne_of_occurrence_ne
    (interpretation : Interpretation admitted environment)
    (first second : Layer admitted environment)
    (different : first.2.1.1 ≠ second.2.1.1) :
    interpretation.construct first ≠ interpretation.construct second := by
  intro same
  exact different (congrArg (fun layer : Layer admitted environment => layer.2.1.1)
    (interpretation.construct_injective same))

/-- Replace every recursive source child by the result of a candidate fold. -/
def mapLayer (interpretation : Interpretation admitted environment)
    {Result : Type 1} (function : interpretation.Carrier → Result)
    (layer : Layer admitted environment) : MappedLayer admitted environment Result :=
  ⟨layer.1, Extension.map admitted.polynomial
    (fun _ index child => function (interpretation.sourceEquiv ⟨index, child⟩)) layer.2⟩

@[simp] theorem transport_mapLayer
    (interpretation : Interpretation admitted environment)
    {Other : Type 1} (equivalence : interpretation.Carrier ≃ Other)
    {Result : Type 1} (function : Other → Result)
    (layer : Layer admitted environment) :
    (interpretation.transport equivalence).mapLayer function layer =
      interpretation.mapLayer (function ∘ equivalence) layer := rfl

/-- The generated structural fold, transported through the selected carrier
equivalence. -/
noncomputable def recurseSource (_interpretation : Interpretation admitted environment)
    {Result : Type 1} (algebra : MappedLayer admitted environment Result → Result) :
    ∀ index, admitted.Family environment index → Result :=
  @Fix.rec (Env I.Value context) (fun _ => I.Index) admitted.polynomial environment
    (fun _ _ => Result)
    (fun {index} shape _children hypotheses => algebra ⟨index, ⟨shape, hypotheses⟩⟩)

noncomputable def recurse (interpretation : Interpretation admitted environment)
    {Result : Type 1} (algebra : MappedLayer admitted environment Result → Result)
    (source : interpretation.Carrier) : Result :=
  let decoded := interpretation.sourceEquiv.symm source
  interpretation.recurseSource algebra decoded.1 decoded.2

@[simp] theorem transport_recurse
    (interpretation : Interpretation admitted environment)
    {Other : Type 1} (equivalence : interpretation.Carrier ≃ Other)
    {Result : Type 1} (algebra : MappedLayer admitted environment Result → Result)
    (source : interpretation.Carrier) :
    (interpretation.transport equivalence).recurse algebra (equivalence source) =
      interpretation.recurse algebra source := by
  unfold recurse
  change interpretation.recurseSource algebra
      ((interpretation.sourceEquiv.trans equivalence).symm (equivalence source)).1
      ((interpretation.sourceEquiv.trans equivalence).symm (equivalence source)).2 =
    interpretation.recurseSource algebra
      (interpretation.sourceEquiv.symm source).1
      (interpretation.sourceEquiv.symm source).2
  have decoded :
      (interpretation.sourceEquiv.trans equivalence).symm (equivalence source) =
        interpretation.sourceEquiv.symm source := by simp
  exact congrArg
    (fun decoded => interpretation.recurseSource algebra decoded.1 decoded.2) decoded

@[simp] theorem recurse_sourceEquiv
    (interpretation : Interpretation admitted environment)
    {Result : Type 1} (algebra : MappedLayer admitted environment Result → Result)
    (source : Source admitted environment) :
    interpretation.recurse algebra (interpretation.sourceEquiv source) =
      interpretation.recurseSource algebra source.1 source.2 := by
  unfold recurse
  rw [interpretation.sourceEquiv.symm_apply_apply]

@[simp] theorem recurse_construct (interpretation : Interpretation admitted environment)
    {Result : Type 1} (algebra : MappedLayer admitted environment Result → Result)
    (layer : Layer admitted environment) :
    interpretation.recurse algebra (interpretation.construct layer) =
      algebra (interpretation.mapLayer (interpretation.recurse algebra) layer) := by
  rcases layer with ⟨index, shape, children⟩
  simp [construct, constructSource, mapLayer, recurseSource,
    Fix.rollExtension, Extension.map]

/-- The constructor equations determine the transported fold uniquely. -/
theorem recurse_unique (interpretation : Interpretation admitted environment)
    {Result : Type 1} (algebra : MappedLayer admitted environment Result → Result)
    (candidate : interpretation.Carrier → Result)
    (equations : ∀ layer, candidate (interpretation.construct layer) =
      algebra (interpretation.mapLayer candidate layer)) :
    candidate = interpretation.recurse algebra := by
  have pointwise : ∀ index (value : admitted.Family environment index),
      candidate (interpretation.sourceEquiv ⟨index, value⟩) =
        interpretation.recurseSource algebra index value :=
    @Fix.rec (Env I.Value context) (fun _ => I.Index) admitted.polynomial environment
      (fun index value => candidate (interpretation.sourceEquiv ⟨index, value⟩) =
        interpretation.recurseSource algebra index value)
      (fun {index} shape children hypotheses => by
      change candidate (interpretation.construct ⟨index, ⟨shape, children⟩⟩) = _
      rw [equations]
      change algebra ⟨index, ⟨shape, fun position =>
          candidate (interpretation.sourceEquiv ⟨_, children position⟩)⟩⟩ =
        algebra ⟨index, ⟨shape, fun position =>
          interpretation.recurseSource algebra _ (children position)⟩⟩
      congr 3
      funext position
      exact hypotheses position)
  funext source
  let decoded := interpretation.sourceEquiv.symm source
  calc
    candidate source = candidate (interpretation.sourceEquiv decoded) :=
      congrArg candidate (interpretation.sourceEquiv.apply_symm_apply source).symm
    _ = interpretation.recurseSource algebra decoded.1 decoded.2 :=
      pointwise decoded.1 decoded.2
    _ = interpretation.recurse algebra source := by rfl

end Interpretation

/-! ## Intrinsic HOL formulas -/

inductive Base where
  | source
  | layer
  | mappedLayer
  | result
  deriving DecidableEq, Repr

abbrev sourceTy : Ty Base := .base .source
abbrev layerTy : Ty Base := .base .layer
abbrev mappedLayerTy : Ty Base := .base .mappedLayer
abbrev resultTy : Ty Base := .base .result

inductive Const : Ty Base → Type where
  | construct : Const (layerTy ⇒ sourceTy)
  | mapLayer : Const ((sourceTy ⇒ resultTy) ⇒ layerTy ⇒ mappedLayerTy)
  | allChildren : Const ((sourceTy ⇒ .prop) ⇒ layerTy ⇒ .prop)
  deriving DecidableEq, Repr

/-- A fold equation for one quantified algebra and candidate function. -/
def recursionEquation {Γ : Ctx Base}
    (algebra : Term Const Γ (mappedLayerTy ⇒ resultTy))
    (function : Term Const Γ (sourceTy ⇒ resultTy)) : Formula Const Γ :=
  .all (σ := layerTy)
    (.eq (.app (weaken function) (.app (.const .construct) (.var .vz)))
      (.app (weaken algebra)
        (.app (.app (.const .mapLayer) (weaken function)) (.var .vz))))

/-- Every algebra on mapped constructor layers has a structural fold. -/
def recursion : ClosedFormula Const :=
  .all (σ := mappedLayerTy ⇒ resultTy)
    (.ex (σ := sourceTy ⇒ resultTy)
      (recursionEquation (.var (.vs .vz)) (.var .vz)))

/-- One predicate is closed under every complete constructor layer. -/
def inductionClosure {Γ : Ctx Base}
    (predicate : Term Const Γ (sourceTy ⇒ .prop)) : Formula Const Γ :=
  .all (σ := layerTy)
    (.imp (.app (.app (.const .allChildren) (weaken predicate)) (.var .vz))
      (.app (weaken predicate) (.app (.const .construct) (.var .vz))))

/-- Constructor closure implies the predicate for every value of the selected
carrier. -/
def induction : ClosedFormula Const :=
  .all (σ := sourceTy ⇒ .prop)
    (.imp (inductionClosure (.var .vz))
      (.all (σ := sourceTy) (.app (weaken (.var .vz)) (.var .vz))))

/-- The complete tagged constructor-layer map is injective.  The reverse
direction is congruence, so the Boolean equality retains both directions. -/
def noConfusion : ClosedFormula Const :=
  .all (σ := layerTy) (.all (σ := layerTy)
    (.eq
      (.eq (.app (.const .construct) (.var (.vs .vz)))
        (.app (.const .construct) (.var .vz)))
      (.eq (.var (.vs .vz)) (.var .vz))))

/-- Dedekind infinity of the selected carrier.  This is not generated from
admission alone. -/
def infinity : ClosedFormula Const :=
  .ex (σ := sourceTy ⇒ sourceTy)
    (.and (.all (σ := sourceTy) (.all (σ := sourceTy)
      (.imp (.eq (.app (.var (.vs (.vs .vz))) (.var (.vs .vz)))
          (.app (.var (.vs (.vs .vz))) (.var .vz)))
        (.eq (.var (.vs .vz)) (.var .vz)))))
      (.ex (σ := sourceTy) (.all (σ := sourceTy)
        (.not (.eq (.app (.var (.vs (.vs .vz))) (.var .vz))
          (.var (.vs .vz)))))))

abbrev LayerDen {admitted : Admitted I context} {environment : Env I.Value context} :=
  ULift.{1} (Layer admitted environment)

abbrev MappedLayerDen {admitted : Admitted I context} {environment : Env I.Value context}
    (Result : Type 1) := ULift.{1, 1} (MappedLayer admitted environment Result)

def constructDen {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) :
    LayerDen (admitted := admitted) (environment := environment) → interpretation.Carrier :=
  fun layer => interpretation.construct layer.down

def mapLayerDen {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) {Result : Type 1} :
    (interpretation.Carrier → Result) →
      LayerDen (admitted := admitted) (environment := environment) →
        MappedLayerDen (admitted := admitted) (environment := environment) Result :=
  fun function layer => ⟨interpretation.mapLayer function layer.down⟩

def allChildrenDen {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) :
    (interpretation.Carrier → ULift.{1} Prop) →
      LayerDen (admitted := admitted) (environment := environment) → ULift.{1} Prop :=
  fun predicate layer =>
    ⟨∀ position : admitted.polynomial.Position layer.down.2.1,
      (predicate (interpretation.sourceEquiv
        ⟨admitted.polynomial.next layer.down.2.1 position,
          layer.down.2.2 position⟩)).down⟩

def carrier {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) (Result : Type 1) :
    Base → Type 1
  | .source => interpretation.Carrier
  | .layer => LayerDen (admitted := admitted) (environment := environment)
  | .mappedLayer => MappedLayerDen (admitted := admitted) (environment := environment) Result
  | .result => Result

def constants {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) (Result : Type 1) :
    {type : Ty Base} → Const type → Ty.denote.{0, 0} (carrier interpretation Result) type
  | _, .construct => constructDen interpretation
  | _, .mapLayer => mapLayerDen interpretation
  | _, .allChildren => allChildrenDen interpretation

/-- The full-domain HOL model selected by one admitted family representation
and one result carrier. -/
def model {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) (Result : Type 1) :
    HenkinModel.{0, 0, 0} Base Const :=
  .standard (carrier interpretation Result) (constants interpretation Result)

theorem recursion_meaning
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) (Result : Type 1) :
    (model interpretation Result).models recursion ↔
      ∀ algebra : MappedLayerDen (admitted := admitted) (environment := environment) Result → Result,
        ∃ function : interpretation.Carrier → Result,
          ∀ layer, function (constructDen interpretation layer) =
            algebra (mapLayerDen interpretation function layer) := by
  constructor
  · intro valid algebra
    obtain ⟨function, _, equations⟩ := valid algebra trivial
    exact ⟨function, fun layer => equations layer trivial⟩
  · intro valid algebra _
    obtain ⟨function, equations⟩ := valid algebra
    exact ⟨function, trivial, fun layer _ => equations layer⟩

def ChildrenHold
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment)
    (predicate : interpretation.Carrier → Prop)
    (layer : Layer admitted environment) : Prop :=
  ∀ position : admitted.polynomial.Position layer.2.1,
    predicate (interpretation.sourceEquiv
      ⟨admitted.polynomial.next layer.2.1 position, layer.2.2 position⟩)

theorem induction_meaning
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) (Result : Type 1) :
    (model interpretation Result).models induction ↔
      ∀ predicate : interpretation.Carrier → Prop,
        (∀ layer, ChildrenHold interpretation predicate layer →
          predicate (interpretation.construct layer)) →
        ∀ source, predicate source := by
  constructor
  · intro valid predicate closed source
    exact valid (fun value => ⟨predicate value⟩) trivial
      (fun layer _ children => closed layer.down children) source trivial
  · intro valid predicate _ closed source _
    exact valid (fun value => (predicate value).down)
      (fun layer children => closed ⟨layer⟩ trivial children) source

theorem noConfusion_meaning
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) (Result : Type 1) :
    (model interpretation Result).models noConfusion ↔
      Function.Injective (constructDen interpretation) := by
  constructor
  · exact fun valid first second same => (valid first trivial second trivial).mp same
  · intro injective first _ second _
    exact ⟨fun same => injective same, fun same => congrArg (constructDen interpretation) same⟩

/-- The evidence required before infinity may enter an export manifest. -/
structure InfinityWitness (Carrier : Type 1) where
  successor : Carrier → Carrier
  successor_injective : Function.Injective successor
  omitted : Carrier
  omitted_not_image : ∀ value, successor value ≠ omitted

def InfinityWitness.transport {Carrier Other : Type 1}
    (witness : InfinityWitness Carrier) (equivalence : Carrier ≃ Other) :
    InfinityWitness Other where
  successor value := equivalence (witness.successor (equivalence.symm value))
  successor_injective := by
    intro first second same
    exact equivalence.symm.injective
      (witness.successor_injective (equivalence.injective same))
  omitted := equivalence witness.omitted
  omitted_not_image := by
    intro value same
    exact witness.omitted_not_image (equivalence.symm value) (equivalence.injective same)

@[simp] theorem InfinityWitness.transport_refl {Carrier : Type 1}
    (witness : InfinityWitness Carrier) :
    witness.transport (Equiv.refl Carrier) = witness := by
  rfl

/-- Dedekind-infinity evidence follows the same composite path as its carrier.
The proposition-valued proof fields are irrelevant to this equality; the
successor and omitted point are transported extensionally. -/
theorem InfinityWitness.transport_trans {Carrier Middle Other : Type 1}
    (witness : InfinityWitness Carrier) (first : Carrier ≃ Middle)
    (second : Middle ≃ Other) :
    (witness.transport first).transport second =
      witness.transport (first.trans second) := by
  rfl

@[simp] theorem InfinityWitness.transport_symm {Carrier Other : Type 1}
    (witness : InfinityWitness Carrier) (equivalence : Carrier ≃ Other) :
    (witness.transport equivalence).transport equivalence.symm = witness := by
  rw [InfinityWitness.transport_trans]
  simp

theorem infinity_meaning
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) (Result : Type 1) :
    (model interpretation Result).models infinity ↔
      Nonempty (InfinityWitness interpretation.Carrier) := by
  constructor
  · rintro ⟨successor, _, injective, omitted, _, omitted_not_image⟩
    exact ⟨⟨successor, fun first second same => injective first trivial second trivial same,
      omitted, fun value => omitted_not_image value trivial⟩⟩
  · rintro ⟨witness⟩
    exact ⟨witness.successor, trivial,
      (fun first _ second _ same => witness.successor_injective same),
      witness.omitted, trivial, fun value _ => witness.omitted_not_image value⟩

theorem models_recursion
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) (Result : Type 1) :
    (model interpretation Result).models recursion := by
  apply (recursion_meaning interpretation Result).mpr
  intro algebra
  let rawAlgebra : MappedLayer admitted environment Result → Result :=
    fun layer => algebra ⟨layer⟩
  refine ⟨interpretation.recurse rawAlgebra, ?_⟩
  intro layer
  exact interpretation.recurse_construct rawAlgebra layer.down

theorem models_induction
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) (Result : Type 1) :
    (model interpretation Result).models induction := by
  apply (induction_meaning interpretation Result).mpr
  intro predicate closed source
  let decoded := interpretation.sourceEquiv.symm source
  have every : ∀ index (value : admitted.Family environment index),
      predicate (interpretation.sourceEquiv ⟨index, value⟩) :=
    @Fix.rec (Env I.Value context) (fun _ => I.Index) admitted.polynomial environment
      (fun index value => predicate (interpretation.sourceEquiv ⟨index, value⟩))
      (fun {index} shape children hypotheses =>
        closed ⟨index, ⟨shape, children⟩⟩ hypotheses)
  exact interpretation.sourceEquiv.apply_symm_apply source ▸ every decoded.1 decoded.2

theorem models_noConfusion
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) (Result : Type 1) :
    (model interpretation Result).models noConfusion :=
  (noConfusion_meaning interpretation Result).mpr (by
    intro first second same
    apply ULift.ext
    exact interpretation.construct_injective same)

theorem models_infinity
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) (Result : Type 1)
    (witness : InfinityWitness interpretation.Carrier) :
    (model interpretation Result).models infinity :=
  (infinity_meaning interpretation Result).mpr ⟨witness⟩

/-! ## Exact export selection -/

inductive Fact where
  | structuralRecursion
  | structuralInduction
  | constructorNoConfusion
  | carrierInfinity
  deriving DecidableEq, Repr

def formula : Fact → ClosedFormula Const
  | .structuralRecursion => recursion
  | .structuralInduction => induction
  | .constructorNoConfusion => noConfusion
  | .carrierInfinity => infinity

/-- Structural facts are always selected.  Infinity appears exactly when its
separate witness is present. -/
structure Selection {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) where
  infinityWitness? : Option (InfinityWitness interpretation.Carrier)

def Selection.transport
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) {Other : Type 1}
    (equivalence : interpretation.Carrier ≃ Other) :
    Selection (interpretation.transport equivalence) where
  infinityWitness? := selection.infinityWitness?.map (·.transport equivalence)

/-- The infinity evidence retained by a selection is transported coherently
with composition of carrier equivalences. -/
@[simp] theorem Selection.transport_trans_witness
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) {Middle Other : Type 1}
    (first : interpretation.Carrier ≃ Middle) (second : Middle ≃ Other) :
    ((selection.transport first).transport second).infinityWitness? =
      (selection.transport (first.trans second)).infinityWitness? := by
  rcases selection with ⟨witness?⟩
  cases witness? with
  | none => rfl
  | some witness =>
      exact congrArg some (InfinityWitness.transport_trans witness first second)

@[simp] theorem Selection.transport_refl_witness
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) :
    (selection.transport (Equiv.refl interpretation.Carrier)).infinityWitness? =
      selection.infinityWitness? := by
  rcases selection with ⟨witness?⟩
  cases witness? <;> rfl

@[simp] theorem Selection.transport_symm_witness
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) {Other : Type 1}
    (equivalence : interpretation.Carrier ≃ Other) :
    ((selection.transport equivalence).transport equivalence.symm).infinityWitness? =
      selection.infinityWitness? := by
  rcases selection with ⟨witness?⟩
  cases witness? with
  | none => rfl
  | some witness =>
      exact congrArg some (InfinityWitness.transport_symm witness equivalence)

def Selection.facts
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) : List Fact :=
  [.structuralRecursion, .structuralInduction, .constructorNoConfusion] ++
    match selection.infinityWitness? with
    | none => []
    | some _ => [.carrierInfinity]

@[simp] theorem Selection.structuralRecursion_mem
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) :
    Fact.structuralRecursion ∈ selection.facts := by
  simp [Selection.facts]

@[simp] theorem Selection.constructorNoConfusion_mem
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) :
    Fact.constructorNoConfusion ∈ selection.facts := by
  simp [Selection.facts]

@[simp] theorem Selection.structuralInduction_mem
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) :
    Fact.structuralInduction ∈ selection.facts := by
  simp [Selection.facts]

theorem Selection.carrierInfinity_mem_iff
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) :
    Fact.carrierInfinity ∈ selection.facts ↔
      selection.infinityWitness?.isSome = true := by
  cases found : selection.infinityWitness? <;> simp [Selection.facts, found]

theorem Selection.transport_facts
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) {Other : Type 1}
    (equivalence : interpretation.Carrier ≃ Other) :
    (selection.transport equivalence).facts = selection.facts := by
  cases found : selection.infinityWitness? <;>
    simp [Selection.transport, Selection.facts, found]

theorem Selection.models_of_mem
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) (Result : Type 1)
    {fact : Fact} (member : fact ∈ selection.facts) :
    (model interpretation Result).models (formula fact) := by
  cases fact with
  | structuralRecursion => exact models_recursion interpretation Result
  | structuralInduction => exact models_induction interpretation Result
  | constructorNoConfusion => exact models_noConfusion interpretation Result
  | carrierInfinity =>
      cases hw : selection.infinityWitness? with
      | none => simp [Selection.facts, hw] at member
      | some actual => exact models_infinity interpretation Result actual

theorem no_infinityWitness_of_finite (Carrier : Type 1) [Finite Carrier] :
    ¬ Nonempty (InfinityWitness Carrier) := by
  rintro ⟨witness⟩
  obtain ⟨source, same⟩ :=
    Finite.surjective_of_injective witness.successor_injective witness.omitted
  exact witness.omitted_not_image source same

theorem Selection.infinity_not_selected_of_finite
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    [Finite interpretation.Carrier] (selection : Selection interpretation) :
    Fact.carrierInfinity ∉ selection.facts := by
  intro member
  cases hw : selection.infinityWitness? with
  | none => simp [Selection.facts, hw] at member
  | some actual =>
      exact no_infinityWitness_of_finite interpretation.Carrier ⟨actual⟩

/-! ## Native statement coding for structural facts -/

namespace WireCatalog

abbrev Wire := Mettapedia.Languages.HOLLight.HOLSyntaxWire.Wire

/-- Decode against a finite emitted catalog.  The first matching wire wins,
so an injectivity premise is required for encode/decode roundtrips. -/
def decode? {α : Type} (encode : α → Wire) : List α → Wire → Option α
  | [], _ => none
  | head :: tail, wire =>
      if encode head = wire then some head else decode? encode tail wire

theorem decode_encode {α : Type} (encode : α → Wire)
    (injective : Function.Injective encode) {items : List α} {item : α}
    (member : item ∈ items) :
    decode? encode items (encode item) = some item := by
  induction items with
  | nil => simp at member
  | cons head tail hypothesis =>
      rcases List.mem_cons.mp member with rfl | member
      · simp [decode?]
      · by_cases same : encode head = encode item
        · have equal : head = item := injective same
          subst head
          simp [decode?]
        · simp [decode?, same, hypothesis member]

theorem decode_sound {α : Type} (encode : α → Wire)
    {items : List α} {wire : Wire} {item : α}
    (decoded : decode? encode items wire = some item) :
    item ∈ items ∧ encode item = wire := by
  induction items with
  | nil => simp [decode?] at decoded
  | cons head tail hypothesis =>
      by_cases same : encode head = wire
      · simp [decode?, same] at decoded
        subst item
        exact ⟨List.mem_cons_self, same⟩
      · simp [decode?, same] at decoded
        obtain ⟨member, encoded⟩ := hypothesis decoded
        exact ⟨List.mem_cons_of_mem _ member, encoded⟩

theorem decode_none_of_absent {α : Type} (encode : α → Wire)
    {items : List α} {wire : Wire}
    (absent : ∀ item ∈ items, encode item ≠ wire) :
    decode? encode items wire = none := by
  induction items with
  | nil => rfl
  | cons head tail hypothesis =>
      simp only [List.mem_cons] at absent
      simp [decode?, absent head (Or.inl rfl),
        hypothesis (fun item member => absent item (Or.inr member))]

end WireCatalog

namespace NativeWire

open Mettapedia.Languages.HOLLight.HOLSyntaxWire

structure StructuralNames where
  sourceType : String
  layerType : String
  mappedLayerType : String
  resultType : String
  construct : String
  mapLayer : String
  allChildren : String

def baseWire (names : StructuralNames) : Base → Wire
  | .source => .application "T" [.string names.sourceType]
  | .layer => .application "T" [.string names.layerType]
  | .mappedLayer => .application "T" [.string names.mappedLayerType]
  | .result => .application "T" [.string names.resultType]

def constantWire (names : StructuralNames) : {type : Ty Base} → Const type → Wire
  | _, .construct => constant names.construct
      (encodeType (baseWire names) (layerTy ⇒ sourceTy))
  | _, .mapLayer => constant names.mapLayer
      (encodeType (baseWire names) ((sourceTy ⇒ resultTy) ⇒ layerTy ⇒ mappedLayerTy))
  | _, .allChildren => constant names.allChildren
      (encodeType (baseWire names) ((sourceTy ⇒ .prop) ⇒ layerTy ⇒ .prop))

def binderName (depth : Nat) : String := "v" ++ toString depth

def closedNames : Mettapedia.Logic.HOL.Names ([] : Ctx Base) :=
  fun {_type} index => nomatch index

def statement (names : StructuralNames) (fact : Fact) : Wire :=
  encodeTerm (baseWire names) (constantWire names) binderName closedNames 0 (formula fact)

structure EmittedFact where
  source : Fact
  statement : Wire

def Selection.emit
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) (names : StructuralNames) : List EmittedFact :=
  selection.facts.map fun fact => ⟨fact, statement names fact⟩

theorem Selection.emit_sources
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) (names : StructuralNames) :
    (Selection.emit selection names).map EmittedFact.source = selection.facts := by
  simp [Selection.emit, Function.comp_def]

theorem Selection.emit_source_models
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) (names : StructuralNames) (Result : Type 1)
    {fact : EmittedFact} (member : fact ∈ Selection.emit selection names) :
    (model interpretation Result).models (formula fact.source) := by
  apply selection.models_of_mem Result
  rw [← Selection.emit_sources selection names]
  exact List.mem_map_of_mem member

def Selection.decode?
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) (names : StructuralNames)
    (wire : Wire) : Option Fact :=
  WireCatalog.decode? (statement names) selection.facts wire

theorem Selection.decode_statement
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) (names : StructuralNames)
    (injective : Function.Injective (statement names))
    {fact : Fact} (member : fact ∈ selection.facts) :
    Selection.decode? selection names (statement names fact) = some fact :=
  WireCatalog.decode_encode (statement names) injective member

theorem Selection.decode_sound
    {admitted : Admitted I context} {environment : Env I.Value context}
    {interpretation : Interpretation admitted environment}
    (selection : Selection interpretation) (names : StructuralNames)
    {wire : Wire} {fact : Fact}
    (decoded : Selection.decode? selection names wire = some fact) :
    fact ∈ selection.facts ∧ statement names fact = wire :=
  WireCatalog.decode_sound (statement names) decoded

end NativeWire

/-! ## Named constructor-separation projections -/

namespace ConstructorProjection

open Mettapedia.Languages.HOLLight.HOLSyntaxWire

inductive ProjectionBase (count : Nat) where
  | source
  | layer
  | occurrence
  deriving DecidableEq, Repr

abbrev projectedSourceTy {count : Nat} : Ty (ProjectionBase count) := .base .source
abbrev projectedLayerTy {count : Nat} : Ty (ProjectionBase count) := .base .layer
abbrev occurrenceTy {count : Nat} : Ty (ProjectionBase count) := .base .occurrence

inductive ProjectionConst (count : Nat) : Ty (ProjectionBase count) → Type where
  | construct : ProjectionConst count (projectedLayerTy ⇒ projectedSourceTy)
  | tag : ProjectionConst count (projectedLayerTy ⇒ occurrenceTy)
  | occurrence (index : Fin count) : ProjectionConst count occurrenceTy
  deriving DecidableEq, Repr

/-- Separation of two named constructor occurrences, stated over complete
layers so every data and recursive field remains present. -/
def separation {count : Nat} (first second : Fin count) :
    ClosedFormula (ProjectionConst count) :=
  .all (σ := projectedLayerTy) (.all (σ := projectedLayerTy)
    (.imp
      (.and
        (.eq (.app (.const .tag) (.var (.vs .vz))) (.const (.occurrence first)))
        (.eq (.app (.const .tag) (.var .vz)) (.const (.occurrence second))))
      (.not (.eq (.app (.const .construct) (.var (.vs .vz)))
        (.app (.const .construct) (.var .vz))))))

def projectionCarrier
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) :
    ProjectionBase admitted.constructors.length → Type 1
  | .source => interpretation.Carrier
  | .layer => LayerDen (admitted := admitted) (environment := environment)
  | .occurrence => ULift.{1} (Fin admitted.constructors.length)

def tagDen {admitted : Admitted I context} {environment : Env I.Value context}
    (layer : LayerDen (admitted := admitted) (environment := environment)) :
    ULift.{1} (Fin admitted.constructors.length) :=
  ⟨layer.down.2.1.1⟩

def projectionConstants
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) :
    {type : Ty (ProjectionBase admitted.constructors.length)} →
      ProjectionConst admitted.constructors.length type →
        Ty.denote.{0, 0} (projectionCarrier interpretation) type
  | _, .construct => constructDen interpretation
  | _, .tag => tagDen
  | _, .occurrence index => ⟨index⟩

def projectionModel
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment) :
    HenkinModel.{0, 0, 0} (ProjectionBase admitted.constructors.length)
      (ProjectionConst admitted.constructors.length) :=
  .standard (projectionCarrier interpretation) (projectionConstants interpretation)

theorem separation_meaning
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment)
    (first second : Fin admitted.constructors.length) :
    (projectionModel interpretation).models (separation first second) ↔
      ∀ left right : LayerDen (admitted := admitted) (environment := environment),
        left.down.2.1.1 = first → right.down.2.1.1 = second →
          constructDen interpretation left ≠ constructDen interpretation right := by
  constructor
  · intro valid left right leftTag rightTag same
    exact valid left trivial right trivial
      ⟨ULift.ext _ _ leftTag, ULift.ext _ _ rightTag⟩ same
  · intro valid left _ right _ tags same
    exact valid left right (congrArg ULift.down tags.1)
      (congrArg ULift.down tags.2) same

theorem models_separation
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment)
    (first second : Fin admitted.constructors.length) (different : first ≠ second) :
    (projectionModel interpretation).models (separation first second) := by
  apply (separation_meaning interpretation first second).mpr
  intro left right leftTag rightTag same
  have layers : left.down = right.down := interpretation.construct_injective same
  have occurrences := congrArg
    (fun layer : Layer admitted environment => layer.2.1.1) layers
  exact different (leftTag.symm.trans (occurrences.trans rightTag))

structure DistinctPair (count : Nat) where
  first : Fin count
  second : Fin count
  different : first ≠ second
  deriving DecidableEq

/-- Enumerate every ordered pair of distinct constructor occurrences. -/
def allDistinctPairs (count : Nat) : List (DistinctPair count) :=
  (List.ofFn fun index : Fin count => index).flatMap fun first =>
    (List.ofFn fun index : Fin count => index).filterMap fun second =>
      if different : first ≠ second then some ⟨first, second, different⟩ else none

structure NamedFormula (count : Nat) where
  name : String × String
  formula : ClosedFormula (ProjectionConst count)

def namedNoConfusion
    (admitted : Admitted I context)
    (pair : DistinctPair admitted.constructors.length) :
    NamedFormula admitted.constructors.length where
  name := ((admitted.constructors.get pair.first).name,
    (admitted.constructors.get pair.second).name)
  formula := separation pair.first pair.second

def namedNoConfusions (admitted : Admitted I context) :
    List (NamedFormula admitted.constructors.length) :=
  (allDistinctPairs admitted.constructors.length).map (namedNoConfusion admitted)

theorem namedNoConfusion_models
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment)
    (pair : DistinctPair admitted.constructors.length) :
    (projectionModel interpretation).models (namedNoConfusion admitted pair).formula :=
  models_separation interpretation pair.first pair.second pair.different

theorem namedNoConfusions_models
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment)
    {fact : NamedFormula admitted.constructors.length}
    (member : fact ∈ namedNoConfusions admitted) :
    (projectionModel interpretation).models fact.formula := by
  obtain ⟨pair, _, rfl⟩ := List.mem_map.mp member
  exact namedNoConfusion_models interpretation pair

/-! ### Native statement coding -/

structure WireNames (count : Nat) where
  sourceType : String
  layerType : String
  occurrenceType : String
  construct : String
  tag : String
  occurrence : Fin count → String

def baseWire {count : Nat} (names : WireNames count) : ProjectionBase count → Wire
  | .source => .application "T" [.string names.sourceType]
  | .layer => .application "T" [.string names.layerType]
  | .occurrence => .application "T" [.string names.occurrenceType]

def constantWire {count : Nat} (names : WireNames count) :
    {type : Ty (ProjectionBase count)} → ProjectionConst count type → Wire
  | _, .construct => constant names.construct
      (encodeType (baseWire names) (projectedLayerTy ⇒ projectedSourceTy))
  | _, .tag => constant names.tag
      (encodeType (baseWire names) (projectedLayerTy ⇒ occurrenceTy))
  | _, .occurrence index => constant (names.occurrence index)
      (encodeType (baseWire names) occurrenceTy)

def binderName : Nat → String
  | 0 => "rightLayer"
  | 1 => "leftLayer"
  | depth => "layer" ++ toString depth

def closedNames {count : Nat} : Names ([] : Ctx (ProjectionBase count)) :=
  fun {_type} index => nomatch index

def statement {count : Nat} (names : WireNames count) (pair : DistinctPair count) : Wire :=
  encodeTerm (baseWire names) (constantWire names) binderName closedNames 0
    (separation pair.first pair.second)

structure EmittedFact (count : Nat) where
  source : NamedFormula count
  statement : Wire

def emitPair (admitted : Admitted I context)
    (names : WireNames admitted.constructors.length)
    (pair : DistinctPair admitted.constructors.length) :
    EmittedFact admitted.constructors.length where
  source := namedNoConfusion admitted pair
  statement := statement names pair

def emitAll (admitted : Admitted I context)
    (names : WireNames admitted.constructors.length) :
    List (EmittedFact admitted.constructors.length) :=
  (allDistinctPairs admitted.constructors.length).map (emitPair admitted names)

/-- Coding preserves the complete source inventory and order exactly. -/
theorem emitAll_sources (admitted : Admitted I context)
    (names : WireNames admitted.constructors.length) :
    (emitAll admitted names).map EmittedFact.source = namedNoConfusions admitted := by
  simp [emitAll, emitPair, namedNoConfusions, Function.comp_def]

theorem emitAll_source_models
    {admitted : Admitted I context} {environment : Env I.Value context}
    (interpretation : Interpretation admitted environment)
    (names : WireNames admitted.constructors.length)
    {fact : EmittedFact admitted.constructors.length}
    (member : fact ∈ emitAll admitted names) :
    (projectionModel interpretation).models fact.source.formula := by
  have sourceMember : fact.source ∈ namedNoConfusions admitted := by
    rw [← emitAll_sources admitted names]
    exact List.mem_map_of_mem member
  exact namedNoConfusions_models interpretation sourceMember

def decodePair? (admitted : Admitted I context)
    (names : WireNames admitted.constructors.length) (wire : Wire) :
    Option (DistinctPair admitted.constructors.length) :=
  WireCatalog.decode? (statement names)
    (allDistinctPairs admitted.constructors.length) wire

theorem decodePair_statement (admitted : Admitted I context)
    (names : WireNames admitted.constructors.length)
    (injective : Function.Injective (statement names))
    {pair : DistinctPair admitted.constructors.length}
    (member : pair ∈ allDistinctPairs admitted.constructors.length) :
    decodePair? admitted names (statement names pair) = some pair :=
  WireCatalog.decode_encode (statement names) injective member

theorem decodePair_sound (admitted : Admitted I context)
    (names : WireNames admitted.constructors.length) {wire : Wire}
    {pair : DistinctPair admitted.constructors.length}
    (decoded : decodePair? admitted names wire = some pair) :
    pair ∈ allDistinctPairs admitted.constructors.length ∧
      statement names pair = wire :=
  WireCatalog.decode_sound (statement names) decoded

end ConstructorProjection

/-! ## The authored natural-family control -/

namespace NaturalControl

open IndexedInductiveNatVec
open Mettapedia.TypeTheory.NaturalRepresentations

def sourceEquiv : Source Natural.admitted PUnit.unit ≃ ULift.{1} Natural.Carrier where
  toFun source := ⟨source.2⟩
  invFun value := ⟨(), value.down⟩
  left_inv source := by rcases source with ⟨index, value⟩; cases index; rfl
  right_inv _ := rfl

def interpretation : Interpretation Natural.admitted PUnit.unit where
  Carrier := ULift.{1} Natural.Carrier
  sourceEquiv := sourceEquiv

def infinityWitness : InfinityWitness interpretation.Carrier where
  successor value := ⟨Natural.succ value.down⟩
  successor_injective := by
    intro first second same
    apply ULift.ext
    exact Natural.succ_injective (congrArg ULift.down same)
  omitted := ⟨Natural.zero⟩
  omitted_not_image := by
    intro value same
    exact Natural.succ_ne_zero value.down (congrArg ULift.down same)

def selection : Selection interpretation := ⟨some infinityWitness⟩

noncomputable def hostCarrierEquiv : interpretation.Carrier ≃ ULift.{1} Nat :=
  (Equiv.ulift.trans Natural.representation).trans Equiv.ulift.symm

noncomputable def hostInterpretation : Interpretation Natural.admitted PUnit.unit :=
  interpretation.transport hostCarrierEquiv

noncomputable def hostSelection : Selection hostInterpretation :=
  selection.transport hostCarrierEquiv

theorem hostSelection_facts : hostSelection.facts = selection.facts :=
  selection.transport_facts hostCarrierEquiv

theorem host_recurse_commutes {Result : Type 1}
    (algebra : MappedLayer Natural.admitted PUnit.unit Result → Result)
    (number : interpretation.Carrier) :
    hostInterpretation.recurse algebra (hostCarrierEquiv number) =
      interpretation.recurse algebra number :=
  interpretation.transport_recurse hostCarrierEquiv algebra number

theorem host_all_selected_models (Result : Type 1) (fact : Fact) :
    (model hostInterpretation Result).models (formula fact) := by
  apply hostSelection.models_of_mem Result
  rw [hostSelection_facts]
  cases fact <;> simp [Selection.facts, selection]

noncomputable def hostMaterialEquiv :
    ULift.{1} Nat ≃ ULift.{1} MaterialNatural.{0} :=
  (Equiv.ulift.trans natMaterialIso.toEquiv).trans Equiv.ulift.symm

noncomputable def hostSurrealEquiv :
    ULift.{1} Nat ≃ ULift.{1} SurrealNatural :=
  (Equiv.ulift.trans natSurrealIso.toEquiv).trans Equiv.ulift.symm

noncomputable def liftedMaterialSurrealEquiv :
    ULift.{1} MaterialNatural.{0} ≃ ULift.{1} SurrealNatural :=
  (Equiv.ulift.trans materialSurrealIso.toEquiv).trans Equiv.ulift.symm

theorem lifted_comparison_triangle :
    hostMaterialEquiv.trans liftedMaterialSurrealEquiv = hostSurrealEquiv := by
  apply Equiv.ext
  rintro ⟨number⟩
  apply ULift.ext
  exact congrArg (fun comparison => comparison.toEquiv number) comparison_triangle

noncomputable def materialInterpretation : Interpretation Natural.admitted PUnit.unit :=
  hostInterpretation.transport hostMaterialEquiv

noncomputable def surrealInterpretation : Interpretation Natural.admitted PUnit.unit :=
  hostInterpretation.transport hostSurrealEquiv

noncomputable def materialSelection : Selection materialInterpretation :=
  hostSelection.transport hostMaterialEquiv

noncomputable def surrealSelection : Selection surrealInterpretation :=
  hostSelection.transport hostSurrealEquiv

/-- Going from host naturals through material naturals and then to natural
surreals selects exactly the same interpretation as the direct route. -/
theorem material_surreal_interpretation_route :
    materialInterpretation.transport liftedMaterialSurrealEquiv =
      surrealInterpretation := by
  calc
    materialInterpretation.transport liftedMaterialSurrealEquiv =
        hostInterpretation.transport
          (hostMaterialEquiv.trans liftedMaterialSurrealEquiv) :=
      Interpretation.transport_trans hostInterpretation hostMaterialEquiv
        liftedMaterialSurrealEquiv
    _ = hostInterpretation.transport hostSurrealEquiv :=
      congrArg (fun equivalence => hostInterpretation.transport equivalence)
        lifted_comparison_triangle
    _ = surrealInterpretation := rfl

theorem materialSelection_facts : materialSelection.facts = selection.facts := by
  unfold materialSelection
  exact (Selection.transport_facts hostSelection hostMaterialEquiv).trans hostSelection_facts

theorem surrealSelection_facts : surrealSelection.facts = selection.facts := by
  unfold surrealSelection
  exact (Selection.transport_facts hostSelection hostSurrealEquiv).trans hostSelection_facts

/-- The selected fact manifest is independent of which side of the commuting
comparison triangle is used. -/
theorem material_surreal_selection_facts_route :
    (materialSelection.transport liftedMaterialSurrealEquiv).facts =
      surrealSelection.facts := by
  exact Eq.trans (Selection.transport_facts materialSelection liftedMaterialSurrealEquiv)
    (Eq.trans materialSelection_facts surrealSelection_facts.symm)

theorem material_recurse_commutes {Result : Type 1}
    (algebra : MappedLayer Natural.admitted PUnit.unit Result → Result)
    (number : hostInterpretation.Carrier) :
    materialInterpretation.recurse algebra (hostMaterialEquiv number) =
      hostInterpretation.recurse algebra number :=
  hostInterpretation.transport_recurse hostMaterialEquiv algebra number

theorem surreal_recurse_commutes {Result : Type 1}
    (algebra : MappedLayer Natural.admitted PUnit.unit Result → Result)
    (number : hostInterpretation.Carrier) :
    surrealInterpretation.recurse algebra (hostSurrealEquiv number) =
      hostInterpretation.recurse algebra number :=
  hostInterpretation.transport_recurse hostSurrealEquiv algebra number

theorem material_all_selected_models (Result : Type 1) (fact : Fact) :
    (model materialInterpretation Result).models (formula fact) := by
  apply materialSelection.models_of_mem Result
  rw [materialSelection_facts]
  cases fact <;> simp [Selection.facts, selection]

theorem surreal_all_selected_models (Result : Type 1) (fact : Fact) :
    (model surrealInterpretation Result).models (formula fact) := by
  apply surrealSelection.models_of_mem Result
  rw [surrealSelection_facts]
  cases fact <;> simp [Selection.facts, selection]

def zeroSuccPair : ConstructorProjection.DistinctPair Natural.admitted.constructors.length where
  first := ⟨0, by decide⟩
  second := ⟨1, by decide⟩
  different := by decide

theorem zeroSuccPair_names :
    (ConstructorProjection.namedNoConfusion Natural.admitted zeroSuccPair).name =
      ("Zero", "Succ") := rfl

theorem zeroSuccPair_models :
    (ConstructorProjection.projectionModel interpretation).models
      (ConstructorProjection.namedNoConfusion Natural.admitted zeroSuccPair).formula :=
  ConstructorProjection.namedNoConfusion_models interpretation zeroSuccPair

theorem all_named_noConfusion_names :
    (ConstructorProjection.namedNoConfusions Natural.admitted).map
      ConstructorProjection.NamedFormula.name =
      [("Zero", "Succ"), ("Succ", "Zero")] := by
  decide +kernel

theorem selected_facts :
    selection.facts =
      [.structuralRecursion, .structuralInduction, .constructorNoConfusion,
        .carrierInfinity] := rfl

theorem all_selected_models (Result : Type 1) (fact : Fact) :
    (model interpretation Result).models (formula fact) := by
  apply selection.models_of_mem Result
  cases fact <;> simp [selected_facts]

/-- Project the four structural capabilities to the existing named natural
fact vocabulary.  Complete-layer no-confusion yields the two customary
constructor laws. -/
def nativeProjection : Fact → List Mettapedia.Languages.HOLLight.NaturalFacts.Fact
  | .structuralRecursion => [.recursion]
  | .structuralInduction => [.induction]
  | .constructorNoConfusion => [.zeroNotSuccessor, .successorInjective]
  | .carrierInfinity => [.infinity]

def projectedNativeFacts : List Mettapedia.Languages.HOLLight.NaturalFacts.Fact :=
  selection.facts.flatMap nativeProjection

theorem projectedNativeFacts_eq :
    projectedNativeFacts = Mettapedia.Languages.HOLLight.NaturalFacts.facts := rfl

/-- The generic selection therefore emits exactly the existing five native
HOL Light statement wires, in their established order.  Proof production and
kernel acceptance remain the existing native qualification route. -/
def projectedStatements : List Mettapedia.Languages.HOLLight.HOLSyntaxWire.Wire :=
  projectedNativeFacts.map Mettapedia.Languages.HOLLight.NaturalFacts.statement

theorem projectedStatements_eq :
    projectedStatements =
      Mettapedia.Languages.HOLLight.NaturalFacts.facts.map
        Mettapedia.Languages.HOLLight.NaturalFacts.statement := by
  unfold projectedStatements
  rw [projectedNativeFacts_eq]

theorem projectedNames_eq :
    projectedNativeFacts.map Mettapedia.Languages.HOLLight.NaturalFacts.name =
      ["num_RECURSION", "num_INDUCTION", "NOT_SUC", "SUC_INJ",
        "NAT_CARRIER_INFINITY"] := by
  rw [projectedNativeFacts_eq]
  rfl

/-- Every projected named formula has the authored natural interpretation.
This links the generated manifest to the exact formulas consumed by the
existing native route. -/
theorem projected_models (Result : Type 1)
    (fact : Mettapedia.Languages.HOLLight.NaturalFacts.Fact)
    (_member : fact ∈ projectedNativeFacts) :
    (IndexedInductiveNaturalHOL.NativeFacts.model Result).models
      (Mettapedia.Languages.HOLLight.NaturalFacts.formula fact) := by
  exact IndexedInductiveNaturalHOL.NativeFacts.all_models Result fact

end NaturalControl

namespace MutualControl

open IndexedInductiveExamples

def interpretation := Interpretation.tagged Mutual.admitted PUnit.unit

def structuralSelection : Selection interpretation := ⟨none⟩

def structuralWireNames : NativeWire.StructuralNames where
  sourceType := "mutual_value"
  layerType := "mutual_layer"
  mappedLayerType := "mutual_mapped_layer"
  resultType := "mutual_result"
  construct := "MUTUAL_CONSTRUCT"
  mapLayer := "MUTUAL_MAP_LAYER"
  allChildren := "MUTUAL_ALL_CHILDREN"

def emittedStructural :=
  NativeWire.Selection.emit structuralSelection structuralWireNames

theorem emittedStructural_sources :
    emittedStructural.map NativeWire.EmittedFact.source =
      [.structuralRecursion, .structuralInduction, .constructorNoConfusion] := rfl

theorem emittedStructural_refuses_infinity :
    Fact.carrierInfinity ∉ emittedStructural.map NativeWire.EmittedFact.source := by
  simp [emittedStructural_sources]

theorem emittedStructural_source_models (Result : Type 1)
    {fact : NativeWire.EmittedFact} (member : fact ∈ emittedStructural) :
    (model interpretation Result).models (formula fact.source) :=
  NativeWire.Selection.emit_source_models structuralSelection structuralWireNames Result member

def structuralRoundtrips : Bool :=
  structuralSelection.facts.all fun fact =>
    decide (NativeWire.Selection.decode? structuralSelection structuralWireNames
      (NativeWire.statement structuralWireNames fact) = some fact)

theorem structural_roundtrips : structuralRoundtrips = true := by
  decide +kernel

def wireNames : ConstructorProjection.WireNames Mutual.admitted.constructors.length where
  sourceType := "mutual_value"
  layerType := "mutual_layer"
  occurrenceType := "mutual_constructor"
  construct := "MUTUAL_CONSTRUCT"
  tag := "MUTUAL_CONSTRUCTOR_TAG"
  occurrence index := (Mutual.admitted.constructors.get index).name

def emitted := ConstructorProjection.emitAll Mutual.admitted wireNames

theorem emitted_sources :
    emitted.map ConstructorProjection.EmittedFact.source =
      ConstructorProjection.namedNoConfusions Mutual.admitted :=
  ConstructorProjection.emitAll_sources Mutual.admitted wireNames

theorem emitted_names :
    emitted.map (fun fact => fact.source.name) =
      [("zero", "odd"), ("zero", "even"),
       ("odd", "zero"), ("odd", "even"),
       ("even", "zero"), ("even", "odd")] := by
  decide +kernel

theorem emitted_source_models
    {fact : ConstructorProjection.EmittedFact Mutual.admitted.constructors.length}
    (member : fact ∈ emitted) :
    (ConstructorProjection.projectionModel interpretation).models fact.source.formula :=
  ConstructorProjection.emitAll_source_models interpretation wireNames member

def pairRoundtrips : Bool :=
  (ConstructorProjection.allDistinctPairs Mutual.admitted.constructors.length).all fun pair =>
    decide (ConstructorProjection.decodePair? Mutual.admitted wireNames
      (ConstructorProjection.statement wireNames pair) = some pair)

theorem pair_roundtrips : pairRoundtrips = true := by
  decide +kernel

def zeroOddPair : ConstructorProjection.DistinctPair Mutual.admitted.constructors.length where
  first := ⟨0, by decide⟩
  second := ⟨1, by decide⟩
  different := by decide

def zeroEvenPair : ConstructorProjection.DistinctPair Mutual.admitted.constructors.length where
  first := ⟨0, by decide⟩
  second := ⟨2, by decide⟩
  different := by decide

def collidingWireNames : ConstructorProjection.WireNames Mutual.admitted.constructors.length :=
  { wireNames with occurrence := fun _ => "same_constructor" }

theorem colliding_occurrence_names_collapse_statements :
    ConstructorProjection.statement collidingWireNames zeroOddPair =
      ConstructorProjection.statement collidingWireNames zeroEvenPair := by
  decide +kernel

theorem colliding_occurrence_names_break_roundtrip :
    ConstructorProjection.decodePair? Mutual.admitted collidingWireNames
      (ConstructorProjection.statement collidingWireNames zeroEvenPair) ≠
        some zeroEvenPair := by
  decide +kernel

end MutualControl

theorem bool_has_no_infinityWitness :
    ¬ Nonempty (InfinityWitness (ULift.{1} Bool)) :=
  no_infinityWitness_of_finite (ULift.{1} Bool)

#print axioms Interpretation.construct_injective
#print axioms Interpretation.construct_ne_of_occurrence_ne
#print axioms Interpretation.transport_construct
#print axioms Interpretation.transport_mapLayer
#print axioms Interpretation.transport_refl
#print axioms Interpretation.transport_trans
#print axioms Interpretation.transport_symm
#print axioms Interpretation.recurse_construct
#print axioms Interpretation.recurse_unique
#print axioms Interpretation.transport_recurse
#print axioms recursion_meaning
#print axioms induction_meaning
#print axioms noConfusion_meaning
#print axioms infinity_meaning
#print axioms InfinityWitness.transport_refl
#print axioms InfinityWitness.transport_trans
#print axioms InfinityWitness.transport_symm
#print axioms models_recursion
#print axioms models_induction
#print axioms models_noConfusion
#print axioms Selection.carrierInfinity_mem_iff
#print axioms Selection.transport_facts
#print axioms Selection.transport_refl_witness
#print axioms Selection.transport_trans_witness
#print axioms Selection.transport_symm_witness
#print axioms Selection.models_of_mem
#print axioms Selection.infinity_not_selected_of_finite
#print axioms WireCatalog.decode_encode
#print axioms WireCatalog.decode_sound
#print axioms WireCatalog.decode_none_of_absent
#print axioms NativeWire.Selection.emit_sources
#print axioms NativeWire.Selection.emit_source_models
#print axioms NativeWire.Selection.decode_statement
#print axioms NativeWire.Selection.decode_sound
#print axioms ConstructorProjection.separation_meaning
#print axioms ConstructorProjection.models_separation
#print axioms ConstructorProjection.namedNoConfusion_models
#print axioms ConstructorProjection.namedNoConfusions_models
#print axioms ConstructorProjection.emitAll_sources
#print axioms ConstructorProjection.emitAll_source_models
#print axioms ConstructorProjection.decodePair_statement
#print axioms ConstructorProjection.decodePair_sound
#print axioms NaturalControl.all_selected_models
#print axioms NaturalControl.hostSelection_facts
#print axioms NaturalControl.host_recurse_commutes
#print axioms NaturalControl.host_all_selected_models
#print axioms NaturalControl.lifted_comparison_triangle
#print axioms NaturalControl.material_surreal_interpretation_route
#print axioms NaturalControl.material_surreal_selection_facts_route
#print axioms NaturalControl.materialSelection_facts
#print axioms NaturalControl.surrealSelection_facts
#print axioms NaturalControl.material_recurse_commutes
#print axioms NaturalControl.surreal_recurse_commutes
#print axioms NaturalControl.material_all_selected_models
#print axioms NaturalControl.surreal_all_selected_models
#print axioms NaturalControl.zeroSuccPair_models
#print axioms NaturalControl.all_named_noConfusion_names
#print axioms NaturalControl.projectedNativeFacts_eq
#print axioms NaturalControl.projectedStatements_eq
#print axioms NaturalControl.projectedNames_eq
#print axioms NaturalControl.projected_models
#print axioms MutualControl.emitted_sources
#print axioms MutualControl.emitted_names
#print axioms MutualControl.emitted_source_models
#print axioms MutualControl.emittedStructural_sources
#print axioms MutualControl.emittedStructural_refuses_infinity
#print axioms MutualControl.emittedStructural_source_models
#print axioms MutualControl.structural_roundtrips
#print axioms MutualControl.pair_roundtrips
#print axioms MutualControl.colliding_occurrence_names_collapse_statements
#print axioms MutualControl.colliding_occurrence_names_break_roundtrip
#print axioms bool_has_no_infinityWitness

/-! ## Empty source families and inhabited HOL types

Structural admission does not assert an inhabitant. An interpretation into
an inhabited simple type must therefore state its carrier comparison. The
guarded representation below keeps source quantifiers restricted to the
represented part of a larger inhabited carrier.
-/

namespace InhabitanceBoundary

variable {I : Interface.{0}} {context : List I.SortCode}

abbrev GuardedCarrier (admitted : Admitted I context) (environment : Env I.Value context) :=
  Option (ULift.{1} (Source admitted environment))

def guard {admitted : Admitted I context} {environment : Env I.Value context} :
    GuardedCarrier admitted environment → Prop
  | none => False
  | some _ => True

def guardedEquiv (admitted : Admitted I context) (environment : Env I.Value context) :
    Source admitted environment ≃ {value : GuardedCarrier admitted environment // guard value} where
  toFun := fun value => ⟨some ⟨value⟩, trivial⟩
  invFun := fun value => match value with
    | ⟨some source, _⟩ => source.down
    | ⟨none, impossible⟩ => impossible.elim
  left_inv := fun _ => rfl
  right_inv := by
    rintro ⟨none | ⟨value⟩, good⟩
    · exact good.elim
    · rfl

inductive GuardConst : Ty Unit → Type where
  | guard : GuardConst (.arr (.base ()) .prop)
  | predicate : GuardConst (.arr (.base ()) .prop)

def guardedAll : ClosedFormula GuardConst :=
  .all (.imp (.app (.const .guard) (.var .vz)) (.app (.const .predicate) (.var .vz)))

def guardedEx : ClosedFormula GuardConst :=
  .ex (.and (.app (.const .guard) (.var .vz)) (.app (.const .predicate) (.var .vz)))

def predicate {admitted : Admitted I context} {environment : Env I.Value context}
    (property : Source admitted environment → Prop) : GuardedCarrier admitted environment → ULift.{1} Prop
  | none => ⟨False⟩
  | some value => ⟨property value.down⟩

def guardedModel (admitted : Admitted I context) (environment : Env I.Value context)
    (property : Source admitted environment → Prop) : HenkinModel.{0, 0, 0} Unit GuardConst :=
  HenkinModel.standard (fun _ => GuardedCarrier admitted environment) (fun {_type} constant =>
    match constant with
    | .guard => fun value => ⟨guard value⟩
    | .predicate => predicate property)

/-- The total carrier is inhabited even when its guarded source part is
empty; full domains therefore supply an explicit semantic choice family. -/
noncomputable def guardedChoice (admitted : Admitted I context) (environment : Env I.Value context)
    (property : Source admitted environment → Prop) :
    (guardedModel admitted environment property).HilbertChoice := by
  let M := guardedModel admitted environment property
  have full : M.FullDomains := fun _ _ => trivial
  exact HenkinModel.HilbertChoice.ofFullInhabitedDomains full
    (M.inhabitedDomains_of_fullDomains full (fun _ => none))

theorem guardedAll_iff (admitted : Admitted I context) (environment : Env I.Value context)
    (property : Source admitted environment → Prop) :
    (guardedModel admitted environment property).models guardedAll ↔ ∀ value, property value := by
  constructor
  · intro valid value
    exact valid (some ⟨value⟩) trivial trivial
  · intro valid value _ good
    cases value with
    | none => exact good.elim
    | some value => exact valid value.down

theorem guardedEx_iff (admitted : Admitted I context) (environment : Env I.Value context)
    (property : Source admitted environment → Prop) :
    (guardedModel admitted environment property).models guardedEx ↔ ∃ value, property value := by
  constructor
  · rintro ⟨none | value, _, good, holds⟩
    · exact good.elim
    · exact ⟨value.down, holds⟩
  · rintro ⟨value, holds⟩
    exact ⟨some ⟨value⟩, trivial, trivial, holds⟩

def interface : Interface where
  SortCode := Empty
  Value := Empty.elim
  Index := Unit
  IndexExpr := fun _ => Unit
  evalIndex := fun expression _ => expression

def recursiveOnly : Admitted interface [] :=
  ⟨[⟨"Loop", .recursive () (.result ())⟩], by decide⟩

def source : Document interface [] :=
  .declaration ⟨"Loop", .recursive () (.result ())⟩

theorem source_admitted : admit? source = some recursiveOnly :=
  (admit_iff source recursiveOnly).2 (by
    simp [source, recursiveOnly, quoteConstructor, RawCode.quote, Extension.DeclarationDocument.values])

noncomputable def noValue {index : Unit} (value : recursiveOnly.Family PUnit.unit index) : Empty :=
  Fix.fold recursiveOnly.polynomial (carrier := fun _ _ => Empty) (fun _ _ layer => by
    rcases layer with ⟨⟨occurrence, shape⟩, children⟩
    change Fin 1 at occurrence
    have same : occurrence = (0 : Fin 1) := Subsingleton.elim _ _
    subst occurrence
    exact children none) PUnit.unit index value

theorem source_empty : IsEmpty (Source recursiveOnly PUnit.unit) :=
  ⟨fun value => (noValue value.2).elim⟩

theorem no_direct_inhabited_interpretation
    (interpretation : Interpretation recursiveOnly PUnit.unit) : ¬Nonempty interpretation.Carrier := by
  rintro ⟨value⟩
  exact (noValue (interpretation.sourceEquiv.symm value).2).elim

theorem source_nonempty_of_choice {Base : Type} {Const : Ty Base → Type}
    (admitted : Admitted I context) (environment : Env I.Value context)
    (M : HenkinModel.{0, 0, 0} Base Const) (choice : M.HilbertChoice) (base : Base)
    (interpretation : Interpretation admitted environment)
    (carrier : interpretation.Carrier ≃ M.Carrier base) : Nonempty (Source admitted environment) :=
  ⟨interpretation.sourceEquiv.symm
    (carrier.symm (choice.inhabitedDomains.witness (.base base)))⟩

theorem no_direct_choice_model {Base : Type} {Const : Ty Base → Type}
    (M : HenkinModel.{0, 0, 0} Base Const) (choice : M.HilbertChoice) (base : Base)
    (interpretation : Interpretation recursiveOnly PUnit.unit)
    (carrier : interpretation.Carrier ≃ M.Carrier base) : False := by
  apply no_direct_inhabited_interpretation interpretation
  exact ⟨carrier.symm (choice.inhabitedDomains.witness (.base base))⟩

theorem guarded_exists_refuses :
    ¬(guardedModel recursiveOnly PUnit.unit (fun _ => True)).models guardedEx := by
  intro valid
  obtain ⟨value, _⟩ := (guardedEx_iff recursiveOnly (show Env interface.Value [] from PUnit.unit) _).mp valid
  exact (noValue value.2).elim

theorem unguarded_exists_accepts :
    (guardedModel recursiveOnly PUnit.unit (fun _ => True)).models
      (.ex (σ := .base ()) .top) :=
  ⟨none, trivial, trivial⟩

theorem guarded_universal_vacuous :
    (guardedModel recursiveOnly PUnit.unit (fun _ => False)).models guardedAll := by
  apply (guardedAll_iff recursiveOnly (show Env interface.Value [] from PUnit.unit) _).mpr
  intro value
  exact (noValue value.2).elim

theorem unguarded_universal_refuses :
    ¬(guardedModel recursiveOnly PUnit.unit (fun _ => False)).models
      (.all (σ := .base ()) .bot) := by
  intro valid
  exact valid none trivial

section Functions

variable {I J K : Interface.{0}} {context : List I.SortCode} {targetContext : List J.SortCode}
  {thirdContext : List K.SortCode}
  {source : Admitted I context} {target : Admitted J targetContext} {third : Admitted K thirdContext}
  {environment : Env I.Value context} {targetEnvironment : Env J.Value targetContext}
  {thirdEnvironment : Env K.Value thirdContext}

def mapSource (function : Source source environment → Source target targetEnvironment) :
    GuardedCarrier source environment → GuardedCarrier target targetEnvironment
  | none => none
  | some value => some ⟨function value.down⟩

/-- A selected strict extension of a total source function. Guard preservation
keeps valid inputs valid; strictness fixes behavior outside the source image.
Strictness is not asserted necessary for every guarded interpretation. -/
structure GuardedFunction (source : Admitted I context) (environment : Env I.Value context)
    (target : Admitted J targetContext) (targetEnvironment : Env J.Value targetContext) where
  toFun : GuardedCarrier source environment → GuardedCarrier target targetEnvironment
  strict : toFun none = none
  preserves : ∀ value, guard value → guard (toFun value)

theorem GuardedFunction.ext
    {first second : GuardedFunction source environment target targetEnvironment}
    (same : first.toFun = second.toFun) : first = second := by
  cases first
  cases second
  cases same
  rfl

def liftFunction (function : Source source environment → Source target targetEnvironment) :
    GuardedFunction source environment target targetEnvironment where
  toFun := mapSource function
  strict := rfl
  preserves := by
    intro value valid
    cases value with
    | none => exact valid.elim
    | some _ => trivial

def restrictFunction (function : GuardedFunction source environment target targetEnvironment) :
    Source source environment → Source target targetEnvironment := fun value =>
  (guardedEquiv target targetEnvironment).symm
    ⟨function.toFun (some ⟨value⟩), function.preserves (some ⟨value⟩) trivial⟩

theorem restrict_lift (function : Source source environment → Source target targetEnvironment) :
    restrictFunction (liftFunction function) = function := rfl

theorem lift_restrict (function : GuardedFunction source environment target targetEnvironment) :
    liftFunction (restrictFunction function) = function := by
  apply GuardedFunction.ext
  funext value
  cases value with
  | none => exact function.strict.symm
  | some value =>
      exact congrArg Subtype.val ((guardedEquiv target targetEnvironment).apply_symm_apply
        ⟨function.toFun (some value), function.preserves (some value) trivial⟩)

/-- Every source function has exactly one strict guard-preserving extension,
and every such extension restricts back to that source function. -/
def functionEquiv : (Source source environment → Source target targetEnvironment) ≃
    GuardedFunction source environment target targetEnvironment where
  toFun := liftFunction
  invFun := restrictFunction
  left_inv := restrict_lift
  right_inv := lift_restrict

theorem mapSource_identity :
    mapSource (id : Source source environment → Source source environment) = id := by
  funext value
  cases value <;> rfl

theorem mapSource_composition
    (first : Source source environment → Source target targetEnvironment)
    (second : Source target targetEnvironment → Source third thirdEnvironment) :
    mapSource (second ∘ first) = mapSource second ∘ mapSource first := by
  funext value
  cases value <;> rfl

theorem constant_none_not_preserving (value : Source source environment) :
    ¬ (∀ input : GuardedCarrier source environment,
      guard input → guard (none : GuardedCarrier source environment)) := by
  intro preserves
  exact preserves (some ⟨value⟩) trivial

/-- A non-strict extension can agree on every source value while exposing a
different result at the added, invalid input. -/
def fillMissing (value : Source source environment) :
    GuardedCarrier source environment → GuardedCarrier source environment
  | none => some ⟨value⟩
  | some input => some input

theorem fillMissing_preserves (value : Source source environment)
    (input : GuardedCarrier source environment) (_valid : guard input) : guard (fillMissing value input) := by
  cases input <;> trivial

theorem fillMissing_agrees_on_guard (value : Source source environment)
    (input : GuardedCarrier source environment) (valid : guard input) : fillMissing value input = input := by
  cases input with
  | none => exact valid.elim
  | some _ => rfl

theorem fillMissing_differs (value : Source source environment) : fillMissing value ≠ id := by
  intro same
  have atNone := congrFun same none
  cases atNone

end Functions

/-! Typed HOL quantifiers over the selected function-space image. The atomic
property is an arbitrary predicate on the host function carrier; the source
predicate is its pullback along the proved encoding. -/

section FunctionQuantification

inductive FunctionBase where
  | domain | codomain
  deriving DecidableEq

abbrev sourceType : Ty FunctionBase := .base .domain
abbrev targetType : Ty FunctionBase := .base .codomain
abbrev functionType : Ty FunctionBase := .arr sourceType targetType

inductive FunctionConst : Ty FunctionBase → Type where
  | noneSource : FunctionConst sourceType
  | noneTarget : FunctionConst targetType
  | sourceGuard : FunctionConst (.arr sourceType .prop)
  | targetGuard : FunctionConst (.arr targetType .prop)
  | property : FunctionConst (.arr functionType .prop)

def functionGuard : Formula FunctionConst [functionType] :=
  .and (.eq (.app (.var .vz) (.const .noneSource)) (.const .noneTarget))
    (.all (σ := sourceType) (.imp
      (.app (.const .sourceGuard) (.var .vz))
      (.app (.const .targetGuard) (.app (.var (.vs .vz)) (.var .vz)))))

def functionsAll : ClosedFormula FunctionConst :=
  .all (σ := functionType) (.imp functionGuard (.app (.const .property) (.var .vz)))

def functionsEx : ClosedFormula FunctionConst :=
  .ex (σ := functionType) (.and functionGuard (.app (.const .property) (.var .vz)))

variable {I J : Interface.{0}} {context : List I.SortCode} {targetContext : List J.SortCode}
  (source : Admitted I context) (environment : Env I.Value context)
  (target : Admitted J targetContext) (targetEnvironment : Env J.Value targetContext)

def functionModel
    (property : (GuardedCarrier source environment → GuardedCarrier target targetEnvironment) → Prop) :
    HenkinModel.{0, 0, 0} FunctionBase FunctionConst :=
  HenkinModel.standard
    (fun | .domain => GuardedCarrier source environment | .codomain => GuardedCarrier target targetEnvironment)
    (fun {_type} constant => match constant with
      | .noneSource => none
      | .noneTarget => none
      | .sourceGuard => fun value => ⟨guard value⟩
      | .targetGuard => fun value => ⟨guard value⟩
      | .property => fun function => ⟨property function⟩)

theorem functionsAll_iff
    (property : (GuardedCarrier source environment → GuardedCarrier target targetEnvironment) → Prop) :
    (functionModel source environment target targetEnvironment property).models functionsAll ↔
      ∀ function : Source source environment → Source target targetEnvironment,
        property (liftFunction function).toFun := by
  constructor
  · intro valid function
    let encoded := liftFunction function
    exact valid encoded.toFun trivial
      ⟨encoded.strict, fun value _ good => encoded.preserves value good⟩
  · intro valid function _ good
    let qualified : GuardedFunction source environment target targetEnvironment :=
      ⟨function, good.1, fun value valid => good.2 value trivial valid⟩
    have holds := valid (restrictFunction qualified)
    rw [lift_restrict] at holds
    exact holds

theorem functionsEx_iff
    (property : (GuardedCarrier source environment → GuardedCarrier target targetEnvironment) → Prop) :
    (functionModel source environment target targetEnvironment property).models functionsEx ↔
      ∃ function : Source source environment → Source target targetEnvironment,
        property (liftFunction function).toFun := by
  constructor
  · rintro ⟨function, _, good, holds⟩
    let qualified : GuardedFunction source environment target targetEnvironment :=
      ⟨function, good.1, fun value valid => good.2 value trivial valid⟩
    refine ⟨restrictFunction qualified, ?_⟩
    rw [lift_restrict]
    exact holds
  · rintro ⟨function, holds⟩
    let encoded := liftFunction function
    exact ⟨encoded.toFun, trivial,
      ⟨encoded.strict, fun value _ good => encoded.preserves value good⟩, holds⟩

end FunctionQuantification

end InhabitanceBoundary

end Mettapedia.GSLT.LanguageDef.IndexedInductive.HOLFacts
