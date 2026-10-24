import Mathlib.Logic.Equiv.Prod
import Mettapedia.TypeTheory.IndexedPositiveContainer

/-!
# Induction bundles for arbitrary registered indexed containers

The executable indexed-container registry records output expressions and
position semantics.  A dependent guest additionally needs a representation of
one motive witness at every recursive position.  This module keeps that
semantic qualification separate from executable lookup and finitarity.

For every qualified registry, `Code.Bundle` recursively combines direct
recursive hypotheses with the registered bundle of each nested field.
`Code.bundleExact` proves that the result is exactly one witness at every
position of the complete constructor polynomial.  Thus the List and Vector
guest specializations are instances of one position-sensitive theorem rather
than unrelated encodings.

Motive transport preserves those same positions across qualified bundle
representations. With a separately supplied traversal order, the bundle is
equivalent to a dependent list of position witnesses. These are semantic
constructions; they do not provide a guest-language decoder for an open term.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPositiveContainer

open IndexedContainer
open IndexedPolynomial
open IndexedPolynomial.Description

universe u v

namespace Entry

/-- Semantic induction qualification for one executable registry entry.  It
does not imply that positions are finite or that an object-language encoding
has been implemented. -/
structure InductionQualified {I : Interface.{u}} (entry : Entry I) where
  bundle : {Element : Type} → (motive : Element → Type) →
    IndexedContainer.InductionBundle entry.container Element motive

end Entry

/-- Every successful lookup in a registry has a semantic induction bundle.
The lookup remains executable because the qualification is stored separately.
-/
structure Registry.InductionQualified {I : Interface.{u}}
    (registry : Registry I) where
  entryQualified : ∀ name entry,
    registry.lookup name = some entry → Entry.InductionQualified entry

/-- The pointwise representation keeps one witness at every actual container
position. It needs no finite-position or traversal assumption. -/
def Registry.pointwiseInductionQualified {I : Interface.{u}} (registry : Registry I) :
    registry.InductionQualified where
  entryQualified _ _entry _ :=
    ⟨fun motive =>
      { Bundle := fun value => ∀ position, motive (value.2 position)
        exact := fun _ => Equiv.refl _ }⟩

namespace Code

variable {I : Interface.{u}} {registry : Registry I} {parameterCount : Nat}

/-- One motive witness at every direct or registered-nested recursive
position, represented according to the selected registry qualification. -/
def Bundle (qualified : registry.InductionQualified)
    {Element : I.Index → Type}
    (motive : ∀ index, Element index → Type) :
    {context : List I.SortCode} →
    (code : Code I registry parameterCount context) →
    {environment : Env I.Value context} → {index : I.Index} →
    (shape : Shape code environment index) →
    (children : ∀ position : Position code shape,
      Element (next code shape position)) → Type u
  | _, .result _, _, _, _, _ => PUnit
  | _, .data _ body, _, _, shape, children =>
      Bundle qualified motive body shape.2 children
  | _, .recursive expression rest, environment, _, shape, children =>
      motive (I.evalIndex expression environment) (children none) ×
        Bundle qualified motive rest shape (fun position => children (some position))
  | _, .nested name entry registered output childIndex rest,
      environment, _, shape, children =>
      let childOutput := entry.evalOutput output environment
      let childFamilyIndex := I.evalIndex childIndex environment
      let value : entry.container.Extension (Element childFamilyIndex) childOutput :=
        ⟨shape.1, fun position => children (.inl position)⟩
      ((qualified.entryQualified name entry registered).bundle
          (motive childFamilyIndex)).Bundle value ×
        Bundle qualified motive rest shape.2
          (fun position => children (.inr position))

/-- The generated bundle contains exactly one motive witness at every
recursive position of the complete constructor code. -/
noncomputable def bundleExact
    (qualified : registry.InductionQualified)
    {Element : I.Index → Type}
    (motive : ∀ index, Element index → Type) :
    {context : List I.SortCode} →
    (code : Code I registry parameterCount context) →
    {environment : Env I.Value context} → {index : I.Index} →
    (shape : Shape code environment index) →
    (children : ∀ position : Position code shape,
      Element (next code shape position)) →
    Bundle qualified motive code shape children ≃
      (∀ position : Position code shape,
        motive (next code shape position) (children position))
  | _, .result _, _, _, _, _ =>
      { toFun := fun _ position => PEmpty.elim position
        invFun := fun _ => PUnit.unit
        left_inv := fun value => by cases value; rfl
        right_inv := fun function => by
          funext position
          exact PEmpty.elim position }
  | _, .data _ body, _, _, shape, children =>
      bundleExact qualified motive body shape.2 children
  | _, .recursive expression rest, environment, _, shape, children => by
      let tailExact := bundleExact qualified motive rest shape
        (fun position => children (some position))
      refine
        { toFun := fun hypotheses position => ?_
          invFun := fun hypotheses =>
            ⟨hypotheses none,
              tailExact.invFun (fun position => hypotheses (some position))⟩
          left_inv := ?_
          right_inv := ?_ }
      · cases position with
        | none => exact hypotheses.1
        | some prior => exact tailExact.toFun hypotheses.2 prior
      · rintro ⟨head, tail⟩
        apply Prod.ext
        · rfl
        · exact tailExact.left_inv tail
      · intro hypotheses
        funext position
        cases position with
        | none => rfl
        | some prior =>
            exact congrFun (tailExact.apply_symm_apply
              (fun position => hypotheses (some position))) prior
  | _, .nested name entry registered output childIndex rest,
      environment, _, shape, children => by
      let childOutput := entry.evalOutput output environment
      let childFamilyIndex := I.evalIndex childIndex environment
      let value : entry.container.Extension (Element childFamilyIndex) childOutput :=
        ⟨shape.1, fun position => children (.inl position)⟩
      let nestedExact :=
        ((qualified.entryQualified name entry registered).bundle
          (motive childFamilyIndex)).exact value
      let tailExact := bundleExact qualified motive rest shape.2
        (fun position => children (.inr position))
      refine
        { toFun := fun hypotheses position => ?_
          invFun := fun hypotheses =>
            ⟨nestedExact.invFun (fun position => hypotheses (.inl position)),
              tailExact.invFun (fun position => hypotheses (.inr position))⟩
          left_inv := ?_
          right_inv := ?_ }
      · cases position with
        | inl nested => exact nestedExact.toFun hypotheses.1 nested
        | inr prior => exact tailExact.toFun hypotheses.2 prior
      · rintro ⟨nested, tail⟩
        apply Prod.ext
        · exact nestedExact.left_inv nested
        · exact tailExact.left_inv tail
      · intro hypotheses
        funext position
        cases position with
        | inl nested =>
            exact congrFun (nestedExact.apply_symm_apply
              (fun position => hypotheses (.inl position))) nested
        | inr prior =>
            exact congrFun (tailExact.apply_symm_apply
              (fun position => hypotheses (.inr position))) prior

/-! ## Motive transport and ordered semantic results -/

section Transport

variable {Element : I.Index → Type}
variable {first second third : ∀ index, Element index → Type}
variable {context : List I.SortCode} {code : Code I registry parameterCount context}
variable {environment : Env I.Value context} {index : I.Index}
variable {shape : Shape code environment index}
variable {children : ∀ position : Position code shape, Element (next code shape position)}

/-- Transport every position witness, retaining its family index and child.
The source and target may choose different qualified bundle representations. -/
noncomputable def mapBundle (source target : registry.InductionQualified)
    (mapping : ∀ index element, first index element → second index element)
    (bundle : Bundle source first code shape children) :
    Bundle target second code shape children :=
  (bundleExact target second code shape children).symm
    (fun position => mapping (next code shape position) (children position)
      (bundleExact source first code shape children bundle position))

@[simp] theorem mapBundle_exact (source target : registry.InductionQualified)
    (mapping : ∀ index element, first index element → second index element)
    (bundle : Bundle source first code shape children) (position : Position code shape) :
    bundleExact target second code shape children (mapBundle source target mapping bundle) position =
      mapping (next code shape position) (children position)
        (bundleExact source first code shape children bundle position) := by
  simp only [mapBundle, Equiv.apply_symm_apply]

@[simp] theorem mapBundle_id (qualified : registry.InductionQualified)
    (bundle : Bundle qualified first code shape children) :
    mapBundle qualified qualified (fun _ _ value => value) bundle = bundle := by
  apply (bundleExact qualified first code shape children).injective
  funext position
  exact mapBundle_exact qualified qualified (fun _ _ value => value) bundle position

theorem mapBundle_comp (source middle target : registry.InductionQualified)
    (firstMap : ∀ index element, first index element → second index element)
    (secondMap : ∀ index element, second index element → third index element)
    (bundle : Bundle source first code shape children) :
    mapBundle middle target secondMap (mapBundle source middle firstMap bundle) =
      mapBundle source target (fun index element value => secondMap index element (firstMap index element value)) bundle := by
  apply (bundleExact target third code shape children).injective
  funext position
  simp only [mapBundle_exact]

/-- An injective witness transformation remains injective on the complete
bundle. No injectivity of the underlying child values is required. -/
theorem mapBundle_injective (source target : registry.InductionQualified)
    (mapping : ∀ index element, first index element → second index element)
    (injective : ∀ index element, Function.Injective (mapping index element)) :
    Function.Injective (mapBundle source target mapping
      (code := code) (shape := shape) (children := children)) := by
  intro left right same
  apply (bundleExact source first code shape children).injective
  funext position
  apply injective (next code shape position) (children position)
  have atPosition := congrFun
    (congrArg (bundleExact target second code shape children) same) position
  simpa only [mapBundle_exact] using atPosition

/-- Pointwise equivalences induce an equivalence of the complete induction
bundles, even when their selected representations differ. -/
noncomputable def bundleEquiv (source target : registry.InductionQualified)
    (equivalent : ∀ index element, first index element ≃ second index element) :
    Bundle source first code shape children ≃ Bundle target second code shape children where
  toFun := mapBundle source target (fun index element => equivalent index element)
  invFun := mapBundle target source (fun index element => (equivalent index element).symm)
  left_inv bundle := by
    apply (bundleExact source first code shape children).injective
    funext position
    simp only [mapBundle_exact, Equiv.symm_apply_apply]
  right_inv bundle := by
    apply (bundleExact target second code shape children).injective
    funext position
    simp only [mapBundle_exact, Equiv.apply_symm_apply]

/-- The selected order enumerates each actual position exactly once. -/
noncomputable def orderedPositionEquiv (ordered : registry.OrderedFinitary)
    (code : Code I registry parameterCount context) (shape : Shape code environment index) :
    Fin (orderedPositions ordered code shape).length ≃ Position code shape :=
  Equiv.ofBijective (orderedPositions ordered code shape).get
    ⟨List.nodup_iff_injective_get.mp (orderedPositions_nodup ordered code shape),
      fun position => List.mem_iff_get.mp (mem_orderedPositions ordered code shape position)⟩

/-- A result at each selected position, retaining its dependent motive type. -/
abbrev OrderedResults (ordered : registry.OrderedFinitary)
    (motive : ∀ index, Element index → Type)
    (code : Code I registry parameterCount context) (shape : Shape code environment index)
    (children : ∀ position : Position code shape, Element (next code shape position)) :=
  IndexedContainer.ListAll
    (fun position => motive (next code shape position) (children position))
    (orderedPositions ordered code shape)

/-- Ordered semantic results determine the complete semantic bundle. The
traversal capability is separate from induction qualification. -/
noncomputable def orderedResultsEquiv (qualified : registry.InductionQualified)
    (ordered : registry.OrderedFinitary) :
    Bundle qualified first code shape children ≃ OrderedResults ordered first code shape children :=
  (bundleExact qualified first code shape children).trans
    ((Equiv.piCongrLeft (fun position => first (next code shape position) (children position))
      (orderedPositionEquiv ordered code shape)).symm.trans
      (IndexedContainer.listAllEquiv
        (fun position => first (next code shape position) (children position))
        (orderedPositions ordered code shape)).symm)

@[simp] theorem orderedResults_at (qualified : registry.InductionQualified)
    (ordered : registry.OrderedFinitary) (bundle : Bundle qualified first code shape children)
    (position : Fin (orderedPositions ordered code shape).length) :
    IndexedContainer.listAllEquiv _ (orderedPositions ordered code shape)
        (orderedResultsEquiv qualified ordered bundle) position =
      bundleExact qualified first code shape children bundle
        ((orderedPositions ordered code shape).get position) := by
  change (IndexedContainer.listAllEquiv
      (fun position => first (next code shape position) (children position)) (orderedPositions ordered code shape))
    ((IndexedContainer.listAllEquiv
      (fun position => first (next code shape position) (children position)) (orderedPositions ordered code shape)).symm
      ((Equiv.piCongrLeft (fun position => first (next code shape position) (children position))
        (orderedPositionEquiv ordered code shape)).symm
        (bundleExact qualified first code shape children bundle))) position = _
  exact (congrFun
    ((IndexedContainer.listAllEquiv
      (fun position => first (next code shape position) (children position))
      (orderedPositions ordered code shape)).apply_symm_apply
        ((Equiv.piCongrLeft (fun position => first (next code shape position) (children position))
          (orderedPositionEquiv ordered code shape)).symm
          (bundleExact qualified first code shape children bundle))) position).trans
    (Equiv.piCongrLeft_symm_apply _ _ _ position)

/-- Mapping results acts on the witness in each existing slot. -/
noncomputable def mapOrderedResults (ordered : registry.OrderedFinitary)
    (mapping : ∀ index element, first index element → second index element)
    (results : OrderedResults ordered first code shape children) :
    OrderedResults ordered second code shape children :=
  (IndexedContainer.listAllEquiv _ (orderedPositions ordered code shape)).symm
    (fun position => mapping
      (next code shape ((orderedPositions ordered code shape).get position))
      (children ((orderedPositions ordered code shape).get position))
      (IndexedContainer.listAllEquiv _ (orderedPositions ordered code shape) results position))

/-- Witness transport commutes with the complete ordered result view. -/
theorem orderedResults_mapBundle (source target : registry.InductionQualified)
    (ordered : registry.OrderedFinitary)
    (mapping : ∀ index element, first index element → second index element)
    (bundle : Bundle source first code shape children) :
    orderedResultsEquiv target ordered (mapBundle source target mapping bundle) =
      mapOrderedResults ordered mapping (orderedResultsEquiv source ordered bundle) := by
  apply (IndexedContainer.listAllEquiv _ (orderedPositions ordered code shape)).injective
  funext position
  simp only [orderedResults_at, mapBundle_exact, mapOrderedResults, Equiv.apply_symm_apply]

theorem orderedResults_injective (qualified : registry.InductionQualified)
    (ordered : registry.OrderedFinitary) :
    Function.Injective (orderedResultsEquiv qualified ordered
      (code := code) (shape := shape) (children := children) (first := first)) :=
  (orderedResultsEquiv qualified ordered).injective

theorem orderedResults_roundtrip (qualified : registry.InductionQualified)
    (ordered : registry.OrderedFinitary) (bundle : Bundle qualified first code shape children) :
    (orderedResultsEquiv qualified ordered).symm (orderedResultsEquiv qualified ordered bundle) = bundle :=
  (orderedResultsEquiv qualified ordered).symm_apply_apply bundle

/-- Read each position witness into a common result type, preserving the
selected order and every occurrence even when result values coincide. -/
noncomputable def readResults {Result : Type v}
    (qualified : registry.InductionQualified) (ordered : registry.OrderedFinitary)
    (read : ∀ index element, first index element → Result)
    (bundle : Bundle qualified first code shape children) : List Result :=
  (orderedPositions ordered code shape).map fun position =>
    read (next code shape position) (children position)
      (bundleExact qualified first code shape children bundle position)

theorem readResults_length {Result : Type v}
    (qualified : registry.InductionQualified) (ordered : registry.OrderedFinitary)
    (read : ∀ index element, first index element → Result)
    (bundle : Bundle qualified first code shape children) :
    (readResults qualified ordered read bundle).length = (orderedPositions ordered code shape).length :=
  List.length_map _

theorem readResults_mapBundle {Result : Type v}
    (source target : registry.InductionQualified) (ordered : registry.OrderedFinitary)
    (mapping : ∀ index element, first index element → second index element)
    (read : ∀ index element, second index element → Result)
    (bundle : Bundle source first code shape children) :
    readResults target ordered read (mapBundle source target mapping bundle) =
      readResults source ordered (fun index element value => read index element (mapping index element value)) bundle := by
  apply List.map_congr_left
  intro position _
  exact congrArg (read (next code shape position) (children position))
    (mapBundle_exact source target mapping bundle position)

/-- An injective readout of each witness retains the complete bundle even
when several recursive positions contain the same child value. -/
theorem readResults_injective {Result : Type v}
    (qualified : registry.InductionQualified) (ordered : registry.OrderedFinitary)
    (read : ∀ index element, first index element → Result)
    (injective : ∀ index element, Function.Injective (read index element)) :
    Function.Injective (readResults qualified ordered read
      (code := code) (shape := shape) (children := children)) := by
  intro left right same
  apply (bundleExact qualified first code shape children).injective
  funext position
  apply injective (next code shape position) (children position)
  exact (List.map_inj_left.mp same) position (mem_orderedPositions ordered code shape position)

end Transport

end Code

/-! ## Registry instances -/

namespace ListInstance

noncomputable def inductionQualified (I : Interface.{u}) :
    (registry I).InductionQualified where
  entryQualified := by
    intro name foundEntry found
    by_cases same : name = "List"
    · subst name
      simp [registry] at found
      subst foundEntry
      exact ⟨fun motive => IndexedContainer.listInductionBundle motive⟩
    · simp [registry, same] at found

end ListInstance

namespace VectorControl

noncomputable def inductionQualified :
    registry.InductionQualified where
  entryQualified := by
    intro name foundEntry found
    by_cases same : name = "Vector"
    · subst name
      simp [registry] at found
      subst foundEntry
      exact ⟨fun motive => IndexedContainer.vectorInductionBundle motive⟩
    · simp [registry, same] at found

/-- The generic registry theorem specializes to the exact length-indexed
Vector position family. -/
noncomputable def genericBundleExact
    {Element : Type} (motive : Element → Type)
    (length : Nat) (values : Fin length → Element) :
    let shape := shapeAt length
    let children : ∀ _position : Code.Position code shape, Element :=
      fun position => values (positionEquiv length position)
    Code.Bundle inductionQualified (fun _ => motive) code shape children ≃
      (∀ position : Code.Position code shape, motive (children position)) := by
  dsimp only
  exact Code.bundleExact inductionQualified (fun _ => motive) code
    (shapeAt length) (fun position => values (positionEquiv length position))

namespace Results

abbrev Elements : interface.Index → Type := fun _ => Unit
abbrev Motive : ∀ index, Elements index → Type := fun _ _ => Bool

def children (length : Nat) :
    ∀ position : Code.Position code (shapeAt length), Elements (Code.next code (shapeAt length) position) :=
  fun _ => ()

def witnesses (position : Code.Position code (shapeAt 2)) : Bool :=
  decide ((positionEquiv 2 position).val = 0)

noncomputable def firstBundle : Code.Bundle inductionQualified Motive code (shapeAt 2) (children 2) :=
  (Code.bundleExact inductionQualified Motive code (shapeAt 2) (children 2)).symm witnesses

noncomputable def secondBundle : Code.Bundle inductionQualified Motive code (shapeAt 2) (children 2) :=
  Code.mapBundle inductionQualified inductionQualified (fun _ _ witness => !witness) firstBundle

theorem independent_witnesses :
    Code.bundleExact inductionQualified Motive code (shapeAt 2) (children 2) firstBundle
        ((positionEquiv 2).symm 0) = true ∧
      Code.bundleExact inductionQualified Motive code (shapeAt 2) (children 2) firstBundle
        ((positionEquiv 2).symm 1) = false := by
  simp [firstBundle, witnesses]

theorem equal_children : children 2 ((positionEquiv 2).symm 0) =
    children 2 ((positionEquiv 2).symm 1) := rfl

theorem bundles_distinct : firstBundle ≠ secondBundle := by
  intro same
  have atZero := congrFun
    (congrArg (Code.bundleExact inductionQualified Motive code (shapeAt 2) (children 2)) same)
      ((positionEquiv 2).symm 0)
  have mapped := Code.mapBundle_exact inductionQualified inductionQualified
    (fun _ _ (witness : Bool) => !witness) firstBundle ((positionEquiv 2).symm 0)
  have atSecond : Code.bundleExact inductionQualified Motive code (shapeAt 2) (children 2)
      secondBundle ((positionEquiv 2).symm 0) = false :=
    mapped.trans (congrArg Bool.not independent_witnesses.1)
  have impossible : true = false := independent_witnesses.1.symm.trans (atZero.trans atSecond)
  cases impossible

theorem results_distinguish_witnesses :
    Code.orderedResultsEquiv inductionQualified orderedFinitary firstBundle ≠
      Code.orderedResultsEquiv inductionQualified orderedFinitary secondBundle := by
  intro same
  exact bundles_distinct (Code.orderedResults_injective inductionQualified orderedFinitary same)

theorem results_roundtrip :
    (Code.orderedResultsEquiv inductionQualified orderedFinitary).symm
      (Code.orderedResultsEquiv inductionQualified orderedFinitary firstBundle) = firstBundle :=
  Code.orderedResults_roundtrip inductionQualified orderedFinitary firstBundle

/-- The list-spine and pointwise registered representations meet through the
complete constructor bundle, retaining its individual Boolean witnesses. -/
theorem representation_roundtrip :
    (Code.bundleEquiv inductionQualified registry.pointwiseInductionQualified
      (fun _ _ => Equiv.refl Bool)).symm
      (Code.bundleEquiv inductionQualified registry.pointwiseInductionQualified
        (fun _ _ => Equiv.refl Bool) firstBundle) = firstBundle :=
  (Code.bundleEquiv inductionQualified registry.pointwiseInductionQualified
    (fun _ _ => Equiv.refl Bool)).symm_apply_apply firstBundle

theorem transport_composes :
    Code.mapBundle registry.pointwiseInductionQualified inductionQualified
      (fun _ _ (number : Nat) => decide (number = 1))
      (Code.mapBundle inductionQualified registry.pointwiseInductionQualified
        (fun _ _ (witness : Bool) => if witness then 1 else 0) firstBundle) =
      Code.mapBundle inductionQualified inductionQualified
        (fun _ _ (witness : Bool) => decide ((if witness then 1 else 0 : Nat) = 1)) firstBundle :=
  Code.mapBundle_comp inductionQualified registry.pointwiseInductionQualified inductionQualified _ _ firstBundle

theorem transport_preserves_results :
    Code.orderedResultsEquiv registry.pointwiseInductionQualified orderedFinitary
      (Code.mapBundle inductionQualified registry.pointwiseInductionQualified
        (fun _ _ (witness : Bool) => !witness) firstBundle) =
      Code.mapOrderedResults orderedFinitary (fun _ _ (witness : Bool) => !witness)
        (Code.orderedResultsEquiv inductionQualified orderedFinitary firstBundle) :=
  Code.orderedResults_mapBundle inductionQualified registry.pointwiseInductionQualified orderedFinitary _ firstBundle

theorem witness_readout_injective :
    Function.Injective (Code.readResults inductionQualified orderedFinitary
      (fun _ _ (witness : Bool) => witness) (code := code) (shape := shapeAt 2) (children := children 2)) :=
  Code.readResults_injective inductionQualified orderedFinitary _ (fun _ _ _ _ same => same)

theorem coincident_results_keep_slots :
    (Code.readResults inductionQualified orderedFinitary
      (fun _ _ (_witness : Bool) => ()) firstBundle).length = 2 := by
  exact (Code.readResults_length inductionQualified orderedFinitary
    (fun _ _ (_witness : Bool) => ()) firstBundle).trans (by decide +kernel)

theorem deduplicating_results_loses_slot :
    (Code.readResults inductionQualified orderedFinitary
      (fun _ _ (_witness : Bool) => ()) firstBundle).eraseDups.length = 1 := by
  decide +kernel

theorem collapsing_witnesses_equal :
    Code.mapBundle inductionQualified registry.pointwiseInductionQualified
        (fun _ _ (_witness : Bool) => ()) firstBundle =
      Code.mapBundle inductionQualified registry.pointwiseInductionQualified
        (fun _ _ (_witness : Bool) => ()) secondBundle := by
  apply (Code.bundleExact registry.pointwiseInductionQualified (fun _ _ => Unit) code (shapeAt 2) (children 2)).injective
  funext position
  rfl

theorem collapsing_witnesses_not_injective :
    ¬ Function.Injective (Code.mapBundle inductionQualified registry.pointwiseInductionQualified
      (fun _ _ (_witness : Bool) => ()) (code := code) (shape := shapeAt 2) (children := children 2)) := by
  intro injective
  exact bundles_distinct (injective collapsing_witnesses_equal)

end Results

end VectorControl

/-! ## Semantic induction does not imply finite traversal -/

namespace ReaderControl

def entry (I : Interface.{u}) : Entry I where
  Output := Unit
  OutputExpr := fun _ => PUnit
  evalOutput := fun _ _ => ()
  container := IndexedContainer.Examples.reader

def registry (I : Interface.{u}) : Registry I where
  lookup name := if name = "Reader" then some (entry I) else none

def inductionQualified (I : Interface.{u}) : (registry I).InductionQualified :=
  (registry I).pointwiseInductionQualified

/-- A semantic witness bundle cannot manufacture the separate finite-position
capability required by an executable traversal. -/
theorem not_finitary (I : Interface.{u}) :
    ¬ Nonempty (registry I).Finitary := by
  rintro ⟨finitary⟩
  have found : (registry I).lookup "Reader" = some (entry I) := by
    simp [registry]
  exact IndexedContainer.Examples.reader_not_finitary
    ⟨finitary.containerFinitary "Reader" (entry I) found⟩

theorem not_orderedFinitary (I : Interface.{u}) :
    ¬ Nonempty (registry I).OrderedFinitary := by
  rintro ⟨ordered⟩
  exact not_finitary I ⟨ordered.toFinitary⟩

end ReaderControl

section AxiomAudit

#print axioms Code.bundleExact
#print axioms Code.mapBundle_exact
#print axioms Code.mapBundle_comp
#print axioms Code.mapBundle_injective
#print axioms Code.bundleEquiv
#print axioms Code.orderedResultsEquiv
#print axioms Code.orderedResults_at
#print axioms Code.orderedResults_mapBundle
#print axioms VectorControl.Results.results_distinguish_witnesses
#print axioms VectorControl.Results.representation_roundtrip
#print axioms VectorControl.Results.collapsing_witnesses_not_injective
#print axioms ListInstance.inductionQualified
#print axioms VectorControl.inductionQualified
#print axioms VectorControl.genericBundleExact
#print axioms ReaderControl.inductionQualified
#print axioms ReaderControl.not_finitary

end AxiomAudit

end Mettapedia.TypeTheory.IndexedPositiveContainer
