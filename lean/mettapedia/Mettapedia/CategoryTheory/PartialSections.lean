import Mettapedia.CategoryTheory.LocalSections
import Mathlib.CategoryTheory.Category.GaloisConnection

/-!
# Partial descriptions, refinement and reports

A view is a section of the existing assignment presheaf together with its
observation context. An arrow extends that context while agreeing on every
previously observed feature. This gives a category of descriptions, not a
category of subjects, events or physical implementations. Its arrows are thin;
occurrence-sensitive categories remain separate.

Reporting restricts the context to a declared set of features. Embedding a
report as a partial description is left adjoint to reporting: the embedding
adds no unobserved values. The adjunction does not reconstruct a unique total
description. Compatible local descriptions have a least common extension,
constructed using `LocalSections.glue`; incompatible descriptions have none.

Values may be arbitrary structured data, products or independent coordinate
families. No scalar, intensity order, experiential interpretation or subject
identity is imposed by this mathematical construction.

Feature selection pulls descriptions back along a declared vocabulary map.
It commutes with reporting and changes of values. A surjective selection
retains the complete description; repeated probes of a restricted vocabulary
can still lose distinctions.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.PartialSections

open _root_.CategoryTheory

universe u v w

structure View (Feature : Type u) (Value : Type v) where
  context : Set Feature
  values : LocalSections.Section context Value

variable {Feature : Type u} {Value : Type v}

@[ext]
theorem View.ext {first second : View Feature Value}
    (contexts : first.context = second.context)
    (values : ∀ feature (inFirst : feature ∈ first.context)
      (inSecond : feature ∈ second.context),
      first.values ⟨feature, inFirst⟩ = second.values ⟨feature, inSecond⟩) :
    first = second := by
  cases first with
  | mk firstContext firstSection =>
    cases second with
    | mk secondContext secondSection =>
      dsimp at contexts
      subst secondContext
      have same : firstSection = secondSection := by
        funext feature
        exact values feature.val feature.property feature.property
      cases same
      rfl

/-- Refinement preserves the values already exposed by the smaller view. -/
def Extends (first second : View Feature Value) : Prop :=
  first.context ⊆ second.context ∧
    ∀ feature (inFirst : feature ∈ first.context) (inSecond : feature ∈ second.context),
      first.values ⟨feature, inFirst⟩ = second.values ⟨feature, inSecond⟩

instance : PartialOrder (View Feature Value) where
  le := Extends
  le_refl _ := ⟨Set.Subset.refl _, fun _ _ _ => rfl⟩
  le_trans first second third firstSecond secondThird :=
    ⟨firstSecond.1.trans secondThird.1, fun feature inFirst inThird =>
      (firstSecond.2 feature inFirst (firstSecond.1 inFirst)).trans
        (secondThird.2 feature (firstSecond.1 inFirst) inThird)⟩
  le_antisymm first second firstSecond secondFirst :=
    View.ext (Set.Subset.antisymm firstSecond.1 secondFirst.1) firstSecond.2

/-- The refinement condition is exactly equality with an actual presheaf
restriction, together with inclusion of contexts. -/
theorem extends_iff_restrict (first second : View Feature Value) :
    first ≤ second ↔ ∃ included : first.context ⊆ second.context,
      LocalSections.restrict included second.values = first.values := by
  constructor
  · intro extension
    refine ⟨extension.1, ?_⟩
    funext feature
    exact (extension.2 feature.val feature.property (extension.1 feature.property)).symm
  · rintro ⟨included, equal⟩
    refine ⟨included, ?_⟩
    intro feature inFirst inSecond
    exact (congrFun equal ⟨feature, inFirst⟩).symm

/-- A complete assignment; this adds no claim of completeness about reality. -/
def total (values : Feature → Value) : View Feature Value where
  context := Set.univ
  values feature := values feature.val

theorem total_injective : Function.Injective (total : (Feature → Value) → View Feature Value) := by
  intro first second equal
  funext feature
  have extension : total first ≤ total second := le_of_eq equal
  exact extension.2 feature (Set.mem_univ _) (Set.mem_univ _)

/-- Keep exactly the available features lying in the observation context. -/
def restrict (observed : Set Feature) (view : View Feature Value) : View Feature Value where
  context := view.context ∩ observed
  values := LocalSections.restrict Set.inter_subset_left view.values

theorem restrict_le (observed : Set Feature) (view : View Feature Value) :
    restrict observed view ≤ view :=
  ⟨Set.inter_subset_left, fun _ _ _ => rfl⟩

theorem restrict_mono (observed : Set Feature) :
    Monotone (restrict (Value := Value) observed) := by
  intro first second extension
  exact ⟨fun _ member => ⟨extension.1 member.1, member.2⟩,
    fun feature inFirst inSecond => extension.2 feature inFirst.1 inSecond.1⟩

theorem restrict_univ (view : View Feature Value) : restrict Set.univ view = view := by
  apply View.ext
  · exact Set.inter_univ _
  · intro _ _ _
    rfl

theorem restrict_restrict (first second : Set Feature) (view : View Feature Value) :
    restrict first (restrict second view) = restrict (first ∩ second) view := by
  apply View.ext
  · ext feature
    simp only [restrict, Set.mem_inter_iff]
    tauto
  · intro _ _ _
    rfl

theorem restrict_of_subset {observed : Set Feature} (view : View Feature Value)
    (included : view.context ⊆ observed) : restrict observed view = view := by
  apply View.ext
  · exact Set.inter_eq_left.mpr included
  · intro _ _ _
    rfl

/-- Reporting is functorial with respect to description refinement. -/
def restrictionFunctor (observed : Set Feature) :
    View Feature Value ⥤ View Feature Value := (restrict_mono observed).functor

/-- Pull a description back along a declared selection of features. The
available context is the preimage; no values outside that context are added. -/
def reindexFeatures {Other : Type w} (select : Other → Feature) (view : View Feature Value) :
    View Other Value where
  context := select ⁻¹' view.context
  values feature := view.values ⟨select feature.val, feature.property⟩

theorem reindexFeatures_mono {Other : Type w} (select : Other → Feature) :
    Monotone (reindexFeatures (Value := Value) select) :=
  fun _ _ extension => ⟨fun _ member => extension.1 member,
    fun feature inFirst inSecond => extension.2 (select feature) inFirst inSecond⟩

def reindexFunctor {Other : Type w} (select : Other → Feature) :
    View Feature Value ⥤ View Other Value := (reindexFeatures_mono select).functor

theorem reindexFeatures_id (view : View Feature Value) :
    reindexFeatures id view = view := rfl

theorem reindexFeatures_comp {Other Next : Type*}
    (first : Other → Feature) (second : Next → Other) (view : View Feature Value) :
    reindexFeatures second (reindexFeatures first view) =
      reindexFeatures (first ∘ second) view := rfl

theorem reindexFeatures_total {Other : Type w} (select : Other → Feature)
    (values : Feature → Value) :
    reindexFeatures select (total values) = total (values ∘ select) := by
  apply View.ext
  · exact Set.preimage_univ
  · intro _ _ _
    rfl

/-- Feature selection commutes with reporting, with the report vocabulary
pulled back along the same selection. -/
theorem reindexFeatures_restrict {Other : Type w} (select : Other → Feature)
    (observed : Set Feature) (view : View Feature Value) :
    reindexFeatures select (restrict observed view) =
      restrict (select ⁻¹' observed) (reindexFeatures select view) := rfl

/-- A selection covering every source feature loses no partial-description
data. A non-surjective selection has no such general guarantee. -/
theorem reindexFeatures_injective {Other : Type w} (select : Other → Feature)
    (covers : Function.Surjective select) :
    Function.Injective (reindexFeatures (Value := Value) select) := by
  intro first second same
  have extension := le_of_eq same
  apply View.ext
  · ext feature
    obtain ⟨other, rfl⟩ := covers feature
    have equal := congrArg (fun view : View Other Value => other ∈ view.context) same
    exact Iff.of_eq equal
  · intro feature inFirst inSecond
    obtain ⟨other, rfl⟩ := covers feature
    exact extension.2 other inFirst inSecond

/-- Reports whose declared contexts lie inside the available vocabulary. -/
abbrev Visible (observed : Set Feature) :=
  {view : View Feature Value // view.context ⊆ observed}

def includeReport (observed : Set Feature) : Visible (Value := Value) observed →
    View Feature Value := Subtype.val

def report (observed : Set Feature) (view : View Feature Value) : Visible (Value := Value) observed :=
  ⟨restrict observed view, Set.inter_subset_right⟩

/-- A report embeds into a view exactly when it refines that view's report.
No choice of hidden feature values is made. -/
theorem report_connection (observed : Set Feature) :
    GaloisConnection (includeReport (Value := Value) observed) (report observed) := by
  intro visible view
  constructor
  · intro extension
    exact ⟨fun _ member => ⟨extension.1 member, visible.property member⟩,
      fun feature inVisible inReport => extension.2 feature inVisible inReport.1⟩
  · intro extension
    exact ⟨fun _ member => (extension.1 member).1,
      fun feature inVisible inView =>
        extension.2 feature inVisible ⟨inView, visible.property inVisible⟩⟩

def inclusionFunctor (observed : Set Feature) :
    Visible (Value := Value) observed ⥤ View Feature Value :=
  (report_connection observed).monotone_l.functor

def reportFunctor (observed : Set Feature) :
    View Feature Value ⥤ Visible (Value := Value) observed :=
  (report_connection observed).monotone_u.functor

/-- A genuine adjunction of the constructed report and refinement categories. -/
def inclusionReportAdjunction (observed : Set Feature) :
    inclusionFunctor (Value := Value) observed ⊣ reportFunctor observed :=
  (report_connection observed).adjunction

theorem report_inclusion (observed : Set Feature) (visible : Visible (Value := Value) observed) :
    report observed (includeReport observed visible) = visible := by
  apply Subtype.ext
  exact restrict_of_subset visible.val visible.property

/-! ## Compatible composition and natural changes of values -/

def Compatible (first second : View Feature Value) : Prop :=
  LocalSections.Compatible first.values second.values

/-- The existing section-gluing construction on the union context. Its
right restriction is justified precisely by compatibility. -/
noncomputable def glue (first second : View Feature Value) : View Feature Value where
  context := first.context ∪ second.context
  values := LocalSections.glue first.values second.values

theorem le_glue_left (first second : View Feature Value) : first ≤ glue first second := by
  refine ⟨Set.subset_union_left, ?_⟩
  intro feature inFirst inUnion
  exact (congrFun (LocalSections.glue_left first.values second.values)
    ⟨feature, inFirst⟩).symm

theorem le_glue_right {first second : View Feature Value}
    (compatible : Compatible first second) : second ≤ glue first second := by
  refine ⟨Set.subset_union_right, ?_⟩
  intro feature inSecond inUnion
  exact (congrFun (LocalSections.glue_right compatible) ⟨feature, inSecond⟩).symm

theorem compatible_of_common_extension {first second whole : View Feature Value}
    (firstExtends : first ≤ whole) (secondExtends : second ≤ whole) :
    Compatible first second := fun feature inFirst inSecond =>
  (firstExtends.2 feature inFirst (firstExtends.1 inFirst)).trans
    (secondExtends.2 feature inSecond (secondExtends.1 inSecond)).symm

theorem glue_le {first second whole : View Feature Value}
    (firstExtends : first ≤ whole) (secondExtends : second ≤ whole) :
    glue first second ≤ whole := by
  classical
  refine ⟨Set.union_subset firstExtends.1 secondExtends.1, ?_⟩
  intro feature inUnion inWhole
  by_cases inFirst : feature ∈ first.context
  · simpa [glue, LocalSections.glue, inFirst] using
      firstExtends.2 feature inFirst inWhole
  · simpa [glue, LocalSections.glue, inFirst] using
      secondExtends.2 feature (inUnion.resolve_left inFirst) inWhole

/-- A common extension exists exactly when the local data agree on overlaps. -/
theorem common_extension_iff (first second : View Feature Value) :
    Compatible first second ↔ ∃ whole, first ≤ whole ∧ second ≤ whole :=
  ⟨fun compatible => ⟨glue first second, le_glue_left first second,
      le_glue_right compatible⟩,
    fun ⟨_, firstExtends, secondExtends⟩ =>
      compatible_of_common_extension firstExtends secondExtends⟩

/-- The constructed compatible union is a categorical join in the refinement
category, expressed by its universal property. -/
theorem glue_universal {first second : View Feature Value}
    (compatible : Compatible first second) (whole : View Feature Value) :
    glue first second ≤ whole ↔ first ≤ whole ∧ second ≤ whole :=
  ⟨fun extension => ⟨(le_glue_left first second).trans extension,
      (le_glue_right compatible).trans extension⟩,
    fun ⟨firstExtends, secondExtends⟩ => glue_le firstExtends secondExtends⟩

def mapValues {Other : Type w} (change : Value → Other) (view : View Feature Value) :
    View Feature Other where
  context := view.context
  values := change ∘ view.values

theorem mapValues_mono {Other : Type w} (change : Value → Other) :
    Monotone (mapValues (Feature := Feature) change) :=
  fun _ _ extension => ⟨extension.1,
    fun feature inFirst inSecond => congrArg change (extension.2 feature inFirst inSecond)⟩

def valueFunctor {Other : Type w} (change : Value → Other) :
    View Feature Value ⥤ View Feature Other := (mapValues_mono change).functor

theorem mapValues_reindexFeatures {Other NewValue : Type*}
    (select : Other → Feature) (change : Value → NewValue) (view : View Feature Value) :
    mapValues change (reindexFeatures select view) =
      reindexFeatures select (mapValues change view) := rfl

theorem mapValues_restrict {Other : Type w} (change : Value → Other)
    (observed : Set Feature) (view : View Feature Value) :
    mapValues change (restrict observed view) = restrict observed (mapValues change view) := rfl

theorem mapValues_glue {Other : Type w} (change : Value → Other)
    (first second : View Feature Value) :
    mapValues change (glue first second) = glue (mapValues change first) (mapValues change second) := by
  apply View.ext
  · rfl
  · intro feature inFirst inSecond
    exact congrFun (LocalSections.map_glue change first.values second.values) ⟨feature, inFirst⟩

/-- Injective value changes reflect equality of full partial descriptions. -/
theorem mapValues_injective {Other : Type w} (change : Value → Other)
    (injective : Function.Injective change) :
    Function.Injective (mapValues (Feature := Feature) change) := by
  classical
  intro first second equal
  apply View.ext
  · exact congrArg (fun view : View Feature Other => view.context) equal
  · intro feature inFirst inSecond
    apply injective
    have valuesEqual := congrArg
      (fun view => if member : feature ∈ view.context then some (view.values ⟨feature, member⟩)
        else none) equal
    simpa [mapValues, inFirst, inSecond] using valuesEqual

/-- Compatible restrictions reconstruct exactly the description on the union
of the two vocabularies, even if that union does not cover all features. -/
theorem glue_restrictions (first second : Set Feature) (view : View Feature Value) :
    glue (restrict first view) (restrict second view) = restrict (first ∪ second) view := by
  classical
  apply View.ext
  · ext feature
    simp only [glue, restrict, Set.mem_union, Set.mem_inter_iff]
    tauto
  · intro feature inUnion inRestricted
    by_cases inFirst : feature ∈ first
    · simp [glue, restrict, LocalSections.glue, LocalSections.restrict,
        inFirst, inRestricted.1]
    · simp [glue, restrict, LocalSections.glue, LocalSections.restrict,
        inFirst, inRestricted.1]

/-- A covering family of two report vocabularies determines the full view. -/
theorem covering_reports_injective (first second : Set Feature)
    (covers : first ∪ second = Set.univ) {left right : View Feature Value}
    (firstEqual : restrict first left = restrict first right)
    (secondEqual : restrict second left = restrict second right) : left = right := by
  have unionEqual : restrict (first ∪ second) left = restrict (first ∪ second) right := by
    rw [← glue_restrictions, ← glue_restrictions, firstEqual, secondEqual]
  simpa [covers, restrict_univ] using unionEqual

/-! ## Complete data and incomplete reports -/

namespace Controls

def first : View Bool Nat := total (fun feature => if feature then 2 else 1)
def second : View Bool Nat := total (fun feature => if feature then 3 else 1)

theorem incomplete_reports_agree : restrict {false} first = restrict {false} second := by
  apply View.ext
  · rfl
  · intro feature inFirst inSecond
    have equal : feature = false := inFirst.2
    subst feature
    rfl

theorem complete_views_differ : first ≠ second := by
  intro equal
  have firstSecond : first ≤ second := le_of_eq equal
  have impossible := firstSecond.2 true (Set.mem_univ _) (Set.mem_univ _)
  change 2 = 3 at impossible
  cases impossible

/-- Repeated probes of one feature still omit the unselected feature. -/
theorem incomplete_feature_selection_loses_data :
    reindexFeatures (fun _ : Nat => false) first =
      reindexFeatures (fun _ : Nat => false) second ∧ first ≠ second := by
  refine ⟨?_, complete_views_differ⟩
  apply View.ext
  · rfl
  · intro _ _ _
    rfl

def conflicting : View Bool Nat := total (fun feature => if feature then 2 else 7)

theorem conflicting_reports_have_no_extension :
    ¬ ∃ whole, restrict {false} first ≤ whole ∧ restrict {false} conflicting ≤ whole := by
  rintro ⟨whole, firstExtends, conflictingExtends⟩
  have compatible := compatible_of_common_extension firstExtends conflictingExtends
  have impossible := compatible false ⟨Set.mem_univ _, rfl⟩ ⟨Set.mem_univ _, rfl⟩
  change 1 = 7 at impossible
  cases impossible

theorem distinct_reports_reconstruct :
    glue (restrict {false} first) (restrict {true} first) = first := by
  rw [glue_restrictions]
  apply restrict_of_subset
  intro feature _
  cases feature <;> simp

end Controls

end Mettapedia.CategoryTheory.PartialSections
