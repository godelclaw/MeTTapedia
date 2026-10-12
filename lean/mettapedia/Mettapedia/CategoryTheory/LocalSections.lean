import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Opposites
import Mathlib.Data.Set.Lattice

/-!
# Local sections on sets of features

Assignments on an observation context restrict contravariantly. Compatible
assignments on two contexts have an explicitly constructed, unique extension
to their union. Pairwise equality on the overlap is both necessary and
sufficient; two arbitrary local assignments need not have a global section.

This is the ordinary assignment presheaf, with binary-cover gluing proved
directly. It can carry declared phenomenal descriptions as values, but it
does not identify sections, their unions, or their carriers with subjects.
Such an identification is additional structure.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.LocalSections

open _root_.CategoryTheory Opposite

universe u v

variable {Feature : Type u} {Value : Type v}

/-- An assignment of values to all features in a context. -/
abbrev Section (context : Set Feature) (Value : Type v) := context → Value

def restrict {small large : Set Feature} (included : small ⊆ large)
    (values : Section large Value) : Section small Value :=
  fun feature => values ⟨feature.val, included feature.property⟩

theorem restrict_identity {context : Set Feature} (values : Section context Value) :
    restrict (Set.Subset.refl context) values = values := rfl

theorem restrict_comp {small middle large : Set Feature}
    (first : small ⊆ middle) (second : middle ⊆ large) (values : Section large Value) :
    restrict first (restrict second values) = restrict (first.trans second) values := rfl

/-- This is an actual functor, including its substitution on values. -/
def presheaf (Feature : Type u) (Value : Type v) :
    (Set Feature)ᵒᵖ ⥤ Type (max u v) where
  obj context := Section context.unop Value
  map inclusion := TypeCat.ofHom (restrict inclusion.unop.le)
  map_id _ := by
    apply TypeCat.Hom.ext
    rfl
  map_comp _ _ := by
    apply TypeCat.Hom.ext
    rfl

/-- Agreement refers to each actual feature in the overlap. -/
def Compatible {left right : Set Feature}
    (first : Section left Value) (second : Section right Value) : Prop :=
  ∀ feature (inLeft : feature ∈ left) (inRight : feature ∈ right),
    first ⟨feature, inLeft⟩ = second ⟨feature, inRight⟩

open scoped Classical in
/-- Construct the union assignment; compatibility earns agreement with the
right-hand assignment on the overlap. -/
noncomputable def glue {left right : Set Feature}
    (first : Section left Value) (second : Section right Value) : Section (left ∪ right) Value :=
  fun feature => if inLeft : feature.val ∈ left then first ⟨feature.val, inLeft⟩
    else second ⟨feature.val, feature.property.resolve_left inLeft⟩

theorem glue_left {left right : Set Feature}
    (first : Section left Value) (second : Section right Value) :
    restrict Set.subset_union_left (glue first second) = first := by
  funext feature
  simp [restrict, glue, feature.property]

theorem glue_right {left right : Set Feature}
    {first : Section left Value} {second : Section right Value}
    (compatible : Compatible first second) :
    restrict Set.subset_union_right (glue first second) = second := by
  funext feature
  by_cases inLeft : feature.val ∈ left
  · simpa [restrict, glue, inLeft] using compatible feature.val inLeft feature.property
  · simp [restrict, glue, inLeft]

theorem restrictions_compatible {left right : Set Feature}
    (whole : Section (left ∪ right) Value) :
    Compatible (restrict Set.subset_union_left whole) (restrict Set.subset_union_right whole) :=
  fun _ _ _ => rfl

/-- Both restrictions determine the union assignment uniquely. -/
theorem section_ext {left right : Set Feature}
    {first second : Section (left ∪ right) Value}
    (sameLeft : restrict Set.subset_union_left first = restrict Set.subset_union_left second)
    (sameRight : restrict Set.subset_union_right first = restrict Set.subset_union_right second) :
    first = second := by
  funext feature
  rcases feature.property with inLeft | inRight
  · exact congrFun sameLeft ⟨feature.val, inLeft⟩
  · exact congrFun sameRight ⟨feature.val, inRight⟩

/-- Binary-cover gluing is an earned equivalence with compatible local data. -/
theorem gluing_iff {left right : Set Feature}
    (first : Section left Value) (second : Section right Value) :
    Compatible first second ↔ ∃! whole : Section (left ∪ right) Value,
      restrict Set.subset_union_left whole = first ∧
        restrict Set.subset_union_right whole = second := by
  constructor
  · intro compatible
    refine ⟨glue first second, ⟨glue_left first second, glue_right compatible⟩, ?_⟩
    intro other agrees
    exact section_ext (agrees.1.trans (glue_left first second).symm)
      (agrees.2.trans (glue_right compatible).symm)
  · rintro ⟨whole, ⟨leftAgree, rightAgree⟩, _⟩
    rw [← leftAgree, ← rightAgree]
    exact restrictions_compatible whole

/-- Re-encoding values commutes with restriction. -/
theorem map_restrict {Other : Type*} {small large : Set Feature}
    (included : small ⊆ large) (change : Value → Other) (values : Section large Value) :
    change ∘ restrict included values = restrict included (change ∘ values) := rfl

/-- Re-encoding commutes with the actual gluing construction. -/
theorem map_glue {Other : Type*} {left right : Set Feature}
    (change : Value → Other) (first : Section left Value) (second : Section right Value) :
    change ∘ glue first second = glue (change ∘ first) (change ∘ second) := by
  funext feature
  by_cases inLeft : feature.val ∈ left <;> simp [glue, inLeft]

namespace Controls

/-- The contexts overlap at feature `1` and each observes one extra feature. -/
def left : Set Nat := {0, 1}
def right : Set Nat := {1, 2}

def first (feature : left) : Nat := feature.val + 10
def second (feature : right) : Nat := feature.val + 10
def conflicting (feature : right) : Nat := feature.val + 20

theorem compatible_distinct_contexts : Compatible first second := fun _ _ _ => rfl

theorem glued_retains_both_sides :
    glue first second ⟨0, Or.inl (by simp [left])⟩ = 10 ∧
      glue first second ⟨2, Or.inr (by simp [right])⟩ = 12 := by
  simp [glue, first, second, left]

theorem conflict_prevents_gluing :
    ¬ ∃ whole : Section (left ∪ right) Nat,
      restrict Set.subset_union_left whole = first ∧
        restrict Set.subset_union_right whole = conflicting := by
  rintro ⟨whole, agreesLeft, agreesRight⟩
  have agree := restrictions_compatible whole 1 (by simp [left]) (by simp [right])
  rw [agreesLeft, agreesRight] at agree
  change 11 = 21 at agree
  omega

/-- Compatible descriptions need not determine how many identities their
carrier contains. Two distinct tokens can carry the same global assignment. -/
theorem copied_section_not_token_identity :
    ∃ first second : Bool × Section (left ∪ right) Nat,
      first.2 = second.2 ∧ first.1 ≠ second.1 :=
  ⟨(false, glue Controls.first Controls.second), (true, glue Controls.first Controls.second),
    rfl, by decide⟩

end Controls

/-! ## Arbitrary covers of observation contexts -/

universe w

variable {Index : Type w}

def FamilyCompatible (contexts : Index → Set Feature)
    (locals : (index : Index) → Section (contexts index) Value) : Prop :=
  ∀ first second feature (inFirst : feature ∈ contexts first)
    (inSecond : feature ∈ contexts second),
    locals first ⟨feature, inFirst⟩ = locals second ⟨feature, inSecond⟩

/-- Choose a covering context for each feature. Compatibility makes the
result independent of which covering context was chosen. -/
noncomputable def glueFamily (contexts : Index → Set Feature)
    (locals : (index : Index) → Section (contexts index) Value) :
    Section (⋃ index, contexts index) Value := fun feature =>
  let cover : ∃ index, feature.val ∈ contexts index := Set.mem_iUnion.mp feature.property
  locals (Classical.choose cover) ⟨feature.val, Classical.choose_spec cover⟩

theorem glueFamily_restrict (contexts : Index → Set Feature)
    {locals : (index : Index) → Section (contexts index) Value}
    (compatible : FamilyCompatible contexts locals) (index : Index) :
    restrict (Set.subset_iUnion contexts index) (glueFamily contexts locals) = locals index := by
  funext feature
  exact compatible _ index feature.val _ feature.property

theorem family_section_ext (contexts : Index → Set Feature)
    {first second : Section (⋃ index, contexts index) Value}
    (agrees : ∀ index, restrict (Set.subset_iUnion contexts index) first =
      restrict (Set.subset_iUnion contexts index) second) : first = second := by
  funext feature
  obtain ⟨index, belongs⟩ := Set.mem_iUnion.mp feature.property
  exact congrFun (agrees index) ⟨feature.val, belongs⟩

/-- The full assignment presheaf glues every compatible cover, not only
binary covers. This does not prove gluing for an arbitrary constrained
subpresheaf, as the restriction-stable negative control below demonstrates. -/
theorem family_gluing_iff (contexts : Index → Set Feature)
    (locals : (index : Index) → Section (contexts index) Value) :
    FamilyCompatible contexts locals ↔
      ∃! whole : Section (⋃ index, contexts index) Value,
        ∀ index, restrict (Set.subset_iUnion contexts index) whole = locals index := by
  constructor
  · intro compatible
    refine ⟨glueFamily contexts locals, glueFamily_restrict contexts compatible, ?_⟩
    intro other agrees
    exact family_section_ext contexts (fun index =>
      (agrees index).trans (glueFamily_restrict contexts compatible index).symm)
  · rintro ⟨whole, agrees, _⟩
    intro first second feature inFirst inSecond
    have left := congrFun (agrees first) ⟨feature, inFirst⟩
    have right := congrFun (agrees second) ⟨feature, inSecond⟩
    exact left.symm.trans right

theorem map_glueFamily {Other : Type*} (contexts : Index → Set Feature)
    (change : Value → Other) (locals : (index : Index) → Section (contexts index) Value) :
    change ∘ glueFamily contexts locals =
      glueFamily contexts (fun index => change ∘ locals index) := rfl

/-! ## Restrictions of a description do not supply all global constraints -/

/-- One possible coherence constraint on an assignment. It is deliberately
separate from agreement of two assignments on their overlap. -/
def Uniform {context : Set Feature} (values : Section context Value) : Prop :=
  ∀ first second, values first = values second

theorem uniform_restrict {small large : Set Feature} (included : small ⊆ large)
    {values : Section large Value} (uniform : Uniform values) :
    Uniform (restrict included values) :=
  fun _ _ => uniform _ _

/-- A shared feature propagates uniformity through a compatible overlap.
The inhabited-overlap hypothesis is substantive, as the control below shows. -/
theorem uniform_glue_of_overlap {left right : Set Feature}
    {first : Section left Value} {second : Section right Value}
    (compatible : Compatible first second) (firstUniform : Uniform first)
    (secondUniform : Uniform second)
    (overlap : ∃ feature, feature ∈ left ∧ feature ∈ right) :
    Uniform (glue first second) := by
  obtain ⟨anchor, inLeft, inRight⟩ := overlap
  have anchored : ∀ feature : ↥(left ∪ right),
      glue first second feature = first ⟨anchor, inLeft⟩ := by
    intro feature
    by_cases belongs : feature.val ∈ left
    · simpa [glue, belongs] using firstUniform ⟨feature.val, belongs⟩ ⟨anchor, inLeft⟩
    · simpa [glue, belongs] using
        (secondUniform ⟨feature.val, feature.property.resolve_left belongs⟩
          ⟨anchor, inRight⟩).trans (compatible anchor inLeft inRight).symm
  exact fun firstFeature secondFeature =>
    (anchored firstFeature).trans (anchored secondFeature).symm

namespace DisconnectedControls

def left : Set Bool := {false}
def right : Set Bool := {true}
def first (_ : left) : Bool := false
def second (_ : right) : Bool := true

theorem compatible_uniform_locals :
    Compatible first second ∧ Uniform first ∧ Uniform second := by
  refine ⟨?_, fun _ _ => rfl, fun _ _ => rfl⟩
  intro feature inLeft inRight
  simp only [left, right, Set.mem_singleton_iff] at inLeft inRight
  exact False.elim (Bool.false_ne_true (inLeft.symm.trans inRight))

/-- Even uniquely gluable local data need not satisfy a global constraint
which survives every restriction. Gluing descriptions is not integration. -/
theorem no_uniform_global_extension :
    ¬ ∃ whole : Section (left ∪ right) Bool,
      restrict Set.subset_union_left whole = first ∧
      restrict Set.subset_union_right whole = second ∧ Uniform whole := by
  rintro ⟨whole, firstAgree, secondAgree, uniform⟩
  have atFalse := congrFun firstAgree ⟨false, by simp [left]⟩
  have atTrue := congrFun secondAgree ⟨true, by simp [right]⟩
  have same := uniform ⟨false, Or.inl (by simp [left])⟩
    ⟨true, Or.inr (by simp [right])⟩
  change whole ⟨false, _⟩ = false at atFalse
  change whole ⟨true, _⟩ = true at atTrue
  exact Bool.false_ne_true (atFalse.symm.trans (same.trans atTrue))

end DisconnectedControls

end Mettapedia.CategoryTheory.LocalSections
