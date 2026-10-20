import Mettapedia.TypeTheory.IndexedPolynomial

/-!
# Displayed algebras for indexed polynomial families

A displayed algebra is a family over an indexed algebra, with a dependent
method for each constructor. Its sections are dependent eliminators satisfying
the constructor equations. The existing polynomial fixed family admits a unique
section for every displayed algebra, and this section is natural under maps of
fibres preserving the methods.

These laws concern semantic dependent elimination. They do not select an
object language's judgmental equality, universe policy, or runtime encoding.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial

universe uBase uIndex uShape uPosition uCarrier uFamily uOther

variable {Base : Type uBase} {Index : Base → Type uIndex}
variable {P : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base Index}

namespace Algebra

/-- Dependent constructor methods over an indexed polynomial algebra. -/
structure Displayed
    {carrier : (base : Base) → Index base → Type uCarrier}
    (algebra : Algebra P carrier)
    (family : ∀ base index, carrier base index → Sort uFamily) where
  act : ∀ base index (shape : P.Shape base index)
    (children : ∀ position, carrier base (P.next shape position)),
    (∀ position, family base (P.next shape position) (children position)) →
      family base index (algebra.act base index ⟨shape, children⟩)

namespace Displayed

variable {carrier : (base : Base) → Index base → Type uCarrier}
variable {algebra : Algebra P carrier}
variable {family : ∀ base index, carrier base index → Sort uFamily}

/-- A dependent section respecting all constructor methods. -/
structure Section (displayed : Displayed algebra family) where
  toFun : ∀ base index value, family base index value
  commutes : ∀ base index (shape : P.Shape base index)
    (children : ∀ position, carrier base (P.next shape position)),
    toFun base index (algebra.act base index ⟨shape, children⟩) =
      displayed.act base index shape children
        (fun position => toFun base (P.next shape position) (children position))

namespace Section

variable {displayed : Displayed algebra family}

/-- Sections are determined by their dependent values. -/
theorem ext (first second : displayed.Section)
    (same : ∀ base index value,
      first.toFun base index value = second.toFun base index value) :
    first = second := by
  cases first with
  | mk first firstCommutes =>
    cases second with
    | mk second secondCommutes =>
      have values : first = second := funext fun base => funext fun index =>
        funext fun value => same base index value
      cases values
      rfl

/-- Map a dependent section along fibre maps that respect the methods. -/
def map (chosen : displayed.Section)
    {otherFamily : ∀ base index, carrier base index → Sort uOther}
    (other : Displayed algebra otherFamily)
    (mapping : ∀ base index value, family base index value → otherFamily base index value)
    (preserves : ∀ base index (shape : P.Shape base index)
      (children : ∀ position, carrier base (P.next shape position))
      (hypotheses : ∀ position, family base (P.next shape position) (children position)),
      mapping base index (algebra.act base index ⟨shape, children⟩)
          (displayed.act base index shape children hypotheses) =
        other.act base index shape children
          (fun position => mapping base (P.next shape position) (children position)
            (hypotheses position))) :
    other.Section where
  toFun := fun base index value => mapping base index value (chosen.toFun base index value)
  commutes := by
    intro base index shape children
    rw [chosen.commutes]
    exact preserves base index shape children _

@[simp] theorem map_toFun (chosen : displayed.Section)
    {otherFamily : ∀ base index, carrier base index → Sort uOther}
    (other : Displayed algebra otherFamily)
    (mapping : ∀ base index value, family base index value → otherFamily base index value)
    (preserves : ∀ base index (shape : P.Shape base index)
      (children : ∀ position, carrier base (P.next shape position))
      (hypotheses : ∀ position, family base (P.next shape position) (children position)),
      mapping base index (algebra.act base index ⟨shape, children⟩)
          (displayed.act base index shape children hypotheses) =
        other.act base index shape children
          (fun position => mapping base (P.next shape position) (children position)
            (hypotheses position)))
    (base : Base) (index : Index base) (value : carrier base index) :
    (chosen.map other mapping preserves).toFun base index value =
      mapping base index value (chosen.toFun base index value) := rfl

end Section

variable {motive : ∀ base index, Fix P base index → Sort uFamily}

/-- Initial polynomial families support dependent elimination into every
displayed algebra. The function is the existing fixed-family eliminator. -/
noncomputable def initialSection
    (displayed : Displayed (Algebra.initial P) motive) : displayed.Section where
  toFun := Fix.eliminate P motive displayed.act
  commutes := by intros; rfl

@[simp] theorem initialSection_roll
    (displayed : Displayed (Algebra.initial P) motive)
    (base : Base) (index : Index base) (shape : P.Shape base index)
    (children : ∀ position, Fix P base (P.next shape position)) :
    displayed.initialSection.toFun base index (.roll shape children) =
      displayed.act base index shape children
        (fun position => displayed.initialSection.toFun base
          (P.next shape position) (children position)) := rfl

/-- The dependent constructor equations determine the whole section. -/
theorem initialSection_unique
    (displayed : Displayed (Algebra.initial P) motive)
    (chosen : displayed.Section)
    (base : Base) (index : Index base) (tree : Fix P base index) :
    chosen.toFun base index tree = displayed.initialSection.toFun base index tree := by
  induction tree with
  | roll shape children hypotheses =>
      change chosen.toFun base _
          ((Algebra.initial P).act base _ ⟨shape, children⟩) = _
      rw [chosen.commutes, initialSection_roll]
      congr 1
      funext position
      exact hypotheses position

/-- There is exactly one section of each displayed algebra over the initial
polynomial family. This does not assert uniqueness over arbitrary algebras. -/
theorem initialSection_subsingleton
    (displayed : Displayed (Algebra.initial P) motive) :
    Subsingleton displayed.Section := by
  constructor
  intro first second
  apply Section.ext
  intro base index tree
  exact (initialSection_unique displayed first base index tree).trans
    (initialSection_unique displayed second base index tree).symm

/-- Method-preserving fibre maps commute with dependent elimination. -/
theorem initialSection_naturality
    (displayed : Displayed (Algebra.initial P) motive)
    {otherMotive : ∀ base index, Fix P base index → Sort uOther}
    (other : Displayed (Algebra.initial P) otherMotive)
    (mapping : ∀ base index tree, motive base index tree → otherMotive base index tree)
    (preserves : ∀ base index (shape : P.Shape base index)
      (children : ∀ position, Fix P base (P.next shape position))
      (hypotheses : ∀ position, motive base (P.next shape position) (children position)),
      mapping base index (.roll shape children)
          (displayed.act base index shape children hypotheses) =
        other.act base index shape children
          (fun position => mapping base (P.next shape position) (children position)
            (hypotheses position)))
    (base : Base) (index : Index base) (tree : Fix P base index) :
    mapping base index tree (displayed.initialSection.toFun base index tree) =
      other.initialSection.toFun base index tree :=
  initialSection_unique other (displayed.initialSection.map other mapping preserves)
    base index tree

#print axioms initialSection
#print axioms initialSection_unique
#print axioms initialSection_subsingleton
#print axioms initialSection_naturality

end Displayed
end Algebra
end Mettapedia.TypeTheory.IndexedPolynomial
