import Mettapedia.TypeTheory.IndexedPolynomialInduction

/-!
# Substitution coherence for polynomial dependent elimination

The canonical comparison for a base substitution retains every constructor and
child. These comparisons preserve identities and composition. Pulling a
displayed algebra back along that comparison gives the same dependent result
whether elimination is performed before or after the base substitution.

The equalities are semantic coherence laws. They do not introduce conversion
rules into an object language.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial

universe uBase uIndex uShape uPosition uNewBase uThirdBase uFamily uCarrier uValue

variable {Base : Type uBase} {Index : Base → Type uIndex}
variable (P : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base Index)

namespace Fix

/-- The canonical comparison for the identity base substitution is identity. -/
@[simp] theorem reindexTo_id {base : Base} {index : Index base}
    (tree : Fix (P.reindex id) base index) :
    reindexTo P id tree = tree := by
  induction tree with
  | roll shape children hypotheses =>
      change Fix.roll shape (fun position => reindexTo P id (children position)) =
        Fix.roll shape children
      congr 1
      funext position
      exact hypotheses position

/-- Consecutive base substitutions use the same canonical comparison as their
composite. The comparison retains constructors and recursive positions. -/
theorem reindexTo_comp
    {NewBase : Type uNewBase} {ThirdBase : Type uThirdBase}
    (first : NewBase → Base) (second : ThirdBase → NewBase)
    {base : ThirdBase} {index : Index (first (second base))}
    (tree : Fix ((P.reindex first).reindex second) base index) :
    reindexTo P first (reindexTo (P.reindex first) second tree) =
      reindexTo P (first ∘ second) tree := by
  refine @Fix.rec ThirdBase (fun base => Index (first (second base)))
    ((P.reindex first).reindex second) base
    (fun index tree =>
      reindexTo P first (reindexTo (P.reindex first) second tree) =
        reindexTo P (first ∘ second) tree)
    ?_ index tree
  intro index shape children hypotheses
  change Fix.roll (polynomial := P) shape (fun position => reindexTo P first
      (reindexTo (P.reindex first) second (children position))) =
    Fix.roll (polynomial := P) shape
      (fun position => reindexTo P (first ∘ second) (children position))
  congr 1
  funext position
  exact hypotheses position

end Fix

namespace Algebra.Displayed

variable {P}
variable {motive : ∀ base index, Fix P base index → Sort uFamily}

private theorem transport_value {Carrier : Sort uCarrier}
    {family : Carrier → Sort uValue} (value : ∀ input, family input)
    {first second : Carrier} (same : first = second) :
    same ▸ value first = value second := by
  cases same
  rfl

/-- The displayed methods after substituting base parameters. The motive is
pulled back along the canonical constructor-preserving comparison. -/
noncomputable def reindex
    (displayed : Displayed (Algebra.initial P) motive)
    {NewBase : Type uNewBase} (substitution : NewBase → Base) :
    Displayed (Algebra.initial (P.reindex substitution))
      (fun base index tree => motive (substitution base) index
        (Fix.reindexTo P substitution tree)) where
  act := fun base index shape children hypotheses =>
    displayed.act (substitution base) index shape
      (fun position => Fix.reindexTo P substitution (children position)) hypotheses

/-- Any section pulls back to the substituted displayed algebra. -/
noncomputable def reindexSection
    (displayed : Displayed (Algebra.initial P) motive)
    (chosen : displayed.Section)
    {NewBase : Type uNewBase} (substitution : NewBase → Base) :
    (displayed.reindex substitution).Section where
  toFun := fun base index tree => chosen.toFun (substitution base) index
    (Fix.reindexTo P substitution tree)
  commutes := by
    intro base index shape children
    exact chosen.commutes (substitution base) index shape
      (fun position => Fix.reindexTo P substitution (children position))

/-- Dependent elimination commutes with arbitrary base substitution, including
substitutions which identify distinct parameter contexts. -/
theorem reindex_initialSection
    (displayed : Displayed (Algebra.initial P) motive)
    {NewBase : Type uNewBase} (substitution : NewBase → Base)
    (base : NewBase) (index : Index (substitution base))
    (tree : Fix (P.reindex substitution) base index) :
    displayed.initialSection.toFun (substitution base) index
        (Fix.reindexTo P substitution tree) =
      (displayed.reindex substitution).initialSection.toFun base index tree :=
  initialSection_unique (displayed.reindex substitution)
    (displayed.reindexSection displayed.initialSection substitution) base index tree

/-- Following two comparison routes gives the same dependent answer after
transport along the proved equality of their reconstructed terms. -/
theorem initialSection_reindex_comp
    (displayed : Displayed (Algebra.initial P) motive)
    {NewBase : Type uNewBase} {ThirdBase : Type uThirdBase}
    (first : NewBase → Base) (second : ThirdBase → NewBase)
    (base : ThirdBase) (index : Index (first (second base)))
    (tree : Fix ((P.reindex first).reindex second) base index) :
    (Fix.reindexTo_comp P first second tree) ▸
        ((displayed.reindex first).reindex second).initialSection.toFun base index tree =
      (displayed.reindex (first ∘ second)).initialSection.toFun base index tree := by
  rw [← reindex_initialSection (displayed.reindex first) second,
    ← reindex_initialSection displayed first]
  exact (transport_value (displayed.initialSection.toFun (first (second base)) index)
    (Fix.reindexTo_comp P first second tree)).trans
      (reindex_initialSection displayed (first ∘ second) base index tree)

end Algebra.Displayed

#print axioms Fix.reindexTo_id
#print axioms Fix.reindexTo_comp
#print axioms Algebra.Displayed.reindex_initialSection
#print axioms Algebra.Displayed.initialSection_reindex_comp

end Mettapedia.TypeTheory.IndexedPolynomial
