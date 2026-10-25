import Mettapedia.TypeTheory.IndexedPolynomial

/-!
# Equivalence of indexed-polynomial signatures

Two indexed polynomials present the same constructor signature when their
shape fibres are equivalent, their recursive-position fibres are equivalent
over corresponding shapes, and those position maps preserve the required
child index.  This is stronger than a carrier bijection and weaker than
definitional equality of presentations.

The comparison transports complete constructor layers naturally in the
recursive carrier. It therefore induces an equivalence of the fixed families;
folding commutes with both directions under the corresponding constructor
methods. These are semantic laws, independent of an object calculus's
judgmental conversion policy and of an executable representation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial

universe uB uI uS₁ uP₁ uS₂ uP₂ uC uD

variable {Base : Type uB} {Index : Base → Type uI}

/-- Fibrewise equivalence of complete polynomial signatures. -/
structure SignatureEquiv
    (first : IndexedPolynomial.{uB, uI, uS₁, uP₁} Base Index)
    (second : IndexedPolynomial.{uB, uI, uS₂, uP₂} Base Index) where
  shape : ∀ base index, first.Shape base index ≃ second.Shape base index
  position : ∀ {base index} (source : first.Shape base index),
    first.Position source ≃ second.Position (shape base index source)
  next_preserved : ∀ {base index} (source : first.Shape base index)
    (sourcePosition : first.Position source),
    second.next (shape base index source) (position source sourcePosition) =
      first.next source sourcePosition

namespace SignatureEquiv

def refl (polynomial : IndexedPolynomial.{uB, uI, uS₁, uP₁} Base Index) :
    SignatureEquiv polynomial polynomial where
  shape := fun _ _ => Equiv.refl _
  position := fun _ => Equiv.refl _
  next_preserved := fun _ _ => rfl

variable {P : IndexedPolynomial.{uB, uI, uS₁, uP₁} Base Index}
  {Q : IndexedPolynomial.{uB, uI, uS₂, uP₂} Base Index}

/-- Equivalent signatures transport constructor layers and every dependent child label. -/
def extensionEquiv (comparison : SignatureEquiv P Q)
    (carrier : ∀ base, Index base → Type uC) (base : Base) (index : Index base) :
    P.Extension carrier base index ≃ Q.Extension carrier base index :=
  Equiv.sigmaCongr (comparison.shape base index) fun shape =>
    Equiv.piCongr (comparison.position shape) fun position =>
      Equiv.cast (congrArg (carrier base) (comparison.next_preserved shape position).symm)

@[simp] theorem extensionEquiv_mk (comparison : SignatureEquiv P Q)
    (carrier : ∀ base, Index base → Type uC) {base : Base} {index : Index base}
    (shape : P.Shape base index)
    (children : ∀ position, carrier base (P.next shape position)) :
    extensionEquiv comparison carrier base index ⟨shape, children⟩ =
      ⟨comparison.shape base index shape,
        (comparison.position shape).piCongr
          (fun position => Equiv.cast
            (congrArg (carrier base) (comparison.next_preserved shape position).symm)) children⟩ := rfl

private theorem cast_map
    {base : Base} {first second : Index base}
    {source : ∀ base, Index base → Type uC}
    {target : ∀ base, Index base → Type uD}
    (mapping : ∀ base index, source base index → target base index)
    (same : first = second) (value : source base first) :
    cast (congrArg (target base) same) (mapping base first value) =
      mapping base second (cast (congrArg (source base) same) value) := by
  cases same
  rfl

/-- Layer transport commutes with arbitrary maps of the recursive carrier family. -/
theorem extensionEquiv_natural (comparison : SignatureEquiv P Q)
    {source : ∀ base, Index base → Type uC}
    {target : ∀ base, Index base → Type uD}
    (mapping : ∀ base index, source base index → target base index)
    {base : Base} {index : Index base} (layer : P.Extension source base index) :
    extensionEquiv comparison target base index (Extension.map P mapping layer) =
      Extension.map Q mapping (extensionEquiv comparison source base index layer) := by
  rcases layer with ⟨shape, children⟩
  simp only [Extension.map, extensionEquiv_mk]
  apply Sigma.ext
  · rfl
  apply heq_of_eq
  funext position
  obtain ⟨sourcePosition, rfl⟩ := (comparison.position shape).surjective position
  simp only [Equiv.piCongr_apply_apply, Equiv.cast_apply]
  exact cast_map mapping (comparison.next_preserved shape sourcePosition).symm
    (children sourcePosition)

theorem extensionEquiv_symm_natural (comparison : SignatureEquiv P Q)
    {source : ∀ base, Index base → Type uC}
    {target : ∀ base, Index base → Type uD}
    (mapping : ∀ base index, source base index → target base index)
    {base : Base} {index : Index base} (layer : Q.Extension source base index) :
    (extensionEquiv comparison target base index).symm (Extension.map Q mapping layer) =
      Extension.map P mapping ((extensionEquiv comparison source base index).symm layer) := by
  apply (extensionEquiv comparison target base index).injective
  rw [Equiv.apply_symm_apply, extensionEquiv_natural, Equiv.apply_symm_apply]

/-- Rebuild a recursive value using the target constructor shapes and positions. -/
noncomputable def toFix (comparison : SignatureEquiv P Q) :
    ∀ base index, Fix P base index → Fix Q base index :=
  Fix.fold P fun base index layer =>
    Fix.rollExtension Q (extensionEquiv comparison (Fix Q) base index layer)

/-- Rebuild a recursive value using the inverse layer comparison. -/
noncomputable def fromFix (comparison : SignatureEquiv P Q) :
    ∀ base index, Fix Q base index → Fix P base index :=
  Fix.fold Q fun base index layer =>
    Fix.rollExtension P ((extensionEquiv comparison (Fix P) base index).symm layer)

@[simp] theorem toFix_rollExtension (comparison : SignatureEquiv P Q)
    {base : Base} {index : Index base} (layer : P.Extension (Fix P) base index) :
    toFix comparison base index (Fix.rollExtension P layer) =
      Fix.rollExtension Q (extensionEquiv comparison (Fix Q) base index
        (Extension.map P (toFix comparison) layer)) := by
  cases layer
  rfl

@[simp] theorem fromFix_rollExtension (comparison : SignatureEquiv P Q)
    {base : Base} {index : Index base} (layer : Q.Extension (Fix Q) base index) :
    fromFix comparison base index (Fix.rollExtension Q layer) =
      Fix.rollExtension P ((extensionEquiv comparison (Fix P) base index).symm
        (Extension.map Q (fromFix comparison) layer)) := by
  cases layer
  rfl

@[simp] theorem fromFix_toFix (comparison : SignatureEquiv P Q)
    (base : Base) (index : Index base) (tree : Fix P base index) :
    fromFix comparison base index (toFix comparison base index tree) = tree := by
  induction tree with
  | roll shape children ih =>
      let layer : P.Extension (Fix P) base _ := ⟨shape, children⟩
      change fromFix comparison base _ (toFix comparison base _
        (Fix.rollExtension P layer)) = Fix.rollExtension P layer
      rw [toFix_rollExtension, fromFix_rollExtension,
        ← extensionEquiv_natural, Equiv.symm_apply_apply]
      change Fix.rollExtension P ⟨shape,
        fun position => fromFix comparison base _
          (toFix comparison base _ (children position))⟩ =
        Fix.rollExtension P ⟨shape, children⟩
      congr 1
      apply Sigma.ext
      · rfl
      apply heq_of_eq
      funext position
      exact ih position

@[simp] theorem toFix_fromFix (comparison : SignatureEquiv P Q)
    (base : Base) (index : Index base) (tree : Fix Q base index) :
    toFix comparison base index (fromFix comparison base index tree) = tree := by
  induction tree with
  | roll shape children ih =>
      let layer : Q.Extension (Fix Q) base _ := ⟨shape, children⟩
      change toFix comparison base _ (fromFix comparison base _
        (Fix.rollExtension Q layer)) = Fix.rollExtension Q layer
      rw [fromFix_rollExtension, toFix_rollExtension,
        ← extensionEquiv_symm_natural, Equiv.apply_symm_apply]
      change Fix.rollExtension Q ⟨shape,
        fun position => toFix comparison base _
          (fromFix comparison base _ (children position))⟩ =
        Fix.rollExtension Q ⟨shape, children⟩
      congr 1
      apply Sigma.ext
      · rfl
      apply heq_of_eq
      funext position
      exact ih position

/-- A complete signature comparison induces an equivalence of recursive families. -/
noncomputable def fixEquiv (comparison : SignatureEquiv P Q)
    (base : Base) (index : Index base) : Fix P base index ≃ Fix Q base index where
  toFun := toFix comparison base index
  invFun := fromFix comparison base index
  left_inv := fromFix_toFix comparison base index
  right_inv := toFix_fromFix comparison base index

/-- Transport target constructor methods to source layers. -/
def pullAlgebra (comparison : SignatureEquiv P Q)
    {carrier : ∀ base, Index base → Type uC} (algebra : Algebra Q carrier) :
    Algebra P carrier where
  act base index layer :=
    algebra.act base index (extensionEquiv comparison carrier base index layer)

/-- Transport source constructor methods to target layers. -/
def pushAlgebra (comparison : SignatureEquiv P Q)
    {carrier : ∀ base, Index base → Type uC} (algebra : Algebra P carrier) :
    Algebra Q carrier where
  act base index layer :=
    algebra.act base index ((extensionEquiv comparison carrier base index).symm layer)

private theorem fold_rollExtension
    {polynomial : IndexedPolynomial.{uB, uI, uS₁, uP₁} Base Index}
    {carrier : ∀ base, Index base → Type uC} (algebra : Algebra polynomial carrier)
    {base : Base} {index : Index base} (layer : polynomial.Extension (Fix polynomial) base index) :
    Fix.fold polynomial algebra.act base index (Fix.rollExtension polynomial layer) =
      algebra.act base index (Extension.map polynomial (Fix.fold polynomial algebra.act) layer) := by
  cases layer
  rfl

/-- Target recursion agrees with source recursion under the transported methods. -/
theorem fold_toFix (comparison : SignatureEquiv P Q)
    {carrier : ∀ base, Index base → Type uC} (algebra : Algebra Q carrier)
    (base : Base) (index : Index base) (tree : Fix P base index) :
    Fix.fold Q algebra.act base index (toFix comparison base index tree) =
      Fix.fold P (pullAlgebra comparison algebra).act base index tree := by
  let homomorphism : Algebra.Hom (Algebra.initial P) (pullAlgebra comparison algebra) :=
    { toFun := fun base index tree =>
        Fix.fold Q algebra.act base index (toFix comparison base index tree)
      commutes := by
        intro base index layer
        change Fix.fold Q algebra.act base index
            (toFix comparison base index (Fix.rollExtension P layer)) =
          algebra.act base index (extensionEquiv comparison carrier base index
            (Extension.map P (fun base index tree =>
              Fix.fold Q algebra.act base index (toFix comparison base index tree)) layer))
        rw [toFix_rollExtension, fold_rollExtension,
          ← extensionEquiv_natural]
        cases layer
        rfl }
  exact Algebra.hom_eq_fold (pullAlgebra comparison algebra) homomorphism base index tree

/-- Source recursion agrees with target recursion under the inverse transport. -/
theorem fold_fromFix (comparison : SignatureEquiv P Q)
    {carrier : ∀ base, Index base → Type uC} (algebra : Algebra P carrier)
    (base : Base) (index : Index base) (tree : Fix Q base index) :
    Fix.fold P algebra.act base index (fromFix comparison base index tree) =
      Fix.fold Q (pushAlgebra comparison algebra).act base index tree := by
  let homomorphism : Algebra.Hom (Algebra.initial Q) (pushAlgebra comparison algebra) :=
    { toFun := fun base index tree =>
        Fix.fold P algebra.act base index (fromFix comparison base index tree)
      commutes := by
        intro base index layer
        change Fix.fold P algebra.act base index
            (fromFix comparison base index (Fix.rollExtension Q layer)) =
          algebra.act base index ((extensionEquiv comparison carrier base index).symm
            (Extension.map Q (fun base index tree =>
              Fix.fold P algebra.act base index (fromFix comparison base index tree)) layer))
        rw [fromFix_rollExtension, fold_rollExtension,
          ← extensionEquiv_symm_natural]
        cases layer
        rfl }
  exact Algebra.hom_eq_fold (pushAlgebra comparison algebra) homomorphism base index tree

end SignatureEquiv

#print axioms SignatureEquiv.refl
#print axioms SignatureEquiv.extensionEquiv_natural
#print axioms SignatureEquiv.fixEquiv
#print axioms SignatureEquiv.fold_toFix
#print axioms SignatureEquiv.fold_fromFix

end Mettapedia.TypeTheory.IndexedPolynomial
