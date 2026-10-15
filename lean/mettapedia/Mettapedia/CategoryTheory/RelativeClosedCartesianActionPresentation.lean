import Mettapedia.CategoryTheory.CartesianMonoidActionFunctor
import Mettapedia.CategoryTheory.RelativeClosedSyntaxEquationInterpretation
import Mettapedia.CategoryTheory.RelativeClosedSyntaxInterpretationLimits

/-!
# A generated presentation of the two complete action diagrams

The two new declarations are parallel typed arrows of the original free
finite-limit and closed presentation. They impose the edge unit and edge
associativity equations without identifying the original operation origins.
The inclusion is an actual finite-limit and closed theory map.

A locally realized original model extends exactly when the transported
complete edge operations satisfy the two action diagrams. Its restriction
recovers the whole original interpretation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.CartesianActionPresentation

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory
open GeneratedCategory

universe k w z

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable (signature : Signature (C := C) (symbols := symbols))
variable (data : CartesianMonoidAction.Data (Object signature))

inductive Law where
  | unit
  | associativity
  deriving DecidableEq

def declaration : ULift.{k} Law → EquationExtension.Declaration signature
  | ⟨.unit⟩ => ⟨data.edge, data.edge,
      representative (CartesianMonoidAction.unitDiagram data), RawHom.identity data.edge⟩
  | ⟨.associativity⟩ => ⟨(data.edge ⊗ data.scalar) ⊗ data.scalar, data.edge,
      representative (CartesianMonoidAction.twiceDiagram data),
      representative (CartesianMonoidAction.mergedDiagram data)⟩

abbrev extended := EquationExtension.extend signature (declaration signature data)
abbrev inclusion := EquationExtension.inclusion signature (declaration signature data)

def headers (original : HeaderFormation signature) : HeaderFormation (extended signature data) :=
  EquationExtension.headers signature (declaration signature data) original

abbrev signatureData {E : Type k} [Category.{k} E] {nextSymbols : Symbols.{k}}
    {next : Signature (C := E) (symbols := nextSymbols)} (mapping : SignatureMap signature next) :
    CartesianMonoidAction.Data (Object next) where
  edge := mapping.functor.obj data.edge
  scalar := mapping.functor.obj data.scalar
  zero := mapping.functor.map data.zero
  merge := mapping.functor.map data.merge
  act := mapping.functor.map data.act

theorem map_eq_signatureData {E : Type k} [Category.{k} E] {nextSymbols : Symbols.{k}}
    {next : Signature (C := E) (symbols := nextSymbols)} (mapping : SignatureMap signature next) :
    CartesianMonoidAction.map mapping.functor data = signatureData signature data mapping := by
  have terminalInverse : inv (terminalComparison mapping.functor) = 𝟙 (terminal next) := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [mapping.terminalComparison_identity]
    exact Category.id_comp (𝟙 (terminal next))
  have productInverse (first second : Object signature) :
      inv (prodComparison mapping.functor first second) =
        𝟙 (mapping.functor.obj first ⊗ mapping.functor.obj second) := by
    apply IsIso.inv_eq_of_hom_inv_id
    rw [mapping.productComparison_identity]
    exact Category.id_comp (𝟙 (product (mapping.functor.obj first) (mapping.functor.obj second)))
  have zeroIdentity : 𝟙 (terminal next) ≫ mapping.functor.map data.zero = mapping.functor.map data.zero :=
    Category.id_comp (mapping.functor.map data.zero)
  simp only [CartesianMonoidAction.map, signatureData,
    terminalInverse, productInverse, zeroIdentity, Category.id_comp]

def operations : CartesianMonoidAction.Data (Object (extended signature data)) :=
  signatureData signature data (inclusion signature data)

theorem action_laws : CartesianMonoidAction.Laws (operations signature data) := by
  rw [operations, ← map_eq_signatureData]
  apply (CartesianMonoidAction.mapped_laws_iff (inclusion signature data).functor data).mpr
  constructor
  · have law := EquationExtension.equation_class signature (declaration signature data) ⟨.unit⟩
    simp only [declaration, classOf_representative, classOf_identity] at law
    change (inclusion signature data).functor.map (CartesianMonoidAction.unitDiagram data) =
      (inclusion signature data).functor.map (𝟙 data.edge) at law
    rw [(inclusion signature data).functor.map_id] at law
    exact law
  · have law := EquationExtension.equation_class signature (declaration signature data) ⟨.associativity⟩
    simpa only [declaration, classOf_representative] using law

def theory := EquationExtension.theory signature (declaration signature data)
def theoryMap := EquationExtension.theoryMap signature (declaration signature data)

section Models

variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [_root_.CategoryTheory.Limits.HasFiniteLimits D]
variable (meanings : Interpretation.Assignment C symbols D)
variable (realized : Interpretation.Realization signature meanings)

def modelOperations : CartesianMonoidAction.Data D :=
  CartesianMonoidAction.map (Interpretation.functor meanings realized) data

theorem satisfaction_iff_action :
    EquationExtension.Satisfies signature (declaration signature data) meanings realized ↔
      CartesianMonoidAction.Laws (modelOperations signature data meanings realized) := by
  rw [modelOperations, CartesianMonoidAction.mapped_laws_iff]
  constructor
  · intro satisfied
    refine ⟨?_, ?_⟩
    · have law := satisfied ⟨.unit⟩
      change (Interpretation.functor meanings realized).map (classOf
        (representative (CartesianMonoidAction.unitDiagram data))) =
          (Interpretation.functor meanings realized).map (𝟙 data.edge) at law
      rw [classOf_representative, (Interpretation.functor meanings realized).map_id] at law
      exact law
    · have law := satisfied ⟨.associativity⟩
      simpa only [declaration, classOf_representative] using law
  · rintro ⟨unit, associativity⟩ ⟨origin⟩
    cases origin with
    | unit =>
        change (Interpretation.functor meanings realized).map (classOf
          (representative (CartesianMonoidAction.unitDiagram data))) =
            (Interpretation.functor meanings realized).map (𝟙 data.edge)
        rw [classOf_representative, (Interpretation.functor meanings realized).map_id]
        exact unit
    | associativity => simpa only [declaration, classOf_representative] using associativity

theorem admission_iff_action :
    Interpretation.Realization (extended signature data)
        (EquationExtension.extendAssignment (Index := ULift.{k} Law) meanings) ↔
      CartesianMonoidAction.Laws (modelOperations signature data meanings realized) :=
  (EquationExtension.realization_iff_satisfaction signature (declaration signature data) meanings realized).trans
    (satisfaction_iff_action signature data meanings realized)

def interpretation (laws : CartesianMonoidAction.Laws (modelOperations signature data meanings realized)) :
    Object (extended signature data) ⥤ D :=
  Interpretation.functor (EquationExtension.extendAssignment (Index := ULift.{k} Law) meanings)
    ((admission_iff_action signature data meanings realized).mpr laws)

theorem complete_restriction (laws : CartesianMonoidAction.Laws (modelOperations signature data meanings realized)) :
    (inclusion signature data).functor ⋙ interpretation signature data meanings realized laws =
      Interpretation.functor meanings realized :=
  EquationExtension.complete_restriction signature (declaration signature data) meanings realized
    ((satisfaction_iff_action signature data meanings realized).mpr laws)

end Models

end Mettapedia.CategoryTheory.RelativeClosedSyntax.CartesianActionPresentation
