import Mettapedia.CategoryTheory.RelativeClosedSyntaxSignatureMapComposition

/-!
# Exact generated functor identity and composition

The independently composed declaration map and sequential interpretation
have equal complete object codes. Their mapped raw arrow codes also agree.
Endpoint transport and quotient induction derive equality of the actual
generated functors, with independent category and symbol sizes.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.SignatureMap

open _root_.CategoryTheory GeneratedCategory

universe u v a w z b r h c

variable {C : Type u} [Category.{v} C] {firstSymbols : Symbols.{a}}
variable {D : Type w} [Category.{z} D] {secondSymbols : Symbols.{b}}
variable {E : Type r} [Category.{h} E] {thirdSymbols : Symbols.{c}}
variable {first : Signature (C := C) (symbols := firstSymbols)}
variable {second : Signature (C := D) (symbols := secondSymbols)}
variable {third : Signature (C := E) (symbols := thirdSymbols)}

private theorem classOf_heq {source target before after : Object third}
    (left : RawHom source target) (right : RawHom before after)
    (sourceSame : source = before) (targetSame : target = after)
    (codes : left.code = right.code) : HEq (classOf left) (classOf right) := by
  subst before
  subst after
  exact heq_of_eq (congrArg classOf (RawHom.ext codes))

theorem functor_compose (before : SignatureMap first second) (after : SignatureMap second third) :
    (before.compose after).functor = before.functor ⋙ after.functor := by
  refine _root_.CategoryTheory.Functor.hext
    (F := (before.compose after).functor) (G := before.functor ⋙ after.functor)
    (fun object => (object_compose before after object).symm) ?_
  intro source target arrow
  refine Quotient.inductionOn arrow ?_
  intro raw
  exact classOf_heq ((before.compose after).rawArrow raw) (after.rawArrow (before.rawArrow raw))
    (object_compose before after source).symm (object_compose before after target).symm
      (arrow_code_compose before after raw).symm

theorem functor_identity (signature : Signature (C := C) (symbols := firstSymbols)) :
    (identity signature).functor = 𝟭 (Object signature) := by
  refine _root_.CategoryTheory.Functor.hext
    (F := (identity signature).functor) (G := 𝟭 (Object signature))
    (fun object => Object.ext (ObjectCode.map_identity object.code)) ?_
  intro source target arrow
  refine Quotient.inductionOn arrow ?_
  intro raw
  exact classOf_heq ((identity signature).rawArrow raw) raw
    (Object.ext (ObjectCode.map_identity source.code)) (Object.ext (ObjectCode.map_identity target.code))
      (ArrowCode.map_identity raw.code)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.SignatureMap
