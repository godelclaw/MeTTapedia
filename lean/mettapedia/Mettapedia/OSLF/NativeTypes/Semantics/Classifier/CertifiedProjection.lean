import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Operations

/-! # Certified classifier values retain their code and actual sort evidence -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Classifier.CertifiedProjection

open _root_.CategoryTheory Opposite
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.TypeTheory
open NativeLocalTypeFormers ContextualLocalUniverses
open Calculi.NativeDependent.Refinement
open DisplayedPresheafTransport DisplayedPresheafComprehension
open Families Operations

universe u
variable {D : Presheaf.CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)

noncomputable section

def certifiedEncode (carrier : D.Carrier) (kind : HSort)
    (point : (Families.emptyScope (W := W)).1.Elements)
    (value : (validPresheaf operational carrier kind).obj point.1) :
    (certifiedMeaning operational carrier kind).decoded.obj point :=
  (certifiedDecodeIso operational carrier kind).inv.app point
    ⟨value.val, ⟨⟨(value.val, .sort kind), value.property⟩, rfl⟩⟩

theorem certifiedRead_encode (carrier : D.Carrier) (kind : HSort)
    (point : (Families.emptyScope (W := W)).1.Elements)
    (value : (validPresheaf operational carrier kind).obj point.1) :
    (certifiedRead operational carrier kind).app point
      (certifiedEncode operational carrier kind point value) = value := by
  apply Subtype.ext
  change ((certifiedDecodeIso operational carrier kind).hom.app point
    ((certifiedDecodeIso operational carrier kind).inv.app point _)).1 = value.val
  exact congrArg Sigma.fst (ConcreteCategory.congr_hom
    (NatTrans.congr_app (certifiedDecodeIso operational carrier kind).inv_hom_id point) _)

theorem certifiedEncode_read (carrier : D.Carrier) (kind : HSort)
    (point : (Families.emptyScope (W := W)).1.Elements)
    (value : (certifiedMeaning operational carrier kind).decoded.obj point) :
    certifiedEncode operational carrier kind point
      ((certifiedRead operational carrier kind).app point value) = value := by
  let pair := (certifiedDecodeIso operational carrier kind).hom.app point value
  have codes : pair.2.val.val = (pair.1, .sort kind) := pair.2.property
  have pairSame :
      (⟨pair.1, ⟨⟨(pair.1, .sort kind),
        ((certifiedRead operational carrier kind).app point value).property⟩, rfl⟩⟩ :
        (DisplayedPresheafSigma.sigmaDisplayed (codeMeaning operational carrier).decoded
          (certifiedBody operational carrier kind).decoded).obj point) = pair := by
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    exact codes.symm
  have replaced := congrArg ((certifiedDecodeIso operational carrier kind).inv.app point) pairSame
  have roundtrip := ConcreteCategory.congr_hom
    (NatTrans.congr_app (certifiedDecodeIso operational carrier kind).hom_inv_id point) value
  exact replaced.trans roundtrip

def certifiedEquiv (carrier : D.Carrier) (kind : HSort)
    (point : (Families.emptyScope (W := W)).1.Elements) :
    (certifiedMeaning operational carrier kind).decoded.obj point ≃
      (validPresheaf operational carrier kind).obj point.1 where
  toFun := (certifiedRead operational carrier kind).app point
  invFun := certifiedEncode operational carrier kind point
  left_inv := certifiedEncode_read operational carrier kind point
  right_inv := certifiedRead_encode operational carrier kind point

abbrev certifiedAt (carrier : D.Carrier) (kind : HSort) (P : Wᵒᵖ ⥤ Type u) :=
  (certifiedMeaning operational carrier kind).reindex ((NativeModel W).toEmpty P)

def certifiedAtEquiv (carrier : D.Carrier) (kind : HSort) (P : Wᵒᵖ ⥤ Type u)
    (point : P.Elements) :
    (certifiedAt operational carrier kind P).decoded.obj point ≃
      (validPresheaf operational carrier kind).obj point.1 :=
  certifiedEquiv operational carrier kind ⟨point.1, PUnit.unit⟩

/-- Read the generic classifier, retaining its independently checked kind. -/
def certifiedGeneric {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort) :
    totalSpace (certifiedAt operational carrier kind P).decoded ⟶
      validPresheaf operational carrier kind where
  app world := TypeCat.ofHom fun value =>
    certifiedAtEquiv operational carrier kind P ⟨world, value.1⟩ value.2
  naturality world future arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    have natural := (certifiedRead operational carrier kind).naturality_apply
      (X := ⟨world, PUnit.unit⟩) (Y := ⟨future, PUnit.unit⟩)
      ⟨arrow, rfl⟩ value.2
    exact natural

def certifiedCodeGeneric {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort) :
    totalSpace (certifiedAt operational carrier kind P).decoded ⟶
      Carrier.presheaf operational carrier :=
  certifiedGeneric operational carrier kind ≫ validInclusion operational carrier kind

/-- An index bundle retains both its classifier and the actual classified
value. Classifier formation alone supplies no such value. -/
abbrev IndexBundle (carrier : D.Carrier) (kind : HSort) (world : Wᵒᵖ) :=
  Σ classifier : (validPresheaf operational carrier kind).obj world,
    {value : Code operational carrier world // Code.Member value classifier.val}

def IndexBundle.map {carrier : D.Carrier} {kind : HSort} {world future : Wᵒᵖ}
    (arrow : world ⟶ future) (bundle : IndexBundle operational carrier kind world) :
    IndexBundle operational carrier kind future :=
  ⟨(validPresheaf operational carrier kind).map arrow bundle.1,
    ⟨Code.map arrow bundle.2.val, Code.member_map arrow bundle.2.property⟩⟩

theorem IndexBundle.map_identity {carrier : D.Carrier} {kind : HSort} {world : Wᵒᵖ}
    (bundle : IndexBundle operational carrier kind world) :
    bundle.map operational (𝟙 world) = bundle := by
  cases bundle with
  | mk classifier value =>
      have first : (validPresheaf operational carrier kind).map (𝟙 world) classifier = classifier :=
        ConcreteCategory.congr_hom ((validPresheaf operational carrier kind).map_id world) classifier
      apply Sigma.ext first
      apply (Subtype.heq_iff_coe_eq (fun candidate =>
        Iff.of_eq (congrArg (Code.Member candidate) (congrArg Subtype.val first)))).2
      exact Code.map_id value.val

theorem IndexBundle.map_composition {carrier : D.Carrier} {kind : HSort}
    {world middle future : Wᵒᵖ} (first : world ⟶ middle) (second : middle ⟶ future)
    (bundle : IndexBundle operational carrier kind world) :
    bundle.map operational (first ≫ second) =
      (bundle.map operational first).map operational second := by
  have classifiers :
      (validPresheaf operational carrier kind).map (first ≫ second) bundle.1 =
        (validPresheaf operational carrier kind).map second
          ((validPresheaf operational carrier kind).map first bundle.1) :=
    ConcreteCategory.congr_hom ((validPresheaf operational carrier kind).map_comp first second) bundle.1
  apply Sigma.ext classifiers
  apply (Subtype.heq_iff_coe_eq (fun candidate =>
    Iff.of_eq (congrArg (Code.Member candidate) (congrArg Subtype.val classifiers)))).2
  exact Code.map_comp first second bundle.2.val

end
end Mettapedia.OSLF.NativeTypes.Semantics.Classifier.CertifiedProjection
