import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Families

/-!
# Actual operations on classifier codes and membership fibres

Membership families retain original operational values, classifier codes and
selected sort evidence. Certified codes decode through their actual dependent
Sigma family, with natural readout in every world.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Operations

open _root_.CategoryTheory Opposite
open Presheaf CubeEnrichment
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.TypeTheory
open NativeLocalTypeFormers ContextualLocalUniverses
open Calculi.NativeDependent.Refinement
open DisplayedPresheafTransport DisplayedPresheafComprehension
open Families

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)

noncomputable section

/-- An actual natural code section is read without discarding its carrier. -/
def sectionName {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (value : (codeAt operational carrier P).decoded.sections) :
    P ⟶ Carrier.presheaf operational carrier where
  app world := TypeCat.ofHom fun argument => value.val ⟨world, argument⟩
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro argument
    exact (@value.property ⟨first, argument⟩ ⟨second, P.map arrow argument⟩ ⟨arrow, rfl⟩).symm

def pairArguments {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (code type : P ⟶ Carrier.presheaf operational carrier) :
    P ⟶ (typingScope operational carrier).1 where
  app world := TypeCat.ofHom fun value => ⟨⟨PUnit.unit, type.app world value⟩, code.app world value⟩
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    change (⟨⟨PUnit.unit, type.app second (P.map arrow value)⟩,
      code.app second (P.map arrow value)⟩ : (typingScope operational carrier).1.obj second) =
        ⟨⟨PUnit.unit, (Carrier.presheaf operational carrier).map arrow (type.app first value)⟩,
          (Carrier.presheaf operational carrier).map arrow (code.app first value)⟩
    rw [type.naturality_apply, code.naturality_apply]

abbrev typingAt {P : Wᵒᵖ ⥤ Type u}  (carrier : D.Carrier)
    (code type : P ⟶ Carrier.presheaf operational carrier) : NativeType P :=
  (typingMeaning operational carrier).reindex (pairArguments operational carrier code type)

abbrev starBoxType  (carrier : D.Carrier) :
    NativeType (Families.emptyScope (W := W)).1 :=
  typingAt operational carrier (sortName operational carrier .star) (sortName operational carrier .box)

def starBoxValue  (carrier : D.Carrier) :
    (starBoxType operational carrier).decoded.sections where
  val _ := ⟨⟨(.sort .star, .sort .box), True.intro⟩, rfl⟩
  property := by
    intro first second arrow
    apply Subtype.ext
    rfl

def codeVariableName (carrier : D.Carrier) :
    (codeScope operational carrier).1 ⟶ Carrier.presheaf operational carrier where
  app _ := TypeCat.ofHom (fun value => value.2)
  naturality _ _ _ := rfl

abbrev certifiedBody (carrier : D.Carrier) (kind : HSort) :
    NativeType (codeScope operational carrier).1 :=
  typingAt operational carrier
    (codeVariableName operational carrier)
    (sortName operational carrier kind)

abbrev certifiedMeaning (carrier : D.Carrier) (kind : HSort) :
    NativeType (Families.emptyScope (W := W)).1 :=
  NativeLocalTypeFormers.sigma (codeMeaning operational carrier) (certifiedBody operational carrier kind)

def validPresheaf (carrier : D.Carrier) (kind : HSort) : Wᵒᵖ ⥤ Type u where
  obj world := {code : Code operational carrier world // Code.Member code (.sort kind)}
  map arrow := TypeCat.ofHom fun value => ⟨Code.map arrow value.val, Code.member_map arrow value.property⟩
  map_id world := by
    ext value
    exact Code.map_id value.val
  map_comp first second := by
    ext value
    exact Code.map_comp first second value.val

def certifiedDecodeIso (carrier : D.Carrier) (kind : HSort) :
    (show DisplayedFamily.{u,u,u,u} (Families.emptyScope (W := W)).1 from
      (certifiedMeaning operational carrier kind).decoded) ≅
    DisplayedPresheafSigma.sigmaDisplayed (codeMeaning operational carrier).decoded
      (certifiedBody operational carrier kind).decoded :=
  eqToIso (sigmaDecode (codeMeaning operational carrier) (certifiedBody operational carrier kind))

def certifiedRead (carrier : D.Carrier) (kind : HSort) :
    (show DisplayedFamily.{u,u,u,u} (Families.emptyScope (W := W)).1 from
      (certifiedMeaning operational carrier kind).decoded) ⟶
      CategoryOfElements.π Families.emptyScope.1 ⋙ validPresheaf operational carrier kind where
  app point := TypeCat.ofHom fun value => by
    let pair := (certifiedDecodeIso operational carrier kind).hom.app point value
    have formed : Code.Member pair.1 (.sort kind) := by
      have same : pair.2.val.val = (pair.1, .sort kind) := pair.2.property
      exact (congrArg (fun codes => Code.Member codes.1 codes.2) same) ▸ pair.2.val.property
    exact ⟨pair.1, formed⟩
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    apply Subtype.ext
    have natural := (certifiedDecodeIso operational carrier kind).hom.naturality_apply arrow value
    exact congrArg Sigma.fst natural

def validInclusion (carrier : D.Carrier) (kind : HSort) :
    validPresheaf operational carrier kind ⟶ Carrier.presheaf operational carrier where
  app _ := TypeCat.ofHom Subtype.val
  naturality _ _ _ := rfl

def closedReadSection {P target : Wᵒᵖ ⥤ Type u}
    (type : NativeType (Families.emptyScope (W := W)).1)
    (read : (show DisplayedFamily.{u,u,u,u} Families.emptyScope.1 from type.decoded) ⟶
      CategoryOfElements.π Families.emptyScope.1 ⋙ target)
    (value : (type.reindex ((NativeModel W).toEmpty P)).decoded.sections) : P ⟶ target where
  app world := TypeCat.ofHom fun argument =>
    read.app ⟨world, PUnit.unit⟩ (value.val ⟨world, argument⟩)
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro argument
    have valueNatural := @value.property ⟨first, argument⟩ ⟨second, P.map arrow argument⟩ ⟨arrow, rfl⟩
    have readNatural := read.naturality_apply (X := ⟨first, PUnit.unit⟩) (Y := ⟨second, PUnit.unit⟩)
      ⟨arrow, rfl⟩ (value.val ⟨first, argument⟩)
    change read.app ⟨second, PUnit.unit⟩ (value.val ⟨second, P.map arrow argument⟩) =
      target.map arrow (read.app ⟨first, PUnit.unit⟩ (value.val ⟨first, argument⟩))
    rw [← valueNatural]
    exact readNatural

theorem typingAt_inhabited_iff {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (value type : P ⟶ Carrier.presheaf operational carrier) (world : Wᵒᵖ) (parameter : P.obj world) :
    Nonempty ((typingAt operational carrier value type).decoded.obj ⟨world, parameter⟩) ↔
      Code.Member (value.app world parameter) (type.app world parameter) :=
  Carrier.fibre_inhabited_iff operational carrier world _ _

/-- Actual membership evidence gives a section of the independently built
membership fibre, retaining the supplied value and classifier. -/
def memberSection {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (value type : P ⟶ Carrier.presheaf operational carrier)
    (member : ∀ world parameter, Code.Member (value.app world parameter) (type.app world parameter)) :
    (typingAt operational carrier value type).decoded.sections where
  val point := ⟨⟨(value.app point.1 point.2, type.app point.1 point.2), member point.1 point.2⟩, rfl⟩
  property := by
    intro first second arrow
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact (value.naturality_apply arrow.val first.2).symm.trans
        (congrArg (value.app second.1) arrow.property)
    · exact (type.naturality_apply arrow.val first.2).symm.trans
        (congrArg (type.app second.1) arrow.property)

end
end Mettapedia.OSLF.NativeTypes.Semantics.Classifier.Operations
