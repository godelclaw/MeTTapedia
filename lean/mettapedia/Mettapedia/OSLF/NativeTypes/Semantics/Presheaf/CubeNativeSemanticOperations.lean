import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticTelescopes

/-!
# Actual operations on generated code and kinding fibres

Former codes are built from ordered code arguments. Formation consumes actual
certified input values and builds the independently defined output kinding
witness at the selected slot. The operational carrier is never reinterpreted
as a sort constant or predicate-power object.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticOperations

open _root_.CategoryTheory Opposite
open CubeEnrichment
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.TypeTheory
open NativeLocalTypeFormers ContextualLocalUniverses
open Calculi.NativeDependent.Refinement
open DisplayedPresheafTransport DisplayedPresheafComprehension
open CubeNativeSemanticFamilies

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)

noncomputable section

/-- An actual natural code section is read without discarding its carrier. -/
def sectionName {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (value : (codeAt operational carrier P).decoded.sections) :
    P ⟶ CubePresheafCode.presheaf operational carrier where
  app world := TypeCat.ofHom fun argument => value.val ⟨world, argument⟩
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro argument
    exact (@value.property ⟨first, argument⟩ ⟨second, P.map arrow argument⟩ ⟨arrow, rfl⟩).symm

def pairArguments {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (code type : P ⟶ CubePresheafCode.presheaf operational carrier) :
    P ⟶ (typingScope operational carrier).1 where
  app world := TypeCat.ofHom fun value => ⟨⟨PUnit.unit, type.app world value⟩, code.app world value⟩
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    change (⟨⟨PUnit.unit, type.app second (P.map arrow value)⟩,
      code.app second (P.map arrow value)⟩ : (typingScope operational carrier).1.obj second) =
        ⟨⟨PUnit.unit, (CubePresheafCode.presheaf operational carrier).map arrow (type.app first value)⟩,
          (CubePresheafCode.presheaf operational carrier).map arrow (code.app first value)⟩
    rw [type.naturality_apply, code.naturality_apply]

abbrev typingAt {P : Wᵒᵖ ⥤ Type u} (vertex : Vertex D) (carrier : D.Carrier)
    (code type : P ⟶ CubePresheafCode.presheaf operational carrier) : NativeType P :=
  (typingMeaning operational vertex carrier).reindex (pairArguments operational carrier code type)

abbrev starBoxType (vertex : Vertex D) (carrier : D.Carrier) :
    NativeType (CubeNativeSemanticFamilies.emptyScope (W := W)).1 :=
  typingAt operational vertex carrier (sortName operational carrier .star) (sortName operational carrier .box)

def starBoxValue (vertex : Vertex D) (carrier : D.Carrier) :
    (starBoxType operational vertex carrier).decoded.sections where
  val _ := ⟨⟨.box, ⟨.sort .star, ⟨.star⟩⟩⟩, rfl⟩
  property := by
    intro first second arrow
    apply Subtype.ext
    rfl

abbrev parameterTypes (declaration : D.Former) :=
  fun position => codeMeaning operational (D.input declaration position)

abbrev parameterScope (declaration : D.Former) : Scope W (D.arity declaration) :=
  CubeNativeSemanticTelescopes.vectorScope (parameterTypes operational declaration)

def parameterName (declaration : D.Former) (position : Fin (D.arity declaration)) :
    (parameterScope operational declaration).1 ⟶
      CubePresheafCode.presheaf operational (D.input declaration position) :=
  sectionName operational (D.input declaration position)
    (CubeNativeSemanticTelescopes.lookupSection (parameterTypes operational declaration) position)

/-- Constructor code generation retains the complete ordered vector. -/
def formerName {P : Wᵒᵖ ⥤ Type u} (declaration : D.Former)
    (arguments : ∀ position, P ⟶ CubePresheafCode.presheaf operational (D.input declaration position)) :
    P ⟶ CubePresheafCode.presheaf operational (D.output declaration) where
  app world := TypeCat.ofHom fun value => .former declaration (fun position => (arguments position).app world value)
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    change CubeEnrichment.Code.former declaration
      (fun position => (arguments position).app second (P.map arrow value)) =
      CubeEnrichment.Code.former declaration (fun position =>
        (CubePresheafCode.presheaf operational (D.input declaration position)).map arrow
          ((arguments position).app first value))
    congr 1
    funext position
    exact (arguments position).naturality_apply arrow value

abbrev formerType (declaration : D.Former) :=
  codeAt operational (D.output declaration) (parameterScope operational declaration).1

abbrev formerValue (declaration : D.Former) :=
  codeSection operational (D.output declaration)
    (formerName operational declaration (parameterName operational declaration))

theorem formerValue_exact (declaration : D.Former)
    (point : (parameterScope operational declaration).1.Elements) :
    (formerValue operational declaration).val point =
      .former declaration (fun position => (parameterName operational declaration position).app point.1 point.2) := rfl

/-- The newest code variable is the actual first component of comprehension. -/
def codeVariableName (carrier : D.Carrier) :
    (codeScope operational carrier).1 ⟶ CubePresheafCode.presheaf operational carrier where
  app _ := TypeCat.ofHom fun value => value.2
  naturality _ _ _ := rfl

abbrev certifiedBody (vertex : Vertex D) (carrier : D.Carrier) (kind : HSort) :
    NativeType (codeScope operational carrier).1 :=
  typingAt operational vertex carrier (codeVariableName operational carrier) (sortName operational carrier kind)

abbrev certifiedMeaning (vertex : Vertex D) (carrier : D.Carrier) (kind : HSort) :
    NativeType (CubeNativeSemanticFamilies.emptyScope (W := W)).1 :=
  NativeLocalTypeFormers.sigma (codeMeaning operational carrier) (certifiedBody operational vertex carrier kind)

/-- The selected-kind code carrier is derived from the independent kinding
judgment, with its actual recursive former/argument code retained. -/
def validPresheaf (vertex : Vertex D) (carrier : D.Carrier) (kind : HSort) : Wᵒᵖ ⥤ Type u where
  obj world := {code : (CubePresheafCode.presheaf operational carrier).obj world //
    Nonempty (CubeEnrichment.Kinded vertex code kind)}
  map arrow := TypeCat.ofHom fun value =>
    ⟨(CubePresheafCode.presheaf operational carrier).map arrow value.val,
      value.property.map (CubePresheafCode.Kinded.map (fun carrier => (operational carrier).map arrow))⟩
  map_id world := by
    apply ConcreteCategory.hom_ext
    intro value
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((CubePresheafCode.presheaf operational carrier).map_id world) value.val
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro value
    apply Subtype.ext
    exact ConcreteCategory.congr_hom ((CubePresheafCode.presheaf operational carrier).map_comp first second) value.val

def certifiedDecodeIso (vertex : Vertex D) (carrier : D.Carrier) (kind : HSort) :
    (show DisplayedFamily.{u,u,u,u} (CubeNativeSemanticFamilies.emptyScope (W := W)).1 from
      (certifiedMeaning operational vertex carrier kind).decoded) ≅
    DisplayedPresheafSigma.sigmaDisplayed (codeMeaning operational carrier).decoded
      (certifiedBody operational vertex carrier kind).decoded :=
  eqToIso (sigmaDecode (codeMeaning operational carrier) (certifiedBody operational vertex carrier kind))

/-- Decoding the actual native Sigma retains both the code and the checked
selected-kind witness of its independently built kinding fibre. -/
def certifiedRead (vertex : Vertex D) (carrier : D.Carrier) (kind : HSort) :
    (show DisplayedFamily.{u,u,u,u} (CubeNativeSemanticFamilies.emptyScope (W := W)).1 from
      (certifiedMeaning operational vertex carrier kind).decoded) ⟶
      CategoryOfElements.π CubeNativeSemanticFamilies.emptyScope.1 ⋙
        validPresheaf operational vertex carrier kind where
  app point := TypeCat.ofHom fun value => by
    let pair := (certifiedDecodeIso operational vertex carrier kind).hom.app point value
    have formed : Nonempty (CubeEnrichment.Kinded vertex pair.1 kind) := by
      have codeEqual : pair.2.val.2.1 = pair.1 := congrArg Prod.fst pair.2.property
      have kindEqual : pair.2.val.1 = kind := CubeEnrichment.Code.sort.inj (congrArg Prod.snd pair.2.property)
      exact (congrArg₂ (fun code kind => Nonempty (CubeEnrichment.Kinded vertex code kind)) codeEqual kindEqual) ▸
        pair.2.val.2.2
    exact ⟨pair.1, formed⟩
  naturality first second arrow := by
    apply ConcreteCategory.hom_ext
    intro value
    apply Subtype.ext
    have natural := (certifiedDecodeIso operational vertex carrier kind).hom.naturality_apply arrow value
    exact congrArg Sigma.fst natural

/-- A closed-family readout acts on an actual substituted dependent section. -/
def closedReadSection {P target : Wᵒᵖ ⥤ Type u}
    (type : NativeType (CubeNativeSemanticFamilies.emptyScope (W := W)).1)
    (read : (show DisplayedFamily.{u,u,u,u} CubeNativeSemanticFamilies.emptyScope.1 from type.decoded) ⟶
      CategoryOfElements.π CubeNativeSemanticFamilies.emptyScope.1 ⋙ target)
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

abbrev formationTypes (vertex : Vertex D) (declaration : D.Former) :=
  fun position => certifiedMeaning operational vertex (D.input declaration position)
    (inputSort D vertex declaration position)

abbrev formationScope (vertex : Vertex D) (declaration : D.Former) : Scope W (D.arity declaration) :=
  CubeNativeSemanticTelescopes.vectorScope (formationTypes operational vertex declaration)

def formationParameterName (vertex : Vertex D) (declaration : D.Former)
    (position : Fin (D.arity declaration)) :
    (formationScope operational vertex declaration).1 ⟶
      validPresheaf operational vertex (D.input declaration position) (inputSort D vertex declaration position) :=
  closedReadSection _ (certifiedRead operational vertex (D.input declaration position)
    (inputSort D vertex declaration position))
    (CubeNativeSemanticTelescopes.lookupSection (formationTypes operational vertex declaration) position)

def validInclusion (vertex : Vertex D) (carrier : D.Carrier) (kind : HSort) :
    validPresheaf operational vertex carrier kind ⟶ CubePresheafCode.presheaf operational carrier where
  app _ := TypeCat.ofHom Subtype.val
  naturality _ _ _ := rfl

abbrev formationCodeNames (vertex : Vertex D) (declaration : D.Former) :=
  fun position => formationParameterName operational vertex declaration position ≫
    validInclusion operational vertex (D.input declaration position) (inputSort D vertex declaration position)

abbrev formationOutputName (vertex : Vertex D) (declaration : D.Former) :=
  formerName operational declaration (formationCodeNames operational vertex declaration)

abbrev formationType (vertex : Vertex D) (declaration : D.Former) :=
  typingAt operational vertex (D.output declaration)
    (formationOutputName operational vertex declaration)
    (sortName operational (D.output declaration) (outputSort D vertex declaration))


/-- A stable supplied kind-formation proof builds a section of the actual
independent fibre at a natural code, retaining that code as its payload. -/
def kindingValue {P : Wᵒᵖ ⥤ Type u} (vertex : Vertex D) (carrier : D.Carrier)
    (name : P ⟶ CubePresheafCode.presheaf operational carrier) (kind : HSort)
    (formed : ∀ world value, Nonempty (CubeEnrichment.Kinded vertex (name.app world value) kind)) :
    (typingAt operational vertex carrier name (sortName operational carrier kind)).decoded.sections where
  val point := ⟨⟨kind, ⟨name.app point.1 point.2, formed point.1 point.2⟩⟩, rfl⟩
  property := by
    intro first second arrow
    apply Subtype.ext
    change (⟨kind, ⟨(CubePresheafCode.presheaf operational carrier).map arrow.val
      (name.app first.1 first.2), _⟩⟩ : (CubePresheafCode.typedPresheaf operational vertex carrier).obj second.1) =
        ⟨kind, ⟨name.app second.1 second.2, _⟩⟩
    refine @Sigma.ext HSort (fun result => {code :
      (CubePresheafCode.presheaf operational carrier).obj second.1 //
        Nonempty (CubeEnrichment.Kinded vertex code result)}) _ _ rfl ?_
    apply heq_of_eq
    apply Subtype.ext
    change (CubePresheafCode.presheaf operational carrier).map arrow.val (name.app first.1 first.2) =
      name.app second.1 second.2
    exact (name.naturality_apply arrow.val first.2).symm.trans (congrArg (name.app second.1) arrow.property)

/-- Formation constructs the actual output proof from the full ordered input
proofs. Neither an arbitrary output witness nor an oracle relation is used. -/
def formationValue (vertex : Vertex D) (declaration : D.Former) :
    (formationType operational vertex declaration).decoded.sections :=
  kindingValue operational vertex (D.output declaration)
    (formationOutputName operational vertex declaration) (outputSort D vertex declaration)
    (fun world value => ⟨.former declaration _ (fun position => Classical.choice
      ((formationParameterName operational vertex declaration position).app world value).property)⟩)

end

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticOperations
