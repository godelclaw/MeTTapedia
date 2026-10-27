import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalContextualConversion

/-!
# Constructing typed contextual endpoints

The target of a dependent application is typed at the source application's
displayed result type by the original equality rule and its validity theorem.
Product and abstraction constructors similarly derive their target typing.
Callers supply the ordinary formation and inner-equality data, never a new
preservation assumption for the completed context.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion.Contextual

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Annotated NativeNaturalVectorFamilies

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
    {operations : Operations Base Const} {profile enabled : Programs.ComputationProfiles.Selection}

section Application

variable {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}
    {domain : CTm Tower.Head Γ.length} {family : CTm Tower.Head (Γ.length + 1)} {σ τ : HOL.Ty Base}

def applicationSource (f : State operations profile ⟨Γ, context, .pi domain family, .arr σ τ⟩)
    (a : State operations profile ⟨Γ, context, domain, σ⟩) :
    State operations profile ⟨Γ, context, CTm.inst0 a.term family, τ⟩ where
  contextFormed := f.contextFormed
  term := .app f.term a.term
  typed := .appElim f.typed a.typed
  code := .app f.code a.code
  reading := .application f.reading a.reading

def applicationTarget
    (f g : State operations profile ⟨Γ, context, .pi domain family, .arr σ τ⟩)
    (a b : State operations profile ⟨Γ, context, domain, σ⟩)
    (functions : CEqual (Programs.Annotated.church profile) context f.term g.term (.pi domain family))
    (arguments : CEqual (Programs.Annotated.church profile) context a.term b.term domain) :
    State operations profile ⟨Γ, context, CTm.inst0 a.term family, τ⟩ where
  contextFormed := f.contextFormed
  term := .app g.term b.term
  typed := (CEqual.typed (Programs.Annotated.levelModel profile) (.appCong functions arguments) f.contextFormed).2
  code := .app g.code b.code
  reading := .application g.reading b.reading

def Proof.app
    {f g : State operations profile ⟨Γ, context, .pi domain family, .arr σ τ⟩}
    {a b : State operations profile ⟨Γ, context, domain, σ⟩}
    {first second : SourceCertificates.Code Γ.length}
    (functions : Proof operations profile enabled f g first)
    (arguments : Proof operations profile enabled a b second) :
    Proof operations profile enabled (applicationSource f a)
      (applicationTarget f g a b functions.sourceEqual arguments.sourceEqual)
      (StructuralConversionCode.Code.congApp g.term.erase a.term.erase first second) :=
  .application rfl rfl functions arguments

end Application

section Abstraction

variable {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length} {σ τ : HOL.Ty Base}
    {family : CTm Tower.Head (Γ.length + 1)} {u w : Tower.Head}

def abstractionSource (a : State operations profile ⟨Γ, context, .head u, .arr σ .prop⟩)
    (b : State operations profile ⟨σ :: Γ, .snoc context a.term, family, τ⟩)
    (hu : (Programs.ComputationProfiles.rules profile).isUniverse u)
    (formed : CTyped (Programs.Annotated.church profile) context (.pi a.term family) (.head w))
    (hw : (Programs.ComputationProfiles.rules profile).isUniverse w) :
    State operations profile ⟨Γ, context, .pi a.term family, .arr σ τ⟩ where
  contextFormed := a.contextFormed
  term := .lam a.term b.term
  typed := .lamIntro a.typed hu formed hw b.typed
  code := .lam b.code
  reading := .abstraction a.reading b.reading

def abstractionTarget
    (a a' : State operations profile ⟨Γ, context, .head u, .arr σ .prop⟩)
    (b b' : State operations profile ⟨σ :: Γ, .snoc context a.term, family, τ⟩)
    (hu : (Programs.ComputationProfiles.rules profile).isUniverse u)
    (formed : CTyped (Programs.Annotated.church profile) context (.pi a.term family) (.head w))
    (hw : (Programs.ComputationProfiles.rules profile).isUniverse w)
    (domains : CEqual (Programs.Annotated.church profile) context a.term a'.term (.head u))
    (bodies : CEqual (Programs.Annotated.church profile) (.snoc context a.term) b.term b'.term family) :
    State operations profile ⟨Γ, context, .pi a.term family, .arr σ τ⟩ where
  contextFormed := a.contextFormed
  term := .lam a'.term b'.term
  typed := (CEqual.typed (Programs.Annotated.levelModel profile)
    (.lamCong domains hu formed hw bodies) a.contextFormed).2
  code := .lam b'.code
  reading := .abstraction a'.reading b'.reading

def Proof.lam
    {a a' : State operations profile ⟨Γ, context, .head u, .arr σ .prop⟩}
    {b b' : State operations profile ⟨σ :: Γ, .snoc context a.term, family, τ⟩}
    {domainCode : SourceCertificates.Code Γ.length} {bodyCode : SourceCertificates.Code (Γ.length + 1)}
    (hu : (Programs.ComputationProfiles.rules profile).isUniverse u)
    (formed : CTyped (Programs.Annotated.church profile) context (.pi a.term family) (.head w))
    (hw : (Programs.ComputationProfiles.rules profile).isUniverse w)
    (domains : Proof operations profile enabled a a' domainCode)
    (bodies : Proof operations profile enabled b b' bodyCode) :
    Proof operations profile enabled (abstractionSource a b hu formed hw)
      (abstractionTarget a a' b b' hu formed hw domains.sourceEqual bodies.sourceEqual)
      (StructuralConversionCode.Code.congLam bodyCode) :=
  .abstraction hu formed hw rfl rfl domains bodies

end Abstraction

section Product

variable {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length} {σ τ : HOL.Ty Base}
    {u v w : Tower.Head}

def productSource (a : State operations profile ⟨Γ, context, .head u, .arr σ .prop⟩)
    (b : State operations profile ⟨σ :: Γ, .snoc context a.term, .head v, .arr τ .prop⟩)
    (hu : (Programs.ComputationProfiles.rules profile).isUniverse u)
    (hv : (Programs.ComputationProfiles.rules profile).isUniverse v)
    (join : (Programs.ComputationProfiles.rules profile).join u v w) :
    State operations profile ⟨Γ, context, .head w, .arr (.arr σ τ) .prop⟩ where
  contextFormed := a.contextFormed
  term := .pi a.term b.term
  typed := .piForm a.typed hu b.typed hv join
  code := HOL.PredicateProducts.pi a.code b.code
  reading := .product a.reading b.reading

def productTarget (a a' : State operations profile ⟨Γ, context, .head u, .arr σ .prop⟩)
    (b b' : State operations profile ⟨σ :: Γ, .snoc context a.term, .head v, .arr τ .prop⟩)
    (hu : (Programs.ComputationProfiles.rules profile).isUniverse u)
    (hv : (Programs.ComputationProfiles.rules profile).isUniverse v)
    (join : (Programs.ComputationProfiles.rules profile).join u v w)
    (domains : CEqual (Programs.Annotated.church profile) context a.term a'.term (.head u))
    (families : CEqual (Programs.Annotated.church profile) (.snoc context a.term) b.term b'.term (.head v)) :
    State operations profile ⟨Γ, context, .head w, .arr (.arr σ τ) .prop⟩ where
  contextFormed := a.contextFormed
  term := .pi a'.term b'.term
  typed := (CEqual.typed (Programs.Annotated.levelModel profile)
    (.piCong domains hu families hv join) a.contextFormed).2
  code := HOL.PredicateProducts.pi a'.code b'.code
  reading := .product a'.reading b'.reading

def Proof.pi
    {a a' : State operations profile ⟨Γ, context, .head u, .arr σ .prop⟩}
    {b b' : State operations profile ⟨σ :: Γ, .snoc context a.term, .head v, .arr τ .prop⟩}
    {domainCode : SourceCertificates.Code Γ.length} {familyCode : SourceCertificates.Code (Γ.length + 1)}
    (hu : (Programs.ComputationProfiles.rules profile).isUniverse u)
    (hv : (Programs.ComputationProfiles.rules profile).isUniverse v)
    (join : (Programs.ComputationProfiles.rules profile).join u v w)
    (domains : Proof operations profile enabled a a' domainCode)
    (families : Proof operations profile enabled b b' familyCode) :
    Proof operations profile enabled (productSource a b hu hv join)
      (productTarget a a' b b' hu hv join domains.sourceEqual families.sourceEqual)
      (StructuralConversionCode.Code.congPi a'.term.erase b.term.erase domainCode familyCode) :=
  .product hu hv join rfl rfl domains families

end Product

#print axioms Proof.app
#print axioms Proof.lam
#print axioms Proof.pi

end AnnotatedConversion.Contextual
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
