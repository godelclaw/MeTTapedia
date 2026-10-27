import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalContextualConstructors
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionContextSubstitution

/-!
# Reindexing contextual annotated conversion evidence

Typed caller substitutions lift through the actual source and HOL binders.
The transported evidence retains the full original source-code substitution,
including argument order and contextual constructors. Permission widening
changes only the permissions of the base paths.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Annotated NativeNaturalVectorFamilies

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
    {operations : Operations Base Const} {profile enabled : Programs.ComputationProfiles.Selection}

def Substitution.lift {Γ Ξ : HOL.Ctx Base}
    {sourceContext : CCtx Tower.Head Γ.length} {targetContext : CCtx Tower.Head Ξ.length}
    (substitution : Substitution operations profile Γ Ξ sourceContext targetContext)
    {domain : HOL.Ty Base} {u : Tower.Head}
    (state : State operations profile ⟨Γ, sourceContext, .head u, .arr domain .prop⟩)
    (allowed : (Programs.ComputationProfiles.rules profile).isUniverse u) :
    Substitution operations profile (domain :: Γ) (domain :: Ξ)
      (.snoc sourceContext state.term) (.snoc targetContext (state.term.subst substitution.source)) where
  targetFormed := .snoc substitution.targetFormed ⟨u, allowed, state.typed.substitute substitution.typed⟩
  source := CTm.liftSub substitution.source
  target := HOL.Subst.lift substitution.target
  typed := substitution.typed.lift state.term
  represented := substitution.lifted_components

namespace Contextual.Proof

def castCode {index : Index Base} {source target : State operations profile index}
    {first second : SourceCertificates.Code index.targetContext.length} (same : first = second)
    (proof : Proof operations profile enabled source target first) :
    Proof operations profile enabled source target second := same ▸ proof

def castStates {index : Index Base} {source target source' target' : State operations profile index}
    {code : SourceCertificates.Code index.targetContext.length}
    (left : source = source') (right : target = target')
    (proof : Proof operations profile enabled source target code) :
    Proof operations profile enabled source' target' code := left ▸ right ▸ proof

def castType {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}
    {first second : CTm Tower.Head Γ.length} {carrier : HOL.Ty Base}
    {source target : State operations profile ⟨Γ, context, first, carrier⟩}
    {code : SourceCertificates.Code Γ.length} (same : first = second)
    (proof : Proof operations profile enabled source target code) :
    Proof operations profile enabled (source.castType same) (target.castType same) code := by
  cases same
  exact proof

theorem work_castCode {index : Index Base} {source target : State operations profile index}
    {first second : SourceCertificates.Code index.targetContext.length} (same : first = second)
    (proof : Proof operations profile enabled source target first) : (proof.castCode same).work = proof.work := by
  cases same
  rfl

theorem work_castStates {index : Index Base} {source target source' target' : State operations profile index}
    {code : SourceCertificates.Code index.targetContext.length} (left : source = source') (right : target = target')
    (proof : Proof operations profile enabled source target code) :
    (proof.castStates left right).work = proof.work := by
  cases left
  cases right
  rfl

theorem work_castType {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}
    {first second : CTm Tower.Head Γ.length} {carrier : HOL.Ty Base}
    {source target : State operations profile ⟨Γ, context, first, carrier⟩}
    {code : SourceCertificates.Code Γ.length} (same : first = second)
    (proof : Proof operations profile enabled source target code) : (proof.castType same).work = proof.work := by
  cases same
  rfl

variable [DecidableEq Base]

theorem hol_castCode {index : Index Base} {source target : State operations profile index}
    {first second : SourceCertificates.Code index.targetContext.length} (same : first = second)
    (proof : Proof operations profile enabled source target first) : (proof.castCode same).hol = proof.hol := by
  cases same
  rfl

theorem hol_castStates {index : Index Base} {source target source' target' : State operations profile index}
    {code : SourceCertificates.Code index.targetContext.length} (left : source = source') (right : target = target')
    (proof : Proof operations profile enabled source target code) :
    HEq (proof.castStates left right).hol proof.hol := by
  cases left
  cases right
  rfl

theorem hol_castType {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}
    {first second : CTm Tower.Head Γ.length} {carrier : HOL.Ty Base}
    {source target : State operations profile ⟨Γ, context, first, carrier⟩}
    {code : SourceCertificates.Code Γ.length} (same : first = second)
    (proof : Proof operations profile enabled source target code) : (proof.castType same).hol = proof.hol := by
  cases same
  rfl

def widen {large : Programs.ComputationProfiles.Selection}
    (included : ∀ row, enabled row = true → large row = true) :
    {index : Index Base} → {source target : State operations profile index} →
      {code : SourceCertificates.Code index.targetContext.length} →
      Proof operations profile enabled source target code → Proof operations profile large source target code
  | _, _, _, _, .base path =>
      (Proof.base ((bubbles operations profile).widen (Step.widen included) path)).castCode
        (congrArg StructuralConversionCode.Certificate.code (SourceCertificates.emit_widen included path))
  | _, _, _, _, .refl source => .refl source
  | _, _, _, _, .symm proof => .symm (proof.widen included)
  | _, _, _, _, .trans first second => .trans (first.widen included) (second.widen included)
  | _, _, _, _, @Proof.application _ _ _ _ _ _Γ _context _domain _family _σ _τ _f _g _a _b _source _target _first _second left right first second =>
      .application left right (first.widen included) (second.widen included)
  | _, _, _, _, @Proof.abstraction _ _ _ _ _ _Γ _context _σ _τ _family _u _w _a _a' _b _b' _source _target _domainCode _bodyCode hu formed hw left right domain body =>
      .abstraction hu formed hw left right (domain.widen included) (body.widen included)
  | _, _, _, _, @Proof.product _ _ _ _ _ _Γ _context _σ _τ _u _v _w _a _a' _b _b' _source _target _domainCode _familyCode hu hv join left right domain family =>
      .product hu hv join left right (domain.widen included) (family.widen included)

omit [DecidableEq Base] in
theorem work_widen {large : Programs.ComputationProfiles.Selection}
    (included : ∀ row, enabled row = true → large row = true)
    {index : Index Base} {source target : State operations profile index}
    {code : SourceCertificates.Code index.targetContext.length}
    (proof : Proof operations profile enabled source target code) : (proof.widen included).work = proof.work := by
  induction proof with
  | base path =>
      simp only [widen, work_castCode, work]
      exact BubbleElaboration.stepCount_widen (bubbles operations profile) (Step.widen included) path
  | refl source => rfl
  | symm proof ih => simpa only [widen, work] using ih
  | trans first second ihFirst ihSecond => simp only [widen, work, ihFirst, ihSecond]
  | application _ _ first second ihFirst ihSecond => simp only [widen, work, ihFirst, ihSecond]
  | abstraction _ _ _ _ _ domain body ihDomain ihBody => simp only [widen, work, ihDomain, ihBody]
  | product _ _ _ _ _ domain family ihDomain ihFamily => simp only [widen, work, ihDomain, ihFamily]

theorem hol_widen {large : Programs.ComputationProfiles.Selection}
    (included : ∀ row, enabled row = true → large row = true)
    {index : Index Base} {source target : State operations profile index}
    {code : SourceCertificates.Code index.targetContext.length}
    (proof : Proof operations profile enabled source target code) : (proof.widen included).hol = proof.hol := by
  induction proof with
  | base path => simpa only [widen, hol_castCode, hol] using elaborate_widen included path
  | refl source => rfl
  | symm proof ih => simpa only [widen, hol] using congrArg HOL.ProofSyntax.eqSymm ih
  | trans first second ihFirst ihSecond => simp only [widen, hol, ihFirst, ihSecond]
  | application _ _ first second ihFirst ihSecond => simp only [widen, hol, ihFirst, ihSecond]
  | abstraction _ _ _ _ _ domain body _ ihBody => simp only [widen, hol, ihBody]
  | product _ _ _ _ _ domain family ihDomain ihFamily => simp only [widen, hol, ihDomain, ihFamily]

#print axioms widen
#print axioms work_widen
#print axioms hol_widen

end Contextual.Proof

namespace Contextual

section CodeSubstitution

variable {n m : Nat} (substitution : CSub Tower.Head n m)

theorem code_app_substitute (function argument : CTm Tower.Head n)
    (first second : SourceCertificates.Code n) :
    StructuralConversionCode.Code.congApp (function.subst substitution).erase (argument.subst substitution).erase
      (first.substitute SourceCertificates.substituteRoot (CTm.eraseSub substitution))
      (second.substitute SourceCertificates.substituteRoot (CTm.eraseSub substitution)) =
    (StructuralConversionCode.Code.congApp function.erase argument.erase first second).substitute
      SourceCertificates.substituteRoot (CTm.eraseSub substitution) := by
  rw [StructuralConversionCode.Code.substitute_congApp]
  simp only [CTm.erase_subst]

theorem code_lam_substitute (body : SourceCertificates.Code (n + 1)) :
    StructuralConversionCode.Code.congLam
      (body.substitute SourceCertificates.substituteRoot (CTm.eraseSub (CTm.liftSub substitution))) =
    (StructuralConversionCode.Code.congLam body).substitute
      SourceCertificates.substituteRoot (CTm.eraseSub substitution) := by
  have lifted : CTm.eraseSub (CTm.liftSub substitution) = Presentation.liftSub (CTm.eraseSub substitution) :=
    funext (CTm.eraseSub_liftSub substitution)
  rw [StructuralConversionCode.Code.substitute_congLam, lifted]

theorem code_pi_substitute (domain : CTm Tower.Head n) (family : CTm Tower.Head (n + 1))
    (first : SourceCertificates.Code n) (second : SourceCertificates.Code (n + 1)) :
    StructuralConversionCode.Code.congPi (domain.subst substitution).erase
      (family.subst (CTm.liftSub substitution)).erase
      (first.substitute SourceCertificates.substituteRoot (CTm.eraseSub substitution))
      (second.substitute SourceCertificates.substituteRoot (CTm.eraseSub (CTm.liftSub substitution))) =
    (StructuralConversionCode.Code.congPi domain.erase family.erase first second).substitute
      SourceCertificates.substituteRoot (CTm.eraseSub substitution) := by
  have lifted : CTm.eraseSub (CTm.liftSub substitution) = Presentation.liftSub (CTm.eraseSub substitution) :=
    funext (CTm.eraseSub_liftSub substitution)
  rw [StructuralConversionCode.Code.substitute_congPi]
  simp only [CTm.erase_subst, lifted]

end CodeSubstitution

namespace Proof

variable [DecidableEq Base]

/-- Substitute the actual contextual proof. The result is indexed by the
existing raw-code substitution, not by a separately reconstructed code. -/
def substitute : {index : Index Base} → {source target : State operations profile index} →
    {code : SourceCertificates.Code index.targetContext.length} →
    (proof : Proof operations profile enabled source target code) →
    {Ξ : HOL.Ctx Base} → {targetContext : CCtx Tower.Head Ξ.length} →
    (substitution : Substitution operations profile index.targetContext Ξ index.sourceContext targetContext) →
    Proof operations profile enabled (substitution.state source) (substitution.state target)
      (code.substitute SourceCertificates.substituteRoot (CTm.eraseSub substitution.source))
  | _, _, _, _, .base path, _, _, substitution =>
      (Proof.base ((substitution.fibreMap _ _ _).mapConv path)).castCode
        (SourceCertificates.emit_substitute substitution path)
  | _, _, _, _, .refl source, _, _, substitution => by
      have result := Proof.refl (enabled := enabled) (substitution.state source)
      exact result.castCode (congrArg StructuralConversionCode.Code.refl
        (CTm.erase_subst substitution.source source.term))
  | _, _, _, _, .symm proof, _, _, substitution => .symm (proof.substitute substitution)
  | _, _, _, _, .trans first second, _, _, substitution =>
      .trans (first.substitute substitution) (second.substitute substitution)
  | _, _, _, _, @Proof.application _ _ _ _ _ Γ context domain family σ τ f g a b source target first second left right fp ap,
      Ξ, targetContext, substitution => by
      let same := CTm.subst_inst0 substitution.source a.term family
      have inner : Proof operations profile enabled
          ((substitution.state source).castType same) ((substitution.state target).castType same)
          (StructuralConversionCode.Code.congApp (substitution.state g).term.erase (substitution.state a).term.erase
            (first.substitute SourceCertificates.substituteRoot (CTm.eraseSub substitution.source))
            (second.substitute SourceCertificates.substituteRoot (CTm.eraseSub substitution.source))) :=
        .application (congrArg (CTm.subst substitution.source) left)
          (congrArg (CTm.subst substitution.source) right) (fp.substitute substitution) (ap.substitute substitution)
      exact (inner.castType same.symm).castCode (code_app_substitute substitution.source g.term a.term first second)
  | _, _, _, _, @Proof.abstraction _ _ _ _ _ Γ context σ τ family u w a a' b b' source target domainCode bodyCode hu formed hw left right dp bp,
      Ξ, targetContext, substitution => by
      let lifted := substitution.lift a hu
      have inner : Proof operations profile enabled (substitution.state source) (substitution.state target)
          (StructuralConversionCode.Code.congLam
            (bodyCode.substitute SourceCertificates.substituteRoot (CTm.eraseSub (CTm.liftSub substitution.source)))) :=
        .abstraction hu (formed.substitute substitution.typed) hw
          (congrArg (CTm.subst substitution.source) left) (congrArg (CTm.subst substitution.source) right)
          (dp.substitute substitution) (bp.substitute lifted)
      exact inner.castCode (code_lam_substitute substitution.source bodyCode)
  | _, _, _, _, @Proof.product _ _ _ _ _ Γ context σ τ u v w a a' b b' source target domainCode familyCode hu hv join left right dp fp,
      Ξ, targetContext, substitution => by
      let lifted := substitution.lift a hu
      have inner : Proof operations profile enabled (substitution.state source) (substitution.state target)
          (StructuralConversionCode.Code.congPi (substitution.state a').term.erase (lifted.state b).term.erase
            (domainCode.substitute SourceCertificates.substituteRoot (CTm.eraseSub substitution.source))
            (familyCode.substitute SourceCertificates.substituteRoot (CTm.eraseSub (CTm.liftSub substitution.source)))) :=
        .product hu hv join (congrArg (CTm.subst substitution.source) left)
          (congrArg (CTm.subst substitution.source) right) (dp.substitute substitution) (fp.substitute lifted)
      exact inner.castCode (code_pi_substitute substitution.source a'.term b.term domainCode familyCode)

theorem work_substitute {index : Index Base} {source target : State operations profile index}
    {code : SourceCertificates.Code index.targetContext.length}
    (proof : Proof operations profile enabled source target code)
    {Ξ : HOL.Ctx Base} {targetContext : CCtx Tower.Head Ξ.length}
    (substitution : Substitution operations profile index.targetContext Ξ index.sourceContext targetContext) :
    (proof.substitute substitution).work = proof.work := by
  induction proof generalizing Ξ with
  | base path =>
      simp only [substitute, work_castCode, work]
      exact substitution.stepCount_mapConv path
  | refl source => simp only [substitute, work_castCode, work]
  | symm proof ih => simpa only [substitute, work] using ih substitution
  | trans first second ihFirst ihSecond => simp only [substitute, work, ihFirst, ihSecond]
  | application _ _ first second ihFirst ihSecond =>
      simp only [substitute, work_castCode, work_castType, work, ihFirst, ihSecond]
  | abstraction _ _ _ _ _ domain body ihDomain ihBody =>
      simp only [substitute, work_castCode, work, ihDomain, ihBody]
  | product _ _ _ _ _ domain family ihDomain ihFamily =>
      simp only [substitute, work_castCode, work, ihDomain, ihFamily]

/-- The transported code is checked at the actual substituted endpoints. -/
theorem substituted_checked {index : Index Base} {source target : State operations profile index}
    {code : SourceCertificates.Code index.targetContext.length}
    (proof : Proof operations profile enabled source target code)
    {Ξ : HOL.Ctx Base} {targetContext : CCtx Tower.Head Ξ.length}
    (substitution : Substitution operations profile index.targetContext Ξ index.sourceContext targetContext) :
    (code.substitute SourceCertificates.substituteRoot (CTm.eraseSub substitution.source)).check
      Tower.rules.headEq (Programs.ComputationProfiles.decoder enabled).decode
      (substitution.state source).term.erase (substitution.state target).term.erase = true :=
  (proof.substitute substitution).checked

#print axioms substitute
#print axioms work_substitute
#print axioms substituted_checked

end Proof
end Contextual
end AnnotatedConversion
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
