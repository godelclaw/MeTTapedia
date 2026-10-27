import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedCertificates

/-!
# Contextual interpretation of annotated natural conversion certificates

The evidence is indexed by the existing structural code. Application,
abstraction and product congruence retain typed annotated endpoints and
their computed HOL readings. The original source equality, retained HOL
proof and source-code acceptance are constructed from the evidence.

A lambda domain is an annotation erased by the raw source syntax. Its
equality evidence remains in this typed derivation even though the raw
lambda certificate only contains the body conversion.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion.Contextual

open Mettapedia.Logic
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Annotated NativeNaturalVectorFamilies

universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
    {operations : Operations Base Const} {profile enabled : Programs.ComputationProfiles.Selection}

theorem assumptions_weaken (operations : Operations Base Const) (Γ : HOL.Ctx Base) (domain : HOL.Ty Base) :
    HOL.weakenHyps (σ := domain) (assumptions operations Γ) = assumptions operations (domain :: Γ) := by
  rw [assumptions_eq_closed operations Γ, assumptions_eq_closed operations (domain :: Γ)]
  exact AnnotatedPredicateReading.assumptions_weaken (closedAssumptions operations) Γ domain

/-- A proof-relevant interpretation of an existing source certificate.
The shape premises refer to the actual annotated endpoint terms; their
HOL-code equations are derived by reading coherence. -/
inductive Proof (operations : Operations Base Const)
    (profile enabled : Programs.ComputationProfiles.Selection) :
    {index : Index Base} → State operations profile index → State operations profile index →
      SourceCertificates.Code index.targetContext.length → Type (max u v) where
  | base {index : Index Base} {source target : State operations profile index}
      (path : (bubbles operations profile).Conv enabled source target) :
      Proof operations profile enabled source target (SourceCertificates.emit path).code
  | refl {index : Index Base} (source : State operations profile index) :
      Proof operations profile enabled source source (.refl source.term.erase)
  | symm {index : Index Base} {source target : State operations profile index}
      {code : SourceCertificates.Code index.targetContext.length} :
      Proof operations profile enabled source target code → Proof operations profile enabled target source (.symm code)
  | trans {index : Index Base} {source middle target : State operations profile index}
      {first second : SourceCertificates.Code index.targetContext.length} :
      Proof operations profile enabled source middle first → Proof operations profile enabled middle target second →
      Proof operations profile enabled source target (.trans first second)
  | application {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}
      {domain : CTm Tower.Head Γ.length} {family : CTm Tower.Head (Γ.length + 1)}
      {σ τ : HOL.Ty Base}
      {f g : State operations profile ⟨Γ, context, .pi domain family, .arr σ τ⟩}
      {a b : State operations profile ⟨Γ, context, domain, σ⟩}
      {source target : State operations profile ⟨Γ, context, CTm.inst0 a.term family, τ⟩}
      {first second : SourceCertificates.Code Γ.length}
      (left : source.term = .app f.term a.term) (right : target.term = .app g.term b.term) :
      Proof operations profile enabled f g first → Proof operations profile enabled a b second →
      Proof operations profile enabled source target
        (StructuralConversionCode.Code.congApp g.term.erase a.term.erase first second)
  | abstraction {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}
      {σ τ : HOL.Ty Base} {family : CTm Tower.Head (Γ.length + 1)} {u w : Tower.Head}
      {a a' : State operations profile ⟨Γ, context, .head u, .arr σ .prop⟩}
      {b b' : State operations profile ⟨σ :: Γ, .snoc context a.term, family, τ⟩}
      {source target : State operations profile ⟨Γ, context, .pi a.term family, .arr σ τ⟩}
      {domainCode : SourceCertificates.Code Γ.length} {bodyCode : SourceCertificates.Code (Γ.length + 1)}
      (domainUniverse : (Programs.ComputationProfiles.rules profile).isUniverse u)
      (productTyped : CTyped (Programs.Annotated.church profile) context (.pi a.term family) (.head w))
      (productUniverse : (Programs.ComputationProfiles.rules profile).isUniverse w)
      (left : source.term = .lam a.term b.term) (right : target.term = .lam a'.term b'.term) :
      Proof operations profile enabled a a' domainCode → Proof operations profile enabled b b' bodyCode →
      Proof operations profile enabled source target (StructuralConversionCode.Code.congLam bodyCode)
  | product {Γ : HOL.Ctx Base} {context : CCtx Tower.Head Γ.length}
      {σ τ : HOL.Ty Base} {u v w : Tower.Head}
      {a a' : State operations profile ⟨Γ, context, .head u, .arr σ .prop⟩}
      {b b' : State operations profile ⟨σ :: Γ, .snoc context a.term, .head v, .arr τ .prop⟩}
      {source target : State operations profile ⟨Γ, context, .head w, .arr (.arr σ τ) .prop⟩}
      {domainCode : SourceCertificates.Code Γ.length} {familyCode : SourceCertificates.Code (Γ.length + 1)}
      (domainUniverse : (Programs.ComputationProfiles.rules profile).isUniverse u)
      (familyUniverse : (Programs.ComputationProfiles.rules profile).isUniverse v)
      (join : (Programs.ComputationProfiles.rules profile).join u v w)
      (left : source.term = .pi a.term b.term) (right : target.term = .pi a'.term b'.term) :
      Proof operations profile enabled a a' domainCode → Proof operations profile enabled b b' familyCode →
      Proof operations profile enabled source target
        (StructuralConversionCode.Code.congPi a'.term.erase b.term.erase domainCode familyCode)

namespace Proof

theorem sourceEqual : {index : Index Base} → {source target : State operations profile index} →
    {code : SourceCertificates.Code index.targetContext.length} → Proof operations profile enabled source target code →
      CEqual (Programs.Annotated.church profile) index.sourceContext source.term target.term index.sourceType
  | _, _, _, _, .base path => source_equal path
  | _, _, _, _, .refl source => .refl source.typed
  | _, _, _, _, .symm proof => .symm proof.sourceEqual
  | _, _, _, _, .trans first second => .trans first.sourceEqual second.sourceEqual
  | _, _, _, _, .application left right function argument => by
      rw [left, right]
      exact .appCong function.sourceEqual argument.sourceEqual
  | _, _, _, _, .abstraction hu formed hw left right domain body => by
      rw [left, right]
      exact .lamCong domain.sourceEqual hu formed hw body.sourceEqual
  | _, _, _, _, .product hu hv join left right domain family => by
      rw [left, right]
      exact .piCong domain.sourceEqual hu family.sourceEqual hv join

variable [DecidableEq Base]

def align {index : Index Base} {source target : State operations profile index}
    {left right : HOL.Term Const index.targetContext index.targetType}
    (leftRead : AnnotatedReads operations source.term left)
    (rightRead : AnnotatedReads operations target.term right)
    (proof : HOL.ProofSyntax Const (assumptions operations index.targetContext) (.eq left right)) :
    HOL.ProofSyntax Const (assumptions operations index.targetContext) (.eq source.code target.code) :=
  HOL.ProofSyntax.castIndices rfl
    (congrArg₂ HOL.Term.eq (AnnotatedReading.term_unique leftRead source.reading)
      (AnnotatedReading.term_unique rightRead target.reading)) proof

def hol : {index : Index Base} → {source target : State operations profile index} →
    {code : SourceCertificates.Code index.targetContext.length} → Proof operations profile enabled source target code →
      HOL.ProofSyntax Const (assumptions operations index.targetContext) (.eq source.code target.code)
  | _, _, _, _, .base path => elaborate path
  | _, _, _, _, .refl source => .eqRefl source.code
  | _, _, _, _, .symm proof => .eqSymm proof.hol
  | _, _, _, _, .trans first second => .eqTrans first.hol second.hol
  | _, _, _, _, @Proof.application _ _ _ _ _ Γ context domain family σ τ f g a b source target _ _ left right first second =>
      align (by rw [left]; exact .application f.reading a.reading)
        (by rw [right]; exact .application g.reading b.reading)
        (HOL.ProofSyntax.appCongr first.hol second.hol)
  | _, _, _, _, @Proof.abstraction _ _ _ _ _ Γ context σ τ family u w a a' b b' source target _ _ _ _ _ left right _ body =>
      align (by rw [left]; exact .abstraction a.reading b.reading)
        (by rw [right]; exact .abstraction a'.reading b'.reading)
        (.eqLam (HOL.ProofSyntax.castIndices (assumptions_weaken operations Γ σ).symm rfl body.hol))
  | _, _, _, _, @Proof.product _ _ _ _ _ Γ context σ τ u v w a a' b b' source target _ _ _ _ _ left right domain family =>
      align (by rw [left]; exact .product a.reading b.reading)
        (by rw [right]; exact .product a'.reading b'.reading)
        (HOL.PredicateProducts.congruence domain.hol
          (HOL.ProofSyntax.castIndices (assumptions_weaken operations Γ σ).symm rfl family.hol))

theorem hol_free {index : Index Base} {source target : State operations profile index}
    {code : SourceCertificates.Code index.targetContext.length}
    (proof : Proof operations profile enabled source target code) : proof.hol.FunctionExtensionalityFree := by
  induction proof with
  | base path => exact elaborate_free path
  | refl source => trivial
  | symm proof ih => exact ih
  | trans first second ihFirst ihSecond => exact ⟨ihFirst, ihSecond⟩
  | application _ _ first second ihFirst ihSecond =>
      simpa only [hol, align, HOL.ProofSyntax.functionExtensionalityFree_castIndices,
        HOL.ProofSyntax.appCongr, HOL.ProofSyntax.FunctionExtensionalityFree] using And.intro ihFirst ihSecond
  | abstraction _ _ _ _ _ domain body _ ihBody =>
      simpa only [hol, align, HOL.ProofSyntax.functionExtensionalityFree_castIndices,
        HOL.ProofSyntax.FunctionExtensionalityFree] using ihBody
  | product _ _ _ _ _ domain family ihDomain ihFamily =>
      simp only [hol, align, HOL.ProofSyntax.functionExtensionalityFree_castIndices]
      apply HOL.PredicateProducts.congruence_free
      · exact ihDomain
      · simpa only [HOL.ProofSyntax.functionExtensionalityFree_castIndices] using ihFamily

end Proof

namespace Proof

theorem checkWith (selected : Programs.ComputationProfiles.Selection)
    (baseCheck : ∀ {index : Index Base} {source target : State operations profile index}
      (path : (bubbles operations profile).Conv enabled source target),
      (SourceCertificates.emit path).code.check Tower.rules.headEq
        (Programs.ComputationProfiles.decoder selected).decode source.term.erase target.term.erase = true) :
    ∀ {index : Index Base} {source target : State operations profile index}
      {code : SourceCertificates.Code index.targetContext.length},
      Proof operations profile enabled source target code →
      code.check Tower.rules.headEq (Programs.ComputationProfiles.decoder selected).decode
        source.term.erase target.term.erase = true
  | _, _, _, _, .base path => baseCheck path
  | _, _, _, _, .refl source => StructuralConversionCode.Code.check_refl _ _ source.term.erase
  | _, _, _, _, .symm proof => StructuralConversionCode.Code.check_symm _ _ (proof.checkWith selected baseCheck)
  | _, _, _, _, .trans first second =>
      StructuralConversionCode.Code.check_trans _ _ (first.checkWith selected baseCheck) (second.checkWith selected baseCheck)
  | _, _, _, _, .application left right first second => by
      rw [left, right]
      exact StructuralConversionCode.Code.check_congApp _ _ (first.checkWith selected baseCheck) (second.checkWith selected baseCheck)
  | _, _, _, _, .abstraction _ _ _ left right _ body => by
      rw [left, right]
      exact StructuralConversionCode.Code.check_congLam _ _ (body.checkWith selected baseCheck)
  | _, _, _, _, .product _ _ _ left right domain family => by
      rw [left, right]
      exact StructuralConversionCode.Code.check_congPi _ _ (domain.checkWith selected baseCheck) (family.checkWith selected baseCheck)

theorem checked {index : Index Base} {source target : State operations profile index}
    {code : SourceCertificates.Code index.targetContext.length}
    (proof : Proof operations profile enabled source target code) :
    code.check Tower.rules.headEq (Programs.ComputationProfiles.decoder enabled).decode
      source.term.erase target.term.erase = true :=
  proof.checkWith enabled SourceCertificates.emit_selected

/-- The interpreted source code is packaged with its actual decoder result. -/
def certificate {index : Index Base} {source target : State operations profile index}
    {code : SourceCertificates.Code index.targetContext.length}
    (proof : Proof operations profile enabled source target code) :
    StructuralConversionCode.Certificate Tower.rules.headEq (Programs.ComputationProfiles.decoder enabled).decode
      source.term.erase target.term.erase := ⟨code, proof.checked⟩

def work : {index : Index Base} → {source target : State operations profile index} →
    {code : SourceCertificates.Code index.targetContext.length} → Proof operations profile enabled source target code → Nat
  | _, _, _, _, .base path => BubbleElaboration.stepCount path
  | _, _, _, _, .refl _ => 0
  | _, _, _, _, .symm proof => proof.work
  | _, _, _, _, .trans first second => first.work + second.work
  | _, _, _, _, @Proof.application _ _ _ _ _ _Γ _context _domain _family _σ _τ _f _g _a _b _source _target _first _second _left _right fp ap => fp.work + ap.work
  | _, _, _, _, @Proof.abstraction _ _ _ _ _ _Γ _context _σ _τ _family _u _w _a _a' _b _b' _source _target _domainCode _bodyCode _hu _formed _hw _left _right dp bp => dp.work + bp.work
  | _, _, _, _, @Proof.product _ _ _ _ _ _Γ _context _σ _τ _u _v _w _a _a' _b _b' _source _target _domainCode _familyCode _hu _hv _join _left _right dp fp => dp.work + fp.work

/-- Erasing annotations cannot add source-step occurrences. Equality need
not hold: a changing lambda domain is absent from the raw certificate. -/
theorem erased_work_le {index : Index Base} {source target : State operations profile index}
    {code : SourceCertificates.Code index.targetContext.length}
    (proof : Proof operations profile enabled source target code) : code.stepCount ≤ proof.work := by
  induction proof with
  | base path => simp only [SourceCertificates.emit_work, work, Nat.le_refl]
  | refl source => simp only [StructuralConversionCode.Code.stepCount, work, Nat.le_refl]
  | symm proof ih => exact ih
  | trans first second ihFirst ihSecond =>
      simpa only [StructuralConversionCode.Code.stepCount, work] using Nat.add_le_add ihFirst ihSecond
  | application _ _ first second ihFirst ihSecond =>
      simp only [StructuralConversionCode.Code.congApp, StructuralConversionCode.Code.stepCount,
        StructuralConversionCode.Code.stepCount_mapContext, work]
      exact Nat.add_le_add ihFirst ihSecond
  | abstraction _ _ _ _ _ domain body _ ihBody =>
      simp only [StructuralConversionCode.Code.congLam, StructuralConversionCode.Code.stepCount_mapContext, work]
      exact ihBody.trans (Nat.le_add_left _ _)
  | product _ _ _ _ _ domain family ihDomain ihFamily =>
      simp only [StructuralConversionCode.Code.congPi, StructuralConversionCode.Code.stepCount,
        StructuralConversionCode.Code.stepCount_mapContext, work]
      exact Nat.add_le_add ihDomain ihFamily

end Proof

#print axioms Proof.sourceEqual
#print axioms Proof.hol
#print axioms Proof.hol_free
#print axioms Proof.checked
#print axioms Proof.erased_work_le

end AnnotatedConversion.Contextual
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
