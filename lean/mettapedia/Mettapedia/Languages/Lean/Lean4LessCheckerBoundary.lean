import Mettapedia.GSLT.LanguageDef.SemanticEvidence
import Mettapedia.GSLT.LanguageDef.KernelCheckingClasses
import Mettapedia.Logic.EqualityRecipe

/-!
# Lean as a checker boundary: Lean4Lean/Lean4Less integration boundary

This module is a theorem-bearing integration skeleton.  It states the exact
objects and commuting laws required to turn a Lean-like kernel into a SemanticService
guest while keeping equality-policy translation separate from proof checking.
It does not claim that the external Lean4Lean or Lean4Less implementations
have already discharged these laws.

The split is deliberate:

* a native proof system retains Lean expressions as proof objects;
* a computing kernel decides its independently stated algorithmic judgment;
* soundness into ideal typing/equality is a separate, potentially incomplete map;
* exact SemanticService parity follows fibrewise, without decoding or tag erasure;
* proof irrelevance, K-like reduction, and quotients form an explicit equality
  profile package rather than becoming properties of SemanticService;
* a Lean-to-Lean-minus translation must insert explicit transports and prove
  judgment preservation;
* universe levels cross the boundary through an order embedding.

Formerly `Mettapedia.Languages.Lean.Lean4LessNIKGuest`, part of the native inference kernel (NIK) development of 2026-08-11 to 2026-10-08; renamed to its subject name on 2026-10-08.
The namespace was `Mettapedia.Languages.Lean.Lean4LessNIKGuest`; it is now `Mettapedia.Languages.Lean.Lean4LessCheckerBoundary`.
-/

namespace Mettapedia.Languages.Lean.Lean4LessCheckerBoundary

open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.SemanticEvidence

universe uExpr uDecl uLevel

/-! ## Equality profile packages -/

/-- Definitional-equality features relevant to the present Lean4Less
translation boundary. -/
inductive EqualityFeature where
  | proofIrrelevance
  | kLikeReduction
  | quotients
  deriving DecidableEq, Repr

/-- A named package of kernel equality features. -/
structure EqualityProfile where
  name : String
  enabled : Finset EqualityFeature

/-- The selected ordinary Lean profile.  This is a profile description, not
an implementation of Lean's full conversion algorithm. -/
def leanProfile : EqualityProfile where
  name := "lean"
  enabled := {.proofIrrelevance, .kLikeReduction, .quotients}

/-- The currently relevant Lean-minus target eliminates definitional proof
irrelevance and K-like reduction while retaining quotient support explicitly. -/
def leanMinusProfile : EqualityProfile where
  name := "lean-minus-pi-klr"
  enabled := {.quotients}

/-- Profile extension is feature inclusion.  It orders equality packages,
not logical strength or consistency strength. -/
def EqualityProfile.Extends (stronger weaker : EqualityProfile) : Prop :=
  weaker.enabled ⊆ stronger.enabled

theorem lean_extends_leanMinus : leanProfile.Extends leanMinusProfile := by
  intro feature member
  simp [leanMinusProfile] at member
  subst feature
  simp [leanProfile]

/-- The extension is strict: Lean-minus does not silently regain proof
irrelevance or K-like reduction. -/
theorem leanMinus_does_not_extend_lean :
    ¬ leanMinusProfile.Extends leanProfile := by
  intro hExtends
  have impossible := hExtends (by simp [leanProfile] :
    EqualityFeature.proofIrrelevance ∈ leanProfile.enabled)
  simp [leanMinusProfile] at impossible

theorem equality_profiles_are_distinct : leanProfile ≠ leanMinusProfile := by
  intro equal
  have sameFeatures := congrArg EqualityProfile.enabled equal
  have proofIrrelevanceInMinus :
      EqualityFeature.proofIrrelevance ∈ leanMinusProfile.enabled := by
    rw [← sameFeatures]
    simp [leanProfile]
  simp [leanMinusProfile] at proofIrrelevanceInMinus

/-! ## The independently stated guest judgment -/

-- The two carrier universes are intentionally independent.
set_option linter.checkUnivs false in
/-- An exact contract for a declared algorithmic profile. Its judgment is
stated before the Boolean checker. Ideal Lean typing/equality is a separate
relation: these fields must not assert an exact ideal decision procedure. -/
structure GuestKernelSpec where
  Expr : Type uExpr
  Declaration : Type uDecl
  Converts : Expr → Expr → Prop
  judges : Expr → Declaration → Prop
  decideConversion : Expr → Expr → Bool
  decideJudgment : Declaration → Expr → Bool
  conversion_correct : ∀ left right,
    decideConversion left right = true ↔ Converts left right
  judgment_correct : ∀ declaration proof,
    decideJudgment declaration proof = true ↔ judges proof declaration
  /-- Nondegeneracy: some submitted proof/declaration pair is rejected. -/
  rejects : ∃ declaration proof,
    decideJudgment declaration proof = false

namespace GuestKernelSpec

/-- Lean terms are the guest's native proof objects; declarations are claims. -/
def proofSystem (spec : GuestKernelSpec) :
    NativeProofSystem spec.Declaration where
  ProofObject := spec.Expr
  Judges := spec.judges

/-- The kernel recomputes the native judgment directly. -/
def nativeKernel (spec : GuestKernelSpec) :
    NativeProofKernel spec.proofSystem where
  decide := spec.decideJudgment
  correct := spec.judgment_correct

/-- Conversion is exposed as a computing sub-judgment, not as certificate
content. -/
def decidedConversion (spec : GuestKernelSpec) :
    DecidedRelation spec.Expr spec.Converts where
  decide := spec.decideConversion
  correct := spec.conversion_correct

/-- A computing Lean guest obtains exact proof-fibre parity automatically:
the primary certificate is the native proof term itself. -/
def exactParity (spec : GuestKernelSpec) :
    CertificateEquivalence spec.nativeKernel.toChecker spec.proofSystem :=
  spec.nativeKernel.certificateEquivalence

/-- The resulting SemanticService checker is exact for inhabitation of the native Lean
proof fibre. -/
theorem authority (spec : GuestKernelSpec) :
    spec.nativeKernel.toChecker.Authority
      (fun declaration => Nonempty (spec.proofSystem.ProofFibre declaration)) :=
  spec.nativeKernel.authority

/-- Exact parity retains proof identity; no decode-only weakening is used. -/
def accepted_fibre_equiv_native_fibre (spec : GuestKernelSpec)
    (declaration : spec.Declaration) :
    AcceptedCertificateFibre spec.nativeKernel.toChecker declaration ≃
      spec.proofSystem.ProofFibre declaration :=
  (spec.exactParity).fibreEquiv declaration

end GuestKernelSpec

/-! ## Algorithmic acceptance and ideal judgments -/

/-- A sound interpretation of an algorithmic profile in ideal judgments.
Neither certificate completeness nor exact ideal conversion is assumed. -/
structure IdealBoundary (spec : GuestKernelSpec) where
  converts : spec.Expr → spec.Expr → Prop
  judges : spec.Expr → spec.Declaration → Prop
  conversionSymm : ∀ {left right}, converts left right → converts right left
  conversionTrans : ∀ {left middle right}, converts left middle → converts middle right → converts left right
  conversionSound : ∀ {left right}, spec.Converts left right → converts left right
  judgmentSound : ∀ {proof declaration}, spec.judges proof declaration → judges proof declaration

namespace GuestKernelSpec

def conversionChecker (spec : GuestKernelSpec) : Checker (spec.Expr × spec.Expr) Unit where
  check pair _ := spec.decideConversion pair.1 pair.2

theorem conversionAuthority (spec : GuestKernelSpec) :
    spec.conversionChecker.Authority (fun pair => spec.Converts pair.1 pair.2) where
  sound _ _ accepted := (spec.conversion_correct _ _).mp accepted
  complete _ valid := ⟨(), (spec.conversion_correct _ _).mpr valid⟩

end GuestKernelSpec

namespace IdealBoundary

variable {spec : GuestKernelSpec} (boundary : IdealBoundary spec)

/-- Exact algorithmic authority projects soundly into the ideal judgment.
The projection records its exact source scope rather than laundering a
sound implementation into a complete ideal checker. -/
theorem conversionProjection :
    spec.conversionChecker.AuthorityProjection
      (fun pair => spec.Converts pair.1 pair.2)
      (fun pair => boundary.converts pair.1 pair.2) where
  authority := spec.conversionAuthority
  project _ := boundary.conversionSound

theorem judgmentProjection :
    spec.nativeKernel.toChecker.AuthorityProjection
      (fun declaration => Nonempty (spec.proofSystem.ProofFibre declaration))
      (fun declaration => ∃ proof, boundary.judges proof declaration) where
  authority := spec.authority
  project _ proved := by
    obtain ⟨proof⟩ := proved
    exact ⟨proof.1, boundary.judgmentSound proof.2⟩

/-- An actual nontransitivity witness separates algorithmic comparison
from any sound equivalence interpretation. No such witness for the complete
Lean implementation is asserted by this abstract theorem. -/
theorem nontransitivity_gap (left middle right : spec.Expr)
    (first : spec.Converts left middle) (second : spec.Converts middle right)
    (refused : ¬ spec.Converts left right) :
    boundary.converts left right ∧ ¬ spec.conversionChecker.Authority
      (fun pair => boundary.converts pair.1 pair.2) := by
  have ideal := boundary.conversionTrans
    (boundary.conversionSound first) (boundary.conversionSound second)
  exact ⟨ideal, boundary.conversionProjection.not_target_authority_of_gap
    (claim := (left, right)) ideal refused⟩

/-- A budgeted family which enumerates exactly the original algorithm's
successes cannot fill an ideal gap. More fuel changes run length, not the
equality policy of that algorithm. -/
theorem fuel_does_not_fill_gap
    (budgeted : Nat → spec.Expr → spec.Expr → Bool)
    (sameSuccesses : ∀ left right,
      (∃ fuel, budgeted fuel left right = true) ↔ spec.Converts left right)
    (left right : spec.Expr) (ideal : boundary.converts left right)
    (refused : ¬ spec.Converts left right) :
    boundary.converts left right ∧ ∀ fuel, budgeted fuel left right = false := by
  refine ⟨ideal, fun fuel => ?_⟩
  cases accepted : budgeted fuel left right with
  | false => rfl
  | true => exact False.elim (refused ((sameSuccesses left right).mp ⟨fuel, accepted⟩))

/-- Ideal equality is reflexive on formed expressions, not necessarily on
arbitrary raw syntax. The native fibre retains that formation obligation.
No decoder from unvalidated raw expressions into this fibre is supplied. -/
def ScopedExpr := { expression : spec.Expr // boundary.converts expression expression }

def scopedConverts (left right : boundary.ScopedExpr) : Prop :=
  spec.Converts left.1 right.1

def scopedConversionChecker : Checker (boundary.ScopedExpr × boundary.ScopedExpr) Unit where
  check pair _ := spec.decideConversion pair.1.1 pair.2.1

theorem scopedConversionAuthority : boundary.scopedConversionChecker.Authority
    (fun pair => boundary.scopedConverts pair.1 pair.2) where
  sound _ _ accepted := (spec.conversion_correct _ _).mp accepted
  complete _ valid := ⟨(), (spec.conversion_correct _ _).mpr valid⟩

theorem scopedEquivalence : Equivalence
    (fun left right : boundary.ScopedExpr => boundary.converts left.1 right.1) :=
  ⟨fun expression => expression.2, fun related => boundary.conversionSymm related,
    fun first second => boundary.conversionTrans first second⟩

variable [DecidableEq spec.Expr]

instance : DecidableEq boundary.ScopedExpr := inferInstanceAs (DecidableEq (Subtype _))

/-- Explicit composition is exact for the generated relation. Equating this
with full ideal Lean equality would require a separate generation theorem. -/
theorem recipeProjection :
    (Mettapedia.Logic.EqualityRecipe.checker boundary.scopedConversionChecker).AuthorityProjection
      (fun pair => Relation.EqvGen boundary.scopedConverts pair.1 pair.2)
      (fun pair => boundary.converts pair.1.1 pair.2.1) where
  authority := Mettapedia.Logic.EqualityRecipe.authority _ boundary.scopedConversionAuthority
  project pair generated := by
    have mapped := Relation.EqvGen.mono
      (fun _ _ related => boundary.conversionSound related) _ _ generated
    exact boundary.scopedEquivalence.eqvGen_iff.mp mapped

/-- This is the missing completeness obligation, not an instance of it.
It is equivalent to actual certificate completeness for ideal conversion. -/
theorem recipe_complete_iff_generation :
    (Mettapedia.Logic.EqualityRecipe.checker boundary.scopedConversionChecker).CertificateComplete
      (fun pair => boundary.converts pair.1.1 pair.2.1) ↔
    ∀ left right : boundary.ScopedExpr, boundary.converts left.1 right.1 →
      Relation.EqvGen boundary.scopedConverts left right := by
  constructor
  · intro complete left right ideal
    obtain ⟨proof, accepted⟩ := complete (left, right) ideal
    exact boundary.recipeProjection.authority.sound _ proof accepted
  · intro generated pair ideal
    exact boundary.recipeProjection.authority.complete pair (generated _ _ ideal)

end IdealBoundary

/-! ## Profile translation and explicit casts -/

/-- A typed translation between two equality profiles over the same
declaration language.  `translate` may insert explicit transports; the
preservation theorem is the actual adequacy obligation. -/
structure ProfileTranslation
    (source target : EqualityProfile)
    (sourceKernel targetKernel : GuestKernelSpec) where
  translate : sourceKernel.Expr → targetKernel.Expr
  declarationMap : sourceKernel.Declaration → targetKernel.Declaration
  preservesJudgment : ∀ {proof declaration},
    sourceKernel.judges proof declaration →
      targetKernel.judges (translate proof) (declarationMap declaration)
  sourceExtendsTarget : source.Extends target

namespace ProfileTranslation

/-- A verified profile translation maps every accepted native proof to an
accepted target proof, with target conversion recomputed by the target
kernel. -/
theorem mapsAccepted
    {source target : EqualityProfile}
    {sourceKernel targetKernel : GuestKernelSpec}
    (translation : ProfileTranslation source target sourceKernel targetKernel)
    {declaration : sourceKernel.Declaration}
    (proof : sourceKernel.proofSystem.ProofFibre declaration) :
    targetKernel.judges (translation.translate proof.1)
      (translation.declarationMap declaration) :=
  translation.preservesJudgment proof.2

end ProfileTranslation

/-- Exact shape of the external Lean4Less obligation: ordinary Lean terms are
translated into the weaker PI/KLR-eliminated profile, and every native
judgment is preserved by explicit transports. -/
abbrev LeanToLeanMinusTranslation
    (leanKernel leanMinusKernel : GuestKernelSpec) :=
  ProfileTranslation leanProfile leanMinusProfile leanKernel leanMinusKernel

/-! ## Universe transport -/

/-- Universe levels cross an authority/profile boundary through an order
embedding.  Monotonicity alone would permit distinct levels to collapse; the
reflection law rules that out. -/
structure UniverseEmbedding
    (sourceLevel targetLevel : Type uLevel)
    [Preorder sourceLevel] [Preorder targetLevel] where
  map : sourceLevel → targetLevel
  preserves : ∀ {lower upper}, lower ≤ upper → map lower ≤ map upper
  reflects : ∀ {lower upper}, map lower ≤ map upper → lower ≤ upper

namespace UniverseEmbedding

theorem injective
    {sourceLevel targetLevel : Type uLevel}
    [PartialOrder sourceLevel] [PartialOrder targetLevel]
    (embedding : UniverseEmbedding sourceLevel targetLevel) :
    Function.Injective embedding.map := by
  intro left right equal
  apply le_antisymm
  · exact embedding.reflects (by rw [equal])
  · exact embedding.reflects (by rw [equal])

/-- Identity is a non-collapsing universe map and supplies the initial
statement shape when source and target share Lean's level algebra. -/
def identity (Level : Type uLevel) [Preorder Level] :
    UniverseEmbedding Level Level where
  map := _root_.id
  preserves := fun related => related
  reflects := fun related => related

end UniverseEmbedding

/-! ## Complete bounded integration package -/

/-- Everything needed for a Lean-as-guest integration claim.  The structure
is intentionally uninhabited here: a real instance must import or re-present
the external kernel, prove its Boolean correctness, supply the PI/KLR
translation, and map universes without collapse. -/
structure LeanAsGuestPackage where
  leanKernel : GuestKernelSpec
  leanMinusKernel : GuestKernelSpec
  translation : LeanToLeanMinusTranslation leanKernel leanMinusKernel
  /-- Lean4Less translates between two equality policies over the same
  expression and declaration syntax.  These equalities prevent the
  nontriviality witness below from being discharged merely because the two
  carriers happened to have different types. -/
  expressionCarrier : leanMinusKernel.Expr = leanKernel.Expr
  declarationCarrier : leanMinusKernel.Declaration = leanKernel.Declaration
  Level : Type uLevel
  levelOrder : PartialOrder Level
  universes : @UniverseEmbedding Level Level levelOrder.toPreorder
    levelOrder.toPreorder
  /-- The profile translation has a real source term whose representation
  changes; this blocks an identity-translation masquerade. -/
  translationNontrivial : ∃ proof,
    cast expressionCarrier (translation.translate proof) ≠ proof

/-- A completed package immediately supplies both exact SemanticService parity squares. -/
theorem package_has_exact_parity (package : LeanAsGuestPackage) :
    Nonempty
        (CertificateEquivalence package.leanKernel.nativeKernel.toChecker
          package.leanKernel.proofSystem) ∧
      Nonempty
        (CertificateEquivalence package.leanMinusKernel.nativeKernel.toChecker
          package.leanMinusKernel.proofSystem) :=
  ⟨⟨package.leanKernel.exactParity⟩,
    ⟨package.leanMinusKernel.exactParity⟩⟩

/-- Equality-profile difference is orthogonal to SemanticService proof-fibre parity: the
two exact guest kernels may coexist without changing the SemanticService waist. -/
theorem profile_change_does_not_change_parity_standard
    (package : LeanAsGuestPackage) :
    leanProfile ≠ leanMinusProfile ∧
      Nonempty
        (CertificateEquivalence package.leanKernel.nativeKernel.toChecker
          package.leanKernel.proofSystem) ∧
      Nonempty
        (CertificateEquivalence package.leanMinusKernel.nativeKernel.toChecker
          package.leanMinusKernel.proofSystem) :=
  ⟨equality_profiles_are_distinct,
    (package_has_exact_parity package).1,
    (package_has_exact_parity package).2⟩

end Mettapedia.Languages.Lean.Lean4LessCheckerBoundary
