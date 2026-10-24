/-
# LF and curriculum-prototype profiles as PTS data

The product rules below distinguish a standard calculus from two historical
MettaKernel curriculum checkers.

* `standardLF` is the ordinary two-rule LF/λP formation profile.  The
  historical `KWCheck` curriculum route at
  `MettaKernel/kernel/kernel_signature_lf_v0.metta:106-110`: it admits
  `(type,type,type)` and `(type,kind,kind)` only.
* `mettaKernelKindResultPrototype` records the four-rule curriculum prototype
  at
  `MettaKernel/kernel/kernel_signature_lf_indexed_v0.metta:99-108`:
  `(kind,type,kind)` and `(kind,kind,kind)`.
  The `(kind,type,kind)` rule is outside the λ-cube: for those premises CoC
  uses `(kind,type,type)`.  The name therefore identifies the prototype and
  its unusual result sort rather than presenting it as a standard indexed LF.
* Both curriculum checkers implement `Type : Kind` and reject `Kind` as a top sort
  (`kernel_signature_lf_v0.metta:112-113` and
  `kernel_signature_lf_indexed_v0.metta:110-111`).

This module makes that difference an explicit point in a profile lattice.
-/

import Mettapedia.GSLT.LanguageDef.LF

namespace Mettapedia.GSLT.LanguageDef.LFProfile

open Mettapedia.GSLT.LanguageDef.LF

/-- One PTS product triple `(domain sort, codomain sort, result sort)`. -/
structure ProductRule where
  domain : Srt
  codomain : Srt
  result : Srt
  deriving DecidableEq, Repr

/-- The kernel-selectable part of the LF statics. -/
structure Profile where
  sortAxiom : Srt → Option Srt
  products : List ProductRule

def typeAxiom : Srt → Option Srt
  | .type => some .kind
  | .kind => none

def typeTypeType : ProductRule := ⟨.type, .type, .type⟩
def typeKindKind : ProductRule := ⟨.type, .kind, .kind⟩
def kindTypeKind : ProductRule := ⟨.kind, .type, .kind⟩
def kindKindKind : ProductRule := ⟨.kind, .kind, .kind⟩

/-- Standard LF/λP formation: ordinary functions and dependent products from
terms into types. -/
def standardLF : Profile where
  sortAxiom := typeAxiom
  products := [typeTypeType, typeKindKind]

/-- Exact four-rule profile of the historical MettaKernel curriculum
prototype.  Its `(Kind, Type, Kind)` rule is intentionally visible in the
name and must not be read as the standard meaning of indexed LF. -/
def mettaKernelKindResultPrototype : Profile where
  sortAxiom := typeAxiom
  products := [typeTypeType, typeKindKind, kindTypeKind, kindKindKind]

/-- Pointwise inclusion of axioms and product rules. -/
def Subsumed (first second : Profile) : Prop :=
  (∀ source target, first.sortAxiom source = some target →
    second.sortAxiom source = some target) ∧
  ∀ rule, rule ∈ first.products → rule ∈ second.products

infix:50 " ⊑ " => Subsumed

theorem Subsumed.refl (profile : Profile) : profile ⊑ profile := by
  constructor
  · intro source target haxiom
    exact haxiom
  · intro rule hrule
    exact hrule

theorem Subsumed.trans {first second third : Profile}
    (hfirst : first ⊑ second) (hsecond : second ⊑ third) :
    first ⊑ third := by
  constructor
  · intro source target haxiom
    exact hsecond.1 source target (hfirst.1 source target haxiom)
  · intro rule hrule
    exact hsecond.2 rule (hfirst.2 rule hrule)

/-- Standard LF is a subprofile of the historical four-rule prototype. -/
theorem standardLF_subsumed_mettaKernelKindResultPrototype :
    standardLF ⊑ mettaKernelKindResultPrototype := by
  constructor
  · intro source target haxiom
    exact haxiom
  · intro rule hrule
    simp [standardLF] at hrule
    rcases hrule with rfl | rfl <;> simp [mettaKernelKindResultPrototype]

/-! A small shared formation judgment makes profile monotonicity substantive. -/

/-- Nat-interned PTS formation skeleton; atoms stand for context/signature heads. -/
inductive SortExpr where
  | sort : Srt → SortExpr
  | atom : Nat → Srt → SortExpr
  | pi : SortExpr → SortExpr → SortExpr
  deriving DecidableEq, Repr

/-- Profile-parametric PTS formation. -/
inductive Forms (profile : Profile) : SortExpr → Srt → Prop where
  | sort {source target} :
      profile.sortAxiom source = some target →
      Forms profile (.sort source) target
  | atom (name : Nat) (sort : Srt) :
      Forms profile (.atom name sort) sort
  | pi {domain codomain domainSort codomainSort resultSort} :
      Forms profile domain domainSort →
      Forms profile codomain codomainSort →
      (⟨domainSort, codomainSort, resultSort⟩ : ProductRule) ∈
        profile.products →
      Forms profile (.pi domain codomain) resultSort

/-- Formation derivations transport monotonically along the profile lattice. -/
theorem Forms.mono {first second : Profile} (hprofiles : first ⊑ second)
    {expression : SortExpr} {sort : Srt}
    (hforms : Forms first expression sort) : Forms second expression sort := by
  induction hforms with
  | sort haxiom => exact .sort (hprofiles.1 _ _ haxiom)
  | atom name sort => exact .atom name sort
  | pi hdomain hcodomain hrule ihDomain ihCodomain =>
      exact .pi ihDomain ihCodomain (hprofiles.2 _ hrule)

/-- Corollary in the exact form needed by later profile-parametric judgments. -/
theorem standardLF_forms_embed {expression : SortExpr} {sort : Srt}
    (hforms : Forms standardLF expression sort) :
    Forms mettaKernelKindResultPrototype expression sort :=
  hforms.mono standardLF_subsumed_mettaKernelKindResultPrototype

def objectArrow : SortExpr :=
  .pi (.atom 0 .type) (.atom 1 .type)

/-- A product between ordinary object types belongs to both profiles. -/
theorem objectArrow_standardLF : Forms standardLF objectArrow .type := by
  exact .pi (.atom 0 .type) (.atom 1 .type) (by simp [standardLF, typeTypeType])

def typeParameterProduct : SortExpr :=
  .pi (.sort .type) (.sort .type)

/-- Positive fixture: the four-rule prototype admits
`Π (α : Type). Type` at sort `Kind`. -/
theorem typeParameterProduct_mettaKernelPrototype :
    Forms mettaKernelKindResultPrototype typeParameterProduct .kind := by
  exact .pi (.sort rfl) (.sort rfl)
    (by simp [mettaKernelKindResultPrototype, kindKindKind])

/-- Standard LF cannot form that type-operator product. -/
theorem typeParameterProduct_not_standardLF :
    ¬ Forms standardLF typeParameterProduct .kind := by
  intro hforms
  cases hforms with
  | pi hdomain hcodomain hrule =>
      cases hdomain with
      | sort hdomainSort =>
          simp [standardLF, typeAxiom] at hdomainSort
          cases hcodomain with
          | sort hcodomainSort =>
              simp [standardLF, typeAxiom] at hcodomainSort
              cases hdomainSort
              cases hcodomainSort
              simp [standardLF, typeTypeType, typeKindKind] at hrule

#print axioms standardLF_subsumed_mettaKernelKindResultPrototype
#print axioms Forms.mono
#print axioms typeParameterProduct_mettaKernelPrototype
#print axioms typeParameterProduct_not_standardLF

end Mettapedia.GSLT.LanguageDef.LFProfile
