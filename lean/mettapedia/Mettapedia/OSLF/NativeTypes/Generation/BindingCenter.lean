import Mettapedia.OSLF.NativeTypes.Generation.GuardedCenter
import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.BindingCodec

open Mettapedia.OSLF.Framework

/-!
# Source-derived finite binding-model admission through one generator

Carriers are derived from the authored grammar, type context and complete
metavariable dependency declarations. Lambda carriers include those declared
dependency arrows. Every retained candidate is classified, and every complete
dependency function is checked in the actual binding valuation model.

Constructor meanings are algebra data, not a satisfaction oracle. A separate
literal interpretation reads constant constructor outputs from the existing
vertex. Its model center is distinct from universe-kind formation stability
and from a cube of full operation tables. Collections and unbounded binder
sequences remain unresolved in this finite model family.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingCenter

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralPremise
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.GSLT.LanguageDef.BindingSyntax.ScopedElaboration
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.BindingCodec
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.NullaryGuards Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding
open Mettapedia.OSLF.NativeTypes.Generation

def rootCarrierShape : Pattern → TypeExpr → Bool
  | .lambda _ _, .arrow _ _ => true
  | .lambda _ _, _ => false
  | .multiLambda _ _ _, .arrow (.multiBinder _) _ => true
  | .multiLambda _ _ _, _ => false
  | .apply _ _, .base _ => true
  | .apply _ _, _ => false
  | _, _ => true

def dependencyCarriers (law : Law) : List TypeExpr :=
  match law.bindings with
  | none => []
  | some spec => spec.dependencies.filterMap fun dependency =>
      (law.context.lookup dependency.1).map fun result => dependency.2.foldr TypeExpr.arrow result

def carrierCandidates (language : LanguageDef) (law : Law) : List TypeExpr :=
  (Mettapedia.OSLF.NativeTypes.Generation.Occurrences.sourceCandidates language (lawRule law) ++ dependencyCarriers law).eraseDups.filter
    fun type => rootCarrierShape law.left type && rootCarrierShape law.right type

def checkCompiled? {language : LanguageDef} {law : Law} {type : TypeExpr}
    (compiled : CompiledLaw language law type) (constructors : Constructors language) (active : Bool) :
    Option Bool :=
  if finiteMetas : finiteMetaContext (metaArities (language := language) (lawRule law) compiled.spec) = true then
    if finiteResult : finiteType type = true then
      some (!active || check language constructors
        (metaArities (language := language) (lawRule law) compiled.spec)
        compiled.left.term compiled.right.term finiteMetas rfl finiteResult)
    else none
  else none

theorem check_compiled_exact {language : LanguageDef} {law : Law} {type : TypeExpr}
    (compiled : CompiledLaw language law type) (constructors : Constructors language) (active : Bool) :
    checkCompiled? compiled constructors active = some true ↔
      finiteMetaContext (metaArities (language := language) (lawRule law) compiled.spec) = true ∧
        finiteType type = true ∧
          (active = true → Satisfies language constructors
            (metaArities (language := language) (lawRule law) compiled.spec)
            compiled.left.term compiled.right.term) := by
  unfold checkCompiled?
  split
  · rename_i metaFinite
    split
    · rename_i resultFinite
      cases active with
      | false => simp [metaFinite, resultFinite]
      | true =>
        simp only [Bool.not_true, Bool.false_or, Option.some.injEq, resultFinite, true_and,
          forall_true_left]
        rw [Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding.check_iff language constructors _ _ _ metaFinite rfl resultFinite]
        exact ⟨fun semantic => ⟨metaFinite, semantic⟩, fun accepted => accepted.2⟩
    · rename_i notFinite
      simp [notFinite]
  · rename_i notFinite
    simp [notFinite]

def CarrierSemantics (language : LanguageDef) (constructors : Constructors language)
    (law : Law) (active : Bool) (type : TypeExpr) : Prop :=
  ∃ compiled : CompiledLaw language law type,
    compileLaw? language law type = some compiled ∧
      finiteMetaContext (metaArities (language := language) (lawRule law) compiled.spec) = true ∧
        finiteType type = true ∧
          (active = true → Satisfies language constructors
            (metaArities (language := language) (lawRule law) compiled.spec)
            compiled.left.term compiled.right.term)

def checkCarrier? (language : LanguageDef) (constructors : Constructors language)
    (law : Law) (active : Bool) (type : TypeExpr) : Option Bool := do
  let compiled ← compileLaw? language law type
  checkCompiled? compiled constructors active

theorem check_carrier_exact (language : LanguageDef) (constructors : Constructors language)
    (law : Law) (active : Bool) (type : TypeExpr) :
    checkCarrier? language constructors law active type = some true ↔
      CarrierSemantics language constructors law active type := by
  simp only [checkCarrier?, Option.bind_eq_bind, Option.bind_eq_some_iff, check_compiled_exact,
    CarrierSemantics]

def checkCarriers? (language : LanguageDef) (constructors : Constructors language)
    (law : Law) (active : Bool) : List TypeExpr → Option Bool
  | [] => some true
  | type :: types => do
      let first ← checkCarrier? language constructors law active type
      let rest ← checkCarriers? language constructors law active types
      pure (first && rest)

theorem check_carriers_exact (language : LanguageDef) (constructors : Constructors language)
    (law : Law) (active : Bool) (types : List TypeExpr) :
    checkCarriers? language constructors law active types = some true ↔
      ∀ type ∈ types, CarrierSemantics language constructors law active type := by
  induction types with
  | nil => simp [checkCarriers?]
  | cons type types ih =>
    constructor
    · intro checked
      simp only [checkCarriers?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at checked
      obtain ⟨first, firstRead, rest, restRead, result⟩ := checked
      have both : first = true ∧ rest = true := by simpa using Option.some.inj result
      rw [both.1] at firstRead
      rw [both.2] at restRead
      exact List.forall_mem_cons.mpr ⟨(check_carrier_exact _ _ _ _ _).mp firstRead, ih.mp restRead⟩
    · intro semantic
      obtain ⟨first, rest⟩ := List.forall_mem_cons.mp semantic
      rw [checkCarriers?, (check_carrier_exact _ _ _ _ _).mpr first]
      change (checkCarriers? language constructors law active types).bind _ = _
      rw [ih.mpr rest]
      rfl

def BindingSemanticStable (language : LanguageDef) (provider : ProviderSnapshot)
    (constructors : Constructors language) (law : Law) : Prop :=
  ∃ guards, GuardedBy provider 0 law.premises guards ∧ carrierCandidates language law ≠ [] ∧
    ∀ type ∈ carrierCandidates language law,
      CarrierSemantics language constructors law (enabled guards) type

def checkLaw? (language : LanguageDef) (provider : ProviderSnapshot)
    (constructors : Constructors language) (law : Law) : Option Bool := do
  let guards ← guards? provider law.premises
  if carrierCandidates language law = [] then none
  else checkCarriers? language constructors law (enabled guards) (carrierCandidates language law)

theorem check_law_exact (language : LanguageDef) (provider : ProviderSnapshot)
    (constructors : Constructors language) (law : Law) :
    checkLaw? language provider constructors law = some true ↔
      BindingSemanticStable language provider constructors law := by
  simp only [checkLaw?, Option.bind_eq_bind, Option.bind_eq_some_iff, BindingSemanticStable]
  constructor
  · rintro ⟨guards, read, admitted⟩
    split at admitted
    · cases admitted
    · rename_i nonempty
      exact ⟨guards, (guards?_exact _ _ _).mp read, nonempty,
        (check_carriers_exact _ _ _ _ _).mp admitted⟩
  · rintro ⟨guards, original, nonempty, semantic⟩
    exact ⟨guards, (guards?_exact _ _ _).mpr original, by
      rw [if_neg nonempty]; exact (check_carriers_exact _ _ _ _ _).mpr semantic⟩

def checkLaws? (language : LanguageDef) (provider : ProviderSnapshot)
    (constructors : Constructors language) : List Law → Option Bool
  | [] => some true
  | law :: laws => do
      let first ← checkLaw? language provider constructors law
      let rest ← checkLaws? language provider constructors laws
      pure (first && rest)

theorem check_laws_exact (language : LanguageDef) (provider : ProviderSnapshot)
    (constructors : Constructors language) (laws : List Law) :
    checkLaws? language provider constructors laws = some true ↔
      ∀ law ∈ laws, BindingSemanticStable language provider constructors law := by
  induction laws with
  | nil => simp [checkLaws?]
  | cons law laws ih =>
    constructor
    · intro checked
      simp only [checkLaws?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def] at checked
      obtain ⟨first, firstRead, rest, restRead, result⟩ := checked
      have both : first = true ∧ rest = true := by simpa using Option.some.inj result
      rw [both.1] at firstRead
      rw [both.2] at restRead
      exact List.forall_mem_cons.mpr ⟨(check_law_exact _ _ _ _).mp firstRead, ih.mp restRead⟩
    · intro semantic
      obtain ⟨first, rest⟩ := List.forall_mem_cons.mp semantic
      rw [checkLaws?, (check_law_exact _ _ _ _).mpr first]
      change (checkLaws? language provider constructors laws).bind _ = _
      rw [ih.mpr rest]
      rfl

def literalConstructors (language : LanguageDef)
    (profile : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Profile (signature language)) : Constructors language where
  ordinary declaration declared _ _ _ _ :=
    Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.output profile (Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.constructorOperation language declaration declared)
  collection declaration declared _ _ _ _ _ :=
    Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.output profile (Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.constructorOperation language declaration declared)

end Mettapedia.OSLF.NativeTypes.Generation.BindingCenter

namespace Mettapedia.OSLF.NativeTypes.Generation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation.BindingCenter
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding

def Generated.bindingLawAdmission? (generated : Generated) (constructors : Constructors generated.snapshot.language) :
    Option Bool :=
  checkLaws? generated.snapshot.language generated.snapshot.provider constructors
    (selectedEquationLaws generated.snapshot.language generated.languageFragment.operational)

def Generated.bindingDirectedAdmission? (generated : Generated) (constructors : Constructors generated.snapshot.language) :
    Option Bool :=
  checkLaws? generated.snapshot.language generated.snapshot.provider constructors
    (selectedRewriteLaws generated.snapshot.language generated.languageFragment.operational)

theorem generated_binding_equations_exact (generated : Generated)
    (constructors : Constructors generated.snapshot.language) :
    generated.bindingLawAdmission? constructors = some true ↔
      ∀ law ∈ selectedEquationLaws generated.snapshot.language generated.languageFragment.operational,
        BindingSemanticStable generated.snapshot.language generated.snapshot.provider constructors law :=
  check_laws_exact _ _ _ _

theorem generated_binding_directed_exact (generated : Generated)
    (constructors : Constructors generated.snapshot.language) :
    generated.bindingDirectedAdmission? constructors = some true ↔
      ∀ law ∈ selectedRewriteLaws generated.snapshot.language generated.languageFragment.operational,
        BindingSemanticStable generated.snapshot.language generated.snapshot.provider constructors law :=
  check_laws_exact _ _ _ _

def Generated.literalBindingLawAdmission? (generated : Generated) : Option Bool :=
  generated.bindingLawAdmission? (literalConstructors generated.snapshot.language generated.vertex.2)

def literalBindingCenter (snapshot : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Snapshot)
    (fragment : LanguageFragment) (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment) :
    Finset (Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex (selectedSnapshot snapshot fragment).language) :=
  Finset.univ.filter fun vertex => (generate snapshot fragment logic vertex).literalBindingLawAdmission? = some true

theorem mem_literalBindingCenter_iff
    (snapshot : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Snapshot)
    (fragment : LanguageFragment) (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : Mettapedia.OSLF.NativeTypes.SortProfiles.Derived.CubeVertex (selectedSnapshot snapshot fragment).language) :
    vertex ∈ literalBindingCenter snapshot fragment logic ↔
      ∀ law ∈ selectedEquationLaws (selectedSnapshot snapshot fragment).language fragment.operational,
        BindingSemanticStable (selectedSnapshot snapshot fragment).language
          (selectedSnapshot snapshot fragment).provider
          (literalConstructors (selectedSnapshot snapshot fragment).language vertex.2) law := by
  simp only [literalBindingCenter, Finset.mem_filter, Finset.mem_univ, true_and]
  exact generated_binding_equations_exact _ _

theorem no_equations_literal_binding_whole_cube
    (snapshot : Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.Snapshot)
    (fragment : LanguageFragment) (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (empty : (selectedSnapshot snapshot fragment).language.equations = []) :
    literalBindingCenter snapshot fragment logic = Finset.univ := by
  ext vertex
  rw [mem_literalBindingCenter_iff]
  simp [selectedEquationLaws, Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler.equationLaws, empty]

end Mettapedia.OSLF.NativeTypes.Generation
