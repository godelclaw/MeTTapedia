import Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Laws
import Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.CompilerRenaming
import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.StableQuotient

open Mettapedia.OSLF.Framework

/-!
# The selected equation and directed-law center of the actual generator

The local argument/result coordinates induce the existing partial formation
interpretation. A successful joint check must cover the selected original
equations and the selected original directed laws. Their centers remain
separate, and their intersection is the joint center.

The independent contract retains unconditional-source support, distinct
context names and scoped-metadata restrictions before asking for preservation
of every typed formation judgment. Unsupported source laws keep their
diagnostics; the computed center does not certify that they are stable.

This interpretation is a partial sort algebra on generated display codes.
Full operation tables and intrinsic scoped binding models have separate
comparison theorems and are not identified with these local coordinates.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.UniversalAlgebra
open ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.SortProfiles.Derived (CubeVertex)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler
open Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence (Profile SourceEquationStable)

/-- Source metadata supported by the uniform display-law interpretation.
No premise-provider decision or satisfaction oracle is part of this data. -/
def MetadataSupported (law : Law) : Prop :=
  law.premises = [] ∧ (law.context.map Prod.fst).Nodup ∧
    ∀ bindings, law.bindings = some bindings →
      (∀ dependency ∈ bindings.dependencies, dependency.2 = []) ∧ bindings.occurrences = []

/-- The source law has a genuine shared formation context and preserves the
entire formation relation, with its source-support conditions retained. -/
def SupportedSourceStable (language : LanguageDef) (law : Law)
    (profile : Profile (signature language)) : Prop :=
  MetadataSupported law ∧ SourceEquationStable language law profile

private theorem metadata_iff (law : Law) :
    MetadataSupported law ↔ law.premises = [] ∧ (law.context.map Prod.fst).Nodup ∧
      (match law.bindings with
       | none => True
       | some bindings =>
           bindings.dependencies.all (fun dependency => dependency.2.isEmpty) = true ∧
             bindings.occurrences.isEmpty = true) := by
  cases binding : law.bindings with
  | none => simp [MetadataSupported, binding]
  | some bindings =>
      simp only [MetadataSupported, binding, Option.some.injEq, forall_eq',
        List.all_eq_true, List.isEmpty_iff]

theorem unresolved_iff_source_support (language : LanguageDef) (law : Law) :
    unresolved language law = [] ↔
      MetadataSupported law ∧
        (encode language (law.context.map Prod.fst) law.left).isSome = true ∧
        (encode language (law.context.map Prod.fst) law.right).isSome = true := by
  rw [metadata_iff]
  cases left : encode language (law.context.map Prod.fst) law.left <;>
    cases right : encode language (law.context.map Prod.fst) law.right <;>
    cases binding : law.bindings <;>
      simp [unresolved, binding, left, right, Bool.and_eq_true]

private theorem stable_has_encodings (language : LanguageDef) (law : Law)
    (profile : Profile (signature language)) (stable : SourceEquationStable language law profile) :
    (encode language (law.context.map Prod.fst) law.left).isSome = true ∧
      (encode language (law.context.map Prod.fst) law.right).isSome = true := by
  obtain ⟨_, _, left, right, encodedLeft, encodedRight, _, _⟩ := stable.1
  simp [encodedLeft, encodedRight]

theorem compiled_check_exact_supported_source (language : LanguageDef) (laws : List Law)
    (profile : Profile (signature language)) :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled? (compileLaws language laws) profile = some true ↔
      ∀ law ∈ laws, SupportedSourceStable language law profile := by
  rw [Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.compiled_stable_check_exact_source]
  constructor
  · rintro ⟨complete, stable⟩ law member
    exact ⟨((unresolved_iff_source_support language law).mp
      (complete_laws language laws complete law member)).1, stable law member⟩
  · intro source
    refine ⟨?_, fun law member => (source law member).2⟩
    apply List.flatMap_eq_nil_iff.mpr
    intro law member
    exact (unresolved_iff_source_support language law).mpr
      ⟨(source law member).1, stable_has_encodings language law profile (source law member).2⟩

/-- Stability of both original selected law streams under the same computed
local profile. The declaration positions are those of the authored source. -/
def SelectedSourceStable (generated : Generated) : Prop :=
  (∀ law ∈ selectedEquationLaws generated.snapshot.language generated.languageFragment.operational,
    SupportedSourceStable generated.snapshot.language law generated.vertex.2) ∧
  (∀ law ∈ selectedRewriteLaws generated.snapshot.language generated.languageFragment.operational,
    SupportedSourceStable generated.snapshot.language law generated.vertex.2)

def equationCenter (snapshot : Snapshot) (fragment : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment) :
    Finset (CubeVertex (selectedSnapshot snapshot fragment).language) :=
  Finset.univ.filter fun vertex => (generate snapshot fragment logic vertex).equationAdmission = some true

def directedCenter (snapshot : Snapshot) (fragment : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment) :
    Finset (CubeVertex (selectedSnapshot snapshot fragment).language) :=
  Finset.univ.filter fun vertex => (generate snapshot fragment logic vertex).rewriteAdmission = some true

/-- One finite enumeration over the actual generator's computed cube.
It consumes the same joint admission used by generated native code checking. -/
def center (snapshot : Snapshot) (fragment : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment) :
    Finset (CubeVertex (selectedSnapshot snapshot fragment).language) :=
  Finset.univ.filter fun vertex =>
    Mettapedia.OSLF.NativeTypes.SortProfiles.Source.jointAdmission (generate snapshot fragment logic vertex) = some true

/-- Unresolved vertices are enumerated separately, not discarded as unstable. -/
def unresolvedCenter (snapshot : Snapshot) (fragment : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment) :
    Finset (CubeVertex (selectedSnapshot snapshot fragment).language) :=
  Finset.univ.filter fun vertex =>
    Mettapedia.OSLF.NativeTypes.SortProfiles.Source.jointAdmission (generate snapshot fragment logic vertex) = none

def rejectedCenter (snapshot : Snapshot) (fragment : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment) :
    Finset (CubeVertex (selectedSnapshot snapshot fragment).language) :=
  Finset.univ.filter fun vertex =>
    Mettapedia.OSLF.NativeTypes.SortProfiles.Source.jointAdmission (generate snapshot fragment logic vertex) = some false

theorem mem_unresolvedCenter_iff (snapshot : Snapshot) (fragment : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot fragment).language) :
    vertex ∈ unresolvedCenter snapshot fragment logic ↔
      Mettapedia.OSLF.NativeTypes.SortProfiles.Source.jointAdmission (generate snapshot fragment logic vertex) = none := by
  simp only [unresolvedCenter, Finset.mem_filter, Finset.mem_univ, true_and]

theorem center_partition (snapshot : Snapshot) (fragment : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment) :
    center snapshot fragment logic ∪ unresolvedCenter snapshot fragment logic ∪
      rejectedCenter snapshot fragment logic = Finset.univ := by
  ext vertex
  cases status : Mettapedia.OSLF.NativeTypes.SortProfiles.Source.jointAdmission (generate snapshot fragment logic vertex) with
  | none => simp [center, unresolvedCenter, rejectedCenter, status]
  | some answer => cases answer <;> simp [center, unresolvedCenter, rejectedCenter, status]

theorem center_unresolved_disjoint (snapshot : Snapshot) (fragment : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment) :
    Disjoint (center snapshot fragment logic) (unresolvedCenter snapshot fragment logic) := by
  rw [Finset.disjoint_left]
  intro vertex accepted unfinished
  have first := (Finset.mem_filter.mp accepted).2
  have second := (mem_unresolvedCenter_iff _ _ _ _).mp unfinished
  rw [second] at first
  cases first

theorem center_intersection (snapshot : Snapshot) (fragment : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment) :
    center snapshot fragment logic =
      equationCenter snapshot fragment logic ∩ directedCenter snapshot fragment logic := by
  ext vertex
  simp only [center, equationCenter, directedCenter, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_inter, Mettapedia.OSLF.NativeTypes.SortProfiles.Source.joint_admission_exact]

theorem joint_admission_exact_source (snapshot : Snapshot) (fragment : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot fragment).language) :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Source.jointAdmission (generate snapshot fragment logic vertex) = some true ↔
      SelectedSourceStable (generate snapshot fragment logic vertex) := by
  rw [Mettapedia.OSLF.NativeTypes.SortProfiles.Source.joint_admission_exact]
  change (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled? (compileLaws _ _) vertex.2 = some true ∧
    Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled? (compileLaws _ _) vertex.2 = some true) ↔ _
  rw [compiled_check_exact_supported_source, compiled_check_exact_supported_source]
  rfl

theorem mem_center_iff (snapshot : Snapshot) (fragment : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot fragment).language) :
    vertex ∈ center snapshot fragment logic ↔
      SelectedSourceStable (generate snapshot fragment logic vertex) := by
  simp only [center, Finset.mem_filter, Finset.mem_univ, true_and, joint_admission_exact_source]

theorem selected_source_stability_original (generated : Generated) :
    SelectedSourceStable generated ↔
      (∀ equation index, (equation, index) ∈ generated.snapshot.language.equations.zipIdx →
        selected generated.languageFragment.operational.equationIndices index = true →
        generated.languageFragment.operational.equationDirections.isEmpty = false →
        SupportedSourceStable generated.snapshot.language (equationLaw equation index) generated.vertex.2) ∧
      (∀ rule index, (rule, index) ∈ generated.snapshot.language.rewrites.zipIdx →
        selected generated.languageFragment.operational.ruleIndices index = true →
        SupportedSourceStable generated.snapshot.language (rewriteLaw rule index) generated.vertex.2) := by
  constructor
  · rintro ⟨equations, rewrites⟩
    constructor
    · intro equation index original enabled direction
      apply equations (equationLaw equation index)
      apply (selected_equation_law_iff _ _ _).mpr
      exact ⟨(equation_law_origin _ _).mpr ⟨equation, index, original, rfl⟩, enabled, direction⟩
    · intro rule index original enabled
      apply rewrites (rewriteLaw rule index)
      apply (selected_rewrite_law_iff _ _ _).mpr
      exact ⟨(rewrite_law_origin _ _).mpr ⟨rule, index, original, rfl⟩, enabled⟩
  · rintro ⟨equations, rewrites⟩
    constructor
    · intro law member
      obtain ⟨original, enabled, direction⟩ := (selected_equation_law_iff _ _ _).mp member
      obtain ⟨equation, index, declared, rfl⟩ := (equation_law_origin _ _).mp original
      exact equations equation index declared enabled direction
    · intro law member
      obtain ⟨original, enabled⟩ := (selected_rewrite_law_iff _ _ _).mp member
      obtain ⟨rule, index, declared, rfl⟩ := (rewrite_law_origin _ _).mp original
      exact rewrites rule index declared enabled

theorem member_joint_admitted {snapshot : Snapshot} {fragment : LanguageFragment}
    {logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment}
    {vertex : CubeVertex (selectedSnapshot snapshot fragment).language}
    (member : vertex ∈ center snapshot fragment logic) :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Source.jointAdmission (generate snapshot fragment logic vertex) = some true := by
  exact (Finset.mem_filter.mp member).2

theorem member_selected_diagnostics {snapshot : Snapshot} {fragment : LanguageFragment}
    {logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment}
    {vertex : CubeVertex (selectedSnapshot snapshot fragment).language}
    (member : vertex ∈ center snapshot fragment logic) :
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.selectedEquations (generate snapshot fragment logic vertex)).diagnostics = [] ∧
      (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.selectedDirectedLaws (generate snapshot fragment logic vertex)).diagnostics = [] := by
  have accepted := (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.joint_admission_exact _).mp (member_joint_admitted member)
  exact ⟨((generated_equation_admission_exact _ _ _ _).mp accepted.1).1,
    ((generated_rewrite_admission_exact _ _ _ _).mp accepted.2).1⟩

theorem unsupported_selected_law_excludes_vertex
    {snapshot : Snapshot} {fragment : LanguageFragment}
    {logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment}
    {vertex : CubeVertex (selectedSnapshot snapshot fragment).language}
    {law : Law}
    (selectedLaw : law ∈ selectedEquationLaws (selectedSnapshot snapshot fragment).language fragment.operational ∨
      law ∈ selectedRewriteLaws (selectedSnapshot snapshot fragment).language fragment.operational)
    (unsupported : ¬ MetadataSupported law) : vertex ∉ center snapshot fragment logic := by
  intro member
  have source := (mem_center_iff _ _ _ _).mp member
  rcases selectedLaw with equation | directed
  · exact unsupported (source.1 law equation).1
  · exact unsupported (source.2 law directed).1

theorem member_native_equation_universe {snapshot : Snapshot} {fragment : LanguageFragment}
    {logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment}
    {vertex : CubeVertex (selectedSnapshot snapshot fragment).language}
    (member : vertex ∈ center snapshot fragment logic)
    (valuation : Nat → HSort)
    (first second : Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Code (selectedSnapshot snapshot fragment).language)
    (equivalent : Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Convertibility vertex.2 valuation
      (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.selectedEquations (generate snapshot fragment logic vertex)).system first second)
    (sort : HSort) :
    first ∈ Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Universe vertex.2 valuation sort ↔
      second ∈ Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Universe vertex.2 valuation sort :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Source.generated_native_equation_universe _ _ _ _ (member_joint_admitted member)
    valuation first second equivalent sort

theorem member_native_directed_universe {snapshot : Snapshot} {fragment : LanguageFragment}
    {logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment}
    {vertex : CubeVertex (selectedSnapshot snapshot fragment).language}
    (member : vertex ∈ center snapshot fragment logic)
    (valuation : Nat → HSort)
    (first second : Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Code (selectedSnapshot snapshot fragment).language)
    (step : Mettapedia.OSLF.NativeTypes.SortProfiles.Source.NativeLawStep vertex.2
      (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.selectedDirectedLaws (generate snapshot fragment logic vertex)).system
      valuation first second) (sort : HSort) :
    first ∈ Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Universe vertex.2 valuation sort ↔
      second ∈ Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Universe vertex.2 valuation sort :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Source.generated_native_directed_universe _ _ _ _ (member_joint_admitted member)
    valuation first second step sort

/-- Directed paths use reflexive transitive closure, without adding reverse
operational edges. Their kind readouts agree at every intermediate code. -/
theorem member_native_directed_path {snapshot : Snapshot} {fragment : LanguageFragment}
    {logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment}
    {vertex : CubeVertex (selectedSnapshot snapshot fragment).language}
    (member : vertex ∈ center snapshot fragment logic)
    (valuation : Nat → HSort)
    (first second : Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Code (selectedSnapshot snapshot fragment).language)
    (path : Relation.ReflTransGen (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.NativeLawStep vertex.2
      (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.selectedDirectedLaws (generate snapshot fragment logic vertex)).system valuation)
      first second) (sort : HSort) :
    first ∈ Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Universe vertex.2 valuation sort ↔
      second ∈ Mettapedia.OSLF.NativeTypes.SortProfiles.Source.Universe vertex.2 valuation sort := by
  induction path with
  | refl => exact Iff.rfl
  | @tail middle target _ step previous =>
      exact previous.trans (member_native_directed_universe member valuation middle target step sort)

theorem member_display_equation_readout {snapshot : Snapshot} {fragment : LanguageFragment}
    {logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment}
    {vertex : CubeVertex (selectedSnapshot snapshot fragment).language}
    (member : vertex ∈ center snapshot fragment logic) (valuation : Nat → HSort)
    (first second : Term (signature (selectedSnapshot snapshot fragment).language))
    (equivalent : Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.TypedDisplayConvertibility vertex.2
      (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.selectedEquations (generate snapshot fragment logic vertex)).system
      valuation first second) :
    Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.displaySort vertex.2 valuation first =
      Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.displaySort vertex.2 valuation second :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.displaySort_equation_invariant
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Source.generated_joint_admission_stable _ _ _ _ (member_joint_admitted member)).1
    valuation first second equivalent

theorem no_equations_equation_center (snapshot : Snapshot) (fragment : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment) (empty : snapshot.language.equations = []) :
    equationCenter snapshot fragment logic = Finset.univ := by
  ext vertex
  simp only [equationCenter, Finset.mem_filter, Finset.mem_univ, true_and]
  exact iff_true_intro (no_authored_equations_generate_every_vertex snapshot fragment logic vertex empty)

theorem no_equations_joint_center_is_directed (snapshot : Snapshot) (fragment : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment) (empty : snapshot.language.equations = []) :
    center snapshot fragment logic = directedCenter snapshot fragment logic := by
  rw [center_intersection, no_equations_equation_center snapshot fragment logic empty, Finset.univ_inter]

theorem metadata_rename (permutation : String ≃ String) (law : Law) :
    MetadataSupported (renameLawVariables permutation law) ↔ MetadataSupported law := by
  unfold MetadataSupported
  rw [renamed_context_names, List.nodup_map_iff permutation.injective]
  rfl

theorem supported_source_rename (language : LanguageDef) (permutation : String ≃ String)
    (law : Law) (profile : Profile (signature language)) :
    SupportedSourceStable language (renameLawVariables permutation law) profile ↔
      SupportedSourceStable language law profile :=
  and_congr (metadata_rename permutation law) (stable_profile_source_rename language permutation law profile)

/-- Rename the variables of the actual selected source laws and recheck them.
This action retains declaration origins, operation headers and the local cube.
It does not assert an unchanged provider implements renamed query arguments. -/
def renamedJointAdmission? (generated : Generated) (permutation : String ≃ String) : Option Bool :=
  Mettapedia.OSLF.NativeTypes.SortProfiles.Source.jointAdmission
    {generated with
      equationAdmission := Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled?
        (compileLaws generated.snapshot.language
          ((selectedEquationLaws generated.snapshot.language generated.languageFragment.operational).map
            (renameLawVariables permutation))) generated.vertex.2
      rewriteAdmission := Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.checkStableCompiled?
        (compileLaws generated.snapshot.language
          ((selectedRewriteLaws generated.snapshot.language generated.languageFragment.operational).map
            (renameLawVariables permutation))) generated.vertex.2}

theorem generated_joint_admission_rename (snapshot : Snapshot) (fragment : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment)
    (vertex : CubeVertex (selectedSnapshot snapshot fragment).language) (permutation : String ≃ String) :
    renamedJointAdmission? (generate snapshot fragment logic vertex) permutation =
      Mettapedia.OSLF.NativeTypes.SortProfiles.Source.jointAdmission (generate snapshot fragment logic vertex) := by
  unfold renamedJointAdmission?
  rw [stable_profile_check_rename, stable_profile_check_rename]
  rfl

theorem center_rename (snapshot : Snapshot) (fragment : LanguageFragment)
    (logic : Mettapedia.OSLF.NativeTypes.Structural.ConnectiveFragment) (permutation : String ≃ String) :
    (Finset.univ.filter fun vertex : CubeVertex (selectedSnapshot snapshot fragment).language =>
      renamedJointAdmission? (generate snapshot fragment logic vertex) permutation = some true) =
      center snapshot fragment logic := by
  simp only [generated_joint_admission_rename, center]

/-- The graph of the existing partial operation interpretation is exactly
the argument/result formation rule specified by a local profile. -/
theorem partial_operation_graph {S : Signature.{0}} (profile : Profile S)
    (operation : S.Operation) (arguments : Fin (S.arity operation) → HSort) (sort : HSort) :
    (Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.partialModel profile).interpret operation (fun position => some (arguments position)) =
      some sort ↔
      (∀ position, arguments position = Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.input profile operation position) ∧
        sort = Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.output profile operation := by
  by_cases admitted : ∀ position,
      arguments position = Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.input profile operation position
  · simp [Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.partialModel, admitted, eq_comm]
  · simp [Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.partialModel, admitted]

end Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter
