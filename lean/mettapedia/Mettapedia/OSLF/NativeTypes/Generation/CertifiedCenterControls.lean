import Mettapedia.OSLF.NativeTypes.Generation.CertifiedModalCenter
import Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.StableControls

open Mettapedia.OSLF.Framework

/-!
# Actual selected-source controls for the joint generated center

The original F/G grammar carries both its equation and directed law. The
joint center is nonempty and proper. An equation-free variant still rejects
a directed profile, while a guarded uniform law retains unresolved vertices.
The accepted source law also transports genuinely different constructor codes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open Mettapedia.UniversalAlgebra
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.SortProfiles.Derived (CubeVertex)
open Mettapedia.OSLF.NativeTypes.SortProfiles.Source
open Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.Compiler
open ModalHypercube (HSort)

def language : LanguageDef :=
  {Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.theory with
    rewrites := [Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.directedRule]}

def snapshot : Snapshot := ⟨language, [], ⟨[], []⟩⟩
def fragment : LanguageFragment := {operational := {includeDerivedEquations := false}}
def logic := Mettapedia.OSLF.NativeTypes.Structural.heytingFragment
def chosen := selectedSnapshot snapshot fragment
def acceptedVertex : CubeVertex chosen.language := (fun _ => .star, fun _ => .star)
def rejectedVertex : CubeVertex chosen.language :=
  (fun _ => .star, Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Controls.separatedOutput chosen.language)
def accepted := generate snapshot fragment logic acceptedVertex
def rejected := generate snapshot fragment logic rejectedVertex

theorem both_original_streams_retained :
    (selectedEquationLaws accepted.snapshot.language fragment.operational).map Law.declaration = [0] ∧
      (selectedRewriteLaws accepted.snapshot.language fragment.operational).map Law.declaration = [0] := by
  decide +kernel

theorem accepted_actual_joint_check : jointAdmission accepted = some true := by decide +kernel
theorem rejected_actual_joint_check : jointAdmission rejected = some false := by decide +kernel

theorem accepted_in_center : acceptedVertex ∈ center snapshot fragment logic :=
  Finset.mem_filter.mpr ⟨Finset.mem_univ _, accepted_actual_joint_check⟩

theorem rejected_not_in_center : rejectedVertex ∉ center snapshot fragment logic := by
  intro member
  have claimed := member_joint_admitted member
  change jointAdmission rejected = some true at claimed
  rw [rejected_actual_joint_check] at claimed
  cases claimed

theorem proper_nonempty_actual_generated_center :
    (center snapshot fragment logic).Nonempty ∧ center snapshot fragment logic ≠ Finset.univ := by
  refine ⟨⟨acceptedVertex, accepted_in_center⟩, ?_⟩
  intro full
  apply rejected_not_in_center
  rw [full]
  exact Finset.mem_univ _

theorem independent_original_source_stability : SelectedSourceStable accepted :=
  (mem_center_iff snapshot fragment logic acceptedVertex).mp accepted_in_center

def directedSnapshot : Snapshot := ⟨Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.directedTheory, [], ⟨[], []⟩⟩
def directedChosen := selectedSnapshot directedSnapshot fragment
def directedRejectedVertex : CubeVertex directedChosen.language :=
  (fun _ => .star, Mettapedia.OSLF.NativeTypes.SortProfiles.Coherence.Controls.separatedOutput directedChosen.language)
def directedRejected := generate directedSnapshot fragment logic directedRejectedVertex

theorem no_equations_accepts_equation_check_but_rejects_joint_check :
    directedRejected.equationAdmission = some true ∧
      jointAdmission directedRejected = some false := by decide +kernel

theorem equation_free_joint_center_is_proper :
    equationCenter directedSnapshot fragment logic = Finset.univ ∧
      center directedSnapshot fragment logic ≠ Finset.univ := by
  refine ⟨no_equations_equation_center _ _ _ rfl, ?_⟩
  intro full
  have member : directedRejectedVertex ∈ center directedSnapshot fragment logic := by
    rw [full]
    exact Finset.mem_univ _
  have claimed := member_joint_admitted member
  change jointAdmission directedRejected = some true at claimed
  rw [no_equations_accepts_equation_check_but_rejects_joint_check.2] at claimed
  cases claimed

def guardedSnapshot : Snapshot := ⟨Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.conditionalTheory, [], ⟨[], []⟩⟩
def guardedChosen := selectedSnapshot guardedSnapshot fragment
def guardedVertex : CubeVertex guardedChosen.language := (fun _ => .star, fun _ => .star)
def guarded := generate guardedSnapshot fragment logic guardedVertex

theorem guarded_uniform_law_remains_unknown : jointAdmission guarded = none := by decide +kernel

theorem guarded_vertex_retained_as_unresolved :
    guardedVertex ∈ unresolvedCenter guardedSnapshot fragment logic :=
  (mem_unresolvedCenter_iff _ _ _ _).mpr guarded_uniform_law_remains_unknown

theorem guarded_vertex_is_not_refuted : guardedVertex ∉ rejectedCenter guardedSnapshot fragment logic := by
  intro member
  have claimed := (Finset.mem_filter.mp member).2
  change jointAdmission guarded = some false at claimed
  rw [guarded_uniform_law_remains_unknown] at claimed
  cases claimed

def firstCode : Code accepted.snapshot.language :=
  .constructor ⟨0, by decide +kernel⟩ (fun _ => .variableCode 0)
def secondCode : Code accepted.snapshot.language :=
  .constructor ⟨1, by decide +kernel⟩ (fun _ => .variableCode 0)

theorem codes_have_different_authored_heads : firstCode ≠ secondCode := by
  intro equal
  have headers := congrArg Code.display equal
  have firstOp := congrArg (fun term : Term (signature accepted.snapshot.language) =>
    match term with | .var _ => none | .op operation _ => some operation.val) headers
  change some (Key.constructor "F" 1) = some (Key.constructor "G" 1) at firstOp
  exact (by decide +kernel : some (Key.constructor "F" 1) ≠ some (Key.constructor "G" 1)) firstOp

theorem actual_selected_equation_contains_codes :
    (firstCode.display, secondCode.display) ∈ (selectedEquations accepted).system := by
  apply (compiled_equation_member _ _ _).mpr
  refine ⟨equationLaw Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.equation 0, ?_, ?_⟩
  · change _ ∈ [_]
    exact List.mem_cons_self
  · cbv
    congr 4 <;> funext index
    all_goals
      have below : index.val < 1 := index.isLt
      have zero : index.val = 0 := by omega
      simp only [zero, List.getElem_cons_zero, Code.display]

theorem actual_selected_directed_law_contains_codes :
    (firstCode.display, secondCode.display) ∈ (selectedDirectedLaws accepted).system := by
  apply (compiled_equation_member _ _ _).mpr
  refine ⟨rewriteLaw Mettapedia.OSLF.NativeTypes.SortProfiles.OperationTables.Controls.directedRule 0, ?_, ?_⟩
  · change _ ∈ [_]
    exact List.mem_cons_self
  · cbv
    congr 4 <;> funext index
    all_goals
      have below : index.val < 1 := index.isLt
      have zero : index.val = 0 := by omega
      simp only [zero, List.getElem_cons_zero, Code.display]

private theorem substitute_variables {sourceLanguage : LanguageDef} (code : Code sourceLanguage) :
    code.substitute (fun index => Code.variableCode index) = code := by
  induction code with
  | variableCode index => rfl
  | constructor index arguments ih =>
      change Code.constructor index (fun position => (arguments position).substitute
        (fun variableIndex => Code.variableCode variableIndex)) = Code.constructor index arguments
      congr 1
      funext position
      exact ih position

theorem actual_native_directed_code_step :
    NativeLawStep accepted.vertex.2 (selectedDirectedLaws accepted).system (fun _ => .star)
      firstCode secondCode := by
  have step := NativeLawStep.law (profile := accepted.vertex.2)
    firstCode secondCode actual_selected_directed_law_contains_codes
    (fun _ => HSort.star) (fun index => Code.variableCode index)
    (fun index => Kinded.variableCode index)
  simp only [substitute_variables] at step
  exact step

theorem nonidentity_code_law_preserves_generated_universe (sort : HSort) :
    firstCode ∈ Universe accepted.vertex.2 (fun _ => .star) sort ↔
      secondCode ∈ Universe accepted.vertex.2 (fun _ => .star) sort :=
  member_native_directed_universe accepted_in_center _ _ _ actual_native_directed_code_step sort

end Mettapedia.OSLF.NativeTypes.Generation.CertifiedCenter.Controls
