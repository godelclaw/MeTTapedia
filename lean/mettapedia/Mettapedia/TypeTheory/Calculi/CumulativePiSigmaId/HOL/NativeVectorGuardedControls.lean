import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorGuardedElimination
import Mettapedia.Logic.HOL.Syntax.DecidableEq
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorEncodedConstructorControls

/-!
# Original Vec contexts with the constructed family guard

The operations are the previously checked encoded constructor and selected
projections. Both source contexts and the declared eliminator type are read
using the new guard. The earlier computation-only table lacks this family
entry and cannot read those dependent contexts.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows.GuardedFamily.Controls
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
local infixr:60 " ⇒ " => HOL.Ty.arr

deriving instance DecidableEq for EncodedConstructor.Controls.Const

def operations := EncodedConstructor.Controls.generated
abbrev Const := EncodedConstructor.Controls.Const
abbrev BaseSort := EncodedConstructor.Controls.BaseSort
def profile := EncodedConstructor.Controls.profile

def readContext (row : Row) :=
  AnnotatedPredicateReading.Reader.admitContext? (Programs.Annotated.church profile) (lexical operations)
    (Programs.Annotated.JudgmentReplay.decoder profile) (row.parameters operations)
    (EncodedConstructor.Controls.sourceContext row) (EncodedConstructor.Controls.contextCertificate row)

theorem nil_context_admitted : (readContext .nil).isSome = true := by decide +kernel
theorem cons_context_admitted : (readContext .cons).isSome = true := by decide +kernel

theorem actual_guard_counts :
    (readContext .nil).map (fun result => result.code.hypotheses.length) = some 4 ∧
    (readContext .cons).map (fun result => result.code.hypotheses.length) = some 7 := by decide +kernel

def sourceEliminatorType : CTm Tower.Head 0 :=
  liftTm (RussellTarski.substLevelsTm Programs.levels vecEliminateType)
def typeReading := AnnotatedPredicateReading.Reader.infer? (lexical operations) [] sourceEliminatorType

theorem declared_eliminator_type_read : typeReading.map Sigma.fst = some (operations.eliminatorType ⇒ .prop) := by
  decide +kernel

theorem old_context_table_refused :
    (AnnotatedPredicateReading.Reader.readContext? operations.lexicalReading (Row.nil.parameters operations)
      (EncodedConstructor.Controls.sourceContext .nil)).isNone = true := by decide +kernel

def exchangedParameters : HOL.Ctx BaseSort :=
  [operations.vector, operations.number, operations.element, operations.method,
    operations.result, operations.motive, operations.elementPredicate]

theorem exchanged_parameter_carriers_refused :
    (AnnotatedPredicateReading.Reader.readContext? (lexical operations) exchangedParameters
      (EncodedConstructor.Controls.sourceContext .cons)).isNone = true := by decide +kernel

theorem original_nil_reading_preserved : AnnotatedPredicateReading.Reader.infer? (lexical operations)
    (Row.nil.parameters operations) (liftTm (Row.nil.rawLeft operations)) =
      some ⟨operations.result, Row.nil.leftCode operations⟩ :=
  AnnotatedPredicateReading.Reader.infer?_complete (original_rows_read operations .nil).1

theorem original_cons_reading_preserved : AnnotatedPredicateReading.Reader.infer? (lexical operations)
    (Row.cons.parameters operations) (liftTm (Row.cons.rawRight operations)) =
      some ⟨operations.result, Row.cons.rightCode operations⟩ :=
  AnnotatedPredicateReading.Reader.infer?_complete (original_rows_read operations .cons).2

def nilMembership := (algebra operations).nil_member (Γ := [operations.elementPredicate]) (Δ := []) (.var .vz)
theorem nil_membership_free : nilMembership.FunctionExtensionalityFree := (algebra operations).nil_member_free _

abbrev fields : HOL.Ctx BaseSort :=
  [operations.vector, operations.element, operations.number, operations.elementPredicate]
def A : HOL.Term Const fields operations.elementPredicate := .var (.vs (.vs (.vs .vz)))
def n : HOL.Term Const fields operations.number := .var (.vs (.vs .vz))
def h : HOL.Term Const fields operations.element := .var (.vs .vz)
def t : HOL.Term Const fields operations.vector := .var .vz
def premises : List (HOL.Formula Const fields) := [.app A h, (algebra operations).member A n t]

def consMembership : HOL.ProofSyntax Const premises
    ((algebra operations).member A (.app (HOL.weakenCtx fields operations.successor) n)
      ((algebra operations).consValue n h t)) :=
  (algebra operations).cons_member A n h t
    (.hyp (Δ := premises) ⟨0, by simp [premises]⟩)
    (.hyp (Δ := premises) ⟨1, by simp [premises]⟩)

theorem cons_membership_free : consMembership.FunctionExtensionalityFree := by
  unfold consMembership
  exact (algebra operations).cons_member_free _ _ _ _ _ _ True.intro True.intro

def familyReadback := family_apply (Δ := premises) operations A n t
theorem family_readback_free : familyReadback.FunctionExtensionalityFree := family_apply_free operations A n t

def sourceNilMembership := nil_member (Γ := [operations.elementPredicate]) (Δ := []) operations (.var .vz)
theorem source_nil_membership_free : sourceNilMembership.FunctionExtensionalityFree := nil_member_free operations _

def sourcePremises : List (HOL.Formula Const fields) := [.app A h, membership operations A n t]
def sourceConsMembership := cons_member (Δ := sourcePremises) operations A n h t
  (.hyp (Δ := sourcePremises) ⟨0, by simp [sourcePremises]⟩)
  (.hyp (Δ := sourcePremises) ⟨1, by simp [sourcePremises]⟩)

theorem source_cons_membership_free : sourceConsMembership.FunctionExtensionalityFree := by
  unfold sourceConsMembership
  exact cons_member_free operations _ _ _ _ _ _ True.intro True.intro

abbrev parameters := Row.nil.parameters operations

def parameterA : HOL.Term Const parameters operations.elementPredicate := .var (.vs (.vs (.vs .vz)))
def parameterP : HOL.Term Const parameters operations.motive := .var (.vs (.vs .vz))
def parameterZ : HOL.Term Const parameters operations.result := .var (.vs .vz)
def parameterS : HOL.Term Const parameters operations.method := .var .vz

def originalGuards : List (HOL.Formula Const parameters) :=
  ((readContext .nil).get (by decide +kernel)).code.hypotheses

theorem original_method_guard : originalGuards[0]? =
    some (.app (methodPredicate operations parameterA parameterP) parameterS) := by decide +kernel

theorem original_base_guard : originalGuards[1]? =
    some (.app (basePredicate operations parameterA parameterP) parameterZ) := by decide +kernel

theorem original_result_reading : AnnotatedPredicateReading.Reader.infer? (lexical operations) parameters
    (liftTm (RussellTarski.substLevelsTm Programs.levels vecEliminateResultType)) =
      some ⟨_, resultPredicate operations parameterA parameterP⟩ := by decide +kernel

def typingAssumptions :=
  EncodedConstructor.assumptions EncodedConstructor.Controls.raw EncodedConstructor.Controls.interface parameters ++ originalGuards

def typingRoots : RootEvidence operations parameters typingAssumptions := fun occurrence =>
  (encodedRoots EncodedConstructor.Controls.raw EncodedConstructor.Controls.interface parameters occurrence).mono
    (HOL.ProofSyntax.OccurrenceMap.appendRight _ originalGuards)

def baseMember : HOL.ProofSyntax Const typingAssumptions (.app (basePredicate operations parameterA parameterP) parameterZ) := by
  have bound : 1 < originalGuards.length := by decide +kernel
  have same : originalGuards.get ⟨1, bound⟩ = .app (basePredicate operations parameterA parameterP) parameterZ := by
    simpa only [List.get_eq_getElem, List.getElem?_eq_getElem bound, Option.some.injEq] using original_base_guard
  exact (HOL.ProofSyntax.castIndices rfl same (.hyp ⟨1, bound⟩)).mono
    (HOL.ProofSyntax.OccurrenceMap.appendLeft _ originalGuards)

def methodMember : HOL.ProofSyntax Const typingAssumptions (.app (methodPredicate operations parameterA parameterP) parameterS) := by
  have bound : 0 < originalGuards.length := by decide +kernel
  have same : originalGuards.get ⟨0, bound⟩ = .app (methodPredicate operations parameterA parameterP) parameterS := by
    simpa only [List.get_eq_getElem, List.getElem?_eq_getElem bound, Option.some.injEq] using original_method_guard
  exact (HOL.ProofSyntax.castIndices rfl same (.hyp ⟨0, bound⟩)).mono
    (HOL.ProofSyntax.OccurrenceMap.appendLeft _ originalGuards)

def dependentResult := result_typed operations parameterA parameterP parameterZ parameterS typingRoots baseMember methodMember

theorem dependent_result_free : dependentResult.FunctionExtensionalityFree := by
  apply result_typed_free
  · simp only [baseMember, HOL.ProofSyntax.functionExtensionalityFree_mono, HOL.ProofSyntax.functionExtensionalityFree_castIndices, HOL.ProofSyntax.FunctionExtensionalityFree]
  · simp only [methodMember, HOL.ProofSyntax.functionExtensionalityFree_mono, HOL.ProofSyntax.functionExtensionalityFree_castIndices, HOL.ProofSyntax.FunctionExtensionalityFree]
  · intro occurrence
    simpa only [typingRoots, HOL.ProofSyntax.functionExtensionalityFree_mono] using
      encodedRoots_free EncodedConstructor.Controls.raw EncodedConstructor.Controls.interface parameters occurrence

def motivePredicate := HOL.PredicateProducts.pi (HOL.PredicateProducts.full operations.number)
  (HOL.PredicateProducts.pi (.app (.app (familyCode operations) (HOL.weaken parameterA)) (.var .vz))
    (HOL.PredicateProducts.full (operations.result ⇒ .prop)))

theorem original_guard_list : originalGuards =
    [.app (methodPredicate operations parameterA parameterP) parameterS,
     .app (basePredicate operations parameterA parameterP) parameterZ,
     .app motivePredicate parameterP,
     .app (HOL.PredicateProducts.full operations.elementPredicate) parameterA] := by decide +kernel

noncomputable def model := EncodedConstructor.Controls.model
def emptyValues : model.Valuation [] := fun index => nomatch index
noncomputable def elementValues : model.Valuation [operations.elementPredicate] :=
  model.extend emptyValues (fun _ => ULift.up True)
noncomputable def motiveValues : model.Valuation [operations.motive, operations.elementPredicate] :=
  model.extend elementValues (fun n _ r => ULift.up (r.down = n.down))
noncomputable def baseValues : model.Valuation [operations.result, operations.motive, operations.elementPredicate] :=
  model.extend motiveValues (ULift.up 0)
noncomputable def parameterValues : model.Valuation parameters :=
  model.extend baseValues (fun _ _ _ r => ULift.up (r.down + 1))

theorem original_guards_realizable : HOL.Soundness.SatisfiesHyps model parameterValues originalGuards := by
  intro formula member
  rw [original_guard_list] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · intro n _ _ h _ _ t _ _ r _ fits
    change r.down = n.down at fits
    change r.down + 1 = n.down + 1
    omega
  · rfl
  · intro n _ _ t _ _
    trivial
  · trivial

theorem typing_background_realizable : HOL.Soundness.SatisfiesHyps model parameterValues typingAssumptions := by
  intro formula member
  rcases List.mem_append.mp member with root | guard
  · rw [EncodedConstructor.assumptions_eq_closed] at root
    obtain ⟨closed, present, rfl⟩ := List.mem_map.mp root
    change (model.denote (HOL.weakenCtx parameters closed) parameterValues).down
    rw [model.denote_weakenCtx]
    exact EncodedConstructor.Controls.background_realizable closed present
  · exact original_guards_realizable formula guard

theorem dependent_result_valid :
    (model.denote (.app (resultPredicate operations parameterA parameterP)
      (appliedEliminator operations parameterA parameterP parameterZ parameterS)) parameterValues).down :=
  HOL.Soundness.extDerivation_sound dependentResult.erase (M := model) (ρ := parameterValues)
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) typing_background_realizable

noncomputable def wrongMethodValues : model.Valuation parameters :=
  model.extend baseValues (fun _ _ _ r => r)

theorem nonpreserving_method_refused :
    ¬ (model.denote (.app (methodPredicate operations parameterA parameterP) parameterS) wrongMethodValues).down := by
  intro claimed
  have emptyValid := HOL.Soundness.extDerivation_sound
    (nil_member (Γ := parameters) (Δ := []) operations parameterA).erase (M := model) (ρ := wrongMethodValues)
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) (fun _ absent => nomatch absent)
  let n : HOL.Term Const parameters operations.number := HOL.weakenCtx parameters operations.zero
  let t : HOL.Term Const parameters operations.vector := .app (HOL.weakenCtx parameters operations.nilCode) parameterA
  let h : HOL.Term Const parameters operations.element := .app (HOL.weakenCtx parameters operations.head) t
  let premises : List (HOL.Formula Const parameters) :=
    [.app (methodPredicate operations parameterA parameterP) parameterS,
     .app parameterA h, membership operations parameterA n t,
     .app (.app (.app parameterP n) t) parameterZ]
  have proof := method_at (Δ := premises) operations parameterA parameterP parameterS n h t parameterZ
    (.hyp ⟨0, by simp [premises]⟩) (.hyp ⟨1, by simp [premises]⟩)
    (.hyp ⟨2, by simp [premises]⟩) (.hyp ⟨3, by simp [premises]⟩)
  have supported : HOL.Soundness.SatisfiesHyps model wrongMethodValues premises := by
    intro formula present
    simp only [premises, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl
    · exact claimed
    · trivial
    · exact emptyValid
    · rfl
  have impossible := HOL.Soundness.extDerivation_sound proof.erase (M := model) (ρ := wrongMethodValues)
    (model.functionsRespectEqv_of_fullDomains (HOL.HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) supported
  change (0 : Nat) = 1 at impossible
  exact Nat.zero_ne_one impossible

#print axioms nil_context_admitted
#print axioms cons_context_admitted
#print axioms declared_eliminator_type_read
#print axioms exchanged_parameter_carriers_refused
#print axioms nil_membership_free
#print axioms cons_membership_free
#print axioms source_nil_membership_free
#print axioms source_cons_membership_free
#print axioms original_result_reading
#print axioms dependent_result_free
#print axioms typing_background_realizable
#print axioms dependent_result_valid
#print axioms nonpreserving_method_refused
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows.GuardedFamily.Controls
