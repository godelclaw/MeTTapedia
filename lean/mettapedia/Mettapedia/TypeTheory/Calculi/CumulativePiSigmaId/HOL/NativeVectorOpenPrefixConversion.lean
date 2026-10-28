import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorOpenPrefix
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateFreeInterpreter

/-!
# Two original cons computations over a neutral tail

The first root instance removes the outer constructor. Application congruence
then transports the second root instance through the open method. The tail
eliminator remains in the reduct. Both roots cite the original address 3.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorOpenPrefix
namespace Conversion
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading NativeNaturalVectorFamilies
open Programs.Annotated

abbrev A : CTm Tower.Head 8 := .var 7
abbrev P : CTm Tower.Head 8 := .var 6
abbrev z : CTm Tower.Head 8 := .var 5
abbrev s : CTm Tower.Head 8 := .var 4
abbrev x : CTm Tower.Head 8 := .var 3
abbrev y : CTm Tower.Head 8 := .var 2
abbrev m : CTm Tower.Head 8 := .var 1
abbrev w : CTm Tower.Head 8 := .var 0

def applyMethod (index head tail recursive : CTm Tower.Head 8) : CTm Tower.Head 8 :=
  .app (.app (.app (.app s index) head) tail) recursive

def tailElimination : CTm Tower.Head 8 := Append.eliminate A P z s m w
def innerElimination : CTm Tower.Head 8 := Append.eliminate A P z s (Functions.successor m) sourceInner
def source : CTm Tower.Head 8 := Append.eliminate A P z s (Functions.successor (Functions.successor m)) sourceOuter
def middle : CTm Tower.Head 8 := applyMethod (Functions.successor m) x sourceInner innerElimination
def target : CTm Tower.Head 8 := applyMethod (Functions.successor m) x sourceInner (applyMethod m y w tailElimination)
def resultType : CTm Tower.Head 8 := .app (.app P (Functions.successor (Functions.successor m))) sourceOuter

theorem motive_typed : CTyped (church profile) context.source P (Append.familyType A) := .var 6

theorem base_typed : CTyped (church profile) context.source z (.app (.app P Functions.zero) (Append.nil A)) := .var 5

theorem method_typed : CTyped (church profile) context.source s (Append.methodType A P) := .var 4

def rowArguments (index head tail : CTm Tower.Head 8) : CSub Tower.Head 7 8 :=
  Fin.cases tail (Fin.cases head (Fin.cases index (Fin.cases s (Fin.cases z (Fin.cases P (fun _ => A))))))

theorem row_arguments_typed {index head tail : CTm Tower.Head 8}
    (indexTyped : CTyped (church profile) context.source index Functions.natural)
    (headTyped : CTyped (church profile) context.source head A)
    (tailTyped : CTyped (church profile) context.source tail (Append.vector A index)) :
    CSubstMor (church profile) (Programs.Annotated.context ⟨3, by decide⟩) context.source (rowArguments index head tail) := by
  intro position
  refine Fin.cases tailTyped (Fin.cases headTyped (Fin.cases indexTyped
    (Fin.cases method_typed (Fin.cases base_typed (Fin.cases motive_typed (Fin.cases element_typed8 (fun impossible => Fin.elim0 impossible))))))) position

theorem cons_equal {index head tail : CTm Tower.Head 8}
    (indexTyped : CTyped (church profile) context.source index Functions.natural)
    (headTyped : CTyped (church profile) context.source head A)
    (tailTyped : CTyped (church profile) context.source tail (Append.vector A index)) :
    CEqual (church profile) context.source
      (Append.eliminate A P z s (Functions.successor index) (Append.cons A index head tail))
      (applyMethod index head tail (Append.eliminate A P z s index tail))
      (.app (.app P (Functions.successor index)) (Append.cons A index head tail)) := by
  have step := instantiated_equal profile ⟨3, by decide⟩ rfl (row_arguments_typed indexTyped headTyped tailTyped)
  change CEqual (church profile) context.source
    ((liftTm vecConsIotaLeft).subst (rowArguments index head tail))
    ((liftTm vecConsIotaRight).subst (rowArguments index head tail))
    ((liftTm vecConsIotaType).subst (rowArguments index head tail)) at step
  exact step

theorem outer_equal : CEqual (church profile) context.source source middle resultType :=
  cons_equal firstLength.typed headX.typed inner.typed

theorem inner_equal : CEqual (church profile) context.source innerElimination (applyMethod m y w tailElimination)
    (.app (.app P (Functions.successor m)) sourceInner) :=
  cons_equal lengthValue.typed headY.typed tailValue.typed

def outerMethod : CTm Tower.Head 8 := .app (.app (.app s (Functions.successor m)) x) sourceInner

theorem outer_method_typed : CTyped (church profile) context.source outerMethod
    (.pi (.app (.app P (Functions.successor m)) sourceInner) (resultType.rename wk)) := by
  exact CDerivable.appElim (CDerivable.appElim (CDerivable.appElim method_typed firstLength.typed) headX.typed) inner.typed

theorem second_equal : CEqual (church profile) context.source middle target resultType := by
  simpa only [CTm.inst0_rename_wk, middle, target, applyMethod, outerMethod] using CDerivable.appCong (.refl outer_method_typed) inner_equal

theorem two_cons_equal : CEqual (church profile) context.source source target resultType :=
  .trans outer_equal second_equal

theorem source_typed : CTyped (church profile) context.source source resultType := realizedElimination.typed

def firstElementCertificate : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile (.var (Γ := baseContext.source) 3) []

def secondElementCertificate : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile (.var (Γ := xContext.source) 4) []

def lengthDomainCertificate : JudgmentReplay.Certificate profile := by
  annotated_certificate 12000 (Functions.natural_typed profile (Γ := yContext.source))

def tailDomainCertificate : JudgmentReplay.Certificate profile := by
  annotated_certificate 12000 (Append.vector_typed profile element_typed7 index7.typed)

def contextCertificate : JudgmentReplay.ContextCertificate profile 8 :=
  .snoc (.snoc (.snoc (.snoc
    (NativeVectorComputationRows.EncodedConstructor.Controls.contextCertificate .nil)
    (.sort (.param 0)) firstElementCertificate)
    (.sort (.param 0)) secondElementCertificate)
    (.sort (.const 0)) lengthDomainCertificate)
    (.sort (.param 0)) tailDomainCertificate

def innerLeftCertificate : JudgmentReplay.Certificate profile := by
  annotated_certificate 12000 ((Evidence.left_3 profile).substitute
    (row_arguments_typed lengthValue.typed headY.typed tailValue.typed))
def innerRightCertificate : JudgmentReplay.Certificate profile := by
  annotated_certificate 12000 ((Evidence.right_3 profile).substitute
    (row_arguments_typed lengthValue.typed headY.typed tailValue.typed))
def outerLeftCertificate : JudgmentReplay.Certificate profile := by
  annotated_certificate 12000 ((Evidence.left_3 profile).substitute
    (row_arguments_typed firstLength.typed headX.typed inner.typed))
def outerRightCertificate : JudgmentReplay.Certificate profile := by
  annotated_certificate 12000 ((Evidence.right_3 profile).substitute
    (row_arguments_typed firstLength.typed headX.typed inner.typed))

def innerValueCertificate : JudgmentReplay.Certificate profile := by
  annotated_certificate 12000 inner.typed

def outerIndexCertificate : JudgmentReplay.Certificate profile := by
  annotated_certificate 12000 firstLength.typed

def outerMethodCertificate : JudgmentReplay.Certificate profile := by
  annotated_certificate 12000 outer_method_typed

def variableCertificate (position : Fin 8) : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile (.var (Γ := context.source) position) []

def innerRootCertificate : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.root (Γ := context.source) (left := innerElimination) (right := applyMethod m y w tailElimination)
      (A := .app (.app P (Functions.successor m)) sourceInner) ⟨3, List.ofFn (rowArguments m y w)⟩)
    [innerLeftCertificate, innerRightCertificate, variableCertificate 0, variableCertificate 2, variableCertificate 1,
      variableCertificate 4, variableCertificate 5, variableCertificate 6, variableCertificate 7]

def outerRootCertificate : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.root (Γ := context.source) (left := source) (right := middle) (A := resultType)
      ⟨3, List.ofFn (rowArguments (Functions.successor m) x sourceInner)⟩)
    [outerLeftCertificate, outerRightCertificate, innerValueCertificate, variableCertificate 3, outerIndexCertificate,
      variableCertificate 4, variableCertificate 5, variableCertificate 6, variableCertificate 7]

def secondCertificate : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.appCong (Γ := context.source) (f := outerMethod) (g := outerMethod)
      (a := innerElimination) (b := applyMethod m y w tailElimination)
      (A := .app (.app P (Functions.successor m)) sourceInner) (B := resultType.rename wk))
    [JudgmentReplay.Producer.assemble profile
      (.refl (Γ := context.source) (a := outerMethod)
        (A := .pi (.app (.app P (Functions.successor m)) sourceInner) (resultType.rename wk))) [outerMethodCertificate],
     innerRootCertificate]

def certificate : JudgmentReplay.Certificate profile :=
  JudgmentReplay.Producer.assemble profile
    (.trans (Γ := context.source) (a := source) (b := middle) (c := target) (A := resultType))
    [outerRootCertificate, secondCertificate]

abbrev parameters : HOL.Ctx BaseSort :=
  [operations.vector, operations.number, operations.element, operations.element, operations.method,
    operations.result, operations.motive, operations.elementPredicate]

def nativeRoots (enabled : Programs.ComputationProfiles.Selection) :=
  FreeInterpreter.roots (NativeNaturalVectorProfile.entries raw interface naturalSelection profile) enabled
    (NativeNaturalVectorProfile.entries_free raw interface naturalSelection profile)

def received := AnnotatedPredicateReading.Interpreter.check? (church profile) (JudgmentReplay.decoder profile)
  FreeInterpreter.operations (nativeRoots profile)
  parameters context.source source target resultType contextCertificate certificate

def citedRows : JudgmentReplay.Certificate profile → List Nat
  | .node _ ⟨_, instruction⟩ _ children =>
      (match instruction with | .root citation => [citation.row] | _ => []) ++
        (List.ofFn (fun index => citedRows (children index))).flatten

theorem source_certificate_checked : JudgmentReplay.check profile certificate
    (.equality context.source source target resultType) = true := by decide +kernel

theorem source_context_checked : JudgmentReplay.checkContext profile context.source contextCertificate = true := by decide +kernel

theorem exact_root_citations : citedRows certificate = [3, 3] := by decide +kernel

theorem interpreted : received.isSome = true := by decide +kernel

def result := received.get interpreted

theorem result_carrier : result.carrier = operations.result := by decide +kernel

theorem result_free : result.evidence.val.proof.FunctionExtensionalityFree := result.evidence.property

def nativeEquality : FreeInterpreter.Evidence lex NativeVectorOpenPrefix.roots parameters source target operations.result :=
  result_carrier ▸ result.evidence

def equality : EqualityAt lex NativeVectorOpenPrefix.roots parameters source target operations.result := nativeEquality.val

theorem equality_free : equality.proof.FunctionExtensionalityFree := nativeEquality.property

def reducedValue : GuardedRealizer NativeVectorOpenPrefix.roots context target resultType operations.result :=
  realizedElimination.rewrite (levelModel profile) two_cons_equal equality

theorem reduced_value_free : reducedValue.Free :=
  GuardedRealizer.rewrite_free _ realizedElimination two_cons_equal equality realized_elimination_free equality_free

def receivedWith (enabled : Programs.ComputationProfiles.Selection) :=
  Interpreter.check? (church profile) (JudgmentReplay.decoder profile)
    FreeInterpreter.operations (nativeRoots enabled)
    parameters context.source source target resultType contextCertificate certificate

theorem disabled_cons_refused : (receivedWith (fun index => index.val != 3)).isNone = true := by decide +kernel

theorem only_cons_required : (receivedWith (fun index => index.val == 3)).isSome = true := by decide +kernel

theorem changed_endpoint_refused : JudgmentReplay.check profile certificate
    (.equality context.source source z resultType) = false := by decide +kernel

theorem swapped_heads_refused : JudgmentReplay.check profile certificate
    (.equality context.source source
      (applyMethod (Functions.successor m) y sourceInner (applyMethod m x w tailElimination)) resultType) = false := by
  decide +kernel

/-- No declared root computation acts on the eliminator at its neutral tail.
This does not assert nonconvertibility under arbitrary conversion paths. -/
theorem neutral_tail_no_root (target : Tower.Tm 8) :
    ¬ (Programs.ComputationProfiles.rules profile).computation.step tailElimination.erase target := by
  intro step
  have generated := (presentation profile).mp step
  generalize leftEquation : tailElimination.erase = left at generated
  cases generated with
  | @instantiate arity left right selected assignment =>
      obtain ⟨index, _permitted, row⟩ := selected
      fin_cases index
      · change (⟨3, natZeroIotaLeft, natZeroIotaRight⟩ : Σ k, Tower.Tm k × Tower.Tm k) = ⟨arity, left, right⟩ at row
        cases row
        simp [tailElimination, Append.eliminate, CTm.erase, natZeroIotaLeft,
          natEliminateAtParameters, Presentation.subst] at leftEquation
      · change (⟨4, natSuccIotaLeft, natSuccIotaRight⟩ : Σ k, Tower.Tm k × Tower.Tm k) = ⟨arity, left, right⟩ at row
        cases row
        simp [tailElimination, Append.eliminate, CTm.erase, natSuccIotaLeft,
          natEliminateAtSuccParameters, succApp, Presentation.subst] at leftEquation
      · change (⟨4, vecNilIotaLeft, vecNilIotaRight⟩ : Σ k, Tower.Tm k × Tower.Tm k) = ⟨arity, left, right⟩ at row
        cases row
        simp [tailElimination, Append.eliminate, CTm.erase, vecNilIotaLeft,
          vecEliminateAtParameters, vnilApp, Presentation.subst] at leftEquation
      · change (⟨7, vecConsIotaLeft, vecConsIotaRight⟩ : Σ k, Tower.Tm k × Tower.Tm k) = ⟨arity, left, right⟩ at row
        cases row
        simp [tailElimination, Append.eliminate, CTm.erase, vecConsIotaLeft,
          vecEliminateAtConsParameters, vconsApp, succApp, Presentation.subst] at leftEquation


#print axioms row_arguments_typed
#print axioms two_cons_equal
#print axioms source_typed
#print axioms source_certificate_checked
#print axioms exact_root_citations
#print axioms interpreted
end Conversion
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorOpenPrefix
