import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorValueRealizers
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalVectorProfileControls

/-!
# A canonical two-element prefix over an open Vec tail

The context retains the original element, motive, base and method parameters,
then introduces two elements, a length and a vector of that length. The prefix
uses the original cons declaration and actual guard evidence. The tail and its
length remain open variables throughout the construction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorOpenPrefix
open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading NativeNaturalVectorFamilies
local infixr:60 " ⇒ " => HOL.Ty.arr

abbrev BaseSort := NativeNaturalVectorProfile.Controls.BaseSort
abbrev Const := NativeNaturalVectorProfile.Controls.Const
def raw := NativeNaturalVectorProfile.Controls.raw
def interface := NativeNaturalVectorProfile.Controls.vectorInterface
def naturalSelection := NativeNaturalVectorProfile.Controls.naturalSelection
def operations := NativeNaturalVectorProfile.Controls.vectorOps
def profile := NativeNaturalVectorProfile.Controls.profile
def lex := NativeNaturalVectorProfile.Controls.lex
def roots := NativeNaturalVectorProfile.closedAssumptions raw interface naturalSelection

theorem compatible : LexicalMap (NativeVectorComputationRows.GuardedFamily.lexical operations) lex (fun head => head) :=
  NativeNaturalVectorProfile.vector_lexical raw interface naturalSelection

abbrev baseParameters : HOL.Ctx BaseSort := [operations.method, operations.result, operations.motive, operations.elementPredicate]

def baseRead := Reader.admitContext? (Programs.Annotated.church profile) lex
  (Programs.Annotated.JudgmentReplay.decoder profile) baseParameters
  (NativeVectorComputationRows.EncodedConstructor.Controls.sourceContext .nil)
  (NativeVectorComputationRows.EncodedConstructor.Controls.contextCertificate .nil)

theorem base_read : baseRead.isSome = true := by decide +kernel

def baseContext : GuardedContext (Programs.Annotated.church profile) lex baseParameters := GuardedContext.ofAdmitted (baseRead.get base_read)

def elementValue : GuardedRealizer roots baseContext (.var 3)
    (Programs.Annotated.Append.elementSort) operations.elementPredicate :=
  GuardedRealizer.ofVariable roots baseContext (.vs (.vs (.vs .vz)))

def element4 : GuardedTypeFormation baseContext (.var 3) operations.element :=
  GuardedTypeFormation.ofUniverseValue (level := NativeVectorComputationRows.GuardedFamily.elementHead)
    (by decide +kernel) elementValue

def xContext := element4.snoc

def addX := GuardedSubstitution.weakening roots baseContext element4.predicate element4.reading element4.formed

def element5 : GuardedTypeFormation xContext (.var 4) operations.element := element4.substitute addX

def yContext := element5.snoc

def addY := GuardedSubstitution.weakening roots xContext element5.predicate element5.reading element5.formed

def element6 : GuardedTypeFormation yContext (.var 5) operations.element := element5.substitute addY

def number6 := NativeVectorValueRealizers.naturalFormation operations compatible profile yContext

def indexContext := number6.snoc

def addIndex := GuardedSubstitution.weakening roots yContext number6.predicate number6.reading number6.formed

def element7 : GuardedTypeFormation indexContext (.var 6) operations.element := element6.substitute addIndex

def index7 : GuardedRealizer roots indexContext (.var 0) (.const natName) operations.number :=
  GuardedRealizer.ofVariable roots indexContext .vz

theorem element_typed7 : CTyped (Programs.Annotated.church profile) indexContext.source (.var 6)
    Programs.Annotated.Append.elementSort := .var 6

def vector7 := NativeVectorValueRealizers.vectorFormation operations compatible profile indexContext roots
  element7 element_typed7 index7

def context := vector7.snoc

def addTail := GuardedSubstitution.weakening roots indexContext vector7.predicate vector7.reading vector7.formed

def element8 : GuardedTypeFormation context (.var 7) operations.element := element7.substitute addTail

def lengthValue : GuardedRealizer roots context (.var 1) (.const natName) operations.number :=
  GuardedRealizer.ofVariable roots context (.vs .vz)

def headX : GuardedRealizer roots context (.var 3) (.var 7) operations.element :=
  GuardedRealizer.ofVariable roots context (.vs (.vs (.vs .vz)))

def headY : GuardedRealizer roots context (.var 2) (.var 7) operations.element :=
  GuardedRealizer.ofVariable roots context (.vs (.vs .vz))

def tailValue : GuardedRealizer roots context (.var 0)
    (Programs.Annotated.Append.vector (.var 7) (.var 1)) operations.vector :=
  GuardedRealizer.ofVariable roots context .vz

theorem element_typed8 : CTyped (Programs.Annotated.church profile) context.source (.var 7)
    Programs.Annotated.Append.elementSort := .var 7

def inner := NativeVectorValueRealizers.cons operations compatible profile context roots
  element8 element_typed8 lengthValue headY tailValue

def firstLength := NativeVectorValueRealizers.successor operations compatible profile context roots lengthValue

def outer := NativeVectorValueRealizers.cons operations compatible profile context roots
  element8 element_typed8 firstLength headX inner

def finalLength := NativeVectorValueRealizers.successor operations compatible profile context roots firstLength

def sourceInner : CTm Tower.Head 8 := Programs.Annotated.Append.cons (.var 7) (.var 1) (.var 2) (.var 0)
def sourceOuter : CTm Tower.Head 8 := Programs.Annotated.Append.cons (.var 7)
  (Programs.Annotated.Functions.successor (.var 1)) (.var 3) sourceInner

theorem inner_typed : CTyped (Programs.Annotated.church profile) context.source sourceInner
    (Programs.Annotated.Append.vector (.var 7) (Programs.Annotated.Functions.successor (.var 1))) := inner.typed

theorem outer_typed : CTyped (Programs.Annotated.church profile) context.source sourceOuter
    (Programs.Annotated.Append.vector (.var 7)
      (Programs.Annotated.Functions.successor (Programs.Annotated.Functions.successor (.var 1)))) := outer.typed

theorem inner_free : inner.Free := NativeVectorValueRealizers.cons_free _ _ _ _ _ _ _ _ _ _
  (GuardedRealizer.ofVariable_free roots context _) (GuardedRealizer.ofVariable_free roots context _)

theorem outer_free : outer.Free := NativeVectorValueRealizers.cons_free _ _ _ _ _ _ _ _ _ _
  (GuardedRealizer.ofVariable_free roots context _) inner_free

def baseRename : Ren 4 8 := fun index => wk (wk (wk (wk index)))

def baseCodeRename : HOL.Rename BaseSort baseParameters
    (operations.vector :: operations.number :: operations.element :: operations.element :: baseParameters) :=
  fun index => .vs (.vs (.vs (.vs index)))

theorem base_context_placement : CCtxRen baseContext.source context.source baseRename :=
  placement_succ (placement_succ (placement_succ (CCtxRen.wk baseContext.source (.var 3))
    (.var 4)) (.const natName)) (Programs.Annotated.Append.vector (.var 6) (.var 0))

def basePlacement := GuardedSubstitution.ofRenaming roots baseContext context baseRename baseCodeRename
  (fun _ => rfl) base_context_placement

def inputNumber := NativeVectorValueRealizers.naturalFormation operations compatible profile baseContext

def inputIndexContext := inputNumber.snoc

def inputAddIndex := GuardedSubstitution.weakening roots baseContext inputNumber.predicate inputNumber.reading inputNumber.formed

def inputElement : GuardedTypeFormation inputIndexContext (.var 4) operations.element := element4.substitute inputAddIndex

def inputIndex : GuardedRealizer roots inputIndexContext (.var 0) (.const natName) operations.number :=
  GuardedRealizer.ofVariable roots inputIndexContext .vz

theorem input_element_typed : CTyped (Programs.Annotated.church profile) inputIndexContext.source (.var 4)
    Programs.Annotated.Append.elementSort := .var 4

def inputVector := NativeVectorValueRealizers.vectorFormation operations compatible profile inputIndexContext roots
  inputElement input_element_typed inputIndex

def inputContext := inputVector.snoc

def indexAssignment := GuardedSubstitution.cons basePlacement inputNumber.predicate inputNumber.reading inputNumber.formed finalLength

def prefixAssignment := GuardedSubstitution.cons indexAssignment inputVector.predicate inputVector.reading inputVector.formed outer

theorem basePlacement_free : basePlacement.Free :=
  GuardedSubstitution.ofRenaming_free roots baseContext context baseRename baseCodeRename
    (fun _ => rfl) base_context_placement

theorem prefixAssignment_free : prefixAssignment.Free := by
  have indexFree : indexAssignment.Free :=
    GuardedSubstitution.cons_free basePlacement inputNumber.predicate inputNumber.reading inputNumber.formed finalLength
      basePlacement_free (NativeVectorValueRealizers.successor_free operations compatible profile context roots firstLength)
  change (indexAssignment.cons inputVector.predicate inputVector.reading inputVector.formed outer).Free
  exact GuardedSubstitution.cons_free indexAssignment inputVector.predicate inputVector.reading inputVector.formed outer indexFree outer_free

def inputLengthVariable : GuardedRealizer roots inputContext (.var 1) (.const natName) operations.number :=
  GuardedRealizer.ofVariable roots inputContext (.vs .vz)

def inputVectorVariable : GuardedRealizer roots inputContext (.var 0)
    (Programs.Annotated.Append.vector (.var 5) (.var 1)) operations.vector :=
  GuardedRealizer.ofVariable roots inputContext .vz

theorem input_vector_variable_free : inputVectorVariable.Free := by
  unfold GuardedRealizer.Free inputVectorVariable GuardedRealizer.ofVariable
  exact inputContext.variableProof_free roots HOL.Var.vz


abbrev inputParameters : HOL.Ctx BaseSort :=
  [operations.vector, operations.number, operations.method, operations.result, operations.motive, operations.elementPredicate]

def inputElementValue := GuardedRealizer.ofVariable roots inputContext
  (.vs (.vs (.vs (.vs (.vs .vz)))) : HOL.Var inputParameters operations.elementPredicate)
def inputMotive := GuardedRealizer.ofVariable roots inputContext
  (.vs (.vs (.vs (.vs .vz))) : HOL.Var inputParameters operations.motive)
def inputBase := GuardedRealizer.ofVariable roots inputContext
  (.vs (.vs (.vs .vz)) : HOL.Var inputParameters operations.result)
def inputMethod := GuardedRealizer.ofVariable roots inputContext
  (.vs (.vs .vz) : HOL.Var inputParameters operations.method)

def inputRoots : NativeVectorComputationRows.GuardedFamily.RootEvidence operations inputParameters (inputContext.hypotheses roots) :=
  fun occurrence => by
    have original := NativeVectorComputationRows.GuardedFamily.encodedRoots raw interface inputParameters occurrence
    have closed := HOL.ProofSyntax.castIndices
      (NativeVectorComputationRows.EncodedConstructor.assumptions_eq_closed raw interface inputParameters) rfl original
    exact ((NativeNaturalVectorProfile.vectorExtension raw interface naturalSelection).proof closed).mono
      (HOL.ProofSyntax.OccurrenceMap.appendRight (assumptions roots inputParameters) inputContext.telescope.hypotheses)

def inputResultType : CTm Tower.Head 6 := .app (.app (.var 4) (.var 1)) (.var 0)
def inputElimination : CTm Tower.Head 6 :=
  Programs.Annotated.Append.eliminate (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

theorem input_elimination_typed : CTyped (Programs.Annotated.church profile) inputContext.source inputElimination inputResultType :=
  Programs.Annotated.Append.eliminate_typed profile inputElementValue.typed inputMotive.typed inputBase.typed inputMethod.typed
    inputLengthVariable.typed inputVectorVariable.typed

theorem input_base_reading : Reads lex (Γ := inputParameters)
    (inputContext.source.lookup (3 : Fin 6))
    (NativeVectorComputationRows.GuardedFamily.basePredicate operations inputElementValue.term inputMotive.term) :=
  Reader.infer?_sound _ _ _ _ _ (by decide +kernel)

theorem input_method_reading : Reads lex (Γ := inputParameters)
    (inputContext.source.lookup (2 : Fin 6))
    (NativeVectorComputationRows.GuardedFamily.methodPredicate operations inputElementValue.term inputMotive.term) :=
  Reader.infer?_sound _ _ _ _ _ (by decide +kernel)

theorem input_vector_reading : Reads lex (Γ := inputParameters)
    (Programs.Annotated.Append.vector (.var 5) (.var 1))
    (.app (.app (NativeVectorComputationRows.GuardedFamily.familyCode operations) inputElementValue.term) inputLengthVariable.term) :=
  Reader.infer?_sound _ _ _ _ _ (by decide +kernel)

def inputBaseGuard : HOL.ProofSyntax Const (inputContext.hypotheses roots)
    (.app (NativeVectorComputationRows.GuardedFamily.basePredicate operations inputElementValue.term inputMotive.term) inputBase.term) :=
  HOL.ProofSyntax.castIndices rfl
    (congrArg (fun predicate => HOL.Term.app predicate inputBase.term)
      (Reader.term_unique inputBase.typeRead input_base_reading)) inputBase.member

def inputMethodGuard : HOL.ProofSyntax Const (inputContext.hypotheses roots)
    (.app (NativeVectorComputationRows.GuardedFamily.methodPredicate operations inputElementValue.term inputMotive.term) inputMethod.term) :=
  HOL.ProofSyntax.castIndices rfl
    (congrArg (fun predicate => HOL.Term.app predicate inputMethod.term)
      (Reader.term_unique inputMethod.typeRead input_method_reading)) inputMethod.member

def inputVectorGuard : HOL.ProofSyntax Const (inputContext.hypotheses roots)
    (NativeVectorComputationRows.GuardedFamily.membership operations inputElementValue.term inputLengthVariable.term inputVectorVariable.term) :=
  HOL.ProofSyntax.castIndices rfl
    (congrArg (fun predicate => HOL.Term.app predicate inputVectorVariable.term)
      (Reader.term_unique inputVectorVariable.typeRead input_vector_reading)) inputVectorVariable.member

def inputEliminator : GuardedRealizer roots inputContext inputElimination inputResultType operations.result where
  typed := input_elimination_typed
  term := .app (.app (NativeVectorComputationRows.GuardedFamily.appliedEliminator operations
    inputElementValue.term inputMotive.term inputBase.term inputMethod.term) inputLengthVariable.term) inputVectorVariable.term
  predicate := .app (.app inputMotive.term inputLengthVariable.term) inputVectorVariable.term
  termRead := .application (.application (.application (.application (.application
    (.application (NativeVectorValueRealizers.eliminatorRead operations compatible) inputElementValue.termRead)
      inputMotive.termRead) inputBase.termRead) inputMethod.termRead) inputLengthVariable.termRead) inputVectorVariable.termRead
  typeRead := .application (.application inputMotive.termRead inputLengthVariable.termRead) inputVectorVariable.termRead
  member := NativeVectorComputationRows.GuardedFamily.result_at operations inputElementValue.term inputMotive.term
    inputBase.term inputMethod.term inputLengthVariable.term inputVectorVariable.term inputRoots
    inputBaseGuard inputMethodGuard inputVectorGuard

theorem input_roots_free : ∀ occurrence, (inputRoots occurrence).FunctionExtensionalityFree := by
  intro occurrence
  simp only [inputRoots, HOL.ProofSyntax.functionExtensionalityFree_mono,
    ReadingExtension.proof, HOL.ProofSyntax.functionExtensionalityFree_castIndices]
  exact NativeVectorComputationRows.GuardedFamily.encodedRoots_free raw interface inputParameters occurrence

theorem input_eliminator_free : inputEliminator.Free := by
  apply NativeVectorComputationRows.GuardedFamily.result_at_free
  · simpa only [inputBaseGuard, inputBase, GuardedRealizer.Free, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using
      GuardedRealizer.ofVariable_free roots inputContext (.vs (.vs (.vs .vz)))
  · simpa only [inputMethodGuard, inputMethod, GuardedRealizer.Free, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using
      GuardedRealizer.ofVariable_free roots inputContext (.vs (.vs .vz))
  · simpa only [GuardedRealizer.Free, inputVectorGuard, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using input_vector_variable_free
  · exact input_roots_free

def realizedElimination := inputEliminator.substitute prefixAssignment

theorem realized_elimination_free : realizedElimination.Free := by
  unfold realizedElimination
  apply GuardedRealizer.substitute_free
  · exact input_eliminator_free
  · exact prefixAssignment_free

#print axioms base_read
#print axioms outer_typed
#print axioms outer_free
#print axioms prefixAssignment_free
#print axioms input_elimination_typed
#print axioms realized_elimination_free
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorOpenPrefix
