import Mettapedia.Languages.HOLLight.OpenVectorCompilation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalVectorProfileControls

/-!
# Native compilation of the original mixed Nat/Vec conversion

The same checked source certificate uses the natural zero row and vector nil
row under an open combining function. The shared interpreter retains the
native proof fragment, and the existing term interpretation supplies native
carriers and closed constants. Background premises remain explicit until a
source history discharges them.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.MixedNaturalVectorCompilation
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation TypedEquality.Annotated AnnotatedPredicateReading
open NativeNaturalVectorFamilies Programs.Annotated
open NativeNaturalVectorProfile.Controls ReverseTranslation

def nativeRoots (enabled : Programs.ComputationProfiles.Selection) :=
  FreeInterpreter.roots
    (NativeNaturalVectorProfile.entries raw vectorInterface naturalSelection profile) enabled
    (NativeNaturalVectorProfile.entries_free raw vectorInterface naturalSelection profile)

def received := Interpreter.check? (church profile) (JudgmentReplay.decoder profile)
  FreeInterpreter.operations (nativeRoots profile) parameters sourceContext mixedLeft mixedRight
  (.const natName) sourceContextCertificate mixedCertificate

theorem interpreted : received.isSome = true := by decide +kernel

def result := received.get interpreted

theorem result_carrier : result.carrier = raw.number := by decide +kernel

def nativeEquality : FreeInterpreter.Evidence lex
    (NativeNaturalVectorProfile.closedAssumptions raw vectorInterface naturalSelection)
    parameters mixedLeft mixedRight raw.number :=
  result_carrier ▸ result.evidence

@[irreducible] def equality : EqualityAt lex
    (NativeNaturalVectorProfile.closedAssumptions raw vectorInterface naturalSelection)
    parameters mixedLeft mixedRight raw.number := nativeEquality.val

theorem equality_free : equality.proof.FunctionExtensionalityFree := by
  unfold equality
  exact nativeEquality.property

theorem original_reading_preserved :
    (⟨raw.number, equality.left⟩ : (type : HOL.Ty BaseSort) × HOL.Term Const parameters type) =
      ⟨NativeNaturalVectorProfile.Controls.result.carrier,
        NativeNaturalVectorProfile.Controls.result.evidence.left⟩ ∧
    (⟨raw.number, equality.right⟩ : (type : HOL.Ty BaseSort) × HOL.Term Const parameters type) =
      ⟨NativeNaturalVectorProfile.Controls.result.carrier,
        NativeNaturalVectorProfile.Controls.result.evidence.right⟩ :=
  ⟨Reader.coherent equality.leftRead NativeNaturalVectorProfile.Controls.result.evidence.leftRead,
    Reader.coherent equality.rightRead NativeNaturalVectorProfile.Controls.result.evidence.rightRead⟩

theorem exact_root_citations : NativeVectorOpenPrefix.Conversion.citedRows mixedCertificate = [0, 2] := by
  decide +kernel

variable (target : HOL.RawVectorConstructors.Signature AtomicTy Symbol)

def names : Naming (parameters.map (HOL.Ty.substitute (OpenVectorCompilation.types target))) :=
  Naming.cons (Name.global "__mix_combine")
    (Naming.cons (Name.global "__mix_vec_method")
      (Naming.cons (Name.global "__mix_vec_base")
        (Naming.cons (Name.global "__mix_vec_motive")
          (Naming.cons (Name.global "__mix_element_predicate")
            (Naming.cons (Name.global "__mix_nat_method")
              (Naming.cons (Name.global "__mix_nat_base")
                (Naming.cons (Name.global "__mix_nat_motive") Naming.empty)))))))

@[irreducible, noinline] def compile :=
  InterpretedCompilation.compile (OpenVectorCompilation.interpretation target)
    equality.proof equality_free (names target) ("mixed-natural-vector", 0)

theorem accepted : (ProofSystem.checker emptyAxiomPolicy).check (compile target).proof.result
    (compile target).proof.certificate = true := (compile target).proof.accepted

def readEquality? : Option CanonicalTerm := do
  let left ← Reader.readTyped? lex parameters mixedLeft raw.number
  let right ← Reader.readTyped? lex parameters mixedRight raw.number
  pure (reverseCanonical (names target) (HOL.ImpredicativeConnectives.expand
    ((OpenVectorCompilation.interpretation target).term (.eq left.val right.val))))

theorem reader_agrees : readEquality? target = some (compile target).proof.result.sequent.concl := by
  rw [(compile target).conclusion_exact]
  unfold readEquality?
  rw [Reader.readTyped?_complete equality.leftRead]
  simp only [Bind.bind, Option.bind_some]
  rw [Reader.readTyped?_complete equality.rightRead]
  rfl

#print axioms interpreted
#print axioms original_reading_preserved
#print axioms exact_root_citations
#print axioms accepted
#print axioms reader_agrees
end Mettapedia.Languages.HOLLight.MixedNaturalVectorCompilation
