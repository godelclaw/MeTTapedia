import Mettapedia.Languages.HOLLight.InterpretedCompilation
import Mettapedia.Languages.HOLLight.NaturalRecursorCompilation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorOpenPrefixConversion

/-!
# Native interpretation of the original open vector proofs

The finite primitive alphabet is interpreted at supplied native constructor
operations. Zero may be a compound closed term, and the vector carrier may be
an instantiated recursive-space type. The same retained source proofs are
translated; no second vector proof stack is introduced.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.OpenVectorCompilation
open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open ReverseTranslation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
abbrev SourceBase := NativeVectorComputationRows.EncodedConstructor.Controls.BaseSort
abbrev SourceConst := NativeVectorComputationRows.EncodedConstructor.Controls.Const
local infixr:60 " ⇒ " => HOL.Ty.arr

variable (raw : HOL.RawVectorConstructors.Signature AtomicTy Symbol)

def types : SourceBase → HOL.Ty AtomicTy
  | .number => raw.number
  | .element => raw.element
  | .space => raw.space

def selection (type : HOL.Ty AtomicTy) : HOL.ClosedTerm Symbol (HOL.SelectionProofs.Selection type) :=
  .const (.constant ModelInterpretation.selectionConstant (ModelInterpretation.selectionType (reverseTy type))
    (by rw [ModelInterpretation.selectionType_toHOL, toHOL_reverseTy]))

def constants : {type : HOL.Ty SourceBase} → SourceConst type →
    HOL.ClosedTerm Symbol (HOL.Ty.substitute (types raw) type)
  | _, .zero => raw.zero
  | _, .successor => raw.successor
  | _, .bottom => raw.bottom
  | _, .construct => raw.construct
  | _, .select type => selection (HOL.Ty.substitute (types raw) type)

def interpretation : HOL.TermInterpretation SourceBase SourceConst AtomicTy Symbol :=
  ⟨types raw, constants raw⟩

def inputNames : Naming (NativeVectorOpenPrefix.inputParameters.map (HOL.Ty.substitute (types raw))) :=
  Naming.cons (Name.global "__vec_tail") (Naming.cons (Name.global "__vec_index")
    (Naming.cons (Name.global "__vec_method") (Naming.cons (Name.global "__vec_base")
      (Naming.cons (Name.global "__vec_motive") (Naming.cons (Name.global "__vec_element_predicate") Naming.empty)))))

def prefixNames : Naming (NativeVectorOpenPrefix.Conversion.parameters.map (HOL.Ty.substitute (types raw))) :=
  Naming.cons (Name.global "__vec_tail") (Naming.cons (Name.global "__vec_index")
    (Naming.cons (Name.global "__vec_second") (Naming.cons (Name.global "__vec_first")
      (Naming.cons (Name.global "__vec_method") (Naming.cons (Name.global "__vec_base")
        (Naming.cons (Name.global "__vec_motive") (Naming.cons (Name.global "__vec_element_predicate") Naming.empty)))))))

def consNames : Naming ((NativeVectorComputationRows.Row.cons.parameters
    NativeVectorComputationRows.EncodedConstructor.Controls.generated).map (HOL.Ty.substitute (types raw))) :=
  Naming.cons (Name.global "__vec_tail") (Naming.cons (Name.global "__vec_head")
    (Naming.cons (Name.global "__vec_index") (Naming.cons (Name.global "__vec_method")
      (Naming.cons (Name.global "__vec_base") (Naming.cons (Name.global "__vec_motive")
        (Naming.cons (Name.global "__vec_element_predicate") Naming.empty))))))

def readMembership? [DecidableEq SourceBase] (Γ : HOL.Ctx SourceBase)
    (source type : Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Annotated.CTm
      Tower.Head Γ.length)
    (names : Naming (Γ.map (HOL.Ty.substitute (types raw)))) : Option CanonicalTerm := do
  let value ← Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.Reader.infer?
    NativeVectorOpenPrefix.lex Γ source
  let predicate ← Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.Reader.readTyped?
    NativeVectorOpenPrefix.lex Γ type (value.1 ⇒ .prop)
  pure (reverseCanonical names (HOL.ImpredicativeConnectives.expand
    ((interpretation raw).term (.app predicate.val value.2))))

theorem readMembership_complete {Γ : HOL.Ctx SourceBase}
    {source type : Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Annotated.CTm
      Tower.Head Γ.length}
    {carrier : HOL.Ty SourceBase} {value : HOL.Term SourceConst Γ carrier}
    {predicate : HOL.Term SourceConst Γ (carrier ⇒ .prop)}
    (valueRead : Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.Reads
      NativeVectorOpenPrefix.lex source value)
    (typeRead : Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.Reads
      NativeVectorOpenPrefix.lex type predicate)
    (names : Naming (Γ.map (HOL.Ty.substitute (types raw)))) :
    readMembership? raw Γ source type names = some (reverseCanonical names
      (HOL.ImpredicativeConnectives.expand ((interpretation raw).term (.app predicate value)))) := by
  unfold readMembership?
  rw [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.Reader.infer?_complete valueRead]
  simp only [Bind.bind, Option.bind_some]
  rw [Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateReading.Reader.readTyped?_complete typeRead]
  rfl

@[irreducible, noinline] def consSchema :=
  InterpretedCompilation.compile (interpretation raw)
    (NativeVectorComputationRows.EncodedConstructor.rowProof
      NativeVectorComputationRows.EncodedConstructor.Controls.raw NativeVectorComputationRows.EncodedConstructor.Controls.interface .cons)
    (NativeVectorComputationRows.EncodedConstructor.rowProof_free _ _ .cons)
    (consNames raw) ("open-vector-cons-schema", 0)

@[irreducible, noinline] def lengthMembership :=
  InterpretedCompilation.compile (interpretation raw) NativeVectorOpenPrefix.finalLength.member
    (NativeVectorValueRealizers.successor_free _ _ _ _ _ NativeVectorOpenPrefix.firstLength)
    (prefixNames raw) ("open-vector-length", 0)

@[irreducible, noinline] def outerMembership :=
  InterpretedCompilation.compile (interpretation raw) NativeVectorOpenPrefix.outer.member
    NativeVectorOpenPrefix.outer_free (prefixNames raw) ("open-vector-outer-membership", 0)

@[irreducible, noinline] def inputMembership :=
  InterpretedCompilation.compile (interpretation raw) NativeVectorOpenPrefix.inputEliminator.member
    NativeVectorOpenPrefix.input_eliminator_free (inputNames raw) ("open-vector-input-membership", 0)

@[irreducible, noinline] def prefixMembership :=
  InterpretedCompilation.compile (interpretation raw) NativeVectorOpenPrefix.realizedElimination.member
    NativeVectorOpenPrefix.realized_elimination_free (prefixNames raw) ("open-vector-substituted-membership", 0)

@[irreducible, noinline] def computation :=
  InterpretedCompilation.compile (interpretation raw) NativeVectorOpenPrefix.Conversion.equality.proof
    NativeVectorOpenPrefix.Conversion.equality_free (prefixNames raw) ("open-vector-two-cons", 0)

@[irreducible, noinline] def reducedMembership :=
  InterpretedCompilation.compile (interpretation raw) NativeVectorOpenPrefix.Conversion.reducedValue.member
    NativeVectorOpenPrefix.Conversion.reduced_value_free (prefixNames raw) ("open-vector-reduced-membership", 0)

theorem input_accepted : (ProofSystem.checker emptyAxiomPolicy).check (inputMembership raw).proof.result
    (inputMembership raw).proof.certificate = true := (inputMembership raw).proof.accepted

theorem prefix_accepted : (ProofSystem.checker emptyAxiomPolicy).check (prefixMembership raw).proof.result
    (prefixMembership raw).proof.certificate = true := (prefixMembership raw).proof.accepted

theorem computation_accepted : (ProofSystem.checker emptyAxiomPolicy).check (computation raw).proof.result
    (computation raw).proof.certificate = true := (computation raw).proof.accepted

theorem reduced_accepted : (ProofSystem.checker emptyAxiomPolicy).check (reducedMembership raw).proof.result
    (reducedMembership raw).proof.certificate = true := (reducedMembership raw).proof.accepted

theorem input_reader_agrees : readMembership? raw NativeVectorOpenPrefix.inputParameters
    NativeVectorOpenPrefix.inputElimination NativeVectorOpenPrefix.inputResultType (inputNames raw) =
      some (inputMembership raw).proof.result.sequent.concl := by
  rw [(inputMembership raw).conclusion_exact]
  exact readMembership_complete raw NativeVectorOpenPrefix.inputEliminator.termRead NativeVectorOpenPrefix.inputEliminator.typeRead _

theorem prefix_reader_agrees : readMembership? raw NativeVectorOpenPrefix.Conversion.parameters
    NativeVectorOpenPrefix.Conversion.source NativeVectorOpenPrefix.Conversion.resultType (prefixNames raw) =
      some (prefixMembership raw).proof.result.sequent.concl := by
  rw [(prefixMembership raw).conclusion_exact]
  exact readMembership_complete raw NativeVectorOpenPrefix.realizedElimination.termRead NativeVectorOpenPrefix.realizedElimination.typeRead _

theorem reduced_reader_agrees : readMembership? raw NativeVectorOpenPrefix.Conversion.parameters
    NativeVectorOpenPrefix.Conversion.target NativeVectorOpenPrefix.Conversion.resultType (prefixNames raw) =
      some (reducedMembership raw).proof.result.sequent.concl := by
  rw [(reducedMembership raw).conclusion_exact]
  exact readMembership_complete raw NativeVectorOpenPrefix.Conversion.reducedValue.termRead
    NativeVectorOpenPrefix.Conversion.reducedValue.typeRead _

#print axioms interpretation
#print axioms input_accepted
#print axioms prefix_accepted
#print axioms computation_accepted
#print axioms reduced_accepted
end Mettapedia.Languages.HOLLight.OpenVectorCompilation
