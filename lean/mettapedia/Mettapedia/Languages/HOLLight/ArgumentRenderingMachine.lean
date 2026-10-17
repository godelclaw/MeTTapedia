import Mettapedia.Languages.HOLLight.TemplateInstantiationMachine
import Mettapedia.Computability.WordHomomorphismMachine
import Mettapedia.Computability.BinaryStackArithmetic
import Mettapedia.Computability.StackMachineRegisters
import Mettapedia.Languages.HOLLight.InferenceStorageBounds
import Mettapedia.GSLT.LanguageDef.CertificateDataEncoding
import Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming
import Mettapedia.GSLT.LanguageDef.PatternSpanExecution

/-!
# Executed source argument rendering components

The source argument codec already stores the complete flat pattern tokens.
The original HOL presentation uses those exact tokens as the namespace of
an opaque data constant. Fixed framing therefore turns the existing source
word into the complete original raw term or checked term word by copying
the dynamic payload once. Admitted binders and collections keep all their
stored data; this operation does not reinterpret them as HOL binders.

Nullary constructors reuse the original token-list framing and indexed name
selection. Binary arities have a separate executed conversion into the
original namespace components. Recursive application rendering uses the
original ordered app spine and curried constructor type; the wire equations
below expose their complete framing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.HOLLight.ArgumentRenderingMachine

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability.WordTemplateMachine
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateDataEncoding
open Mettapedia.Logic.HOL.Embedding.InferenceRules
open Mettapedia.Languages.HOLLight.InferenceHosting
open Mettapedia.Languages.HOLLight.InferenceStorageBounds
open Mettapedia.Languages.HOLLight.TemplateInstantiationMachine (termWire)
open Turing StateTransition Polynomial

/-- The exact existing source codec, including opaque binder metadata. -/
def patternWire (pattern : Pattern) : List Alphabet := encodeWith patternCodec pattern

/-- The original typed translation of a closed source argument. -/
abbrev renderedArgument (pattern : Pattern) : CanonicalTerm :=
  ReverseTranslation.reverseCanonical ReverseTranslation.Naming.empty (term (encode pattern))

def argumentWire (pattern : Pattern) : List Alphabet :=
  encodeWith canonicalCodec (renderedArgument pattern)

/-- These are precisely the pattern constructors represented as opaque
literals by the existing source-to-HOL translation. -/
def isOpaque : Pattern → Bool
  | .fvar _ | .apply _ _ => false
  | _ => true

def rawPrefix : List Alphabet :=
  [4] ++ encodeData (.atom 0) ++ [4, 4, 4] ++
    [4] ++ encodeData (Codec.string.put "inference") ++
    [4] ++ encodeData (Codec.string.put "literal")

def rawSuffix : List Alphabet :=
  encodeData (Codec.string.put "") ++ encodeData (.atom 0) ++ encodeData (putTy dataType)

/-- Full canonical storage retains the original displayed type as well as
the type annotation in the constant term. -/
def canonicalPrefix : List Alphabet := [4] ++ rawPrefix

def canonicalSuffix : List Alphabet := rawSuffix ++ encodeData (putTy dataType)

def rawTemplate : Template Alphabet := rawPrefix.map some ++ [none] ++ rawSuffix.map some

def canonicalTemplate : Template Alphabet :=
  canonicalPrefix.map some ++ [none] ++ canonicalSuffix.map some

theorem patternWire_tokens (pattern : Pattern) :
    patternWire pattern = encodeData ((Codec.list Codec.string).put
      (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern)) := rfl

theorem literalTerm_wire (value : Mettapedia.Logic.HOL.Embedding.InferenceRules.Data) :
    termWire (literalTerm value) = rawPrefix ++ patternWire value.val ++ rawSuffix := by
  simp only [termWire, literalTerm, putTerm, putConst, putConstProvenance,
    nameCodec, Codec.mapped, Codec.prod, functionName, Codec.list,
    Codec.putList, encodeData_pair, patternWire, Binary.encodeWith, patternCodec,
    rawPrefix, rawSuffix, List.append_assoc, List.cons_append, List.nil_append]

theorem renderedArgument_term (pattern : Pattern) :
    (renderedArgument pattern).term = dataTerm pattern := by
  change ReverseTranslation.reverseTerm ReverseTranslation.Naming.empty (term (encode pattern)) = _
  rw [ReverseTranslation.reverseTerm_eq_reverseTermOpen, render_encode]

theorem renderedArgument_ty (pattern : Pattern) :
    (renderedArgument pattern).ty = dataType := rfl

theorem opaque_term (pattern : Pattern) (literalCase : isOpaque pattern = true)
    (valid : argumentValidAt 0 pattern = true) :
    (renderedArgument pattern).term = literalTerm ⟨pattern, valid⟩ := by
  rw [renderedArgument_term]
  cases pattern <;> simp_all only [isOpaque, Bool.false_eq_true, dataTerm,
    Mettapedia.Logic.HOL.Embedding.InferenceRules.Data.opaque, dif_pos]

theorem raw_wire (pattern : Pattern) (literalCase : isOpaque pattern = true)
    (valid : argumentValidAt 0 pattern = true) :
    termWire (renderedArgument pattern).term = rawPrefix ++ patternWire pattern ++ rawSuffix := by
  rw [opaque_term pattern literalCase valid, literalTerm_wire]

theorem canonical_wire (pattern : Pattern) (literalCase : isOpaque pattern = true)
    (valid : argumentValidAt 0 pattern = true) :
    argumentWire pattern = canonicalPrefix ++ patternWire pattern ++ canonicalSuffix := by
  change encodeData (.pair (putTerm (renderedArgument pattern).term)
    (putTy (renderedArgument pattern).ty)) = _
  rw [encodeData_pair, renderedArgument_ty]
  change 4 :: (termWire (renderedArgument pattern).term ++ encodeData (putTy dataType)) = _
  rw [raw_wire pattern literalCase valid]
  simp only [canonicalPrefix, canonicalSuffix, List.append_assoc, List.cons_append, List.nil_append]

theorem rawTemplate_exact (pattern : Pattern) (literalCase : isOpaque pattern = true)
    (valid : argumentValidAt 0 pattern = true) :
    instantiate rawTemplate (patternWire pattern) = termWire (renderedArgument pattern).term := by
  rw [raw_wire pattern literalCase valid]
  simp [rawTemplate]

theorem canonicalTemplate_exact (pattern : Pattern) (literalCase : isOpaque pattern = true)
    (valid : argumentValidAt 0 pattern = true) :
    instantiate canonicalTemplate (patternWire pattern) = argumentWire pattern := by
  rw [canonical_wire pattern literalCase valid]
  simp [canonicalTemplate]

/-- The actual finite stack machine emits the complete raw term word. -/
def rawOutputs (pattern : Pattern) (literalCase : isOpaque pattern = true)
    (valid : argumentValidAt 0 pattern = true) :
    TM2OutputsInTime (machine rawTemplate) (patternWire pattern)
      (some (termWire (renderedArgument pattern).term))
      (4 * (rawTemplate.length + 1) * ((patternWire pattern).length + 1)) := by
  rw [← rawTemplate_exact pattern literalCase valid]
  exact Mettapedia.Computability.WordTemplateMachine.outputs rawTemplate (patternWire pattern)

/-- Canonical output includes the retained type and its decoder validation.
The clock charges the actual complete source word copied by the machine. -/
def canonicalOutputs (pattern : Pattern) (literalCase : isOpaque pattern = true)
    (valid : argumentValidAt 0 pattern = true) :
    TM2OutputsInTime (machine canonicalTemplate) (patternWire pattern)
      (some (argumentWire pattern))
      (4 * (canonicalTemplate.length + 1) * ((patternWire pattern).length + 1)) := by
  rw [← canonicalTemplate_exact pattern literalCase valid]
  exact Mettapedia.Computability.WordTemplateMachine.outputs canonicalTemplate (patternWire pattern)

theorem canonical_length (pattern : Pattern) (literalCase : isOpaque pattern = true)
    (valid : argumentValidAt 0 pattern = true) :
    (argumentWire pattern).length = canonicalPrefix.length +
      (patternWire pattern).length + canonicalSuffix.length := by
  rw [canonical_wire pattern literalCase valid, List.length_append, List.length_append]

theorem canonical_decode (pattern : Pattern) (literalCase : isOpaque pattern = true)
    (valid : argumentValidAt 0 pattern = true) :
    decodeWith canonicalCodec (instantiate canonicalTemplate (patternWire pattern)) =
      some (renderedArgument pattern) := by
  rw [canonicalTemplate_exact pattern literalCase valid]
  exact decodeWith_encodeWith canonicalCodec (renderedArgument pattern)

/-- Actual polynomial-time rendering on the source's admitted opaque
argument fragment. The predicate supplies source admission, while execution
uses only the original encoded pattern word. -/
noncomputable def realization :
    TM2ComputableInPolyTime
      (fun value : {pattern : Pattern // isOpaque pattern = true ∧ argumentValidAt 0 pattern = true} =>
        patternWire value.val)
      (encodeWith canonicalCodec)
      (fun value => renderedArgument value.val) where
  tm := machine canonicalTemplate
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := C (4 * (canonicalTemplate.length + 1)) * (X + C 1)
  outputsFun value := by
    change TM2OutputsInTime (machine canonicalTemplate) ((patternWire value.val).map id)
      (some ((argumentWire value.val).map id)) _
    simp only [List.map_id_fun]
    simpa only [id_eq, Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_X] using canonicalOutputs value.val value.property.1 value.property.2

namespace Controls

theorem binder_retained :
    decodeWith canonicalCodec
      (instantiate canonicalTemplate (patternWire (.lambda none (.bvar 0)))) =
      some (renderedArgument (.lambda none (.bvar 0))) :=
  canonical_decode _ rfl (by decide)

theorem escaping_binder_refused : argumentValidAt 0 (.lambda none (.bvar 1)) = false := by decide

theorem constructor_separate (name : String) (arguments : List Pattern) :
    isOpaque (.apply name arguments) = false := rfl

theorem metadata_refused (body : Pattern) (name : String) :
    argumentValidAt 0 (.lambda (some name) body) = false := by
  simp [argumentValidAt, Pattern.hasCanonicalBinderMetadata]

end Controls

namespace Nullary

/-- A nullary constructor's source token list, retained by the original codec. -/
def tokens (name : String) : List String := ["a", name, "z"]

def rawPrefix : List Alphabet :=
  [4] ++ encodeData (.atom 0) ++ [4, 4, 4] ++
    encodeData ((Codec.list Codec.string).put ["inference", "constructor"])

def rawSuffix : List Alphabet := encodeData (.atom 0) ++ encodeData (putTy dataType)

def canonicalPrefix : List Alphabet := [4] ++ rawPrefix

def canonicalSuffix : List Alphabet := rawSuffix ++ encodeData (putTy dataType)

/-- Only the original independently stored name field is selected. -/
def template : Indexed.Template Alphabet 3 :=
  canonicalPrefix.map Sum.inl ++ [.inr ⟨1, by decide⟩] ++ canonicalSuffix.map Sum.inl

def words (name : String) (index : Fin 3) : List Alphabet :=
  encodeWith Codec.string (if index.val = 0 then "a" else if index.val = 1 then name else "z")

theorem source_wire (name : String) :
    patternWire (.apply name []) = encodeWith (Codec.list Codec.string) (tokens name) := rfl

theorem framed_words (name : String) :
    Indexed.argumentWire (words name) =
      Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming.framedArguments Codec.string (tokens name) := rfl

theorem constructor_term (name : String) :
    (renderedArgument (.apply name [])).term = constructorTerm name 0 := by
  rw [renderedArgument_term]
  simp only [dataTerm, List.length_nil, List.map_nil, applyTerms, List.foldl_nil]

theorem canonical_wire (name : String) :
    argumentWire (.apply name []) =
      canonicalPrefix ++ encodeWith Codec.string name ++ canonicalSuffix := by
  change encodeData (.pair (putTerm (renderedArgument (.apply name [])).term)
    (putTy (renderedArgument (.apply name [])).ty)) = _
  rw [constructor_term, renderedArgument_ty]
  simp only [constructorTerm, dataArrow, putTerm, putConst, putConstProvenance,
    nameCodec, Codec.mapped, Codec.prod, functionName, natComponents,
    Mettapedia.OSLF.MeTTaIL.PatternTokens.bits, Nat.digits_zero, List.map_nil,
    List.append_nil, encodeData_pair, canonicalPrefix, canonicalSuffix,
    rawPrefix, rawSuffix, Binary.encodeWith, List.append_assoc,
    List.cons_append, List.nil_append]

theorem template_exact (name : String) :
    Indexed.instantiate template (words name) = argumentWire (.apply name []) := by
  rw [canonical_wire]
  simp only [template, Indexed.instantiate_append, Indexed.instantiate_hole,
    Indexed.instantiate_literals, Indexed.instantiate_nil, List.append_nil]
  rfl

theorem framed_exact (name : String) :
    (Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming.Execution.frameAtArity
      Codec.string 3 (tokens name)).map (Indexed.instantiateWire template) =
      some (argumentWire (.apply name [])) := by
  rw [Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming.Execution.frameAtArity,
    if_pos (show (tokens name).length = 3 from rfl), Option.map_some,
    ← framed_words, Indexed.instantiateWire_argumentWire, template_exact]

/-- The source codec is parsed before the indexed copier runs. Its explicit
success tag distinguishes a rendered value from refused input. -/
noncomputable def outputs (name : String) :
    TM2OutputsInTime
      (Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming.Execution.framedMachine 3 template)
      (patternWire (.apply name []))
      (some (Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming.Execution.resultWire
        (some (argumentWire (.apply name [])))))
      ((4 * (template.length + 2) + 10) * (patternWire (.apply name [])).length +
        4 * (template.length + 2) + 12) := by
  rw [source_wire]
  have result := Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming.Execution.framedOutputs
    Codec.string 3 template (tokens name)
  rw [framed_exact] at result
  exact result

set_option maxRecDepth 4096 in
/-- Every authored constructor name is retained with the original type,
namespace and undefined provenance, including its complete UTF-8 payload. -/
noncomputable def realization :
    TM2ComputableInPolyTime (fun name : String => patternWire (.apply name []))
      (fun value : CanonicalTerm =>
        Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming.Execution.resultWire
          (some (encodeWith canonicalCodec value)))
      (fun name => renderedArgument (.apply name [])) where
  tm := Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming.Execution.framedMachine 3 template
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := C (4 * (template.length + 2) + 10) * X + C (4 * (template.length + 2) + 12)
  outputsFun name := by
    change TM2OutputsInTime
      (Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming.Execution.framedMachine 3 template)
      ((patternWire (.apply name [])).map id)
      (some ((Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming.Execution.resultWire
        (some (argumentWire (.apply name [])))).map id)) _
    simp only [List.map_id_fun]
    simpa only [id_eq, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Nat.add_assoc] using outputs name

end Nullary

namespace Arity

/-- Original namespace digits are stored as independently framed UTF-8
strings; the binary terminator becomes the original list terminator. -/
def images (symbol : Alphabet) : List Alphabet :=
  if symbol.val = 0 then 4 :: encodeWith Codec.string "0"
  else if symbol.val = 1 then 4 :: encodeWith Codec.string "1"
  else if symbol.val = 2 then encodeData (.atom 0) else []

private theorem digits_exact (digits : List Nat) :
    ((digits.map fun digit => if digit = 0 then (0 : Alphabet) else 1) ++ [2]).flatMap images =
      encodeWith (Codec.list Codec.string)
        (digits.map fun digit => if digit = 0 then "0" else "1") := by
  rw [Binary.encodeWith_list]
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
  change _ ++ encodeData (.atom 0) = _ ++ encodeData (.atom 0)
  congr 1
  simp only [List.flatMap_map]
  apply congrArg (fun function : Nat → List Alphabet => digits.flatMap function)
  funext digit
  by_cases zero : digit = 0 <;> simp [zero, images]

theorem natural_exact (arity : Nat) :
    (Binary.natural arity).flatMap images =
      encodeWith (Codec.list Codec.string) (natComponents arity) := by
  exact digits_exact (Nat.digits 2 arity)

/-- The actual transducer realizes the original arity namespace. Its clock
depends on binary input length, not on the represented natural number. -/
def outputs (arity : Nat) :
    TM2OutputsInTime (Mettapedia.Computability.WordHomomorphismMachine.machine images)
      (Binary.natural arity)
      (some (encodeWith (Codec.list Codec.string) (natComponents arity)))
      (2 * (Binary.natural arity).length +
        2 * (encodeWith (Codec.list Codec.string) (natComponents arity)).length + 2) := by
  have result := Mettapedia.Computability.WordHomomorphismMachine.outputs images (Binary.natural arity)
  rw [natural_exact] at result
  exact result

noncomputable def realization :
    TM2ComputableInPolyTime Binary.natural (encodeWith (Codec.list Codec.string)) natComponents where
  tm := Mettapedia.Computability.WordHomomorphismMachine.machine images
  inputAlphabet := Equiv.refl Alphabet
  outputAlphabet := Equiv.refl Alphabet
  time := (Mettapedia.Computability.WordHomomorphismMachine.realization images).time
  outputsFun arity := by
    have result := (Mettapedia.Computability.WordHomomorphismMachine.realization images).outputsFun
      (Binary.natural arity)
    change TM2OutputsInTime (Mettapedia.Computability.WordHomomorphismMachine.machine images)
      ((Binary.natural arity).map id)
      (some (((Binary.natural arity).flatMap images).map id)) _ at result
    rw [natural_exact] at result
    exact result

def namespacePrefix : List Alphabet :=
  [4] ++ encodeWith Codec.string "inference" ++ [4] ++ encodeWith Codec.string "constructor"

/-- These are the complete original name fields used by every constructor. -/
theorem constructor_name_wire (name : String) (arity : Nat) :
    encodeWith nameCodec (functionName (.constructor name arity)) =
      [4] ++ namespacePrefix ++
        encodeWith (Codec.list Codec.string) (natComponents arity) ++ encodeWith Codec.string name := by
  simp only [Binary.encodeWith, nameCodec, Codec.mapped, Codec.prod,
    functionName, Codec.list, Codec.putList, List.cons_append, List.nil_append,
    encodeData_pair, namespacePrefix, List.append_assoc]

end Arity

namespace Constructor

def applicationPrefix : List Alphabet := [4] ++ encodeData (.atom 3) ++ [4]

theorem application_wire (function argument : DBTerm) :
    termWire (.app function argument) =
      applicationPrefix ++ termWire function ++ termWire argument := by
  simp only [termWire, putTerm, encodeData_pair, applicationPrefix,
    List.cons_append, List.nil_append, List.append_assoc]

/-- The original left-associated application spine is emitted in authored
child order, retaining each occurrence separately. -/
theorem applyTerms_wire (head : DBTerm) (arguments : List DBTerm) :
    termWire (applyTerms head arguments) =
      (List.replicate arguments.length applicationPrefix).flatten ++
        termWire head ++ arguments.flatMap termWire := by
  induction arguments generalizing head with
  | nil => simp [applyTerms]
  | cons argument arguments ih =>
    change termWire (applyTerms (.app head argument) arguments) = _
    rw [ih, application_wire]
    simp only [List.length_cons, List.replicate_succ', List.flatten_append,
      List.flatten_cons, List.flatten_nil, List.append_nil,
      List.flatMap_cons, List.append_assoc]

theorem constructor_term (name : String) (arguments : List Pattern) :
    (renderedArgument (.apply name arguments)).term =
      applyTerms (constructorTerm name arguments.length)
        (arguments.map fun argument => (renderedArgument argument).term) := by
  rw [renderedArgument_term]
  simp only [dataTerm]
  congr 1
  exact List.map_congr_left fun argument _ => (renderedArgument_term argument).symm

/-- This is the existing full source token stream, with no alternative
tree encoding or altered constructor semantics. -/
theorem source_wire (name : String) (arguments : List Pattern) :
    patternWire (.apply name arguments) = encodeWith (Codec.list Codec.string)
      ("a" :: name :: Mettapedia.OSLF.MeTTaIL.PatternTokens.writeList arguments []) := rfl

theorem raw_wire (name : String) (arguments : List Pattern) :
    termWire (renderedArgument (.apply name arguments)).term =
      (List.replicate arguments.length applicationPrefix).flatten ++
        termWire (constructorTerm name arguments.length) ++
        arguments.flatMap (fun argument => termWire (renderedArgument argument).term) := by
  rw [constructor_term, applyTerms_wire, List.length_map]
  simp only [List.flatMap_map]

def arrowPrefix : List Alphabet :=
  [4] ++ encodeData (.atom 1) ++ [4] ++ encodeData (putTypeOp TypeOp.function) ++
    [4] ++ encodeData (putTy dataType) ++ [4]

def arrowSuffix : List Alphabet := encodeData (.atom 0)

theorem arrow_wire (codomain : Ty) :
    encodeData (putTy (.function dataType codomain)) =
      arrowPrefix ++ encodeData (putTy codomain) ++ arrowSuffix := by
  simp only [Ty.function, putTy, putTys, encodeData_pair, arrowPrefix, arrowSuffix,
    List.cons_append, List.nil_append, List.append_assoc]

/-- Full type storage grows with the physical argument count. Binary arity
storage alone would not account for these retained function-type fields. -/
theorem dataArrow_wire (arity : Nat) :
    encodeData (putTy (dataArrow arity)) =
      (List.replicate arity arrowPrefix).flatten ++ encodeData (putTy dataType) ++
        (List.replicate arity arrowSuffix).flatten := by
  induction arity with
  | zero => simp [dataArrow]
  | succ arity ih =>
    rw [dataArrow, arrow_wire, ih]
    rw [List.replicate_succ (a := arrowPrefix), List.replicate_succ' (a := arrowSuffix)]
    simp only [List.flatten_cons, List.flatten_append, List.flatten_nil,
      List.append_nil, List.append_assoc]

theorem dataArrow_length (arity : Nat) :
    (encodeWith tyCodec (dataArrow arity)).length =
      arity * (arrowPrefix.length + arrowSuffix.length) +
        (encodeData (putTy dataType)).length := by
  rw [show encodeWith tyCodec (dataArrow arity) =
    Wrapping.wrapped arrowPrefix (encodeData (putTy dataType)) arrowSuffix arity from dataArrow_wire arity]
  exact Wrapping.wrapped_length _ _ _ _

/-- Every immediate child has an authored physical list marker. Thus the
full retained constructor type is bounded by the original complete input. -/
theorem child_count_le_wire (name : String) (arguments : List Pattern) :
    arguments.length ≤ (patternWire (.apply name arguments)).length := by
  have tokenCount : arguments.length ≤
      (Mettapedia.OSLF.MeTTaIL.PatternTokens.writeList arguments []).length := by
    induction arguments with
    | nil => simp [Mettapedia.OSLF.MeTTaIL.PatternTokens.writeList]
    | cons argument arguments ih =>
        simp only [Mettapedia.OSLF.MeTTaIL.PatternTokens.writeList, List.length_cons]
        rw [Mettapedia.OSLF.MeTTaIL.PatternTokens.write_length]
        omega
  rw [source_wire, Mettapedia.GSLT.LanguageDef.CertificateArgumentFraming.encoded_list_length]
  simp only [List.length_cons]
  omega

theorem dataArrow_clock_le_source (name : String) (arguments : List Pattern) :
    arguments.length * (arrowPrefix.length + arrowSuffix.length + 4) +
      (encodeData (putTy dataType)).length +
      (encodeWith tyCodec (dataArrow arguments.length)).length + 4 ≤
    2 * (arrowPrefix.length + arrowSuffix.length + 2) *
      (patternWire (.apply name arguments)).length +
      2 * (encodeData (putTy dataType)).length + 4 := by
  rw [dataArrow_length]
  have bound := child_count_le_wire name arguments
  nlinarith

/-- A discovered child supplies a physical marker. The executed wrapper
retains the full original type, with one arrow on both sides per marker. -/
def dataArrowOutputs (arity : Nat) :
    TM2OutputsInTime
      (Wrapping.machine arrowPrefix (encodeData (putTy dataType)) arrowSuffix)
      (List.replicate arity ()) (some (encodeWith tyCodec (dataArrow arity)))
      (arity * (arrowPrefix.length + arrowSuffix.length + 4) +
        (encodeData (putTy dataType)).length + (encodeWith tyCodec (dataArrow arity)).length + 4) := by
  have result := Wrapping.outputs arrowPrefix (encodeData (putTy dataType)) arrowSuffix arity
  have same : Wrapping.wrapped arrowPrefix (encodeData (putTy dataType)) arrowSuffix arity =
      encodeWith tyCodec (dataArrow arity) := (dataArrow_wire arity).symm
  rw [same] at result
  exact result

/-- This cost is polynomial in the physically enumerated children. The
binary arity field is converted separately by `Arity.realization`. -/
noncomputable def dataArrowRealization :
    TM2ComputableInPolyTime (fun arity : Nat => List.replicate arity ())
      (encodeWith tyCodec) dataArrow where
  tm := Wrapping.machine arrowPrefix (encodeData (putTy dataType)) arrowSuffix
  inputAlphabet := Equiv.refl Unit
  outputAlphabet := Equiv.refl Alphabet
  time := (Wrapping.computable arrowPrefix (encodeData (putTy dataType)) arrowSuffix).time
  outputsFun arity := by
    have result := (Wrapping.computable arrowPrefix (encodeData (putTy dataType)) arrowSuffix).outputsFun arity
    change TM2OutputsInTime
      (Wrapping.machine arrowPrefix (encodeData (putTy dataType)) arrowSuffix)
      ((List.replicate arity ()).map id)
      (some ((Wrapping.wrapped arrowPrefix (encodeData (putTy dataType)) arrowSuffix arity).map id)) _ at result
    rw [show Wrapping.wrapped arrowPrefix (encodeData (putTy dataType)) arrowSuffix arity =
      encodeWith tyCodec (dataArrow arity) from (dataArrow_wire arity).symm] at result
    exact result


namespace Head

/-- Three original fields complete the constructor head: binary namespace
components, the authored UTF-8 name, and its complete curried type. -/
def opening : List Alphabet :=
  [4] ++ encodeData (.atom 0) ++ [4, 4, 4] ++ Arity.namespacePrefix

def template : Indexed.Template Alphabet 3 :=
  opening.map Sum.inl ++ [.inr ⟨0, by decide⟩, .inr ⟨1, by decide⟩] ++
    (encodeData (.atom 0)).map Sum.inl ++ [.inr ⟨2, by decide⟩]

def words (name : String) (arity : Nat) : Fin 3 → List Alphabet
  | ⟨0, _⟩ => encodeWith (Codec.list Codec.string) (natComponents arity)
  | ⟨1, _⟩ => encodeWith Codec.string name
  | ⟨2, _⟩ => encodeWith tyCodec (dataArrow arity)

theorem constructor_wire (name : String) (arity : Nat) :
    termWire (constructorTerm name arity) =
      opening ++ encodeWith (Codec.list Codec.string) (natComponents arity) ++
        encodeWith Codec.string name ++ encodeData (.atom 0) ++ encodeWith tyCodec (dataArrow arity) := by
  simp only [termWire, constructorTerm, putTerm, putConst, putConstProvenance,
    nameCodec, Codec.mapped, Codec.prod, functionName, Codec.list, Codec.putList,
    List.cons_append, List.nil_append, encodeData_pair, opening, Arity.namespacePrefix,
    Binary.encodeWith, tyCodec, List.append_assoc]

theorem template_exact (name : String) (arity : Nat) :
    Indexed.instantiate template (words name arity) = termWire (constructorTerm name arity) := by
  rw [constructor_wire]
  simp only [template, Indexed.instantiate_append, Indexed.instantiate_literals,
    Indexed.instantiate_hole, Indexed.instantiate_nil,
    List.append_nil, List.append_assoc, words]

/-- Executed constructor-head copying keeps every original name, arity,
type and undefined-provenance byte. Its inputs are the actual field words
produced by the name, binary-count and arrow-type operations. -/
def outputs (name : String) (arity : Nat) :
    TM2OutputsInTime (Indexed.machine template) (Indexed.argumentWire (words name arity))
      (some (termWire (constructorTerm name arity)))
      (4 * (template.length + 1) * ((Indexed.argumentWire (words name arity)).length + 1)) := by
  have run := Indexed.outputs template (words name arity)
  rw [template_exact] at run
  exact run

end Head

namespace Spine
open Turing.TM2.Stmt

/-- Child words use the existing delimiter framing. A physical marker records
one child occurrence, independently of its term or of equality with another child. -/
inductive Stack where
  | input | head | children | openings | headMemo | result | markers
  deriving DecidableEq, Fintype
abbrev StackAlphabet : Stack → Type
  | .input => Option Alphabet
  | .markers => Unit
  | _ => Alphabet
inductive Phase where
  | scan | bodies | headScan | headReturn | openings
  deriving DecidableEq, Fintype
abbrev Control := Option (Option Alphabet)

def selected (state : Control) : Alphabet := state.join.getD 2

def pushOpen : List Alphabet → TM2.Stmt StackAlphabet Phase Control → TM2.Stmt StackAlphabet Phase Control
  | [], rest => rest
  | symbol :: symbols, rest => push .openings (fun _ => symbol) (pushOpen symbols rest)

/-- Assemble the original left-associated application spine. Every child byte
is transferred explicitly; constructor heads retain all original annotations. -/
def program : Phase → TM2.Stmt StackAlphabet Phase Control
  | .scan => pop .input (fun _ value => value)
      (branch Option.isSome
        (branch (fun state => state.join.isSome)
          (push .children selected (goto fun _ => .scan))
          (pushOpen applicationPrefix (push .markers (fun _ => ()) (goto fun _ => .scan))))
        (goto fun _ => .bodies))
  | .bodies => pop .children (fun _ value => value.map some)
      (branch Option.isSome (push .result selected (goto fun _ => .bodies))
        (goto fun _ => .headScan))
  | .headScan => pop .head (fun _ value => value.map some)
      (branch Option.isSome (push .headMemo selected (goto fun _ => .headScan))
        (goto fun _ => .headReturn))
  | .headReturn => pop .headMemo (fun _ value => value.map some)
      (branch Option.isSome (push .result selected (goto fun _ => .headReturn))
        (goto fun _ => .openings))
  | .openings => pop .openings (fun _ value => value.map some)
      (branch Option.isSome (push .result selected (goto fun _ => .openings))
        (load (fun _ => none) halt))

def machine : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .result
  Γ := StackAlphabet
  Γk₀Fin := by change Fintype (Option Alphabet); infer_instance
  Λ := Phase
  main := .scan
  σ := Control
  initialState := none
  m := program

abbrev Cfg := TM2.Cfg StackAlphabet Phase Control

def step : Cfg → Option Cfg := TM2.step program

theorem machine_step : machine.step = step := rfl

def config (phase : Option Phase) (state : Control) (input : List (Option Alphabet))
    (head children openings headMemo result : List Alphabet) (markers : List Unit) : Cfg where
  l := phase
  var := state
  stk key := match (show Stack from key) with
    | .input => input | .head => head | .children => children | .openings => openings
    | .headMemo => headMemo | .result => result | .markers => markers

theorem pushOpen_apply (opening : List Alphabet) (statement : TM2.Stmt StackAlphabet Phase Control)
    (phase : Option Phase) (state : Control) (input : List (Option Alphabet))
    (head children openings headMemo result : List Alphabet) (markers : List Unit) :
    TM2.stepAux (pushOpen opening statement) state
      (config phase state input head children openings headMemo result markers).stk =
    TM2.stepAux statement state
      (config phase state input head children (opening.reverse ++ openings) headMemo result markers).stk := by
  induction opening generalizing statement openings with
  | nil => simp only [pushOpen, List.reverse_nil, List.nil_append]
  | cons symbol symbols ih =>
      simp only [pushOpen, TM2.stepAux]
      have stackEq : Function.update
          (config phase state input head children openings headMemo result markers).stk
          .openings (symbol :: openings) =
          (config phase state input head children (symbol :: openings) headMemo result markers).stk := by
        funext key
        cases key <;> simp [config, Function.update]
      change TM2.stepAux (pushOpen symbols statement) state
        (Function.update (config phase state input head children openings headMemo result markers).stk
          .openings (symbol :: openings)) = _
      rw [stackEq, ih]
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

theorem scan_symbol (state : Control) (symbol : Alphabet) (input : List (Option Alphabet))
    (head children openings headMemo result : List Alphabet) (markers : List Unit) :
    step (config (some .scan) state (some symbol :: input) head children openings headMemo result markers) =
      some (config (some .scan) (some (some symbol)) input head (symbol :: children)
        openings headMemo result markers) := by
  simp [step, program, config, selected, TM2.step, TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem scan_separator (state : Control) (input : List (Option Alphabet))
    (head children openings headMemo result : List Alphabet) (markers : List Unit) :
    step (config (some .scan) state (none :: input) head children openings headMemo result markers) =
      some (config (some .scan) (some none) input head children
        (applicationPrefix.reverse ++ openings) headMemo result (() :: markers)) := by
  change some (TM2.stepAux (pushOpen applicationPrefix
      (push .markers (fun _ => ()) (goto fun _ => .scan))) (some none)
      (Function.update
        (config (some .scan) state (none :: input) head children openings headMemo result markers).stk
        .input input)) = _
  have inputEq : Function.update
      (config (some .scan) state (none :: input) head children openings headMemo result markers).stk
      .input input = (config none (some none) input head children openings headMemo result markers).stk := by
    funext key
    cases key <;> simp [config, Function.update]
  rw [inputEq, pushOpen_apply]
  simp only [TM2.stepAux]
  congr 1
  congr 1
  funext key
  cases key <;> simp [config, Function.update]

theorem scan_nil (state : Control) (head children openings headMemo result : List Alphabet)
    (markers : List Unit) :
    step (config (some .scan) state [] head children openings headMemo result markers) =
      some (config (some .bodies) none [] head children openings headMemo result markers) := by
  simp [step, program, config, TM2.step, TM2.stepAux]

def wordState : List Alphabet → Control → Control
  | [], state => state
  | symbol :: symbols, _ => wordState symbols (some (some symbol))

/-- Each payload byte enters the same physical child accumulation stack. -/
noncomputable def wordRun (state : Control) (word : List Alphabet) (input : List (Option Alphabet))
    (head children openings headMemo result : List Alphabet) (markers : List Unit) :
    EvalsToInTime step
      (config (some .scan) state (word.map some ++ input) head children openings headMemo result markers)
      (some (config (some .scan) (wordState word state)
        input head (word.reverse ++ children) openings headMemo result markers)) word.length := by
  induction word generalizing state children with
  | nil =>
      simpa only [wordState, List.map_nil, List.nil_append, List.reverse_nil, List.length_nil] using
        EvalsToInTime.refl step (config (some .scan) state input head children openings headMemo result markers)
  | cons symbol symbols ih =>
      have first := Mettapedia.Computability.StackMachineComposition.oneStep
        (scan_symbol state symbol (symbols.map some ++ input) head children openings headMemo result markers)
      have rest := ih (some (some symbol)) (symbol :: children)
      simpa only [wordState, List.map_cons, List.cons_append, List.reverse_cons, List.singleton_append,
        List.append_assoc, List.nil_append, List.length_cons] using EvalsToInTime.trans _ _ _ _ _ _ first rest

noncomputable def vectorRun (state : Control) (words : List (List Alphabet)) (input : List (Option Alphabet))
    (head children openings headMemo result : List Alphabet) (markers : List Unit) :
    EvalsToInTime step
      (config (some .scan) state (Indexed.frame words ++ input) head children openings headMemo result markers)
      (some (config (some .scan) (if words.isEmpty then state else some none) input head
        (words.flatten.reverse ++ children)
        ((List.replicate words.length applicationPrefix).flatten.reverse ++ openings)
        headMemo result (List.replicate words.length () ++ markers))) (Indexed.frame words).length := by
  induction words generalizing state children openings markers with
  | nil =>
      simpa [Indexed.frame] using EvalsToInTime.refl step
        (config (some .scan) state input head children openings headMemo result markers)
  | cons word words ih =>
      have first := wordRun state word (none :: (Indexed.frame words ++ input))
        head children openings headMemo result markers
      have separator := Mettapedia.Computability.StackMachineComposition.oneStep
        (scan_separator (wordState word state) (Indexed.frame words ++ input)
          head (word.reverse ++ children) openings headMemo result markers)
      have rest := ih (some none) (word.reverse ++ children)
        (applicationPrefix.reverse ++ openings) (() :: markers)
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first separator
      have joined := EvalsToInTime.trans _ _ _ _ _ _ joined rest
      have clock : (Indexed.frame words).length + (1 + word.length) =
          (Indexed.frame (word :: words)).length := by
        simp only [Indexed.frame, List.flatMap_cons, List.length_append, List.length_map,
          List.length_singleton]
        omega
      rw [clock] at joined
      simpa only [Indexed.frame, List.flatMap_cons, List.cons_append, List.append_assoc,
        List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, ite_self, List.flatten_cons,
        List.reverse_append, List.length_cons, List.replicate_succ' (n := words.length) (a := ()),
        List.replicate_succ, List.flatten_append,
        List.flatten_cons, List.flatten_nil, List.append_nil, List.singleton_append, List.nil_append]
        using joined

local macro "spine_step" : tactic => `(tactic| (
  simp [step, program, config, selected, TM2.step, TM2.stepAux]
  all_goals funext key
  all_goals cases key <;> simp [Function.update]))

theorem bodies_cons (state : Control) (symbol : Alphabet)
    (head children openings headMemo result : List Alphabet) (markers : List Unit) :
    step (config (some .bodies) state [] head (symbol :: children) openings headMemo result markers) =
      some (config (some .bodies) (some (some symbol)) [] head children openings headMemo
        (symbol :: result) markers) := by spine_step

theorem bodies_nil (state : Control) (head openings headMemo result : List Alphabet) (markers : List Unit) :
    step (config (some .bodies) state [] head [] openings headMemo result markers) =
      some (config (some .headScan) none [] head [] openings headMemo result markers) := by spine_step

theorem headScan_cons (state : Control) (symbol : Alphabet)
    (head openings headMemo result : List Alphabet) (markers : List Unit) :
    step (config (some .headScan) state [] (symbol :: head) [] openings headMemo result markers) =
      some (config (some .headScan) (some (some symbol)) [] head [] openings (symbol :: headMemo)
        result markers) := by spine_step

theorem headScan_nil (state : Control) (openings headMemo result : List Alphabet) (markers : List Unit) :
    step (config (some .headScan) state [] [] [] openings headMemo result markers) =
      some (config (some .headReturn) none [] [] [] openings headMemo result markers) := by spine_step

theorem headReturn_cons (state : Control) (symbol : Alphabet)
    (openings headMemo result : List Alphabet) (markers : List Unit) :
    step (config (some .headReturn) state [] [] [] openings (symbol :: headMemo) result markers) =
      some (config (some .headReturn) (some (some symbol)) [] [] [] openings headMemo
        (symbol :: result) markers) := by spine_step

theorem headReturn_nil (state : Control) (openings result : List Alphabet) (markers : List Unit) :
    step (config (some .headReturn) state [] [] [] openings [] result markers) =
      some (config (some .openings) none [] [] [] openings [] result markers) := by spine_step

theorem openings_cons (state : Control) (symbol : Alphabet)
    (openings result : List Alphabet) (markers : List Unit) :
    step (config (some .openings) state [] [] [] (symbol :: openings) [] result markers) =
      some (config (some .openings) (some (some symbol)) [] [] [] openings []
        (symbol :: result) markers) := by spine_step

theorem openings_nil (state : Control) (result : List Alphabet) (markers : List Unit) :
    step (config (some .openings) state [] [] [] [] [] result markers) =
      some (config none none [] [] [] [] [] result markers) := by spine_step

noncomputable def bodiesRun (state : Control)
    (head children openings headMemo result : List Alphabet) (markers : List Unit) :
    EvalsToInTime step (config (some .bodies) state [] head children openings headMemo result markers)
      (some (config (some .headScan) none [] head [] openings headMemo (children.reverse ++ result) markers))
      (children.length + 1) := by
  induction children generalizing state result with
  | nil => simpa using Mettapedia.Computability.StackMachineComposition.oneStep (bodies_nil state head openings headMemo result markers)
  | cons symbol children ih =>
      have first := Mettapedia.Computability.StackMachineComposition.oneStep (bodies_cons state symbol head children openings headMemo result markers)
      have rest := ih (some (some symbol)) (symbol :: result)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first rest

noncomputable def headScanRun (state : Control)
    (head openings headMemo result : List Alphabet) (markers : List Unit) :
    EvalsToInTime step (config (some .headScan) state [] head [] openings headMemo result markers)
      (some (config (some .headReturn) none [] [] [] openings (head.reverse ++ headMemo) result markers))
      (head.length + 1) := by
  induction head generalizing state headMemo with
  | nil => simpa using Mettapedia.Computability.StackMachineComposition.oneStep (headScan_nil state openings headMemo result markers)
  | cons symbol head ih =>
      have first := Mettapedia.Computability.StackMachineComposition.oneStep (headScan_cons state symbol head openings headMemo result markers)
      have rest := ih (some (some symbol)) (symbol :: headMemo)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first rest

noncomputable def headReturnRun (state : Control)
    (openings headMemo result : List Alphabet) (markers : List Unit) :
    EvalsToInTime step (config (some .headReturn) state [] [] [] openings headMemo result markers)
      (some (config (some .openings) none [] [] [] openings [] (headMemo.reverse ++ result) markers))
      (headMemo.length + 1) := by
  induction headMemo generalizing state result with
  | nil => simpa using Mettapedia.Computability.StackMachineComposition.oneStep (headReturn_nil state openings result markers)
  | cons symbol headMemo ih =>
      have first := Mettapedia.Computability.StackMachineComposition.oneStep (headReturn_cons state symbol openings headMemo result markers)
      have rest := ih (some (some symbol)) (symbol :: result)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first rest

noncomputable def openingsRun (state : Control)
    (openings result : List Alphabet) (markers : List Unit) :
    EvalsToInTime step (config (some .openings) state [] [] [] openings [] result markers)
      (some (config none none [] [] [] [] [] (openings.reverse ++ result) markers))
      (openings.length + 1) := by
  induction openings generalizing state result with
  | nil => simpa using Mettapedia.Computability.StackMachineComposition.oneStep (openings_nil state result markers)
  | cons symbol openings ih =>
      have first := Mettapedia.Computability.StackMachineComposition.oneStep (openings_cons state symbol openings result markers)
      have rest := ih (some (some symbol)) (symbol :: result)
      simpa [List.reverse_cons, List.append_assoc] using EvalsToInTime.trans _ _ _ _ _ _ first rest


/-- Caller supplies the original ordered head word and delimiter-framed child
words. The finite assembly program consumes each physical field once. -/
def startConfig (head : List Alphabet) (words : List (List Alphabet)) : Cfg :=
  config (some .scan) none (Indexed.frame words) head [] [] [] [] []

def output (head : List Alphabet) (words : List (List Alphabet)) : List Alphabet :=
  (List.replicate words.length applicationPrefix).flatten ++ head ++ words.flatten

def clock (head : List Alphabet) (words : List (List Alphabet)) : Nat :=
  (Indexed.frame words).length + words.flatten.length + 2 * head.length +
    (List.replicate words.length applicationPrefix).flatten.length + 5

/-- Actual execution assembles every original child word and retains a
physical occurrence marker for subsequent arity and constructor-type work. -/
noncomputable def assemblyRun (head : List Alphabet) (words : List (List Alphabet)) :
    EvalsToInTime step (startConfig head words)
      (some (config none none [] [] [] [] [] (output head words)
        (List.replicate words.length ()))) (clock head words) := by
  let openings := (List.replicate words.length applicationPrefix).flatten
  let markers := List.replicate words.length ()
  have scanned := vectorRun none words [] head [] [] [] [] []
  have exhausted := Mettapedia.Computability.StackMachineComposition.oneStep
    (scan_nil (if words.isEmpty then none else some none) head words.flatten.reverse
      openings.reverse [] [] markers)
  have bodies := bodiesRun none head words.flatten.reverse openings.reverse [] [] markers
  have headScan := headScanRun none head openings.reverse [] words.flatten markers
  have headReturn := headReturnRun none openings.reverse head.reverse words.flatten markers
  have finished := openingsRun none openings.reverse (head ++ words.flatten) markers
  simp only [List.append_nil] at scanned
  simp only [List.reverse_reverse, List.append_nil] at bodies
  simp only [List.append_nil] at headScan
  simp only [List.reverse_reverse] at headReturn finished
  have joined := EvalsToInTime.trans _ _ _ _ _ _ scanned exhausted
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined bodies
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined headScan
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined headReturn
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined finished
  change EvalsToInTime step (startConfig head words)
      (some (config none none [] [] [] [] [] (openings ++ (head ++ words.flatten)) markers))
      ((openings.reverse.length + 1) +
        ((head.reverse.length + 1) + ((head.length + 1) +
          ((words.flatten.reverse.length + 1) + (1 + (Indexed.frame words).length))))) at joined
  have timeEq :
      (openings.reverse.length + 1) +
        ((head.reverse.length + 1) + ((head.length + 1) +
          ((words.flatten.reverse.length + 1) + (1 + (Indexed.frame words).length)))) = clock head words := by
    simp only [List.length_reverse, clock, openings]
    omega
  rw [timeEq] at joined
  simpa only [output, openings, markers, List.append_assoc] using joined

/-- The emitted bytes are the complete original raw HOL term codec, including
all constructor annotations and the ordered children without deduplication. -/
noncomputable def termRun (head : DBTerm) (arguments : List DBTerm) :
    EvalsToInTime step (startConfig (termWire head) (arguments.map termWire))
      (some (config none none [] [] [] [] [] (termWire (applyTerms head arguments))
        (List.replicate arguments.length ()))) (clock (termWire head) (arguments.map termWire)) := by
  have run := assemblyRun (termWire head) (arguments.map termWire)
  have outputEq : output (termWire head) (arguments.map termWire) = termWire (applyTerms head arguments) := by
    rw [applyTerms_wire]
    simp only [output, List.length_map, List.flatMap, List.append_assoc]
  rw [outputEq, List.length_map] at run
  exact run

/-- Extract the original raw term from its complete canonical storage by
executing the existing pair-field selector, including the displayed type scan. -/
noncomputable def canonicalTermOutputs (value : CanonicalTerm) :=
  (Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.selectFirstCodec
    dbTermCodec tyCodec).outputsFun (value.term, value.ty)

theorem canonicalTerm_input (value : CanonicalTerm) :
    encodeWith canonicalCodec value =
      encodeWith (Codec.prod dbTermCodec tyCodec) (value.term, value.ty) := rfl

theorem canonicalTerm_output (value : CanonicalTerm) :
    Mettapedia.GSLT.LanguageDef.CertificateDataTraversal.ProductField.successEncoding
      dbTermCodec value.term = 1 :: termWire value.term := rfl


theorem prefix_length : applicationPrefix.length = 6 := rfl

theorem clock_le (head : List Alphabet) (words : List (List Alphabet)) :
    clock head words ≤ 8 * (head.length + (Indexed.frame words).length) + 5 := by
  have frames := Indexed.frame_length words
  have flattened := List.length_flatten (L := words)
  have openings : (List.replicate words.length applicationPrefix).flatten.length = words.length * 6 := by
    simp only [List.length_flatten, List.map_replicate, prefix_length, List.sum_replicate, smul_eq_mul]
  unfold clock
  rw [openings]
  omega

/-- The executed spine assembly has a linear clock in its original physical
head word and child framing; no term-size or represented-number shortcut is used. -/
theorem assembly_linear (head : List Alphabet) (words : List (List Alphabet)) :
    Nonempty (EvalsToInTime step (startConfig head words)
      (some (config none none [] [] [] [] [] (output head words)
        (List.replicate words.length ())))
      (8 * (head.length + (Indexed.frame words).length) + 5)) :=
  let run := assemblyRun head words
  ⟨⟨run.toEvalsTo, run.steps_le_m.trans (clock_le head words)⟩⟩

end Spine

end Constructor

namespace HookLiteral

open Mettapedia.GSLT.LanguageDef.PatternSpanExecution

/-- Complete opaque spans are consumed from the shared structural hooks.
The static projection retains each original field byte and list marker. -/
def template : Template Alphabet :=
  rawPrefix.map some ++ [none] ++ ([3,2] ++ rawSuffix).map some

def canonicalTemplate : Template Alphabet :=
  canonicalPrefix.map some ++ [none] ++ ([3,2] ++ canonicalSuffix).map some

def projectMachine : FinTM2 :=
  Mettapedia.Computability.WordHomomorphismMachine.machine Hooks.sourceImage

local instance : Fintype (projectMachine.Γ projectMachine.k₁) := by
  change Fintype Alphabet
  infer_instance
local instance : Inhabited (projectMachine.Γ projectMachine.k₁) := by
  change Inhabited Alphabet
  infer_instance

def machine : FinTM2 := Mettapedia.Computability.StackMachineComposition.machine
  projectMachine (Mettapedia.Computability.WordTemplateMachine.machine template) (Equiv.refl Alphabet)

def canonicalMachine : FinTM2 := Mettapedia.Computability.StackMachineComposition.machine
  projectMachine (Mettapedia.Computability.WordTemplateMachine.machine canonicalTemplate) (Equiv.refl Alphabet)

theorem projected_length (hooks : List Hooks.Symbol) :
    (Hooks.sourceBytes hooks).length ≤ hooks.length := by
  induction hooks with
  | nil => simp [Hooks.sourceBytes]
  | cons head hooks ih =>
      change (hooks.flatMap Hooks.sourceImage).length ≤ hooks.length at ih
      cases head <;> simp only [Hooks.sourceBytes, List.flatMap_cons, Hooks.sourceImage,
        List.length_append, List.length_nil, List.length_cons] <;> omega

theorem template_exact (pattern : Pattern) (hooks : List Hooks.Symbol)
    (traced : Hooks.Trace [.pattern] (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern) [] hooks)
    (literalCase : isOpaque pattern = true) (admitted : argumentValidAt 0 pattern = true) :
    instantiate template (Hooks.sourceBytes hooks) = termWire (renderedArgument pattern).term := by
  rw [raw_wire pattern literalCase admitted]
  have bytes := Hooks.Trace.pattern_sourceBytes pattern hooks traced
  change Hooks.sourceBytes hooks ++ [3,2] = patternWire pattern at bytes
  simp only [template, instantiate_append, instantiate_literals, instantiate_hole,
    instantiate_nil, List.append_nil]
  rw [← bytes]
  simp only [List.append_assoc]

theorem canonicalTemplate_exact (pattern : Pattern) (hooks : List Hooks.Symbol)
    (traced : Hooks.Trace [.pattern] (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern) [] hooks)
    (literalCase : isOpaque pattern = true) (admitted : argumentValidAt 0 pattern = true) :
    instantiate canonicalTemplate (Hooks.sourceBytes hooks) = argumentWire pattern := by
  rw [canonical_wire pattern literalCase admitted]
  have bytes := Hooks.Trace.pattern_sourceBytes pattern hooks traced
  change Hooks.sourceBytes hooks ++ [3,2] = patternWire pattern at bytes
  simp only [canonicalTemplate, instantiate_append, instantiate_literals, instantiate_hole,
    instantiate_nil, List.append_nil]
  rw [← bytes]
  simp only [List.append_assoc]

/-- Both actual machines and the physical word transfer are charged. -/
def outputs (pattern : Pattern) (hooks : List Hooks.Symbol)
    (traced : Hooks.Trace [.pattern] (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern) [] hooks)
    (literalCase : isOpaque pattern = true) (admitted : argumentValidAt 0 pattern = true) :
    TM2OutputsInTime machine hooks (some (termWire (renderedArgument pattern).term))
      ((4 * (template.length + 1) + 6) * (hooks.length + 1)) := by
  have projected := Mettapedia.Computability.WordHomomorphismMachine.outputs Hooks.sourceImage hooks
  have copied := Mettapedia.Computability.WordTemplateMachine.outputs template (Hooks.sourceBytes hooks)
  rw [template_exact pattern hooks traced literalCase admitted] at copied
  have copied' : TM2OutputsInTime (Mettapedia.Computability.WordTemplateMachine.machine template)
      ((Hooks.sourceBytes hooks).map (Equiv.refl Alphabet))
      (some (termWire (renderedArgument pattern).term))
      (4*(template.length+1)*((Hooks.sourceBytes hooks).length+1)) := by
    simpa only [Equiv.coe_refl, List.map_id] using copied
  have run := Mettapedia.Computability.StackMachineComposition.outputs projectMachine
    (Mettapedia.Computability.WordTemplateMachine.machine template) (Equiv.refl Alphabet)
    hooks (Hooks.sourceBytes hooks) (termWire (renderedArgument pattern).term) _ _ projected copied'
  have length := projected_length hooks
  refine ⟨run.toEvalsTo, run.steps_le_m.trans ?_⟩
  dsimp only [Hooks.sourceBytes] at length ⊢
  nlinarith

/-- Displayed and embedded types are both retained in the complete target
canonical codec, independently of the source admission judgment. -/
def canonicalOutputs (pattern : Pattern) (hooks : List Hooks.Symbol)
    (traced : Hooks.Trace [.pattern] (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern) [] hooks)
    (literalCase : isOpaque pattern = true) (admitted : argumentValidAt 0 pattern = true) :
    TM2OutputsInTime canonicalMachine hooks (some (argumentWire pattern))
      ((4 * (canonicalTemplate.length + 1) + 6) * (hooks.length + 1)) := by
  have projected := Mettapedia.Computability.WordHomomorphismMachine.outputs Hooks.sourceImage hooks
  have copied := Mettapedia.Computability.WordTemplateMachine.outputs canonicalTemplate (Hooks.sourceBytes hooks)
  rw [canonicalTemplate_exact pattern hooks traced literalCase admitted] at copied
  have copied' : TM2OutputsInTime (Mettapedia.Computability.WordTemplateMachine.machine canonicalTemplate)
      ((Hooks.sourceBytes hooks).map (Equiv.refl Alphabet)) (some (argumentWire pattern))
      (4*(canonicalTemplate.length+1)*((Hooks.sourceBytes hooks).length+1)) := by
    simpa only [Equiv.coe_refl, List.map_id] using copied
  have run := Mettapedia.Computability.StackMachineComposition.outputs projectMachine
    (Mettapedia.Computability.WordTemplateMachine.machine canonicalTemplate) (Equiv.refl Alphabet)
    hooks (Hooks.sourceBytes hooks) (argumentWire pattern) _ _ projected copied'
  have length := projected_length hooks
  refine ⟨run.toEvalsTo, run.steps_le_m.trans ?_⟩
  dsimp only [Hooks.sourceBytes] at length ⊢
  nlinarith

end HookLiteral

namespace Named

open PrimitiveTransport

/-- Naming a constructor application uses the same original child order. -/
theorem applyTerms_context (head : DBTerm) (arguments : List DBTerm)
    (first second : List SourceVar)
    (headEq : named? head first = named? head second)
    (childEq : ∀ argument ∈ arguments, named? argument first = named? argument second) :
    named? (applyTerms head arguments) first = named? (applyTerms head arguments) second := by
  induction arguments generalizing head with
  | nil => exact headEq
  | cons argument rest ih =>
      apply ih (.app head argument)
      · simp only [named?, headEq, childEq argument (by simp)]
      · intro child member
        exact childEq child (by simp [member])

theorem applyTerms_isSome (head : DBTerm) (arguments : List DBTerm) (binders : List SourceVar)
    (headSome : (named? head binders).isSome)
    (childSome : ∀ argument ∈ arguments, (named? argument binders).isSome) :
    (named? (applyTerms head arguments) binders).isSome := by
  induction arguments generalizing head with
  | nil => exact headSome
  | cons argument rest ih =>
      apply ih (.app head argument)
      · obtain ⟨functionSource, functionEq⟩ := Option.isSome_iff_exists.mp headSome
        obtain ⟨argumentSource, argumentEq⟩ := Option.isSome_iff_exists.mp (childSome argument (by simp))
        simp [named?,functionEq,argumentEq]
      · intro child member
        exact childSome child (by simp [member])

theorem applyTerms_freeNames (head : DBTerm) (arguments : List DBTerm) :
    freeNames (applyTerms head arguments) = freeNames head ++ arguments.flatMap freeNames := by
  induction arguments generalizing head with
  | nil => simp [applyTerms]
  | cons argument rest ih =>
      simpa only [applyTerms,List.foldl_cons,freeNames,List.flatMap_cons,List.append_assoc] using
        ih (.app head argument)

/-- Source pattern binders are literal data; they do not introduce target
bound or free variables into a rendered argument. -/
theorem dataTerm_freeNames (pattern : Pattern) : freeNames (dataTerm pattern) = [] := by
  cases pattern with
  | apply name arguments =>
      rw [dataTerm,applyTerms_freeNames]
      simp only [constructorTerm,freeNames,List.nil_append]
      have children : arguments.flatMap (fun argument => freeNames (dataTerm argument)) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro argument member
        exact dataTerm_freeNames argument
      simpa only [List.flatMap_map,Function.comp_def] using children
  | _ => simp only [dataTerm,literalTerm,freeNames]
termination_by sizeOf pattern
decreasing_by all_goals sizeOf_pattern_dec

/-- The original naming algorithm produces the same source syntax under
any external binder context, without selecting fresh names for data. -/
theorem dataTerm_context (pattern : Pattern) (first second : List SourceVar) :
    named? (dataTerm pattern) first = named? (dataTerm pattern) second := by
  cases pattern with
  | apply name arguments =>
      rw [dataTerm]
      apply applyTerms_context (constructorTerm name arguments.length)
      · simp only [constructorTerm,named?]
      · intro argument member
        obtain ⟨child, childMember, same⟩ := List.mem_map.mp member
        subst argument
        exact dataTerm_context child first second
  | _ => simp only [dataTerm,literalTerm,named?]
termination_by sizeOf pattern
decreasing_by
  all_goals
    have smaller := List.sizeOf_lt_of_mem childMember
    simp only [Pattern.apply.sizeOf_spec]
    omega

theorem dataTerm_isSome (pattern : Pattern) (binders : List SourceVar) :
    (named? (dataTerm pattern) binders).isSome := by
  cases pattern with
  | apply name arguments =>
      rw [dataTerm]
      apply applyTerms_isSome (constructorTerm name arguments.length)
      · simp only [constructorTerm,named?,Option.isSome_some]
      · intro argument member
        obtain ⟨child, childMember, same⟩ := List.mem_map.mp member
        subst argument
        exact dataTerm_isSome child binders
  | _ => simp only [dataTerm,literalTerm,named?,Option.isSome_some]
termination_by sizeOf pattern
decreasing_by
  all_goals
    have smaller := List.sizeOf_lt_of_mem childMember
    simp only [Pattern.apply.sizeOf_spec]
    omega

/-- This value is obtained from the existing naming operation, whose
successful result is proved above for every original rendered argument. -/
def argument (pattern : Pattern) : SourceTerm :=
  (named? (dataTerm pattern) []).get (dataTerm_isSome pattern [])

theorem argument_exact (pattern : Pattern) (binders : List SourceVar) :
    named? (dataTerm pattern) binders = some (argument pattern) := by
  rw [dataTerm_context pattern binders []]
  exact (Option.some_get (dataTerm_isSome pattern [])).symm

theorem checkedSource_argument (pattern : Pattern) :
    (PrimitiveTransport.checkedSource (renderedArgument pattern)).source = argument pattern := by
  have original := TemplateInstantiationMachine.Named.checkedSource_named (renderedArgument pattern)
  rw [renderedArgument_term,argument_exact pattern []] at original
  exact (Option.some.inj original).symm

theorem checkedSource_context (pattern : Pattern) (binders : List SourceVar) :
    PrimitiveTransport.named? (renderedArgument pattern).term binders =
      some (PrimitiveTransport.checkedSource (renderedArgument pattern)).source := by
  rw [renderedArgument_term,checkedSource_argument]
  exact argument_exact pattern binders

theorem opaque_wire (pattern : Pattern) (literalCase : isOpaque pattern = true)
    (admitted : argumentValidAt 0 pattern = true) :
    encodeWith sourceTermCodec (argument pattern) = termWire (renderedArgument pattern).term := by
  have named := argument_exact pattern []
  rw [← renderedArgument_term pattern, opaque_term pattern literalCase admitted] at named
  simp only [literalTerm,named?,Option.some.injEq] at named
  rw [← named]
  rw [opaque_term pattern literalCase admitted]
  rfl

end Named

end Mettapedia.Languages.HOLLight.ArgumentRenderingMachine

namespace Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Continuation
open Turing StateTransition
open Turing.TM2.Stmt
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability.StackMachineRegisters

/-- Names, ordered child words and occurrence markers have independently
owned frames. An optional byte is data here; the outer option owns the frame. -/
inductive Arena where
  | name | children | markers
  deriving DecidableEq, Fintype
inductive Key where
  | local (arena : Arena) | frames (arena : Arena)
  deriving DecidableEq, Fintype
abbrev Cell := Option Alphabet
abbrev Cells : Key → Type
  | .local _ => Cell
  | .frames _ => Option Cell
instance (key : Key) : Fintype (Cells key) := by cases key <;> dsimp only [Cells] <;> infer_instance
inductive Phase where
  | sub (restoring : Bool) (arena : Arena) (phase : WordFrame.Phase)
  | returning (restoring : Bool) (arena : Arena)
  deriving DecidableEq, Fintype
abbrev Control := WordFrame.Control (A:=Cell)
abbrev Cfg := TM2.Cfg Cells Phase Control

def keys (arena : Arena) : WordFrame.Key → Key
  | .local => .local arena
  | .frames => .frames arena

theorem cells (arena : Arena) (key : WordFrame.Key) : WordFrame.Cells (A:=Cell) key = Cells (keys arena key) := by
  cases key <;> rfl

@[simp] theorem cells_local_apply (arena : Arena) (value : Cell) :
    (cells arena .local).mp value = value := rfl
@[simp] theorem cells_frames_apply (arena : Arena) (value : Option Cell) :
    (cells arena .frames).mp value = value := rfl

def program : Phase → TM2.Stmt Cells Phase Control
  | .sub restoring arena phase => embedStatement (keys arena) (Phase.sub restoring arena)
      id (fun _ value => value) (cells arena)
      (goto fun _ => .returning restoring arena) (WordFrame.program phase)
  | .returning restoring .name => branch (fun state => state.2.2)
      (load (fun _ => WordFrame.initial)
        (goto fun _ => .sub restoring .children (if restoring then .restore else .push))) halt
  | .returning restoring .children => branch (fun state => state.2.2)
      (load (fun _ => WordFrame.initial)
        (goto fun _ => .sub restoring .markers (if restoring then .restore else .push))) halt
  | .returning _ .markers => halt

def step : Cfg → Option Cfg := TM2.step program

def storage (arena : Arena) (locals : Arena → List Cell)
    (frames : Arena → List (Option Cell)) (original : ∀ key, List (WordFrame.Cells (A:=Cell) key)) :
    ∀ key, List (Cells key)
  | .local selected => if selected = arena then original .local else locals selected
  | .frames selected => if selected = arena then original .frames else frames selected

def embed (restoring : Bool) (arena : Arena) (locals : Arena → List Cell)
    (frames : Arena → List (Option Cell)) (original : WordFrame.Cfg (A:=Cell)) : Cfg :=
  embeddedReturningConfig (Phase.sub restoring arena) (.returning restoring arena) id
    (storage arena locals frames) original

theorem storage_read (arena : Arena) (locals : Arena → List Cell) (frames : Arena → List (Option Cell))
    (original : ∀ key, List (WordFrame.Cells (A:=Cell) key)) (key : WordFrame.Key) :
    storage arena locals frames original (keys arena key) = (original key).map (cells arena key).mp := by
  cases key <;> change _ = List.map id _ <;> simp [storage,keys]

theorem storage_write (arena : Arena) (locals : Arena → List Cell) (frames : Arena → List (Option Cell))
    (original : ∀ key, List (WordFrame.Cells (A:=Cell) key)) (key : WordFrame.Key)
    (value : List (WordFrame.Cells (A:=Cell) key)) :
    storage arena locals frames (Function.update original key value) =
      Function.update (storage arena locals frames original) (keys arena key) (value.map (cells arena key).mp) := by
  cases key with
  | «local» =>
      change storage arena locals frames (Function.update original .local value) =
        Function.update (storage arena locals frames original) (Key.local arena) (value.map id)
      funext target
      cases target with
      | «local» selected =>
          by_cases same : selected = arena
          · subst selected; simp [storage,Function.update]
          · simp [storage,Function.update,same]
      | frames selected => simp [storage,Function.update]
  | frames =>
      change storage arena locals frames (Function.update original .frames value) =
        Function.update (storage arena locals frames original) (Key.frames arena) (value.map id)
      funext target
      cases target with
      | «local» selected => simp [storage,Function.update]
      | frames selected =>
          by_cases same : selected = arena
          · subst selected; simp [storage,Function.update]
          · simp [storage,Function.update,same]

/-- The original word-frame transition executes in the selected arena;
all other caller storage retains its exact physical contents. -/
theorem embed_step (restoring : Bool) (arena : Arena) (locals : Arena → List Cell)
    (frames : Arena → List (Option Cell)) (before after : WordFrame.Cfg (A:=Cell))
    (executed : WordFrame.step before = some after) :
    step (embed restoring arena locals frames before) = some (embed restoring arena locals frames after) := by
  apply step_embedStatement (keys arena) (Phase.sub restoring arena) (.returning restoring arena)
    id (fun _ value => value) (cells arena) id
    (storage arena locals frames) (fun _ => rfl) (fun _ _ => rfl)
    ?_ ?_ WordFrame.program program before after ?_ executed
  · intro contents key
    exact storage_read arena locals frames contents key
  · intro contents key value
    exact storage_write arena locals frames contents key value
  · intro label present
    rfl

/-- Saving/returning moves each byte and its delimiter, with no word stored
in the finite register. The selected arena's original frame clock is retained. -/
noncomputable def saveArena (arena : Arena) (locals : Arena → List Cell)
    (frames : Arena → List (Option Cell)) (state : Control) :
    EvalsToInTime step
      (embed false arena locals frames (WordFrame.config (some .push) state (locals arena) (frames arena)))
      (some (embed false arena locals frames
        (WordFrame.config none (none,none,true) [] ((locals arena).reverse.map some++none::frames arena))))
      ((locals arena).length+2) :=
  Mettapedia.Computability.StackMachineComposition.lift_execution WordFrame.step step
    (embed false arena locals frames) (embed_step false arena locals frames)
    (WordFrame.saveRun (locals arena) (frames arena) state)

noncomputable def restoreArena (arena : Arena) (locals : Arena → List Cell)
    (frames : Arena → List (Option Cell)) (saved : List Cell) (state : Control) :
    EvalsToInTime step
      (embed true arena locals frames
        (WordFrame.config (some .restore) state (locals arena) (saved.reverse.map some++none::frames arena)))
      (some (embed true arena locals frames
        (WordFrame.config none (none,none,true) (saved++locals arena) (frames arena))))
      (saved.length+1) :=
  Mettapedia.Computability.StackMachineComposition.lift_execution WordFrame.step step
    (embed true arena locals frames) (embed_step true arena locals frames)
    (WordFrame.restoreRun saved (frames arena) (locals arena) state)

def config (phase : Option Phase) (state : Control) (locals : Arena → List Cell)
    (frames : Arena → List (Option Cell)) : Cfg :=
  ⟨phase,state,fun key => match key with | .local arena => locals arena | .frames arena => frames arena⟩

theorem embed_config (restoring : Bool) (arena : Arena) (locals : Arena → List Cell)
    (frames : Arena → List (Option Cell)) (phase : Option WordFrame.Phase) (state : Control)
    (word : List Cell) (owned : List (Option Cell)) :
    embed restoring arena locals frames (WordFrame.config phase state word owned) =
      config (some (phase.elim (.returning restoring arena) (Phase.sub restoring arena))) state
        (Function.update locals arena word) (Function.update frames arena owned) := by
  simp only [embed,embeddedReturningConfig,config,WordFrame.config,id_eq]
  congr 1
  funext key
  cases key <;> simp [storage,Function.update]

/-- A failed owned-frame return stops before the next arena is touched. -/
theorem returning_refuses (restoring : Bool) (arena : Arena) (state : Control)
    (refused : state.2.2 = false) (locals : Arena → List Cell)
    (frames : Arena → List (Option Cell)) :
    step (config (some (.returning restoring arena)) state locals frames) =
      some (config none state locals frames) := by
  cases arena <;> simp [step,program,config,TM2.step,TM2.stepAux,refused]

def savedFrames (locals : Arena → List Cell) (frames : Arena → List (Option Cell)) :
    Arena → List (Option Cell) := fun arena => (locals arena).reverse.map some++none::frames arena

/-- Whole caller suspension saves all three arena images in their authored
order. Empty words and duplicate child words retain their owned boundaries. -/
noncomputable def saveRun (locals : Arena → List Cell) (frames : Arena → List (Option Cell)) :
    EvalsToInTime step (config (some (.sub false .name .push)) WordFrame.initial locals frames)
      (some (config none (none,none,true) (fun _ => []) (savedFrames locals frames)))
      ((locals .name).length+(locals .children).length+(locals .markers).length+9) := by
  let l1 := Function.update locals .name []
  let f1 := Function.update frames .name ((locals .name).reverse.map some++none::frames .name)
  let l2 := Function.update l1 .children []
  let f2 := Function.update f1 .children ((locals .children).reverse.map some++none::frames .children)
  have first := saveArena .name locals frames WordFrame.initial
  rw [embed_config,embed_config] at first
  simp only [Option.elim_some,Option.elim_none,Function.update_eq_self] at first
  have switch1 : step (config (some (.returning false .name)) (none,none,true) l1 f1) =
      some (config (some (.sub false .children .push)) WordFrame.initial l1 f1) := by
    simp [step,program,config,TM2.step,TM2.stepAux]
  have second := saveArena .children l1 f1 WordFrame.initial
  rw [embed_config,embed_config] at second
  simp only [Option.elim_some,Option.elim_none,Function.update_eq_self] at second
  simp only [l1,f1,Function.update_of_ne (by decide : Arena.children ≠ Arena.name)] at second
  have switch2 : step (config (some (.returning false .children)) (none,none,true) l2 f2) =
      some (config (some (.sub false .markers .push)) WordFrame.initial l2 f2) := by
    simp [step,program,config,TM2.step,TM2.stepAux]
  have third := saveArena .markers l2 f2 WordFrame.initial
  rw [embed_config,embed_config] at third
  simp only [Option.elim_some,Option.elim_none,Function.update_eq_self] at third
  simp only [l2,l1,f2,f1,Function.update_of_ne (by decide : Arena.markers ≠ Arena.name),
    Function.update_of_ne (by decide : Arena.markers ≠ Arena.children)] at third
  have finish : step (config (some (.returning false .markers)) (none,none,true)
      (Function.update l2 .markers [])
      (Function.update f2 .markers ((locals .markers).reverse.map some++none::frames .markers))) =
      some (config none (none,none,true) (fun _ => []) (savedFrames locals frames)) := by
    simp only [step,program,config,TM2.step,TM2.stepAux]
    congr 1
    congr 1
    funext key
    cases key with
    | «local» arena => cases arena <;> simp [l1,l2,Function.update]
    | frames arena => cases arena <;> simp [f1,f2,savedFrames,Function.update]
  have joined := EvalsToInTime.trans _ _ _ _ _ _ first
    (Mettapedia.Computability.StackMachineComposition.oneStep switch1)
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined second
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined
    (Mettapedia.Computability.StackMachineComposition.oneStep switch2)
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined third
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined
    (Mettapedia.Computability.StackMachineComposition.oneStep finish)
  convert joined using 1; omega

/-- Restoring a caller reinstates all three saved images and leaves every
outer frame intact. A saved empty child arena is not a missing frame. -/
noncomputable def restoreRun (saved : Arena → List Cell) (frames : Arena → List (Option Cell)) :
    EvalsToInTime step
      (config (some (.sub true .name .restore)) WordFrame.initial (fun _ => []) (savedFrames saved frames))
      (some (config none (none,none,true) saved frames))
      ((saved .name).length+(saved .children).length+(saved .markers).length+6) := by
  let empty : Arena → List Cell := fun _ => []
  let f0 := savedFrames saved frames
  let l1 := Function.update empty .name (saved .name)
  let f1 := Function.update f0 .name (frames .name)
  let l2 := Function.update l1 .children (saved .children)
  let f2 := Function.update f1 .children (frames .children)
  have first := restoreArena .name empty f1 (saved .name) WordFrame.initial
  rw [embed_config,embed_config] at first
  simp only [Option.elim_some,Option.elim_none] at first
  have first' : EvalsToInTime step
      (config (some (.sub true .name .restore)) WordFrame.initial empty f0)
      (some (config (some (.returning true .name)) (none,none,true) l1 f1))
      ((saved .name).length+1) := by
    convert first using 1
    all_goals
      simp only [Option.some.injEq,config]
      congr 1
      funext key
      cases key with
      | «local» arena => cases arena <;> simp [empty,l1,Function.update]
      | frames arena => cases arena <;> simp [f0,f1,savedFrames,Function.update]
  have switch1 : step (config (some (.returning true .name)) (none,none,true) l1 f1) =
      some (config (some (.sub true .children .restore)) WordFrame.initial l1 f1) := by
    simp [step,program,config,TM2.step,TM2.stepAux]
  have second := restoreArena .children l1 f2 (saved .children) WordFrame.initial
  rw [embed_config,embed_config] at second
  simp only [Option.elim_some,Option.elim_none] at second
  have second' : EvalsToInTime step
      (config (some (.sub true .children .restore)) WordFrame.initial l1 f1)
      (some (config (some (.returning true .children)) (none,none,true) l2 f2))
      ((saved .children).length+1) := by
    convert second using 1
    all_goals
      simp only [Option.some.injEq,config]
      congr 1
      funext key
      cases key with
      | «local» arena => cases arena <;> simp [empty,l1,l2,Function.update]
      | frames arena => cases arena <;> simp [f0,f1,f2,savedFrames,Function.update]
  have switch2 : step (config (some (.returning true .children)) (none,none,true) l2 f2) =
      some (config (some (.sub true .markers .restore)) WordFrame.initial l2 f2) := by
    simp [step,program,config,TM2.step,TM2.stepAux]
  have third := restoreArena .markers l2 frames (saved .markers) WordFrame.initial
  rw [embed_config,embed_config] at third
  simp only [Option.elim_some,Option.elim_none] at third
  have third' : EvalsToInTime step
      (config (some (.sub true .markers .restore)) WordFrame.initial l2 f2)
      (some (config (some (.returning true .markers)) (none,none,true) saved frames))
      ((saved .markers).length+1) := by
    convert third using 1
    all_goals
      simp only [Option.some.injEq,config]
      congr 1
      funext key
      cases key with
      | «local» arena => cases arena <;> simp [empty,l1,l2,Function.update]
      | frames arena => cases arena <;> simp [f0,f1,f2,savedFrames,Function.update]
  have finish : step (config (some (.returning true .markers)) (none,none,true) saved frames) =
      some (config none (none,none,true) saved frames) := rfl
  have joined := EvalsToInTime.trans _ _ _ _ _ _ first'
    (Mettapedia.Computability.StackMachineComposition.oneStep switch1)
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined second'
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined
    (Mettapedia.Computability.StackMachineComposition.oneStep switch2)
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined third'
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined
    (Mettapedia.Computability.StackMachineComposition.oneStep finish)
  convert joined using 1; omega

end Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Continuation

namespace Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.ChildReturn
open Turing StateTransition
open Turing.TM2.Stmt
open Mettapedia.Computability.StackMachineRegisters
open Mettapedia.OSLF.Binding.WireCodec.Binary

abbrev Cells := withStackAlphabet Continuation.Cells Continuation.Cell
inductive Phase where
  | restore (phase : Continuation.Phase) | returned | attach
  deriving DecidableEq, Fintype
abbrev Control := Continuation.Control
abbrev Cfg := TM2.Cfg Cells Phase Control

def program : Phase → TM2.Stmt Cells Phase Control
  | .restore phase => embedStatement some Phase.restore id (fun _ value => value)
      (fun _ => rfl) (goto fun _ => .returned) (Continuation.program phase)
  | .returned => branch (fun state => state.2.2) (goto fun _ => .attach) halt
  | .attach => pop none (fun state value => (value,state.2))
      (branch (fun state => state.1.isSome)
        (push (some (.local .children)) (fun state => state.1.getD none) (goto fun _ => .attach))
        (push (some (.local .children)) (fun _ => none)
          (push (some (.local .markers)) (fun _ => none) halt)))

def step : Cfg → Option Cfg := TM2.step program

def embed (word : List Continuation.Cell) (original : Continuation.Cfg) : Cfg :=
  embeddedReturningConfig Phase.restore .returned id (fun contents => withStackContents contents word) original

theorem embed_step (word : List Continuation.Cell) (before after : Continuation.Cfg)
    (executed : Continuation.step before = some after) :
    step (embed word before) = some (embed word after) := by
  apply step_embedStatement some Phase.restore .returned id (fun _ value => value) (fun _ => rfl) id
    (fun contents => withStackContents contents word) (fun _ => rfl) (fun _ _ => rfl) ?_ ?_
    Continuation.program program before after ?_ executed
  · intro contents key
    change contents key = List.map id (contents key)
    simp only [List.map_id]
  · intro contents key value
    change withStackContents (Function.update contents key value) word =
      Function.update (withStackContents contents word) (some key) (value.map id)
    simpa only [List.map_id] using withStackContents_update contents word key value
  · intro label present
    rfl

def config (phase : Option Phase) (state : Control) (word : List Continuation.Cell)
    (locals : Continuation.Arena → List Continuation.Cell)
    (frames : Continuation.Arena → List (Option Continuation.Cell)) : Cfg :=
  ⟨phase,state,fun key => match key with
    | none => word
    | some (.local arena) => locals arena
    | some (.frames arena) => frames arena⟩

theorem embed_config (word : List Continuation.Cell) (phase : Option Continuation.Phase)
    (state : Control) (locals : Continuation.Arena → List Continuation.Cell)
    (frames : Continuation.Arena → List (Option Continuation.Cell)) :
    embed word (Continuation.config phase state locals frames) =
      config (some (phase.elim .returned Phase.restore)) state word locals frames := by
  simp only [embed,embeddedReturningConfig,Continuation.config,id_eq]
  congr 1
  funext key
  cases key with
  | none => rfl
  | some key => cases key <;> rfl

/-- No child bytes or marker are committed when restoration refused. -/
theorem returned_refuses (state : Control) (refused : state.2.2 = false)
    (word : List Continuation.Cell) (locals : Continuation.Arena → List Continuation.Cell)
    (frames : Continuation.Arena → List (Option Continuation.Cell)) :
    step (config (some .returned) state word locals frames) =
      some (config none state word locals frames) := by
  simp [step,program,config,TM2.step,TM2.stepAux,refused]

def attachedLocals (word : List Alphabet) (locals : Continuation.Arena → List Continuation.Cell) :
    Continuation.Arena → List Continuation.Cell
  | .name => locals .name
  | .children => none :: (word.reverse.map some ++ locals .children)
  | .markers => none :: locals .markers

theorem attach_cons (state : Control) (symbol : Continuation.Cell) (word : List Continuation.Cell)
    (locals : Continuation.Arena → List Continuation.Cell)
    (frames : Continuation.Arena → List (Option Continuation.Cell)) :
    step (config (some .attach) state (symbol::word) locals frames) =
      some (config (some .attach) (some symbol,state.2) word
        (Function.update locals .children (symbol::locals .children)) frames) := by
  simp [step,program,config,TM2.step,TM2.stepAux]
  funext key
  cases key with
  | none => simp [Function.update]
  | some key => cases key with
    | «local» arena => cases arena <;> simp [Function.update]
    | frames arena => cases arena <;> simp [Function.update]

theorem attach_nil (state : Control)
    (locals : Continuation.Arena → List Continuation.Cell)
    (frames : Continuation.Arena → List (Option Continuation.Cell)) :
    step (config (some .attach) state [] locals frames) =
      some (config none (none,state.2) []
        (Function.update (Function.update locals .children (none::locals .children)) .markers
          (none::locals .markers)) frames) := by
  simp [step,program,config,TM2.step,TM2.stepAux]
  funext key
  cases key with
  | none => simp [Function.update]
  | some key => cases key with
    | «local» arena => cases arena <;> simp [Function.update]
    | frames arena => cases arena <;> simp [Function.update]

theorem attachedLocals_nil (locals : Continuation.Arena → List Continuation.Cell) :
    attachedLocals [] locals = Function.update
      (Function.update locals .children (none::locals .children)) .markers (none::locals .markers) := by
  funext arena; cases arena <;> simp [attachedLocals,Function.update]

theorem attachedLocals_cons (symbol : Alphabet) (word : List Alphabet)
    (locals : Continuation.Arena → List Continuation.Cell) :
    attachedLocals (symbol::word) locals = attachedLocals word
      (Function.update locals .children (some symbol::locals .children)) := by
  funext arena; cases arena <;> simp [attachedLocals,Function.update,List.reverse_cons,List.map_append,List.append_assoc]

/-- Returning a physical child word adds one delimiter and one occurrence
marker. Equal words are copied independently, preserving their order. -/
noncomputable def attachRun (word : List Alphabet) (state : Control)
    (locals : Continuation.Arena → List Continuation.Cell)
    (frames : Continuation.Arena → List (Option Continuation.Cell)) :
    EvalsToInTime step (config (some .attach) state (word.map some) locals frames)
      (some (config none (none,state.2) [] (attachedLocals word locals) frames))
      (word.length+1) := by
  induction word generalizing state locals with
  | nil =>
      simpa only [List.map_nil,List.length_nil,Nat.zero_add,attachedLocals_nil] using
        Mettapedia.Computability.StackMachineComposition.oneStep (attach_nil state locals frames)
  | cons symbol word ih =>
      have first := Mettapedia.Computability.StackMachineComposition.oneStep
        (attach_cons state (some symbol) (word.map some) locals frames)
      have rest := ih (some (some symbol),state.2)
        (Function.update locals .children (some symbol::locals .children))
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
      simpa only [List.map_cons,attachedLocals_cons,List.length_cons,Nat.add_assoc] using joined

/-- Whole child return restores the caller's saved arenas, then copies the
completed original term word into its ordered child vector. Every transfer
has its original executed clock. -/
noncomputable def run (word : List Alphabet)
    (saved : Continuation.Arena → List Continuation.Cell)
    (frames : Continuation.Arena → List (Option Continuation.Cell)) :
    EvalsToInTime step
      (config (some (.restore (.sub true .name .restore))) WordFrame.initial (word.map some)
        (fun _ => []) (Continuation.savedFrames saved frames))
      (some (config none (none,none,true) [] (attachedLocals word saved) frames))
      ((saved .name).length+(saved .children).length+(saved .markers).length+word.length+8) := by
  have restore := Mettapedia.Computability.StackMachineComposition.lift_execution
    Continuation.step step (embed (word.map some)) (embed_step (word.map some))
    (Continuation.restoreRun saved frames)
  rw [embed_config,embed_config] at restore
  simp only [Option.elim_some,Option.elim_none] at restore
  have resume : step (config (some .returned) (none,none,true) (word.map some) saved frames) =
      some (config (some .attach) (none,none,true) (word.map some) saved frames) := rfl
  have middle := Mettapedia.Computability.StackMachineComposition.oneStep resume
  have attach := attachRun word (none,none,true) saved frames
  have joined := EvalsToInTime.trans _ _ _ _ _ _ restore middle
  have joined := EvalsToInTime.trans _ _ _ _ _ _ joined attach
  convert joined using 1; omega

end Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.ChildReturn

namespace Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Routing

open Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Nesting

open Turing StateTransition
open Turing.TM2.Stmt
open Mettapedia.Computability.StackMachineComposition (oneStep)
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef.PatternSpanExecution
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Commands retain complete dynamic field bytes. Opaque nested nodes do not
become constructor commands. -/
inductive Symbol where
  | start | constructor | literal | finish | refused
  | name (value : Alphabet) | source (value : Alphabet)
  deriving DecidableEq, Fintype

inductive Mode where
  | pending | constructor | literal
  deriving DecidableEq, Fintype

/-- These lists are compile-time transition images, never machine registers. -/
inductive Action where
  | put (mode : Mode) (capture : Bool) (word : List Symbol) (enter : Bool)
  | finishLiteral

def action (mode : Mode) (capture : Bool) (symbol : Hooks.Symbol) : Action :=
  match mode, symbol with
  | .literal, .fieldStart _ => .put .literal false [.source 4] false
  | .literal, .byte value => .put .literal false [.source value] false
  | .literal, .event (.begin _) => .put .literal false [] true
  | .literal, .event .finish => .finishLiteral
  | .literal, _ => .put .literal false [] false
  | .pending, .fieldStart .pattern => .put .pending false [.start, .source 4] false
  | .pending, .fieldStart _ => .put .pending false [.source 4] false
  | .pending, .byte value => .put .pending false [.source value] false
  | .pending, .event (.begin .application) => .put .constructor false [.constructor] false
  | .pending, .event (.begin _) => .put .literal false [.literal] true
  | .pending, _ => .put .pending false [] false
  | .constructor, .fieldStart .pattern => .put .pending false [.start, .source 4] false
  | .constructor, .fieldStart (.name .constructor) => .put .constructor true [] false
  | .constructor, .fieldEnd => .put .constructor false [] false
  | .constructor, .byte value =>
      .put .constructor capture (if capture then [.name value] else []) false
  | .constructor, .event .finish => .put .constructor false [.finish] false
  | .constructor, _ => .put .constructor capture [] false

abbrev State := Mode × Bool × List Unit

def advance (state : State) (symbol : Hooks.Symbol) : State × List Symbol :=
  match action state.1 state.2.1 symbol with
  | .put mode capture word enter =>
      ((mode, capture, if enter then () :: state.2.2 else state.2.2), word)
  | .finishLiteral =>
      match state.2.2 with
      | [] => ((.constructor, false, []), [.refused])
      | _ :: [] => ((.constructor, false, []), [.finish])
      | _ :: rest => ((.literal, false, rest), [])

def route (state : State) : List Hooks.Symbol → State × List Symbol
  | [] => (state, [])
  | head :: tail =>
      let next := advance state head
      let result := route next.1 tail
      (result.1, next.2 ++ result.2)

theorem route_append (state : State) (left right : List Hooks.Symbol) :
    route state (left ++ right) =
      ((route (route state left).1 right).1,
        (route state left).2 ++ (route (route state left).1 right).2) := by
  induction left generalizing state with
  | nil => simp [route]
  | cons head tail ih => simp only [List.cons_append,route,ih,List.append_assoc]

theorem literal_neutral (depth : List Unit) (symbol : Hooks.Symbol)
    (notBegin : ∀ node, symbol ≠ .event (.begin node))
    (notFinish : symbol ≠ .event .finish) :
    advance (.literal,false,()::depth) symbol =
      ((.literal,false,()::depth), (Hooks.sourceImage symbol).map Symbol.source) := by
  cases symbol with
  | fieldStart task => rfl
  | byte value => rfl
  | fieldEnd => rfl
  | event event =>
      cases event <;> simp_all [advance,action,Hooks.sourceImage]

/-- Every byte of a balanced nested span survives, while all of its internal
constructor events are suppressed. Literal ownership is kept intact. -/
theorem literal_closed {hooks : List Hooks.Symbol} (closed : Closed hooks) (depth : List Unit) :
    route (.literal,false,()::depth) hooks =
      ((.literal,false,()::depth), (Hooks.sourceBytes hooks).map Symbol.source) := by
  induction closed generalizing depth with
  | nil => rfl
  | @neutral head tail notBegin notFinish _ ih =>
      rw [route,literal_neutral depth head notBegin notFinish,ih]
      simp only [Hooks.sourceBytes,List.flatMap_cons,List.map_append]
  | @nested node body tail _ _ bodyIH tailIH =>
      simp only [List.cons_append]
      rw [route]
      change (route (.literal,false,()::()::depth) (body ++ .event .finish :: tail)) = _
      rw [route_append,bodyIH (()::depth)]
      simp only [route,advance,action]
      rw [tailIH depth]
      simp only [Hooks.sourceBytes,List.flatMap_cons,List.flatMap_append,Hooks.sourceImage,
        List.nil_append,List.map_append]

/-- All original source bytes of a suspended literal span are retained. The
final two symbols are the existing source-list terminator, not a new codec. -/
theorem literal_pattern_bytes (pattern : Pattern) (hooks : List Hooks.Symbol)
    (traced : Hooks.Trace [.pattern] (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern) [] hooks)
    (observed : Hooks.erase hooks = events pattern) (depth : List Unit) :
    (route (.literal,false,()::depth) hooks).2 ++ [.source 3,.source 2] =
      (patternWire pattern).map Symbol.source := by
  have retained := literal_closed (pattern_span_closed pattern hooks observed) depth
  rw [retained]
  have original := Hooks.Trace.pattern_sourceBytes pattern hooks traced
  change Hooks.sourceBytes hooks ++ [3,2] = patternWire pattern at original
  simpa only [List.map_append,List.map_cons,List.map_nil] using congrArg (List.map Symbol.source) original

theorem name_bytes (name : List Alphabet) (depth : List Unit) :
    route (.constructor,true,depth) (name.map Hooks.Symbol.byte) =
      ((.constructor,true,depth), name.map Symbol.name) := by
  induction name with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons,route,advance,action,Bool.false_eq_true,↓reduceIte,ih,List.cons_append,List.nil_append]

/-- Constructor-name extraction copies the exact original UTF-8 String
field. Tag spellings have no special behavior at this field boundary. -/
theorem constructor_name_field (name : String) (depth : List Unit) :
    route (.constructor,false,depth) (Hooks.field (.name .constructor) name) =
      ((.constructor,false,depth), (encodeWith Codec.string name).map Symbol.name) := by
  simp only [Hooks.field,List.cons_append]
  rw [route]
  change route (.constructor,true,depth)
    ((encodeWith Codec.string name).map Hooks.Symbol.byte ++ [.fieldEnd]) = _
  rw [route_append,name_bytes]
  simp [route,advance,action]

def actionLength : Action → Nat
  | .put _ _ word _ => word.length
  | .finishLiteral => 1

private theorem classified_word_bound :
    ∀ (mode : Mode) (capture : Bool) (symbol : Hooks.Symbol),
      actionLength (action mode capture symbol) ≤ 2 := by
  decide

theorem action_word_length (mode : Mode) (capture : Bool) (symbol : Hooks.Symbol)
    (nextMode : Mode) (nextCapture : Bool) (word : List Symbol) (enter : Bool)
    (equal : action mode capture symbol = .put nextMode nextCapture word enter) :
    word.length ≤ 2 := by
  have bound := classified_word_bound mode capture symbol
  rw [equal] at bound
  exact bound

theorem advance_length (state : State) (symbol : Hooks.Symbol) :
    (advance state symbol).2.length ≤ 2 := by
  unfold advance
  split
  · rename_i mode capture word enter equal
    exact action_word_length state.1 state.2.1 symbol mode capture word enter equal
  · split <;> simp_all

theorem route_length (state : State) (symbols : List Hooks.Symbol) :
    (route state symbols).2.length ≤ 2 * symbols.length := by
  induction symbols generalizing state with
  | nil => simp [route]
  | cons head tail ih =>
      have emitted := advance_length state head
      have remaining := ih (advance state head).1
      simp only [route, List.length_append, List.length_cons]
      omega

inductive Key where
  | input | output | result | depth
  deriving DecidableEq, Fintype
abbrev Cells : Key → Type
  | .input => Hooks.Symbol
  | .depth => Unit
  | .output | .result => Symbol
inductive Phase where
  | read | dispatch (mode : Mode) (capture : Bool) (symbol : Hooks.Symbol) | reverse | cleanup
  deriving DecidableEq, Fintype
abbrev Control := Mode × Bool × Option Hooks.Symbol × Option Unit × Option Symbol
abbrev Cfg := TM2.Cfg Cells Phase Control

def pushWord : List Symbol → TM2.Stmt Cells Phase Control → TM2.Stmt Cells Phase Control
  | [], statement => statement
  | value :: values, statement => push .output (fun _ => value) (pushWord values statement)

def dispatch (command : Action) : TM2.Stmt Cells Phase Control :=
  match command with
  | .put mode capture word enter =>
      load (fun _ => (mode, capture, none, none, none))
        (if enter then push .depth (fun _ => ()) (pushWord word (goto fun _ => .read))
         else pushWord word (goto fun _ => .read))
  | .finishLiteral =>
      pop .depth (fun state value => (state.1, state.2.1, none, value, none))
        (branch (fun state => state.2.2.2.1.isSome)
          (pop .depth (fun state value => (state.1, state.2.1, none, value, none))
            (branch (fun state => state.2.2.2.1.isSome)
              (push .depth (fun _ => ())
                (load (fun _ => (.literal, false, none, none, none)) (goto fun _ => .read)))
              (load (fun _ => (.constructor, false, none, none, none))
                (push .output (fun _ => .finish) (goto fun _ => .read)))))
          (load (fun _ => (.constructor, false, none, none, none))
            (push .output (fun _ => .refused) (goto fun _ => .read))))

def program : Phase → TM2.Stmt Cells Phase Control
  | .read => pop .input (fun state value => (state.1, state.2.1, value, none, none))
      (branch (fun state => state.2.2.1.isSome)
        (goto fun state => .dispatch state.1 state.2.1 (state.2.2.1.getD .fieldEnd))
        (goto fun _ => .reverse))
  | .dispatch mode capture symbol => dispatch (action mode capture symbol)
  | .reverse => pop .output (fun state value => (state.1, state.2.1, none, none, value))
      (branch (fun state => state.2.2.2.2.isSome)
        (push .result (fun state => state.2.2.2.2.getD .refused) (goto fun _ => .reverse))
        (goto fun _ => .cleanup))
  | .cleanup => pop .depth (fun state value => (state.1,state.2.1,none,value,none))
      (branch (fun state => state.2.2.2.1.isSome) (goto fun _ => .cleanup)
        (load (fun _ => (.pending,false,none,none,none)) halt))

def step : Cfg → Option Cfg := TM2.step program

def config (phase : Option Phase) (control : Control) (input : List Hooks.Symbol)
    (output result : List Symbol) (depth : List Unit) : Cfg :=
  ⟨phase,control,fun key => match key with
    | .input => input | .output => output | .result => result | .depth => depth⟩

def registers (state : State) : Control := (state.1, state.2.1, none, none, none)

theorem pushWord_apply (word : List Symbol) (statement : TM2.Stmt Cells Phase Control)
    (phase : Option Phase) (control : Control) (input : List Hooks.Symbol)
    (output result : List Symbol) (depth : List Unit) :
    TM2.stepAux (pushWord word statement) control
      (config phase control input output result depth).stk =
    TM2.stepAux statement control
      (config phase control input (word.reverse ++ output) result depth).stk := by
  induction word generalizing statement output with
  | nil => simp only [pushWord,List.reverse_nil,List.nil_append]
  | cons head tail ih =>
      simp only [pushWord,TM2.stepAux]
      change TM2.stepAux (pushWord tail statement) control
        (Function.update (config phase control input output result depth).stk .output (head::output)) = _
      have updated : Function.update (config phase control input output result depth).stk
          .output (head :: output) =
          (config phase control input (head :: output) result depth).stk := by
        funext key
        cases key <;> simp [config,Function.update]
      rw [updated,ih]
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

theorem read_cons (state : State) (head : Hooks.Symbol) (tail : List Hooks.Symbol)
    (output result : List Symbol) :
    step (config (some .read) (registers state) (head :: tail) output result state.2.2) =
      some (config (some (.dispatch state.1 state.2.1 head))
        (state.1,state.2.1,some head,none,none) tail output result state.2.2) := by
  simp [step,program,config,registers,TM2.step,TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem dispatch_exact (state : State) (symbol : Hooks.Symbol) (input : List Hooks.Symbol)
    (output result : List Symbol) :
    step (config (some (.dispatch state.1 state.2.1 symbol))
      (state.1,state.2.1,some symbol,none,none) input output result state.2.2) =
      some (config (some .read) (registers (advance state symbol).1) input
        ((advance state symbol).2.reverse ++ output) result (advance state symbol).1.2.2) := by
  simp only [step,TM2.step,config,program]
  unfold advance
  generalize commandEq : action state.1 state.2.1 symbol = command
  cases command with
  | put mode capture word enter =>
      cases enter with
      | false =>
          change some (TM2.stepAux (dispatch (.put mode capture word false))
            (state.1,state.2.1,some symbol,none,none)
            (config none (mode,capture,none,none,none) input output result state.2.2).stk) = _
          simp only [dispatch,Bool.false_eq_true,↓reduceIte,TM2.stepAux]
          rw [pushWord_apply]
          rfl
      | true =>
          change some (TM2.stepAux (dispatch (.put mode capture word true))
            (state.1,state.2.1,some symbol,none,none)
            (config none (mode,capture,none,none,none) input output result state.2.2).stk) = _
          simp only [dispatch,↓reduceIte,TM2.stepAux]
          have updated : Function.update
              (config none (mode,capture,none,none,none) input output result state.2.2).stk
              .depth (() :: state.2.2) =
              (config none (mode,capture,none,none,none) input output result (()::state.2.2)).stk := by
            funext key
            cases key <;> simp [config,Function.update]
          change some (TM2.stepAux (pushWord word (goto fun _ => .read))
            (mode,capture,none,none,none)
            (Function.update (config none (mode,capture,none,none,none) input output result state.2.2).stk
              .depth (() :: state.2.2))) = _
          rw [updated,pushWord_apply]
          rfl
  | finishLiteral =>
      rcases state with ⟨mode,capture,depth⟩
      cases depth with
      | nil =>
          simp [dispatch,TM2.stepAux,registers]
          funext key
          cases key <;> simp [Function.update]
      | cons head tail =>
          cases head
          cases tail with
          | nil =>
              simp [dispatch,TM2.stepAux,registers]
              funext key
              cases key <;> simp [Function.update]
          | cons head tail =>
              cases head
              simp [dispatch,TM2.stepAux,registers]
              funext key
              cases key <;> simp [Function.update]

theorem read_nil (state : State) (output result : List Symbol) :
    step (config (some .read) (registers state) [] output result state.2.2) =
      some (config (some .reverse) (registers state) [] output result state.2.2) := by
  simp [step,program,config,registers,TM2.step,TM2.stepAux]

theorem reverse_cons (state : State) (head : Symbol) (tail result : List Symbol) :
    step (config (some .reverse) (registers state) [] (head :: tail) result state.2.2) =
      some (config (some .reverse) (state.1,state.2.1,none,none,some head)
        [] tail (head :: result) state.2.2) := by
  simp [step,program,config,registers,TM2.step,TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem reverse_cons_registers (state : State) (selected : Option Symbol)
    (head : Symbol) (tail result : List Symbol) :
    step (config (some .reverse) (state.1,state.2.1,none,none,selected)
      [] (head :: tail) result state.2.2) =
      some (config (some .reverse) (state.1,state.2.1,none,none,some head)
        [] tail (head :: result) state.2.2) := by
  simp [step,program,config,TM2.step,TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem reverse_nil (state : State) (selected : Option Symbol) (result : List Symbol) :
    step (config (some .reverse) (state.1,state.2.1,none,none,selected)
      [] [] result state.2.2) =
      some (config (some .cleanup) (registers state) [] [] result state.2.2) := by
  simp [step,program,config,registers,TM2.step,TM2.stepAux]

/-- Routing consumes each original hook once. Dynamic fields stay on stacks;
the only nesting memory is the physical literal-depth stack. -/
def routingRun (state : State) (symbols : List Hooks.Symbol) (output result : List Symbol) :
    EvalsToInTime step
      (config (some .read) (registers state) symbols output result state.2.2)
      (some (config (some .read) (registers (route state symbols).1) []
        ((route state symbols).2.reverse ++ output) result (route state symbols).1.2.2))
      (2 * symbols.length) := by
  induction symbols generalizing state output with
  | nil =>
      simpa only [route,List.reverse_nil,List.nil_append,List.length_nil,Nat.mul_zero] using
        EvalsToInTime.refl step
          (config (some .read) (registers state) [] output result state.2.2)
  | cons head tail ih =>
      have read := oneStep (read_cons state head tail output result)
      have dispatched := oneStep (dispatch_exact state head tail output result)
      have rest := ih (advance state head).1 ((advance state head).2.reverse ++ output)
      have complete := EvalsToInTime.trans _ _ _ _ _ _ read (EvalsToInTime.trans _ _ _ _ _ _ dispatched rest)
      simpa only [route,List.reverse_append,List.append_assoc,List.length_cons,
        Nat.mul_add,Nat.mul_one] using complete

def reversalRun (state : State) (selected : Option Symbol) (word result : List Symbol) :
    EvalsToInTime step
      (config (some .reverse) (state.1,state.2.1,none,none,selected)
        [] word result state.2.2)
      (some (config (some .cleanup) (registers state) [] [] (word.reverse ++ result) state.2.2))
      (word.length + 1) := by
  induction word generalizing selected result with
  | nil =>
      simpa only [List.reverse_nil,List.nil_append,List.length_nil,Nat.zero_add] using
        oneStep (reverse_nil state selected result)
  | cons head tail ih =>
      have popped := oneStep (reverse_cons_registers state selected head tail result)
      have remaining := ih (some head) (head :: result)
      simpa only [List.reverse_cons,List.append_assoc,List.singleton_append,List.length_cons,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using EvalsToInTime.trans _ _ _ _ _ _ popped remaining

def initial : State := (.pending,false,[])

def startConfig (symbols : List Hooks.Symbol) : Cfg :=
  config (some .read) (registers initial) symbols [] [] []

def machine : FinTM2 where
  K := Key
  k₀ := .input
  k₁ := .result
  Γ := Cells
  Γk₀Fin := by change Fintype Hooks.Symbol; infer_instance
  Λ := Phase
  main := .read
  σ := Control
  initialState := registers initial
  m := program

theorem machine_step : machine.step = step := rfl

theorem cleanup_cons (state : State) (selected : Option Unit) (head : Unit) (tail : List Unit)
    (result : List Symbol) :
    step (config (some .cleanup) (state.1,state.2.1,none,selected,none) [] [] result (head::tail)) =
      some (config (some .cleanup) (state.1,state.2.1,none,some head,none) [] [] result tail) := by
  simp [step,program,config,TM2.step,TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem cleanup_nil (state : State) (selected : Option Unit) (result : List Symbol) :
    step (config (some .cleanup) (state.1,state.2.1,none,selected,none) [] [] result []) =
      some (config none (registers initial) [] [] result []) := by
  simp [step,program,config,registers,initial,TM2.step,TM2.stepAux]

def cleanupRun (state : State) (selected : Option Unit) (depth : List Unit) (result : List Symbol) :
    EvalsToInTime step
      (config (some .cleanup) (state.1,state.2.1,none,selected,none) [] [] result depth)
      (some (config none (registers initial) [] [] result [])) (depth.length+1) := by
  induction depth generalizing selected with
  | nil => simpa only [List.length_nil,Nat.zero_add] using oneStep (cleanup_nil state selected result)
  | cons head tail ih =>
      have popped := oneStep (cleanup_cons state selected head tail result)
      have remaining := ih (some head)
      have joined := EvalsToInTime.trans _ _ _ _ _ _ popped remaining
      convert joined using 1; simp only [List.length_cons]


theorem advance_depth (state : State) (symbol : Hooks.Symbol) :
    (advance state symbol).1.2.2.length ≤ state.2.2.length + 1 := by
  unfold advance
  split
  · rename_i mode capture word enter equal
    cases enter <;> simp
  · split <;> simp_all only [List.length_nil,List.length_cons] <;> omega

theorem route_depth (state : State) (symbols : List Hooks.Symbol) :
    (route state symbols).1.2.2.length ≤ state.2.2.length + symbols.length := by
  induction symbols generalizing state with
  | nil => simp [route]
  | cons head tail ih =>
      have next := advance_depth state head
      have rest := ih (advance state head).1
      simp only [route,List.length_cons]
      omega

private theorem init_eq (symbols : List Hooks.Symbol) : initList machine symbols = startConfig symbols := by
  simp only [initList,machine,startConfig,config,initial,registers]
  congr 1
  funext key
  cases key <;> simp

private theorem halt_eq (word : List Symbol) :
    haltList machine word = config none (registers initial) [] [] word [] := by
  simp only [haltList,machine,config]
  congr 1
  funext key
  cases key <;> simp

/-- The clock charges every read, dispatch, emitted-byte reversal and final
physical cleanup. The router is a rendering front end, not source admission. -/
def outputs (symbols : List Hooks.Symbol) :
    TM2OutputsInTime machine symbols (some (route initial symbols).2)
      (5 * symbols.length + 3) := by
  have routed := routingRun initial symbols [] []
  simp only [List.append_nil] at routed
  have exhausted := oneStep
    (read_nil (route initial symbols).1 (route initial symbols).2.reverse [])
  have reversed := reversalRun (route initial symbols).1 none (route initial symbols).2.reverse []
  simp only [List.reverse_reverse,List.append_nil] at reversed
  have cleared := cleanupRun (route initial symbols).1 none (route initial symbols).1.2.2
    (route initial symbols).2
  have complete := EvalsToInTime.trans _ _ _ _ _ _ routed exhausted
  have complete := EvalsToInTime.trans _ _ _ _ _ _ complete reversed
  have complete := EvalsToInTime.trans _ _ _ _ _ _ complete cleared
  change EvalsToInTime step (initList machine symbols) (some (haltList machine (route initial symbols).2)) _
  rw [init_eq,halt_eq]
  have bound := route_length initial symbols
  simp only [initial] at bound
  have nesting := route_depth initial symbols
  refine ⟨complete.toEvalsTo,complete.steps_le_m.trans ?_⟩
  simp only [List.length_reverse,initial,List.length_nil,Nat.zero_add] at nesting ⊢
  omega


end Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Routing


namespace Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Routing.Traversal

open Turing StateTransition
open Turing.TM2.Stmt
open Mettapedia.Computability
open Mettapedia.Computability.StackMachineRegisters
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.PatternSpanExecution
open Mettapedia.OSLF.MeTTaIL.Syntax

abbrev Key := Option (Option PatternSpanExecution.Execution.Stack)
abbrev Cells := Hooks.Execution.Cells

def clearKeys : List Key :=
  [Hooks.Execution.key .input, Hooks.Execution.key .frames, Hooks.Execution.key .scratch,
   Hooks.Execution.key .span, Hooks.Execution.key .tasks, Hooks.Execution.key .events,
   Hooks.Execution.key .result, some none]

inductive Phase where
  | visit (phase : Hooks.Execution.Phase)
  | sweep (index : Fin (clearKeys.length+1))
  deriving DecidableEq, Fintype
abbrev Control := (Hooks.Execution.Control × Bool) × Unit

def initial : Control := ((Hooks.Execution.initial,false),())

def program : Phase → TM2.Stmt Cells Phase Control
  | .visit phase => embedStatement id Phase.visit (fun state => state.1.1)
      (fun state value => ((value,state.1.2),state.2)) (fun _ => rfl)
      (.goto (fun _ => .sweep ⟨0,by simp [clearKeys]⟩)) (Hooks.Execution.program phase)
  | .sweep index => extend Phase.sweep (StackMachineComposition.Sweep.program clearKeys Hooks.Execution.initial index)

abbrev Cfg := TM2.Cfg Cells Phase Control
def step : Cfg → Option Cfg := TM2.step program

def machine : FinTM2 where
  K := Key
  k₀ := Hooks.Execution.key .input
  k₁ := none
  Γ := Cells
  Γk₀Fin := by change Fintype Alphabet; infer_instance
  Λ := Phase
  main := .visit (.visit .start)
  σ := Control
  initialState := initial
  m := program

theorem machine_step : machine.step = step := rfl

def visitConfig (source : Hooks.Execution.Cfg) : Cfg :=
  embeddedReturningConfig Phase.visit (.sweep ⟨0,by simp [clearKeys]⟩)
    (fun state => ((state,false),())) id source

def sweepConfig (source : StackMachineComposition.Sweep.Cfg (Cells:=Cells) (State:=Hooks.Execution.Control) clearKeys) : Cfg :=
  StackMachineRegisters.config Phase.sweep () source

theorem visit_step (before after : Hooks.Execution.Cfg) (executed : Hooks.Execution.step before = some after) :
    step (visitConfig before) = some (visitConfig after) := by
  apply step_embedStatement id Phase.visit (.sweep ⟨0,by simp [clearKeys]⟩)
    (fun state => state.1.1) (fun state value => ((value,state.1.2),state.2))
    (fun _ => rfl) (fun state => ((state,false),())) id
    (fun _ => rfl) (fun _ _ => rfl) ?_ ?_ Hooks.Execution.program program before after ?_ executed
  · intro contents key; change contents key = (contents key).map id; simp
  · intro contents key value; change Function.update contents key value = Function.update contents key (value.map id); simp
  · intro label present; rfl

theorem sweep_step (before after : StackMachineComposition.Sweep.Cfg
    (Cells:=Cells) (State:=Hooks.Execution.Control) clearKeys)
    (executed : StackMachineComposition.Sweep.step clearKeys Hooks.Execution.initial before = some after) :
    step (sweepConfig before) = some (sweepConfig after) := by
  change TM2.step (StackMachineComposition.Sweep.program clearKeys Hooks.Execution.initial) before = some after at executed
  have mapped := step_extend Phase.sweep () (StackMachineComposition.Sweep.program clearKeys Hooks.Execution.initial)
    program before (fun _ _ => rfl)
  simpa only [step,sweepConfig,StackMachineComposition.Sweep.step,executed,Option.map_some] using mapped

private theorem clear_result (hooks : List Hooks.Symbol) (contents : ∀ key, List (Cells key))
    (retained : contents none = hooks) :
    StackMachineComposition.Sweep.clear contents clearKeys = fun key => match key with
      | none => hooks | some _ => [] := by
  funext key
  cases key with
  | none => simpa [StackMachineComposition.Sweep.clear,clearKeys,Hooks.Execution.key] using retained
  | some key => cases key with
    | none => simp [StackMachineComposition.Sweep.clear,clearKeys,Hooks.Execution.key]
    | some key => cases key <;> simp [StackMachineComposition.Sweep.clear,clearKeys,Hooks.Execution.key]

private theorem init_eq (value : Pattern) :
    initList machine (encodeWith Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec value) =
      visitConfig (Hooks.Execution.startConfig (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)) := by
  simp only [initList,machine,visitConfig,embeddedReturningConfig,Option.elim_some,initial,
    Hooks.Execution.startConfig,Hooks.Execution.config]
  rw [PatternSpanExecution.Execution.original_pattern_wire]
  congr 1
  funext key
  cases key with
  | none => simp [Hooks.Execution.key]
  | some key => cases key with
    | none => simp [Hooks.Execution.key]
    | some key => cases key <;> simp [Hooks.Execution.key]

private theorem halt_eq (hooks : List Hooks.Symbol) (contents : ∀ key, List (Cells key))
    (retained : contents none = hooks) :
    sweepConfig (StackMachineComposition.Sweep.config clearKeys none (Hooks.Execution.initial,false)
      (StackMachineComposition.Sweep.clear contents clearKeys)) = haltList machine hooks := by
  rw [clear_result hooks contents retained]
  simp only [sweepConfig,StackMachineRegisters.config,StackMachineComposition.Sweep.config,
    Option.map_none,haltList,machine,initial]
  congr 1
  funext key
  cases key <;> simp

/-- The original byte visitor runs unchanged and physically clears its source
receipts, events and scratch storage before exposing its hook stream. -/
theorem outputs (value : Pattern) :
    ∃ hooks, Hooks.Trace [.pattern] (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value) [] hooks ∧
      Hooks.erase hooks = PatternSpanExecution.events value ∧
      Nonempty (TM2OutputsInTime machine
        (encodeWith Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec value)
        (some hooks) (40*(encodeWith Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec value).length+19)) := by
  obtain ⟨hooks,traced,erased,⟨visited⟩⟩ := Hooks.Execution.pattern_execution_linear value []
  simp only [List.append_nil] at visited
  let contents := (Hooks.Execution.config none Hooks.Execution.initial
    (PatternSpanExecution.Execution.tokenWire []) [] [] [] []
    (PatternSpanExecution.events value).reverse
    (PatternSpanExecution.Execution.tokenWire (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)) [] hooks).stk
  have traversed := StackMachineComposition.lift_execution Hooks.Execution.step step visitConfig visit_step visited
  have cleanup := StackMachineComposition.Sweep.run clearKeys Hooks.Execution.initial [] clearKeys rfl
    (Hooks.Execution.initial,false) contents
  have cleaned := StackMachineComposition.lift_execution
    (StackMachineComposition.Sweep.step clearKeys Hooks.Execution.initial) step sweepConfig sweep_step cleanup
  have boundary : visitConfig (Hooks.Execution.config none Hooks.Execution.initial
      (PatternSpanExecution.Execution.tokenWire []) [] [] [] []
      (PatternSpanExecution.events value).reverse
      (PatternSpanExecution.Execution.tokenWire (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)) [] hooks) =
      sweepConfig (StackMachineComposition.Sweep.config clearKeys (some ⟨0,by simp [clearKeys]⟩)
        (Hooks.Execution.initial,false) contents) := rfl
  rw [boundary] at traversed
  have joined := EvalsToInTime.trans _ _ _ _ _ _ traversed cleaned
  rw [halt_eq hooks contents rfl,←init_eq value] at joined
  have clearBound := StackMachineComposition.Sweep.cost_le contents clearKeys
  have sumEq : (clearKeys.map fun key => (contents key).length).sum =
      2+(PatternSpanExecution.events value).length+
        (encodeWith Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec value).length := by
    simp only [contents,clearKeys,Hooks.Execution.config,Hooks.Execution.key,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,List.length_reverse,List.length_nil,Nat.zero_add,Nat.add_zero]
    rw [← PatternSpanExecution.Execution.original_pattern_wire]
    have nilLength : (PatternSpanExecution.Execution.tokenWire []).length = 2 := rfl
    rw [nilLength]
    omega
  rw [sumEq] at clearBound
  have eventsBound := PatternSpanExecution.Execution.pattern_events_length_le value
  have fieldsBound : (PatternSpanExecution.Execution.fields (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)).length ≤
      (encodeWith Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.patternCodec value).length := by
    rw [PatternSpanExecution.Execution.original_pattern_wire,PatternSpanExecution.Execution.tokenWire_eq,
      List.length_append]
    exact Nat.le_add_right _ _
  refine ⟨hooks,traced,erased,⟨⟨joined.toEvalsTo,joined.steps_le_m.trans ?_⟩⟩⟩
  have keyCount : clearKeys.length = 8 := rfl
  rw [keyCount] at clearBound
  omega

end Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Routing.Traversal

namespace Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Routing.Pipeline

open Turing StateTransition
open Mettapedia.Computability
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.PatternSpanExecution
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.WireCodec.Binary

local instance : Fintype (Traversal.machine.Γ Traversal.machine.k₁) := by change Fintype Hooks.Symbol; infer_instance
local instance : Inhabited (Traversal.machine.Γ Traversal.machine.k₁) := ⟨.fieldEnd⟩

def machine : FinTM2 := StackMachineComposition.machine Traversal.machine Routing.machine (Equiv.refl Hooks.Symbol)

/-- The source byte packet is visited once, scratch-cleared, handed off and
routed through the declared rendering commands. Both programs and every
handoff transition execute on physical stacks. -/
theorem outputs (value : Pattern) :
    ∃ hooks, Hooks.Trace [.pattern] (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value) [] hooks ∧
      Hooks.erase hooks = PatternSpanExecution.events value ∧
      Nonempty (TM2OutputsInTime machine (encodeWith CertificateDataEncoding.patternCodec value)
        (some (Routing.route Routing.initial hooks).2)
        (124*(encodeWith CertificateDataEncoding.patternCodec value).length+31)) := by
  obtain ⟨hooks,traced,erased,⟨visited⟩⟩ := Traversal.outputs value
  have routed := Routing.outputs hooks
  have routed' : TM2OutputsInTime Routing.machine (hooks.map (Equiv.refl Hooks.Symbol))
      (some (Routing.route Routing.initial hooks).2) (5*hooks.length+3) := by
    simpa only [Equiv.coe_refl,List.map_id] using routed
  have joined := StackMachineComposition.outputs Traversal.machine Routing.machine (Equiv.refl Hooks.Symbol)
    (encodeWith CertificateDataEncoding.patternCodec value) hooks (Routing.route Routing.initial hooks).2 _ _ visited routed'
  have hookBound := traced.hooks_length_le
  rw [erased] at hookBound
  have eventBound := PatternSpanExecution.Execution.pattern_events_length_le value
  have countBound := PatternSpanExecution.Execution.fields_count_le (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)
  have fieldsBound : (PatternSpanExecution.Execution.fields (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode value)).length ≤
      (encodeWith CertificateDataEncoding.patternCodec value).length := by
    rw [PatternSpanExecution.Execution.original_pattern_wire,PatternSpanExecution.Execution.tokenWire_eq,List.length_append]
    exact Nat.le_add_right _ _
  refine ⟨hooks,traced,erased,⟨⟨joined.toEvalsTo,joined.steps_le_m.trans ?_⟩⟩⟩
  omega

/-- Expose only the concrete finite program for execution; enumerating the
bundled machine's finite state product is unnecessary for a native run. -/
def program := StackMachineComposition.Programs.body (none : Traversal.Key) Routing.Key.input Routing.Phase.read
  (Hooks.Symbol.fieldEnd) (fun symbol : Hooks.Symbol => symbol) Traversal.program Routing.program

theorem program_eq : machine.m = program := by
  exact (StackMachineComposition.body_eq Traversal.machine Routing.machine (Equiv.refl Hooks.Symbol)).symm

end Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Routing.Pipeline

namespace Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Routing

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.PatternSpanExecution
open Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Nesting
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary

theorem pending_bytes (word : List Alphabet) (depth : List Unit) :
    route (.pending,false,depth) (word.map Hooks.Symbol.byte) =
      ((.pending,false,depth),word.map Symbol.source) := by
  induction word with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons,route,advance,action,Bool.false_eq_true,↓reduceIte,ih,List.cons_append,List.nil_append]

theorem first_field (token : String) (depth : List Unit) :
    route (.constructor,false,depth) (Hooks.field .pattern token) =
      ((.pending,false,depth),.start ::
        (4 :: encodeWith Codec.string token).map Symbol.source) := by
  simp only [Hooks.field,List.cons_append]
  rw [route]
  change ((route (.pending,false,depth)
    ((encodeWith Codec.string token).map Hooks.Symbol.byte ++ [.fieldEnd])).1,
    [.start,.source 4] ++ (route (.pending,false,depth)
      ((encodeWith Codec.string token).map Hooks.Symbol.byte ++ [.fieldEnd])).2) = _
  rw [route_append,pending_bytes]
  simp [route,advance,action]

theorem discarded_bytes (word : List Alphabet) (depth : List Unit) :
    route (.constructor,false,depth) (word.map Hooks.Symbol.byte) =
      ((.constructor,false,depth),[]) := by
  induction word with
  | nil => rfl
  | cons head tail ih => simp [route,advance,action,ih]

theorem patterns_field (token : String) (depth : List Unit) :
    route (.constructor,false,depth) (Hooks.field .patterns token) =
      ((.constructor,false,depth),[]) := by
  simp only [Hooks.field,List.cons_append]
  rw [route]
  change route (.constructor,false,depth)
    ((encodeWith Codec.string token).map Hooks.Symbol.byte ++ [.fieldEnd]) = _
  rw [route_append,discarded_bytes]
  simp [route,advance,action]

/-- The literal command retains the complete original field prefix and body.
Nested constructor events belong to the literal and stay suppressed. -/
theorem opaque_route (token : String) (node : Node)
    (nonApplication : node ≠ .application) (body : List Hooks.Symbol)
    (closed : Closed body) :
    route (.constructor,false,[]) (Hooks.field .pattern token ++
      .event (.begin node) :: body ++ [.event .finish]) =
      ((.constructor,false,[]),
        .start :: (4 :: encodeWith Codec.string token).map Symbol.source ++
          [.literal] ++ (Hooks.sourceBytes body).map Symbol.source ++ [.finish]) := by
  simp only [List.append_assoc,List.cons_append]
  rw [route_append,first_field]
  have entered : advance (.pending,false,[]) (.event (.begin node)) =
      ((.literal,false,[()]),[.literal]) := by
    cases node <;> simp_all [advance,action]
  simp only [List.cons_append]
  rw [route]
  simp only [entered]
  rw [route_append,literal_closed closed []]
  simp [route,advance,action]

def opaqueCommands (token : String) (rest : List String) : List Symbol :=
  .start :: (4 :: encodeWith Codec.string token).map Symbol.source ++ [.literal] ++
    (PatternSpanExecution.Execution.fields rest).map Symbol.source ++ [.finish]

mutual
  /-- Static command specification for the original pattern visitor. -/
  def commands : Pattern → List Symbol
    | .apply name arguments => .start ::
        (4 :: encodeWith Codec.string "a").map Symbol.source ++ [.constructor] ++
        (encodeWith Codec.string name).map Symbol.name ++
        listCommands arguments ++ [.finish]
    | pattern => opaqueCommands
        ((Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).headD "")
        (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).tail
  def listCommands : List Pattern → List Symbol
    | [] => []
    | pattern :: patterns => commands pattern ++ listCommands patterns
end

theorem opaque_trace {tasks : List Task} {token : String} {node : Node}
    {rest tail : List String} {bodyEvents : List Event}
    (accepted : plan .pattern (tokenTag token) =
      some (.emit (.begin node) :: tasks ++ [.emit .finish]))
    (visited : Visits tasks (rest ++ tail) tail bodyEvents)
    (balanced : EventClosed bodyEvents) (nonApplication : node ≠ .application) :
    ∃ hooks, Hooks.Trace [.pattern] (token :: rest ++ tail) tail hooks ∧
      route (.constructor,false,[]) hooks =
        ((.constructor,false,[]),opaqueCommands token rest) := by
  obtain ⟨body,traced,events⟩ := Hooks.Visits.with_trace visited
  refine ⟨Hooks.field .pattern token ++ .event (.begin node) :: body ++ [.event .finish],?_,?_⟩
  · simp only [List.append_assoc,List.cons_append]
    apply Hooks.Trace.token (tasks:=[]) accepted
    simpa only [List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.append_assoc]
      using traced.surround [.begin node] [.finish]
  · rw [opaque_route token node nonApplication body (Closed.of_events balanced body events)]
    obtain ⟨consumed,same,bytes⟩ := traced.sourceBytes
    have equal : consumed = rest := List.append_cancel_right same.symm
    rw [equal] at bytes
    simp only [opaqueCommands,bytes]


mutual
  theorem routed_write (pattern : Pattern) (tail : List String) :
      ∃ hooks, Hooks.Trace [.pattern]
        (Mettapedia.OSLF.MeTTaIL.PatternTokens.write pattern tail) tail hooks ∧
          route (.constructor,false,[]) hooks = ((.constructor,false,[]),commands pattern) := by
    cases pattern with
    | bvar index =>
        have visited := (visits_number .boundIndex index tail).surround [.numberStart .boundIndex] []
        have balanced : EventClosed (.numberStart .boundIndex :: numberEvents .boundIndex index) :=
          EventClosed.neutral (by decide) (by decide) (numberEvents_closed .boundIndex index)
        have answer := opaque_trace (tasks:=[.emit (.numberStart .boundIndex),.natural .boundIndex]) (token:="b") (node:=.bound) (tail:=tail)
          (rest:=Mettapedia.OSLF.MeTTaIL.PatternTokens.bits index++["e"])
          (by rw [show tokenTag "b"=some 7 from tokenTag_authored 7]; rfl)
          (by simpa only [List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_nil,List.append_assoc] using visited)
          (by simpa only [List.nil_append,List.append_nil] using balanced) (by decide)
        simpa only [Mettapedia.OSLF.MeTTaIL.PatternTokens.write,
          Mettapedia.OSLF.MeTTaIL.PatternTokens.encode,commands,List.headD_cons,List.tail_cons,
          List.cons_append,List.singleton_append,List.nil_append,List.append_assoc] using answer
    | fvar name =>
        have visited := (visits_name .free name tail).surround [.freeVariable] []
        have answer := opaque_trace (tasks:=[.emit .freeVariable,.name .free]) (token:="v") (node:=.free) (tail:=tail) (rest:=[name])
          (by rw [show tokenTag "v"=some 8 from tokenTag_authored 8]; rfl)
          (by simpa only [List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_nil] using visited)
          (by apply EventClosed.neutrals; simp [boundary]) (by decide)
        simpa only [Mettapedia.OSLF.MeTTaIL.PatternTokens.write,
          Mettapedia.OSLF.MeTTaIL.PatternTokens.encode,commands,List.headD_cons,List.tail_cons,
          List.cons_append,List.singleton_append,List.nil_append] using answer
    | apply name arguments =>
        obtain ⟨childHooks,children,childrenRoute⟩ := routed_writeList arguments tail
        have named : Hooks.Trace [.name .constructor]
            (name::Mettapedia.OSLF.MeTTaIL.PatternTokens.writeList arguments tail)
            (Mettapedia.OSLF.MeTTaIL.PatternTokens.writeList arguments tail)
            (Hooks.field (.name .constructor) name++[.event (.name .constructor)]) :=
          .token (plan_name .constructor _) (.emit (.done _))
        have middle := named.append ((Hooks.Trace.event .argumentsStart _).append children)
        refine ⟨Hooks.field .pattern "a" ++
          [.event (.begin .application)] ++
            (Hooks.field (.name .constructor) name++[.event (.name .constructor)]) ++
            [.event .argumentsStart] ++ childHooks ++
            [.event .argumentsEnd,.event .finish],?_,?_⟩
        · simp only [List.append_assoc,List.cons_append,List.nil_append]
          apply Hooks.Trace.token (tasks:=[])
          · rw [show tokenTag "a"=some 0 from tokenTag_authored 0]; rfl
          · simpa only [List.map_cons,List.map_nil,List.cons_append,List.nil_append,List.append_assoc]
              using middle.surround [.begin .application] [.argumentsEnd,.finish]
        · simp only [List.append_assoc,List.cons_append,List.nil_append]
          rw [route_append,first_field]
          simp only [route,advance,action,Bool.false_eq_true,↓reduceIte]
          rw [route_append,constructor_name_field]
          simp only [route,advance,action,Bool.false_eq_true,↓reduceIte]
          rw [route_append,childrenRoute]
          simp [route,advance,action,commands,List.append_assoc]
    | lambda name body =>
        have middle := (visits_option .lambdaBinder name _).append
          ((visits_write body tail).surround [.enterOne] [.leave])
        have bodyBalanced := ((EventClosed.neutrals [.enterOne] (by simp [boundary])).append
          (pattern_events_closed body)).append (EventClosed.neutrals [.leave] (by simp [boundary]))
        have balanced := (optionEvents_closed .lambdaBinder name).append bodyBalanced
        have answer := opaque_trace (tasks:=[.optional .lambdaBinder,.emit .enterOne,.pattern,.emit .leave])
          (token:="l") (node:=.lambda) (tail:=tail)
          (rest:=Mettapedia.OSLF.MeTTaIL.PatternTokens.option name
            (Mettapedia.OSLF.MeTTaIL.PatternTokens.write body []))
          (by rw [show tokenTag "l"=some 3 from tokenTag_authored 3]; rfl)
          (by simpa only [← Mettapedia.OSLF.MeTTaIL.PatternTokens.write_append,
              ← Mettapedia.OSLF.MeTTaIL.PatternTokens.option_append,List.nil_append,
              List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_assoc] using middle)
          (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using balanced) (by decide)
        simpa only [Mettapedia.OSLF.MeTTaIL.PatternTokens.write,
          Mettapedia.OSLF.MeTTaIL.PatternTokens.encode,commands,List.headD_cons,List.tail_cons,
          List.cons_append,← Mettapedia.OSLF.MeTTaIL.PatternTokens.option_append,
          ← Mettapedia.OSLF.MeTTaIL.PatternTokens.write_append,List.nil_append] using answer
    | multiLambda arity names body =>
        have entered := (visits_write body tail).surround [.enterMany] [.leave]
        have named := (visits_names names _).append entered
        have numbered := (visits_number .binderArity arity _).append named
        have middle := numbered.surround [.numberStart .binderArity] []
        have bodyBalanced := ((EventClosed.neutrals [.enterMany] (by simp [boundary])).append
          (pattern_events_closed body)).append (EventClosed.neutrals [.leave] (by simp [boundary]))
        have inside := (numberEvents_closed .binderArity arity).append
          ((nameEvents_closed names).append bodyBalanced)
        have balanced : EventClosed (.numberStart .binderArity ::
          (numberEvents .binderArity arity ++ (nameEvents names ++ ([.enterMany] ++ events body ++ [.leave])))) :=
          EventClosed.neutral (by decide) (by decide) inside
        have answer := opaque_trace (tasks:=[.emit (.numberStart .binderArity),.natural .binderArity,
          .names,.emit .enterMany,.pattern,.emit .leave]) (token:="m") (node:=.multiLambda) (tail:=tail)
          (rest:=Mettapedia.OSLF.MeTTaIL.PatternTokens.bits arity++"e"::
            Mettapedia.OSLF.MeTTaIL.PatternTokens.names names
              (Mettapedia.OSLF.MeTTaIL.PatternTokens.write body []))
          (by rw [show tokenTag "m"=some 4 from tokenTag_authored 4]; rfl)
          (by simpa only [← Mettapedia.OSLF.MeTTaIL.PatternTokens.write_append,
              ← Mettapedia.OSLF.MeTTaIL.PatternTokens.names_append,List.nil_append,
              List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_nil,List.append_assoc] using middle)
          (by simpa only [List.append_assoc,List.cons_append,List.nil_append,List.append_nil] using balanced) (by decide)
        simpa only [Mettapedia.OSLF.MeTTaIL.PatternTokens.write,
          Mettapedia.OSLF.MeTTaIL.PatternTokens.encode,commands,List.headD_cons,List.tail_cons,
          List.cons_append,← Mettapedia.OSLF.MeTTaIL.PatternTokens.names_append,
          ← Mettapedia.OSLF.MeTTaIL.PatternTokens.write_append,List.nil_append,List.append_assoc] using answer
    | subst body replacement =>
        have left := (visits_write body (Mettapedia.OSLF.MeTTaIL.PatternTokens.write replacement tail)).surround
          [.enterOne] [.leave]
        have middle := left.append (visits_write replacement tail)
        have bodyBalanced := ((EventClosed.neutrals [.enterOne] (by simp [boundary])).append
          (pattern_events_closed body)).append (EventClosed.neutrals [.leave] (by simp [boundary]))
        have balanced := bodyBalanced.append (pattern_events_closed replacement)
        have answer := opaque_trace (tasks:=[.emit .enterOne,.pattern,.emit .leave,.pattern]) (token:="s") (node:=.substitution) (tail:=tail)
          (rest:=Mettapedia.OSLF.MeTTaIL.PatternTokens.write body
            (Mettapedia.OSLF.MeTTaIL.PatternTokens.write replacement []))
          (by rw [show tokenTag "s"=some 5 from tokenTag_authored 5]; rfl)
          (by simpa only [← Mettapedia.OSLF.MeTTaIL.PatternTokens.write_append,List.nil_append,
              List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_assoc] using middle)
          (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using balanced) (by decide)
        simpa only [Mettapedia.OSLF.MeTTaIL.PatternTokens.write,
          Mettapedia.OSLF.MeTTaIL.PatternTokens.encode,commands,List.headD_cons,List.tail_cons,
          List.cons_append,← Mettapedia.OSLF.MeTTaIL.PatternTokens.write_append,List.nil_append] using answer
    | collection kind elements capture =>
        have entered := (visits_writeList elements tail).surround [.argumentsStart] [.argumentsEnd]
        have captured := (visits_option .collectionCapture capture _).append entered
        have middle := (visits_kind kind _).append captured
        have bodyBalanced := ((EventClosed.neutrals [.argumentsStart] (by simp [boundary])).append
          (patterns_events_closed elements)).append (EventClosed.neutrals [.argumentsEnd] (by simp [boundary]))
        have capturedBalanced := (optionEvents_closed .collectionCapture capture).append bodyBalanced
        have balanced := (EventClosed.neutrals [kindEvent kind]
          (by cases kind <;> simp [kindEvent,boundary])).append capturedBalanced
        have answer := opaque_trace (tasks:=[.collectionKind,.optional .collectionCapture,
          .emit .argumentsStart,.patterns,.emit .argumentsEnd]) (token:="c") (node:=.collection) (tail:=tail)
          (rest:=Mettapedia.OSLF.MeTTaIL.PatternTokens.collection kind ::
            Mettapedia.OSLF.MeTTaIL.PatternTokens.option capture
              (Mettapedia.OSLF.MeTTaIL.PatternTokens.writeList elements []))
          (by rw [show tokenTag "c"=some 6 from tokenTag_authored 6]; rfl)
          (by simpa only [← Mettapedia.OSLF.MeTTaIL.PatternTokens.writeList_append,
              ← Mettapedia.OSLF.MeTTaIL.PatternTokens.option_append,List.nil_append,
              List.map_cons,List.map_nil,List.nil_append,List.cons_append,List.append_assoc] using middle)
          (by simpa only [List.append_assoc,List.cons_append,List.nil_append] using balanced) (by decide)
        simpa only [Mettapedia.OSLF.MeTTaIL.PatternTokens.write,
          Mettapedia.OSLF.MeTTaIL.PatternTokens.encode,commands,List.headD_cons,List.tail_cons,
          List.cons_append,← Mettapedia.OSLF.MeTTaIL.PatternTokens.option_append,
          ← Mettapedia.OSLF.MeTTaIL.PatternTokens.writeList_append,List.nil_append] using answer
    termination_by sizeOf pattern
    decreasing_by all_goals sizeOf_pattern_dec

  theorem routed_writeList (patterns : List Pattern) (tail : List String) :
      ∃ hooks, Hooks.Trace [.patterns]
        (Mettapedia.OSLF.MeTTaIL.PatternTokens.writeList patterns tail) tail hooks ∧
          route (.constructor,false,[]) hooks = ((.constructor,false,[]),listCommands patterns) := by
    cases patterns with
    | nil =>
        refine ⟨Hooks.field .patterns "z",?_,?_⟩
        · apply Hooks.Trace.token
          · rw [show tokenTag "z"=some 2 from tokenTag_authored 2]; rfl
          · exact .done tail
        · exact patterns_field "z" []
    | cons pattern patterns =>
        obtain ⟨before,first,firstRoute⟩ := routed_write pattern
          (Mettapedia.OSLF.MeTTaIL.PatternTokens.writeList patterns tail)
        obtain ⟨after,second,secondRoute⟩ := routed_writeList patterns tail
        refine ⟨Hooks.field .patterns "h" ++ before ++ after,?_,?_⟩
        · apply Hooks.Trace.token
          · rw [show tokenTag "h"=some 1 from tokenTag_authored 1]; rfl
          · exact first.append second
        · simp only [List.append_assoc]
          rw [route_append,patterns_field]
          simp only [List.nil_append]
          rw [route_append,firstRoute,secondRoute]
          rfl
    termination_by sizeOf patterns
    decreasing_by all_goals sizeOf_pattern_dec
end

/-- Any trace earned by the original visitor has the same complete command
stream. This includes opaque metadata and preserves sibling order. -/
theorem pattern_commands (pattern : Pattern) (tail : List String) (hooks : List Hooks.Symbol)
    (traced : Hooks.Trace [.pattern]
      (Mettapedia.OSLF.MeTTaIL.PatternTokens.write pattern tail) tail hooks) :
    route (.constructor,false,[]) hooks = ((.constructor,false,[]),commands pattern) := by
  obtain ⟨canonical,witness,exact⟩ := routed_write pattern tail
  have same := (traced.unique witness).2
  simpa only [same] using exact



theorem patterns_commands (patterns : List Pattern) (tail : List String) (hooks : List Hooks.Symbol)
    (traced : Hooks.Trace [.patterns]
      (Mettapedia.OSLF.MeTTaIL.PatternTokens.writeList patterns tail) tail hooks) :
    route (.constructor,false,[]) hooks = ((.constructor,false,[]),listCommands patterns) := by
  obtain ⟨canonical,witness,exact⟩ := routed_writeList patterns tail
  have same := (traced.unique witness).2
  simpa only [same] using exact

/-- Source chunks are exactly the original field list. The only omitted
symbols are its fixed two-symbol terminator, inserted by literal rendering. -/
theorem command_source_fields (pattern : Pattern) :
    ((4 :: encodeWith Codec.string
      ((Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).headD "")) ++
      PatternSpanExecution.Execution.fields
        (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).tail) ++ [3,2] =
      patternWire pattern := by
  have split : Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern =
      (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).headD "" ::
        (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).tail := by
    cases pattern <;> rfl
  have fields : (4 :: encodeWith Codec.string
      ((Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).headD "")) ++
      PatternSpanExecution.Execution.fields
        (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).tail =
      PatternSpanExecution.Execution.fields
        (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern) := by
    conv_rhs => rw [split]
    rfl
  rw [fields,←PatternSpanExecution.Execution.tokenWire_eq]
  exact (PatternSpanExecution.Execution.original_pattern_wire pattern).symm

theorem opaque_no_constructor (pattern : Pattern) (literalCase : isOpaque pattern = true) :
    Symbol.constructor ∉ commands pattern := by
  cases pattern <;> simp_all [isOpaque,commands,opaqueCommands]

namespace Controls

theorem duplicate_children (name : String) (child : Pattern) :
    commands (.apply name [child,child]) = .start ::
      (4 :: encodeWith Codec.string "a").map Symbol.source ++ [.constructor] ++
      (encodeWith Codec.string name).map Symbol.name ++
      (commands child ++ commands child) ++ [.finish] := by
  simp only [commands,listCommands,List.append_nil,List.append_assoc]

theorem opaque_constructor_is_data (name : String) :
    Symbol.constructor ∉ commands (.lambda none (.apply name [])) :=
  opaque_no_constructor _ rfl

theorem outer_depth_not_constructor_boundary :
    advance (.literal,false,[(),()]) (.event .finish) = ((.literal,false,[()]),[]) := rfl

end Controls

end Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Routing

namespace Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Constructor.HeadFromMarkers

open Turing StateTransition
open Turing.TM2.Stmt
open Mettapedia.Computability
open Mettapedia.Computability.StackMachineRegisters
open Mettapedia.Computability.StackMachineComposition (oneStep lift_execution)
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.Languages.HOLLight.InferenceHosting
open Mettapedia.Languages.HOLLight.InferenceStorageBounds
open Mettapedia.Languages.HOLLight.TemplateInstantiationMachine (termWire)

inductive Key where
  | input | countMarkers | arrowMarkers | arrowClosing
  | bits | bitTemporary
  | name | typeScratch | typeWord | scratch | result
  deriving DecidableEq, Fintype
abbrev Cells : Key → Type
  | .input | .countMarkers | .arrowMarkers | .arrowClosing => Unit
  | .bits | .bitTemporary => Bool
  | _ => Alphabet

instance (key : Key) : Fintype (Cells key) := by cases key <;> infer_instance

abbrev ArrowPhase := WordTemplateMachine.Wrapping.Phase
  (WordTemplateMachine.Wrapping.limit arrowPrefix (encodeData (putTy dataType)) arrowSuffix)

inductive Phase where
  | fork
  | count (phase : BinaryStackArithmetic.MarkerCounting.Phase)
  | arrow (phase : ArrowPhase)
  | opening | bits | name | typeWord | reverse
  deriving DecidableEq, Fintype

structure Control where
  counter : BinaryStackArithmetic.MarkerCounting.Control
  arrow : WordTemplateMachine.Wrapping.State (Γ:=Alphabet)
  bit : Option Bool
  symbol : Option Alphabet
  marker : Option Unit
  deriving Fintype

def initial : Control := ⟨BinaryStackArithmetic.MarkerCounting.initial,(false,none),none,none,none⟩

def countKey : Option Bool → Key
  | none => .countMarkers | some false => .bits | some true => .bitTemporary

def arrowKey : WordTemplateMachine.Wrapping.Stack → Key
  | .input => .arrowMarkers | .closing => .arrowClosing | .output => .typeScratch | .result => .typeWord

theorem countCells : ∀ key, BinaryStackArithmetic.MarkerCounting.Cells key = Cells (countKey key) := by
  intro key
  cases key with
  | none => rfl
  | some key => cases key <;> rfl

theorem arrowCells : ∀ key, WordTemplateMachine.Wrapping.Alphabet (Γ:=Alphabet) key = Cells (arrowKey key) := by
  intro key; cases key <;> rfl

/-- Every pushed word is a fixed program fragment. Dynamic names, types and
count bits live only in physical stacks. -/
def pushFixed : List Alphabet → TM2.Stmt Cells Phase Control → TM2.Stmt Cells Phase Control
  | [],rest => rest
  | head::tail,rest => push .scratch (fun _ => head) (pushFixed tail rest)

def digitImage (bit : Bool) : List Alphabet := 4::encodeWith Codec.string (if bit then "1" else "0")

def program : Phase → TM2.Stmt Cells Phase Control
  | .fork => pop .input (fun state value => {state with marker:=value})
      (branch (fun state => state.marker.isSome)
        (push .countMarkers (fun _ => ()) (push .arrowMarkers (fun _ => ()) (goto fun _ => .fork)))
        (load (fun _ => initial) (goto fun _ => .count .count)))
  | .count phase => embedStatement countKey Phase.count Control.counter
      (fun state value => {state with counter:=value}) countCells
      (goto fun _ => .arrow .read) (BinaryStackArithmetic.MarkerCounting.program phase)
  | .arrow phase => embedStatement arrowKey Phase.arrow Control.arrow
      (fun state value => {state with arrow:=value}) arrowCells
      (goto fun _ => .opening)
      ((WordTemplateMachine.Wrapping.machine arrowPrefix (encodeData (putTy dataType)) arrowSuffix).m phase)
  | .opening => pushFixed Head.opening (goto fun _ => .bits)
  | .bits => pop .bits (fun state value => {state with bit:=value})
      (branch (fun state => state.bit.isSome)
        (branch (fun state => state.bit.getD false)
          (pushFixed (digitImage true) (goto fun _ => .bits))
          (pushFixed (digitImage false) (goto fun _ => .bits)))
        (pushFixed (encodeData (.atom 0)) (goto fun _ => .name)))
  | .name => pop .name (fun state value => {state with symbol:=value})
      (branch (fun state => state.symbol.isSome)
        (push .scratch (fun state => state.symbol.getD 2) (goto fun _ => .name))
        (pushFixed (encodeData (.atom 0)) (goto fun _ => .typeWord)))
  | .typeWord => pop .typeWord (fun state value => {state with symbol:=value})
      (branch (fun state => state.symbol.isSome)
        (push .scratch (fun state => state.symbol.getD 2) (goto fun _ => .typeWord))
        (goto fun _ => .reverse))
  | .reverse => pop .scratch (fun state value => {state with symbol:=value})
      (branch (fun state => state.symbol.isSome)
        (push .result (fun state => state.symbol.getD 2) (goto fun _ => .reverse))
        (load (fun _ => initial) halt))

abbrev Cfg := TM2.Cfg Cells Phase Control
def step : Cfg → Option Cfg := TM2.step program

/-- The stored words are a mathematical configuration description, never
finite-control registers. Caller integration maps these original stacks. -/
structure Storage where
  input : List Unit := []
  countMarkers : List Unit := []
  arrowMarkers : List Unit := []
  arrowClosing : List Unit := []
  bits : List Bool := []
  bitTemporary : List Bool := []
  name : List Alphabet := []
  typeScratch : List Alphabet := []
  typeWord : List Alphabet := []
  scratch : List Alphabet := []
  result : List Alphabet := []

def contents (storage : Storage) : ∀ key, List (Cells key)
  | .input => storage.input | .countMarkers => storage.countMarkers
  | .arrowMarkers => storage.arrowMarkers | .arrowClosing => storage.arrowClosing
  | .bits => storage.bits | .bitTemporary => storage.bitTemporary
  | .name => storage.name | .typeScratch => storage.typeScratch | .typeWord => storage.typeWord
  | .scratch => storage.scratch | .result => storage.result

def config (phase : Option Phase) (state : Control) (storage : Storage) : Cfg := ⟨phase,state,contents storage⟩

theorem pushFixed_apply (word : List Alphabet) (rest : TM2.Stmt Cells Phase Control)
    (state : Control) (storage : Storage) :
    TM2.stepAux (pushFixed word rest) state (contents storage) =
      TM2.stepAux rest state (contents {storage with scratch:=word.reverse++storage.scratch}) := by
  induction word generalizing storage with
  | nil => rfl
  | cons head tail ih =>
      simp only [pushFixed,TM2.stepAux]
      have updated : Function.update (contents storage) .scratch (head::storage.scratch) =
          contents {storage with scratch:=head::storage.scratch} := by
        funext key; cases key <;> simp [contents,Function.update]
      change TM2.stepAux (pushFixed tail rest) state (Function.update (contents storage) .scratch (head::storage.scratch)) = _
      rw [updated,ih]
      simp only [List.reverse_cons,List.append_assoc,List.singleton_append]

theorem fork_cons (state : Control) (storage : Storage) (head : Unit) (tail : List Unit)
    (stored : storage.input=head::tail) :
    step (config (some .fork) state storage) =
      some (config (some .fork) {state with marker:=some head}
        {storage with input:=tail,countMarkers:=()::storage.countMarkers,arrowMarkers:=()::storage.arrowMarkers}) := by
  simp [step,program,config,contents,TM2.step,TM2.stepAux,stored]
  funext key; cases key <;> simp [contents,Function.update]

theorem fork_nil (state : Control) (storage : Storage) (empty : storage.input=[]) :
    step (config (some .fork) state storage) = some (config (some (.count .count)) initial storage) := by
  simp [step,program,config,contents,TM2.step,TM2.stepAux,empty]

/-- The physical input supplies both original programs with one marker per
child occurrence, including duplicates. -/
def forkRun (state : Control) (markers : List Unit) (storage : Storage) :
    EvalsToInTime step (config (some .fork) state {storage with input:=markers})
      (some (config (some (.count .count)) initial
        {storage with input:=[],countMarkers:=markers.reverse++storage.countMarkers,arrowMarkers:=markers.reverse++storage.arrowMarkers})) (markers.length+1) := by
  induction markers generalizing state storage with
  | nil => simpa only [List.length_nil,Nat.zero_add,List.reverse_nil,List.nil_append] using
      oneStep (fork_nil state {storage with input:=[]} rfl)
  | cons head tail ih =>
      cases head
      have first := oneStep (fork_cons state {storage with input:=()::tail} () tail rfl)
      have rest := ih {state with marker:=some ()}
        {storage with input:=tail,countMarkers:=()::storage.countMarkers,arrowMarkers:=()::storage.arrowMarkers}
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
      convert joined using 1
      all_goals simp only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append]

private def counterStorage (base : Storage) (source : ∀ key, List (BinaryStackArithmetic.MarkerCounting.Cells key)) : Storage :=
  {base with countMarkers:=source none,bits:=source (some false),bitTemporary:=source (some true)}

def counterConfig (base : Storage) (state : Control) (source : BinaryStackArithmetic.MarkerCounting.Cfg) : Cfg :=
  embeddedReturningConfig Phase.count (.arrow .read) (fun value => {state with counter:=value})
    (fun stored => contents (counterStorage base stored)) source

private theorem counter_read (base : Storage) (source : ∀ key, List (BinaryStackArithmetic.MarkerCounting.Cells key))
    (key : Option Bool) :
    contents (counterStorage base source) (countKey key) = (source key).map (countCells key).mp := by
  cases key with
  | none => change source none = (source none).map id; simp
  | some key => cases key <;> change _ = List.map id _ <;> simp [contents,counterStorage,countKey]

private theorem counter_write (base : Storage) (source : ∀ key, List (BinaryStackArithmetic.MarkerCounting.Cells key))
    (key : Option Bool) (value : List (BinaryStackArithmetic.MarkerCounting.Cells key)) :
    contents (counterStorage base (Function.update source key value)) =
      Function.update (contents (counterStorage base source)) (countKey key) (value.map (countCells key).mp) := by
  cases key with
  | none =>
      funext target; cases target <;> simp [contents,counterStorage,countKey,Function.update]
      change value = value.map id; simp
  | some key =>
      cases key <;> funext target <;> cases target <;> simp [contents,counterStorage,countKey,Function.update]
      all_goals change value = value.map id; simp

theorem counter_step (base : Storage) (state : Control) (before after : BinaryStackArithmetic.MarkerCounting.Cfg)
    (executed : BinaryStackArithmetic.MarkerCounting.step before = some after) :
    step (counterConfig base state before) = some (counterConfig base state after) := by
  apply step_embedStatement countKey Phase.count (.arrow .read) Control.counter
    (fun state value => {state with counter:=value}) countCells
    (fun value => {state with counter:=value}) (fun stored => contents (counterStorage base stored))
    (fun _ => rfl) (fun _ _ => rfl) (counter_read base) (counter_write base)
    BinaryStackArithmetic.MarkerCounting.program program before after (fun _ _ => rfl) executed

private def arrowStorage (base : Storage) (source : ∀ key, List (WordTemplateMachine.Wrapping.Alphabet (Γ:=Alphabet) key)) : Storage :=
  {base with arrowMarkers:=source .input,arrowClosing:=source .closing,typeScratch:=source .output,typeWord:=source .result}

def arrowConfig (base : Storage) (state : Control)
    (source : (WordTemplateMachine.Wrapping.machine arrowPrefix (encodeData (putTy dataType)) arrowSuffix).Cfg) : Cfg :=
  embeddedReturningConfig Phase.arrow .opening (fun value => {state with arrow:=value})
    (fun stored => contents (arrowStorage base stored)) source

private theorem arrow_read (base : Storage) (source : ∀ key, List (WordTemplateMachine.Wrapping.Alphabet (Γ:=Alphabet) key))
    (key : WordTemplateMachine.Wrapping.Stack) :
    contents (arrowStorage base source) (arrowKey key) = (source key).map (arrowCells key).mp := by
  cases key <;> change _ = List.map id _ <;> simp [contents,arrowStorage,arrowKey]

private theorem arrow_write (base : Storage) (source : ∀ key, List (WordTemplateMachine.Wrapping.Alphabet (Γ:=Alphabet) key))
    (key : WordTemplateMachine.Wrapping.Stack) (value : List (WordTemplateMachine.Wrapping.Alphabet (Γ:=Alphabet) key)) :
    contents (arrowStorage base (Function.update source key value)) =
      Function.update (contents (arrowStorage base source)) (arrowKey key) (value.map (arrowCells key).mp) := by
  cases key <;> funext target <;> cases target <;> simp [contents,arrowStorage,arrowKey,Function.update]
  all_goals change value = value.map id; simp

theorem arrow_step (base : Storage) (state : Control)
    (before after : (WordTemplateMachine.Wrapping.machine arrowPrefix (encodeData (putTy dataType)) arrowSuffix).Cfg)
    (executed : (WordTemplateMachine.Wrapping.machine arrowPrefix (encodeData (putTy dataType)) arrowSuffix).step before = some after) :
    step (arrowConfig base state before) = some (arrowConfig base state after) := by
  apply step_embedStatement arrowKey Phase.arrow .opening Control.arrow
    (fun state value => {state with arrow:=value}) arrowCells
    (fun value => {state with arrow:=value}) (fun stored => contents (arrowStorage base stored))
    (fun _ => rfl) (fun _ _ => rfl) (arrow_read base) (arrow_write base)
    (WordTemplateMachine.Wrapping.machine arrowPrefix (encodeData (putTy dataType)) arrowSuffix).m
    program before after (fun _ _ => rfl) executed

theorem opening_step (state : Control) (storage : Storage) :
    step (config (some .opening) state storage) =
      some (config (some .bits) state {storage with scratch:=Head.opening.reverse++storage.scratch}) := by
  simp only [step,program,config,TM2.step]
  rw [pushFixed_apply]
  rfl

theorem bits_cons (state : Control) (storage : Storage) (head : Bool) (tail : List Bool) (stored : storage.bits=head::tail) :
    step (config (some .bits) state storage) =
      some (config (some .bits) {state with bit:=some head}
        {storage with bits:=tail,scratch:=(digitImage head).reverse++storage.scratch}) := by
  have updated : Function.update (contents storage) .bits tail = contents {storage with bits:=tail} := by
    funext key; cases key <;> simp [contents,Function.update]
  simp only [step,program,config,TM2.step,TM2.stepAux,contents,stored,List.head?_cons,List.tail_cons]
  rw [updated]
  cases head <;> simp only [Option.isSome_some,Option.getD_some,Bool.cond_true,Bool.cond_false]
  all_goals rw [pushFixed_apply]; rfl

theorem bits_nil (state : Control) (storage : Storage) (empty : storage.bits=[]) :
    step (config (some .bits) state storage) =
      some (config (some .name) {state with bit:=none}
        {storage with scratch:=(encodeData (.atom 0)).reverse++storage.scratch}) := by
  have updated : Function.update (contents storage) .bits [] = contents storage := by
    funext key; cases key <;> simp [contents,Function.update,empty]
  simp only [step,program,config,TM2.step,TM2.stepAux,contents,empty,List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
  rw [updated,pushFixed_apply]
  simp only [TM2.stepAux]
  congr 1
  congr 1
  funext key; cases key <;> simp [contents,empty]

def components (bits : List Bool) : List Alphabet := bits.flatMap digitImage ++ encodeData (.atom 0)

def bitsRun (state : Control) (bits : List Bool) (storage : Storage) :
    EvalsToInTime step (config (some .bits) state {storage with bits:=bits})
      (some (config (some .name) {state with bit:=none}
        {storage with bits:=[],scratch:=(components bits).reverse++storage.scratch})) (bits.length+1) := by
  induction bits generalizing state storage with
  | nil => simpa only [components,List.flatMap_nil,List.nil_append,List.length_nil,Nat.zero_add] using
      oneStep (bits_nil state {storage with bits:=[]} rfl)
  | cons head tail ih =>
      have first := oneStep (bits_cons state {storage with bits:=head::tail} head tail rfl)
      have remaining := ih {state with bit:=some head}
        {storage with bits:=tail,scratch:=(digitImage head).reverse++storage.scratch}
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first remaining
      convert joined using 1
      all_goals simp only [components,List.flatMap_cons,List.reverse_append,List.append_assoc,List.length_cons]


def copyWord (typed : Bool) (storage : Storage) : List Alphabet := if typed then storage.typeWord else storage.name

def copyKey (typed : Bool) : Key := if typed then .typeWord else .name

def copyPhase (typed : Bool) : Phase := if typed then .typeWord else .name

def afterCopy (typed : Bool) : Phase := if typed then .reverse else .typeWord

def copySuffix (typed : Bool) : List Alphabet := if typed then [] else encodeData (.atom 0)

def copyStorage (typed : Bool) (storage : Storage) (word : List Alphabet) : Storage :=
  if typed then {storage with typeWord:=word} else {storage with name:=word}

theorem copy_cons (typed : Bool) (state : Control) (storage : Storage)
    (head : Alphabet) (tail : List Alphabet) (stored : copyWord typed storage=head::tail) :
    step (config (some (copyPhase typed)) state storage) =
      some (config (some (copyPhase typed)) {state with symbol:=some head}
        {copyStorage typed storage tail with scratch:=head::storage.scratch}) := by
  cases typed <;> simp [copyWord,copyPhase,copyStorage] at stored ⊢
  all_goals
    simp [step,program,config,TM2.step,TM2.stepAux,contents,stored]
    funext key
    cases key <;> simp [contents,Function.update]

theorem copy_nil (typed : Bool) (state : Control) (storage : Storage)
    (empty : copyWord typed storage=[]) :
    step (config (some (copyPhase typed)) state storage) =
      some (config (some (afterCopy typed)) {state with symbol:=none}
        {storage with scratch:=(copySuffix typed).reverse++storage.scratch}) := by
  cases typed <;> simp [copyWord,copyPhase,copySuffix,afterCopy] at empty ⊢
  · have updated : Function.update (contents storage) .name [] = contents storage := by
      funext key; cases key <;> simp [contents,Function.update,empty]
    simp only [step,program,config,TM2.step,TM2.stepAux,contents,empty,
      List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
    rw [updated,pushFixed_apply]
    simp only [TM2.stepAux]
    congr 1
    congr 1
    funext key; cases key <;> simp [contents,empty]
  · simp [step,program,config,contents,TM2.step,TM2.stepAux,empty]
    funext key; cases key <;> simp [contents,Function.update]

def copyRun (typed : Bool) (state : Control) (word : List Alphabet) (storage : Storage) :
    EvalsToInTime step (config (some (copyPhase typed)) state (copyStorage typed storage word))
      (some (config (some (afterCopy typed)) {state with symbol:=none}
        {copyStorage typed storage [] with scratch:=(word++copySuffix typed).reverse++storage.scratch}))
      (word.length+1) := by
  induction word generalizing state storage with
  | nil =>
      have empty : copyWord typed (copyStorage typed storage [])=[] := by cases typed <;> rfl
      have first := oneStep (copy_nil typed state (copyStorage typed storage []) empty)
      have unchanged : (copyStorage typed storage []).scratch=storage.scratch := by cases typed <;> rfl
      simpa only [List.nil_append,List.length_nil,Nat.zero_add,unchanged] using first
  | cons head tail ih =>
      have stored : copyWord typed (copyStorage typed storage (head::tail))=head::tail := by cases typed <;> rfl
      have first := oneStep (copy_cons typed state (copyStorage typed storage (head::tail)) head tail stored)
      have rest := ih {state with symbol:=some head}
        {copyStorage typed storage tail with scratch:=head::storage.scratch}
      have boundary : copyStorage typed {copyStorage typed storage tail with scratch:=head::storage.scratch} tail =
          {copyStorage typed (copyStorage typed storage (head::tail)) tail with scratch:=head::storage.scratch} := by
        cases typed <;> rfl
      rw [boundary] at rest
      have kept : (copyStorage typed storage (head::tail)).scratch=storage.scratch := by cases typed <;> rfl
      rw [kept] at first
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
      convert joined using 1
      · cases typed <;> simp [copyStorage,List.reverse_cons,List.append_assoc]
      · simp only [List.length_cons]

theorem reverse_cons (state : Control) (storage : Storage) (head : Alphabet) (tail : List Alphabet)
    (stored : storage.scratch=head::tail) :
    step (config (some .reverse) state storage) =
      some (config (some .reverse) {state with symbol:=some head}
        {storage with scratch:=tail,result:=head::storage.result}) := by
  simp [step,program,config,contents,TM2.step,TM2.stepAux,stored]
  funext key; cases key <;> simp [contents,Function.update]

theorem reverse_nil (state : Control) (storage : Storage) (empty : storage.scratch=[]) :
    step (config (some .reverse) state storage) = some (config none initial storage) := by
  simp [step,program,config,contents,TM2.step,TM2.stepAux,empty]

def reverseRun (state : Control) (word : List Alphabet) (storage : Storage) :
    EvalsToInTime step (config (some .reverse) state {storage with scratch:=word})
      (some (config none initial {storage with scratch:=[],result:=word.reverse++storage.result}))
      (word.length+1) := by
  induction word generalizing state storage with
  | nil => simpa only [List.length_nil,Nat.zero_add,List.reverse_nil,List.nil_append] using
      oneStep (reverse_nil state {storage with scratch:=[]} rfl)
  | cons head tail ih =>
      have first := oneStep (reverse_cons state {storage with scratch:=head::tail} head tail rfl)
      have rest := ih {state with symbol:=some head} {storage with scratch:=tail,result:=head::storage.result}
      have joined := EvalsToInTime.trans _ _ _ _ _ _ first rest
      convert joined using 1
      all_goals simp only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append]


theorem components_exact (arity : Nat) :
    components (BinaryStackArithmetic.naturalBits arity) =
      encodeWith (Codec.list Codec.string) (natComponents arity) := by
  rw [Binary.encodeWith_list]
  simp only [components,BinaryStackArithmetic.naturalBits,natComponents,
    Mettapedia.OSLF.MeTTaIL.PatternTokens.bits,List.flatMap_map]
  congr 1
  apply List.flatMap_congr
  intro digit member
  have bound := Nat.digits_lt_base (by decide : 1 < 2) member
  have cases : digit=0 ∨ digit=1 := by omega
  rcases cases with equal | equal <;> subst digit <;> simp [digitImage]

private theorem counter_config (base : Storage) (state : Control)
    (phase : Option BinaryStackArithmetic.MarkerCounting.Phase)
    (sourceState : BinaryStackArithmetic.MarkerCounting.Control) (markers : List Unit)
    (bits temporary : List Bool) :
    counterConfig base state (BinaryStackArithmetic.MarkerCounting.config phase sourceState markers bits temporary) =
      config (some (phase.elim (.arrow .read) Phase.count)) {state with counter:=sourceState}
        {base with countMarkers:=markers,bits:=bits,bitTemporary:=temporary} := rfl

private theorem arrow_config (base : Storage) (state : Control) (phase : Option ArrowPhase)
    (sourceState : WordTemplateMachine.Wrapping.State (Γ:=Alphabet)) (markers closing : List Unit)
    (scratch output : List Alphabet) :
    arrowConfig base state (WordTemplateMachine.Wrapping.config arrowPrefix (encodeData (putTy dataType)) arrowSuffix
      phase sourceState markers closing scratch output) =
      config (some (phase.elim .opening Phase.arrow)) {state with arrow:=sourceState}
        {base with arrowMarkers:=markers,arrowClosing:=closing,typeScratch:=scratch,typeWord:=output} := rfl

private theorem arrow_init (arity : Nat) :
    initList (WordTemplateMachine.Wrapping.machine arrowPrefix (encodeData (putTy dataType)) arrowSuffix)
      (List.replicate arity ()) =
      WordTemplateMachine.Wrapping.config arrowPrefix (encodeData (putTy dataType)) arrowSuffix
        (some .read) (false,none) (List.replicate arity ()) [] [] [] := by
  simp only [initList,WordTemplateMachine.Wrapping.machine,WordTemplateMachine.Wrapping.config]
  congr 1
  funext key; cases key <;> simp

private theorem arrow_halt (word : List Alphabet) :
    haltList (WordTemplateMachine.Wrapping.machine arrowPrefix (encodeData (putTy dataType)) arrowSuffix) word =
      WordTemplateMachine.Wrapping.config arrowPrefix (encodeData (putTy dataType)) arrowSuffix
        none (false,none) [] [] [] word := by
  simp only [haltList,WordTemplateMachine.Wrapping.machine,WordTemplateMachine.Wrapping.config]
  congr 1
  funext key; cases key <;> simp

def clock (name : String) (arity : Nat) : Nat :=
  arity+1 + (arity*(2*arity+4)+1) +
  (arity*(arrowPrefix.length+arrowSuffix.length+4)+(encodeData (putTy dataType)).length+
    (encodeWith tyCodec (dataArrow arity)).length+4) + 1 +
  ((BinaryStackArithmetic.naturalBits arity).length+1)+
  ((encodeWith Codec.string name).length+1)+
  ((encodeWith tyCodec (dataArrow arity)).length+1)+
  ((termWire (constructorTerm name arity)).length+1)

set_option maxRecDepth 4096 in
/-- Both actual original programs consume the discovered marker copies.
The emitted head retains the authored name, computed binary arity namespace,
complete curried type and original undefined provenance. -/
noncomputable def run (name : String) (arity : Nat) :
    EvalsToInTime step
      (config (some .fork) initial {input:=List.replicate arity (),name:=encodeWith Codec.string name})
      (some (config none initial {result:=termWire (constructorTerm name arity)})) (clock name arity) := by
  let nameWord := encodeWith Codec.string name
  let typeWord := encodeWith tyCodec (dataArrow arity)
  let bits := BinaryStackArithmetic.naturalBits arity
  let storage0 : Storage := {name:=nameWord}
  let storage1 : Storage := {name:=nameWord,arrowMarkers:=List.replicate arity ()}
  let storage2 : Storage := {name:=nameWord,bits:=bits}
  let storage3 : Storage := {name:=nameWord,bits:=bits,typeWord:=typeWord}
  have forked := forkRun initial (List.replicate arity ()) storage0
  simp only [List.reverse_replicate] at forked
  have counted := lift_execution BinaryStackArithmetic.MarkerCounting.step step
    (counterConfig storage1 initial) (counter_step storage1 initial)
    (BinaryStackArithmetic.MarkerCounting.countRun (List.replicate arity ()) 0 none)
  rw [counter_config,counter_config] at counted
  simp only [Option.elim_some,Option.elim_none,List.length_replicate,Nat.zero_add,
    BinaryStackArithmetic.naturalBits,Nat.digits_zero,List.map_nil] at counted
  have arrowedSource := dataArrowOutputs arity
  change EvalsToInTime
    (WordTemplateMachine.Wrapping.machine arrowPrefix (encodeData (putTy dataType)) arrowSuffix).step
    (initList (WordTemplateMachine.Wrapping.machine arrowPrefix (encodeData (putTy dataType)) arrowSuffix) (List.replicate arity ()))
    (some (haltList (WordTemplateMachine.Wrapping.machine arrowPrefix (encodeData (putTy dataType)) arrowSuffix) typeWord)) _ at arrowedSource
  rw [arrow_init,arrow_halt] at arrowedSource
  have arrowed := lift_execution _ step (arrowConfig storage2 initial) (arrow_step storage2 initial) arrowedSource
  rw [arrow_config,arrow_config] at arrowed
  simp only [Option.elim_some,Option.elim_none] at arrowed
  have headOpening :=  oneStep (opening_step initial storage3)
  have bitRun := bitsRun initial bits {storage3 with scratch:=Head.opening.reverse}
  have nameRun := copyRun false {initial with bit:=none} nameWord
    {storage3 with bits:=[],scratch:=(components bits).reverse++Head.opening.reverse}
  have typeRun := copyRun true {initial with bit:=none,symbol:=none} typeWord
    {storage3 with bits:=[],name:=[],scratch:=(nameWord++encodeData (.atom 0)).reverse++((components bits).reverse++Head.opening.reverse)}
  simp [copyStorage,copyPhase,afterCopy,copySuffix] at nameRun typeRun
  have reverse := reverseRun {initial with bit:=none,symbol:=none}
    (typeWord.reverse++((nameWord++encodeData (.atom 0)).reverse++((components bits).reverse++Head.opening.reverse)))
    ({} : Storage)
  simp only [List.reverse_append,List.append_assoc] at reverse
  have first : EvalsToInTime step
      (config (some .fork) initial {input:=List.replicate arity (),name:=nameWord})
      (some (config (some (.count .count)) initial {name:=nameWord,countMarkers:=List.replicate arity (),arrowMarkers:=List.replicate arity ()})) (arity+1) := by
    simpa only [storage0,List.length_replicate,List.append_nil] using forked
  have counted' : EvalsToInTime step
      (config (some (.count .count)) initial {name:=nameWord,countMarkers:=List.replicate arity (),arrowMarkers:=List.replicate arity ()})
      (some (config (some (.arrow .read)) initial {name:=nameWord,bits:=bits,arrowMarkers:=List.replicate arity ()})) (arity*(2*arity+4)+1) := by
    simpa only [storage1,initial,bits,BinaryStackArithmetic.MarkerCounting.initial,BinaryStackArithmetic.naturalBits] using counted
  have arrowed' : EvalsToInTime step
      (config (some (.arrow .read)) initial {name:=nameWord,bits:=bits,arrowMarkers:=List.replicate arity ()})
      (some (config (some .opening) initial storage3))
      (arity*(arrowPrefix.length+arrowSuffix.length+4)+(encodeData (putTy dataType)).length+typeWord.length+4) := by
    simpa only [storage2,storage3,initial,typeWord] using arrowed
  have first := EvalsToInTime.trans _ _ _ _ _ _ first counted'
  have first := EvalsToInTime.trans _ _ _ _ _ _ first arrowed'
  have first := EvalsToInTime.trans _ _ _ _ _ _ first headOpening
  have first := EvalsToInTime.trans _ _ _ _ _ _ first bitRun
  have first := EvalsToInTime.trans _ _ _ _ _ _ first nameRun
  have first := EvalsToInTime.trans _ _ _ _ _ _ first typeRun
  have first := EvalsToInTime.trans _ _ _ _ _ _ first reverse
  have headEq :
      (typeWord.reverse++((nameWord++encodeData (.atom 0)).reverse++((components bits).reverse++Head.opening.reverse))).reverse =
        termWire (constructorTerm name arity) := by
    rw [List.reverse_append,List.reverse_append,List.reverse_append,List.reverse_reverse,
      List.reverse_reverse,List.reverse_reverse,List.reverse_reverse,components_exact,Head.constructor_wire]
    simp only [nameWord,typeWord,List.append_assoc]
  simp only [List.reverse_append,List.reverse_reverse,List.append_assoc] at headEq
  simp only [List.reverse_reverse,List.append_nil] at first
  rw [headEq] at first
  have lengthEq := congrArg List.length headEq
  simp only [nameWord,typeWord,bits,List.length_append] at lengthEq
  convert first using 1
  simp only [clock,nameWord,typeWord,bits,List.length_append,List.length_reverse]
  omega

theorem digitImage_length (bit : Bool) :
    (digitImage bit).length = (digitImage false).length := by
  cases bit <;> rfl

theorem components_length (bits : List Bool) :
    (components bits).length = bits.length * (digitImage false).length +
      (encodeData (.atom 0)).length := by
  induction bits with
  | nil => simp [components]
  | cons head tail ih =>
      simp only [components,List.flatMap_cons,List.length_append] at ih ⊢
      rw [digitImage_length]
      simp only [List.length_cons]
      nlinarith

theorem constructor_length (name : String) (arity : Nat) :
    (termWire (constructorTerm name arity)).length =
      Head.opening.length + (BinaryStackArithmetic.naturalBits arity).length *
        (digitImage false).length + 2 * (encodeData (.atom 0)).length +
      (encodeWith Codec.string name).length + (encodeWith tyCodec (dataArrow arity)).length := by
  rw [Head.constructor_wire,←components_exact]
  simp only [List.length_append]
  rw [components_length]
  omega

/-- The head construction charges all marker scans and retained UTF-8 name,
binary namespace, curried type and original syntax bytes. -/
theorem clock_le (name : String) (arity : Nat) :
    clock name arity ≤ 2 * arity ^ 2 +
      (4 * (arrowPrefix.length + arrowSuffix.length) + (digitImage false).length + 10) * arity +
      2 * (encodeWith Codec.string name).length +
      4 * (encodeData (putTy dataType)).length + Head.opening.length +
      2 * (encodeData (.atom 0)).length + 11 := by
  have digits : (BinaryStackArithmetic.naturalBits arity).length ≤ arity := by
    rw [BinaryStackArithmetic.naturalBits,List.length_map]
    apply (Nat.digits_length_le_iff (by decide : 1 < 2) arity).mpr
    exact Nat.lt_two_pow_self
  simp only [clock,constructor_length,dataArrow_length]
  nlinarith

end Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Constructor.HeadFromMarkers

namespace Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Constructor.Completion
open Turing StateTransition
open Turing.TM2.Stmt
open Mettapedia.Computability
open Mettapedia.Computability.StackMachineRegisters
open Mettapedia.Computability.StackMachineComposition (oneStep lift_execution)
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability.WordTemplateMachine
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.InferenceStorageBounds
open Mettapedia.Languages.HOLLight.TemplateInstantiationMachine (termWire)

inductive Key where
  | saved (key : Continuation.Key)
  | head (key : HeadFromMarkers.Key)
  | children
  deriving DecidableEq, Fintype
abbrev Cells : Key → Type
  | .saved key => Continuation.Cells key
  | .head key => HeadFromMarkers.Cells key
  | .children => Option Alphabet
instance (key : Key) : Fintype (Cells key) := by cases key <;> infer_instance

inductive Phase where
  | name | children | markers
  | head (phase : HeadFromMarkers.Phase)
  | spine (phase : Spine.Phase)
  | done
  deriving DecidableEq, Fintype
structure Control where
  head : HeadFromMarkers.Control
  spine : Spine.Control
  cell : Option Continuation.Cell
  accepted : Bool
  deriving Fintype

def initial : Control := ⟨HeadFromMarkers.initial,none,none,true⟩

def spineKey : Spine.Stack → Key
  | .input => .children
  | .head => .head .result
  | .children => .head .typeWord
  | .openings => .head .typeScratch
  | .headMemo => .head .name
  | .result => .head .scratch
  | .markers => .head .input

theorem spineCells : ∀ key, Spine.StackAlphabet key = Cells (spineKey key) := by
  intro key; cases key <;> rfl

def program : Phase → TM2.Stmt Cells Phase Control
  | .name => pop (.saved (.local .name)) (fun state value => {state with cell:=value})
      (branch (fun state => state.cell.isSome)
        (branch (fun state => state.cell.join.isSome)
          (push (.head .name) (fun state => state.cell.join.getD 2) (goto fun _ => .name))
          (load (fun state => {state with accepted:=false}) halt))
        (load (fun state => {state with cell:=none}) (goto fun _ => .children)))
  | .children => pop (.saved (.local .children)) (fun state value => {state with cell:=value})
      (branch (fun state => state.cell.isSome)
        (push .children (fun state => state.cell.getD none) (goto fun _ => .children))
        (load (fun state => {state with cell:=none}) (goto fun _ => .markers)))
  | .markers => pop (.saved (.local .markers)) (fun state value => {state with cell:=value})
      (branch (fun state => state.cell.isSome)
        (branch (fun state => state.cell.join.isSome)
          (load (fun state => {state with accepted:=false}) halt)
          (push (.head .input) (fun _ => ()) (goto fun _ => .markers)))
        (load (fun _ => initial) (goto fun _ => .head .fork)))
  | .head phase => embedStatement Key.head Phase.head Control.head
      (fun state value => {state with head:=value}) (fun _ => rfl)
      (goto fun _ => .spine .scan) (HeadFromMarkers.program phase)
  | .spine phase => embedStatement spineKey Phase.spine Control.spine
      (fun state value => {state with spine:=value}) spineCells (goto fun _ => .done) (Spine.program phase)
  | .done => halt

abbrev Cfg := TM2.Cfg Cells Phase Control
def step : Cfg → Option Cfg := TM2.step program

structure Storage where
  locals : Continuation.Arena → List Continuation.Cell := fun _ => []
  frames : Continuation.Arena → List (Option Continuation.Cell) := fun _ => []
  head : HeadFromMarkers.Storage := {}
  children : List (Option Alphabet) := []

def contents (storage : Storage) : ∀ key, List (Cells key)
  | .saved (.local arena) => storage.locals arena
  | .saved (.frames arena) => storage.frames arena
  | .head key => HeadFromMarkers.contents storage.head key
  | .children => storage.children

def config (phase : Option Phase) (state : Control) (storage : Storage) : Cfg := ⟨phase,state,contents storage⟩

theorem name_cons (state : Control) (storage : Storage) (symbol : Alphabet)
    (tail : List Continuation.Cell) (stored : storage.locals .name=some symbol::tail) :
    step (config (some .name) state storage) =
      some (config (some .name) {state with cell:=some (some symbol)}
        {storage with locals:=Function.update storage.locals .name tail,head:={storage.head with name:=symbol::storage.head.name}}) := by
  simp [step,program,config,contents,TM2.step,TM2.stepAux,stored]
  funext key; cases key with
  | saved key => cases key with
    | «local» arena => cases arena <;> simp [contents,Function.update]
    | frames arena => cases arena <;> simp [contents,Function.update]
  | head key => cases key <;> simp [contents,HeadFromMarkers.contents,Function.update]
  | children => simp [contents,Function.update]

theorem name_nil (state : Control) (storage : Storage) (empty : storage.locals .name=[]) :
    step (config (some .name) state storage) =
      some (config (some .children) {state with cell:=none} storage) := by
  simp [step,program,config,contents,TM2.step,TM2.stepAux,empty]

theorem children_cons (state : Control) (storage : Storage) (symbol : Continuation.Cell)
    (tail : List Continuation.Cell) (stored : storage.locals .children=symbol::tail) :
    step (config (some .children) state storage) =
      some (config (some .children) {state with cell:=some symbol}
        {storage with locals:=Function.update storage.locals .children tail,children:=symbol::storage.children}) := by
  simp [step,program,config,contents,TM2.step,TM2.stepAux,stored]
  funext key; cases key with
  | saved key => cases key with
    | «local» arena => cases arena <;> simp [contents,Function.update]
    | frames arena => cases arena <;> simp [contents,Function.update]
  | head key => cases key <;> simp [contents,Function.update]
  | children => simp [contents,Function.update]

theorem children_nil (state : Control) (storage : Storage) (empty : storage.locals .children=[]) :
    step (config (some .children) state storage) =
      some (config (some .markers) {state with cell:=none} storage) := by
  simp [step,program,config,contents,TM2.step,TM2.stepAux,empty]

theorem markers_cons (state : Control) (storage : Storage)
    (tail : List Continuation.Cell) (stored : storage.locals .markers=none::tail) :
    step (config (some .markers) state storage) =
      some (config (some .markers) {state with cell:=some none}
        {storage with locals:=Function.update storage.locals .markers tail,head:={storage.head with input:=()::storage.head.input}}) := by
  simp [step,program,config,contents,TM2.step,TM2.stepAux,stored]
  funext key; cases key with
  | saved key => cases key with
    | «local» arena => cases arena <;> simp [contents,Function.update]
    | frames arena => cases arena <;> simp [contents,Function.update]
  | head key => cases key <;> simp [contents,HeadFromMarkers.contents,Function.update]
  | children => simp [contents,Function.update]

theorem markers_nil (state : Control) (storage : Storage) (empty : storage.locals .markers=[]) :
    step (config (some .markers) state storage) =
      some (config (some (.head .fork)) initial storage) := by
  simp [step,program,config,contents,TM2.step,TM2.stepAux,empty]

noncomputable def nameRun (word : List Alphabet) (state : Control) (storage : Storage) :
    EvalsToInTime step
      (config (some .name) state {storage with locals:=Function.update storage.locals .name (word.map some)})
      (some (config (some .children) {state with cell:=none}
        {storage with locals:=Function.update storage.locals .name [],head:={storage.head with name:=word.reverse++storage.head.name}})) (word.length+1) := by
  induction word generalizing state storage with
  | nil => simpa using oneStep (name_nil state {storage with locals:=Function.update storage.locals .name []} (by simp))
  | cons head tail ih =>
    have first:=oneStep (name_cons state {storage with locals:=Function.update storage.locals .name ((head::tail).map some)} head (tail.map some) (by simp))
    have rest:=ih {state with cell:=some (some head)}
      {storage with locals:=Function.update storage.locals .name (tail.map some),head:={storage.head with name:=head::storage.head.name}}
    dsimp only at first rest
    simp only [Function.update_idem] at first rest
    have joined:=EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [Function.update_idem,List.length_cons,List.reverse_cons,List.map_cons,List.append_assoc,List.singleton_append] using joined

noncomputable def childrenRun (word : List Continuation.Cell) (state : Control) (storage : Storage) :
    EvalsToInTime step
      (config (some .children) state {storage with locals:=Function.update storage.locals .children word})
      (some (config (some .markers) {state with cell:=none}
        {storage with locals:=Function.update storage.locals .children [],children:=word.reverse++storage.children})) (word.length+1) := by
  induction word generalizing state storage with
  | nil => simpa using oneStep (children_nil state {storage with locals:=Function.update storage.locals .children []} (by simp))
  | cons head tail ih =>
    have first:=oneStep (children_cons state {storage with locals:=Function.update storage.locals .children (head::tail)} head tail (by simp))
    have rest:=ih {state with cell:=some head} {storage with locals:=Function.update storage.locals .children tail,children:=head::storage.children}
    dsimp only at first rest
    simp only [Function.update_idem] at first rest
    have joined:=EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [Function.update_idem,List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append,Nat.add_assoc,Nat.add_comm] using joined

noncomputable def markersRun (count : Nat) (state : Control) (storage : Storage) :
    EvalsToInTime step
      (config (some .markers) state {storage with locals:=Function.update storage.locals .markers (List.replicate count none)})
      (some (config (some (.head .fork)) initial
        {storage with locals:=Function.update storage.locals .markers [],head:={storage.head with input:=List.replicate count ()++storage.head.input}})) (count+1) := by
  induction count generalizing state storage with
  | zero => simpa using oneStep (markers_nil state {storage with locals:=Function.update storage.locals .markers []} (by simp))
  | succ count ih =>
    have first:=oneStep (markers_cons state {storage with locals:=Function.update storage.locals .markers (List.replicate (count+1) none)} (List.replicate count none) (by simp [List.replicate_succ]))
    have rest:=ih {state with cell:=some none}
      {storage with locals:=Function.update storage.locals .markers (List.replicate count none),head:={storage.head with input:=()::storage.head.input}}
    dsimp only at first rest
    simp only [Function.update_idem] at first rest
    have joined:=EvalsToInTime.trans _ _ _ _ _ _ first rest
    simpa only [Function.update_idem,List.replicate_succ',List.length_cons,List.append_assoc,List.singleton_append] using joined

def headContents (storage : Storage) (original : ∀ key,List (HeadFromMarkers.Cells key)) :
    ∀ key,List (Cells key)
  | .saved (.local arena) => storage.locals arena
  | .saved (.frames arena) => storage.frames arena
  | .head key => original key
  | .children => storage.children

def headConfig (state : Control) (storage : Storage) (original : HeadFromMarkers.Cfg) : Cfg :=
  embeddedReturningConfig Phase.head (.spine .scan) (fun value=>{state with head:=value})
    (headContents storage) original

theorem head_step (state : Control) (storage : Storage) (before after : HeadFromMarkers.Cfg)
    (executed : HeadFromMarkers.step before=some after) :
    step (headConfig state storage before)=some (headConfig state storage after) := by
  apply step_embedStatement Key.head Phase.head (.spine .scan) Control.head
    (fun state value=>{state with head:=value}) (fun _=>rfl)
    (fun value=>{state with head:=value}) (headContents storage) (fun _=>rfl) (fun _ _=>rfl) ?_ ?_
    HeadFromMarkers.program program before after ?_ ?_
  · intro original key
    change original key=List.map id (original key)
    simp
  · intro original key value
    change headContents storage (Function.update original key value)=
      Function.update (headContents storage original) (.head key) (value.map id)
    simp only [List.map_id]
    funext target
    cases target with
    | saved target => cases target <;> simp [headContents,Function.update]
    | children => simp [headContents,Function.update]
    | head target => cases key <;> cases target <;> simp [headContents,Function.update]
  · intro label present; rfl
  · exact executed

theorem head_config (state : Control) (storage : Storage) (phase : Option HeadFromMarkers.Phase)
    (register : HeadFromMarkers.Control) (stored : HeadFromMarkers.Storage) :
    headConfig state storage (HeadFromMarkers.config phase register stored)=
      config (some (phase.elim (.spine .scan) Phase.head)) {state with head:=register}
        {storage with head:=stored} := by
  rfl

def spineContents (storage : Storage) (original : ∀ key,List (Spine.StackAlphabet key)) :
    ∀ key,List (Cells key)
  | .saved (.local arena) => storage.locals arena
  | .saved (.frames arena) => storage.frames arena
  | .children => original .input
  | .head .input => original .markers
  | .head .result => original .head
  | .head .typeWord => original .children
  | .head .typeScratch => original .openings
  | .head .name => original .headMemo
  | .head .scratch => original .result
  | .head .countMarkers => storage.head.countMarkers
  | .head .arrowMarkers => storage.head.arrowMarkers
  | .head .arrowClosing => storage.head.arrowClosing
  | .head .bits => storage.head.bits
  | .head .bitTemporary => storage.head.bitTemporary

def spineConfig (state : Control) (storage : Storage) (original : Spine.Cfg) : Cfg :=
  embeddedReturningConfig Phase.spine .done (fun value=>{state with spine:=value})
    (spineContents storage) original

theorem spine_read (storage : Storage) (original : ∀ key,List (Spine.StackAlphabet key))
    (key : Spine.Stack) :
    spineContents storage original (spineKey key) = (original key).map (spineCells key).mp := by
  cases key <;> change _ = List.map id _ <;> simp [spineContents,spineKey]

theorem spine_write (storage : Storage) (original : ∀ key,List (Spine.StackAlphabet key))
    (key : Spine.Stack) (value : List (Spine.StackAlphabet key)) :
    spineContents storage (Function.update original key value)=
      Function.update (spineContents storage original) (spineKey key) (value.map (spineCells key).mp) := by
  cases key with
  | input =>
    change spineContents storage (Function.update original .input value) = Function.update (spineContents storage original) (.children) (value.map id)
    simp only [List.map_id]
    funext target
    cases target with
    | saved target => cases target <;> simp [spineContents,Function.update]
    | children => simp [spineContents,Function.update]
    | head target => cases target <;> simp [spineContents,Function.update]
  | head =>
    change spineContents storage (Function.update original .head value) = Function.update (spineContents storage original) (.head .result) (value.map id)
    simp only [List.map_id]
    funext target
    cases target with
    | saved target => cases target <;> simp [spineContents,Function.update]
    | children => simp [spineContents,Function.update]
    | head target => cases target <;> simp [spineContents,Function.update]
  | children =>
    change spineContents storage (Function.update original .children value) = Function.update (spineContents storage original) (.head .typeWord) (value.map id)
    simp only [List.map_id]
    funext target
    cases target with
    | saved target => cases target <;> simp [spineContents,Function.update]
    | children => simp [spineContents,Function.update]
    | head target => cases target <;> simp [spineContents,Function.update]
  | openings =>
    change spineContents storage (Function.update original .openings value) = Function.update (spineContents storage original) (.head .typeScratch) (value.map id)
    simp only [List.map_id]
    funext target
    cases target with
    | saved target => cases target <;> simp [spineContents,Function.update]
    | children => simp [spineContents,Function.update]
    | head target => cases target <;> simp [spineContents,Function.update]
  | headMemo =>
    change spineContents storage (Function.update original .headMemo value) = Function.update (spineContents storage original) (.head .name) (value.map id)
    simp only [List.map_id]
    funext target
    cases target with
    | saved target => cases target <;> simp [spineContents,Function.update]
    | children => simp [spineContents,Function.update]
    | head target => cases target <;> simp [spineContents,Function.update]
  | result =>
    change spineContents storage (Function.update original .result value) = Function.update (spineContents storage original) (.head .scratch) (value.map id)
    simp only [List.map_id]
    funext target
    cases target with
    | saved target => cases target <;> simp [spineContents,Function.update]
    | children => simp [spineContents,Function.update]
    | head target => cases target <;> simp [spineContents,Function.update]
  | markers =>
    change spineContents storage (Function.update original .markers value) = Function.update (spineContents storage original) (.head .input) (value.map id)
    simp only [List.map_id]
    funext target
    cases target with
    | saved target => cases target <;> simp [spineContents,Function.update]
    | children => simp [spineContents,Function.update]
    | head target => cases target <;> simp [spineContents,Function.update]

theorem spine_step (state : Control) (storage : Storage) (before after : Spine.Cfg)
    (executed : Spine.step before=some after) :
    step (spineConfig state storage before)=some (spineConfig state storage after) := by
  apply step_embedStatement spineKey Phase.spine .done Control.spine
    (fun state value=>{state with spine:=value}) spineCells
    (fun value=>{state with spine:=value}) (spineContents storage) (fun _=>rfl) (fun _ _=>rfl)
    (spine_read storage) (spine_write storage) Spine.program program before after ?_ executed
  intro label present; rfl

theorem spine_config (state : Control) (storage : Storage) (phase : Option Spine.Phase)
    (register : Spine.Control) (input : List (Option Alphabet))
    (head children openings headMemo result : List Alphabet) (markers : List Unit) :
    spineConfig state storage (Spine.config phase register input head children openings headMemo result markers)=
      config (some (phase.elim .done Phase.spine)) {state with spine:=register}
        {storage with children:=input,head:={storage.head with input:=markers,result:=head,typeWord:=children,typeScratch:=openings,name:=headMemo,scratch:=result}} := by
  simp only [spineConfig,embeddedReturningConfig,Spine.config,config]
  congr 1
  funext key
  cases key with
  | saved key => cases key <;> rfl
  | children => rfl
  | head key => cases key <;> rfl

theorem done_step (state : Control) (storage : Storage) :
    step (config (some .done) state storage)=some (config none state storage) := rfl

def storedLocals (name : String) (words : List (List Alphabet)) : Continuation.Arena → List Continuation.Cell
  | .name => (encodeWith Codec.string name).reverse.map some
  | .children => (Indexed.frame words).reverse
  | .markers => List.replicate words.length none

def clock (name : String) (words : List (List Alphabet)) : Nat :=
  (encodeWith Codec.string name).length+(Indexed.frame words).length+words.length+3+
    HeadFromMarkers.clock name words.length+
    Spine.clock (termWire (constructorTerm name words.length)) words+1

set_option maxRecDepth 4096 in
/-- Complete one constructor from its physically captured current arenas.
The caller's saved frames survive unchanged. Equal children remain separate
ordered words and contribute separate count markers. -/
noncomputable def run (name : String) (words : List (List Alphabet))
    (frames : Continuation.Arena → List (Option Continuation.Cell)) :
    EvalsToInTime step
      (config (some .name) initial {locals:=storedLocals name words,frames:=frames})
      (some (config none initial {frames:=frames,head:={input:=List.replicate words.length (),scratch:=Spine.output (termWire (constructorTerm name words.length)) words}}))
      (clock name words) := by
  let nameWord:=encodeWith Codec.string name
  let childWord:=Indexed.frame words
  let headWord:=termWire (constructorTerm name words.length)
  let locals0 : Continuation.Arena → List Continuation.Cell := fun arena=>match arena with
    | .name => [] | .children=>childWord.reverse | .markers=>List.replicate words.length none
  let locals1 : Continuation.Arena → List Continuation.Cell := fun arena=>match arena with
    | .name => [] | .children=>[] | .markers=>List.replicate words.length none
  let storage0 : Storage := {locals:=locals0,frames:=frames}
  let storage1 : Storage := {locals:=locals0,frames:=frames,head:={name:=nameWord}}
  let storage2 : Storage := {locals:=locals1,frames:=frames,head:={name:=nameWord},children:=childWord}
  let storage3 : Storage := {frames:=frames,head:={name:=nameWord,input:=List.replicate words.length ()},children:=childWord}
  have named:=nameRun nameWord.reverse initial storage0
  have children:=childrenRun childWord.reverse initial storage1
  have marked:=markersRun words.length initial storage2
  have namesEq : Function.update locals0 .name (nameWord.reverse.map some)=storedLocals name words := by
    funext arena; cases arena <;> simp [locals0,storedLocals,nameWord,childWord,Function.update]
  have namesClear : Function.update locals0 .name []=locals0 := by
    funext arena; cases arena <;> simp [locals0,Function.update]
  have childrenEq : Function.update locals0 .children childWord.reverse=locals0 := by
    funext arena; cases arena <;> simp [locals0,Function.update]
  have childrenClear : Function.update locals0 .children []=locals1 := by
    funext arena; cases arena <;> simp [locals0,locals1,Function.update]
  have markersEq : Function.update locals1 .markers (List.replicate words.length none)=locals1 := by
    funext arena; cases arena <;> simp [locals1,Function.update]
  have markersClear : Function.update locals1 .markers []=(fun _=>[]) := by
    funext arena; cases arena <;> simp [locals1,Function.update]
  dsimp only [storage0] at named
  rw [namesEq,namesClear] at named
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at named
  dsimp only [storage1] at children
  rw [childrenEq,childrenClear] at children
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at children
  dsimp only [storage2] at marked
  rw [markersEq,markersClear] at marked
  simp only [List.append_nil] at marked
  change EvalsToInTime step (config (some .name) initial {locals:=storedLocals name words,frames:=frames})
    (some (config (some .children) initial storage1)) (nameWord.length+1) at named
  change EvalsToInTime step (config (some .children) initial storage1)
    (some (config (some .markers) initial storage2)) (childWord.length+1) at children
  change EvalsToInTime step (config (some .markers) initial storage2)
    (some (config (some (.head .fork)) initial storage3)) (words.length+1) at marked
  have head:=lift_execution HeadFromMarkers.step step (headConfig initial storage3)
    (head_step initial storage3) (HeadFromMarkers.run name words.length)
  rw [head_config,head_config] at head
  simp only [Option.elim_some,Option.elim_none] at head
  change EvalsToInTime step (config (some (.head .fork)) initial storage3)
    (some (config (some (.spine .scan)) initial {frames:=frames,children:=childWord,head:={result:=headWord}})) _ at head
  let spineStorage : Storage := {frames:=frames,head:={result:=headWord}}
  have assembled:=lift_execution Spine.step step (spineConfig initial spineStorage)
    (spine_step initial spineStorage) (Spine.assemblyRun headWord words)
  change EvalsToInTime step
    (spineConfig initial spineStorage (Spine.config (some .scan) none childWord headWord [] [] [] [] [])) _ _ at assembled
  rw [spine_config,spine_config] at assembled
  simp only [Option.elim_some,Option.elim_none] at assembled
  change EvalsToInTime step
    (config (some (.spine .scan)) initial {frames:=frames,children:=childWord,head:={result:=headWord}})
    (some (config (some .done) initial {frames:=frames,head:={input:=List.replicate words.length (),scratch:=Spine.output headWord words}})) _ at assembled
  have finished:=oneStep (done_step initial {frames:=frames,head:={input:=List.replicate words.length (),scratch:=Spine.output headWord words}})
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ named children
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined marked
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined head
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined assembled
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined finished
  convert joined using 1
  simp only [clock,nameWord,childWord,headWord]
  omega

theorem clock_le (name : String) (words : List (List Alphabet)) :
    clock name words ≤ 2 * words.length ^ 2 +
      (12 * (arrowPrefix.length + arrowSuffix.length) +
        9 * (HeadFromMarkers.digitImage false).length + 11) * words.length +
      11 * (encodeWith Codec.string name).length + 9 * (Indexed.frame words).length +
      12 * (encodeData (Mettapedia.Languages.OpenTheory.SyntaxEncoding.putTy Mettapedia.Languages.HOLLight.InferenceHosting.dataType)).length +
      9 * Head.opening.length + 18 * (encodeData (.atom 0)).length + 20 := by
  have digits : (BinaryStackArithmetic.naturalBits words.length).length ≤ words.length := by
    rw [BinaryStackArithmetic.naturalBits,List.length_map]
    apply (Nat.digits_length_le_iff (by decide : 1<2) words.length).mpr
    exact Nat.lt_two_pow_self
  have headBound:=HeadFromMarkers.clock_le name words.length
  have spineBound:=Spine.clock_le (termWire (constructorTerm name words.length)) words
  rw [HeadFromMarkers.constructor_length,Constructor.dataArrow_length] at spineBound
  dsimp only [clock]
  nlinarith

theorem malformed_name_refused (state : Control) (storage : Storage) (tail : List Continuation.Cell)
    (stored : storage.locals .name=none::tail) :
    step (config (some .name) state storage)=
      some (config none {state with cell:=some none,accepted:=false}
        {storage with locals:=Function.update storage.locals .name tail}) := by
  simp [step,program,config,contents,TM2.step,TM2.stepAux,stored]
  funext key; cases key with
  | saved key => cases key with
    | «local» arena=>cases arena <;> simp [contents,Function.update]
    | frames arena=>cases arena <;> simp [contents,Function.update]
  | head key => cases key <;> simp [contents,Function.update]
  | children => simp [contents,Function.update]

theorem malformed_marker_refused (state : Control) (storage : Storage) (symbol : Alphabet)
    (tail : List Continuation.Cell) (stored : storage.locals .markers=some symbol::tail) :
    step (config (some .markers) state storage)=
      some (config none {state with cell:=some (some symbol),accepted:=false}
        {storage with locals:=Function.update storage.locals .markers tail}) := by
  simp [step,program,config,contents,TM2.step,TM2.stepAux,stored]
  funext key; cases key with
  | saved key => cases key with
    | «local» arena=>cases arena <;> simp [contents,Function.update]
    | frames arena=>cases arena <;> simp [contents,Function.update]
  | head key => cases key <;> simp [contents,Function.update]
  | children => simp [contents,Function.update]

/-- The completed constructor retains the original child ASTs and their
full codecs, including opaque source binders carried as literal data. -/
noncomputable def termRun (name : String) (arguments : List DBTerm)
    (frames : Continuation.Arena → List (Option Continuation.Cell)) :
    EvalsToInTime step
      (config (some .name) initial {locals:=storedLocals name (arguments.map termWire),frames:=frames})
      (some (config none initial {frames:=frames,head:={input:=List.replicate arguments.length (),scratch:=termWire (applyTerms (constructorTerm name arguments.length) arguments)}}))
      (clock name (arguments.map termWire)) := by
  have executed:=run name (arguments.map termWire) frames
  have outputEq : Spine.output (termWire (constructorTerm name arguments.length)) (arguments.map termWire)=
      termWire (applyTerms (constructorTerm name arguments.length) arguments) := by
    rw [applyTerms_wire]
    simp only [Spine.output,List.length_map,List.flatMap,List.append_assoc]
  simp only [List.length_map] at executed
  rw [outputEq] at executed
  exact executed

end Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Constructor.Completion

/-! The recursive consumer keeps unfinished constructors in owned physical
frames. It invokes the original completed constructor, literal, mapping,
cleanup and child-return operations. The call-site theorems below preserve
caller stacks and attach each operation's actual transition bound. -/

namespace Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Execution
open Turing StateTransition
open Turing.TM2.Stmt
open Mettapedia.Computability
open Mettapedia.Computability.StackMachineRegisters
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Languages.HOLLight.TemplateInstantiationMachine (termWire)
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.Languages.HOLLight.InferenceHosting
open Mettapedia.Languages.HOLLight.InferenceStorageBounds

inductive Key where
  | body (key : Constructor.Completion.Key)
  | input | result | returnWord | returnScratch
  deriving DecidableEq, Fintype
abbrev Cells : Key→Type
  | .body key=>Constructor.Completion.Cells key
  | .input=>Routing.Symbol
  | .result=>Alphabet
  | .returnWord | .returnScratch=>Continuation.Cell
instance (key : Key) : Fintype (Cells key) := by cases key <;> infer_instance

def headKeys : List Key := [
  .body (.head .input),.body (.head .countMarkers),.body (.head .arrowMarkers),.body (.head .arrowClosing),
  .body (.head .bits),.body (.head .bitTemporary),.body (.head .name),.body (.head .typeScratch),
  .body (.head .typeWord),.body (.head .scratch),.body (.head .result)]
def localClearKeys : List Key := headKeys++[.body .children,.returnScratch]
def clearKeys : List Key := localClearKeys++[
  .input,.returnWord,
  .body (.saved (.local .name)),.body (.saved (.local .children)),.body (.saved (.local .markers)),
  .body (.saved (.frames .name)),.body (.saved (.frames .children)),.body (.saved (.frames .markers))]

def wordImage (symbol : Alphabet) : List Continuation.Cell := [some symbol]
abbrev MapPhase := WordHomomorphismMachine.Phase (WordHomomorphismMachine.capacity wordImage)
def rootTemplate : WordTemplateMachine.Template Alphabet := [some 4,none]++(encodeData (putTy dataType)).map some

inductive Mode where
  | pending | constructor | literal
  deriving DecidableEq, BEq, Fintype
inductive Phase where
  | read | dispatch (symbol : Routing.Symbol)
  | save (phase : Continuation.Phase) | entered | clearPrelude
  | constructor (phase : Constructor.Completion.Phase) | constructorDone
  | opaquePrepare | opaque (phase : WordTemplateMachine.Phase HookLiteral.template.length)
  | map (literal : Bool) (phase : MapPhase)
  | localClear (index : Fin (localClearKeys.length+1))
  | returnChild (phase : ChildReturn.Phase) | returned
  | extract | rootBody | rootMarker | rootMarkerEnd | rootName
  | rootFrame (arena : Continuation.Arena)
  | wrap (phase : WordTemplateMachine.Phase rootTemplate.length)
  | refuseResult | cleanup (index : Fin (clearKeys.length+1))
  deriving DecidableEq, Fintype

structure Control where
  body : Constructor.Completion.Control
  continuation : Continuation.Control
  literal : Option Alphabet
  mapper : WordHomomorphismMachine.State (A:=Alphabet) (B:=Continuation.Cell)
  sweep : Unit×Bool
  mode : Mode
  command : Option Routing.Symbol
  cell : Option Continuation.Cell
  present : Bool
  accepted : Bool

private abbrev Registers := (Constructor.Completion.Control) × (Continuation.Control) × (Option Alphabet) × (WordHomomorphismMachine.State (A:=Alphabet) (B:=Continuation.Cell)) × (Unit×Bool) × (Mode) × (Option Routing.Symbol) × (Option Continuation.Cell) × (Bool) × (Bool)

set_option synthInstance.maxSize 1024 in
instance : Fintype Control := Fintype.ofEquiv Registers {
  toFun:=fun registers=>⟨registers.1,registers.2.1,registers.2.2.1,registers.2.2.2.1,registers.2.2.2.2.1,registers.2.2.2.2.2.1,registers.2.2.2.2.2.2.1,registers.2.2.2.2.2.2.2.1,registers.2.2.2.2.2.2.2.2.1,registers.2.2.2.2.2.2.2.2.2⟩
  invFun:=fun state=>(state.body,state.continuation,state.literal,state.mapper,state.sweep,state.mode,state.command,state.cell,state.present,state.accepted)
  left_inv:=by intro registers; rcases registers with ⟨body,continuation,literal,mapper,sweep,mode,command,cell,present,accepted⟩; rfl
  right_inv:=by intro state; cases state; rfl}

def initial : Control := ⟨Constructor.Completion.initial,WordFrame.initial,none,(none,none),((),false),.constructor,none,none,false,true⟩

def continuationKey (key : Continuation.Key) : Key := .body (.saved key)
def childReturnKey : Option Continuation.Key→Key
  | none=>.returnWord | some key=>continuationKey key

def literalKey : WordTemplateMachine.Stack→Key
  | .input=>.body (.head .name) | .temporary=>.body (.head .typeScratch) | .output=>.body (.head .scratch)
def rootKey : WordTemplateMachine.Stack→Key
  | .input=>.result | .temporary=>.body (.head .typeWord) | .output=>.body (.head .typeScratch)
def mapKey (literal : Bool) : WordHomomorphismMachine.Stack→Key
  | .input=>if literal then .body (.head .name) else .body (.head .scratch)
  | .output=>.returnScratch | .result=>.returnWord

theorem childReturnCells : ∀ key,ChildReturn.Cells key=Cells (childReturnKey key) := by
  intro key; cases key <;> rfl
theorem literalCells : ∀ key, Alphabet=Cells (literalKey key) := by intro key; cases key <;> rfl
theorem rootCells : ∀ key, Alphabet=Cells (rootKey key) := by intro key; cases key <;> rfl
theorem mapCells (literal : Bool) : ∀ key,
    WordHomomorphismMachine.Alphabet (A:=Alphabet) (B:=Continuation.Cell) key=Cells (mapKey literal key) := by
  intro key; cases key <;> cases literal <;> rfl

def fail : TM2.Stmt Cells Phase Control := load (fun state=>{state with accepted:=false}) (goto fun _=>.refuseResult)
def program : Phase→TM2.Stmt Cells Phase Control
  | .read=>pop .input (fun state value=>{state with command:=value})
      (branch (fun state=>state.command.isSome)
        (goto fun state=>.dispatch (state.command.getD .refused)) (goto fun _=>.extract))
  | .dispatch .start=>load (fun state=>{state with continuation:=WordFrame.initial})
      (goto fun _=>.save (.sub false .name .push))
  | .dispatch (.source symbol)=>branch (fun state=>state.mode != .constructor)
      (push (.body (.saved (.local .name))) (fun _=>some symbol) (goto fun _=>.read)) fail
  | .dispatch (.name symbol)=>branch (fun state=>state.mode==.constructor)
      (push (.body (.saved (.local .name))) (fun _=>some symbol) (goto fun _=>.read)) fail
  | .dispatch .constructor=>branch (fun state=>state.mode==.pending) (goto fun _=>.clearPrelude) fail
  | .dispatch .literal=>branch (fun state=>state.mode==.pending)
      (load (fun state=>{state with mode:=.literal}) (goto fun _=>.read)) fail
  | .dispatch .finish=>branch (fun state=>state.mode==.constructor)
      (load (fun state=>{state with body:=Constructor.Completion.initial}) (goto fun _=>.constructor .name))
      (branch (fun state=>state.mode==.literal) (goto fun _=>.opaquePrepare) fail)
  | .dispatch .refused=>fail
  | .save phase=>embedStatement continuationKey Phase.save Control.continuation
      (fun state value=>{state with continuation:=value}) (fun _=>rfl)
      (goto fun _=>.entered) (Continuation.program phase)
  | .entered=>branch (fun state=>state.continuation.2.2)
      (load (fun state=>{state with mode:=.pending,continuation:=WordFrame.initial}) (goto fun _=>.read)) fail
  | .clearPrelude=>pop (.body (.saved (.local .name))) (fun state value=>{state with present:=value.isSome})
      (branch Control.present (goto fun _=>.clearPrelude)
        (load (fun state=>{state with mode:=.constructor,present:=false}) (goto fun _=>.read)))
  | .constructor phase=>embedStatement Key.body Phase.constructor Control.body
      (fun state value=>{state with body:=value}) (fun _=>rfl)
      (goto fun _=>.constructorDone) (Constructor.Completion.program phase)
  | .constructorDone=>branch (fun state=>state.body.accepted)
      (load (fun state=>{state with mapper:=(none,none)}) (goto fun _=>.map false .read)) fail
  | .opaquePrepare=>pop (.body (.saved (.local .name))) (fun state value=>{state with cell:=value})
      (branch (fun state=>state.cell.isSome)
        (branch (fun state=>state.cell.join.isSome)
          (push (.body (.head .name)) (fun state=>state.cell.join.getD 2) (goto fun _=>.opaquePrepare)) fail)
        (load (fun state=>{state with cell:=none,literal:=none})
          (goto fun _=>.opaque (.emit ⟨0,by omega⟩))))
  | .opaque phase=>embedStatement literalKey Phase.opaque Control.literal
      (fun state value=>{state with literal:=value}) literalCells
      (load (fun state=>{state with mapper:=(none,none)}) (goto fun _=>.map true .read))
      (WordTemplateMachine.program HookLiteral.template phase)
  | .map literal phase=>embedStatement (mapKey literal) (Phase.map literal) Control.mapper
      (fun state value=>{state with mapper:=value}) (mapCells literal)
      (load (fun state=>{state with sweep:=((),false)}) (goto fun _=>.localClear ⟨0,by omega⟩))
      (WordHomomorphismMachine.program wordImage phase)
  | .localClear index=>embedStatement id Phase.localClear Control.sweep
      (fun state value=>{state with sweep:=value}) (fun _=>rfl)
      (load (fun state=>{state with continuation:=WordFrame.initial})
        (goto fun _=>.returnChild (.restore (.sub true .name .restore))))
      (StackMachineComposition.Sweep.program (Cells:=Cells) localClearKeys () index)
  | .returnChild phase=>embedStatement childReturnKey Phase.returnChild Control.continuation
      (fun state value=>{state with continuation:=value}) childReturnCells
      (goto fun _=>.returned) (ChildReturn.program phase)
  | .returned=>branch (fun state=>state.continuation.2.2)
      (load (fun _=>initial) (goto fun _=>.read)) fail
  | .extract=>pop (.body (.saved (.local .children))) (fun state value=>{state with cell:=value})
      (branch (fun state=>state.cell.isSome)
        (branch (fun state=>state.cell.join.isSome) fail (goto fun _=>.rootBody)) fail)
  | .rootBody=>pop (.body (.saved (.local .children))) (fun state value=>{state with cell:=value})
      (branch (fun state=>state.cell.isSome)
        (branch (fun state=>state.cell.join.isSome)
          (push .result (fun state=>state.cell.join.getD 2) (goto fun _=>.rootBody)) fail)
        (goto fun _=>.rootMarker))
  | .rootMarker=>pop (.body (.saved (.local .markers))) (fun state value=>{state with cell:=value})
      (branch (fun state=>state.cell.isSome)
        (branch (fun state=>state.cell.join.isSome) fail (goto fun _=>.rootMarkerEnd)) fail)
  | .rootMarkerEnd=>peek (.body (.saved (.local .markers))) (fun state value=>{state with present:=value.isSome})
      (branch Control.present fail (goto fun _=>.rootName))
  | .rootName=>peek (.body (.saved (.local .name))) (fun state value=>{state with present:=value.isSome})
      (branch Control.present fail (goto fun _=>.rootFrame .name))
  | .rootFrame arena=>peek (.body (.saved (.frames arena))) (fun state value=>{state with present:=value.isSome})
      (branch Control.present fail (match arena with
        | .name=>goto fun _=>.rootFrame .children
        | .children=>goto fun _=>.rootFrame .markers
        | .markers=>load (fun state=>{state with literal:=none}) (goto fun _=>.wrap (.emit ⟨0,by omega⟩))))
  | .wrap phase=>embedStatement rootKey Phase.wrap Control.literal
      (fun state value=>{state with literal:=value}) rootCells
      (load (fun state=>{state with sweep:=((),false)}) (goto fun _=>.cleanup ⟨0,by omega⟩))
      (WordTemplateMachine.program rootTemplate phase)
  | .refuseResult=>pop .result (fun state value=>{state with present:=value.isSome})
      (branch Control.present (goto fun _=>.refuseResult)
        (load (fun state=>{state with sweep:=((),false)}) (goto fun _=>.cleanup ⟨0,by omega⟩)))
  | .cleanup index=>embedStatement id Phase.cleanup Control.sweep
      (fun state value=>{state with sweep:=value}) (fun _=>rfl)
      (load (fun state=>{initial with accepted:=state.accepted}) halt)
      (StackMachineComposition.Sweep.program (Cells:=Cells) clearKeys () index)

abbrev Cfg:=TM2.Cfg Cells Phase Control
def step : Cfg→Option Cfg:=TM2.step program

def machine : FinTM2 where
  K:=Key
  k₀:=.input
  k₁:=.result
  Γ:=Cells
  Λ:=Phase
  main:=.read
  σ:=Control
  initialState:=initial
  m:=program

theorem machine_step : machine.step=step:=rfl

def config (phase : Option Phase) (state : Control) (commands : List Routing.Symbol)
    (body : ∀ key,List (Constructor.Completion.Cells key))
    (returnWord returnScratch : List Continuation.Cell) (result : List Alphabet) : Cfg :=
  ⟨phase,state,fun key=>match key with
    | .input=>commands | .result=>result
    | .returnWord=>returnWord | .returnScratch=>returnScratch | .body key=>body key⟩


/-- The constructor subroutine uses exactly its physical body arenas. -/
def bodySelect : Key → Option Constructor.Completion.Key
  | .body key => some key
  | _ => none

theorem body_select_sound (target : Key) (key : Constructor.Completion.Key)
    (selected : bodySelect target = some key) : Key.body key = target := by
  cases target <;> simp [bodySelect] at selected
  subst key
  rfl

theorem body_select_complete (key : Constructor.Completion.Key) : bodySelect (.body key) = some key := rfl

def bodyOverlay (base : ∀ key, List (Cells key)) :=
  Frame.overlay Key.body bodySelect body_select_sound (fun _ => rfl) base

def completionConfig (state : Control) (base : ∀ key,List (Cells key))
    (original : Constructor.Completion.Cfg) : Cfg :=
  embeddedContinuationConfig Phase.constructor
    (fun body => {state with body:=body}) (bodyOverlay base) (goto fun _=>.constructorDone) original

theorem completion_step (state : Control) (base : ∀ key,List (Cells key))
    (before after : Constructor.Completion.Cfg)
    (executed : Constructor.Completion.step before = some after) :
    step (completionConfig state base before) = some (completionConfig state base after) := by
  exact step_embedContinuation Key.body Phase.constructor (goto fun _=>.constructorDone)
    Control.body (fun state body => {state with body:=body}) (fun _=>rfl)
    (fun body => {state with body:=body}) (bodyOverlay base)
    (fun _=>rfl) (fun _ _=>rfl)
    (Frame.read Key.body bodySelect body_select_sound body_select_complete (fun _=>rfl) base)
    (Frame.write Key.body bodySelect body_select_sound body_select_complete (fun _=>rfl) base)
    Constructor.Completion.program program before after (fun _ _=>rfl) executed

/-- Actual completion retains the caller's input, result and child-return arenas.
Every child occurrence still contributes a physical marker and ordered word. -/
noncomputable def completionRun (state : Control) (base : ∀ key,List (Cells key))
    (name : String) (words : List (List Alphabet))
    (frames : Continuation.Arena → List (Option Continuation.Cell)) :
    EvalsToInTime step
      (completionConfig state base (Constructor.Completion.config (some .name)
        Constructor.Completion.initial {locals:=Constructor.Completion.storedLocals name words,frames:=frames}))
      (some (completionConfig state base (Constructor.Completion.config none
        Constructor.Completion.initial {
          frames:=frames
          head:={
            input:=List.replicate words.length ()
            scratch:=Constructor.Spine.output (termWire (constructorTerm name words.length)) words}})))
      (Constructor.Completion.clock name words) :=
  StackMachineComposition.lift_execution Constructor.Completion.step step (completionConfig state base)
    (completion_step state base) (Constructor.Completion.run name words frames)


def continuationSelect : Key → Option Continuation.Key
  | .body (.saved key) => some key
  | _ => none

theorem continuation_select_sound (target : Key) (key : Continuation.Key)
    (selected : continuationSelect target = some key) : continuationKey key = target := by
  cases target with
  | body body => cases body <;> simp [continuationSelect] at selected
                 subst key; rfl
  | input | result | returnWord | returnScratch => simp [continuationSelect] at selected

theorem continuation_select_complete (key : Continuation.Key) :
    continuationSelect (continuationKey key) = some key := rfl

def continuationOverlay (base : ∀ key,List (Cells key)) :=
  Frame.overlay continuationKey continuationSelect continuation_select_sound (fun _=>rfl) base

def saveConfig (state : Control) (base : ∀ key,List (Cells key)) (original : Continuation.Cfg) : Cfg :=
  embeddedContinuationConfig Phase.save (fun value=>{state with continuation:=value})
    (continuationOverlay base) (goto fun _=>.entered) original

theorem save_step (state : Control) (base : ∀ key,List (Cells key))
    (before after : Continuation.Cfg) (executed : Continuation.step before=some after) :
    step (saveConfig state base before)=some (saveConfig state base after) := by
  exact step_embedContinuation continuationKey Phase.save (goto fun _=>.entered)
    Control.continuation (fun state value=>{state with continuation:=value}) (fun _=>rfl)
    (fun value=>{state with continuation:=value}) (continuationOverlay base)
    (fun _=>rfl) (fun _ _=>rfl)
    (Frame.read continuationKey continuationSelect continuation_select_sound continuation_select_complete (fun _=>rfl) base)
    (Frame.write continuationKey continuationSelect continuation_select_sound continuation_select_complete (fun _=>rfl) base)
    Continuation.program program before after (fun _ _=>rfl) executed

noncomputable def saveRun (state : Control) (base : ∀ key,List (Cells key))
    (locals : Continuation.Arena → List Continuation.Cell)
    (frames : Continuation.Arena → List (Option Continuation.Cell)) :
    EvalsToInTime step
      (saveConfig state base (Continuation.config (some (.sub false .name .push)) WordFrame.initial locals frames))
      (some (saveConfig state base (Continuation.config none (none,none,true)
        (fun _=>[]) (Continuation.savedFrames locals frames))))
      ((locals .name).length+(locals .children).length+(locals .markers).length+9) :=
  StackMachineComposition.lift_execution Continuation.step step (saveConfig state base)
    (save_step state base) (Continuation.saveRun locals frames)

def childSelect : Key → Option (Option Continuation.Key)
  | .returnWord => some none
  | .body (.saved key) => some (some key)
  | _ => none

theorem child_select_sound (target : Key) (key : Option Continuation.Key)
    (selected : childSelect target = some key) : childReturnKey key = target := by
  cases target with
  | body body =>
      cases body <;> simp [childSelect] at selected
      subst key; rfl
  | returnWord => simp only [childSelect,Option.some.injEq] at selected; subst key; rfl
  | input | result | returnScratch => simp [childSelect] at selected

theorem child_select_complete (key : Option Continuation.Key) :
    childSelect (childReturnKey key)=some key := by cases key <;> rfl

def childOverlay (base : ∀ key,List (Cells key)) :=
  Frame.overlay childReturnKey childSelect child_select_sound childReturnCells base

def childConfig (state : Control) (base : ∀ key,List (Cells key)) (original : ChildReturn.Cfg) : Cfg :=
  embeddedContinuationConfig Phase.returnChild (fun value=>{state with continuation:=value})
    (childOverlay base) (goto fun _=>.returned) original

theorem child_step (state : Control) (base : ∀ key,List (Cells key))
    (before after : ChildReturn.Cfg) (executed : ChildReturn.step before=some after) :
    step (childConfig state base before)=some (childConfig state base after) := by
  exact step_embedContinuation childReturnKey Phase.returnChild (goto fun _=>.returned)
    Control.continuation (fun state value=>{state with continuation:=value}) childReturnCells
    (fun value=>{state with continuation:=value}) (childOverlay base)
    (fun _=>rfl) (fun _ _=>rfl)
    (Frame.read childReturnKey childSelect child_select_sound child_select_complete childReturnCells base)
    (Frame.write childReturnKey childSelect child_select_sound child_select_complete childReturnCells base)
    ChildReturn.program program before after (fun _ _=>rfl) executed

noncomputable def childRun (state : Control) (base : ∀ key,List (Cells key)) (word : List Alphabet)
    (locals : Continuation.Arena → List Continuation.Cell)
    (frames : Continuation.Arena → List (Option Continuation.Cell)) :
    EvalsToInTime step
      (childConfig state base (ChildReturn.config (some (.restore (.sub true .name .restore)))
        WordFrame.initial (word.map some) (fun _=>[]) (Continuation.savedFrames locals frames)))
      (some (childConfig state base (ChildReturn.config none (none,none,true) []
        (ChildReturn.attachedLocals word locals) frames)))
      ((locals .name).length+(locals .children).length+(locals .markers).length+word.length+8) :=
  StackMachineComposition.lift_execution ChildReturn.step step (childConfig state base)
    (child_step state base) (ChildReturn.run word locals frames)


def mapSelect (literal : Bool) : Key → Option WordHomomorphismMachine.Stack
  | .body (.head .name) => if literal then some .input else none
  | .body (.head .scratch) => if literal then none else some .input
  | .returnScratch => some .output
  | .returnWord => some .result
  | _ => none

theorem map_select_sound (literal : Bool) (target : Key) (key : WordHomomorphismMachine.Stack)
    (selected : mapSelect literal target=some key) : mapKey literal key=target := by
  cases literal <;> cases target with
  | body body => cases body with
    | head head =>
        cases head <;> simp [mapSelect] at selected
        all_goals subst key; rfl
    | saved key | children => simp [mapSelect] at selected
  | input | result => simp [mapSelect] at selected
  | returnScratch | returnWord => simp only [mapSelect,Option.some.injEq] at selected; subst key; rfl

theorem map_select_complete (literal : Bool) (key : WordHomomorphismMachine.Stack) :
    mapSelect literal (mapKey literal key)=some key := by cases literal <;> cases key <;> rfl

def mapOverlay (literal : Bool) (base : ∀ key,List (Cells key)) :=
  Frame.overlay (mapKey literal) (mapSelect literal) (map_select_sound literal) (mapCells literal) base

def mapContinuation : TM2.Stmt Cells Phase Control :=
  load (fun state=>{state with sweep:=((),false)}) (goto fun _=>.localClear ⟨0,by omega⟩)

def mapConfig (literal : Bool) (state : Control) (base : ∀ key,List (Cells key))
    (original : (WordHomomorphismMachine.machine wordImage).Cfg) : Cfg :=
  embeddedContinuationConfig (Phase.map literal) (fun value=>{state with mapper:=value})
    (mapOverlay literal base) mapContinuation original

theorem map_step (literal : Bool) (state : Control) (base : ∀ key,List (Cells key))
    (before after : (WordHomomorphismMachine.machine wordImage).Cfg)
    (executed : (WordHomomorphismMachine.machine wordImage).step before=some after) :
    step (mapConfig literal state base before)=some (mapConfig literal state base after) := by
  exact step_embedContinuation (mapKey literal) (Phase.map literal) mapContinuation
    Control.mapper (fun state value=>{state with mapper:=value}) (mapCells literal)
    (fun value=>{state with mapper:=value}) (mapOverlay literal base)
    (fun _=>rfl) (fun _ _=>rfl)
    (Frame.read (mapKey literal) (mapSelect literal) (map_select_sound literal) (map_select_complete literal) (mapCells literal) base)
    (Frame.write (mapKey literal) (mapSelect literal) (map_select_sound literal) (map_select_complete literal) (mapCells literal) base)
    (WordHomomorphismMachine.program wordImage) program before after (fun _ _=>rfl) executed

noncomputable def mapRun (literal : Bool) (state : Control) (base : ∀ key,List (Cells key)) (word : List Alphabet) :
    EvalsToInTime step
      (mapConfig literal state base (initList (WordHomomorphismMachine.machine wordImage) word))
      (some (mapConfig literal state base (haltList (WordHomomorphismMachine.machine wordImage) (word.flatMap wordImage))))
      (2*word.length+2*(word.flatMap wordImage).length+2) :=
  StackMachineComposition.lift_execution (WordHomomorphismMachine.machine wordImage).step step
    (mapConfig literal state base) (map_step literal state base) (WordHomomorphismMachine.outputs wordImage word)


def literalSelect : Key → Option WordTemplateMachine.Stack
  | .body (.head .name) => some .input
  | .body (.head .typeScratch) => some .temporary
  | .body (.head .scratch) => some .output
  | _ => none

theorem literal_select_sound (target : Key) (key : WordTemplateMachine.Stack)
    (selected : literalSelect target=some key) : literalKey key=target := by
  cases target with
  | body body => cases body with
    | head head =>
        cases head <;> simp [literalSelect] at selected
        all_goals subst key; rfl
    | saved key | children => simp [literalSelect] at selected
  | input | result | returnScratch | returnWord => simp [literalSelect] at selected

theorem literal_select_complete (key : WordTemplateMachine.Stack) : literalSelect (literalKey key)=some key := by
  cases key <;> rfl

def literalOverlay (base : ∀ key,List (Cells key)) :=
  Frame.overlay literalKey literalSelect literal_select_sound literalCells base

def literalContinuation : TM2.Stmt Cells Phase Control :=
  load (fun state=>{state with mapper:=(none,none)}) (goto fun _=>.map true .read)

def literalConfig (state : Control) (base : ∀ key,List (Cells key))
    (original : (WordTemplateMachine.machine HookLiteral.template).Cfg) : Cfg :=
  embeddedContinuationConfig Phase.opaque (fun value=>{state with literal:=value})
    (literalOverlay base) literalContinuation original

theorem literal_step (state : Control) (base : ∀ key,List (Cells key))
    (before after : (WordTemplateMachine.machine HookLiteral.template).Cfg)
    (executed : (WordTemplateMachine.machine HookLiteral.template).step before=some after) :
    step (literalConfig state base before)=some (literalConfig state base after) := by
  exact step_embedContinuation literalKey Phase.opaque literalContinuation
    Control.literal (fun state value=>{state with literal:=value}) literalCells
    (fun value=>{state with literal:=value}) (literalOverlay base)
    (fun _=>rfl) (fun _ _=>rfl)
    (Frame.read literalKey literalSelect literal_select_sound literal_select_complete literalCells base)
    (Frame.write literalKey literalSelect literal_select_sound literal_select_complete literalCells base)
    (WordTemplateMachine.program HookLiteral.template) program before after (fun _ _=>rfl) executed

noncomputable def literalRun (state : Control) (base : ∀ key,List (Cells key)) (word : List Alphabet) :
    EvalsToInTime step
      (literalConfig state base (initList (WordTemplateMachine.machine HookLiteral.template) word))
      (some (literalConfig state base (haltList (WordTemplateMachine.machine HookLiteral.template)
        (WordTemplateMachine.instantiate HookLiteral.template word))))
      (4*(HookLiteral.template.length+1)*(word.length+1)) :=
  StackMachineComposition.lift_execution (WordTemplateMachine.machine HookLiteral.template).step step
    (literalConfig state base) (literal_step state base) (WordTemplateMachine.outputs HookLiteral.template word)

def clearContinuation : TM2.Stmt Cells Phase Control :=
  load (fun state=>{state with continuation:=WordFrame.initial})
    (goto fun _=>.returnChild (.restore (.sub true .name .restore)))

def clearConfig (state : Control)
    (original : StackMachineComposition.Sweep.Cfg (Cells:=Cells) (State:=Unit) localClearKeys) : Cfg :=
  embeddedContinuationConfig Phase.localClear (fun value=>{state with sweep:=value})
    id clearContinuation original

theorem clear_step (state : Control)
    (before after : StackMachineComposition.Sweep.Cfg (Cells:=Cells) (State:=Unit) localClearKeys)
    (executed : StackMachineComposition.Sweep.step localClearKeys () before=some after) :
    step (clearConfig state before)=some (clearConfig state after) := by
  exact step_embedContinuation id Phase.localClear clearContinuation
    Control.sweep (fun state value=>{state with sweep:=value}) (fun _=>rfl)
    (fun value=>{state with sweep:=value}) id
    (fun _=>rfl) (fun _ _=>rfl)
    (fun contents key=>by change contents key=(contents key).map id; simp)
    (fun contents key value=>by change Function.update contents key value=Function.update contents key (value.map id); simp)
    (StackMachineComposition.Sweep.program (Cells:=Cells) localClearKeys ()) program before after
    (fun _ _=>rfl) executed

noncomputable def clearRun (state : Control) (contents : ∀ key,List (Cells key)) :
    EvalsToInTime step
      (clearConfig state (StackMachineComposition.Sweep.config localClearKeys (some ⟨0,by omega⟩) ((),false) contents))
      (some (clearConfig state (StackMachineComposition.Sweep.config localClearKeys none ((),false)
        (StackMachineComposition.Sweep.clear contents localClearKeys))))
      (StackMachineComposition.Sweep.cost contents localClearKeys) :=
  StackMachineComposition.lift_execution (StackMachineComposition.Sweep.step localClearKeys ()) step
    (clearConfig state) (clear_step state) (StackMachineComposition.Sweep.run localClearKeys () [] localClearKeys (by simp) ((),false) contents)


def rootSelect : Key → Option WordTemplateMachine.Stack
  | .result => some .input
  | .body (.head .typeWord) => some .temporary
  | .body (.head .typeScratch) => some .output
  | _ => none

theorem root_select_sound (target : Key) (key : WordTemplateMachine.Stack)
    (selected : rootSelect target=some key) : rootKey key=target := by
  cases target with
  | body body => cases body with
    | head head =>
        cases head <;> simp [rootSelect] at selected
        all_goals subst key; rfl
    | saved key | children => simp [rootSelect] at selected
  | result => simp only [rootSelect,Option.some.injEq] at selected; subst key; rfl
  | input | returnScratch | returnWord => simp [rootSelect] at selected

theorem root_select_complete (key : WordTemplateMachine.Stack) : rootSelect (rootKey key)=some key := by
  cases key <;> rfl

def rootOverlay (base : ∀ key,List (Cells key)) :=
  Frame.overlay rootKey rootSelect root_select_sound rootCells base

def rootContinuation : TM2.Stmt Cells Phase Control :=
  load (fun state=>{state with sweep:=((),false)}) (goto fun _=>.cleanup ⟨0,by omega⟩)

def rootConfig (state : Control) (base : ∀ key,List (Cells key))
    (original : (WordTemplateMachine.machine rootTemplate).Cfg) : Cfg :=
  embeddedContinuationConfig Phase.wrap (fun value=>{state with literal:=value})
    (rootOverlay base) rootContinuation original

theorem root_step (state : Control) (base : ∀ key,List (Cells key))
    (before after : (WordTemplateMachine.machine rootTemplate).Cfg)
    (executed : (WordTemplateMachine.machine rootTemplate).step before=some after) :
    step (rootConfig state base before)=some (rootConfig state base after) := by
  exact step_embedContinuation rootKey Phase.wrap rootContinuation
    Control.literal (fun state value=>{state with literal:=value}) rootCells
    (fun value=>{state with literal:=value}) (rootOverlay base)
    (fun _=>rfl) (fun _ _=>rfl)
    (Frame.read rootKey rootSelect root_select_sound root_select_complete rootCells base)
    (Frame.write rootKey rootSelect root_select_sound root_select_complete rootCells base)
    (WordTemplateMachine.program rootTemplate) program before after (fun _ _=>rfl) executed

noncomputable def rootRun (state : Control) (base : ∀ key,List (Cells key)) (word : List Alphabet) :
    EvalsToInTime step
      (rootConfig state base (initList (WordTemplateMachine.machine rootTemplate) word))
      (some (rootConfig state base (haltList (WordTemplateMachine.machine rootTemplate)
        (WordTemplateMachine.instantiate rootTemplate word))))
      (4*(rootTemplate.length+1)*(word.length+1)) :=
  StackMachineComposition.lift_execution (WordTemplateMachine.machine rootTemplate).step step
    (rootConfig state base) (root_step state base) (WordTemplateMachine.outputs rootTemplate word)

def cleanupContinuation : TM2.Stmt Cells Phase Control :=
  load (fun state=>{initial with accepted:=state.accepted}) halt

def cleanupConfig (state : Control)
    (original : StackMachineComposition.Sweep.Cfg (Cells:=Cells) (State:=Unit) clearKeys) : Cfg :=
  embeddedContinuationConfig Phase.cleanup (fun value=>{state with sweep:=value})
    id cleanupContinuation original

theorem cleanup_step (state : Control)
    (before after : StackMachineComposition.Sweep.Cfg (Cells:=Cells) (State:=Unit) clearKeys)
    (executed : StackMachineComposition.Sweep.step clearKeys () before=some after) :
    step (cleanupConfig state before)=some (cleanupConfig state after) := by
  exact step_embedContinuation id Phase.cleanup cleanupContinuation
    Control.sweep (fun state value=>{state with sweep:=value}) (fun _=>rfl)
    (fun value=>{state with sweep:=value}) id
    (fun _=>rfl) (fun _ _=>rfl)
    (fun contents key=>by change contents key=(contents key).map id; simp)
    (fun contents key value=>by change Function.update contents key value=Function.update contents key (value.map id); simp)
    (StackMachineComposition.Sweep.program (Cells:=Cells) clearKeys ()) program before after
    (fun _ _=>rfl) executed

noncomputable def cleanupRun (state : Control) (contents : ∀ key,List (Cells key)) :
    EvalsToInTime step
      (cleanupConfig state (StackMachineComposition.Sweep.config clearKeys (some ⟨0,by omega⟩) ((),false) contents))
      (some (cleanupConfig state (StackMachineComposition.Sweep.config clearKeys none ((),false)
        (StackMachineComposition.Sweep.clear contents clearKeys))))
      (StackMachineComposition.Sweep.cost contents clearKeys) :=
  StackMachineComposition.lift_execution (StackMachineComposition.Sweep.step clearKeys ()) step
    (cleanupConfig state) (cleanup_step state) (StackMachineComposition.Sweep.run clearKeys () [] clearKeys (by simp) ((),false) contents)

end Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Execution

/-! Physical field loops and ordered child attachment for the recursive consumer. -/

namespace Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Execution
open Turing StateTransition
open Mettapedia.Computability
open Mettapedia.Computability.StackMachineComposition (oneStep)
open Mettapedia.OSLF.Binding.WireCodec.Binary

abbrev nameArena : Key := .body (.saved (.local .name))

def fieldContents (base : ∀ key,List (Cells key)) (commands : List Routing.Symbol)
    (field : List Continuation.Cell) : ∀ key,List (Cells key) :=
  Function.update (Function.update base .input commands) nameArena field

def fieldConfig (phase : Option Phase) (state : Control) (base : ∀ key,List (Cells key))
    (commands : List Routing.Symbol) (field : List Continuation.Cell) : Cfg :=
  ⟨phase,state,fieldContents base commands field⟩

def byteSymbol (name : Bool) (symbol : Alphabet) : Routing.Symbol :=
  if name then .name symbol else .source symbol

def byteAllowed (name : Bool) (state : Control) : Bool :=
  if name then state.mode == .constructor else state.mode != .constructor

theorem read_field (state : Control) (base : ∀ key,List (Cells key))
    (head : Routing.Symbol) (tail : List Routing.Symbol) (field : List Continuation.Cell) :
    step (fieldConfig (some .read) state base (head::tail) field)=
      some (fieldConfig (some (.dispatch head)) {state with command:=some head} base tail field) := by
  simp only [step,program,fieldConfig,fieldContents,TM2.step,TM2.stepAux]
  simp only [Function.update_of_ne (by decide : Key.input ≠ nameArena),Function.update_self,
    List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some]
  congr 1
  rw [Function.update_comm (by decide : Key.input ≠ nameArena)]
  simp only [Function.update_idem]
  rw [Function.update_comm (by decide : nameArena ≠ Key.input)]

theorem dispatch_field (name : Bool) (state : Control) (allowed : byteAllowed name state=true)
    (base : ∀ key,List (Cells key)) (head : Alphabet) (tail : List Routing.Symbol)
    (field : List Continuation.Cell) :
    step (fieldConfig (some (.dispatch (byteSymbol name head))) state base tail field)=
      some (fieldConfig (some .read) state base tail (some head::field)) := by
  cases name <;> simp only [byteAllowed,byteSymbol,Bool.false_eq_true,↓reduceIte] at allowed ⊢
  all_goals
    simp only [step,program,fieldConfig,fieldContents,nameArena,TM2.step,TM2.stepAux,allowed,
      Bool.cond_true,Function.update_self,Function.update_idem]

def fieldState (name : Bool) : List Alphabet → Control → Control
  | [],state => state
  | head::tail,state => fieldState name tail {state with command:=some (byteSymbol name head)}

noncomputable def fieldRun (name : Bool) (state : Control) (allowed : byteAllowed name state=true)
    (word : List Alphabet) (base : ∀ key,List (Cells key)) (tail : List Routing.Symbol)
    (field : List Continuation.Cell) :
    EvalsToInTime step
      (fieldConfig (some .read) state base (word.map (byteSymbol name)++tail) field)
      (some (fieldConfig (some .read) (fieldState name word state) base tail (word.reverse.map some++field)))
      (2*word.length) := by
  induction word generalizing state field with
  | nil =>
      simpa only [List.map_nil,List.nil_append,List.reverse_nil,List.length_nil,Nat.mul_zero,fieldState]
        using (EvalsToInTime.refl step (fieldConfig (some .read) state base tail field))
  | cons head rest ih =>
      have first:=oneStep (read_field state base (byteSymbol name head)
        (rest.map (byteSymbol name)++tail) field)
      have second:=oneStep (dispatch_field name {state with command:=some (byteSymbol name head)}
        allowed base head (rest.map (byteSymbol name)++tail) field)
      have remaining:=ih {state with command:=some (byteSymbol name head)} allowed (some head::field)
      have front:=EvalsToInTime.trans _ _ _ _ _ _ first second
      have joined:=EvalsToInTime.trans _ _ _ _ _ _ front remaining
      convert joined using 1
      · simp only [List.map_cons,List.cons_append]
      · simp only [fieldState,List.reverse_cons,List.map_append,List.map_cons,List.map_nil,
          List.append_assoc,List.singleton_append]
      · simp only [List.length_cons]; omega

theorem prelude_cons (state : Control) (base : ∀ key,List (Cells key))
    (commands : List Routing.Symbol) (head : Continuation.Cell) (tail : List Continuation.Cell) :
    step (fieldConfig (some .clearPrelude) state base commands (head::tail))=
      some (fieldConfig (some .clearPrelude) {state with present:=true} base commands tail) := by
  simp [step,program,fieldConfig,fieldContents,nameArena,TM2.step,TM2.stepAux]

theorem prelude_nil (state : Control) (base : ∀ key,List (Cells key)) (commands : List Routing.Symbol) :
    step (fieldConfig (some .clearPrelude) state base commands [])=
      some (fieldConfig (some .read) {state with mode:=.constructor,present:=false} base commands []) := by
  simp [step,program,fieldConfig,fieldContents,nameArena,TM2.step,TM2.stepAux]

noncomputable def preludeRun (state : Control) (base : ∀ key,List (Cells key))
    (commands : List Routing.Symbol) (field : List Continuation.Cell) :
    EvalsToInTime step (fieldConfig (some .clearPrelude) state base commands field)
      (some (fieldConfig (some .read) {state with mode:=.constructor,present:=false} base commands []))
      (field.length+1) := by
  induction field generalizing state with
  | nil => exact oneStep (prelude_nil state base commands)
  | cons head tail ih =>
      have first:=oneStep (prelude_cons state base commands head tail)
      have rest:=ih {state with present:=true}
      have joined:=EvalsToInTime.trans _ _ _ _ _ _ first rest
      convert joined using 1
      simp only [List.length_cons]


abbrev opaqueArena : Key := .body (.head .name)

def opaqueConfig (phase : Option Phase) (state : Control) (base : ∀ key,List (Cells key))
    (commands : List Routing.Symbol) (field : List Continuation.Cell) (word : List Alphabet) : Cfg :=
  ⟨phase,state,Function.update (fieldContents base commands field) opaqueArena word⟩

theorem opaque_cons (state : Control) (base : ∀ key,List (Cells key))
    (commands : List Routing.Symbol) (head : Alphabet) (tail : List Continuation.Cell) (word : List Alphabet) :
    step (opaqueConfig (some .opaquePrepare) state base commands (some head::tail) word)=
      some (opaqueConfig (some .opaquePrepare) {state with cell:=some (some head)} base commands tail (head::word)) := by
  simp only [step,opaqueConfig,TM2.step]
  rw [program]
  simp only [fieldContents,TM2.stepAux]
  simp only [Function.update_of_ne (by decide : nameArena ≠ opaqueArena),Function.update_self,
    List.head?_cons,List.tail_cons,Option.isSome_some,Option.join_some,Option.getD_some,Bool.cond_true]
  congr 1
  rw [Function.update_comm (by decide : nameArena ≠ opaqueArena)]
  simp only [Function.update_idem]
  rw [Function.update_comm (by decide : opaqueArena ≠ nameArena)]
  simp [nameArena,opaqueArena,Function.update]

theorem opaque_nil (state : Control) (base : ∀ key,List (Cells key))
    (commands : List Routing.Symbol) (word : List Alphabet) :
    step (opaqueConfig (some .opaquePrepare) state base commands [] word)=
      some (opaqueConfig (some (.opaque (.emit ⟨0,by omega⟩)))
        {state with cell:=none,literal:=none} base commands [] word) := by
  simp only [step,opaqueConfig,TM2.step]
  rw [program]
  simp only [fieldContents,TM2.stepAux,
    Function.update_of_ne (by decide : nameArena ≠ opaqueArena),Function.update_self,
    List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false]
  congr 1
  rw [Function.update_comm (by decide : nameArena ≠ opaqueArena)]
  simp only [Function.update_idem]

noncomputable def opaquePrepareRun (state : Control) (base : ∀ key,List (Cells key))
    (commands : List Routing.Symbol) (field word : List Alphabet) :
    EvalsToInTime step
      (opaqueConfig (some .opaquePrepare) state base commands (field.map some) word)
      (some (opaqueConfig (some (.opaque (.emit ⟨0,by omega⟩))) {state with cell:=none,literal:=none}
        base commands [] (field.reverse++word)))
      (field.length+1) := by
  induction field generalizing state word with
  | nil => exact oneStep (opaque_nil state base commands word)
  | cons head tail ih =>
      have first:=oneStep (opaque_cons state base commands head (tail.map some) word)
      have rest:=ih {state with cell:=some (some head)} (head::word)
      have joined:=EvalsToInTime.trans _ _ _ _ _ _ first rest
      convert joined using 1
      · simp only [List.map_cons]
      · simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
      · simp only [List.length_cons]

/-- Returning the next physical child agrees with the authored ordered frame.
Its occurrence contributes a marker even when its byte word equals another. -/
theorem child_attached_stored (name : String) (words : List (List Alphabet)) (word : List Alphabet) :
    ChildReturn.attachedLocals word (Constructor.Completion.storedLocals name words)=
      Constructor.Completion.storedLocals name (words++[word]) := by
  funext arena
  cases arena <;> simp [ChildReturn.attachedLocals,Constructor.Completion.storedLocals,
    WordTemplateMachine.Indexed.frame,List.flatMap_append,List.reverse_append,List.replicate_succ]

open Mettapedia.Computability.StackMachineRegisters
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.Languages.HOLLight.TemplateInstantiationMachine (termWire)
open Mettapedia.Languages.HOLLight.InferenceStorageBounds

def nodeConfig (phase : Option Phase) (state : Control) (commands : List Routing.Symbol)
    (storage : Constructor.Completion.Storage) (returned : List Continuation.Cell := []) : Cfg :=
  config phase state commands (Constructor.Completion.contents storage) returned [] []

theorem completion_nodeConfig (state : Control) (commands : List Routing.Symbol)
    (phase : Option Constructor.Completion.Phase) (body : Constructor.Completion.Control)
    (storage : Constructor.Completion.Storage) :
    completionConfig state (nodeConfig none state commands {}).stk
      (Constructor.Completion.config phase body storage)=
      nodeConfig (some (phase.elim .constructorDone Phase.constructor)) {state with body:=body} commands storage := by
  simp only [completionConfig,StackMachineRegisters.embeddedContinuationConfig,
    nodeConfig,config,Constructor.Completion.config]
  cases phase <;> simp only [Option.elim_some,Option.elim_none,TM2.stepAux]
  all_goals
    congr 1
    funext key
    cases key with
    | body key =>
        have observed := Frame.read (Alphabet:=Constructor.Completion.Cells) (TargetAlphabet:=Cells) Key.body bodySelect body_select_sound body_select_complete
          (fun _=>rfl) (nodeConfig none state commands {}).stk (Constructor.Completion.contents storage) key
        change bodyOverlay _ _ (.body key) = (Constructor.Completion.contents storage key).map id at observed
        simpa only [List.map_id,nodeConfig,config,Continuation.config,ChildReturn.config,Constructor.Completion.contents] using observed
    | input | result | returnWord | returnScratch => simp [bodyOverlay,Frame.overlay,bodySelect]

theorem save_nodeConfig (state : Control) (commands : List Routing.Symbol)
    (phase : Option Continuation.Phase) (control : Continuation.Control)
    (locals : Continuation.Arena→List Continuation.Cell)
    (frames : Continuation.Arena→List (Option Continuation.Cell)) :
    saveConfig state (nodeConfig none state commands {}).stk
      (Continuation.config phase control locals frames)=
      nodeConfig (some (phase.elim .entered Phase.save)) {state with continuation:=control} commands
        {locals:=locals,frames:=frames} := by
  simp only [saveConfig,StackMachineRegisters.embeddedContinuationConfig,nodeConfig,config,Continuation.config]
  cases phase <;> simp only [Option.elim_some,Option.elim_none,TM2.stepAux]
  all_goals
    congr 1
    funext key
    cases key with
    | body key => cases key with
        | saved key =>
            change continuationOverlay _ _ (continuationKey key)=_
            have observed := Frame.read (Alphabet:=Continuation.Cells) (TargetAlphabet:=Cells) continuationKey continuationSelect continuation_select_sound continuation_select_complete
              (fun _=>rfl) (nodeConfig none state commands {}).stk
              (Continuation.config none control locals frames).stk key
            cases key with
            | «local» arena =>
                change continuationOverlay _ _ (continuationKey (.local arena))=(locals arena).map id at observed
                simpa only [List.map_id,nodeConfig,config,Continuation.config,ChildReturn.config,Constructor.Completion.contents] using observed
            | frames arena =>
                change continuationOverlay _ _ (continuationKey (.frames arena))=(frames arena).map id at observed
                simpa only [List.map_id,nodeConfig,config,Continuation.config,ChildReturn.config,Constructor.Completion.contents] using observed
        | head key => cases key <;> simp [continuationOverlay,Frame.overlay,continuationSelect,Constructor.Completion.contents]
        | children => simp [continuationOverlay,Frame.overlay,continuationSelect,Constructor.Completion.contents]
    | input | result | returnWord | returnScratch =>
        simp [continuationOverlay,StackMachineRegisters.Frame.overlay,continuationSelect]

theorem child_nodeConfig (state : Control) (commands : List Routing.Symbol)
    (phase : Option ChildReturn.Phase) (control : ChildReturn.Control) (word : List Continuation.Cell)
    (locals : Continuation.Arena→List Continuation.Cell)
    (frames : Continuation.Arena→List (Option Continuation.Cell)) :
    childConfig state (nodeConfig none state commands {}).stk
      (ChildReturn.config phase control word locals frames)=
      nodeConfig (some (phase.elim .returned Phase.returnChild)) {state with continuation:=control} commands
        {locals:=locals,frames:=frames} word := by
  simp only [childConfig,StackMachineRegisters.embeddedContinuationConfig,nodeConfig,config,ChildReturn.config]
  cases phase <;> simp only [Option.elim_some,Option.elim_none,TM2.stepAux]
  all_goals
    congr 1
    funext key
    cases key with
    | body key => cases key with
        | saved key =>
            change childOverlay _ _ (childReturnKey (some key))=_
            have observed := Frame.read (Alphabet:=ChildReturn.Cells) (TargetAlphabet:=Cells) childReturnKey childSelect child_select_sound child_select_complete childReturnCells
              (nodeConfig none state commands {}).stk (ChildReturn.config none control word locals frames).stk (some key)
            cases key with
            | «local» arena =>
                change childOverlay _ _ (childReturnKey (some (.local arena)))=(locals arena).map id at observed
                simpa only [List.map_id,nodeConfig,config,Continuation.config,ChildReturn.config,Constructor.Completion.contents] using observed
            | frames arena =>
                change childOverlay _ _ (childReturnKey (some (.frames arena)))=(frames arena).map id at observed
                simpa only [List.map_id,nodeConfig,config,Continuation.config,ChildReturn.config,Constructor.Completion.contents] using observed
        | head key => cases key <;> simp [childOverlay,Frame.overlay,childSelect,Constructor.Completion.contents]
        | children => simp [childOverlay,Frame.overlay,childSelect,Constructor.Completion.contents]
    | returnWord =>
        change childOverlay _ _ (childReturnKey none)=_
        have observed := Frame.read (Alphabet:=ChildReturn.Cells) (TargetAlphabet:=Cells) childReturnKey childSelect child_select_sound child_select_complete childReturnCells
          (nodeConfig none state commands {}).stk (ChildReturn.config none control word locals frames).stk none
        change childOverlay _ _ (childReturnKey none)=word.map id at observed
        simpa only [List.map_id,nodeConfig,config,Continuation.config,ChildReturn.config,Constructor.Completion.contents] using observed
    | input | result | returnScratch =>
        simp [childOverlay,StackMachineRegisters.Frame.overlay,childSelect]

theorem read_node (state : Control) (head : Routing.Symbol) (tail : List Routing.Symbol)
    (storage : Constructor.Completion.Storage) (word : List Continuation.Cell) :
    step (nodeConfig (some .read) state (head::tail) storage word)=
      some (nodeConfig (some (.dispatch head)) {state with command:=some head} tail storage word) := by
  simp [step,program,nodeConfig,config,TM2.step,TM2.stepAux]
  funext key
  cases key <;> simp [Function.update]

theorem dispatch_start (state : Control) (commands : List Routing.Symbol)
    (storage : Constructor.Completion.Storage) :
    step (nodeConfig (some (.dispatch .start)) state commands storage)=
      some (nodeConfig (some (.save (.sub false .name .push)))
        {state with continuation:=WordFrame.initial} commands storage) := rfl

theorem entered_node (state : Control) (accepted : state.continuation.2.2=true)
    (commands : List Routing.Symbol) (storage : Constructor.Completion.Storage) :
    step (nodeConfig (some .entered) state commands storage)=
      some (nodeConfig (some .read) {state with mode:=.pending,continuation:=WordFrame.initial} commands storage) := by
  simp [step,program,nodeConfig,config,TM2.step,TM2.stepAux,accepted]

noncomputable def enterRun (state : Control) (commands : List Routing.Symbol)
    (locals : Continuation.Arena→List Continuation.Cell)
    (frames : Continuation.Arena→List (Option Continuation.Cell)) :
    EvalsToInTime step (nodeConfig (some .read) state (.start::commands) {locals:=locals,frames:=frames})
      (some (nodeConfig (some .read) {state with command:=some .start,mode:=.pending,continuation:=WordFrame.initial}
        commands {frames:=Continuation.savedFrames locals frames}))
      ((locals .name).length+(locals .children).length+(locals .markers).length+12) := by
  let started : Control := {state with command:=some .start,continuation:=WordFrame.initial}
  have first:=oneStep (read_node state .start commands {locals:=locals,frames:=frames} [])
  have second:=oneStep (dispatch_start {state with command:=some .start} commands {locals:=locals,frames:=frames})
  have saved:=saveRun started (nodeConfig none state commands {}).stk locals frames
  have saved := saved
  have baseEq : (nodeConfig none state commands {}).stk=(nodeConfig none started commands {}).stk := rfl
  rw [baseEq,save_nodeConfig,save_nodeConfig] at saved
  have third:=oneStep (entered_node {started with continuation:=(none,none,true)} rfl commands
    {frames:=Continuation.savedFrames locals frames})
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ first second
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined saved
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined third
  convert joined using 1
  simp
  omega


theorem field_nodeConfig (phase : Option Phase) (state baseState : Control) (commands baseCommands : List Routing.Symbol)
    (storage : Constructor.Completion.Storage) (field : List Continuation.Cell) :
    fieldConfig phase state (nodeConfig none baseState baseCommands storage).stk commands field=
      nodeConfig phase state commands {storage with locals:=Function.update storage.locals .name field} := by
  simp only [fieldConfig,fieldContents,nodeConfig,config]
  congr 1
  funext key
  cases key with
  | body key => cases key with
    | saved key => cases key with
      | «local» arena => cases arena <;> simp [Constructor.Completion.contents,Function.update]
      | frames arena => simp [Constructor.Completion.contents,Function.update]
    | head key => cases key <;> simp [Constructor.Completion.contents,Function.update]
    | children => simp [Constructor.Completion.contents,Function.update]
  | input | result | returnWord | returnScratch => simp [Function.update]

theorem opaque_nodeConfig (phase : Option Phase) (state baseState : Control) (commands baseCommands : List Routing.Symbol)
    (storage : Constructor.Completion.Storage) (field : List Continuation.Cell) (word : List Alphabet) :
    opaqueConfig phase state (nodeConfig none baseState baseCommands storage).stk commands field word=
      nodeConfig phase state commands {storage with locals:=(Function.update storage.locals .name field), head:={storage.head with name:=word}} := by
  simp only [opaqueConfig,fieldContents,nodeConfig,config]
  congr 1
  funext key
  cases key with
  | body key => cases key with
    | saved key => cases key with
      | «local» arena => cases arena <;> simp [Constructor.Completion.contents,Function.update]
      | frames arena => simp [Constructor.Completion.contents,Function.update]
    | head key => cases key <;> simp [Constructor.Completion.contents,Constructor.HeadFromMarkers.contents,Function.update]
    | children => simp [Constructor.Completion.contents,Function.update]
  | input | result | returnWord | returnScratch => simp [Function.update]

noncomputable def nodeFieldRun (name : Bool) (state : Control) (allowed : byteAllowed name state=true)
    (word : List Alphabet) (tail : List Routing.Symbol) (storage : Constructor.Completion.Storage) :
    EvalsToInTime step
      (nodeConfig (some .read) state (word.map (byteSymbol name)++tail) storage)
      (some (nodeConfig (some .read) (fieldState name word state) tail
        {storage with locals:=(Function.update storage.locals .name (word.reverse.map some++storage.locals .name))})) (2*word.length) := by
  have executed:=fieldRun name state allowed word (nodeConfig none state tail storage).stk tail (storage.locals .name)
  rw [field_nodeConfig,field_nodeConfig] at executed
  have unchanged : {storage with locals:=Function.update storage.locals .name (storage.locals .name)}=storage := by
    simp
  rw [unchanged] at executed
  exact executed

theorem dispatch_constructor (state : Control) (pending : state.mode=.pending)
    (commands : List Routing.Symbol) (storage : Constructor.Completion.Storage) :
    step (nodeConfig (some (.dispatch .constructor)) state commands storage)=
      some (nodeConfig (some .clearPrelude) state commands storage) := by
  simp [step,program,nodeConfig,config,TM2.step,TM2.stepAux,pending,show ((.pending:Mode)==.pending)=true from rfl]

theorem dispatch_literal (state : Control) (pending : state.mode=.pending)
    (commands : List Routing.Symbol) (storage : Constructor.Completion.Storage) :
    step (nodeConfig (some (.dispatch .literal)) state commands storage)=
      some (nodeConfig (some .read) {state with mode:=.literal} commands storage) := by
  simp [step,program,nodeConfig,config,TM2.step,TM2.stepAux,pending,show ((.pending:Mode)==.pending)=true from rfl]

theorem fieldState_mode (name : Bool) (word : List Alphabet) (state : Control) :
    (fieldState name word state).mode=state.mode := by
  induction word generalizing state with
  | nil => rfl
  | cons _ _ ih => exact ih _

theorem fieldState_commandUpdate (name : Bool) (word : List Alphabet) (state : Control) (command : Option Routing.Symbol) :
    {fieldState name word state with command:=command}={state with command:=command} := by
  induction word generalizing state with
  | nil => rfl
  | cons _ _ ih => exact ih _

def constructorReadyState (state : Control) (name : String) : Control :=
  fieldState true (encodeWith Codec.string name) {state with command:=some .constructor,mode:=.constructor,present:=false}

noncomputable def constructorReadyRun (state : Control) (pending : state.mode=.pending)
    (name : String) (commands : List Routing.Symbol)
    (frames : Continuation.Arena→List (Option Continuation.Cell)) :
    EvalsToInTime step
      (nodeConfig (some .read) state
        ((4::encodeWith Codec.string "a").map Routing.Symbol.source++[.constructor]++
          (encodeWith Codec.string name).map Routing.Symbol.name++commands) {frames:=frames})
      (some (nodeConfig (some .read) (constructorReadyState state name) commands
        {locals:=Constructor.Completion.storedLocals name [],frames:=frames}))
      (3*(4::encodeWith Codec.string "a").length+2*(encodeWith Codec.string name).length+3) := by
  let sourceWord:=4::encodeWith Codec.string "a"
  let prefixState:=fieldState false sourceWord state
  let field:=sourceWord.reverse.map some
  have prefixMode : prefixState.mode=.pending := (fieldState_mode false sourceWord state).trans pending
  have captured:=nodeFieldRun false state (by simpa only [byteAllowed,pending,Bool.false_eq_true,↓reduceIte] using (show ((.pending:Mode)!=.constructor)=true from rfl)) sourceWord
    ([.constructor]++(encodeWith Codec.string name).map Routing.Symbol.name++commands) {frames:=frames}
  have readMarker:=oneStep (read_node prefixState .constructor
    ((encodeWith Codec.string name).map Routing.Symbol.name++commands)
    {locals:=Function.update (fun _=>[]) .name field,frames:=frames} [])
  have dispatch:=oneStep (dispatch_constructor {prefixState with command:=some .constructor} prefixMode
    ((encodeWith Codec.string name).map Routing.Symbol.name++commands)
    {locals:=Function.update (fun _=>[]) .name field,frames:=frames})
  have cleared:=preludeRun {prefixState with command:=some .constructor}
    (nodeConfig none {prefixState with command:=some .constructor}
      ((encodeWith Codec.string name).map Routing.Symbol.name++commands) {frames:=frames}).stk
    ((encodeWith Codec.string name).map Routing.Symbol.name++commands) field
  rw [field_nodeConfig] at cleared
  let clearState : Control := {prefixState with command:=some .constructor,mode:=.constructor,present:=false}
  rw [field_nodeConfig] at cleared
  simp only [Function.update_eq_self] at cleared
  have named:=nodeFieldRun true clearState rfl (encodeWith Codec.string name) commands {frames:=frames}
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ captured readMarker
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined dispatch
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined cleared
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined named
  have resetState := congrArg (fun control : Control=>{control with mode:=.constructor,present:=false})
    (fieldState_commandUpdate false sourceWord state (some .constructor))
  change clearState={state with command:=some .constructor,mode:=.constructor,present:=false} at resetState
  convert joined using 1
  · simp only [sourceWord,List.append_assoc,show byteSymbol false=Routing.Symbol.source from rfl]
  · rw [resetState]
    simp only [constructorReadyState]
    congr 1
    congr 1
    congr 1
    funext arena; cases arena <;> simp [Constructor.Completion.storedLocals,WordTemplateMachine.Indexed.frame,Function.update]
  · simp [sourceWord,field]
    omega


def mapStorage (literal : Bool) (storage : Constructor.Completion.Storage) (word : List Alphabet) :
    Constructor.Completion.Storage :=
  if literal then {storage with head:={storage.head with name:=word}}
  else {storage with head:={storage.head with scratch:=word}}

theorem map_config (literal : Bool) (state baseState : Control) (commands : List Routing.Symbol)
    (storage : Constructor.Completion.Storage) (phase : Option MapPhase)
    (mapper : WordHomomorphismMachine.State (A:=Alphabet) (B:=Continuation.Cell))
    (input : List Alphabet) (output result : List Continuation.Cell) :
    mapConfig literal state (nodeConfig none baseState commands storage).stk
      (WordHomomorphismMachine.config wordImage phase mapper input output result)=
      config (some (phase.elim (.localClear ⟨0,by omega⟩) (Phase.map literal)))
        (if phase.isSome then {state with mapper:=mapper} else {state with mapper:=mapper,sweep:=((),false)})
        commands (Constructor.Completion.contents (mapStorage literal storage input)) result output [] := by
  let source:=WordHomomorphismMachine.config wordImage phase mapper input output result
  let base:=(nodeConfig none baseState commands storage).stk
  have inputReadCore (value : Bool) : mapOverlay value base source.stk (mapKey value .input)=
      input.map (mapCells value .input).mp :=
    Frame.read (Alphabet:=WordHomomorphismMachine.Alphabet (A:=Alphabet) (B:=Continuation.Cell))
      (TargetAlphabet:=Cells) (mapKey value) (mapSelect value) (map_select_sound value) (map_select_complete value)
      (mapCells value) base source.stk .input
  have inputRead : (if literal then mapOverlay literal base source.stk (.body (.head .name))
      else mapOverlay literal base source.stk (.body (.head .scratch)))=input := by
    cases literal with
    | false =>
        have observed:=inputReadCore false
        change mapOverlay false base source.stk (.body (.head .scratch))=input.map id at observed
        simpa only [List.map_id,Bool.false_eq_true,↓reduceIte] using observed
    | true =>
        have observed:=inputReadCore true
        change mapOverlay true base source.stk (.body (.head .name))=input.map id at observed
        simpa only [List.map_id,Bool.false_eq_true,↓reduceIte] using observed
  have outputRead : mapOverlay literal base source.stk .returnScratch=output := by
    have observed:=Frame.read (Alphabet:=WordHomomorphismMachine.Alphabet (A:=Alphabet) (B:=Continuation.Cell))
      (TargetAlphabet:=Cells) (mapKey literal) (mapSelect literal) (map_select_sound literal) (map_select_complete literal)
      (mapCells literal) base source.stk .output
    change mapOverlay literal base source.stk .returnScratch=output.map id at observed
    simpa only [List.map_id] using observed
  have resultRead : mapOverlay literal base source.stk .returnWord=result := by
    have observed:=Frame.read (Alphabet:=WordHomomorphismMachine.Alphabet (A:=Alphabet) (B:=Continuation.Cell))
      (TargetAlphabet:=Cells) (mapKey literal) (mapSelect literal) (map_select_sound literal) (map_select_complete literal)
      (mapCells literal) base source.stk .result
    change mapOverlay literal base source.stk .returnWord=result.map id at observed
    simpa only [List.map_id] using observed
  simp only [mapConfig,StackMachineRegisters.embeddedContinuationConfig]
  simp only [WordHomomorphismMachine.config]
  cases phase <;> simp only [mapContinuation,TM2.stepAux,Option.elim_none,Option.elim_some,Option.isSome_none,
    Option.isSome_some,Bool.false_eq_true,↓reduceIte,config]
  all_goals
    congr 1
    funext key
    cases literal <;> cases key with
    | body key => cases key with
      | head key =>
          cases key
          all_goals first
            | simpa only [Bool.false_eq_true,↓reduceIte,source,base,nodeConfig,config,mapStorage,
                Constructor.Completion.contents,Constructor.HeadFromMarkers.contents,WordHomomorphismMachine.config] using inputRead
            | simp [mapOverlay,Frame.overlay,mapSelect,mapStorage,Constructor.Completion.contents,
                Constructor.HeadFromMarkers.contents,nodeConfig,config]
      | saved key => cases key <;> simp [mapOverlay,Frame.overlay,mapSelect,mapStorage,Constructor.Completion.contents,nodeConfig,config]
      | children => simp [mapOverlay,Frame.overlay,mapSelect,mapStorage,Constructor.Completion.contents,nodeConfig,config]
    | returnScratch => simpa only [source,base,nodeConfig,config,WordHomomorphismMachine.config] using outputRead
    | returnWord => simpa only [source,base,nodeConfig,config,WordHomomorphismMachine.config] using resultRead
    | input | result => simp [mapOverlay,Frame.overlay,mapSelect,nodeConfig,config]


theorem wordImage_list (word : List Alphabet) : word.flatMap wordImage=word.map some := by
  induction word with
  | nil => rfl
  | cons _ _ ih => simp only [List.flatMap_cons,List.map_cons,wordImage,List.singleton_append,ih]

theorem mapper_init (word : List Alphabet) : initList (WordHomomorphismMachine.machine wordImage) word=
    WordHomomorphismMachine.config wordImage (some .read) (none,none) word [] [] := by
  simp only [initList,WordHomomorphismMachine.machine,WordHomomorphismMachine.config]
  congr 1
  funext key; cases key <;> simp

theorem mapper_halt (word : List Continuation.Cell) : haltList (WordHomomorphismMachine.machine wordImage) word=
    WordHomomorphismMachine.config wordImage none (none,none) [] [] word := by
  simp only [haltList,WordHomomorphismMachine.machine,WordHomomorphismMachine.config]
  congr 1
  funext key; cases key <;> simp

noncomputable def nodeMapRun (literal : Bool) (state : Control) (commands : List Routing.Symbol)
    (storage : Constructor.Completion.Storage) (word : List Alphabet) :
    EvalsToInTime step
      (nodeConfig (some (.map literal .read)) {state with mapper:=(none,none)} commands (mapStorage literal storage word))
      (some (nodeConfig (some (.localClear ⟨0,by omega⟩)) {state with mapper:=(none,none),sweep:=((),false)}
        commands (mapStorage literal storage []) (word.map some))) (4*word.length+2) := by
  have executed:=mapRun literal state (nodeConfig none state commands storage).stk word
  rw [mapper_init,mapper_halt,map_config,map_config,wordImage_list] at executed
  simp only [Option.elim_some,Option.elim_none,Option.isSome_some,Option.isSome_none,Bool.false_eq_true,↓reduceIte] at executed
  convert executed using 1
  all_goals first | rfl | (simp only [List.length_map]; omega)

def finishedStorage (frames : Continuation.Arena→List (Option Continuation.Cell)) (markers : Nat) :
    Constructor.Completion.Storage := {frames:=frames,head:={input:=List.replicate markers ()}}

theorem clear_finished (state : Control) (commands : List Routing.Symbol)
    (frames : Continuation.Arena→List (Option Continuation.Cell)) (markers : Nat) (word : List Alphabet) :
    StackMachineComposition.Sweep.clear (nodeConfig none state commands (finishedStorage frames markers) (word.map some)).stk
      localClearKeys=(nodeConfig none state commands {frames:=frames} (word.map some)).stk := by
  funext key
  cases key with
  | body key => cases key with
    | saved key => cases key <;> simp [StackMachineComposition.Sweep.clear,localClearKeys,headKeys,nodeConfig,config,
        finishedStorage,Constructor.Completion.contents,Function.update]
    | head key => cases key <;> simp [StackMachineComposition.Sweep.clear,localClearKeys,headKeys,nodeConfig,config,
        finishedStorage,Constructor.Completion.contents,Constructor.HeadFromMarkers.contents,Function.update]
    | children => simp [StackMachineComposition.Sweep.clear,localClearKeys,headKeys,nodeConfig,config,
        finishedStorage,Constructor.Completion.contents,Function.update]
  | input | result | returnWord | returnScratch =>
      simp [StackMachineComposition.Sweep.clear,localClearKeys,headKeys,nodeConfig,config,Function.update]

theorem clear_finished_clock (state : Control) (commands : List Routing.Symbol)
    (frames : Continuation.Arena→List (Option Continuation.Cell)) (markers : Nat) (word : List Alphabet) :
    StackMachineComposition.Sweep.cost (nodeConfig none state commands (finishedStorage frames markers) (word.map some)).stk
      localClearKeys=markers+localClearKeys.length+1 := by
  simp [StackMachineComposition.Sweep.cost,localClearKeys,headKeys,nodeConfig,config,
    finishedStorage,Constructor.Completion.contents,Constructor.HeadFromMarkers.contents,Function.update]

noncomputable def nodeClearRun (state : Control) (commands : List Routing.Symbol)
    (frames : Continuation.Arena→List (Option Continuation.Cell)) (markers : Nat) (word : List Alphabet) :
    EvalsToInTime step
      (nodeConfig (some (.localClear ⟨0,by omega⟩)) {state with sweep:=((),false)} commands
        (finishedStorage frames markers) (word.map some))
      (some (nodeConfig (some (.returnChild (.restore (.sub true .name .restore))))
        {state with sweep:=((),false),continuation:=WordFrame.initial} commands {frames:=frames} (word.map some)))
      (markers+localClearKeys.length+1) := by
  have executed:=clearRun state (nodeConfig none state commands (finishedStorage frames markers) (word.map some)).stk
  rw [clear_finished,clear_finished_clock] at executed
  simpa only [clearConfig,StackMachineRegisters.embeddedContinuationConfig,StackMachineComposition.Sweep.config,
    clearContinuation,TM2.stepAux,nodeConfig,config,id_eq] using executed

theorem returned_node (state : Control) (accepted : state.continuation.2.2=true)
    (commands : List Routing.Symbol) (storage : Constructor.Completion.Storage) :
    step (nodeConfig (some .returned) state commands storage)=
      some (nodeConfig (some .read) initial commands storage) := by
  simp [step,program,nodeConfig,config,TM2.step,TM2.stepAux,accepted]

noncomputable def nodeReturnRun (state : Control) (commands : List Routing.Symbol) (word : List Alphabet)
    (locals : Continuation.Arena→List Continuation.Cell)
    (frames : Continuation.Arena→List (Option Continuation.Cell)) :
    EvalsToInTime step
      (nodeConfig (some (.returnChild (.restore (.sub true .name .restore))))
        {state with continuation:=WordFrame.initial} commands
        {frames:=Continuation.savedFrames locals frames} (word.map some))
      (some (nodeConfig (some .read) initial commands {locals:=ChildReturn.attachedLocals word locals,frames:=frames}))
      ((locals .name).length+(locals .children).length+(locals .markers).length+word.length+9) := by
  have executed:=childRun state (nodeConfig none state commands {}).stk word locals frames
  rw [child_nodeConfig,child_nodeConfig] at executed
  have finish:=oneStep (returned_node {state with continuation:=(none,none,true)} rfl commands
    {locals:=ChildReturn.attachedLocals word locals,frames:=frames})
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ executed finish
  convert joined using 1
  all_goals first | rfl | omega


theorem dispatch_finish_constructor (state : Control) (mode : state.mode=.constructor)
    (commands : List Routing.Symbol) (storage : Constructor.Completion.Storage) :
    step (nodeConfig (some (.dispatch .finish)) state commands storage)=
      some (nodeConfig (some (.constructor .name)) {state with body:=Constructor.Completion.initial} commands storage) := by
  simp [step,program,nodeConfig,config,TM2.step,TM2.stepAux,mode,
    show ((.constructor:Mode)==.constructor)=true from rfl]

theorem constructor_done (state : Control) (accepted : state.body.accepted=true)
    (commands : List Routing.Symbol) (storage : Constructor.Completion.Storage) :
    step (nodeConfig (some .constructorDone) state commands storage)=
      some (nodeConfig (some (.map false .read)) {state with mapper:=(none,none)} commands storage) := by
  simp [step,program,nodeConfig,config,TM2.step,TM2.stepAux,accepted]

def constructorWord (name : String) (words : List (List Alphabet)) : List Alphabet :=
  Constructor.Spine.output (termWire (constructorTerm name words.length)) words

def parentSize (locals : Continuation.Arena→List Continuation.Cell) : Nat :=
  (locals .name).length+(locals .children).length+(locals .markers).length

def constructorFinishClock (name : String) (words : List (List Alphabet))
    (locals : Continuation.Arena→List Continuation.Cell) : Nat :=
  Constructor.Completion.clock name words+4*(constructorWord name words).length+2+
    words.length+localClearKeys.length+1+parentSize locals+(constructorWord name words).length+9+3

noncomputable def constructorFinishRun (state : Control) (mode : state.mode=.constructor)
    (name : String) (words : List (List Alphabet)) (commands : List Routing.Symbol)
    (locals : Continuation.Arena→List Continuation.Cell)
    (frames : Continuation.Arena→List (Option Continuation.Cell)) :
    EvalsToInTime step
      (nodeConfig (some .read) state (.finish::commands)
        {locals:=Constructor.Completion.storedLocals name words,frames:=Continuation.savedFrames locals frames})
      (some (nodeConfig (some .read) initial commands
        {locals:=ChildReturn.attachedLocals (constructorWord name words) locals,frames:=frames}))
      (constructorFinishClock name words locals) := by
  let finishedState : Control := {state with command:=some .finish}
  let suspended:=Continuation.savedFrames locals frames
  let stored : Constructor.Completion.Storage := {locals:=Constructor.Completion.storedLocals name words,frames:=suspended}
  let completed : Constructor.Completion.Storage := {
    frames:=suspended,head:={input:=List.replicate words.length (),scratch:=constructorWord name words}}
  have first:=oneStep (read_node state .finish commands stored [])
  have second:=oneStep (dispatch_finish_constructor finishedState mode commands stored)
  have assembled:=completionRun finishedState (nodeConfig none finishedState commands {}).stk name words suspended
  rw [completion_nodeConfig,completion_nodeConfig] at assembled
  have next:=oneStep (constructor_done {finishedState with body:=Constructor.Completion.initial} rfl commands completed)
  have mapped:=nodeMapRun false {finishedState with body:=Constructor.Completion.initial} commands
    (finishedStorage suspended words.length) (constructorWord name words)
  have cleared:=nodeClearRun {finishedState with body:=Constructor.Completion.initial,mapper:=(none,none)} commands
    suspended words.length (constructorWord name words)
  have returned:=nodeReturnRun {finishedState with body:=Constructor.Completion.initial,mapper:=(none,none),sweep:=((),false)}
    commands (constructorWord name words) locals frames
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ first second
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined assembled
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined next
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined mapped
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined cleared
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined returned
  convert joined using 1
  all_goals first | rfl | (unfold constructorFinishClock parentSize; omega)


def literalStorage (storage : Constructor.Completion.Storage) (input temporary output : List Alphabet) :
    Constructor.Completion.Storage :=
  {storage with head:={storage.head with name:=input,typeScratch:=temporary,scratch:=output}}

theorem literal_config (state baseState : Control) (commands : List Routing.Symbol)
    (storage : Constructor.Completion.Storage) (phase : Option (WordTemplateMachine.Phase HookLiteral.template.length))
    (literal : Option Alphabet) (input temporary output : List Alphabet) :
    literalConfig state (nodeConfig none baseState commands storage).stk
      (WordTemplateMachine.config HookLiteral.template phase literal input temporary output)=
      nodeConfig (some (phase.elim (.map true .read) Phase.opaque))
        (if phase.isSome then {state with literal:=literal} else {state with literal:=literal,mapper:=(none,none)})
        commands (literalStorage storage input temporary output) := by
  let original:=WordTemplateMachine.config HookLiteral.template phase literal input temporary output
  let base:=(nodeConfig none baseState commands storage).stk
  have readField (key : WordTemplateMachine.Stack) :=
    Frame.read (Alphabet:=fun _ : WordTemplateMachine.Stack=>Alphabet) (TargetAlphabet:=Cells)
      literalKey literalSelect literal_select_sound literal_select_complete literalCells base original.stk key
  have inputRead : literalOverlay base original.stk (.body (.head .name))=input := by
    have observed:=readField .input
    change literalOverlay base original.stk (.body (.head .name))=input.map id at observed
    simpa only [List.map_id] using observed
  have temporaryRead : literalOverlay base original.stk (.body (.head .typeScratch))=temporary := by
    have observed:=readField .temporary
    change literalOverlay base original.stk (.body (.head .typeScratch))=temporary.map id at observed
    simpa only [List.map_id] using observed
  have outputRead : literalOverlay base original.stk (.body (.head .scratch))=output := by
    have observed:=readField .output
    change literalOverlay base original.stk (.body (.head .scratch))=output.map id at observed
    simpa only [List.map_id] using observed
  simp only [literalConfig,StackMachineRegisters.embeddedContinuationConfig,WordTemplateMachine.config]
  cases phase <;> simp only [literalContinuation,TM2.stepAux,Option.elim_none,Option.elim_some,Option.isSome_none,
    Option.isSome_some,Bool.false_eq_true,↓reduceIte,nodeConfig,config]
  all_goals
    congr 1
    funext key
    cases key with
    | body key => cases key with
      | head key =>
          cases key
          all_goals first
            | simpa only [literalKey,List.map_id,original,base,nodeConfig,config,WordTemplateMachine.config,
                literalStorage,Constructor.Completion.contents,Constructor.HeadFromMarkers.contents] using inputRead
            | simpa only [literalKey,List.map_id,original,base,nodeConfig,config,WordTemplateMachine.config,
                literalStorage,Constructor.Completion.contents,Constructor.HeadFromMarkers.contents] using temporaryRead
            | simpa only [literalKey,List.map_id,original,base,nodeConfig,config,WordTemplateMachine.config,
                literalStorage,Constructor.Completion.contents,Constructor.HeadFromMarkers.contents] using outputRead
            | simp [literalOverlay,Frame.overlay,literalSelect,literalStorage,Constructor.Completion.contents,
                Constructor.HeadFromMarkers.contents]
      | saved key => cases key <;> simp [literalOverlay,Frame.overlay,literalSelect,literalStorage,
          Constructor.Completion.contents]
      | children => simp [literalOverlay,Frame.overlay,literalSelect,literalStorage,Constructor.Completion.contents]
    | input | result | returnWord | returnScratch => simp [literalOverlay,Frame.overlay,literalSelect]

noncomputable def nodeLiteralRun (state : Control) (commands : List Routing.Symbol)
    (frames : Continuation.Arena→List (Option Continuation.Cell)) (word : List Alphabet) :
    EvalsToInTime step
      (nodeConfig (some (.opaque (.emit ⟨0,by omega⟩))) {state with literal:=none} commands
        {frames:=frames,head:={name:=word}})
      (some (nodeConfig (some (.map true .read)) {state with literal:=none,mapper:=(none,none)} commands
        {frames:=frames,head:={name:=WordTemplateMachine.instantiate HookLiteral.template word}}))
      (4*(HookLiteral.template.length+1)*(word.length+1)) := by
  have executed:=literalRun state (nodeConfig none state commands {frames:=frames}).stk word
  rw [WordTemplateMachine.init_eq,WordTemplateMachine.halt_eq,literal_config,literal_config] at executed
  convert executed using 1 <;> rfl

theorem dispatch_finish_literal (state : Control) (mode : state.mode=.literal)
    (commands : List Routing.Symbol) (storage : Constructor.Completion.Storage) :
    step (nodeConfig (some (.dispatch .finish)) state commands storage)=
      some (nodeConfig (some .opaquePrepare) state commands storage) := by
  simp [step,program,nodeConfig,config,TM2.step,TM2.stepAux,mode,
    show ((.literal:Mode)==.constructor)=false from rfl,show ((.literal:Mode)==.literal)=true from rfl]

def literalFinishClock (span : List Alphabet) (locals : Continuation.Arena→List Continuation.Cell) : Nat :=
  2+(span.length+1)+4*(HookLiteral.template.length+1)*(span.length+1)+
    4*(WordTemplateMachine.instantiate HookLiteral.template span).length+2+localClearKeys.length+1+
    parentSize locals+(WordTemplateMachine.instantiate HookLiteral.template span).length+9

noncomputable def literalFinishRun (state : Control) (mode : state.mode=.literal)
    (commands : List Routing.Symbol) (span : List Alphabet)
    (locals : Continuation.Arena→List Continuation.Cell)
    (frames : Continuation.Arena→List (Option Continuation.Cell)) :
    EvalsToInTime step
      (nodeConfig (some .read) state (.finish::commands)
        {locals:=Function.update (fun _=>[]) .name (span.reverse.map some),
          frames:=Continuation.savedFrames locals frames})
      (some (nodeConfig (some .read) initial commands
        {locals:=ChildReturn.attachedLocals (WordTemplateMachine.instantiate HookLiteral.template span) locals,frames:=frames}))
      (literalFinishClock span locals) := by
  let finishedState : Control := {state with command:=some .finish}
  let suspended:=Continuation.savedFrames locals frames
  let stored : Constructor.Completion.Storage := {
    locals:=Function.update (fun _=>[]) .name (span.reverse.map some),frames:=suspended}
  have first:=oneStep (read_node state .finish commands stored [])
  have second:=oneStep (dispatch_finish_literal finishedState mode commands stored)
  have prepared:=opaquePrepareRun finishedState (nodeConfig none finishedState commands {frames:=suspended}).stk
    commands span.reverse []
  rw [opaque_nodeConfig,opaque_nodeConfig] at prepared
  simp only [List.reverse_reverse,List.append_nil,Function.update_eq_self] at prepared
  have literal:=nodeLiteralRun {finishedState with cell:=none} commands suspended span
  have mapped:=nodeMapRun true {finishedState with cell:=none,literal:=none} commands
    {frames:=suspended} (WordTemplateMachine.instantiate HookLiteral.template span)
  have cleared:=nodeClearRun {finishedState with cell:=none,literal:=none,mapper:=(none,none)} commands
    suspended 0 (WordTemplateMachine.instantiate HookLiteral.template span)
  have returned:=nodeReturnRun {finishedState with cell:=none,literal:=none,mapper:=(none,none),sweep:=((),false)}
    commands (WordTemplateMachine.instantiate HookLiteral.template span) locals frames
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ first second
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined prepared
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined literal
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined mapped
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined cleared
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined returned
  convert joined using 1
  all_goals first | rfl | (unfold literalFinishClock parentSize; simp only [List.length_reverse]; omega)


open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Logic.HOL.Embedding.InferenceRules (valid_apply_iff)

abbrev enteredState (state : Control) : Control :=
  {state with command:=some .start,mode:=.pending,continuation:=WordFrame.initial}

def opaqueSpan (token : String) (rest : List String) : List Alphabet :=
  (4::encodeWith Codec.string token)++Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.fields rest

def literalReadyState (state : Control) (token : String) (rest : List String) : Control :=
  fieldState false (Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.fields rest)
    {fieldState false (4::encodeWith Codec.string token) state with command:=some .literal,mode:=.literal}

noncomputable def literalReadyRun (state : Control) (pending : state.mode=.pending)
    (token : String) (rest : List String) (commands : List Routing.Symbol)
    (frames : Continuation.Arena→List (Option Continuation.Cell)) :
    EvalsToInTime step
      (nodeConfig (some .read) state
        ((4::encodeWith Codec.string token).map Routing.Symbol.source++[.literal]++
          (Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.fields rest).map Routing.Symbol.source++commands)
        {frames:=frames})
      (some (nodeConfig (some .read) (literalReadyState state token rest) commands
        {locals:=Function.update (fun _=>[]) .name ((opaqueSpan token rest).reverse.map some),frames:=frames}))
      (2*(4::encodeWith Codec.string token).length+2+
        2*(Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.fields rest).length) := by
  let sourceWord:=4::encodeWith Codec.string token
  let tailWord:=Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.fields rest
  let prefixState:=fieldState false sourceWord state
  let field:=sourceWord.reverse.map some
  have prefixMode : prefixState.mode=.pending := (fieldState_mode false sourceWord state).trans pending
  have captured:=nodeFieldRun false state
    (by simpa only [byteAllowed,pending,Bool.false_eq_true,↓reduceIte] using (show ((.pending:Mode)!=.constructor)=true from rfl))
    sourceWord ([.literal]++tailWord.map Routing.Symbol.source++commands) {frames:=frames}
  simp only [List.append_nil,List.singleton_append] at captured
  have readMarker:=oneStep (read_node prefixState .literal (tailWord.map Routing.Symbol.source++commands)
    {locals:=Function.update (fun _=>[]) .name field,frames:=frames} [])
  have dispatch:=oneStep (dispatch_literal {prefixState with command:=some .literal} prefixMode
    (tailWord.map Routing.Symbol.source++commands) {locals:=Function.update (fun _=>[]) .name field,frames:=frames})
  have remaining:=nodeFieldRun false {prefixState with command:=some .literal,mode:=.literal}
    (by simpa only [byteAllowed,Bool.false_eq_true,↓reduceIte] using (show ((.literal:Mode)!=.constructor)=true from rfl))
    tailWord commands {locals:=Function.update (fun _=>[]) .name field,frames:=frames}
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ captured readMarker
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined dispatch
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined remaining
  convert joined using 1
  · simp only [List.append_assoc,sourceWord,tailWord,List.singleton_append,show byteSymbol false=Routing.Symbol.source from rfl]
  · simp only [literalReadyState,opaqueSpan,sourceWord,tailWord,field,prefixState,
      Function.update_self,Function.update_idem,List.reverse_append,List.map_append]
  · dsimp only [sourceWord,tailWord]
    omega

def childrenState (state : Control) : List Pattern → Control
  | [] => state
  | _::_ => initial

theorem constructorWord_exact (name : String) (arguments : List Pattern) :
    constructorWord name (arguments.map (fun argument=>termWire (dataTerm argument)))=
      termWire (dataTerm (.apply name arguments)) := by
  rw [dataTerm,Constructor.applyTerms_wire]
  simp only [constructorWord,Constructor.Spine.output,List.length_map,
    List.flatten_eq_flatMap,List.flatMap_map,id_eq]

def patternSpan (pattern : Pattern) : List Alphabet :=
  opaqueSpan ((Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).headD "")
    (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).tail

theorem literalWord_exact (pattern : Pattern) (opaqueCase : isOpaque pattern=true)
    (admitted : argumentValidAt 0 pattern=true) :
    WordTemplateMachine.instantiate HookLiteral.template (patternSpan pattern)=termWire (dataTerm pattern) := by
  rw [←renderedArgument_term,raw_wire pattern opaqueCase admitted]
  have span:=Routing.command_source_fields pattern
  change patternSpan pattern++[3,2]=patternWire pattern at span
  simp only [HookLiteral.template,WordTemplateMachine.instantiate_append,
    WordTemplateMachine.instantiate_literals,WordTemplateMachine.instantiate_hole,
    WordTemplateMachine.instantiate_nil,List.append_nil]
  rw [←span]
  simp only [List.append_assoc]

noncomputable def opaqueNodeRun (state : Control) (token : String) (rest : List String)
    (commands : List Routing.Symbol) (locals : Continuation.Arena→List Continuation.Cell)
    (frames : Continuation.Arena→List (Option Continuation.Cell)) :
    EvalsToInTime step
      (nodeConfig (some .read) state (Routing.opaqueCommands token rest++commands) {locals:=locals,frames:=frames})
      (some (nodeConfig (some .read) initial commands
        {locals:=ChildReturn.attachedLocals (WordTemplateMachine.instantiate HookLiteral.template (opaqueSpan token rest)) locals,
          frames:=frames}))
      (parentSize locals+12+2*(4::encodeWith Codec.string token).length+2+
        2*(Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.fields rest).length+
        literalFinishClock (opaqueSpan token rest) locals) := by
  let suffix:=.finish::commands
  let body:=(4::encodeWith Codec.string token).map Routing.Symbol.source++[.literal]++
    (Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.fields rest).map Routing.Symbol.source++suffix
  have entered:=enterRun state body locals frames
  have prepared:=literalReadyRun (enteredState state) rfl token rest suffix (Continuation.savedFrames locals frames)
  have readyMode : (literalReadyState (enteredState state) token rest).mode=.literal :=
    fieldState_mode false _ _
  have finished:=literalFinishRun (literalReadyState (enteredState state) token rest) readyMode commands
    (opaqueSpan token rest) locals frames
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ entered prepared
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined finished
  convert joined using 1
  · simp only [Routing.opaqueCommands,List.append_assoc,List.cons_append,List.nil_append,body,suffix]
  · unfold parentSize; omega

mutual
  def nodeClock (pattern : Pattern) (locals : Continuation.Arena→List Continuation.Cell) : Nat :=
    parentSize locals+12+match pattern with
    | .apply name arguments =>
        3*(4::encodeWith Codec.string "a").length+2*(encodeWith Codec.string name).length+3+
        childrenClock name [] arguments+
        constructorFinishClock name (arguments.map (fun argument=>termWire (dataTerm argument))) locals
    | pattern =>
        2*(4::encodeWith Codec.string ((Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).headD "")).length+2+
        2*(Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.fields
          (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).tail).length+
        literalFinishClock (patternSpan pattern) locals
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec
  def childrenClock (name : String) (words : List (List Alphabet)) : List Pattern → Nat
    | [] => 0
    | argument::arguments => nodeClock argument (Constructor.Completion.storedLocals name words)+
        childrenClock name (words++[termWire (dataTerm argument)]) arguments
  termination_by arguments=>sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec
end

noncomputable def opaquePatternRun (pattern : Pattern) (opaqueCase : isOpaque pattern=true)
    (admitted : argumentValidAt 0 pattern=true) (state : Control) (commands : List Routing.Symbol)
    (locals : Continuation.Arena→List Continuation.Cell)
    (frames : Continuation.Arena→List (Option Continuation.Cell)) :
    EvalsToInTime step
      (nodeConfig (some .read) state (Routing.commands pattern++commands) {locals:=locals,frames:=frames})
      (some (nodeConfig (some .read) initial commands
        {locals:=ChildReturn.attachedLocals (termWire (dataTerm pattern)) locals,frames:=frames}))
      (nodeClock pattern locals) := by
  have executed:=opaqueNodeRun state ((Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).headD "")
    (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).tail commands locals frames
  have exactWord:=literalWord_exact pattern opaqueCase admitted
  change WordTemplateMachine.instantiate HookLiteral.template
    (opaqueSpan ((Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).headD "")
      (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).tail)=_ at exactWord
  rw [exactWord] at executed
  cases pattern <;> simp only [isOpaque,Bool.false_eq_true] at opaqueCase
  all_goals simpa only [nodeClock,Routing.commands,patternSpan,Nat.add_assoc] using executed

mutual
  noncomputable def nodeRun (pattern : Pattern) (admitted : argumentValidAt 0 pattern=true)
      (state : Control) (commands : List Routing.Symbol)
      (locals : Continuation.Arena→List Continuation.Cell)
      (frames : Continuation.Arena→List (Option Continuation.Cell)) :
      EvalsToInTime step
        (nodeConfig (some .read) state (Routing.commands pattern++commands) {locals:=locals,frames:=frames})
        (some (nodeConfig (some .read) initial commands
          {locals:=ChildReturn.attachedLocals (termWire (dataTerm pattern)) locals,frames:=frames}))
        (nodeClock pattern locals) := by
    cases pattern with
    | apply name arguments =>
        let suffix:=.finish::commands
        let body:=(4::encodeWith Codec.string "a").map Routing.Symbol.source++[.constructor]++
          (encodeWith Codec.string name).map Routing.Symbol.name++Routing.listCommands arguments++suffix
        have entered:=enterRun state body locals frames
        simp only [body,List.append_assoc] at entered
        have prepared:=constructorReadyRun (enteredState state) rfl name
          (Routing.listCommands arguments++suffix) (Continuation.savedFrames locals frames)
        simp only [List.append_assoc] at prepared
        have children:=childrenRun name [] arguments ((valid_apply_iff name arguments).mp admitted)
          (constructorReadyState (enteredState state) name) suffix (Continuation.savedFrames locals frames)
        have finalMode : (childrenState (constructorReadyState (enteredState state) name) arguments).mode=.constructor := by
          cases arguments with
          | nil => exact fieldState_mode true _ _
          | cons _ _ => rfl
        have finished:=constructorFinishRun (childrenState (constructorReadyState (enteredState state) name) arguments)
          finalMode name (arguments.map (fun argument=>termWire (dataTerm argument))) commands locals frames
        simp only [List.nil_append] at children
        have joined:=EvalsToInTime.trans _ _ _ _ _ _ entered prepared
        have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined children
        have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined finished
        rw [constructorWord_exact] at joined
        convert joined using 1
        · simp only [Routing.commands,List.cons_append,List.append_assoc,List.nil_append,suffix]
        · simp only [nodeClock,parentSize]
          omega
    | fvar name => simp [argumentValidAt,Pattern.isGroundAt] at admitted
    | bvar index => exact opaquePatternRun _ rfl admitted state commands locals frames
    | lambda name body => exact opaquePatternRun _ rfl admitted state commands locals frames
    | multiLambda arity names body => exact opaquePatternRun _ rfl admitted state commands locals frames
    | subst body replacement => exact opaquePatternRun _ rfl admitted state commands locals frames
    | collection kind arguments rest => exact opaquePatternRun _ rfl admitted state commands locals frames
  termination_by sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec
  noncomputable def childrenRun (name : String) (words : List (List Alphabet)) (arguments : List Pattern)
      (admitted : ∀ argument∈arguments,argumentValidAt 0 argument=true)
      (state : Control) (commands : List Routing.Symbol)
      (frames : Continuation.Arena→List (Option Continuation.Cell)) :
      EvalsToInTime step
        (nodeConfig (some .read) state (Routing.listCommands arguments++commands)
          {locals:=Constructor.Completion.storedLocals name words,frames:=frames})
        (some (nodeConfig (some .read) (childrenState state arguments) commands
          {locals:=Constructor.Completion.storedLocals name (words++arguments.map (fun argument=>termWire (dataTerm argument))),
            frames:=frames}))
        (childrenClock name words arguments) := by
    cases arguments with
    | nil =>
        simpa only [Routing.listCommands,List.nil_append,List.map_nil,List.append_nil,childrenClock,childrenState]
          using (EvalsToInTime.refl (f:=step) (a:=nodeConfig (some .read) state commands
            {locals:=Constructor.Completion.storedLocals name words,frames:=frames}))
    | cons argument arguments =>
        have first:=nodeRun argument (admitted argument (by simp)) state
          (Routing.listCommands arguments++commands) (Constructor.Completion.storedLocals name words) frames
        rw [child_attached_stored] at first
        have rest:=childrenRun name (words++[termWire (dataTerm argument)]) arguments
          (fun value member=>admitted value (by simp [member])) initial commands frames
        have joined:=EvalsToInTime.trans _ _ _ _ _ _ first rest
        convert joined using 1
        · simp only [Routing.listCommands,List.append_assoc]
        · cases arguments <;> simp only [childrenState,List.map_cons,List.append_assoc,List.singleton_append]
        · rw [childrenClock]; omega
  termination_by sizeOf arguments
  decreasing_by all_goals sizeOf_pattern_dec
end

def finalConfig (phase : Option Phase) (state : Control) (storage : Constructor.Completion.Storage)
    (result : List Alphabet) : Cfg := config phase state [] (Constructor.Completion.contents storage) [] [] result

def rootStorage (children markers : List Continuation.Cell) : Constructor.Completion.Storage := {
  locals:=fun arena=>match arena with | .name=>[] | .children=>children | .markers=>markers}

theorem read_empty (state : Control) (storage : Constructor.Completion.Storage) :
    step (nodeConfig (some .read) state [] storage)=
      some (finalConfig (some .extract) {state with command:=none} storage []) := by
  simp [step,program,nodeConfig,finalConfig,config,TM2.step,TM2.stepAux]

theorem extract_root (state : Control) (word : List Alphabet) :
    step (finalConfig (some .extract) state (rootStorage (none::word.reverse.map some) [none]) [])=
      some (finalConfig (some .rootBody) {state with cell:=some none}
        (rootStorage (word.reverse.map some) [none]) []) := by
  simp [step,program,finalConfig,config,rootStorage,Constructor.Completion.contents,TM2.step,TM2.stepAux]
  funext key; cases key with
  | body key=>cases key with
    | saved key=>cases key with
      | «local» arena=>cases arena <;> simp [Function.update]
      | frames arena=>simp [Function.update]
    | head key=>simp [Function.update]
    | children=>simp [Function.update]
  | input | result | returnWord | returnScratch=>simp [Function.update]

theorem root_body_cons (state : Control) (symbol : Alphabet) (field result : List Alphabet) :
    step (finalConfig (some .rootBody) state (rootStorage (some symbol::field.map some) [none]) result)=
      some (finalConfig (some .rootBody) {state with cell:=some (some symbol)}
        (rootStorage (field.map some) [none]) (symbol::result)) := by
  simp [step,program,finalConfig,config,rootStorage,Constructor.Completion.contents,TM2.step,TM2.stepAux]
  funext key; cases key with
  | body key=>cases key with
    | saved key=>cases key with
      | «local» arena=>cases arena <;> simp [Function.update]
      | frames arena=>simp [Function.update]
    | head key=>simp [Function.update]
    | children=>simp [Function.update]
  | input | result | returnWord | returnScratch=>simp [Function.update]

theorem root_body_nil (state : Control) (result : List Alphabet) :
    step (finalConfig (some .rootBody) state (rootStorage [] [none]) result)=
      some (finalConfig (some .rootMarker) {state with cell:=none} (rootStorage [] [none]) result) := by
  simp [step,program,finalConfig,config,rootStorage,Constructor.Completion.contents,TM2.step,TM2.stepAux]

noncomputable def rootBodyRun (state : Control) (field result : List Alphabet) :
    EvalsToInTime step
      (finalConfig (some .rootBody) state (rootStorage (field.map some) [none]) result)
      (some (finalConfig (some .rootMarker) {state with cell:=none} (rootStorage [] [none]) (field.reverse++result)))
      (field.length+1) := by
  induction field generalizing state result with
  | nil=>simpa only [List.reverse_nil,List.nil_append,List.map_nil,List.length_nil,Nat.zero_add]
      using oneStep (root_body_nil state result)
  | cons symbol field ih=>
      have first:=oneStep (root_body_cons state symbol field result)
      have rest:=ih {state with cell:=some (some symbol)} (symbol::result)
      have joined:=EvalsToInTime.trans _ _ _ _ _ _ first rest
      convert joined using 1
      · simp only [List.map_cons]
      · simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
      · simp only [List.length_cons]

theorem root_marker (state : Control) (result : List Alphabet) :
    step (finalConfig (some .rootMarker) state (rootStorage [] [none]) result)=
      some (finalConfig (some .rootMarkerEnd) {state with cell:=some none} {} result) := by
  simp [step,program,finalConfig,config,rootStorage,Constructor.Completion.contents,TM2.step,TM2.stepAux]
  funext key; cases key with
  | body key=>cases key with
    | saved key=>cases key with
      | «local» arena=>cases arena <;> simp [Function.update]
      | frames arena=>simp [Function.update]
    | head key=>simp [Function.update]
    | children=>simp [Function.update]
  | input | result | returnWord | returnScratch=>simp [Function.update]

theorem root_marker_end (state : Control) (result : List Alphabet) :
    step (finalConfig (some .rootMarkerEnd) state {} result)=
      some (finalConfig (some .rootName) {state with present:=false} {} result) := by
  simp [step,program,finalConfig,config,Constructor.Completion.contents,TM2.step,TM2.stepAux]

theorem root_name (state : Control) (result : List Alphabet) :
    step (finalConfig (some .rootName) state {} result)=
      some (finalConfig (some (.rootFrame .name)) {state with present:=false} {} result) := by
  simp [step,program,finalConfig,config,Constructor.Completion.contents,TM2.step,TM2.stepAux]

theorem root_frame_name (state : Control) (result : List Alphabet) :
    step (finalConfig (some (.rootFrame .name)) state {} result)=
      some (finalConfig (some (.rootFrame .children)) {state with present:=false} {} result) := by
  simp [step,program,finalConfig,config,Constructor.Completion.contents,TM2.step,TM2.stepAux]

theorem root_frame_children (state : Control) (result : List Alphabet) :
    step (finalConfig (some (.rootFrame .children)) state {} result)=
      some (finalConfig (some (.rootFrame .markers)) {state with present:=false} {} result) := by
  simp [step,program,finalConfig,config,Constructor.Completion.contents,TM2.step,TM2.stepAux]

theorem root_frame_markers (state : Control) (result : List Alphabet) :
    step (finalConfig (some (.rootFrame .markers)) state {} result)=
      some (finalConfig (some (.wrap (.emit ⟨0,by omega⟩))) {state with present:=false,literal:=none} {} result) := by
  simp only [step,finalConfig,config,TM2.step]
  rw [program]
  simp only [Constructor.Completion.contents,TM2.stepAux,List.head?_nil,Option.isSome_none,
    Bool.cond_false]

noncomputable def rootExtractRun (state : Control) (word : List Alphabet) :
    EvalsToInTime step
      (nodeConfig (some .read) state [] {locals:=ChildReturn.attachedLocals word (fun _=>[])})
      (some (finalConfig (some (.wrap (.emit ⟨0,by omega⟩)))
        {state with command:=none,cell:=some none,present:=false,literal:=none} {} word))
      (word.length+9) := by
  have first:=oneStep (read_empty state {locals:=ChildReturn.attachedLocals word (fun _=>[])})
  have storageEqual : (⟨ChildReturn.attachedLocals word (fun _=>[]),fun _=>[],{},[]⟩ : Constructor.Completion.Storage)=
      rootStorage (none::word.reverse.map some) [none] := by
    congr 1
    funext arena
    cases arena <;> simp [ChildReturn.attachedLocals]
  rw [storageEqual] at first
  have second:=oneStep (extract_root {state with command:=none} word)
  have body:=rootBodyRun {state with command:=none,cell:=some none} word.reverse []
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at body
  have marker:=oneStep (root_marker {state with command:=none,cell:=none} word)
  have markerEnd:=oneStep (root_marker_end {state with command:=none,cell:=some none} word)
  have name:=oneStep (root_name {state with command:=none,cell:=some none,present:=false} word)
  have frameName:=oneStep (root_frame_name {state with command:=none,cell:=some none,present:=false} word)
  have frameChildren:=oneStep (root_frame_children {state with command:=none,cell:=some none,present:=false} word)
  have frameMarkers:=oneStep (root_frame_markers {state with command:=none,cell:=some none,present:=false} word)
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ first second
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined body
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined marker
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined markerEnd
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined name
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined frameName
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined frameChildren
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined frameMarkers
  convert joined using 1
  · simpa only [nodeConfig,finalConfig,config] using congrArg (fun storage : Constructor.Completion.Storage=>
      config (some .read) state [] (Constructor.Completion.contents storage) [] [] []) storageEqual
  · omega

def rootTemplateStorage (temporary output : List Alphabet) : Constructor.Completion.Storage := {
  head:={typeWord:=temporary,typeScratch:=output}}

theorem root_config (state : Control) (phase : Option (WordTemplateMachine.Phase rootTemplate.length))
    (literal : Option Alphabet) (input temporary output : List Alphabet) :
    rootConfig state (finalConfig none state {} []).stk
      (WordTemplateMachine.config rootTemplate phase literal input temporary output)=
      finalConfig (some (phase.elim (.cleanup ⟨0,by omega⟩) Phase.wrap))
        (if phase.isSome then {state with literal:=literal} else {state with literal:=literal,sweep:=((),false)})
        (rootTemplateStorage temporary output) input := by
  let original:=WordTemplateMachine.config rootTemplate phase literal input temporary output
  let base:=(finalConfig none state {} []).stk
  have readField (key : WordTemplateMachine.Stack) :=
    Frame.read (Alphabet:=fun _=>Alphabet) (TargetAlphabet:=Cells) rootKey rootSelect root_select_sound
      root_select_complete rootCells base original.stk key
  have inputRead : rootOverlay base original.stk .result=input := by
    have observed:=readField .input
    change rootOverlay base original.stk .result=input.map id at observed
    simpa only [List.map_id] using observed
  have temporaryRead : rootOverlay base original.stk (.body (.head .typeWord))=temporary := by
    have observed:=readField .temporary
    change rootOverlay base original.stk (.body (.head .typeWord))=temporary.map id at observed
    simpa only [List.map_id] using observed
  have outputRead : rootOverlay base original.stk (.body (.head .typeScratch))=output := by
    have observed:=readField .output
    change rootOverlay base original.stk (.body (.head .typeScratch))=output.map id at observed
    simpa only [List.map_id] using observed
  simp only [rootConfig,StackMachineRegisters.embeddedContinuationConfig,WordTemplateMachine.config]
  cases phase <;> simp only [rootContinuation,TM2.stepAux,Option.elim_none,Option.elim_some,
    Option.isSome_none,Option.isSome_some,Bool.false_eq_true,↓reduceIte,finalConfig,config]
  all_goals
    congr 1
    funext key
    cases key with
    | result=>simpa only [rootKey,List.map_id,original,base,finalConfig,config,WordTemplateMachine.config,
        rootTemplateStorage,Constructor.Completion.contents] using inputRead
    | body key=>cases key with
      | head key=>
          cases key
          all_goals first
            | simpa only [rootKey,List.map_id,original,base,finalConfig,config,WordTemplateMachine.config,
                rootTemplateStorage,Constructor.Completion.contents,Constructor.HeadFromMarkers.contents] using temporaryRead
            | simpa only [rootKey,List.map_id,original,base,finalConfig,config,WordTemplateMachine.config,
                rootTemplateStorage,Constructor.Completion.contents,Constructor.HeadFromMarkers.contents] using outputRead
            | simp [rootOverlay,Frame.overlay,rootSelect,rootTemplateStorage,Constructor.Completion.contents,
                Constructor.HeadFromMarkers.contents]
      | saved key=>cases key <;> simp [rootOverlay,Frame.overlay,rootSelect,rootTemplateStorage,Constructor.Completion.contents]
      | children=>simp [rootOverlay,Frame.overlay,rootSelect,rootTemplateStorage,Constructor.Completion.contents]
    | input | returnWord | returnScratch=>simp [rootOverlay,Frame.overlay,rootSelect]

noncomputable def wrapRun (state : Control) (word : List Alphabet) :
    EvalsToInTime step
      (finalConfig (some (.wrap (.emit ⟨0,by omega⟩))) {state with literal:=none} {} word)
      (some (finalConfig (some (.cleanup ⟨0,by omega⟩)) {state with literal:=none,sweep:=((),false)} {}
        (WordTemplateMachine.instantiate rootTemplate word)))
      (4*(rootTemplate.length+1)*(word.length+1)) := by
  have executed:=rootRun state (finalConfig none state {} []).stk word
  rw [WordTemplateMachine.init_eq,WordTemplateMachine.halt_eq,root_config,root_config] at executed
  simpa only [Option.elim_some,Option.elim_none,Option.isSome_none,Option.isSome_some,
    Bool.false_eq_true,↓reduceIte,rootTemplateStorage] using executed


theorem cleanup_final_storage (state : Control) (word : List Alphabet) :
    StackMachineComposition.Sweep.clear (finalConfig none state {} word).stk clearKeys=
      (finalConfig none state {} word).stk := by
  funext key
  cases key with
  | body key=>cases key with
    | head key=>cases key <;> simp [StackMachineComposition.Sweep.clear,clearKeys,localClearKeys,headKeys,
        finalConfig,config,Constructor.Completion.contents,Constructor.HeadFromMarkers.contents,Function.update]
    | saved key=>cases key with
      | «local» arena=>cases arena <;> simp [StackMachineComposition.Sweep.clear,clearKeys,localClearKeys,headKeys,
          finalConfig,config,Constructor.Completion.contents,Function.update]
      | frames arena=>cases arena <;> simp [StackMachineComposition.Sweep.clear,clearKeys,localClearKeys,headKeys,
          finalConfig,config,Constructor.Completion.contents,Function.update]
    | children=>simp [StackMachineComposition.Sweep.clear,clearKeys,localClearKeys,headKeys,
        finalConfig,config,Constructor.Completion.contents,Function.update]
  | input | result | returnWord | returnScratch=>simp [StackMachineComposition.Sweep.clear,clearKeys,localClearKeys,headKeys,
        finalConfig,config,Function.update]

theorem cleanup_final_clock (state : Control) (word : List Alphabet) :
    StackMachineComposition.Sweep.cost (finalConfig none state {} word).stk clearKeys=clearKeys.length+1 := by
  simp [StackMachineComposition.Sweep.cost,clearKeys,localClearKeys,headKeys,finalConfig,config,
    Constructor.Completion.contents,Constructor.HeadFromMarkers.contents]

theorem consumer_halt (word : List Alphabet) : haltList machine word=finalConfig none initial {} word := by
  simp only [haltList,machine,finalConfig,config,Constructor.Completion.contents]
  congr 1
  funext key
  cases key with
  | body key=>cases key with
    | head key=>cases key <;> rfl
    | saved key=>cases key with
      | «local» arena=>cases arena <;> rfl
      | frames arena=>cases arena <;> rfl
    | children=>rfl
  | input | result | returnWord | returnScratch=>rfl

noncomputable def finalCleanupRun (state : Control) (accepted : state.accepted=true) (word : List Alphabet) :
    EvalsToInTime step
      (finalConfig (some (.cleanup ⟨0,by omega⟩)) {state with sweep:=((),false)} {} word)
      (some (haltList machine word)) (clearKeys.length+1) := by
  rw [consumer_halt]
  have acceptedReset : {initial with accepted:=true}=initial := rfl
  have executed:=cleanupRun state (finalConfig none state {} word).stk
  rw [cleanup_final_storage,cleanup_final_clock] at executed
  simpa only [cleanupConfig,StackMachineRegisters.embeddedContinuationConfig,StackMachineComposition.Sweep.config,
    Option.elim_none,Option.elim_some,cleanupContinuation,TM2.stepAux,accepted,
    finalConfig,config,id_eq,acceptedReset] using executed

def consumerClock (pattern : Pattern) : Nat := nodeClock pattern (fun _=>[])+
  (termWire (dataTerm pattern)).length+9+
  4*(rootTemplate.length+1)*((termWire (dataTerm pattern)).length+1)+clearKeys.length+1

theorem consumer_init (commands : List Routing.Symbol) : initList machine commands=
    nodeConfig (some .read) initial commands {} := by
  simp only [initList,machine,nodeConfig,config,Constructor.Completion.contents]
  congr 1
  funext key
  cases key with
  | body key=>cases key with
    | head key=>cases key <;> rfl
    | saved key=>cases key with
      | «local» arena=>cases arena <;> rfl
      | frames arena=>cases arena <;> rfl
    | children=>rfl
  | input | result | returnWord | returnScratch=>rfl

theorem rootTemplate_exact (pattern : Pattern) :
    WordTemplateMachine.instantiate rootTemplate (termWire (dataTerm pattern))=argumentWire pattern := by
  simp only [rootTemplate,WordTemplateMachine.instantiate_append,WordTemplateMachine.instantiate_literal,
    WordTemplateMachine.instantiate_literals,WordTemplateMachine.instantiate_nil,WordTemplateMachine.instantiate_hole,List.append_nil]
  change 4::(termWire (dataTerm pattern)++encodeData (Mettapedia.Languages.OpenTheory.SyntaxEncoding.putTy
      Mettapedia.Languages.HOLLight.InferenceHosting.dataType))=argumentWire pattern
  change 4::(termWire (dataTerm pattern)++encodeData (Mettapedia.Languages.OpenTheory.SyntaxEncoding.putTy
      Mettapedia.Languages.HOLLight.InferenceHosting.dataType))=
    encodeData (.pair (Mettapedia.Languages.OpenTheory.SyntaxEncoding.putTerm (renderedArgument pattern).term)
      (Mettapedia.Languages.OpenTheory.SyntaxEncoding.putTy (renderedArgument pattern).ty))
  rw [encodeData_pair,renderedArgument_term,renderedArgument_ty]
  rfl

set_option maxRecDepth 4096 in
noncomputable def consumerOutputs (pattern : Pattern) (admitted : argumentValidAt 0 pattern=true) :
    TM2OutputsInTime machine (Routing.commands pattern) (some (argumentWire pattern)) (consumerClock pattern) := by
  have generated:=nodeRun pattern admitted initial [] (fun _=>[]) (fun _=>[])
  simp only [List.append_nil] at generated
  have extracted:=rootExtractRun initial (termWire (dataTerm pattern))
  let extractedState : Control := {initial with command:=none,cell:=some none,present:=false,literal:=none}
  have wrapped:=wrapRun extractedState (termWire (dataTerm pattern))
  have cleaned:=finalCleanupRun {extractedState with literal:=none} rfl
    (WordTemplateMachine.instantiate rootTemplate (termWire (dataTerm pattern)))
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ generated extracted
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined wrapped
  have joined:=EvalsToInTime.trans _ _ _ _ _ _ joined cleaned
  rw [←consumer_init,rootTemplate_exact] at joined
  refine ⟨joined.toEvalsTo,joined.steps_le_m.trans ?_⟩
  unfold consumerClock
  omega


section RecursiveInputBounds
set_option maxRecDepth 4096
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.GSLT.LanguageDef.CertificateDataEncoding (patternCodec)
local notation "W" => Mettapedia.OSLF.MeTTaIL.PatternTokens.weight

theorem patternWire_length (pattern : Pattern) :
    (patternWire pattern).length=dataWeight (patternCodec.put pattern) := by
  simp only [patternWire,encodeWith,encodeData,writeData_length,List.length_nil,Nat.add_zero]

theorem patternWire_length_bounds (pattern : Pattern) :
    W pattern≤(patternWire pattern).length ∧ (patternWire pattern).length≤74*W pattern := by
  rw [patternWire_length]
  exact ⟨Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.dataWeight_pattern_lower pattern,
    Mettapedia.GSLT.LanguageDef.CertificateDataEncoding.dataWeight_pattern pattern⟩

theorem dataWord_length (pattern : Pattern) :
    (termWire (dataTerm pattern)).length≤6400*W pattern := by
  have source:=dataTerm_storage pattern
  have codec:=term_payload_bound (dataTerm pattern)
  have length : (termWire (dataTerm pattern)).length=dataWeight (putTerm (dataTerm pattern)) := by
    simp only [termWire,encodeData,writeData_length,List.length_nil,Nat.add_zero]
  rw [length]
  omega

theorem nameWord_length (name : String) : (encodeWith Codec.string name).length≤11*name.utf8ByteSize+2 := by
  simpa only [encodeWith,encodeData,writeData_length,List.length_nil,Nat.add_zero] using dataWeight_string name

theorem storedSize (name : String) (words : List (List Alphabet)) :
    parentSize (Constructor.Completion.storedLocals name words)=
      (encodeWith Codec.string name).length+words.flatten.length+2*words.length := by
  have frame:=WordTemplateMachine.Indexed.frame_length words
  simp only [parentSize,Constructor.Completion.storedLocals,List.length_map,List.length_reverse,List.length_replicate]
  have flatten:=List.length_flatten (L:=words)
  omega

theorem storedSize_append (name : String) (words : List (List Alphabet)) (word : List Alphabet) :
    parentSize (Constructor.Completion.storedLocals name (words++[word]))=
      parentSize (Constructor.Completion.storedLocals name words)+word.length+2 := by
  rw [←child_attached_stored]
  simp only [parentSize,ChildReturn.attachedLocals,List.length_cons,List.length_append,List.length_map,List.length_reverse]
  omega

theorem constructorFinishClock_le (name : String) (words : List (List Alphabet))
    (locals : Continuation.Arena→List Continuation.Cell) :
    constructorFinishClock name words locals≤parentSize locals+2*words.length^2+
      10000*(words.length+(encodeWith Codec.string name).length+
        (WordTemplateMachine.Indexed.frame words).length+(constructorWord name words).length+1) := by
  have completed:=Constructor.Completion.clock_le name words
  have coef : 12*(Constructor.arrowPrefix.length+Constructor.arrowSuffix.length)+
      9*(Constructor.HeadFromMarkers.digitImage false).length+11≤9999 := by decide
  have constant : 12*(encodeData (putTy Mettapedia.Languages.HOLLight.InferenceHosting.dataType)).length+
      9*Constructor.Head.opening.length+18*(encodeData (.atom 0)).length+20+localClearKeys.length+15≤10000 := by decide
  have scaled:=Nat.mul_le_mul_right words.length coef
  unfold constructorFinishClock
  nlinarith

theorem patternSpan_length (pattern : Pattern) : (patternSpan pattern).length≤74*W pattern := by
  have exactSource:=Routing.command_source_fields pattern
  change patternSpan pattern++[3,2]=patternWire pattern at exactSource
  have upper:=(patternWire_length_bounds pattern).2
  have same:=congrArg List.length exactSource
  simp only [List.length_append,List.length_cons,List.length_nil] at same
  omega

theorem literalFinishClock_le (span : List Alphabet) (locals : Continuation.Arena→List Continuation.Cell) :
    literalFinishClock span locals≤parentSize locals+10000*(span.length+1) := by
  have resultLength : (WordTemplateMachine.instantiate HookLiteral.template span).length=
      rawPrefix.length+span.length+2+rawSuffix.length := by
    simp only [HookLiteral.template,WordTemplateMachine.instantiate_append,WordTemplateMachine.instantiate_literals,
      WordTemplateMachine.instantiate_hole,WordTemplateMachine.instantiate_nil,List.append_nil,
      List.length_append,List.length_cons,List.length_nil]
    omega
  have coefficient : 6+4*(HookLiteral.template.length+1)≤10000 := by decide
  have constant : 3+4*(HookLiteral.template.length+1)+5*(rawPrefix.length+2+rawSuffix.length)+
      localClearKeys.length+12≤10000 := by decide
  have scaled:=Nat.mul_le_mul_right span.length coefficient
  unfold literalFinishClock
  rw [resultLength]
  nlinarith

def weightSum (arguments : List Pattern) : Nat := (arguments.map W).sum

theorem words_length_le (arguments : List Pattern) :
    (arguments.map (fun argument=>termWire (dataTerm argument))).flatten.length≤6400*weightSum arguments := by
  induction arguments with
  | nil=>simp [weightSum]
  | cons argument arguments ih=>
      have first:=dataWord_length argument
      simp only [List.map_cons,List.flatten_cons,List.length_append,weightSum,List.sum_cons] at ih ⊢
      omega

theorem arguments_length_le (arguments : List Pattern) : arguments.length≤weightSum arguments := by
  induction arguments with
  | nil=>simp [weightSum]
  | cons argument arguments ih=>
      have positive:=pattern_weight_positive argument
      simp only [List.length_cons,weightSum,List.map_cons,List.sum_cons] at ih ⊢
      omega


theorem nodeClock_parent (pattern : Pattern) (locals : Continuation.Arena→List Continuation.Cell) :
    nodeClock pattern locals=2*parentSize locals+nodeClock pattern (fun _=>[]) := by
  cases pattern <;> simp only [nodeClock,constructorFinishClock,literalFinishClock,parentSize,List.length_nil]
  all_goals omega

theorem weightSum_cons (argument : Pattern) (arguments : List Pattern) :
    weightSum (argument::arguments)=W argument+weightSum arguments := rfl

theorem cubes_le (first second : Nat) : first^3+second^3≤(first+second)^3 := by
  have firstCross : 0≤first^2*second := Nat.zero_le _
  have secondCross : 0≤first*second^2 := Nat.zero_le _
  nlinarith


theorem childrenClock_le (name : String) (words : List (List Alphabet)) (arguments : List Pattern)
    (children : ∀ argument∈arguments,nodeClock argument (fun _=>[])≤1000000000*(W argument)^3) :
    childrenClock name words arguments≤2*arguments.length*parentSize (Constructor.Completion.storedLocals name words)+
      1000000000*(weightSum arguments)^3+12804*arguments.length*weightSum arguments := by
  induction arguments generalizing words with
  | nil=>simp [childrenClock,weightSum]
  | cons argument arguments ih=>
      have first:=children argument (by simp)
      have rest:=ih (words++[termWire (dataTerm argument)]) (fun value member=>children value (by simp [member]))
      have output:=dataWord_length argument
      have positive:=pattern_weight_positive argument
      have cubes:=cubes_le (W argument) (weightSum arguments)
      have cubeScaled:=Nat.mul_le_mul_left 1000000000 cubes
      have outputScaled:=Nat.mul_le_mul_left (2*arguments.length) output
      rw [storedSize_append] at rest
      rw [childrenClock,nodeClock_parent]
      rw [weightSum_cons,List.length_cons]
      nlinarith


theorem cube_gap (first second : Nat) (gap : first+1≤second) : first^3+second^2≤second^3 := by
  have square:=Nat.pow_le_pow_left (by omega : first≤second) 2
  have firstPart:=Nat.mul_le_mul_left first square
  have secondPart:=Nat.mul_le_mul_right (second^2) gap
  nlinarith


theorem constructorOverhead_le (name : String) (arguments : List Pattern) :
    12+3*(4::encodeWith Codec.string "a").length+2*(encodeWith Codec.string name).length+3+
      constructorFinishClock name (arguments.map (fun argument=>termWire (dataTerm argument))) (fun _=>[])+
      2*arguments.length*(encodeWith Codec.string name).length+12804*arguments.length*weightSum arguments≤
        1000000000*(W (.apply name arguments))^2 := by
  let words:=arguments.map (fun argument=>termWire (dataTerm argument))
  let total:=W (.apply name arguments)
  have source : total=name.utf8ByteSize+arguments.length+weightSum arguments+2 := by
    simp only [total,Mettapedia.OSLF.MeTTaIL.PatternTokens.weight,pattern_list_weight,weightSum]
    omega
  have positive : 1≤total := by omega
  have count : arguments.length≤total := by omega
  have nameCount : name.utf8ByteSize≤total := by omega
  have childrenCount : weightSum arguments≤total := by omega
  have output:=dataWord_length (.apply name arguments)
  have exactOutput:=constructorWord_exact name arguments
  have nameField:=nameWord_length name
  have flattened:=words_length_le arguments
  have completed:=constructorFinishClock_le name words (fun _=>[])
  have prefixBound : 12+3*(4::encodeWith Codec.string "a").length+3≤10000 := by decide
  have nameProduct:=Nat.mul_le_mul_left (2*arguments.length) nameField
  have countSquare:=Nat.pow_le_pow_left count 2
  have childProduct:=Nat.mul_le_mul count childrenCount
  have nameProductBound:=Nat.mul_le_mul count nameCount
  have totalSquare : total≤total^2 := le_self_pow positive (by decide)
  have wordCount : words.length=arguments.length := List.length_map _
  have frameBound : (WordTemplateMachine.Indexed.frame words).length≤6400*weightSum arguments+arguments.length := by
    rw [WordTemplateMachine.Indexed.frame_length,←List.length_flatten (L:=words),wordCount]
    exact Nat.add_le_add_right flattened arguments.length
  rw [exactOutput] at completed
  simp only [parentSize,List.length_nil] at completed
  change (termWire (dataTerm (.apply name arguments))).length≤6400*total at output
  change _≤1000000000*total^2
  rw [wordCount] at completed
  nlinarith


theorem opaqueClock_le (pattern : Pattern) (opaqueCase : isOpaque pattern=true) :
    nodeClock pattern (fun _=>[])≤1000000000*(W pattern)^3 := by
  have result:=literalFinishClock_le (patternSpan pattern) (fun _=>[])
  have span:=patternSpan_length pattern
  have positive:=pattern_weight_positive pattern
  have cube : W pattern≤(W pattern)^3 := le_self_pow (by omega) (by decide)
  have spanFields : (patternSpan pattern).length=
      (4::encodeWith Codec.string ((Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).headD "")).length+
      (Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.fields
        (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern).tail).length := by
    simp only [patternSpan,opaqueSpan,List.length_append]
  cases pattern <;> simp only [isOpaque,Bool.false_eq_true] at opaqueCase
  all_goals simp only [nodeClock,parentSize,List.length_nil] at result ⊢
  all_goals nlinarith


theorem nodeClock_polynomial (pattern : Pattern) :
    nodeClock pattern (fun _=>[])≤1000000000*(W pattern)^3 := by
  cases pattern with
  | apply name arguments=>
      have children:=childrenClock_le name [] arguments (fun argument member=>nodeClock_polynomial argument)
      have overhead:=constructorOverhead_le name arguments
      have source : weightSum arguments+1≤W (.apply name arguments) := by
        simp only [Mettapedia.OSLF.MeTTaIL.PatternTokens.weight,pattern_list_weight,weightSum]
        omega
      have gap:=Nat.mul_le_mul_left 1000000000 (cube_gap (weightSum arguments) (W (.apply name arguments)) source)
      rw [storedSize] at children
      simp only [List.flatten_nil,List.length_nil,Nat.mul_zero,Nat.add_zero] at children
      simp only [nodeClock,parentSize,List.length_nil]
      nlinarith
  | fvar name=>
      have result:=literalFinishClock_le (patternSpan (.fvar name)) (fun _=>[])
      have span:=patternSpan_length (.fvar name)
      have positive:=pattern_weight_positive (.fvar name)
      have cube : W (.fvar name)≤(W (.fvar name))^3 := le_self_pow (by omega) (by decide)
      have spanFields : (patternSpan (.fvar name)).length=
          (4::encodeWith Codec.string ((Mettapedia.OSLF.MeTTaIL.PatternTokens.encode (.fvar name)).headD "")).length+
          (Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.fields
            (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode (.fvar name)).tail).length := by
        simp only [patternSpan,opaqueSpan,List.length_append]
      simp only [nodeClock,parentSize,List.length_nil] at result ⊢
      nlinarith
  | bvar index=>exact opaqueClock_le _ rfl
  | lambda name body=>exact opaqueClock_le _ rfl
  | multiLambda arity names body=>exact opaqueClock_le _ rfl
  | subst body replacement=>exact opaqueClock_le _ rfl
  | collection kind arguments rest=>exact opaqueClock_le _ rfl
termination_by sizeOf pattern
decreasing_by
  have smaller:=List.sizeOf_lt_of_mem member
  simp only [Pattern.apply.sizeOf_spec]
  omega


theorem consumerClock_polynomial (pattern : Pattern) :
    consumerClock pattern≤2000000000*(patternWire pattern).length^3 := by
  have node:=nodeClock_polynomial pattern
  have term:=dataWord_length pattern
  have positive:=pattern_weight_positive pattern
  have cube : W pattern≤(W pattern)^3 := le_self_pow (by omega) (by decide)
  have source:=(patternWire_length_bounds pattern).1
  have sourceCube:=Nat.pow_le_pow_left source 3
  have scaled:=Nat.mul_le_mul_left 2000000000 sourceCube
  have coefficient : 1+4*(rootTemplate.length+1)≤10000 := by decide
  have constant : 10+4*(rootTemplate.length+1)+clearKeys.length≤10000 := by decide
  have termScaled:=Nat.mul_le_mul_right (termWire (dataTerm pattern)).length coefficient
  unfold consumerClock
  nlinarith

end RecursiveInputBounds

end Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Execution



namespace Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Routing
open Mettapedia.GSLT.LanguageDef.PatternSpanExecution
open Mettapedia.OSLF.MeTTaIL.Syntax

theorem initial_pattern_commands (pattern : Pattern) (hooks : List Hooks.Symbol)
    (traced : Hooks.Trace [.pattern] (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern) [] hooks) :
    route initial hooks=((.constructor,false,[]),commands pattern) := by
  have canonical:=pattern_commands pattern [] hooks traced
  generalize Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern=input at traced
  cases traced with
  | token accepted rest=>
      have firstSame (token : String) (tail : List Hooks.Symbol) :
          route initial (Hooks.field .pattern token++tail)=
            route (.constructor,false,[]) (Hooks.field .pattern token++tail) := by
        simp only [Hooks.field,List.cons_append,route]
        rfl
      exact (firstSame _ _).trans canonical

theorem commands_length (pattern : Pattern) :
    (commands pattern).length≤28*(patternWire pattern).length+2 := by
  obtain ⟨hooks,traced,erased,⟨executed⟩⟩:=Pipeline.outputs pattern
  have routed:=initial_pattern_commands pattern hooks traced
  have output:=route_length initial hooks
  rw [routed] at output
  change (commands pattern).length≤2*hooks.length at output
  have hookBound:=traced.hooks_length_le
  rw [erased] at hookBound
  have eventBound:=Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.pattern_events_length_le pattern
  have countBound:=Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.fields_count_le
    (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern)
  have fieldsBound : (Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.fields
      (Mettapedia.OSLF.MeTTaIL.PatternTokens.encode pattern)).length≤(patternWire pattern).length := by
    rw [patternWire,Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.original_pattern_wire,
      Mettapedia.GSLT.LanguageDef.PatternSpanExecution.Execution.tokenWire_eq,List.length_append]
    exact Nat.le_add_right _ _
  omega
end Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Routing

/-! The complete single-argument source-wire renderer composes the original
visitor and routing machine with the recursive argument consumer. Its bound
charges parsing, physical handoff, constructor assembly and final cleanup. -/
namespace Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Full
set_option maxRecDepth 4096
open Turing StateTransition
open Mettapedia.Computability
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

local instance outputFinite : Fintype (Routing.Pipeline.machine.Γ Routing.Pipeline.machine.k₁) := by
  change Fintype Routing.Symbol; infer_instance
local instance outputDefault : Inhabited (Routing.Pipeline.machine.Γ Routing.Pipeline.machine.k₁) := ⟨.refused⟩

def machine : FinTM2 := @StackMachineComposition.machine Routing.Pipeline.machine Execution.machine outputFinite outputDefault (Equiv.refl Routing.Symbol)

def program := StackMachineComposition.Programs.body
  (some (.inr Routing.Key.result) : Routing.Pipeline.machine.K) Execution.Key.input Execution.Phase.read
  (default : Routing.Pipeline.machine.Γ Routing.Pipeline.machine.k₁) (fun symbol : Routing.Symbol=>symbol) Routing.Pipeline.program Execution.program

theorem program_eq : machine.m=program := by
  unfold program
  rw [← Routing.Pipeline.program_eq]
  exact (@StackMachineComposition.body_eq Routing.Pipeline.machine Execution.machine outputFinite outputDefault (Equiv.refl Routing.Symbol)).symm

def clock (pattern : Pattern) : Nat :=124*(patternWire pattern).length+31+
  2*(Routing.commands pattern).length+2+Execution.consumerClock pattern

theorem outputs (pattern : Pattern) (admitted : argumentValidAt 0 pattern=true) :
    Nonempty (TM2OutputsInTime machine (patternWire pattern) (some (argumentWire pattern)) (clock pattern)) := by
  obtain ⟨hooks,traced,_,⟨routed⟩⟩:=Routing.Pipeline.outputs pattern
  rw [Routing.initial_pattern_commands pattern hooks traced] at routed
  have generated:=Execution.consumerOutputs pattern admitted
  have generated' : TM2OutputsInTime Execution.machine
      ((Routing.commands pattern).map (Equiv.refl Routing.Symbol)) (some (argumentWire pattern))
      (Execution.consumerClock pattern) := by simpa only [Equiv.coe_refl,List.map_id] using generated
  exact ⟨StackMachineComposition.outputs Routing.Pipeline.machine Execution.machine (Equiv.refl Routing.Symbol)
    (patternWire pattern) (Routing.commands pattern) (argumentWire pattern) _ _ routed generated'⟩

theorem clock_polynomial (pattern : Pattern) : clock pattern≤3000000000*((patternWire pattern).length+1)^3 := by
  have rendered:=Execution.consumerClock_polynomial pattern
  have commands:=Routing.commands_length pattern
  have positive : 1≤(patternWire pattern).length :=
    (by have p:=Mettapedia.Languages.HOLLight.InferenceStorageBounds.pattern_weight_positive pattern
        have q:=(Execution.patternWire_length_bounds pattern).1; omega)
  have cube : (patternWire pattern).length≤((patternWire pattern).length)^3 := le_self_pow positive (by decide)
  have enlargement:=Nat.pow_le_pow_left (Nat.le_add_right (patternWire pattern).length 1) 3
  have scaled:=Nat.mul_le_mul_left 3000000000 enlargement
  unfold clock
  nlinarith

theorem outputs_polynomial (pattern : Pattern) (admitted : argumentValidAt 0 pattern=true) :
    Nonempty (TM2OutputsInTime machine (patternWire pattern) (some (argumentWire pattern))
      (3000000000*((patternWire pattern).length+1)^3)) := by
  obtain ⟨executed⟩:=outputs pattern admitted
  exact ⟨⟨executed.toEvalsTo,executed.steps_le_m.trans (clock_polynomial pattern)⟩⟩

end Mettapedia.Languages.HOLLight.ArgumentRenderingMachine.Full
