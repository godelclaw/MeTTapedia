import Mettapedia.OSLF.Syntax.BindingWireBinary
import Mettapedia.GSLT.LanguageDef.ExactEndpointCodec
import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

/-!
# Pattern serialization of parameterized scoped Pi/Sigma/identity syntax

One recursive codec handles arbitrary heads, scalar representations, terms,
contexts and coherent typing-claim data. Decoding checks intrinsic scope.
Groundness, canonical metadata and scalar-matching requirements remain explicit.
Cumulative profiles specialize this codec downstream. Fixed constructor tags
are retained protocol data, not a choice of a MeTTa foundation.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodec
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Fixed-alphabet scalar data -/

def encodeNat : Nat → Pattern
  | 0 => .apply "prime-nat-zero" []
  | n + 1 => .apply "prime-nat-succ" [encodeNat n]

def decodeNat? : Pattern → Option Nat
  | .apply "prime-nat-zero" [] => some 0
  | .apply "prime-nat-succ" [predecessor] => do
      pure ((← decodeNat? predecessor) + 1)
  | _ => none

@[simp] theorem decodeNat?_encodeNat (value : Nat) :
    decodeNat? (encodeNat value) = some value := by
  induction value with
  | zero => rfl
  | succ value ih => simp [encodeNat, decodeNat?, ih]

theorem encodeNat_injective : Function.Injective encodeNat :=
  PartialCodec.encode_injective
    { encode := encodeNat
      decode := decodeNat?
      decode_encode := decodeNat?_encodeNat }

def encodeChars : List Char → Pattern
  | [] => .apply "prime-string-nil" []
  | character :: rest =>
      .apply "prime-string-cons" [encodeNat character.toNat, encodeChars rest]

def decodeChars? : Pattern → Option (List Char)
  | .apply "prime-string-nil" [] => some []
  | .apply "prime-string-cons" [codepoint, rest] => do
      pure (Char.ofNat (← decodeNat? codepoint) :: (← decodeChars? rest))
  | _ => none

@[simp] theorem decodeChars?_encodeChars (characters : List Char) :
    decodeChars? (encodeChars characters) = some characters := by
  induction characters with
  | nil => rfl
  | cons character rest ih =>
      simp [encodeChars, decodeChars?, ih, Char.ofNat_toNat]

def encodeString (value : String) : Pattern := encodeChars value.toList

def decodeString? (encoded : Pattern) : Option String := do
  pure (String.ofList (← decodeChars? encoded))

@[simp] theorem decodeString?_encodeString (value : String) :
    decodeString? (encodeString value) = some value := by
  have rebuild : String.ofList value.toList = value := by
    apply String.toList_injective
    simp
  simp [decodeString?, encodeString, rebuild]

def encodeDeclName : Lean.Name → Pattern
  | .anonymous => .apply "prime-name-anonymous" []
  | .str pre component =>
      .apply "prime-name-string" [encodeDeclName pre, encodeString component]
  | .num pre component =>
      .apply "prime-name-number" [encodeDeclName pre, encodeNat component]

def decodeDeclName? : Pattern → Option Lean.Name
  | .apply "prime-name-anonymous" [] => some .anonymous
  | .apply "prime-name-string" [pre, component] => do
      pure (.str (← decodeDeclName? pre) (← decodeString? component))
  | .apply "prime-name-number" [pre, component] => do
      pure (.num (← decodeDeclName? pre) (← decodeNat? component))
  | _ => none

@[simp] theorem decodeDeclName?_encodeDeclName (name : Lean.Name) :
    decodeDeclName? (encodeDeclName name) = some name := by
  induction name with
  | anonymous => rfl
  | str pre component ih =>
      simp [encodeDeclName, decodeDeclName?, ih]
  | num pre component ih =>
      simp [encodeDeclName, decodeDeclName?, ih]

/-- Scalar encodings may change independently of the native constructor grammar. -/
structure ScalarCodecs where
  natural : PartialCodec Nat Pattern
  declaration : PartialCodec Lean.Name Pattern

abbrev existingScalars : ScalarCodecs where
  natural := ⟨encodeNat, decodeNat?, decodeNat?_encodeNat⟩
  declaration := ⟨encodeDeclName, decodeDeclName?, decodeDeclName?_encodeDeclName⟩

/-- A context, subject, and type sharing one intrinsic ambient arity. -/
structure TypingClaim (Head : Type) where
  arity : Nat
  context : Ctx Head arity
  subject : Tm Head arity
  type : Tm Head arity

/-- Structural binary scalars share the existing canonical UTF-8 and
binary wire. They are packet data inside the single native syntax codec. -/
def binaryScalar {α : Type} (codec : Mettapedia.OSLF.Binding.WireCodec.Codec α) :
    PartialCodec α Pattern where
  encode value := .fvar (Mettapedia.OSLF.Binding.WireCodec.Binary.Text.render
    (Mettapedia.OSLF.Binding.WireCodec.Binary.encodeWith codec value))
  decode
    | .fvar text => do
        Mettapedia.OSLF.Binding.WireCodec.Binary.decodeWith codec
          (← Mettapedia.OSLF.Binding.WireCodec.Binary.Text.parse text)
    | _ => none
  decode_encode value := by
    simp only [Mettapedia.OSLF.Binding.WireCodec.Binary.Text.parse_render,
      Mettapedia.OSLF.Binding.WireCodec.Binary.decodeWith_encodeWith, Bind.bind, Option.bind]

def binaryScalars : ScalarCodecs where
  natural := binaryScalar Mettapedia.OSLF.Binding.WireCodec.Codec.nat
  declaration := binaryScalar Mettapedia.OSLF.Binding.WireCodec.Codec.name

namespace WithScalars

abbrev encodeTm (scalars : ScalarCodecs) (headCodec : PartialCodec Head Pattern) :
    Tm Head n → Pattern
  | .var index => .apply "prime-tm-var" [scalars.natural.encode index.val]
  | .const name => .apply "prime-tm-const" [scalars.declaration.encode name]
  | .head head => .apply "prime-tm-head" [headCodec.encode head]
  | .pi domain body =>
      .apply "prime-tm-pi" [encodeTm scalars headCodec domain, encodeTm scalars headCodec body]
  | .sigma domain body =>
      .apply "prime-tm-sigma" [encodeTm scalars headCodec domain, encodeTm scalars headCodec body]
  | .id type left right =>
      .apply "prime-tm-id"
        [encodeTm scalars headCodec type, encodeTm scalars headCodec left,
          encodeTm scalars headCodec right]
  | .lam body => .apply "prime-tm-lam" [encodeTm scalars headCodec body]
  | .app function argument =>
      .apply "prime-tm-app"
        [encodeTm scalars headCodec function, encodeTm scalars headCodec argument]
  | .pair first second =>
      .apply "prime-tm-pair"
        [encodeTm scalars headCodec first, encodeTm scalars headCodec second]
  | .fst pair => .apply "prime-tm-fst" [encodeTm scalars headCodec pair]
  | .snd pair => .apply "prime-tm-snd" [encodeTm scalars headCodec pair]
  | .refl term => .apply "prime-tm-refl" [encodeTm scalars headCodec term]

@[simp] def decodeTm? (scalars : ScalarCodecs) (headCodec : PartialCodec Head Pattern) (n : Nat) :
    Pattern → Option (Tm Head n)
  | .apply "prime-tm-var" [encodedIndex] => do
      let index ← scalars.natural.decode encodedIndex
      if inScope : index < n then
        pure (.var ⟨index, inScope⟩)
      else
        none
  | .apply "prime-tm-const" [name] => do
      pure (.const (← scalars.declaration.decode name))
  | .apply "prime-tm-head" [head] => do
      pure (.head (← headCodec.decode head))
  | .apply "prime-tm-pi" [domain, body] => do
      pure (.pi (← decodeTm? scalars headCodec n domain)
        (← decodeTm? scalars headCodec (n + 1) body))
  | .apply "prime-tm-sigma" [domain, body] => do
      pure (.sigma (← decodeTm? scalars headCodec n domain)
        (← decodeTm? scalars headCodec (n + 1) body))
  | .apply "prime-tm-id" [type, left, right] => do
      pure (.id (← decodeTm? scalars headCodec n type)
        (← decodeTm? scalars headCodec n left) (← decodeTm? scalars headCodec n right))
  | .apply "prime-tm-lam" [body] => do
      pure (.lam (← decodeTm? scalars headCodec (n + 1) body))
  | .apply "prime-tm-app" [function, argument] => do
      pure (.app (← decodeTm? scalars headCodec n function)
        (← decodeTm? scalars headCodec n argument))
  | .apply "prime-tm-pair" [first, second] => do
      pure (.pair (← decodeTm? scalars headCodec n first)
        (← decodeTm? scalars headCodec n second))
  | .apply "prime-tm-fst" [pair] => do
      pure (.fst (← decodeTm? scalars headCodec n pair))
  | .apply "prime-tm-snd" [pair] => do
      pure (.snd (← decodeTm? scalars headCodec n pair))
  | .apply "prime-tm-refl" [term] => do
      pure (.refl (← decodeTm? scalars headCodec n term))
  | _ => none

@[simp] theorem decodeTm?_encodeTm (scalars : ScalarCodecs)
    (headCodec : PartialCodec Head Pattern) (term : Tm Head n) :
    decodeTm? scalars headCodec n (encodeTm scalars headCodec term) = some term := by
  induction term with
  | var index =>
      simp [encodeTm, decodeTm?, scalars.natural.decode_encode, index.isLt]
  | const name => simp [encodeTm, decodeTm?, scalars.declaration.decode_encode]
  | head head => simp [encodeTm, decodeTm?, headCodec.decode_encode]
  | pi domain body domainIH bodyIH =>
      simp [encodeTm, decodeTm?, domainIH, bodyIH]
  | sigma domain body domainIH bodyIH =>
      simp [encodeTm, decodeTm?, domainIH, bodyIH]
  | id type left right typeIH leftIH rightIH =>
      simp [encodeTm, decodeTm?, typeIH, leftIH, rightIH]
  | lam body bodyIH => simp [encodeTm, decodeTm?, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [encodeTm, decodeTm?, functionIH, argumentIH]
  | pair first second firstIH secondIH =>
      simp [encodeTm, decodeTm?, firstIH, secondIH]
  | fst pair pairIH => simp [encodeTm, decodeTm?, pairIH]
  | snd pair pairIH => simp [encodeTm, decodeTm?, pairIH]
  | refl term termIH => simp [encodeTm, decodeTm?, termIH]

abbrev tmCodec (scalars : ScalarCodecs) (headCodec : PartialCodec Head Pattern) (n : Nat) :
    PartialCodec (Tm Head n) Pattern where
  encode := encodeTm scalars headCodec
  decode := decodeTm? scalars headCodec n
  decode_encode := decodeTm?_encodeTm scalars headCodec

abbrev encodeCtx (scalars : ScalarCodecs) (headCodec : PartialCodec Head Pattern) :
    Ctx Head n → Pattern
  | .nil => .apply "prime-ctx-nil" []
  | .snoc context type =>
      .apply "prime-ctx-snoc"
        [encodeCtx scalars headCodec context, encodeTm scalars headCodec type]

@[simp] def decodeCtx? (scalars : ScalarCodecs) (headCodec : PartialCodec Head Pattern) :
    (n : Nat) → Pattern → Option (Ctx Head n)
  | 0, .apply "prime-ctx-nil" [] => some .nil
  | n + 1, .apply "prime-ctx-snoc" [context, type] => do
      pure (.snoc (← decodeCtx? scalars headCodec n context)
        (← decodeTm? scalars headCodec n type))
  | _, _ => none

@[simp] theorem decodeCtx?_encodeCtx (scalars : ScalarCodecs)
    (headCodec : PartialCodec Head Pattern) (context : Ctx Head n) :
    decodeCtx? scalars headCodec n (encodeCtx scalars headCodec context) = some context := by
  induction context with
  | nil => rfl
  | snoc context type contextIH =>
      simp [encodeCtx, decodeCtx?, contextIH]

abbrev ctxCodec (scalars : ScalarCodecs) (headCodec : PartialCodec Head Pattern) (n : Nat) :
    PartialCodec (Ctx Head n) Pattern where
  encode := encodeCtx scalars headCodec
  decode := decodeCtx? scalars headCodec n
  decode_encode := decodeCtx?_encodeCtx scalars headCodec

/-! ## One scope-coherent typing-claim carrier -/

abbrev encodeTypingClaim (scalars : ScalarCodecs) (headCodec : PartialCodec Head Pattern)
    (claim : TypingClaim Head) : Pattern :=
  .apply "prime-has-type"
    [scalars.natural.encode claim.arity, encodeCtx scalars headCodec claim.context,
      encodeTm scalars headCodec claim.subject, encodeTm scalars headCodec claim.type]

abbrev decodeTypingClaim? (scalars : ScalarCodecs) (headCodec : PartialCodec Head Pattern) :
    Pattern → Option (TypingClaim Head)
  | .apply "prime-has-type" [arity, context, subject, type] => do
      let n ← scalars.natural.decode arity
      pure
        { arity := n
          context := ← decodeCtx? scalars headCodec n context
          subject := ← decodeTm? scalars headCodec n subject
          type := ← decodeTm? scalars headCodec n type }
  | _ => none

@[simp] theorem decodeTypingClaim?_encodeTypingClaim (scalars : ScalarCodecs)
    (headCodec : PartialCodec Head Pattern) (claim : TypingClaim Head) :
    decodeTypingClaim? scalars headCodec (encodeTypingClaim scalars headCodec claim) =
      some claim := by
  cases claim
  simp [encodeTypingClaim, decodeTypingClaim?, scalars.natural.decode_encode]

abbrev typingClaimCodec (scalars : ScalarCodecs) (headCodec : PartialCodec Head Pattern) :
    PartialCodec (TypingClaim Head) Pattern where
  encode := encodeTypingClaim scalars headCodec
  decode := decodeTypingClaim? scalars headCodec
  decode_encode := decodeTypingClaim?_encodeTypingClaim scalars headCodec

end WithScalars

abbrev encodeTm (headCodec : PartialCodec Head Pattern) : Tm Head n → Pattern :=
  WithScalars.encodeTm existingScalars headCodec

abbrev decodeTm? (headCodec : PartialCodec Head Pattern) (n : Nat) : Pattern → Option (Tm Head n) :=
  WithScalars.decodeTm? existingScalars headCodec n

@[simp] theorem decodeTm?_encodeTm (headCodec : PartialCodec Head Pattern) (term : Tm Head n) :
    decodeTm? headCodec n (encodeTm headCodec term) = some term :=
  WithScalars.decodeTm?_encodeTm existingScalars headCodec term

def tmCodec (headCodec : PartialCodec Head Pattern) (n : Nat) : PartialCodec (Tm Head n) Pattern :=
  WithScalars.tmCodec existingScalars headCodec n

abbrev encodeCtx (headCodec : PartialCodec Head Pattern) : Ctx Head n → Pattern :=
  WithScalars.encodeCtx existingScalars headCodec

abbrev decodeCtx? (headCodec : PartialCodec Head Pattern) : (n : Nat) → Pattern → Option (Ctx Head n) :=
  WithScalars.decodeCtx? existingScalars headCodec

@[simp] theorem decodeCtx?_encodeCtx (headCodec : PartialCodec Head Pattern) (context : Ctx Head n) :
    decodeCtx? headCodec n (encodeCtx headCodec context) = some context :=
  WithScalars.decodeCtx?_encodeCtx existingScalars headCodec context

def ctxCodec (headCodec : PartialCodec Head Pattern) (n : Nat) : PartialCodec (Ctx Head n) Pattern :=
  WithScalars.ctxCodec existingScalars headCodec n

abbrev encodeTypingClaim (headCodec : PartialCodec Head Pattern) (claim : TypingClaim Head) : Pattern :=
  WithScalars.encodeTypingClaim existingScalars headCodec claim

abbrev decodeTypingClaim? (headCodec : PartialCodec Head Pattern) : Pattern → Option (TypingClaim Head) :=
  WithScalars.decodeTypingClaim? existingScalars headCodec

@[simp] theorem decodeTypingClaim?_encodeTypingClaim
    (headCodec : PartialCodec Head Pattern) (claim : TypingClaim Head) :
    decodeTypingClaim? headCodec (encodeTypingClaim headCodec claim) = some claim :=
  WithScalars.decodeTypingClaim?_encodeTypingClaim existingScalars headCodec claim

def typingClaimCodec (headCodec : PartialCodec Head Pattern) : PartialCodec (TypingClaim Head) Pattern :=
  WithScalars.typingClaimCodec existingScalars headCodec

/-! ## Checker-side shape laws -/

theorem encodeNat_ground (value : Nat) :
    (encodeNat value).isGroundAt 0 = true := by
  induction value with
  | zero => simp [encodeNat, Pattern.isGroundAt, Pattern.isGroundListAt]
  | succ value ih =>
      simp [encodeNat, Pattern.isGroundAt, Pattern.isGroundListAt, ih]

theorem encodeNat_canonical (value : Nat) :
    (encodeNat value).hasCanonicalBinderMetadata = true := by
  induction value with
  | zero =>
      simp [encodeNat, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | succ value ih =>
      simp [encodeNat, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, ih]

private theorem encodeChars_ground (characters : List Char) :
    (encodeChars characters).isGroundAt 0 = true := by
  induction characters with
  | nil => simp [encodeChars, Pattern.isGroundAt, Pattern.isGroundListAt]
  | cons character rest ih =>
      simp [encodeChars, Pattern.isGroundAt, Pattern.isGroundListAt,
        encodeNat_ground, ih]

private theorem encodeChars_canonical (characters : List Char) :
    (encodeChars characters).hasCanonicalBinderMetadata = true := by
  induction characters with
  | nil =>
      simp [encodeChars, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | cons character rest ih =>
      simp [encodeChars, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, encodeNat_canonical, ih]

theorem encodeDeclName_ground (name : Lean.Name) :
    (encodeDeclName name).isGroundAt 0 = true := by
  induction name with
  | anonymous =>
      simp [encodeDeclName, Pattern.isGroundAt, Pattern.isGroundListAt]
  | str pre component ih =>
      simp [encodeDeclName, encodeString, Pattern.isGroundAt,
        Pattern.isGroundListAt, ih, encodeChars_ground]
  | num pre component ih =>
      simp [encodeDeclName, Pattern.isGroundAt, Pattern.isGroundListAt,
        ih, encodeNat_ground]

theorem encodeDeclName_canonical (name : Lean.Name) :
    (encodeDeclName name).hasCanonicalBinderMetadata = true := by
  induction name with
  | anonymous =>
      simp [encodeDeclName, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | str pre component ih =>
      simp [encodeDeclName, encodeString, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, ih, encodeChars_canonical]
  | num pre component ih =>
      simp [encodeDeclName, Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, ih, encodeNat_canonical]

/-- The shape properties needed when encoded syntax is itself admitted as
closed, canonical Pattern data. Exact transport alone does not imply them. -/
structure ScalarAdmissible (scalars : ScalarCodecs) : Prop where
  naturalGround : ∀ value, (scalars.natural.encode value).isGroundAt 0 = true
  naturalCanonical : ∀ value, (scalars.natural.encode value).hasCanonicalBinderMetadata = true
  declarationGround : ∀ value, (scalars.declaration.encode value).isGroundAt 0 = true
  declarationCanonical : ∀ value, (scalars.declaration.encode value).hasCanonicalBinderMetadata = true

theorem existingScalarsAdmissible : ScalarAdmissible existingScalars where
  naturalGround := encodeNat_ground
  naturalCanonical := encodeNat_canonical
  declarationGround := encodeDeclName_ground
  declarationCanonical := encodeDeclName_canonical

namespace WithScalars

theorem encodeTm_ground (scalars : ScalarCodecs) (admissible : ScalarAdmissible scalars) (headCodec : PartialCodec Head Pattern)
    (headGround : ∀ head, (headCodec.encode head).isGroundAt 0 = true)
    (term : Tm Head n) :
    (encodeTm scalars headCodec term).isGroundAt 0 = true := by
  induction term with
  | var index =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt,
        admissible.naturalGround]
  | const name =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt,
        admissible.declarationGround]
  | head head =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt,
        headGround]
  | pi domain body domainIH bodyIH =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt,
        domainIH, bodyIH]
  | sigma domain body domainIH bodyIH =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt,
        domainIH, bodyIH]
  | id type left right typeIH leftIH rightIH =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt,
        typeIH, leftIH, rightIH]
  | lam body bodyIH =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt,
        functionIH, argumentIH]
  | pair first second firstIH secondIH =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt,
        firstIH, secondIH]
  | fst pair pairIH =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt, pairIH]
  | snd pair pairIH =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt, pairIH]
  | refl term termIH =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt, termIH]

theorem encodeTm_canonical (scalars : ScalarCodecs) (admissible : ScalarAdmissible scalars) (headCodec : PartialCodec Head Pattern)
    (headCanonical : ∀ head,
      (headCodec.encode head).hasCanonicalBinderMetadata = true)
    (term : Tm Head n) :
    (encodeTm scalars headCodec term).hasCanonicalBinderMetadata = true := by
  induction term with
  | var index =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, admissible.naturalCanonical]
  | const name =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, admissible.declarationCanonical]
  | head head =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, headCanonical]
  | pi domain body domainIH bodyIH =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, domainIH, bodyIH]
  | sigma domain body domainIH bodyIH =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, domainIH, bodyIH]
  | id type left right typeIH leftIH rightIH =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, typeIH, leftIH, rightIH]
  | lam body bodyIH =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, bodyIH]
  | app function argument functionIH argumentIH =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, functionIH, argumentIH]
  | pair first second firstIH secondIH =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, firstIH, secondIH]
  | fst pair pairIH =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, pairIH]
  | snd pair pairIH =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, pairIH]
  | refl term termIH =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, termIH]

theorem encodeCtx_ground (scalars : ScalarCodecs) (admissible : ScalarAdmissible scalars) (headCodec : PartialCodec Head Pattern)
    (headGround : ∀ head, (headCodec.encode head).isGroundAt 0 = true)
    (context : Ctx Head n) :
    (encodeCtx scalars headCodec context).isGroundAt 0 = true := by
  induction context with
  | nil => simp [Pattern.isGroundAt, Pattern.isGroundListAt]
  | snoc context type contextIH =>
      simp [Pattern.isGroundAt, Pattern.isGroundListAt,
        contextIH, encodeTm_ground scalars admissible headCodec headGround]

theorem encodeCtx_canonical (scalars : ScalarCodecs) (admissible : ScalarAdmissible scalars) (headCodec : PartialCodec Head Pattern)
    (headCanonical : ∀ head,
      (headCodec.encode head).hasCanonicalBinderMetadata = true)
    (context : Ctx Head n) :
    (encodeCtx scalars headCodec context).hasCanonicalBinderMetadata = true := by
  induction context with
  | nil =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList]
  | snoc context type contextIH =>
      simp [Pattern.hasCanonicalBinderMetadata,
        Pattern.hasCanonicalBinderMetadataList, contextIH,
        encodeTm_canonical scalars admissible headCodec headCanonical]

end WithScalars

theorem encodeTm_ground (headCodec : PartialCodec Head Pattern)
    (headGround : ∀ head, (headCodec.encode head).isGroundAt 0 = true)
    (term : Tm Head n) :
    (encodeTm headCodec term).isGroundAt 0 = true :=
  WithScalars.encodeTm_ground existingScalars existingScalarsAdmissible headCodec headGround term

theorem encodeTm_canonical (headCodec : PartialCodec Head Pattern)
    (headCanonical : ∀ head,
      (headCodec.encode head).hasCanonicalBinderMetadata = true)
    (term : Tm Head n) :
    (encodeTm headCodec term).hasCanonicalBinderMetadata = true :=
  WithScalars.encodeTm_canonical existingScalars existingScalarsAdmissible headCodec headCanonical term

theorem encodeCtx_ground (headCodec : PartialCodec Head Pattern)
    (headGround : ∀ head, (headCodec.encode head).isGroundAt 0 = true)
    (context : Ctx Head n) :
    (encodeCtx headCodec context).isGroundAt 0 = true :=
  WithScalars.encodeCtx_ground existingScalars existingScalarsAdmissible headCodec headGround context

theorem encodeCtx_canonical (headCodec : PartialCodec Head Pattern)
    (headCanonical : ∀ head,
      (headCodec.encode head).hasCanonicalBinderMetadata = true)
    (context : Ctx Head n) :
    (encodeCtx headCodec context).hasCanonicalBinderMetadata = true :=
  WithScalars.encodeCtx_canonical existingScalars existingScalarsAdmissible headCodec headCanonical context

theorem encodeNat_argumentValid (value : Nat) :
    argumentValidAt 0 (encodeNat value) = true := by
  simp [argumentValidAt, encodeNat_ground, encodeNat_canonical]

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PatternCodec
