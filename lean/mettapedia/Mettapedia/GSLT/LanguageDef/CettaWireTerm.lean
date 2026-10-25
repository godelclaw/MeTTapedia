/-!
# Physical CeTTa S-expression carrier

CeTTa's authored data protocols distinguish symbols, quoted strings, natural
numbers, and applications.  This module records that shared physical carrier
once, independently of any grammar, calculus, or proof protocol.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CettaWire

universe u v

/-- The distinctions retained by CeTTa's parsed S-expression carrier. -/
inductive Term where
  | symbol (name : String)
  | string (value : String)
  | natural (value : Nat)
  | application (head : String) (arguments : List Term)
deriving Repr

mutual

/-- Render one physical carrier value using CeTTa's authored catalog syntax. -/
def Term.render : Term -> String
  | .symbol name => name
  | .string value => reprStr value
  | .natural value => toString value
  | .application head arguments =>
      "(" ++ head ++ Term.renderArguments arguments ++ ")"

def Term.renderArguments : List Term -> String
  | [] => ""
  | argument :: arguments =>
      " " ++ argument.render ++ Term.renderArguments arguments

end

/-- The exact `LNil`/`LCons` algebraic-list carrier shared by CeTTa data
protocols. -/
def encodeList {α : Type u} (encode : α -> Term) : List α -> Term
  | [] => .symbol "LNil"
  | value :: values =>
      .application "LCons" [encode value, encodeList encode values]

/-- The shared physical `None`/`Some` option representation. The element
encoder determines the payload; absence introduces no payload value. -/
def encodeOption {α : Type u} (encode : α → Term) : Option α → Term
  | none => .symbol "None"
  | some value => .application "Some" [encode value]

@[simp] theorem encodeOption_none {α : Type u} (encode : α → Term) :
    encodeOption encode none = .symbol "None" := rfl

@[simp] theorem encodeOption_some {α : Type u} (encode : α → Term) (value : α) :
    encodeOption encode (some value) = .application "Some" [encode value] := rfl

/-- Mapping before encoding is the same physical list as composing the
element encoder. -/
@[simp] theorem encodeList_map {α : Type u} {β : Type v}
    (encode : β → Term) (transform : α → β) (values : List α) :
    encodeList encode (values.map transform) = encodeList (encode ∘ transform) values := by
  induction values with
  | nil => rfl
  | cons value values ih => simp only [List.map_cons, encodeList, ih, Function.comp_apply]

/-- Fail-closed decoding of the exact `LNil`/`LCons` carrier. -/
def decodeList {α : Type u} (decode : Term -> Option α) :
    Term -> Option (List α)
  | .symbol "LNil" => some []
  | .application "LCons" [value, values] => do
      let head <- decode value
      let tail <- decodeList decode values
      some (head :: tail)
  | _ => none
termination_by term => sizeOf term

@[simp] theorem decodeList_encodeList {α : Type u}
    (decode : Term -> Option α)
    (encode : α -> Term)
    (roundTrip : forall value, decode (encode value) = some value)
    (values : List α) :
    decodeList decode (encodeList encode values) = some values := by
  induction values with
  | nil => simp [encodeList, decodeList]
  | cons value values inductionHypothesis =>
      simp [encodeList, decodeList, roundTrip, inductionHypothesis]

/-- Successful decoding retains the complete source spelling when the
element codec has the same property. Extra structure cannot disappear into
an accepted list value. -/
theorem encodeList_decodeList {α : Type u}
    (decode : Term → Option α) (encode : α → Term)
    (elementExact : ∀ term value, decode term = some value → encode value = term)
    (term : Term) (values : List α)
    (accepted : decodeList decode term = some values) :
    encodeList encode values = term := by
  unfold decodeList at accepted
  split at accepted
  · cases Option.some.inj accepted
    rfl
  · rename_i head tail
    cases headDecoded : decode head with
    | none => simp [headDecoded] at accepted
    | some value =>
        cases tailDecoded : decodeList decode tail with
        | none => simp [headDecoded, tailDecoded] at accepted
        | some rest =>
            have same : value :: rest = values := by
              simpa [headDecoded, tailDecoded] using accepted
            subst values
            rw [encodeList, elementExact head value headDecoded,
              encodeList_decodeList decode encode elementExact tail rest tailDecoded]
  · cases accepted
termination_by sizeOf term

/-- A verified element decoder gives an exact injective list encoder. -/
theorem encodeList_injective_of_decode {α : Type u}
    (decode : Term → Option α) (encode : α → Term)
    (roundTrip : ∀ value, decode (encode value) = some value) :
    Function.Injective (encodeList encode) := by
  intro left right same
  have decoded := congrArg (decodeList decode) same
  rw [decodeList_encodeList decode encode roundTrip,
    decodeList_encodeList decode encode roundTrip] at decoded
  exact Option.some.inj decoded

/-- List encoding retains order and multiplicity whenever its element
encoder is injective. No choice of decoder is required. -/
theorem encodeList_injective {α : Type u} (encode : α → Term)
    (injective : Function.Injective encode) : Function.Injective (encodeList encode) := by
  intro left right same
  induction left generalizing right with
  | nil => cases right <;> simp_all [encodeList]
  | cons first rest ih =>
      cases right with
      | nil => simp [encodeList] at same
      | cons other tail =>
          have arguments := (Term.application.inj same).2
          have heads := (List.cons.inj arguments).1
          have tails := (List.cons.inj (List.cons.inj arguments).2).1
          rw [injective heads, ih tails]

/-- Heterogeneous list correspondence for a physical element encoder whose
decoder produces a distinct typed representation. -/
theorem decodeList_encodeList_map {α : Type u} {β : Type v}
    (decode : Term -> Option β) (encode : α -> Term) (meaning : α -> β)
    (elementExact : forall value, decode (encode value) = some (meaning value))
    (values : List α) :
    decodeList decode (encodeList encode values) = some (values.map meaning) := by
  induction values with
  | nil => simp [encodeList, decodeList]
  | cons value values inductionHypothesis =>
      simp [encodeList, decodeList, elementExact, inductionHypothesis]

end Mettapedia.GSLT.LanguageDef.CettaWire
