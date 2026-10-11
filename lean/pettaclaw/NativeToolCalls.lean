/-!
# NativeToolCalls — command structure before content

The `singnet/Omega` loop asks the model for up to five commands as text and
parses the reply into MeTTa calls. Untrusted text reaches the model through
messages, files and web pages; on ingest, real newlines and quotes are replaced
by the words `_newline_` and `_quote_`, while those words already present in
the text pass unchanged.

* Before pull request #379 (merged as `2117654`), the reply was decoded first,
  turning every `_newline_` back into a newline, and then split into command
  lines. A model repeating `menu_newline_shell rm -rf ~` inside a `send`
  produced a second command line, `shell rm -rf ~`.
* #379 splits on real newlines first and decodes tokens only inside each
  argument.
* #358 (head `030c014`, open; part of #349, head `9d28e83`) asks the provider for
  native tool calls. It validates each call against the tools advertised in
  that request (`_validate_response`: a known name and every declared parameter
  present as a string), then serializes the calls to S-expression text,
  escaping `"` as `\"` and `\` as `\\`, and reads that text back with `sread`
  before evaluation. #349 also builds the turn's message list as the
  assistant's tool-call message followed by one result per call.

Results:
* `decode_then_split_injects`: decoding before splitting turns relayed data
  into a new command. `split_then_decode_keeps_commands`: with #379 the number
  of commands equals the number of real lines the model wrote, whatever tokens
  the arguments contain.
* `readStr_escape` and `roundtrip`: when the reader inverts the writer's
  escaping, reading the serialized calls returns exactly the structured calls,
  so argument text cannot add, remove or rename a call.
* `quirky_reader_misplaces_boundary` and `quirky_breaks_roundtrip`: a reader
  that honors `\"` but not `\\` ends an argument in the wrong place, and a call
  whose argument ends in a backslash no longer parses, so the whole batch
  fails. Text leaked outside a literal cannot start a new literal, because the
  writer escapes every quote; the failure observed in this model is a rejected
  batch, not an injected call. The property to check against the deployed
  reader is `readStr_escape`.
* `validated_call_was_advertised`: a call passes validation only if the
  request advertised its name and it supplies every declared parameter.

A CeTTa-native loop builds each call as an atom directly from the provider's
structured fields, with arguments as grounded strings, so no text is parsed and
no escaping contract exists to violate. Validation stays as #358 has it,
against the tool set captured in the request.
-/

namespace NativeToolCalls

/-- Symbols: quote, backslash, newline, parentheses, space, the `_newline_`
token and other characters. -/
inductive Sym
  | quote
  | backslash
  | newline
  | lparen
  | rparen
  | space
  | token
  | chr (n : Nat)
deriving Repr, DecidableEq

/-! ## Splitting text replies -/

def splitLines : List Sym → List (List Sym)
  | [] => [[]]
  | .newline :: rest => [] :: splitLines rest
  | x :: rest =>
      match splitLines rest with
      | l :: ls => (x :: l) :: ls
      | [] => [[x]]

/-- Decode the `_newline_` token. -/
def decode : List Sym → List Sym
  | [] => []
  | .token :: rest => .newline :: decode rest
  | x :: rest => x :: decode rest

def beforeFix (reply : List Sym) : List (List Sym) := splitLines (decode reply)

def afterFix (reply : List Sym) : List (List Sym) := (splitLines reply).map decode

/-- Untrusted text `menu_newline_shell rm`, relayed inside one `send` command. -/
def relayed : List Sym :=
  [.chr 50, .space, .quote, .chr 1, .token, .chr 2, .space, .chr 3, .quote]

theorem decode_then_split_injects :
    (beforeFix relayed).length = 2 ∧ (afterFix relayed).length = 1 := by
  decide

theorem split_then_decode_keeps_commands (reply : List Sym) :
    (afterFix reply).length = (splitLines reply).length := by
  simp [afterFix]

/-! ## Structured calls serialized as text -/

def escape : List Sym → List Sym
  | [] => []
  | .quote :: s => .backslash :: .quote :: escape s
  | .backslash :: s => .backslash :: .backslash :: escape s
  | x :: s => x :: escape s

/-- A string-literal reader after the opening quote: `\x` reads `x`. Returns
the content and the text after the closing quote. -/
def readStr : List Sym → Option (List Sym × List Sym)
  | [] => none
  | .quote :: rest => some ([], rest)
  | [.backslash] => none
  | .backslash :: x :: rest => (readStr rest).map (fun r => (x :: r.1, r.2))
  | x :: rest => (readStr rest).map (fun r => (x :: r.1, r.2))

theorem readStr_escape (s rest : List Sym) :
    readStr (escape s ++ .quote :: rest) = some (s, rest) := by
  induction s with
  | nil => simp [escape, readStr]
  | cons x s ih =>
    cases x <;> simp [escape, readStr, ih]

structure CallT where
  name : Nat
  args : List (List Sym)
deriving Repr, DecidableEq

def argText (a : List Sym) : List Sym := .space :: .quote :: (escape a ++ [.quote])

def callText (c : CallT) : List Sym :=
  .lparen :: .chr c.name :: ((c.args.map argText).flatten ++ [.rparen])

def serialize (cs : List CallT) : List Sym := (cs.map callText).flatten

abbrev Reader := List Sym → Option (List Sym × List Sym)

def parseArgs (rd : Reader) : Nat → List Sym → Option (List (List Sym) × List Sym)
  | 0, _ => none
  | _ + 1, .rparen :: rest => some ([], rest)
  | n + 1, .space :: .quote :: rest =>
      match rd rest with
      | some (a, r) => (parseArgs rd n r).map (fun p => (a :: p.1, p.2))
      | none => none
  | _ + 1, _ => none

def parseCalls (rd : Reader) : Nat → List Sym → Option (List CallT)
  | _, [] => some []
  | 0, _ :: _ => none
  | n + 1, .lparen :: .chr name :: rest =>
      match parseArgs rd (rest.length + 1) rest with
      | some (args, r) => (parseCalls rd n r).map (fun cs => ⟨name, args⟩ :: cs)
      | none => none
  | _ + 1, _ :: _ => none

theorem parseArgs_roundtrip (args : List (List Sym)) (rest : List Sym) (fuel : Nat)
    (h : args.length < fuel) :
    parseArgs readStr fuel ((args.map argText).flatten ++ .rparen :: rest) = some (args, rest) := by
  induction args generalizing fuel with
  | nil =>
    match fuel, h with
    | n + 1, _ => simp [parseArgs]
  | cons a as ih =>
    match fuel, h with
    | n + 1, h =>
      simp only [List.map_cons, List.flatten_cons, argText, List.cons_append, parseArgs,
        List.append_assoc, readStr_escape, List.nil_append]
      rw [ih n (by simp at h; omega)]
      rfl

theorem args_length_le (args : List (List Sym)) :
    args.length ≤ ((args.map argText).flatten).length := by
  induction args with
  | nil => simp
  | cons a as ih =>
    have h1 : 1 ≤ (argText a).length := by simp [argText]
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem roundtrip (cs : List CallT) (k : Nat) :
    parseCalls readStr (cs.length + k) (serialize cs) = some cs := by
  induction cs generalizing k with
  | nil => simp [serialize, parseCalls]
  | cons c cs ih =>
    have hser : serialize (c :: cs) =
        .lparen :: .chr c.name :: ((c.args.map argText).flatten ++ .rparen :: serialize cs) := by
      simp [serialize, callText]
    have hfuel : (c :: cs).length + k = (cs.length + k) + 1 := by simp; omega
    rw [hser, hfuel]
    simp only [parseCalls]
    rw [parseArgs_roundtrip c.args (serialize cs) _ (by
      have := args_length_le c.args
      simp only [List.length_append, List.length_cons]
      omega)]
    simp [ih k]

/-- A reader that honors `\"` but not `\\`. -/
def readStrQ : List Sym → Option (List Sym × List Sym)
  | [] => none
  | .quote :: rest => some ([], rest)
  | .backslash :: .quote :: rest => (readStrQ rest).map (fun r => (.quote :: r.1, r.2))
  | x :: rest => (readStrQ rest).map (fun r => (x :: r.1, r.2))

/-- An argument ending in a backslash, followed by a second argument: the
reader takes the closing quote as escaped, ends the literal at the next
argument's opening quote, and leaves that argument's text outside any
literal. -/
theorem quirky_reader_misplaces_boundary :
    readStrQ (escape [.backslash] ++ [.quote, .space, .quote, .chr 5, .quote]) =
      some ([.backslash, .quote, .space], [.chr 5, .quote]) := by
  decide

theorem quirky_breaks_roundtrip :
    let cs := [CallT.mk 1 [[.backslash]]]
    parseCalls readStr 1 (serialize cs) = some cs ∧ parseCalls readStrQ 1 (serialize cs) = none := by
  decide

/-! ## Validation against the request -/

structure Tool where
  name : Nat
  params : List Nat
deriving Repr, DecidableEq

/-- A provider call: name and arguments, each with whether it is a string. -/
structure RawCall where
  name : Nat
  args : List (Nat × Bool)
deriving Repr, DecidableEq

/-- `_validate_response`. -/
def validate (tools : List Tool) (c : RawCall) : Bool :=
  match tools.find? (fun t => t.name == c.name) with
  | some t => t.params.all (fun p => c.args.any (fun a => a.1 == p && a.2))
  | none => false

theorem validated_call_was_advertised (tools : List Tool) (c : RawCall)
    (h : validate tools c = true) :
    ∃ t ∈ tools, t.name = c.name ∧ ∀ p ∈ t.params, (p, true) ∈ c.args := by
  unfold validate at h
  split at h
  · rename_i t ht
    refine ⟨t, List.mem_of_find?_eq_some ht, ?_, ?_⟩
    · have := List.find?_some ht
      simpa using this
    · intro p hp
      have := List.all_eq_true.mp h p hp
      obtain ⟨a, ha, hsat⟩ := List.any_eq_true.mp this
      simp only [Bool.and_eq_true, beq_iff_eq] at hsat
      obtain ⟨h1, h2⟩ := hsat
      have : a = (p, true) := by
        obtain ⟨a1, a2⟩ := a
        simp only at h1 h2
        subst h1; subst h2; rfl
      exact this ▸ ha
  · cases h

end NativeToolCalls

/-! ## Axiom audit -/
#print axioms NativeToolCalls.decode_then_split_injects
#print axioms NativeToolCalls.split_then_decode_keeps_commands
#print axioms NativeToolCalls.readStr_escape
#print axioms NativeToolCalls.parseArgs_roundtrip
#print axioms NativeToolCalls.args_length_le
#print axioms NativeToolCalls.roundtrip
#print axioms NativeToolCalls.quirky_reader_misplaces_boundary
#print axioms NativeToolCalls.quirky_breaks_roundtrip
#print axioms NativeToolCalls.validated_call_was_advertised
