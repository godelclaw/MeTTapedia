import Mettapedia.Computability.OriginalMachineTrace
import Mathlib.Data.List.OfFn
import Mathlib.Data.Nat.Pairing
import Mettapedia.OSLF.Syntax.BindingWireBinary

/-!
# Finite data for original stack-machine traces

An ordered finite profile represents every internal alphabet, register value,
label and stack key. Actual statement functions are sampled into literal tables;
the table interpreter below has no function-valued instruction fields. Complete
configurations retain stack order, multiplicity and the original register value.
The profile is additional data: `FinTM2` alone does not make every alphabet finite.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.OriginalMachineTraceEncoding
open Turing

/-- Explicit ordered representations, including all internal alphabets. -/
structure FiniteProfile (machine : FinTM2) where
  stackCount : Nat
  labels : Nat
  states : Nat
  symbols : machine.K → Nat
  stackIndex : machine.K ≃ Fin stackCount
  labelIndex : machine.Λ ≃ Fin labels
  stateIndex : machine.σ ≃ Fin states
  symbolIndex : (k : machine.K) → machine.Γ k ≃ Fin (symbols k)

/-- The entire configuration, with stack columns in the profile's order. -/
structure Configuration where
  label : Option Nat
  state : Nat
  columns : List (List Nat)
  deriving DecidableEq, Repr

/-- Literal instruction data. Peek/pop rows put the empty-stack case first. -/
inductive Statement where
  | push (stack : Nat) (table : List Nat) (next : Statement)
  | peek (stack : Nat) (table : List (List Nat)) (next : Statement)
  | pop (stack : Nat) (table : List (List Nat)) (next : Statement)
  | load (table : List Nat) (next : Statement)
  | branch (table : List Bool) (yes no : Statement)
  | goto (table : List Nat)
  | halt
  deriving DecidableEq, Repr

namespace Statement

/-- Default values make malformed raw data executable; correspondence is earned
on generated descriptors and complete encoded configurations. -/
def run : Statement → Nat → List (List Nat) → Configuration
  | .push k table next, state, columns =>
      run next state (columns.set k ((table.getD state 0) :: columns.getD k []))
  | .peek k table next, state, columns =>
      run next ((table.getD state []).getD
        ((columns.getD k []).head?.map Nat.succ |>.getD 0) 0) columns
  | .pop k table next, state, columns =>
      run next ((table.getD state []).getD
        ((columns.getD k []).head?.map Nat.succ |>.getD 0) 0)
        (columns.set k (columns.getD k []).tail)
  | .load table next, state, columns => run next (table.getD state 0) columns
  | .branch table yes no, state, columns =>
      if table.getD state false then run yes state columns else run no state columns
  | .goto table, state, columns => ⟨some (table.getD state 0), state, columns⟩
  | .halt, state, columns => ⟨none, state, columns⟩

end Statement

/-- The payload pairs contain the ordered elements; the separate count controls decoding. -/
def encodePayload : List Nat → Nat
  | [] => 0
  | head :: tail => Nat.pair head (encodePayload tail)

def decodePayload : Nat → Nat → List Nat
  | 0, _ => []
  | count + 1, payload => payload.unpair.1 :: decodePayload count payload.unpair.2

def dropPayload : Nat → Nat → Nat
  | 0, payload => payload
  | count + 1, payload => dropPayload count payload.unpair.2

def encodeList (values : List Nat) : Nat := Nat.pair values.length (encodePayload values)
def decodeList (packet : Nat) : List Nat := decodePayload packet.unpair.1 packet.unpair.2

theorem decodePayload_encodePayload (values : List Nat) :
    decodePayload values.length (encodePayload values) = values := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [encodePayload, decodePayload, ih]

theorem decodeList_encodeList (values : List Nat) : decodeList (encodeList values) = values := by
  simp only [decodeList, encodeList, Nat.unpair_pair, decodePayload_encodePayload]

theorem decodePayload_length (count payload : Nat) : (decodePayload count payload).length = count := by
  induction count generalizing payload with
  | zero => rfl
  | succ count ih => simp only [decodePayload, List.length_cons, ih]

theorem dropPayload_encodePayload (values : List Nat) : dropPayload values.length (encodePayload values) = 0 := by
  induction values with
  | nil => rfl
  | cons head tail ih => simp [dropPayload, encodePayload, ih]

theorem encodePayload_decodePayload (count payload : Nat) (exhausted : dropPayload count payload = 0) :
    encodePayload (decodePayload count payload) = payload := by
  induction count generalizing payload with
  | zero => exact exhausted.symm
  | succ count ih =>
      simp only [dropPayload] at exhausted
      simp only [decodePayload, encodePayload, ih _ exhausted, Nat.pair_unpair]

theorem encodeList_decodeList (packet : Nat) (exhausted : dropPayload packet.unpair.1 packet.unpair.2 = 0) :
    encodeList (decodeList packet) = packet := by
  simp only [encodeList, decodeList, decodePayload_length,
    encodePayload_decodePayload _ _ exhausted, Nat.pair_unpair]

def readList (packet : Nat) : Option (List Nat) :=
  if encodeList (decodeList packet) = packet then some (decodeList packet) else none

theorem readList_encodeList (values : List Nat) : readList (encodeList values) = some values := by
  simp only [readList, decodeList_encodeList, ↓reduceIte]

theorem encodeList_injective : Function.Injective encodeList :=
  Function.LeftInverse.injective decodeList_encodeList

theorem encodeList_eq_zero (values : List Nat) : encodeList values = 0 ↔ values = [] := by
  have empty : encodeList [] = 0 := rfl
  rw [← empty, encodeList_injective.eq_iff]

def canonicalWord (packet : Nat) : Bool := decide (encodeList (decodeList packet) = packet)

theorem canonicalWord_exhausted (packet : Nat) : canonicalWord packet = true ↔
    dropPayload packet.unpair.1 packet.unpair.2 = 0 := by
  simp only [canonicalWord, decide_eq_true_eq]
  constructor
  · intro canonical
    rw [← canonical, encodeList, Nat.unpair_pair]
    exact dropPayload_encodePayload _
  · exact encodeList_decodeList packet

theorem all_fixed_iff_map {normalize : Nat → Nat}
    (idempotent : ∀ value, normalize (normalize value) = normalize value) (values : List Nat) :
    values.all (fun value => decide (normalize value = value)) = true ↔ values.map normalize = values := by
  constructor
  · intro fixed
    have pointwise : ∀ value ∈ values, normalize value = value := by
      simpa only [List.all_eq_true, decide_eq_true_eq] using fixed
    calc
      values.map normalize = values.map id := List.map_congr_left pointwise
      _ = values := List.map_id _
  · intro mapped
    rw [← mapped, List.all_map]
    simp only [Function.comp_def, idempotent, decide_true, List.all_eq_true]
    exact fun _ _ => trivial

theorem mappedPacket_fixed_iff {normalize : Nat → Nat}
    (idempotent : ∀ value, normalize (normalize value) = normalize value) (packet : Nat) :
    encodeList ((decodeList packet).map normalize) = packet ↔
      canonicalWord packet = true ∧
        (decodeList packet).all (fun value => decide (normalize value = value)) = true := by
  rw [all_fixed_iff_map (normalize := normalize) idempotent]
  constructor
  · intro equality
    have mapped := congrArg decodeList equality
    rw [decodeList_encodeList] at mapped
    exact ⟨by simpa only [canonicalWord, decide_eq_true_eq, mapped] using equality, mapped⟩
  · rintro ⟨outer, mapped⟩
    rw [mapped]
    exact of_decide_eq_true outer

namespace Statement

def depth : Statement → Nat
  | .push _ _ next | .peek _ _ next | .pop _ _ next | .load _ next => next.depth + 1
  | .branch _ yes no => max yes.depth no.depth + 1
  | .goto _ | .halt => 1

def encode : Statement → Nat
  | .push stack table next => encodeList [0, stack, encodeList table, next.encode]
  | .peek stack table next => encodeList [1, stack, encodeList (table.map encodeList), next.encode]
  | .pop stack table next => encodeList [2, stack, encodeList (table.map encodeList), next.encode]
  | .load table next => encodeList [3, encodeList table, next.encode]
  | .branch table yes no => encodeList
      [4, encodeList (table.map (fun value => if value then 1 else 0)), yes.encode, no.encode]
  | .goto table => encodeList [5, encodeList table]
  | .halt => encodeList [6]

private def decodeBoolean (value : Nat) : Option Bool :=
  if value = 0 then some false else if value = 1 then some true else none

private theorem decodeBooleans_encode (values : List Bool) :
    (values.map (fun value => if value then 1 else 0)).mapM decodeBoolean = some values := by
  induction values with
  | nil => rfl
  | cons value rest ih => cases value <;> simp [decodeBoolean, ih]

/-- The supplied structural depth bounds decoding; it is not a runtime TM clock. -/
def decode : Nat → Nat → Option Statement
  | 0, _ => none
  | fuel + 1, packet =>
      match decodeList packet with
      | [0, stack, table, next] =>
          (decode fuel next).map (.push stack (decodeList table))
      | [1, stack, table, next] =>
          (decode fuel next).map (.peek stack ((decodeList table).map decodeList))
      | [2, stack, table, next] =>
          (decode fuel next).map (.pop stack ((decodeList table).map decodeList))
      | [3, table, next] => (decode fuel next).map (.load (decodeList table))
      | [4, table, yes, no] => do
          let values ← (decodeList table).mapM decodeBoolean
          let yes ← decode fuel yes
          let no ← decode fuel no
          pure (.branch values yes no)
      | [5, table] => some (.goto (decodeList table))
      | [6] => some .halt
      | _ => none

theorem decode_encode (statement : Statement) (fuel : Nat) (enough : statement.depth ≤ fuel) :
    decode fuel statement.encode = some statement := by
  induction statement generalizing fuel with
  | push stack table next ih | peek stack table next ih | pop stack table next ih =>
      cases fuel with
      | zero => simp only [depth] at enough; omega
      | succ fuel =>
          have bound : next.depth ≤ fuel := by simpa only [depth, Nat.add_le_add_iff_right] using enough
          simp [encode, decode, decodeList_encodeList, ih fuel bound, List.map_map, Function.comp_def]
  | load table next ih =>
      cases fuel with
      | zero => simp only [depth] at enough; omega
      | succ fuel =>
          have bound : next.depth ≤ fuel := by simpa only [depth, Nat.add_le_add_iff_right] using enough
          simp [encode, decode, decodeList_encodeList, ih fuel bound]
  | branch table yes no iy ino =>
      cases fuel with
      | zero => simp only [depth] at enough; omega
      | succ fuel =>
          have bounds : yes.depth ≤ fuel ∧ no.depth ≤ fuel := by
            simp only [depth] at enough
            omega
          simp only [encode, decode, decodeList_encodeList, decodeBooleans_encode,
            iy fuel bounds.1, ino fuel bounds.2, Option.pure_def]
          rfl
  | goto table =>
      cases fuel with
      | zero => simp only [depth] at enough; omega
      | succ fuel => simp [encode, decode, decodeList_encodeList]
  | halt =>
      cases fuel with
      | zero => simp only [depth] at enough; omega
      | succ fuel => simp [encode, decode, decodeList_encodeList]

def packet (statement : Statement) : Nat := Nat.pair statement.depth statement.encode
def readPacket (value : Nat) : Option Statement :=
  (decode value.unpair.1 value.unpair.2).bind
    (fun statement => if statement.packet = value then some statement else none)

theorem readPacket_packet (statement : Statement) : readPacket statement.packet = some statement := by
  simp [readPacket, packet, decode_encode]

end Statement

namespace Configuration

def encode (configuration : Configuration) : Nat :=
  Nat.pair (configuration.label.map Nat.succ |>.getD 0)
    (Nat.pair configuration.state (encodeList (configuration.columns.map encodeList)))

def decode (packet : Nat) : Configuration :=
  let fields := packet.unpair
  ⟨if fields.1 = 0 then none else some fields.1.pred,
    fields.2.unpair.1, (decodeList fields.2.unpair.2).map decodeList⟩

theorem decode_encode (configuration : Configuration) : decode (encode configuration) = configuration := by
  cases configuration with
  | mk label state columns =>
      cases label <;> simp [encode, decode, decodeList_encodeList, List.map_map, Function.comp_def]

theorem encode_injective : Function.Injective encode :=
  Function.LeftInverse.injective decode_encode

def read (packet : Nat) : Option Configuration :=
  if encode (decode packet) = packet then some (decode packet) else none

theorem read_encode (configuration : Configuration) : read configuration.encode = some configuration := by
  simp only [read, decode_encode, ↓reduceIte]

def canonical (packet : Nat) : Bool := decide ((decode packet).encode = packet)

theorem canonical_columns (packet : Nat) : canonical packet = true ↔
    canonicalWord packet.unpair.2.unpair.2 = true ∧
      (decodeList packet.unpair.2.unpair.2).all canonicalWord = true := by
  let words := packet.unpair.2.unpair.2
  have label : ((if packet.unpair.1 = 0 then none else some packet.unpair.1.pred).map
      Nat.succ).getD 0 = packet.unpair.1 := by
    by_cases zero : packet.unpair.1 = 0
    · simp [zero]
    · simp only [if_neg zero, Option.map_some, Option.getD_some]
      exact Nat.succ_pred_eq_of_ne_zero zero
  have expression : (decode packet).encode = Nat.pair packet.unpair.1
      (Nat.pair packet.unpair.2.unpair.1
        (encodeList ((decodeList words).map (fun value => encodeList (decodeList value))))) := by
    simp only [decode, encode, List.map_map, Function.comp_def, label]
    rfl
  have original : packet = Nat.pair packet.unpair.1
      (Nat.pair packet.unpair.2.unpair.1 words) := by
    simp only [words, Nat.pair_unpair]
  simp only [canonical, decide_eq_true_eq, expression]
  conv_lhs => rhs; exact original
  simp only [Nat.pair_eq_pair, true_and]
  change _ ↔ canonicalWord words = true ∧ (decodeList words).all canonicalWord = true
  exact mappedPacket_fixed_iff (normalize := fun value => encodeList (decodeList value))
    (fun value => congrArg encodeList (decodeList_encodeList (decodeList value))) words

end Configuration

/-- A finite program descriptor. All transition functions have become data. -/
structure Descriptor where
  stackCount : Nat
  main : Nat
  initialState : Nat
  inputStack : Nat
  outputStack : Nat
  program : List Statement
  deriving DecidableEq, Repr

namespace Descriptor

def encode (descriptor : Descriptor) : Nat :=
  encodeList [descriptor.stackCount, descriptor.main, descriptor.initialState,
    descriptor.inputStack, descriptor.outputStack,
    encodeList (descriptor.program.map Statement.packet)]

private def decodeFields (packet : Nat) : Option Descriptor :=
  match decodeList packet with
  | [count, main, initialState, input, output, program] =>
      ((decodeList program).mapM Statement.readPacket).map
        (fun statements => ⟨count, main, initialState, input, output, statements⟩)
  | _ => none

def decode (packet : Nat) : Option Descriptor :=
  (decodeFields packet).bind
    (fun descriptor => if descriptor.encode = packet then some descriptor else none)

theorem decode_encode (descriptor : Descriptor) : decode descriptor.encode = some descriptor := by
  have program : (descriptor.program.map Statement.packet).mapM Statement.readPacket =
      some descriptor.program := by
    induction descriptor.program with
    | nil => rfl
    | cons statement rest ih => simp [Statement.readPacket_packet, ih]
  have fields : decodeFields descriptor.encode = some descriptor := by
    simp [decodeFields, encode, decodeList_encodeList, program]
  simp only [decode, fields, Option.bind_some, ↓reduceIte]

theorem decode_canonical {packet : Nat} {descriptor : Descriptor}
    (decoded : decode packet = some descriptor) : descriptor.encode = packet := by
  unfold decode at decoded
  cases fields : decodeFields packet with
  | none => simp [fields] at decoded
  | some result =>
      simp only [fields, Option.bind_some] at decoded
      split at decoded
      · cases decoded
        assumption
      · cases decoded

def step (descriptor : Descriptor) (configuration : Configuration) : Option Configuration :=
  configuration.label.bind (fun label =>
    descriptor.program[label]?.map (fun statement =>
      statement.run configuration.state configuration.columns))

def initial (descriptor : Descriptor) (input : List Nat) : Configuration :=
  ⟨some descriptor.main, descriptor.initialState,
    (List.replicate descriptor.stackCount []).set descriptor.inputStack input⟩

def terminal (descriptor : Descriptor) (output : List Nat) : Configuration :=
  ⟨none, descriptor.initialState,
    (List.replicate descriptor.stackCount []).set descriptor.outputStack output⟩

def replay (descriptor : Descriptor) : Configuration → List Configuration → Option Configuration
  | start, [] => some start
  | start, next :: rest =>
      if descriptor.step start = some next then descriptor.replay next rest else none

/-- Exact endpoint equality includes all registers and every scratch column. -/
def accepts (descriptor : Descriptor) (input output : List Nat)
    (trace : List Configuration) : Bool :=
  decide (descriptor.replay (descriptor.initial input) trace = some (descriptor.terminal output))

/-- Trace packets contain complete configurations, never supplied acceptance bits. -/
def acceptsPacket (descriptor : Descriptor) (input output trace : Nat) : Bool :=
  descriptor.accepts (decodeList input) (decodeList output)
    ((decodeList trace).map Configuration.decode)

theorem wrong_successor (descriptor : Descriptor) (start next : Configuration)
    (rest : List Configuration) (wrong : descriptor.step start ≠ some next) :
    descriptor.replay start (next :: rest) = none := by
  simp only [replay, if_neg wrong]

end Descriptor

structure OriginalDescriptor where
  program : Descriptor
  inputCapacity : Nat
  outputCapacity : Nat
  deriving DecidableEq, Repr

namespace Bytes
open Mettapedia.OSLF.Binding.WireCodec

private def boolCodec : Codec Bool :=
  Codec.nat.mapped (fun value => if value then 1 else 0)
    (fun value => if value = 0 then some false else if value = 1 then some true else none)
    (fun value => by cases value <;> rfl)

def putStatement : Statement → Data
  | .push stack table next => .pair (.atom 0)
      (.pair (.atom stack) (.pair ((Codec.list Codec.nat).put table) (putStatement next)))
  | .peek stack table next => .pair (.atom 1)
      (.pair (.atom stack) (.pair ((Codec.list (Codec.list Codec.nat)).put table) (putStatement next)))
  | .pop stack table next => .pair (.atom 2)
      (.pair (.atom stack) (.pair ((Codec.list (Codec.list Codec.nat)).put table) (putStatement next)))
  | .load table next => .pair (.atom 3) (.pair ((Codec.list Codec.nat).put table) (putStatement next))
  | .branch table yes no => .pair (.atom 4)
      (.pair ((Codec.list boolCodec).put table) (.pair (putStatement yes) (putStatement no)))
  | .goto table => .pair (.atom 5) ((Codec.list Codec.nat).put table)
  | .halt => .atom 6

def getStatement : Data → Option Statement
  | .pair (.atom 0) (.pair (.atom stack) (.pair table next)) =>
      do return .push stack (← (Codec.list Codec.nat).get table) (← getStatement next)
  | .pair (.atom 1) (.pair (.atom stack) (.pair table next)) =>
      do return .peek stack (← (Codec.list (Codec.list Codec.nat)).get table) (← getStatement next)
  | .pair (.atom 2) (.pair (.atom stack) (.pair table next)) =>
      do return .pop stack (← (Codec.list (Codec.list Codec.nat)).get table) (← getStatement next)
  | .pair (.atom 3) (.pair table next) =>
      do return .load (← (Codec.list Codec.nat).get table) (← getStatement next)
  | .pair (.atom 4) (.pair table (.pair yes no)) =>
      do return .branch (← (Codec.list boolCodec).get table) (← getStatement yes) (← getStatement no)
  | .pair (.atom 5) table => (.goto ·) <$> (Codec.list Codec.nat).get table
  | .atom 6 => some .halt
  | _ => none

theorem get_putStatement (statement : Statement) : getStatement (putStatement statement) = some statement := by
  induction statement with
  | push stack table next ih | peek stack table next ih | pop stack table next ih =>
      simp only [putStatement, getStatement, Codec.get_put, ih]
      rfl
  | load table next ih =>
      simp only [putStatement, getStatement, Codec.get_put, ih]
      rfl
  | branch table yes no iy ino =>
      simp only [putStatement, getStatement, Codec.get_put, iy, ino]
      rfl
  | goto table => simp only [putStatement, getStatement, Codec.get_put]; rfl
  | halt => rfl

def statementCodec : Codec Statement := ⟨putStatement, getStatement, get_putStatement⟩

def descriptorCodec : Codec Descriptor :=
  (Codec.prod Codec.nat (Codec.prod Codec.nat (Codec.prod Codec.nat
    (Codec.prod Codec.nat (Codec.prod Codec.nat (Codec.list statementCodec)))))).mapped
    (fun descriptor => (descriptor.stackCount, descriptor.main, descriptor.initialState,
      descriptor.inputStack, descriptor.outputStack, descriptor.program))
    (fun value => some ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1,
      value.2.2.2.2.1, value.2.2.2.2.2⟩) (fun _ => rfl)

private def optionNatCodec : Codec (Option Nat) :=
  Codec.nat.mapped (fun value => (value.map Nat.succ).getD 0)
    (fun value => some (if value = 0 then none else some value.pred))
    (fun value => by cases value <;> simp)

def configurationCodec : Codec Configuration :=
  (Codec.prod optionNatCodec (Codec.prod Codec.nat (Codec.list (Codec.list Codec.nat)))).mapped
    (fun configuration => (configuration.label, configuration.state, configuration.columns))
    (fun value => some ⟨value.1, value.2.1, value.2.2⟩) (fun _ => rfl)

def encodeDescriptor (descriptor : Descriptor) : List Binary.Alphabet :=
  Binary.encodeWith descriptorCodec descriptor

def decodeDescriptor (word : List Binary.Alphabet) : Option Descriptor :=
  (Binary.decodeWith descriptorCodec word).bind
    (fun descriptor => if encodeDescriptor descriptor = word then some descriptor else none)

theorem descriptor_roundtrip (descriptor : Descriptor) :
    decodeDescriptor (encodeDescriptor descriptor) = some descriptor := by
  simp only [decodeDescriptor, encodeDescriptor, Binary.decodeWith_encodeWith,
    Option.bind_some, ↓reduceIte]

theorem descriptor_trailing_refused (descriptor : Descriptor) (tail : List Binary.Alphabet)
    (nonempty : tail.isEmpty = false) : decodeDescriptor (encodeDescriptor descriptor ++ tail) = none := by
  simp only [decodeDescriptor, encodeDescriptor,
    Binary.decodeWith_trailing_refused descriptorCodec descriptor tail nonempty, Option.bind_none]

theorem decodeDescriptor_canonical {word : List Binary.Alphabet} {descriptor : Descriptor}
    (decoded : decodeDescriptor word = some descriptor) : encodeDescriptor descriptor = word := by
  unfold decodeDescriptor at decoded
  cases parsed : Binary.decodeWith descriptorCodec word with
  | none => simp [parsed] at decoded
  | some result =>
      simp only [parsed, Option.bind_some] at decoded
      split at decoded
      · cases decoded
        assumption
      · cases decoded

def originalDescriptorCodec : Codec OriginalDescriptor :=
  (Codec.prod descriptorCodec (Codec.prod Codec.nat Codec.nat)).mapped
    (fun descriptor => (descriptor.program, descriptor.inputCapacity, descriptor.outputCapacity))
    (fun value => some ⟨value.1, value.2.1, value.2.2⟩) (fun _ => rfl)

def encodeOriginalDescriptor (descriptor : OriginalDescriptor) : List Binary.Alphabet :=
  Binary.encodeWith originalDescriptorCodec descriptor

def decodeOriginalDescriptor (word : List Binary.Alphabet) : Option OriginalDescriptor :=
  (Binary.decodeWith originalDescriptorCodec word).bind
    (fun descriptor => if encodeOriginalDescriptor descriptor = word then some descriptor else none)

theorem originalDescriptor_roundtrip (descriptor : OriginalDescriptor) :
    decodeOriginalDescriptor (encodeOriginalDescriptor descriptor) = some descriptor := by
  simp only [decodeOriginalDescriptor, encodeOriginalDescriptor, Binary.decodeWith_encodeWith,
    Option.bind_some, ↓reduceIte]

theorem originalDescriptor_trailing_refused (descriptor : OriginalDescriptor) (tail : List Binary.Alphabet)
    (nonempty : tail.isEmpty = false) :
    decodeOriginalDescriptor (encodeOriginalDescriptor descriptor ++ tail) = none := by
  simp only [decodeOriginalDescriptor, encodeOriginalDescriptor,
    Binary.decodeWith_trailing_refused originalDescriptorCodec descriptor tail nonempty, Option.bind_none]

end Bytes

namespace TraceCursor

abbrev Cursor := Option (Configuration × List Configuration)

def encode : Cursor → Nat
  | none => 0
  | some (current, rest) =>
      Nat.pair 1 (Nat.pair current.encode (encodeList (rest.map Configuration.encode)))

def decode (packet : Nat) : Cursor :=
  if packet = 0 then none else some
    (Configuration.decode packet.unpair.2.unpair.1,
      (decodeList packet.unpair.2.unpair.2).map Configuration.decode)

theorem decode_encode (cursor : Cursor) : decode (encode cursor) = cursor := by
  cases cursor with
  | none => simp [decode, encode]
  | some pair =>
      rcases pair with ⟨current, rest⟩
      have nonzero : Nat.pair 1 (Nat.pair current.encode (encodeList (rest.map Configuration.encode))) ≠ 0 := by
        intro zero
        have lower := Nat.left_le_pair 1 (Nat.pair current.encode (encodeList (rest.map Configuration.encode)))
        rw [zero] at lower
        omega
      simp [decode, encode, nonzero, decodeList_encodeList, Configuration.decode_encode,
        List.map_map, Function.comp_def]

def advance (descriptor : Descriptor) : Cursor → Cursor
  | none => none
  | some (_, []) => none
  | some (current, next :: rest) =>
      if descriptor.step current = some next then some (next, rest) else none

def run (descriptor : Descriptor) (count : Nat) (cursor : Cursor) : Cursor :=
  (advance descriptor)^[count] cursor

theorem run_none (descriptor : Descriptor) (count : Nat) : run descriptor count none = none :=
  Function.iterate_fixed rfl count

/-- Count exhaustion and cursor exhaustion are both required. -/
theorem run_complete_iff (descriptor : Descriptor) (count : Nat)
    (start finish : Configuration) (trace : List Configuration) :
    run descriptor count (some (start, trace)) = some (finish, []) ↔
      trace.length = count ∧ descriptor.replay start trace = some finish := by
  induction count generalizing start trace with
  | zero =>
      cases trace with
      | nil => simp [run, Descriptor.replay]
      | cons next rest => simp [run]
  | succ count ih =>
      rw [run, Function.iterate_succ_apply]
      cases trace with
      | nil =>
          change run descriptor count none = _ ↔ _
          rw [run_none]
          simp
      | cons next rest =>
          by_cases edge : descriptor.step start = some next
          · simp only [advance, if_pos edge]
            change run descriptor count (some (next, rest)) = _ ↔ _
            rw [ih]
            simp only [List.length_cons, Nat.add_right_cancel_iff, Descriptor.replay, if_pos edge]
          · simp only [advance, if_neg edge]
            change run descriptor count none = _ ↔ _
            rw [run_none]
            simp [Descriptor.replay, edge]

def accepts (descriptor : Descriptor) (input output : List Nat)
    (count : Nat) (trace : List Configuration) : Bool :=
  decide (run descriptor count (some (descriptor.initial input, trace)) =
    some (descriptor.terminal output, []))

theorem accepts_iff (descriptor : Descriptor) (input output : List Nat)
    (count : Nat) (trace : List Configuration) :
    accepts descriptor input output count trace = true ↔
      trace.length = count ∧ descriptor.accepts input output trace = true := by
  simp only [accepts, Descriptor.accepts, decide_eq_true_eq, run_complete_iff]

end TraceCursor

/-- Count is a separate field from the encoded trace and from evaluator fuel. -/
structure Request where
  input : List Nat
  output : List Nat
  trace : List Configuration
  count : Nat
  deriving DecidableEq, Repr

namespace Request

def payload (request : Request) : Nat :=
  Nat.pair (encodeList request.input)
    (Nat.pair (encodeList request.output) (encodeList (request.trace.map Configuration.encode)))

def encode (request : Request) : Nat := Nat.pair request.payload request.count

def decode (packet : Nat) : Request :=
  let payload := packet.unpair.1
  ⟨decodeList payload.unpair.1, decodeList payload.unpair.2.unpair.1,
    (decodeList payload.unpair.2.unpair.2).map Configuration.decode, packet.unpair.2⟩

theorem decode_encode (request : Request) : decode request.encode = request := by
  cases request
  simp [decode, encode, payload, decodeList_encodeList, List.map_map, Function.comp_def,
    Configuration.decode_encode]

def read (packet : Nat) : Option Request :=
  if encode (decode packet) = packet then some (decode packet) else none

theorem read_encode (request : Request) : read request.encode = some request := by
  simp only [read, decode_encode, ↓reduceIte]

theorem read_canonical {packet : Nat} {request : Request}
    (decoded : read packet = some request) : request.encode = packet := by
  unfold read at decoded
  split at decoded
  · cases decoded
    assumption
  · cases decoded

def canonical (packet : Nat) : Bool := decide ((decode packet).encode = packet)

theorem canonical_fields (packet : Nat) : canonical packet = true ↔
    canonicalWord packet.unpair.1.unpair.1 = true ∧
      canonicalWord packet.unpair.1.unpair.2.unpair.1 = true ∧
        canonicalWord packet.unpair.1.unpair.2.unpair.2 = true ∧
          (decodeList packet.unpair.1.unpair.2.unpair.2).all Configuration.canonical = true := by
  have original : packet = Nat.pair
      (Nat.pair packet.unpair.1.unpair.1
        (Nat.pair packet.unpair.1.unpair.2.unpair.1 packet.unpair.1.unpair.2.unpair.2))
      packet.unpair.2 := by simp only [Nat.pair_unpair]
  simp only [canonical, decode, encode, payload, List.map_map, Function.comp_def, decide_eq_true_eq]
  conv_lhs => rhs; exact original
  simp only [Nat.pair_eq_pair, and_true]
  rw [mappedPacket_fixed_iff (normalize := fun value => (Configuration.decode value).encode)
    (fun value => congrArg Configuration.encode
    (Configuration.decode_encode (Configuration.decode value)))]
  simp only [canonicalWord, decide_eq_true_eq]
  rfl

def check (descriptor : Descriptor) (request : Request) : Bool :=
  TraceCursor.accepts descriptor request.input request.output request.count request.trace

end Request

namespace FiniteProfile

variable {machine : FinTM2} (profile : FiniteProfile machine)

def encodeWord (k : machine.K) (word : List (machine.Γ k)) : List Nat :=
  word.map (fun symbol => (profile.symbolIndex k symbol).val)

def encodeStacks (columns : (k : machine.K) → List (machine.Γ k)) : List (List Nat) :=
  List.ofFn (fun index : Fin profile.stackCount =>
    profile.encodeWord (profile.stackIndex.symm index) (columns (profile.stackIndex.symm index)))

def encodeConfiguration (configuration : machine.Cfg) : Configuration :=
  ⟨configuration.l.map (fun label => (profile.labelIndex label).val),
    (profile.stateIndex configuration.var).val, profile.encodeStacks configuration.stk⟩

private theorem lookup_ofFn {α : Type} {count : Nat} (values : Fin count → α)
    (index : Fin count) (fallback : α) :
    (List.ofFn values).getD index.val fallback = values index := by
  simp [List.getD, index.isLt]

theorem encodeStacks_lookup (columns : (k : machine.K) → List (machine.Γ k))
    (k : machine.K) :
    (profile.encodeStacks columns).getD (profile.stackIndex k).val [] =
      profile.encodeWord k (columns k) := by
  dsimp only [encodeStacks]
  rw [lookup_ofFn, Equiv.symm_apply_apply]

theorem encodeStacks_update (columns : (k : machine.K) → List (machine.Γ k))
    (k : machine.K) (word : List (machine.Γ k)) :
    profile.encodeStacks (Function.update columns k word) =
      (profile.encodeStacks columns).set (profile.stackIndex k).val (profile.encodeWord k word) := by
  apply List.ext_getElem
  · simp [encodeStacks]
  · intro index leftBound rightBound
    have bound : index < profile.stackCount := by simpa [encodeStacks] using leftBound
    let key := profile.stackIndex.symm ⟨index, bound⟩
    by_cases same : key = k
    · have indexSame : index = (profile.stackIndex k).val := by
        have h := congrArg (fun x => (profile.stackIndex x).val) same
        simpa [key] using h
      subst index
      simp only [encodeStacks, List.getElem_ofFn, List.getElem_set_self]
      rw [Equiv.symm_apply_apply, Function.update_self]
    · have indexDifferent : index ≠ (profile.stackIndex k).val := by
        intro h
        apply same
        apply profile.stackIndex.injective
        apply Fin.ext
        simpa [key] using h
      simp only [encodeStacks, List.getElem_ofFn, List.getElem_set,
        Ne.symm indexDifferent, ↓reduceIte]
      change profile.encodeWord key (Function.update columns k word key) =
        profile.encodeWord key (columns key)
      rw [Function.update_of_ne same]

private def stateTable {α : Type} (encode : α → Nat) (function : machine.σ → α) : List Nat :=
  List.ofFn (fun index : Fin profile.states => encode (function (profile.stateIndex.symm index)))

private def symbolTable (k : machine.K)
    (function : machine.σ → Option (machine.Γ k) → machine.σ) : List (List Nat) :=
  List.ofFn (fun state : Fin profile.states =>
    (profile.stateIndex (function (profile.stateIndex.symm state) none)).val ::
      List.ofFn (fun symbol : Fin (profile.symbols k) =>
        (profile.stateIndex (function (profile.stateIndex.symm state)
          (some (profile.symbolIndex k |>.symm symbol)))).val))

/-- Sample the actual original callbacks, with linear state tables and rectangular
state/symbol tables, rather than a catalogue of all configurations or traces. -/
def lowerStatement (profile : FiniteProfile machine) :
    TM2.Stmt machine.Γ machine.Λ machine.σ → Statement
  | .push k function next => .push (profile.stackIndex k).val
      (profile.stateTable (fun symbol => (profile.symbolIndex k symbol).val) function)
      (profile.lowerStatement next)
  | .peek k function next => .peek (profile.stackIndex k).val
      (profile.symbolTable k function) (profile.lowerStatement next)
  | .pop k function next => .pop (profile.stackIndex k).val
      (profile.symbolTable k function) (profile.lowerStatement next)
  | .load function next => .load
      (profile.stateTable (fun state => (profile.stateIndex state).val) function)
      (profile.lowerStatement next)
  | .branch function yes no => .branch
      (List.ofFn (fun state : Fin profile.states => function (profile.stateIndex.symm state)))
      (profile.lowerStatement yes) (profile.lowerStatement no)
  | .goto function => .goto
      (profile.stateTable (fun label => (profile.labelIndex label).val) function)
  | .halt => .halt

private theorem stateTable_lookup {α : Type} (encode : α → Nat)
    (function : machine.σ → α) (state : machine.σ) :
    (profile.stateTable encode function).getD (profile.stateIndex state).val 0 =
      encode (function state) := by
  simp [stateTable]

private theorem symbolTable_lookup (k : machine.K)
    (function : machine.σ → Option (machine.Γ k) → machine.σ)
    (state : machine.σ) (symbol : Option (machine.Γ k)) :
    ((profile.symbolTable k function).getD (profile.stateIndex state).val []).getD
      ((symbol.map (fun value => (profile.symbolIndex k value).val.succ)).getD 0) 0 =
      (profile.stateIndex (function state symbol)).val := by
  cases symbol <;> simp [symbolTable, List.getD]

theorem lowerStatement_run (statement : TM2.Stmt machine.Γ machine.Λ machine.σ) (state : machine.σ)
    (columns : (k : machine.K) → List (machine.Γ k)) :
    (profile.lowerStatement statement).run (profile.stateIndex state).val
      (profile.encodeStacks columns) =
      profile.encodeConfiguration (TM2.stepAux statement state columns) := by
  induction statement generalizing state columns with
  | push k function next ih =>
      simp only [lowerStatement, Statement.run, stateTable_lookup, encodeStacks_lookup]
      change (profile.lowerStatement next).run (profile.stateIndex state).val
        ((profile.encodeStacks columns).set (profile.stackIndex k).val
          (profile.encodeWord k (function state :: columns k))) = _
      rw [← encodeStacks_update]
      simpa only [TM2.stepAux] using ih state (Function.update columns k (function state :: columns k))
  | peek k function next ih =>
      simp only [lowerStatement, Statement.run, encodeStacks_lookup]
      have head : ((profile.encodeWord k (columns k)).head?.map Nat.succ).getD 0 =
          ((columns k).head?.map (fun value => (profile.symbolIndex k value).val.succ)).getD 0 := by
        cases columns k <;> rfl
      rw [head, symbolTable_lookup]
      exact ih _ _
  | pop k function next ih =>
      simp only [lowerStatement, Statement.run, encodeStacks_lookup]
      have head : ((profile.encodeWord k (columns k)).head?.map Nat.succ).getD 0 =
          ((columns k).head?.map (fun value => (profile.symbolIndex k value).val.succ)).getD 0 := by
        cases columns k <;> rfl
      rw [head, symbolTable_lookup]
      have tail : (profile.encodeWord k (columns k)).tail =
          profile.encodeWord k (columns k).tail := by cases columns k <;> rfl
      rw [tail, ← encodeStacks_update]
      exact ih _ _
  | load function next ih =>
      simpa only [lowerStatement, Statement.run, stateTable_lookup, TM2.stepAux] using ih (function state) columns
  | branch function yes no iy ino =>
      simp only [lowerStatement, Statement.run, lookup_ofFn, Equiv.symm_apply_apply]
      cases value : function state
      · simpa only [value, Bool.false_eq_true, if_false, TM2.stepAux, Bool.cond_false] using ino state columns
      · simpa only [value, if_true, TM2.stepAux, Bool.cond_true] using iy state columns
  | goto function =>
      simp only [lowerStatement, Statement.run, stateTable_lookup, encodeConfiguration,
        TM2.stepAux, Option.map_some]
  | halt => rfl

theorem encodeWord_injective (k : machine.K) : Function.Injective (profile.encodeWord k) := by
  apply List.map_injective_iff.mpr
  intro first second same
  apply (profile.symbolIndex k).injective
  exact Fin.ext same

def wordWithin (k : machine.K) (word : List Nat) : Bool :=
  word.all (fun value => decide (value < profile.symbols k))

def checkedWord (k : machine.K) (word : List Nat) (bounded : profile.wordWithin k word = true) :
    List (machine.Γ k) :=
  word.attach.map (fun value => (profile.symbolIndex k).symm
    ⟨value.1, of_decide_eq_true ((List.all_eq_true.mp bounded) value.1 value.2)⟩)

def decodeWord (k : machine.K) (word : List Nat) : Option (List (machine.Γ k)) :=
  if bounded : profile.wordWithin k word = true then
    some (profile.checkedWord k word bounded)
  else none

theorem decodeWord_exists (k : machine.K) (word : List Nat)
    (bounded : profile.wordWithin k word = true) : ∃ original, profile.decodeWord k word = some original := by
  unfold decodeWord
  rw [dif_pos bounded]
  exact ⟨_, rfl⟩

theorem encode_decodeWord (k : machine.K) {word : List Nat} {original : List (machine.Γ k)}
    (decoded : profile.decodeWord k word = some original) : profile.encodeWord k original = word := by
  unfold decodeWord at decoded
  split at decoded
  · cases decoded
    simp only [encodeWord, checkedWord, List.map_map, Function.comp_def, Equiv.apply_symm_apply]
    simpa only [List.map_id, id_eq] using (List.attach_map_val (l := word) (f := id))
  · cases decoded

theorem encode_checkedWord (k : machine.K) (word : List Nat)
    (bounded : profile.wordWithin k word = true) :
    profile.encodeWord k (profile.checkedWord k word bounded) = word := by
  apply profile.encode_decodeWord k
  simp only [decodeWord, dif_pos bounded]

theorem wordWithin_encodeWord (k : machine.K) (word : List (machine.Γ k)) :
    profile.wordWithin k (profile.encodeWord k word) = true := by
  simp only [wordWithin, encodeWord, List.all_map, List.all_eq_true, Function.comp_def, decide_eq_true_eq]
  exact fun symbol _ => (profile.symbolIndex k symbol).isLt

theorem decodeWord_encodeWord (k : machine.K) (word : List (machine.Γ k)) :
    profile.decodeWord k (profile.encodeWord k word) = some word := by
  obtain ⟨original, decoded⟩ := profile.decodeWord_exists k _ (profile.wordWithin_encodeWord k word)
  have same : original = word := profile.encodeWord_injective k (profile.encode_decodeWord k decoded)
  simpa only [same] using decoded

theorem encodeConfiguration_injective : Function.Injective profile.encodeConfiguration := by
  intro first second same
  have labels : first.l = second.l := by
    have h := congrArg Configuration.label same
    have injective : Function.Injective (fun label : machine.Λ => (profile.labelIndex label).val) :=
      fun _ _ h => profile.labelIndex.injective (Fin.ext h)
    exact Option.map_injective injective h
  have states : first.var = second.var := by
    have h := congrArg Configuration.state same
    exact profile.stateIndex.injective (Fin.ext h)
  have columns : first.stk = second.stk := by
    funext k
    apply profile.encodeWord_injective k
    have h := congrArg (fun c => c.columns.getD (profile.stackIndex k).val []) same
    simpa only [encodeConfiguration, encodeStacks_lookup] using h
  cases first
  cases second
  cases labels
  cases states
  cases columns
  rfl

def descriptor (profile : FiniteProfile machine) : Descriptor where
  stackCount := profile.stackCount
  main := (profile.labelIndex machine.main).val
  initialState := (profile.stateIndex machine.initialState).val
  inputStack := (profile.stackIndex machine.k₀).val
  outputStack := (profile.stackIndex machine.k₁).val
  program := List.ofFn (fun label : Fin profile.labels =>
    profile.lowerStatement (machine.m (profile.labelIndex.symm label)))

def originalDescriptor (profile : FiniteProfile machine) : OriginalDescriptor :=
  ⟨profile.descriptor, profile.symbols machine.k₀, profile.symbols machine.k₁⟩

theorem descriptor_step (configuration : machine.Cfg) :
    profile.descriptor.step (profile.encodeConfiguration configuration) =
      (machine.step configuration).map profile.encodeConfiguration := by
  cases configuration with
  | mk label state columns =>
      cases label with
      | none => rfl
      | some label =>
          simp only [Descriptor.step, descriptor, encodeConfiguration, Option.map_some,
            Option.bind_some, List.getElem?_ofFn, Fin.isLt, ↓reduceDIte,
            Fin.eta, Equiv.symm_apply_apply, Option.map_some]
          exact congrArg some (profile.lowerStatement_run (machine.m label) state columns)

private theorem singleton_columns (k : machine.K) (word : List (machine.Γ k)) :
    profile.encodeStacks (Function.update (fun key : machine.K => ([] : List (machine.Γ key))) k word) =
      (List.replicate profile.stackCount []).set (profile.stackIndex k).val (profile.encodeWord k word) := by
  rw [encodeStacks_update]
  simp [encodeStacks, encodeWord]

theorem descriptor_initial (input : List (machine.Γ machine.k₀)) :
    profile.descriptor.initial (profile.encodeWord machine.k₀ input) =
      profile.encodeConfiguration (initList machine input) := by
  have columns : (initList machine input).stk =
      Function.update (fun key : machine.K => ([] : List (machine.Γ key))) machine.k₀ input := by
    funext k
    by_cases same : k = machine.k₀
    · subst k; simp [initList]
    · simp [initList, same]
  simp only [Descriptor.initial, descriptor, encodeConfiguration, initList]
  rw [← singleton_columns]
  exact congrArg (fun columns => Configuration.mk _ _ (profile.encodeStacks columns)) columns.symm

theorem descriptor_terminal (output : List (machine.Γ machine.k₁)) :
    profile.descriptor.terminal (profile.encodeWord machine.k₁ output) =
      profile.encodeConfiguration (haltList machine output) := by
  have columns : (haltList machine output).stk =
      Function.update (fun key : machine.K => ([] : List (machine.Γ key))) machine.k₁ output := by
    funext k
    by_cases same : k = machine.k₁
    · subst k; simp [haltList]
    · simp [haltList, same]
  simp only [Descriptor.terminal, descriptor, encodeConfiguration, haltList]
  rw [← singleton_columns]
  exact congrArg (fun columns => Configuration.mk _ _ (profile.encodeStacks columns)) columns.symm

/-- Equality is computed from all encoded fields, with injectivity already proved. -/
def configurationEquality (profile : FiniteProfile machine) : DecidableEq machine.Cfg :=
  fun first second => decidable_of_iff
    (profile.encodeConfiguration first = profile.encodeConfiguration second)
    profile.encodeConfiguration_injective.eq_iff

theorem descriptor_replay [DecidableEq machine.Cfg] (start : machine.Cfg)
    (trace : List machine.Cfg) :
    profile.descriptor.replay (profile.encodeConfiguration start)
      (trace.map profile.encodeConfiguration) =
      (OriginalMachineTrace.replay machine start trace).map profile.encodeConfiguration := by
  induction trace generalizing start with
  | nil => rfl
  | cons next rest ih =>
      have edge_iff : profile.descriptor.step (profile.encodeConfiguration start) =
          some (profile.encodeConfiguration next) ↔ machine.step start = some next := by
        rw [descriptor_step]
        simpa only [Option.map_some] using
          (Option.map_injective profile.encodeConfiguration_injective).eq_iff
            (a := machine.step start) (b := some next)
      by_cases edge : machine.step start = some next
      · simpa only [List.map_cons, Descriptor.replay, OriginalMachineTrace.replay,
          if_pos edge, if_pos (edge_iff.mpr edge)] using ih next
      · simp only [List.map_cons, Descriptor.replay, OriginalMachineTrace.replay,
          if_neg edge, if_neg (mt edge_iff.mp edge), Option.map_none]

/-- Even an arbitrary raw trace is reflected into an actual counted original run.
No canonicality or semantic correctness of the supplied trace is assumed. -/
def replay_reflects (trace : List Configuration) (start finish : machine.Cfg)
    (accepted : profile.descriptor.replay (profile.encodeConfiguration start) trace =
      some (profile.encodeConfiguration finish)) :
    StateTransition.EvalsToInTime machine.step start (some finish) trace.length := by
  induction trace generalizing start with
  | nil =>
      have same := profile.encodeConfiguration_injective (Option.some.inj accepted)
      subst finish
      exact StateTransition.EvalsToInTime.refl machine.step start
  | cons next rest ih =>
      by_cases edge : profile.descriptor.step (profile.encodeConfiguration start) = some next
      · have remaining : profile.descriptor.replay next rest =
            some (profile.encodeConfiguration finish) := by
          simpa only [Descriptor.replay, if_pos edge] using accepted
        cases physical : machine.step start with
        | none =>
            have impossible := profile.descriptor_step start
            rw [physical, Option.map_none, edge] at impossible
            cases impossible
        | some actual =>
            have encoded := profile.descriptor_step start
            rw [physical, Option.map_some, edge] at encoded
            have same : next = profile.encodeConfiguration actual := Option.some.inj encoded
            subst next
            exact StateTransition.EvalsToInTime.trans machine.step 1 rest.length start actual
              (some finish) (StackMachineComposition.oneStep physical) (ih actual remaining)
      · simp only [Descriptor.replay, if_neg edge] at accepted
        cases accepted

def accepts_reflects (input : List (machine.Γ machine.k₀))
    (output : List (machine.Γ machine.k₁)) (trace : List Configuration)
    (accepted : profile.descriptor.accepts (profile.encodeWord machine.k₀ input)
      (profile.encodeWord machine.k₁ output) trace = true) :
    TM2OutputsInTime machine input (some output) trace.length := by
  apply profile.replay_reflects trace
  have checked := of_decide_eq_true accepted
  simpa only [descriptor_initial, descriptor_terminal] using checked

/-- Generated descriptors accept exactly the original canonical executions. -/
theorem accepts_iff_original (input : List (machine.Γ machine.k₀))
    (output : List (machine.Γ machine.k₁)) :
    (∃ trace, profile.descriptor.accepts (profile.encodeWord machine.k₀ input)
      (profile.encodeWord machine.k₁ output) trace = true) ↔
      Nonempty (TM2Outputs machine input (some output)) := by
  let : DecidableEq machine.Cfg := profile.configurationEquality
  constructor
  · rintro ⟨trace, accepted⟩
    exact ⟨(profile.accepts_reflects input output trace accepted).toEvalsTo⟩
  · intro execution
    obtain ⟨trace, accepted⟩ :=
      (OriginalMachineTrace.accepts_iff_original_execution machine input output).mpr execution
    refine ⟨trace.map profile.encodeConfiguration, ?_⟩
    apply decide_eq_true
    simp only [descriptor_initial, descriptor_terminal, descriptor_replay]
    exact congrArg (Option.map profile.encodeConfiguration) (of_decide_eq_true accepted)

theorem acceptsPacket_iff_original (input : List (machine.Γ machine.k₀))
    (output : List (machine.Γ machine.k₁)) :
    (∃ packet, profile.descriptor.acceptsPacket
      (encodeList (profile.encodeWord machine.k₀ input))
      (encodeList (profile.encodeWord machine.k₁ output)) packet = true) ↔
      Nonempty (TM2Outputs machine input (some output)) := by
  rw [← profile.accepts_iff_original input output]
  constructor
  · rintro ⟨packet, accepted⟩
    exact ⟨(decodeList packet).map Configuration.decode,
      by simpa only [Descriptor.acceptsPacket, decodeList_encodeList] using accepted⟩
  · rintro ⟨trace, accepted⟩
    refine ⟨encodeList (trace.map Configuration.encode), ?_⟩
    simpa [Descriptor.acceptsPacket, decodeList_encodeList, List.map_map,
      Function.comp_def, Configuration.decode_encode] using accepted

end FiniteProfile

end Mettapedia.Computability.OriginalMachineTraceEncoding
