import Mathlib.Data.List.Basic

/-!
# Text on a terminal: what a sanitizer must remove

A terminal reads its input as characters to show and control functions to run
(ECMA-48). In its ground state it prints a graphic character, and executes a C0
control such as a carriage return or a bell. An escape (ESC), or a C1 control,
starts a control sequence or a control string: a CSI sequence until its final
byte (cursor moves, clearing the screen), an OSC string until BEL or ST (the
window title, the clipboard). The characters inside are consumed, not shown.

The model is the core of the DEC/ANSI parser state machine: the ground,
escape, CSI and OSC states, with C1 controls as single characters (U+0080 to
U+009F; UTF-8 writes them as two bytes).

The theorems:
- `run_osc_hides`: an escape sequence runs a control function and swallows the
  text that follows it: the title is set, and the text after it is not shown.
- `run_c1_clears`: a lone C1 CSI clears the screen, with no ESC in sight; a
  sanitizer that removes only ESC misses it.
- `run_controlFree`: text without control characters (tab and line feed aside)
  leaves the terminal in its ground state and shows exactly that text.
- `printable_shows`: the sanitizer that removes C0 (but tab and line feed), DEL
  and C1 makes any text safe in that sense, and keeps every other character.

A terminal reads bytes. The model's terminal acts on characters, as one does that
decodes UTF-8 first and then acts on U+0080 to U+009F as C1; one that ignores C1
characters is only safer, and one in 8-bit mode, which acts on raw bytes `80` to
`9F`, finds them inside ordinary UTF-8 text and is outside this account. Arbitrary
earlier terminal state, and text that deceives by look (bidirectional overrides,
look-alike characters), are outside it too.
- `oldFilter_clears`: the filter as first shipped, `tr` and one `sed` pass over
  bytes, turns `C2 C2 9B 9B 2 J`, which is not UTF-8, into the UTF-8 of the C1
  erase-display sequence: removing a C1 control can make one.
- `printableBytes_shows`: decoding first (what is not UTF-8 becomes some
  character), filtering, and writing UTF-8 gives bytes that any decoder correct
  on UTF-8 reads as the filtered text, which the terminal shows exactly.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Injection.Terminal

/-- ESC. -/
def esc : Char := Char.ofNat 0x1b
/-- BEL, which ends an OSC string. -/
def bel : Char := Char.ofNat 0x07
/-- The C1 control sequence introducer, CSI. -/
def csi1 : Char := Char.ofNat 0x9b
/-- The C1 operating system command, OSC. -/
def osc1 : Char := Char.ofNat 0x9d
/-- The C1 string terminator, ST. -/
def st1 : Char := Char.ofNat 0x9c

/-- A control character a terminal acts on: C0 but tab and line feed, DEL, or C1. -/
def isControl (c : Char) : Bool :=
  (c.toNat < 0x20 && c != '\t' && c != '\n') || c.toNat == 0x7f ||
    (0x80 ≤ c.toNat && c.toNat ≤ 0x9f)

/-- The parser's states. -/
inductive State where
  | ground
  | escape
  | csi
  | osc
  deriving DecidableEq, Repr

/-- What the terminal does with an input character. -/
inductive Effect where
  /-- Show a character (tab and line feed are shown as layout). -/
  | show (c : Char)
  /-- Run a C0 or C1 control on its own: a bell, a carriage return. -/
  | execute (c : Char)
  /-- Run a control function: an escape sequence, a CSI sequence, an OSC string. -/
  | dispatch (s : State)
  deriving DecidableEq, Repr

/-- One step of the parser. -/
def step : State → Char → State × List Effect
  | .ground, c =>
    if c = esc then (.escape, [])
    else if c = csi1 then (.csi, [])
    else if c = osc1 then (.osc, [])
    else if isControl c then (.ground, [.execute c])
    else (.ground, [.show c])
  | .escape, c =>
    if c = '[' then (.csi, [])
    else if c = ']' then (.osc, [])
    else (.ground, [.dispatch .escape])
  | .csi, c =>
    if 0x40 ≤ c.toNat ∧ c.toNat ≤ 0x7e then (.ground, [.dispatch .csi]) else (.csi, [])
  | .osc, c =>
    if c = bel ∨ c = st1 then (.ground, [.dispatch .osc])
    else if c = esc then (.escape, [.dispatch .osc])
    else (.osc, [])

/-- The terminal on a whole input, from a state: the final state and the effects. -/
def run : State → List Char → State × List Effect
  | s, [] => (s, [])
  | s, c :: cs =>
    let (s', e) := step s c
    let (s'', es) := run s' cs
    (s'', e ++ es)

/-! ## What escapes do -/

/-- `ESC ] 0 ; x BEL h i`: the OSC string runs (the title becomes `x`), and only
what follows its terminator is shown. -/
theorem run_osc_hides :
    run .ground [esc, ']', '0', ';', 'x', bel, 'h', 'i'] =
      (.ground, [.dispatch .osc, .show 'h', .show 'i']) := by
  decide

/-- `ESC ] 0 ; h i`, unterminated: nothing after the escape is ever shown. -/
theorem run_osc_swallows :
    run .ground [esc, ']', '0', ';', 'h', 'i'] = (.osc, []) := by
  decide

/-- A lone C1 CSI and `2 J`, the erase-display sequence: the screen is cleared,
with no ESC in the input. -/
theorem run_c1_clears : run .ground [csi1, '2', 'J'] = (.ground, [.dispatch .csi]) := by
  decide

/-! ## Text without controls is shown as it is -/

theorem step_ground_text {c : Char} (h : isControl c = false) (hesc : c ≠ esc)
    (hcsi : c ≠ csi1) (hosc : c ≠ osc1) : step .ground c = (.ground, [.show c]) := by
  simp [step, hesc, hcsi, hosc, h]

theorem esc_isControl : isControl esc = true := by decide
theorem csi1_isControl : isControl csi1 = true := by decide
theorem osc1_isControl : isControl osc1 = true := by decide

/-- **Text without controls is shown as it is.** The terminal stays in its ground
state, runs no control function, and shows every character in order. -/
theorem run_controlFree (cs : List Char) (h : ∀ c ∈ cs, isControl c = false) :
    run .ground cs = (.ground, cs.map .show) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc : isControl c = false := h c (by simp)
    have hesc : c ≠ esc := fun he => by rw [he, esc_isControl] at hc; exact absurd hc (by decide)
    have hcsi : c ≠ csi1 := fun he => by rw [he, csi1_isControl] at hc; exact absurd hc (by decide)
    have hosc : c ≠ osc1 := fun he => by rw [he, osc1_isControl] at hc; exact absurd hc (by decide)
    have ih' := ih (fun x hx => h x (by simp [hx]))
    simp [run, step_ground_text hc hesc hcsi hosc, ih']

/-! ## The sanitizer -/

/-- Remove every control character, keeping tab, line feed and everything else. -/
def printable (cs : List Char) : List Char := cs.filter (fun c => !isControl c)

theorem printable_controlFree (cs : List Char) : ∀ c ∈ printable cs, isControl c = false := by
  intro c hc
  simpa [printable] using (List.mem_filter.mp hc).2

/-- **The sanitizer makes text safe to show.** Whatever the input, the sanitized
text leaves the terminal in its ground state and is shown exactly. -/
theorem printable_shows (cs : List Char) :
    run .ground (printable cs) = (.ground, (printable cs).map .show) :=
  run_controlFree _ (printable_controlFree cs)

/-- It keeps every character that is not a control, in order. -/
theorem printable_keeps (cs : List Char) :
    printable cs = cs.filter (fun c => !isControl c) := rfl

theorem printable_of_controlFree (cs : List Char) (h : ∀ c ∈ cs, isControl c = false) :
    printable cs = cs := by
  unfold printable
  rw [List.filter_eq_self]
  intro c hc
  simp [h c hc]

/-- Tab and line feed are kept: layout is not a control here. -/
theorem printable_keeps_layout : printable ['a', '\t', 'b', '\n'] = ['a', '\t', 'b', '\n'] := by
  decide

/-- The sanitized hostile inputs: the escapes are gone and their text is shown. -/
theorem printable_osc :
    printable [esc, ']', '0', ';', 'x', bel, 'h', 'i'] = [']', '0', ';', 'x', 'h', 'i'] := by
  decide

/-! ## Bytes -/

/-- `tr -d '\000-\010\013-\037\177'`: C0 bytes but tab and line feed, and DEL. -/
def trBytes (b : List UInt8) : List UInt8 :=
  b.filter fun x => !((x < 0x20 && x != 0x09 && x != 0x0a) || x == 0x7f)

/-- One pass of `sed 's/\xc2[\x80-\x9f]//g'`, left to right: each match is removed
and the text after it scanned on, never what the removal brings together. The flag
says a `C2` is held, waiting for the next byte. -/
def sedC1 : Bool → List UInt8 → List UInt8
  | false, [] => []
  | false, x :: rest => if x = 0xC2 then sedC1 true rest else x :: sedC1 false rest
  | true, [] => [0xC2]
  | true, y :: rest =>
    if 0x80 ≤ y ∧ y ≤ 0x9F then sedC1 false rest
    else if y = 0xC2 then 0xC2 :: sedC1 true rest
    else 0xC2 :: y :: sedC1 false rest

/-- The filter as first shipped, on bytes. -/
def oldFilter (b : List UInt8) : List UInt8 := sedC1 false (trBytes b)

/-- **Removing a C1 control can make one.** `C2 C2 9B 9B 2 J` is not UTF-8; the
old filter removes the `C2 9B` inside it, and what is left is the UTF-8 of CSI,
`2`, `J`: the erase-display sequence (`run_c1_clears`). -/
theorem oldFilter_clears :
    ByteArray.mk (oldFilter [0xC2, 0xC2, 0x9B, 0x9B, 0x32, 0x4A]).toArray =
      [csi1, '2', 'J'].utf8Encode := by
  decide

/-- The filter now: the bytes are decoded (`decode` turns what is not UTF-8 into
some character, as jq turns it into U+FFFD), filtered, and written as UTF-8. -/
noncomputable def printableBytes (decode : ByteArray → List Char) (b : ByteArray) : ByteArray :=
  (printable (decode b)).utf8Encode

/-- What it writes is UTF-8. -/
theorem printableBytes_valid (decode : ByteArray → List Char) (b : ByteArray) :
    (printableBytes decode b).IsValidUTF8 :=
  ByteArray.isValidUTF8_utf8Encode

/-- **The filter's bytes are shown as text.** Whatever the input bytes, a terminal
whose decoder reads every UTF-8 encoding back as its characters, whatever it does
with other input, stays in its ground state and shows exactly the filtered text. -/
theorem printableBytes_shows (decode : ByteArray → List Char) (b : ByteArray)
    (read : ByteArray → List Char) (hread : ∀ l : List Char, read l.utf8Encode = l) :
    run .ground (read (printableBytes decode b)) =
      (.ground, (printable (decode b)).map .show) := by
  rw [printableBytes, hread]
  exact printable_shows _

/-- A strict decoder, Lean's own, is such a decoder. -/
def strictRead (b : ByteArray) : List Char := (b.utf8Decode?.map Array.toList).getD []

theorem strictRead_utf8Encode (l : List Char) : strictRead l.utf8Encode = l := by
  simp [strictRead, List.utf8Decode?_utf8Encode]

end Mettapedia.Protocols.Injection.Terminal
