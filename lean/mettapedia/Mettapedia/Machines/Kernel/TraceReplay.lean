import Mettapedia.Machines.Kernel.SexOSGenesis

/-!
# Executable observations of the capability-kernel model

This executable calls `SingleAddressSpace.step` directly on the generated SexOS genesis. The host
comparison in the SexOS port supplies the same requests to the actual C syscall and ring code.
It compares results and a state projection after every request. This is differential evidence, not
a refinement proof of C, page tables, machine instructions, the scheduler or the C compiler.

The projection includes all ordinary ring/frame capabilities, FIFO contents, pending reply counts,
reply slots, frame ownership, mappings and access to each declared domain's key. Shared key 14,
device/input capabilities, allocation failures and hardware memory accesses are outside this test.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.TraceReplay

open SexOSGenesis

def domains : List Dom :=
  [.sexdisplay, .sexdrive, .silk_shell, .sexinput, .sexusb, .silkbar, .linen,
   .sexstore, .quil, .sexbell, .sexfiles, .spindle, .sexnet, .kaleidoscope]

def initial : State Dom := genesis config caps

def finalState (s : State Dom) : List (Dom × Op Dom) → State Dom
  | [] => s
  | (d, op) :: rest => finalState (step config s d op).1 rest

theorem finalState_reachable {start s : State Dom} (h : Reachable config start s)
    (events : List (Dom × Op Dom)) : Reachable config start (finalState s events) := by
  induction events generalizing s with
  | nil => exact h
  | cons event rest ih => exact ih (Reachable.next event.1 event.2 h)

theorem finalState_good (events : List (Dom × Op Dom)) : Good config (finalState initial events) :=
  (finalState_reachable Reachable.init events).good (genesis_good config caps caps_no_frames)

private def cat (parts : List String) : String := String.join parts

private def capText (s : State Dom) (d : Dom) (slot : Nat) : String :=
  match s.caps d slot with
  | some ⟨.ring target, _⟩ => s!"c{slot}:r{key target},"
  | some ⟨.frame frame, _⟩ => s!"c{slot}:f{frame},"
  | none => ""

private def domainText (s : State Dom) (d : Dom) : String :=
  let cs := cat ((List.range 31).map fun n => capText s d (n + 1))
  let q := cat ((s.ring d).map fun (sender, word) => s!"{key sender}:{word},")
  let p := cat (domains.map fun sender =>
    let count := (s.pending d).count sender
    if count = 0 then "" else s!"{key sender}:{count},")
  let answer := match s.slot d with | some word => toString word | none => "-"
  let access := cat (domains.map fun other => if s.mask d (key other) then "1" else "0")
  s!"|D{key d}{cs}q{q}p{p}s{answer}x{access}"

def snapshot (s : State Dom) : String :=
  let ds := cat (domains.map (domainText s))
  let owners := cat ((List.range s.fresh).map fun frame =>
    match s.owner frame with
    | some d => s!"{frame}:{key d},"
    | none => s!"{frame}:?,")
  let maps := cat (s.maps.reverse.map fun (frame, k) => s!"{frame}:{k},")
  s!"|F{s.fresh}{ds}|O{owners}|M{maps}"

def resultText : Result Dom → String
  | .done word => s!"D{word}"
  | .message sender word => s!"H{key sender}:{word}"
  | .answer word => s!"A{word}"
  | .empty => "E"
  | .refused => "R"

private def findDomain (n : Nat) : Except String Dom :=
  match domains.find? fun d => key d == n with
  | some d => .ok d
  | none => .error s!"unknown domain key: {n}"

def parse (line : String) : Except String (Dom × Op Dom) := do
  let words := (line.trimAscii.toString.splitOn " ").filter (· != "")
  let numbers ← words.mapM fun word => match word.toNat? with
    | some n => Except.ok n
    | none => Except.error s!"expected a natural: {word}"
  match numbers with
  | [d, op, a, b] =>
    let domain ← findDomain d
    let request : Op Dom ← match op with
      | 0 => pure (.send a b)
      | 1 => pure .listen
      | 2 => do
        let target ← findDomain a
        pure (.reply target b)
      | 3 => pure .alloc
      | 4 => pure (.map a)
      | 5 => pure (.lend a b)
      | 6 => pure (.mapLent a)
      | _ => throw s!"unknown operation: {op}"
    return (domain, request)
  | _ => throw "expected: domain-key operation argument argument"

end Mettapedia.Machines.Kernel.TraceReplay
