import Mettapedia.Machines.ProducerReadReuse

/-!
# First-revision capture for recursive producers

The logical capture operation retains one revision per producer. A conflicting
read refuses reuse rather than overwriting the earlier observation. Its accepted
certificate validates exactly the complete read trace. The association list is
an independent specification of the native hashed representation; hash probes,
allocation and native correspondence are controlled separately.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ProducerReadCapture

open ReadOnlyQuery

universe u
variable {Key : Type u} [DecidableEq Key]

def lookup (key : Key) : Reads Key Nat → Option Nat
  | [] => none
  | read :: rest => if read.1 = key then some read.2 else lookup key rest

theorem lookup_agrees (store : Key → Nat) (key : Key) (reads : Reads Key Nat)
    (valid : Agrees store reads) (value : Nat) (found : lookup key reads = some value) :
    store key = value := by
  induction reads with
  | nil => simp [lookup] at found
  | cons read rest ih =>
      have here := valid read (by simp)
      have tail : Agrees store rest := fun item member => valid item (by simp [member])
      by_cases same : read.1 = key
      · have equal : read.2 = value := by simpa [lookup, same] using found
        simpa only [same, equal] using here
      · exact ih tail (by simpa [lookup, same] using found)

def remember (reads : Reads Key Nat) (read : Key × Nat) : Option (Reads Key Nat) :=
  match lookup read.1 reads with
  | none => some (read :: reads)
  | some old => if old = read.2 then some reads else none

def checked (store : Key → Nat) : Option (Reads Key Nat) → Bool
  | none => false
  | some reads => checkReads store reads

/-- Refusal or deduplication accounts for the new read as well as all old ones. -/
theorem remember_check_exact (store : Key → Nat) (reads : Reads Key Nat)
    (read : Key × Nat) :
    checked store (remember reads read) =
      (checkReads store reads && decide (store read.1 = read.2)) := by
  cases found : lookup read.1 reads with
  | none => simp [remember, found, checked, checkReads, Bool.and_comm]
  | some old =>
      by_cases equal : old = read.2
      · by_cases accepted : checkReads store reads = true
        · have current := lookup_agrees store read.1 reads
            ((checkReads_iff _ _).mp accepted) old found
          simp [remember, found, equal, checked, accepted, current]
        · have rejected : checkReads store reads = false := by
            cases h : checkReads store reads <;> simp_all
          simp [remember, found, equal, checked, rejected]
      · by_cases accepted : checkReads store reads = true
        · have current := lookup_agrees store read.1 reads
            ((checkReads_iff _ _).mp accepted) old found
          simp [remember, found, equal, checked, accepted, current]
        · have rejected : checkReads store reads = false := by
            cases h : checkReads store reads <;> simp_all
          simp [remember, found, equal, checked, rejected]

def captureFrom (seen : Reads Key Nat) : Reads Key Nat → Option (Reads Key Nat)
  | [] => some seen
  | read :: rest => (remember seen read).bind fun next => captureFrom next rest

/-- Validation of the captured map is equivalent to every original read. -/
theorem capture_check_exact (store : Key → Nat)
    (seen trace : Reads Key Nat) :
    checked store (captureFrom seen trace) =
      (checkReads store seen && checkReads store trace) := by
  induction trace generalizing seen with
  | nil => simp [captureFrom, checked, checkReads]
  | cons read rest ih =>
      have recorded := remember_check_exact store seen read
      cases captured : remember seen read with
      | none =>
          simp only [captured, checked] at recorded
          simp only [captureFrom, captured, Option.bind_none, checked]
          calc
            false = ((checkReads store seen && decide (store read.1 = read.2)) &&
                checkReads store rest) := by rw [← recorded]; rfl
            _ = (checkReads store seen && checkReads store (read :: rest)) := by
              simp [checkReads, Bool.and_assoc]
      | some next =>
          simp only [captured, checked] at recorded
          simp only [captureFrom, captured, Option.bind_some, ih]
          rw [recorded]
          simp [checkReads, Bool.and_assoc]

theorem empty_capture_checks_the_trace (store : Key → Nat) (trace : Reads Key Nat) :
    checked store (captureFrom [] trace) = checkReads store trace := by
  rw [capture_check_exact]
  simp [checkReads]

/-- A captured first-revision certificate licenses the independently executed
interleaved-query comparison, under the actual append-only list law. -/
theorem captured_versions_replay_exact {Item Answer : Type*}
    (stores : Nat → Key → List Item) (final : Key → List Item) (start : Nat)
    (program : Program Key (List Item) Answer)
    (extension : ProducerReadReuse.ExtendsReads final
      (ProducerReadReuse.runChanging stores start program).reads)
    (valid : checked (fun key => (final key).length)
      (captureFrom [] (ProducerReadReuse.versions
        (ProducerReadReuse.runChanging stores start program).reads)) = true) :
    run final program = ProducerReadReuse.runChanging stores start program := by
  apply ProducerReadReuse.version_replay_exact stores final start program extension
  simpa only [empty_capture_checks_the_trace] using valid

/-! ## Controls -/

theorem first_revision_retained :
    captureFrom ([] : Reads Nat Nat) [(3, 0), (3, 0), (7, 2)] =
      some [(7, 2), (3, 0)] := by decide

theorem changed_first_revision_refused :
    captureFrom ([] : Reads Nat Nat) [(3, 0), (7, 2), (3, 1)] = none := by decide

theorem conflicting_round_never_becomes_valid (store : Nat → Nat) :
    checked store (captureFrom [] [(3, 0), (3, 1)]) = false := by
  rfl

#print axioms lookup_agrees
#print axioms remember_check_exact
#print axioms capture_check_exact
#print axioms captured_versions_replay_exact

end Mettapedia.Machines.ProducerReadCapture
