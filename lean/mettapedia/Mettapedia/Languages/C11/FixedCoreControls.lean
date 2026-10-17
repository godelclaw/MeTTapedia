import Mettapedia.Languages.C11.FixedCoreStatements
import Mettapedia.Languages.C11.IntegerMemoryControls

/-!
# Fixed C core controls

Complete programs run on the core machine under the LP64 little-endian integer
model with natural alignment. Recursion computes a factorial through nested
activations and parameter objects; a pointer that escapes its block, a use after
release, a second release, signed overflow, a missing return value used by the
caller, pointer arithmetic past an array and a stray `break` each stop with their
own reason; an external request suspends with the complete configuration and a
single reply resumes it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.C11.FixedCoreControls

open FixedCore IntegerMemoryModel
open Mettapedia.GSLT.Distinction.ProductiveBlocks (Outcome)

abbrev model : Model := IntegerMemoryControls.model

/-- Natural alignment for the LP64 object sizes. -/
def abi (type : IntegerType IntegerExtension) : ObjectLayout.Layout :=
  match (model.objects type).byteCount with
  | 2 => ⟨1, 2, by decide, by decide⟩
  | 4 => ⟨2, 4, by decide, by decide⟩
  | 8 => ⟨3, 8, by decide, by decide⟩
  | _ => ⟨0, 1, by decide, by decide⟩

def policy : SignedConversionPolicy := intervalReductionPolicy

def int (value : Int) (fits : IntegerFormat.Represents (IntegerType.int.format model.parameters) value) :
    IntegerScalar.Value model.parameters := ⟨.int, ⟨value, fits⟩⟩

def zero := int 0 (by decide)
def one := int 1 (by decide)
def two := int 2 (by decide)
def five := int 5 (by decide)
def six := int 6 (by decide)
def seven := int 7 (by decide)
def three := int 3 (by decide)
def intMax := int 2147483647 (by decide)

def scalar (name : String) : IntegerObjectConstruction.Declaration := ⟨name, .int, .scalar⟩
def array (name : String) (count : Nat) (positive : 0 < count) : IntegerObjectConstruction.Declaration :=
  ⟨name, .int, .array count positive⟩

def readNamed (name : String) : Expression model := .read (.named name)

/-- The integer a finished run returns, if any. -/
def returned : List (Event model) × Outcome (Executable model) (Option (Value model)) (Request model) → Option Int
  | (_, .finished (some (.integer value))) => some value.integer.value
  | _ => none

/-- The fault a run stops with, if any. -/
def faulted : List (Event model) × Outcome (Executable model) (Option (Value model)) (Request model) →
    Option (Fault model)
  | (events, .faulted) =>
      match events.getLast? with
      | some (.fault reason) => some reason
      | _ => none
  | _ => none

def runProgram (program : Program model) (fuel : Nat) :
    Option (List (Event model) × Outcome (Executable model) (Option (Value model)) (Request model)) :=
  (start model program "main" ⟨[], []⟩ []).map ((machine model policy abi program).run fuel)

/-! ## Recursion through activations -/

/-- `int fact(int n) { int r; if (n) { r = fact(n - 1); r = n * r; } else r = 1; return r; }` -/
def factorial : Function model where
  parameters := [.integer "n" .int]
  body := .block [.object (scalar "r") none]
    (.sequence
      (.conditional (readNamed "n")
        (.sequence (.call (some "r") "fact" [.binary .subtract (readNamed "n") (.constant one)])
          (.assign (.named "r") (.binary .multiply (readNamed "n") (readNamed "r"))))
        (.assign (.named "r") (.constant one)))
      (.returnValue (some (readNamed "r"))))

def factorialMain : Function model where
  parameters := []
  body := .block [.object (scalar "x") none]
    (.sequence (.call (some "x") "fact" [.constant five]) (.returnValue (some (readNamed "x"))))

def factorialProgram : Program model := [("main", factorialMain), ("fact", factorial)]

theorem recursive_factorial_returns_120 :
    (runProgram factorialProgram 400).bind returned = some 120 := by decide +kernel

/-! ## Lifetimes and pointers -/

/-- `int *p; { int x = 7; p = &x; } return *p;` -/
def danglingMain : Function model where
  parameters := []
  body := .block [.pointer "p" none]
    (.sequence
      (.block [.object (scalar "x") (some (.constant seven))] (.setPointer "p" (.addressOf (.named "x"))))
      (.returnValue (some (.read (.deref (.variable "p"))))))

theorem escaped_pointer_read_is_undefined :
    ((runProgram [("main", danglingMain)] 60).bind faulted).map (fun
      | .access _ => true
      | _ => false) = some true := by decide +kernel

/-- The same read while `x` is alive returns 7. -/
def liveMain : Function model where
  parameters := []
  body := .block [.pointer "p" none]
    (.block [.object (scalar "x") (some (.constant seven))]
      (.sequence (.setPointer "p" (.addressOf (.named "x"))) (.returnValue (some (.read (.deref (.variable "p")))))))

theorem live_pointer_read_returns_seven :
    (runProgram [("main", liveMain)] 60).bind returned = some 7 := by decide +kernel

/-- `int a[2]; int *p = a + 3;` forms a pointer outside the array. -/
def outsideMain : Function model where
  parameters := []
  body := .block [.object (array "a" 2 (by decide)) none, .pointer "p" none]
    (.setPointer "p" (.offset (.addressOf (.element "a" (.constant zero))) (.constant three)))

theorem pointer_past_array_is_undefined :
    (runProgram [("main", outsideMain)] 40).bind faulted = some .pointer := by decide +kernel

/-! ## Dynamic objects -/

/-- `p = malloc(2); *p = 5; *(p + 1) = 6; s = *p + *(p + 1); free(p); return s;` -/
def heapMain (afterFree : Statement model) : Function model where
  parameters := []
  body := .block [.pointer "p" none, .object (scalar "s") none]
    (.sequence (.allocate "p" .int (.constant two))
      (.sequence (.assign (.deref (.variable "p")) (.constant five))
        (.sequence (.assign (.deref (.offset (.variable "p") (.constant one))) (.constant six))
          (.sequence (.assign (.named "s") (.binary .add (.read (.deref (.variable "p")))
              (.read (.deref (.offset (.variable "p") (.constant one))))))
            (.sequence (.release (.variable "p")) afterFree)))))

theorem allocated_object_sum_returns_eleven :
    (runProgram [("main", heapMain (.returnValue (some (readNamed "s"))))] 120).bind returned = some 11 := by
  decide +kernel

theorem use_after_release_is_undefined :
    ((runProgram [("main", heapMain (.returnValue (some (.read (.deref (.variable "p"))))))] 120).bind
      faulted).map (fun
        | .access _ => true
        | _ => false) = some true := by decide +kernel

theorem second_release_is_undefined :
    (runProgram [("main", heapMain (.release (.variable "p")))] 120).bind faulted = some .invalidRelease := by
  decide +kernel

/-! ## Undefined and ill-formed behaviors keep their reasons -/

/-- `int x = INT_MAX; x = x + 1;` -/
def overflowMain : Function model where
  parameters := []
  body := .block [.object (scalar "x") (some (.constant intMax))]
    (.assign (.named "x") (.binary .add (readNamed "x") (.constant one)))

theorem signed_overflow_is_undefined :
    ((runProgram [("main", overflowMain)] 40).bind faulted).map (fun
      | .arithmetic _ .overflow => true
      | _ => false) = some true := by decide +kernel

/-- `int f() { }` used as `x = f();` -/
def silent : Function model := ⟨[], .skip⟩

def missingReturnMain : Function model where
  parameters := []
  body := .block [.object (scalar "x") none]
    (.sequence (.call (some "x") "f" []) (.returnValue (some (readNamed "x"))))

theorem used_missing_return_is_undefined :
    (runProgram [("main", missingReturnMain), ("f", silent)] 60).bind faulted = some .missingReturn := by
  decide +kernel

/-- Discarding the value of the same call is defined. -/
def discardedMain : Function model where
  parameters := []
  body := .sequence (.call none "f" []) (.returnValue (some (.constant seven)))

theorem discarded_missing_return_is_defined :
    (runProgram [("main", discardedMain), ("f", silent)] 60).bind returned = some 7 := by decide +kernel

theorem stray_break_violates_a_constraint :
    (runProgram [("main", ⟨[], .breakLoop⟩)] 20).bind faulted = some .constraint := by decide +kernel

/-! ## External interaction -/

/-- `x = read(); return x + 1;` -/
def echoMain : Function model where
  parameters := []
  body := .block [.object (scalar "x") none]
    (.sequence (.external (some "x") "read" [])
      (.returnValue (some (.binary .add (readNamed "x") (.constant one)))))

def suspended : Option (Executable model) :=
  (runProgram [("main", echoMain)] 40).bind fun
    | (_, .suspended _ saved) => some saved
    | _ => none

theorem external_call_suspends_with_its_request :
    (runProgram [("main", echoMain)] 40).map (fun
      | (_, .suspended request _) => request.service == "read" && request.arguments.isEmpty
      | _ => false) = some true := by
  decide +kernel

theorem reply_resumes_once :
    let resumed := suspended.bind (reply model policy (.integer six))
    (resumed.map ((machine model policy abi [("main", echoMain)]).run 40)).bind returned = some 7 ∧
      (resumed.bind (reply model policy (.integer six))).isNone = true := by
  decide +kernel

end Mettapedia.Languages.C11.FixedCoreControls
