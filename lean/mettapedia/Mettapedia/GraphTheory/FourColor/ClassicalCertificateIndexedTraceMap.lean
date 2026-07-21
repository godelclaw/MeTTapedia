import Mettapedia.GraphTheory.FourColor.ClassicalCertificateTraceTree

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateIndexedTraceMap

open ClassicalCertificateTraceTree

/-- A finite ternary trace map.  Leaves carry externally generated natural
values, while malformed or missing paths have no value. -/
inductive Tree where
  | empty
  | leaf (value : Nat)
  | node (red blue purple : Tree)
  deriving DecidableEq, Repr

namespace Tree

def child : Tree → TraceSymbol → Tree
  | .node red _ _, .red => red
  | .node _ blue _, .blue => blue
  | .node _ _ purple, .purple => purple
  | _, _ => .empty

/-- Direct lookup follows exactly one constructor per trace symbol. -/
def lookup : Tree → List TraceSymbol → Option Nat
  | .leaf value, [] => some value
  | .node red _ _, .red :: word => lookup red word
  | .node _ blue _, .blue :: word => lookup blue word
  | .node _ _ purple, .purple :: word => lookup purple word
  | _, _ => none

/-- Validate each stored leaf against a Boolean relation between its value
and its complete root-to-leaf trace. -/
def checkAt (accepts : Nat → List TraceSymbol → Bool) :
    Nat → Tree → List TraceSymbol → Bool
  | _, .empty, _ => true
  | 0, .leaf value, stem => accepts value stem
  | length + 1, .node red blue purple, stem =>
      checkAt accepts length red (stem ++ [.red]) &&
        checkAt accepts length blue (stem ++ [.blue]) &&
        checkAt accepts length purple (stem ++ [.purple])
  | _, _, _ => false

def checker (length : Nat) (tree : Tree)
    (accepts : Nat → List TraceSymbol → Bool) : Bool :=
  checkAt accepts length tree []

/-- A checked trace map returns only values satisfying its validation
relation. -/
theorem lookup_sound_of_checkAt_true
    (accepts : Nat → List TraceSymbol → Bool)
    (length : Nat) (tree : Tree) (stem word : List TraceSymbol)
    (value : Nat)
    (hcheck : checkAt accepts length tree stem = true)
    (hlength : word.length = length)
    (hlookup : tree.lookup word = some value) :
    accepts value (stem ++ word) = true := by
  induction word generalizing length tree stem with
  | nil =>
      have hzero : length = 0 := by simpa using hlength.symm
      subst length
      cases tree with
      | empty => simp [lookup] at hlookup
      | node red blue purple => simp [lookup] at hlookup
      | leaf stored =>
          have hstored : stored = value := by
            simpa [lookup] using hlookup
          subst stored
          simpa [checkAt] using hcheck
  | cons symbol word ih =>
      cases length with
      | zero => simp at hlength
      | succ length =>
          have htail : word.length = length := by
            simpa using Nat.succ.inj hlength
          cases tree with
          | empty => simp [lookup] at hlookup
          | leaf stored => simp [lookup] at hlookup
          | node red blue purple =>
              simp only [checkAt, Bool.and_eq_true] at hcheck
              cases symbol with
              | red =>
                  have hlookup' : red.lookup word = some value := by
                    simpa [lookup] using hlookup
                  have hsound := ih length red (stem ++ [.red])
                    hcheck.1.1 htail hlookup'
                  simpa [List.append_assoc] using hsound
              | blue =>
                  have hlookup' : blue.lookup word = some value := by
                    simpa [lookup] using hlookup
                  have hsound := ih length blue (stem ++ [.blue])
                    hcheck.1.2 htail hlookup'
                  simpa [List.append_assoc] using hsound
              | purple =>
                  have hlookup' : purple.lookup word = some value := by
                    simpa [lookup] using hlookup
                  have hsound := ih length purple (stem ++ [.purple])
                    hcheck.2 htail hlookup'
                  simpa [List.append_assoc] using hsound

theorem lookup_sound_of_checker_true
    (length : Nat) (tree : Tree)
    (accepts : Nat → List TraceSymbol → Bool)
    (hchecker : tree.checker length accepts = true)
    (word : List TraceSymbol) (value : Nat)
    (hlength : word.length = length)
    (hlookup : tree.lookup word = some value) :
    accepts value word = true := by
  simpa [checker] using
    lookup_sound_of_checkAt_true accepts length tree [] word value
      hchecker hlength hlookup

end Tree

end ClassicalCertificateIndexedTraceMap

end Mettapedia.GraphTheory.FourColor
