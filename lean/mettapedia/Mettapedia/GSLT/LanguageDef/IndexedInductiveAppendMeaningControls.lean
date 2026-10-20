import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendSourceMeaning

/-!
# Source append computation and representation controls

The closed function is obtained from the textual producer. Finite execution
uses the existing recipe producer and independent replay; a depleted budget
may return an intermediate term. The generic forward theorem is tested
separately from those conversion receipts and from dependent type checking.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.AppendMeaningControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies Declaration.IndexedFamily
open IndexedInductiveNatVec VectorMeaning AppendMeaning

def element : Tower.Tm 0 := .const `Bool
def payload (value : Bool) : Tower.Tm 0 := if value then .const `True else .const `False

def packet (parameter : Tower.Tm 0) : List Bool → Tower.Tm 0
  | [] => vnilApp parameter
  | head :: tail => vconsApp parameter (numeral tail.length) (payload head) (packet parameter tail)

def application (term : Tower.Tm 0) (left right : List Bool) : Tower.Tm 0 :=
  applyArgs term [element, numeral left.length, numeral right.length, packet element left, packet element right]

def program := application Programs.appendTerm [true] [false]
def expected := packet element [true, false]

/-- A nonempty source instance of the general forward theorem. Its target
retains the source operation; finite recipe controls independently inspect
the concrete constructor packet below. -/
theorem append_nonempty_source : ProgramExecutes
    (applyArgs Programs.appendTerm [element, quoteIndex (Natural.succ Natural.zero),
      quoteIndex (Natural.succ Natural.zero),
      encodeVector element payload (Vectors.cons true Vectors.nil),
      encodeVector element payload (Vectors.cons false Vectors.nil)])
    (encodeVector element payload
      (Vectors.append (Vectors.cons true Vectors.nil) (Vectors.cons false Vectors.nil))) :=
  appendTerm_program element payload _ _

local instance : DecidableRel Programs.rules.headEq :=
  fun first second => inferInstanceAs (Decidable (Tower.rules.headEq first second))

/-- A checked conversion result, possibly intermediate when fuel runs out. -/
def run (fuel : Nat) (left right : List Bool) : Option (Tower.Tm 0) := do
  let term ← AppendSource.proposedAppend
  let candidate ← StructuralConversionSearch.normalize Programs.decoder Programs.searchRoot
    (headEq := Programs.rules.headEq) fuel (application term left right)
  return candidate.term

def verdicts : List (String × Bool) := [
  ("textual append computes the ordered pair", run 12 [true] [false] == some expected),
  ("recursive append retains every element", run 12 [true, false] [true] == some (packet element [true, false, true])),
  ("empty left retains the complete suffix", run 12 [] [false, true] == some (packet element [false, true])),
  ("empty right retains the complete prefix", run 12 [true, false] [] == some (packet element [true, false])),
  ("missing element is a different result", decide (expected ≠ packet element [true])),
  ("extra element is a different result", decide (expected ≠ packet element [true, false, false])),
  ("equal length does not hide reordered payload", decide (expected ≠ packet element [false, true])),
  ("same shape does not hide changed payload", decide (expected ≠ packet element [true, true])),
  ("selected element representation remains visible", decide (expected ≠ packet (.const `Other) [true, false])),
  ("zero fuel retains the original application", run 0 [true] [false] == some program),
  ("zero fuel has not computed the answer", run 0 [true] [false] != some expected),
  ("natural-only typing does not license vector execution",
    ((Programs.ComputationProfiles.decoder Programs.ComputationProfiles.naturalOnly).decode Programs.ComputationProfiles.vectorNilCode).isNone),
  ("full execution policy accepts that vector receipt",
    ((Programs.ComputationProfiles.decoder (fun _ => true)).decode Programs.ComputationProfiles.vectorNilCode).isSome)]

#eval verdicts

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

#print axioms append_nonempty_source
#print axioms all_verdicts

end Mettapedia.GSLT.LanguageDef.IndexedInductive.Guest.AppendMeaningControls
