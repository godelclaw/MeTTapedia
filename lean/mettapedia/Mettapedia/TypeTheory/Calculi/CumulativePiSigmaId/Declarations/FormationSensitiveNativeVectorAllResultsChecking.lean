import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllResultsEvidence

/-!
# Independent replay of the constant-motive Vector result program

The finite certificate was emitted by the existing untrusted evidence
producer. Kernel replay, rather than producer output, establishes typing.
The negative executable control uses original children as result values.
No general raw-iota preservation or source-fold compiler theorem is claimed.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ResultView
open Presentation Declaration
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies
open CanonicalAdequacy
open Mettapedia.TypeTheory.IndexedContainer

local instance : DecidableRel NativeVectorAll.rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred NativeVectorAll.rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (NativeVectorAll.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel NativeVectorAll.rules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel NativeVectorAll.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

theorem replay_checked : FormationSensitiveElaboration.replay NativeVectorAll.rules NativeVectorAll.decoder .nil program programType submission = true := by decide +kernel

theorem program_formed : FormationSensitive.Judgment NativeVectorAll.rules .nil program programType := FormationSensitiveElaboration.replay_sound NativeVectorAll.rules NativeVectorAll.decoder replay_checked

#print axioms program_formed

def wrongConsCase {n : Nat} (result : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.lam (.lam (.lam
    (vconsApp (rename wk (NativeVectorAll.weaken4 result)) (.var 4) (.fst (.var 0)) (.var 2))))))

def wrongProgram : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (.lam
    (.app (vecEliminateApp (.var 4) (motive (.var 4) (.var 3)) (nilCase (.var 3))
      (wrongConsCase (.var 3)) (.var 2) (.var 1)) (.var 0))))))



def conversionAccepted {n : Nat} (left right : Tower.Tm n) : Bool :=
  match NativeVectorAll.choices.conversion 64 left right with
  | none => false
  | some code => code.check NativeVectorAll.rules.headEq NativeVectorAll.decoder.decode left right

def proofContext : Tower.Ctx 3 := .snoc (.snoc (.snoc .nil unitType) unitType) unitType
def repeatedValues : List (Tower.Tm 3) := [zeroTm, zeroTm]
def independentWitnesses : List (Tower.Tm 3) := [.var 0, .var 1]
def independentBundle : Tower.Tm 3 := PairSpine.assemble independentWitnesses (.var 2)
def independentType : Tower.Tm 3 := NativeVectorAll.allType natTm (predicate unitType)
  (numeral repeatedValues.length) (encodeVector natTm repeatedValues)
def independentSource : Tower.Tm 3 := project natTm unitType
  (numeral repeatedValues.length) (encodeVector natTm repeatedValues) independentBundle
def independentResult : Tower.Tm 3 := encodeVector unitType independentWitnesses

def independentConversion := conversionAccepted independentSource independentResult
def independentAccepted := NativeVectorAll.accepted proofContext independentBundle independentType

theorem independent_conversion : independentConversion = true := by decide +kernel
theorem independent_accepted : independentAccepted = true := by decide +kernel

theorem independent_formed : FormationSensitive.Judgment NativeVectorAll.rules
    proofContext independentBundle independentType := NativeVectorAll.accepted_sound independent_accepted

theorem independent_steps : Steps independentSource independentResult :=
  canonical_steps_assembled natTm unitType repeatedValues independentWitnesses (.var 2) rfl

def opaqueResultEvidence : Tower.Tm 1 := .var 0
def opaqueResultValues : List (Tower.Tm 1) := [zeroTm, zeroTm]

theorem opaque_result_steps :
    Steps (project natTm unitType (numeral opaqueResultValues.length)
      (encodeVector natTm opaqueResultValues) opaqueResultEvidence)
      (encodeVector unitType (PairSpine.reads opaqueResultValues.length opaqueResultEvidence)) :=
  canonical_steps_observe natTm unitType opaqueResultValues opaqueResultEvidence

def oneValue : List (Tower.Tm 3) := [zeroTm]
def firstTailBundle : Tower.Tm 3 := .pair (.var 0) (.var 1)
def secondTailBundle : Tower.Tm 3 := .pair (.var 0) (.var 2)
def tailBundleType : Tower.Tm 3 := NativeVectorAll.allType natTm (predicate unitType)
  (numeral oneValue.length) (encodeVector natTm oneValue)
def oneResult : Tower.Tm 3 := encodeVector unitType [.var 0]

def firstTailAccepted := NativeVectorAll.accepted proofContext firstTailBundle tailBundleType
def secondTailAccepted := NativeVectorAll.accepted proofContext secondTailBundle tailBundleType

theorem first_tail_accepted : firstTailAccepted = true := by decide +kernel
theorem second_tail_accepted : secondTailAccepted = true := by decide +kernel

theorem first_tail_formed : FormationSensitive.Judgment NativeVectorAll.rules
    proofContext firstTailBundle tailBundleType := NativeVectorAll.accepted_sound first_tail_accepted

theorem second_tail_formed : FormationSensitive.Judgment NativeVectorAll.rules
    proofContext secondTailBundle tailBundleType := NativeVectorAll.accepted_sound second_tail_accepted

/-- Two well-typed input spines can share this result observation while differing as raw inputs. -/
theorem shared_result_distinct_inputs :
    firstTailBundle ≠ secondTailBundle ∧
    Steps (project natTm unitType (numeral oneValue.length) (encodeVector natTm oneValue) firstTailBundle) oneResult ∧
    Steps (project natTm unitType (numeral oneValue.length) (encodeVector natTm oneValue) secondTailBundle) oneResult := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · exact canonical_steps_assembled natTm unitType oneValue [.var 0] (.var 1) rfl
  · exact canonical_steps_assembled natTm unitType oneValue [.var 0] (.var 2) rfl

def tailSyntaxDifferent := decide (firstTailBundle ≠ secondTailBundle)
theorem tail_syntax_checked : tailSyntaxDifferent = true := by decide +kernel

def positionEvidence (position : Fin repeatedValues.length) : Tower.Tm 3 :=
  if position.val = 0 then .var 0 else .var 1

noncomputable def independentSemanticBundle :
    (vectorInductionBundle (fun _ : Tower.Tm 3 => Tower.Tm 3)).Bundle (semanticValue repeatedValues) :=
  ((vectorInductionBundle (fun _ : Tower.Tm 3 => Tower.Tm 3)).exact (semanticValue repeatedValues)).symm positionEvidence

theorem semantic_readout_exact :
    (List.ofFn fun position : Fin repeatedValues.length =>
      ((vectorInductionBundle (fun _ : Tower.Tm 3 => Tower.Tm 3)).exact
        (semanticValue repeatedValues) independentSemanticBundle position)) = independentWitnesses := by
  have exactness := ((vectorInductionBundle (fun _ : Tower.Tm 3 => Tower.Tm 3)).exact
    (semanticValue repeatedValues)).apply_symm_apply positionEvidence
  have positionExact :
      (fun position : Fin repeatedValues.length =>
        (vectorInductionBundle (fun _ : Tower.Tm 3 => Tower.Tm 3)).exact
          (semanticValue repeatedValues) independentSemanticBundle position) = positionEvidence := by
    funext position
    exact congrFun exactness position
  rw [positionExact]
  rfl

theorem semantic_independent_steps :
    Steps (project natTm unitType (numeral repeatedValues.length) (encodeVector natTm repeatedValues)
      (quoteWitnesses independentWitnesses)) independentResult := by
  have path := semanticBundle_steps natTm unitType (P := fun _ : Tower.Tm 3 => Tower.Tm 3)
    (fun _ evidence => evidence) repeatedValues independentSemanticBundle
  dsimp only at path
  rw [semantic_readout_exact] at path
  exact path

def verdicts : List (String × Bool) :=
  [("constant-motive All result program replays", FormationSensitiveElaboration.replay
      NativeVectorAll.rules NativeVectorAll.decoder .nil program programType submission),
   ("original children cannot replace recursive results", !(NativeVectorAll.accepted .nil wrongProgram programType)),
   ("repeated source values retain independent ordered witnesses", independentConversion),
   ("independent position witnesses form a valid source All bundle", independentAccepted),
   ("the first opaque tail has a well-typed source bundle", firstTailAccepted),
   ("the second opaque tail has a well-typed source bundle", secondTailAccepted),
   ("distinct raw tails remain distinct before the result observation", tailSyntaxDifferent)]



end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.ResultView
