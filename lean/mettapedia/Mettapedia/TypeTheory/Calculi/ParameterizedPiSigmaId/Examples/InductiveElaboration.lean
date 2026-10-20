import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.IndexedPolynomialGeneratedChecking
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveElaboration
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.IndexedFamilyChecking

/-!+# Generated-root replay and bidirectional dependent evidence controls

The generated natural recursor is checked through the common table decoder.
The evidence producer separately consumes the actual cumulative Nat/Vec
declarations. Malicious producer choices, wrong dependent payload types and
unformed contexts are refused by final replay.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace InductiveElaborationControls

open TypedEquality Normalization Annotated
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

variable {n : Nat}

abbrev constructors : List (DeclName × List (Normalization.Field Unit)) := exampleNat
abbrev recursor : DeclName := `natRec
abbrev zeroOrigin : IndexedPolynomialGenerated.Origin constructors := ⟨0, `zero, [], rfl⟩
abbrev succOrigin : IndexedPolynomialGenerated.Origin constructors := ⟨1, `suc, [.recursive], rfl⟩

def zeroReceipt : IndexedPolynomialGenerated.Receipt constructors 0 :=
  ⟨zeroOrigin, ![.const `step, .const `base, .const `motive]⟩

def succReceipt : IndexedPolynomialGenerated.Receipt constructors 1 :=
  ⟨succOrigin, ![.var 0, .const `step, .const `base, .const `motive]⟩

abbrev generatedDecoder := IndexedPolynomialGenerated.Checking.decoder constructors recursor

def generatedVerdicts : List (String × Bool) := [
  ("generated natural root retains row and arguments",
    decide (generatedDecoder.decode (IndexedPolynomialGenerated.Checking.receiptCode zeroReceipt) =
      some (recApp recursor [.const `motive, .const `base, .const `step] (.const `zero),
        .const `base))),
  ("generated successor keeps recursive argument and recursive call",
    decide (generatedDecoder.decode (IndexedPolynomialGenerated.Checking.receiptCode succReceipt) =
      some (recApp recursor [.const `motive, .const `base, .const `step]
          (appSpine (.const `suc) [.var 0]),
        appSpine (.const `step) [.var 0,
          recApp recursor [.const `motive, .const `base, .const `step] (.var 0)]))),
  ("generated missing constructor rejected", (generatedDecoder.decode (n := 0) ⟨2, []⟩).isNone),
  ("generated missing metavariable rejected",
    (generatedDecoder.decode (n := 0) ⟨0, [.const `step, .const `base]⟩).isNone),
  ("generated extra metavariable rejected",
    (generatedDecoder.decode (n := 0) ⟨0, [.const `step, .const `base, .const `motive, .const `extra]⟩).isNone),
  ("generated changed reduct rejected",
    !(IndexedPolynomialGenerated.Checking.check constructors recursor
      (IndexedPolynomialGenerated.Checking.receiptRecipe zeroReceipt)
      (zeroReceipt.left recursor) (.const `step))),
  ("generated root recipe composes under a binder",
    (StructuralConversionCode.Code.single
      (.congLam (.root (IndexedPolynomialGenerated.Checking.receiptCode succReceipt)))).check
      Eq generatedDecoder.decode (.lam (succReceipt.left recursor))
      (.lam (succReceipt.right recursor))),
  ("generated root under binder rejects changed free variable",
    !(StructuralConversionCode.Code.single
      (.congLam (.root (IndexedPolynomialGenerated.Checking.receiptCode succReceipt)))).check
      Eq generatedDecoder.decode (.lam (succReceipt.left recursor)) (.lam (.var 0)))]

abbrev u0 : Tower.Head := .sort (.const 0)
abbrev ground {n : Nat} : Tower.Tm n := .head .legacyGround
abbrev identity {n : Nat} : Tower.Tm n := .lam (.var 0)
abbrev functionType {n : Nat} : Tower.Tm n := .pi (.head u0) (.head u0)

/-- Primitive choices use the maintained universe presentation. Conversion
search here proposes only syntax reflexivity, head conversion and root beta. -/
def choices (RootCode : Nat → Type) : FormationSensitiveElaboration.Choices Tower.Head RootCode where
  headType head := some (StructuralTypingReplay.TowerDecisions.headTarget head)
  join first second := match first, second with
    | .sort first, .sort second => some (.sort (.max first second))
    | _, _ => none
  cumulative first second := decide (Tower.rules.cumulative first second)
  normalize := fun _ term => term
  conversion := fun _ left right =>
    if left = right then some (.refl left)
    else match left, right with
      | .head first, .head second => some (.single (.head first second))
      | .app (.lam body) argument, _ =>
          if inst0 argument body = right then some (.single (.betaPi body argument)) else none
      | _, .app (.lam body) argument =>
          if inst0 argument body = left then some (.symm (.single (.betaPi body argument))) else none
      | _, _ => none

def towerAccept (ambient : Tower.Ctx n) (term type : Tower.Tm n) : Bool :=
  (FormationSensitiveElaboration.elaborate Tower.rules Tower.Checking.decoder
    (choices _) 48 ambient term type).isSome

abbrev nativeDecoder := NativeNaturalVectorFamilies.Checking.decoder
abbrev nativeRules := NativeNaturalVectorFamilies.rules

local instance : DecidableRel nativeRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred nativeRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (nativeRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel nativeRules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel nativeRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def nativeAccept (ambient : Tower.Ctx n) (term type : Tower.Tm n) : Bool :=
  (FormationSensitiveElaboration.elaborate nativeRules nativeDecoder
    (choices _) 64 ambient term type).isSome

open NativeNaturalVectorFamilies

abbrev elementContext : Tower.Ctx 2 :=
  .snoc (.snoc .nil (.head (.sort elementLevel))) (.var 0)

abbrev singleton : Tower.Tm 2 :=
  vconsApp (.var 1) zeroTm (.var 0) (vnilApp (.var 1))

def dishonest : FormationSensitiveElaboration.Choices Tower.Head Tower.Checking.decoder.Code :=
  { choices Tower.Checking.decoder.Code with
    conversion := fun _ left _right => some (.refl left)
    cumulative := fun _ _ => true }

def dishonestAccept (ambient : Tower.Ctx n) (term type : Tower.Tm n) : Bool :=
  (FormationSensitiveElaboration.elaborate Tower.rules Tower.Checking.decoder
    dishonest 48 ambient term type).isSome

abbrev implicitTelescope : Tower.Ctx 2 :=
  .snoc (.snoc .nil (.head (.sort elementLevel))) natTm

def implicitPatterns : List (Tower.Tm 2) := [.var 1, vecApp (.var 1) (.var 0)]

def inferredSingleton := FormationSensitiveElaboration.Implicit.elaborate nativeRules nativeDecoder
  (choices _) 64 elementContext implicitTelescope implicitPatterns (.const vconsName)
  [.var 0, vnilApp (.var 1)] (vecApp (.var 1) (succApp zeroTm))

/-- Check against the independent fully explicit constructor expression,
including its payload, index and both omitted argument values. -/
def inferredSingletonExact : Bool := match inferredSingleton with
  | none => false
  | some result => decide (result.substitution 0 = zeroTm ∧ result.substitution 1 = .var 1 ∧
      FormationSensitiveElaboration.Implicit.render implicitTelescope result.substitution
        (.const vconsName) [.var 0, vnilApp (.var 1)] = singleton)

def verdicts : List (String × Bool) := generatedVerdicts ++ [
  ("bidirectional checked lambda", towerAccept .nil identity functionType),
  ("bidirectional dependent variable", towerAccept Tower.Checking.Controls.dependentContext
    (.var 0) (.var 1)),
  ("bidirectional dependent pair", towerAccept .nil (.pair ground ground)
    (.sigma (.head u0) (.head u0))),
  ("bidirectional dependent second projection", towerAccept
    (.snoc .nil (.sigma (.head u0) (.head u0))) (.snd (.var 0)) (.head u0)),
  ("bidirectional beta conversion of expected type", towerAccept .nil ground
    (.app identity (.head u0))),
  ("bidirectional wrong lambda domain refused", !(towerAccept .nil identity (.head u0))),
  ("bidirectional malformed ambient context refused",
    !(towerAccept (.snoc .nil (.app ground ground)) (.var 0) (.app ground ground))),
  ("bidirectional fabricated conversion cannot publish",
    !(dishonestAccept .nil ground (.pi (.head u0) (.head u0)))),
  ("bidirectional fabricated downward cumulativity cannot publish",
    !(dishonestAccept .nil (.head u0) (.head u0))),
  ("bidirectional fuel exhaustion is no submission",
    (FormationSensitiveElaboration.elaborate Tower.rules Tower.Checking.decoder
      (choices _) 0 .nil identity functionType).isNone),
  ("bidirectional native zero", nativeAccept .nil zeroTm natTm),
  ("bidirectional native successor", nativeAccept .nil (succApp (succApp zeroTm)) natTm),
  ("bidirectional native natural lambda", nativeAccept .nil (.lam (succApp (.var 0)))
    (.pi natTm natTm)),
  ("bidirectional native vector nil", nativeAccept elementContext (vnilApp (.var 1))
    (vecApp (.var 1) zeroTm)),
  ("bidirectional native vector singleton", nativeAccept elementContext singleton
    (vecApp (.var 1) (succApp zeroTm))),
  ("bidirectional vector wrong length refused", !(nativeAccept elementContext singleton
    (vecApp (.var 1) zeroTm))),
  ("bidirectional vector wrong payload type refused", !(nativeAccept elementContext
    (vconsApp (.var 1) zeroTm zeroTm (vnilApp (.var 1))) (vecApp (.var 1) (succApp zeroTm)))),
  ("implicit constructor recovers element type and length", inferredSingleton.isSome),
  ("implicit constructor preserves explicit payload and order", inferredSingletonExact),
  ("implicit unconstrained length is not defaulted",
    (FormationSensitiveElaboration.Implicit.infer nativeRules (choices nativeDecoder.Code)
      64 elementContext ([.var 1] : List (Tower.Tm 2)) [.var 0]).isNone),
  ("implicit inconsistent repeated element type refused",
    (FormationSensitiveElaboration.Implicit.infer nativeRules (choices nativeDecoder.Code)
      64 elementContext ([.var 0, .var 0] : List (Tower.Tm 1)) [.var 0, zeroTm]).isNone),
  ("implicit missing explicit argument refused",
    (FormationSensitiveElaboration.Implicit.infer nativeRules (choices nativeDecoder.Code)
      64 elementContext implicitPatterns [.var 0]).isNone),
  ("implicit extra explicit argument refused",
    (FormationSensitiveElaboration.Implicit.infer nativeRules (choices nativeDecoder.Code)
      64 elementContext implicitPatterns [.var 0, vnilApp (.var 1), .var 0]).isNone),
  ("implicit hints cannot change actual function declaration",
    (FormationSensitiveElaboration.Implicit.elaborate nativeRules nativeDecoder
      (choices _) 64 elementContext implicitTelescope implicitPatterns (.const succName)
      [.var 0, vnilApp (.var 1)] (vecApp (.var 1) (succApp zeroTm))).isNone)]

theorem all_verdicts : verdicts.all (·.2) = true := by decide +kernel

/-- A concrete, formed dependent judgment obtained from inferred arguments,
compared with the independently written explicit constructor application. -/
theorem inferredSingleton_typed : FormationSensitive.Judgment nativeRules elementContext
    singleton (vecApp (.var 1) (succApp zeroTm)) := by
  have exactResult : inferredSingletonExact = true := by decide +kernel
  cases produced : inferredSingleton with
  | none => simp [inferredSingletonExact, produced] at exactResult
  | some result =>
      have typed := FormationSensitiveElaboration.Implicit.elaborate_sound nativeRules nativeDecoder
        (choices _) 64 elementContext implicitTelescope implicitPatterns (.const vconsName)
        [.var 0, vnilApp (.var 1)] (vecApp (.var 1) (succApp zeroTm)) result produced
      simp only [inferredSingletonExact, produced, decide_eq_true_eq] at exactResult
      rw [exactResult.2.2] at typed
      exact typed

end InductiveElaborationControls
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
