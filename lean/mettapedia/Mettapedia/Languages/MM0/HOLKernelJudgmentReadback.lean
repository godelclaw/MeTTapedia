import Mettapedia.Languages.MM0.HOLKernelTermReadbackCoherence
import Mettapedia.Languages.MM0.HOLKernelJudgment

/-!
# Intrinsic reading of mixed native HOL judgments

Native object typing, theorem assertion, context conjunction and consequence
are read in one supplied typed variable frame. A typing claim retains the
reconstructed term and its intrinsic type; it is refused when the annotation
and the term disagree. Its logical reading is truth because that formation
obligation has already been discharged by reconstruction. This erasure does
not identify formation claims as syntax.

Assertions retain the actual source formula. Native context conjunction and
consequence become source conjunction and implication. Reading a judgment
does not supply a derivation of its logical reading.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelJudgmentReadback

open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback
open NamedElaboration (BinderNames SomeConst)

universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}

inductive Judgment (Const : Ty Unit → Type u) (gamma : Ctx Unit) where
  | typing {type : Ty Unit} (term : Term Const gamma type)
  | assertion (formula : Formula Const gamma)
  | conjunction (first second : Judgment Const gamma)
  | consequence (first second : Judgment Const gamma)

/-- Formation data are retained in `Judgment.typing`, independently of this
logical interpretation of the already checked judgment. -/
def Judgment.formula : Judgment Const gamma → Formula Const gamma
  | .typing _ => .top
  | .assertion formula => formula
  | .conjunction first second => .and first.formula second.formula
  | .consequence first second => .imp first.formula second.formula

def readTypingWith (reader : TermReader Const) (references : HOLKernelSyntax.Symbol → Nat)
    (names : Names gamma) (nativeTerm nativeType : Preterm) :
    Option (Judgment Const gamma) :=
  match readType references nativeType with
  | none => none
  | some type => do
      let decoded ← reader names nativeTerm
      pure (.typing (← expect type decoded))

def readJudgmentWith (reader : TermReader Const) (references : HOLKernelSyntax.Symbol → Nat)
    (names : Names gamma) : Preterm → Option (Judgment Const gamma)
  | .app (.term index) object =>
      if readHead references index = some .thm then
        ((reader names object).bind (expect .prop)).map Judgment.assertion
      else none
  | .app (.app (.term index) first) second =>
      match readHead references index with
      | some .ty => readTypingWith reader references names first second
      | some .an => do
          pure (.conjunction (← readJudgmentWith reader references names first)
            (← readJudgmentWith reader references names second))
      | some .im => do
          pure (.consequence (← readJudgmentWith reader references names first)
            (← readJudgmentWith reader references names second))
      | _ => none
  | _ => none
termination_by native => sizeOf native


def readTyping (references : HOLKernelSyntax.Symbol → Nat)
    (constants : Nat → Option (SomeConst Const)) (parameters : Nat)
    (names : Names gamma) (nativeTerm nativeType : Preterm) : Option (Judgment Const gamma) :=
  readTypingWith (readTerm references constants parameters) references names nativeTerm nativeType

def readJudgment (references : HOLKernelSyntax.Symbol → Nat)
    (constants : Nat → Option (SomeConst Const)) (parameters : Nat)
    (names : Names gamma) (native : Preterm) : Option (Judgment Const gamma) :=
  readJudgmentWith (readTerm references constants parameters) references names native

theorem readJudgment_holds (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references)
    (constants : Nat → Option (SomeConst Const)) (parameters : Nat)
    (names : Names gamma) (native : Preterm) :
    readJudgment references constants parameters names
      (HOLKernelJudgment.holds references native) =
      (readFormula references constants parameters names native).map Judgment.assertion := by
  simp [HOLKernelJudgment.holds, applySymbol, Preterm.applyArgs, readJudgment, readJudgmentWith, readFormula,
    readHead_reference references faithful]

theorem readJudgment_hasType (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references)
    (constants : Nat → Option (SomeConst Const)) (parameters : Nat)
    (names : Names gamma) (nativeTerm nativeType : Preterm) :
    readJudgment references constants parameters names
      (HOLKernelJudgment.hasType references nativeTerm nativeType) =
      readTyping references constants parameters names nativeTerm nativeType := by
  simp [HOLKernelJudgment.hasType, applySymbol, Preterm.applyArgs, readJudgment, readJudgmentWith, readTyping,
    readHead_reference references faithful]

theorem readJudgment_conjunction (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references)
    (constants : Nat → Option (SomeConst Const)) (parameters : Nat)
    (names : Names gamma) (first second : Preterm) :
    readJudgment references constants parameters names
      (HOLKernelJudgment.conjunction references first second) =
      ((readJudgment references constants parameters names first).bind fun left =>
        (readJudgment references constants parameters names second).bind fun right =>
          some (Judgment.conjunction left right)) := by
  simp [HOLKernelJudgment.conjunction, applySymbol, Preterm.applyArgs, readJudgment, readJudgmentWith,
    readHead_reference references faithful]

theorem readJudgment_entails (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references)
    (constants : Nat → Option (SomeConst Const)) (parameters : Nat)
    (names : Names gamma) (first second : Preterm) :
    readJudgment references constants parameters names
      (HOLKernelJudgment.entails references first second) =
      ((readJudgment references constants parameters names first).bind fun left =>
        (readJudgment references constants parameters names second).bind fun right =>
          some (Judgment.consequence left right)) := by
  simp [HOLKernelJudgment.entails, applySymbol, Preterm.applyArgs, readJudgment, readJudgmentWith,
    readHead_reference references faithful]

theorem readTyping_encode (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references)
    (constants : Nat → Option (SomeConst Const))
    (indices : {type : Ty Unit} → Const type → Nat) (parameters : Nat)
    (constantReadback : ∀ {type} (constant : Const type),
      constants (indices constant) = some ⟨type, constant⟩)
    (constantBound : ∀ {type} (constant : Const type), indices constant < parameters)
    (names : Names gamma) (depth : Nat)
    (scope : InScope parameters names depth)
    {type : Ty Unit} (term : Term Const gamma type) :
    readTyping references constants parameters names
      (encodeTerm references (fun _ : Unit => .var 0)
        (fun {_} constant => .var (indices constant)) (fun level => parameters + level)
        names.nameOf depth term)
      (encodeType references (fun _ : Unit => .var 0) type) = some (.typing term) := by
  unfold readTyping readTypingWith
  rw [readType_encode references faithful]
  dsimp only
  rw [readTerm_encode references faithful constants indices parameters
    constantReadback constantBound term names depth scope]
  change (expect type ⟨type, term⟩).bind (fun decoded => some (Judgment.typing decoded)) = _
  rw [expect_same]
  rfl

#print axioms readTyping_encode
#print axioms readJudgment_entails

end Mettapedia.Languages.MM0.HOLKernelJudgmentReadback
