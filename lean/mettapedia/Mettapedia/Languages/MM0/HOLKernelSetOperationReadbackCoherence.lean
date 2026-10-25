import Mettapedia.Languages.MM0.HOLKernelTermReadbackCoherence
import Mettapedia.Languages.MM0.HOLKernelSetOperationReadback
import Mettapedia.Languages.MM0.HOLKernelSetOperationSyntax

/-!
# Exact source reconstruction for the common MM0 HOL representation

All typed HOL term constructors round-trip through the independently defined
native-spine decoder. Name-bank bounds and distinct constructor references
state the representation conditions explicitly. No theorem-table acceptance
or source proof is an input to the decoder.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelSetOperationReadback
open Mettapedia.Logic.HOL
open HOLKernelTermReadback
open Kernel HOLKernelSyntax
open Embedding.ZFSetHenkinInterpretation (Symbol)
open HOLKernelSetOperationInterpretation (typeCode symbolCode symbolIndex binderName)
open NamedElaboration (BinderNames SomeTerm)

theorem readType_encode (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) (type : Ty Unit) :
    readType references (encodeType references typeCode type) = some type :=
  HOLKernelTermReadback.readType_encode references faithful type

theorem readConstant_symbol {type : Ty Unit} (symbol : Symbol type) :
    readConstant (symbolIndex symbol) = some ⟨type, symbol⟩ := by cases symbol <;> rfl


/-- The material profile has one type and six operation parameters. -/
def InScope {gamma : Ctx Unit} (names : Names gamma) (depth : Nat) : Prop :=
  HOLKernelTermReadback.InScope 7 names depth

theorem binderName_value (depth : Nat) : binderName depth = 7 + depth := rfl

theorem symbolIndex_bound {type : Ty Unit} (symbol : Symbol type) : symbolIndex symbol < 7 := by
  cases symbol <;> decide

theorem readTerm_encode (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) {gamma : Ctx Unit} {type : Ty Unit}
    (source : Term Symbol gamma type) (names : Names gamma) (depth : Nat) (scope : InScope names depth) :
    readTerm references names
      (encodeTerm references typeCode (fun {_} symbol => symbolCode symbol)
        binderName names.nameOf depth source) = some ⟨type, source⟩ :=
  HOLKernelTermReadback.readTerm_encode references faithful readConstant (fun {_} symbol => symbolIndex symbol)
    7 (fun symbol => readConstant_symbol symbol) (fun symbol => symbolIndex_bound symbol) source names depth scope

def encode (references : HOLKernelSyntax.Symbol → Nat) {gamma : Ctx Unit}
    (names : Names gamma) (depth : Nat) {type : Ty Unit} (source : Term Symbol gamma type) : Preterm :=
  encodeTerm references typeCode (fun {_} symbol => symbolCode symbol) binderName names.nameOf depth source

/-- The reconstructed term is compared with the submitted bytes' actual
preterm. The independently computed decoder supplies the typed term. -/
def readCanonicalTerm (references : HOLKernelSyntax.Symbol → Nat) {gamma : Ctx Unit}
    (names : Names gamma) (depth : Nat) (native : Preterm) : Option (Decoded Symbol gamma) := do
  let decoded ← readTerm references names native
  if encode references names depth decoded.term = native then some decoded else none

theorem readCanonicalTerm_sound (references : HOLKernelSyntax.Symbol → Nat)
    {gamma : Ctx Unit} (names : Names gamma) (depth : Nat) (native : Preterm) (decoded : Decoded Symbol gamma)
    (accepted : readCanonicalTerm references names depth native = some decoded) :
    encode references names depth decoded.term = native := by
  cases parsed : readTerm references names native with
  | none => simp [readCanonicalTerm, parsed] at accepted
  | some actual =>
      by_cases same : encode references names depth actual.term = native
      · simp [readCanonicalTerm, parsed, same] at accepted
        subst decoded
        exact same
      · simp [readCanonicalTerm, parsed, same] at accepted

theorem readCanonicalTerm_encode (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) {gamma : Ctx Unit} {type : Ty Unit}
    (source : Term Symbol gamma type) (names : Names gamma) (depth : Nat) (scope : InScope names depth) :
    readCanonicalTerm references names depth (encode references names depth source) = some ⟨type, source⟩ := by
  simp [readCanonicalTerm, encode, readTerm_encode references faithful source names depth scope]

theorem readCanonicalTerm_iff (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) {gamma : Ctx Unit} (names : Names gamma) (depth : Nat)
    (scope : InScope names depth) (native : Preterm) (decoded : Decoded Symbol gamma) :
    readCanonicalTerm references names depth native = some decoded ↔
      native = encode references names depth decoded.term := by
  constructor
  · exact fun accepted => (readCanonicalTerm_sound references names depth native decoded accepted).symm
  · intro same
    rw [same]
    exact readCanonicalTerm_encode references faithful decoded.term names depth scope

theorem encode_injective (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) {gamma : Ctx Unit} (names : Names gamma) (depth : Nat)
    (scope : InScope names depth) :
    Function.Injective (fun decoded : Decoded Symbol gamma => encode references names depth decoded.term) := by
  intro first second same
  have compared := congrArg (readCanonicalTerm references names depth) same
  rw [readCanonicalTerm_encode references faithful first.term names depth scope,
    readCanonicalTerm_encode references faithful second.term names depth scope] at compared
  cases first
  cases second
  exact Option.some.inj compared

def readCanonicalFormula (references : HOLKernelSyntax.Symbol → Nat) {gamma : Ctx Unit}
    (names : Names gamma) (depth : Nat) (native : Preterm) : Option (Formula Symbol gamma) := do
  let formula ← readFormula references names native
  if encode references names depth formula = native then some formula else none

theorem readFormula_encode (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) {gamma : Ctx Unit} (source : Formula Symbol gamma)
    (names : Names gamma) (depth : Nat) (scope : InScope names depth) :
    readFormula references names (encode references names depth source) = some source := by
  simp [readFormula, encode, readTerm_encode references faithful source names depth scope]

theorem readCanonicalFormula_encode (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) {gamma : Ctx Unit} (source : Formula Symbol gamma)
    (names : Names gamma) (depth : Nat) (scope : InScope names depth) :
    readCanonicalFormula references names depth (encode references names depth source) = some source := by
  simp [readCanonicalFormula, readFormula_encode references faithful source names depth scope]

theorem readCanonicalFormula_sound (references : HOLKernelSyntax.Symbol → Nat)
    {gamma : Ctx Unit} (names : Names gamma) (depth : Nat) (native : Preterm) (formula : Formula Symbol gamma)
    (accepted : readCanonicalFormula references names depth native = some formula) :
    encode references names depth formula = native := by
  cases parsed : readFormula references names native with
  | none => simp [readCanonicalFormula, parsed] at accepted
  | some actual =>
      by_cases same : encode references names depth actual = native
      · simp [readCanonicalFormula, parsed, same] at accepted
        subst formula
        exact same
      · simp [readCanonicalFormula, parsed, same] at accepted

def readFormulas (references : HOLKernelSyntax.Symbol → Nat) {gamma : Ctx Unit}
    (names : Names gamma) (depth : Nat) (native : List Preterm) : Option (List (Formula Symbol gamma)) :=
  native.mapM (readCanonicalFormula references names depth)

theorem readFormulas_encode (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) {gamma : Ctx Unit} (source : List (Formula Symbol gamma))
    (names : Names gamma) (depth : Nat) (scope : InScope names depth) :
    readFormulas references names depth (source.map (encode references names depth)) = some source := by
  induction source with
  | nil => rfl
  | cons first rest ih =>
      simp only [readFormulas, List.map_cons, List.mapM_cons,
        readCanonicalFormula_encode references faithful first names depth scope] at ih ⊢
      simp [ih]

theorem readFormulas_sound (references : HOLKernelSyntax.Symbol → Nat)
    {gamma : Ctx Unit} (names : Names gamma) (depth : Nat) (native : List Preterm)
    (formulas : List (Formula Symbol gamma))
    (accepted : readFormulas references names depth native = some formulas) :
    List.Forall₂ (fun code formula => encode references names depth formula = code) native formulas := by
  induction native generalizing formulas with
  | nil => simp [readFormulas] at accepted; subst formulas; exact .nil
  | cons first rest ih =>
      cases parsed : readCanonicalFormula references names depth first with
      | none => simp [readFormulas, List.mapM_cons, parsed] at accepted
      | some formula =>
          cases remainder : readFormulas references names depth rest with
          | none =>
              have expanded := remainder
              unfold readFormulas at expanded
              simp [readFormulas, List.mapM_cons, parsed, expanded] at accepted
          | some tail =>
              have expanded := remainder
              unfold readFormulas at expanded
              have result : formula :: tail = formulas := by
                simpa [readFormulas, List.mapM_cons, parsed, expanded] using accepted
              subst formulas
              exact .cons (readCanonicalFormula_sound references names depth first formula parsed) (ih tail remainder)

#print axioms readCanonicalTerm_sound
#print axioms readCanonicalTerm_iff
#print axioms encode_injective
#print axioms readFormulas_sound

#print axioms readType_encode
#print axioms readConstant_symbol
#print axioms readTerm_encode
end Mettapedia.Languages.MM0.HOLKernelSetOperationReadback
