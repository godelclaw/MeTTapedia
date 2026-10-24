import Mettapedia.Languages.MM0.HOLKernelSetOperationReadbackCoherence

/-!
# Exact ordered sequent readback for the maintained MM0 material profile

The reader computes the authored HOL conclusion and every ordered assumption
from the actual native statement. It recognizes the existing formation
antecedent and the native context conjunction, rather than treating object
Boolean conjunction as a context constructor. The complete source sequent
round-trips, and successful canonical reading has an exact native encoding.

These are statement and representation results. Native proof acceptance and
reconstruction of an ordinary source derivation remain separate judgments.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelSetOperationReadback
open Mettapedia.Logic.HOL
open HOLKernelTermReadback
open Kernel HOLKernelSyntax HOLKernelJudgment
open Embedding.ZFSetHenkinInterpretation (Symbol)
open NamedElaboration (BinderNames)

abbrev ScopedSequent (gamma : Ctx Unit) := List (Formula Symbol gamma) × Formula Symbol gamma
abbrev SourceSequent := ScopedSequent []

/-- The actual regular-parameter representation and the position representation
coincide on the closed context. -/
theorem encode_closed (references : HOLKernelSyntax.Symbol → Nat) (source : ClosedFormula Symbol) :
    encode references (BinderNames.nil : Names []) 0 source =
      HOLKernelSetOperationInterpretation.term references source := by
  have assignment : (fun {type} (index : Var ([] : Ctx Unit) type) =>
      HOLKernelSetOperationInterpretation.noAssignment index) =
      (fun {type} (index : Var ([] : Ctx Unit) type) =>
        Preterm.var ((BinderNames.nil : Names []).nameOf index)) := by
    funext type index
    nomatch index
  unfold HOLKernelSetOperationInterpretation.term encode
  rw [assignment, HOLKernelTermAssignments.encode_positions]

def readAntecedent (references : HOLKernelSyntax.Symbol → Nat) {gamma : Ctx Unit}
    (names : Names gamma) (depth : Nat) (formation : Preterm) (native : Preterm) :
    Option (List (Formula Symbol gamma)) :=
  if native = formation then some [] else
    match native with
    | .app (.app (.term conjunction) rest) (.app (.term assertion) first) => do
        if readHead references conjunction = some .an ∧ readHead references assertion = some .thm then
          let formula ← readCanonicalFormula references names depth first
          let tail ← readAntecedent references names depth formation rest
          pure (formula :: tail)
        else none
    | _ => none
termination_by sizeOf native

private theorem sizeOf_app (function argument : Preterm) :
    sizeOf (Preterm.app function argument) = 1 + sizeOf function + sizeOf argument := rfl

theorem antecedent_size (references : HOLKernelSyntax.Symbol → Nat) (formation : Preterm)
    (assumptions : List Preterm) :
    sizeOf formation ≤ sizeOf (HOLKernelAssumptions.antecedent references formation assumptions) := by
  induction assumptions with
  | nil => exact Nat.le_refl _
  | cons first rest ih =>
      change sizeOf formation ≤ sizeOf (Preterm.app
        (.app (.term (references .an)) (HOLKernelAssumptions.antecedent references formation rest)) first)
      rw [sizeOf_app, sizeOf_app]
      omega

theorem antecedent_cons_ne_formation (references : HOLKernelSyntax.Symbol → Nat) (formation first : Preterm)
    (rest : List Preterm) :
    HOLKernelAssumptions.antecedent references formation (first :: rest) ≠ formation := by
  have previous := antecedent_size references formation rest
  have larger : sizeOf formation < sizeOf (HOLKernelAssumptions.antecedent references formation (first :: rest)) := by
    change sizeOf formation < sizeOf (Preterm.app
      (.app (.term (references .an)) (HOLKernelAssumptions.antecedent references formation rest)) first)
    rw [sizeOf_app, sizeOf_app]
    omega
  exact fun equal => (Nat.ne_of_lt larger) (congrArg sizeOf equal).symm

theorem readAntecedent_encode (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) {gamma : Ctx Unit} (names : Names gamma) (depth : Nat)
    (scope : InScope names depth) (formation : Preterm) (assumptions : List (Formula Symbol gamma)) :
    readAntecedent references names depth formation
      (HOLKernelAssumptions.antecedent references formation
        (assumptions.map (fun formula => holds references (encode references names depth formula)))) =
      some assumptions := by
  induction assumptions with
  | nil =>
      simp only [List.map_nil, HOLKernelAssumptions.antecedent]
      unfold readAntecedent
      simp
  | cons first rest ih =>
      have different := antecedent_cons_ne_formation references formation
        (holds references (encode references names depth first))
        (rest.map (fun formula => holds references (encode references names depth formula)))
      simp only [List.map_cons, HOLKernelAssumptions.antecedent, conjunction, holds,
        applySymbol, Preterm.applyArgs] at different ⊢
      simp only [holds, applySymbol, Preterm.applyArgs] at ih
      unfold readAntecedent
      split
      · rename_i same
        exact False.elim (different same)
      · simp [readHead_reference references faithful,
          readCanonicalFormula_encode references faithful first names depth scope, ih]

def encodeSequent (references : HOLKernelSyntax.Symbol → Nat) {gamma : Ctx Unit}
    (names : Names gamma) (depth : Nat) (formation : Preterm) (sequent : ScopedSequent gamma) : Preterm :=
  entails references
    (HOLKernelAssumptions.antecedent references formation
      (sequent.1.map (fun formula => holds references (encode references names depth formula))))
    (holds references (encode references names depth sequent.2))

private def parseSequent (references : HOLKernelSyntax.Symbol → Nat) {gamma : Ctx Unit}
    (names : Names gamma) (depth : Nat) (formation : Preterm) : Preterm → Option (ScopedSequent gamma)
  | .app (.app (.term implication) antecedent) (.app (.term assertion) conclusion) => do
      if readHead references implication = some .im ∧ readHead references assertion = some .thm then
        let assumptions ← readAntecedent references names depth formation antecedent
        let goal ← readCanonicalFormula references names depth conclusion
        pure (assumptions, goal)
      else none
  | _ => none

/-- Read an explicitly supplied typed context and formation prefix. The
reader derives the sequent data; it does not derive its proof or the frame. -/
def readSequentIn (references : HOLKernelSyntax.Symbol → Nat) {gamma : Ctx Unit}
    (names : Names gamma) (depth : Nat) (formation native : Preterm) : Option (ScopedSequent gamma) := do
  let sequent ← parseSequent references names depth formation native
  if encodeSequent references names depth formation sequent = native then some sequent else none

theorem readSequentIn_sound (references : HOLKernelSyntax.Symbol → Nat) {gamma : Ctx Unit}
    (names : Names gamma) (depth : Nat) (formation native : Preterm) (sequent : ScopedSequent gamma)
    (accepted : readSequentIn references names depth formation native = some sequent) :
    encodeSequent references names depth formation sequent = native := by
  cases parsed : parseSequent references names depth formation native with
  | none => simp [readSequentIn, parsed] at accepted
  | some actual =>
      by_cases same : encodeSequent references names depth formation actual = native
      · simp [readSequentIn, parsed, same] at accepted
        subst sequent
        exact same
      · simp [readSequentIn, parsed, same] at accepted

theorem readSequentIn_encode (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) {gamma : Ctx Unit} (names : Names gamma) (depth : Nat)
    (scope : InScope names depth) (formation : Preterm) (sequent : ScopedSequent gamma) :
    readSequentIn references names depth formation (encodeSequent references names depth formation sequent) =
      some sequent := by
  have contextRead := readAntecedent_encode references faithful names depth scope formation sequent.1
  have formulaRead := readCanonicalFormula_encode references faithful sequent.2 names depth scope
  simp only [holds, applySymbol, Preterm.applyArgs] at contextRead
  unfold readSequentIn parseSequent encodeSequent
  cases sequent
  simp [entails, holds, applySymbol, Preterm.applyArgs, readHead_reference references faithful,
    contextRead, formulaRead]

theorem scoped_sequent_injective (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) {gamma : Ctx Unit} (names : Names gamma) (depth : Nat)
    (scope : InScope names depth) (formation : Preterm) :
    Function.Injective (encodeSequent references names depth formation) := by
  intro first second same
  have compared := congrArg (readSequentIn references names depth formation) same
  rw [readSequentIn_encode references faithful names depth scope,
    readSequentIn_encode references faithful names depth scope] at compared
  exact Option.some.inj compared

theorem encodeSequent_closed (references : HOLKernelSyntax.Symbol → Nat) (sequent : SourceSequent) :
    encodeSequent references BinderNames.nil 0 (HOLKernelSetOperationInterpretation.formation references) sequent =
      HOLKernelSetOperationInterpretation.statement references sequent.1 sequent.2 := by
  simp only [encodeSequent, encode_closed, HOLKernelSetOperationInterpretation.statement]

def readSequent (references : HOLKernelSyntax.Symbol → Nat) (native : Preterm) : Option SourceSequent :=
  readSequentIn references BinderNames.nil 0 (HOLKernelSetOperationInterpretation.formation references) native

theorem readSequent_sound (references : HOLKernelSyntax.Symbol → Nat) (native : Preterm) (sequent : SourceSequent)
    (accepted : readSequent references native = some sequent) :
    HOLKernelSetOperationInterpretation.statement references sequent.1 sequent.2 = native := by
  have exactCode := readSequentIn_sound references BinderNames.nil 0
    (HOLKernelSetOperationInterpretation.formation references) native sequent accepted
  simpa only [encodeSequent_closed] using exactCode

theorem readSequent_statement (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) (assumptions : List (ClosedFormula Symbol)) (goal : ClosedFormula Symbol) :
    readSequent references (HOLKernelSetOperationInterpretation.statement references assumptions goal) =
      some (assumptions, goal) := by
  have emptyScope : InScope (BinderNames.nil : Names []) 0 := ⟨by simp [BinderNames.toList], by simp [BinderNames.toList]⟩
  change readSequentIn references BinderNames.nil 0 (HOLKernelSetOperationInterpretation.formation references)
    (HOLKernelSetOperationInterpretation.statement references assumptions goal) = some (assumptions, goal)
  rw [← encodeSequent_closed references (assumptions, goal)]
  exact readSequentIn_encode references faithful BinderNames.nil 0 emptyScope _ _

theorem readSequent_iff (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) (native : Preterm) (sequent : SourceSequent) :
    readSequent references native = some sequent ↔
      native = HOLKernelSetOperationInterpretation.statement references sequent.1 sequent.2 := by
  constructor
  · exact fun accepted => (readSequent_sound references native sequent accepted).symm
  · intro same
    rw [same]
    exact readSequent_statement references faithful sequent.1 sequent.2

theorem statement_injective (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) :
    Function.Injective (fun sequent : SourceSequent =>
      HOLKernelSetOperationInterpretation.statement references sequent.1 sequent.2) := by
  intro first second same
  have compared := congrArg (readSequent references) same
  rw [readSequent_statement references faithful, readSequent_statement references faithful] at compared
  exact Option.some.inj compared


theorem accepted_sequent_unique (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) {terms : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm} {witness : ProofWitness}
    {first second : SourceSequent}
    (firstAccepted : witness.check terms definitions theorems context hypotheses
      (HOLKernelSetOperationInterpretation.statement references first.1 first.2) = true)
    (secondAccepted : witness.check terms definitions theorems context hypotheses
      (HOLKernelSetOperationInterpretation.statement references second.1 second.2) = true) : first = second :=
  statement_injective references faithful (ProofWitness.Checks.deterministic
    ((ProofWitness.check_iff _ _ _ _ _ _ _).mp firstAccepted)
    ((ProofWitness.check_iff _ _ _ _ _ _ _).mp secondAccepted))

theorem refuses_changed_sequent (references : HOLKernelSyntax.Symbol → Nat)
    (faithful : Function.Injective references) {terms : TermSignature} {definitions : Definition.Signature}
    {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm} {witness : ProofWitness}
    {first second : SourceSequent}
    (accepted : witness.check terms definitions theorems context hypotheses
      (HOLKernelSetOperationInterpretation.statement references first.1 first.2) = true)
    (different : first ≠ second) :
    witness.check terms definitions theorems context hypotheses
      (HOLKernelSetOperationInterpretation.statement references second.1 second.2) = false := by
  cases result : witness.check terms definitions theorems context hypotheses
      (HOLKernelSetOperationInterpretation.statement references second.1 second.2) with
  | false => rfl
  | true => exact False.elim (different (accepted_sequent_unique references faithful accepted result))

#print axioms accepted_sequent_unique
#print axioms refuses_changed_sequent

#print axioms readSequentIn_encode
#print axioms scoped_sequent_injective
#print axioms readAntecedent_encode
#print axioms readSequent_sound
#print axioms readSequent_statement
#print axioms statement_injective
end Mettapedia.Languages.MM0.HOLKernelSetOperationReadback
