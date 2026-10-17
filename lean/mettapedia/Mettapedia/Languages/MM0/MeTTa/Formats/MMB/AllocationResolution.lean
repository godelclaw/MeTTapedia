import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MatchAuthority

/-!
# Current constructor resolution for original allocated MMB expressions

Allocation pointer coherence and current constructor resolution are separate.
The invariant here records the binary-to-logical constructor map consulted by
the original source. It is preserved when a proof run keeps that resolver
fixed; an arbitrary changed resolver does not acquire this invariant.
-/

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

namespace Mettapedia.Languages.MM0.MeTTa.MMBAllocationResolution

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Eval
open Effects (State boolean)
open Store (natural)
open ListAccess (listValue optionValue)
open MMBProofRunExecution (stateValue expressionValue)
open MMBAllocationExecution
open Kernel (Preterm)

abbrev program := MMBAllocationExecution.program

/-- Original variable entries or original application entries whose resolved
logical name is present in the current actual source map. -/
def ResolvedEntry (terms : List MMUResolution.Binding) (entry : Atom) : Prop :=
  (∃ pointer index, entry = variableEntry pointer index) ∨
  ∃ pointer binary identifier arguments values,
    entry = applicationEntry pointer binary identifier arguments values ∧
    MMUResolution.lookup terms (natural binary) = some (natural identifier)

def ResolvedHistory (terms : List MMUResolution.Binding) (history : List Atom) : Prop :=
  ∀ entry ∈ history, ResolvedEntry terms entry

theorem ResolvedHistory.empty (terms : List MMUResolution.Binding) : ResolvedHistory terms [] := by
  intro entry impossible
  cases impossible

theorem ResolvedHistory.variable {terms : List MMUResolution.Binding} {history : List Atom}
    (resolved : ResolvedHistory terms history) (index : Nat) :
    ResolvedHistory terms (history ++ [variableEntry history.length index]) := by
  intro entry member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact resolved entry member
  · exact .inl ⟨history.length, index, rfl⟩

theorem ResolvedHistory.application {terms : List MMUResolution.Binding} {history : List Atom}
    (resolved : ResolvedHistory terms history) (binary identifier : Nat) (arguments : List Atom) (values : List Preterm)
    (lookup : MMUResolution.lookup terms (natural binary) = some (natural identifier)) :
    ResolvedHistory terms (history ++ [applicationEntry history.length binary identifier arguments values]) := by
  intro entry member
  simp only [List.mem_append, List.mem_singleton] at member
  rcases member with member | rfl
  · exact resolved entry member
  · exact .inr ⟨history.length, binary, identifier, arguments, values, rfl, lookup⟩

theorem variables_resolved (terms : List MMUResolution.Binding) (index count : Nat) :
    ResolvedHistory terms (variableEntries index count) := by
  intro entry member
  obtain ⟨pointer, _, rfl⟩ := List.mem_map.mp member
  exact .inl ⟨pointer, pointer, rfl⟩

theorem initial_resolved (terms : List MMUResolution.Binding) (arity : Nat) :
    ResolvedHistory terms (variableEntries 0 arity) := variables_resolved terms 0 arity

/-- A chronologically authorized application retains the actual current
source resolution, without identifying its binary and logical constructor IDs. -/
theorem application_resolution {terms : List MMUResolution.Binding} {history children : List Atom}
    (resolved : ResolvedHistory terms history) (pointer binary : Nat) (value : Atom)
    (authorized : AuthorizedExpression history
      (expressionValue pointer value (.expression [.symbol "MM0:MMBApplication", natural binary, listValue children]))) :
    ∃ identifier values,
      MMUResolution.lookup terms (natural binary) = some (natural identifier) ∧
      value = Data.preterm (Preterm.applyArgs (.term identifier) values) := by
  obtain ⟨allocation, originalValue, node, same, found⟩ := authorized
  have fields := resolved _ (List.mem_of_getElem? found)
  rcases fields with ⟨allocation, index, shape⟩ |
      ⟨allocation, originalBinary, identifier, arguments, values, shape, lookup⟩
  · simp [variableEntry, expressionValue, listValue] at shape
  · simp only [applicationEntry, expressionValue, listValue, Atom.expression.injEq, List.cons.injEq,
      and_true, true_and] at shape
    have binarySame : binary = originalBinary := Data.natural_injective shape.2.2.1
    exact ⟨identifier, values, by simpa only [binarySame] using lookup, shape.2.1⟩

/-- Original initialization earns the name-resolution invariant without
consulting or evaluating arbitrary context payloads. -/
theorem initial_resolved_returns (bindings : Subst) (state : State) (context : List Atom) (count : Nat)
    (contextName countName : String)
    (contextCaptured : applySubst bindings (.var contextName) = listValue context)
    (countCaptured : applySubst bindings (.var countName) = natural count)
    (terms : List MMUResolution.Binding) :
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-initial", .var contextName, .var countName]) state
      (stateValue context.length context.length count [] (variableEntries 0 context.length) [] [] []) ∧
    ConstructedHistory (variableEntries 0 context.length) ∧
    StateCoherent (variableEntries 0 context.length) [] (variableEntries 0 context.length) [] ∧
    ResolvedHistory terms (variableEntries 0 context.length) := by
  obtain ⟨computed, built, coherent⟩ := initial_authorized_returns bindings state context count contextName countName
    contextCaptured countCaptured
  exact ⟨computed, built, coherent, initial_resolved terms context.length⟩

/-- Original dummy allocation changes only the variable history, so the
fixed current term resolver remains aligned with every application entry. -/
theorem dummy_resolved_returns (bindings : Subst) (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images : Atom)
    (binary arity count : Nat) (history stack heap dummies hypotheses saved : List Atom) (sort : Atom)
    (resolverName stateName binaryName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (stateCaptured : applySubst bindings (.var stateName) = stateValue history.length arity count stack heap dummies hypotheses saved)
    (binaryCaptured : applySubst bindings (.var binaryName) = natural binary)
    (lookup : MMUResolution.lookup sorts (natural binary) = some sort)
    (built : ConstructedHistory history) (coherent : StateCoherent history stack heap hypotheses)
    (resolved : ResolvedHistory terms history) :
    let entry := variableEntry history.length (arity + dummies.length)
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-dummy",
      .var resolverName, .var stateName, .var binaryName]) state
      (optionValue (some (stateValue (history.length + 1) arity count (entry :: stack) (heap ++ [entry])
        (dummies ++ [sort]) hypotheses saved))) ∧
    ConstructedHistory (history ++ [entry]) ∧
    StateCoherent (history ++ [entry]) (entry :: stack) (heap ++ [entry]) hypotheses ∧
    ResolvedHistory terms (history ++ [entry]) := by
  obtain ⟨computed, constructed, after⟩ := dummy_authorized_returns bindings state published sorts terms theorems
    nextSort nextTerm nextTheorem images binary arity count history stack heap dummies hypotheses saved sort
    resolverName stateName binaryName resolverCaptured stateCaptured binaryCaptured lookup built coherent
  exact ⟨computed, constructed, after, resolved.variable (arity + dummies.length)⟩

/-- The original constructor lookup and execution preserve the same current
resolution for every earlier allocation and the newly allocated application. -/
theorem term_resolved_returns (bindings : Subst) (state : State) (published : Atom)
    (sorts terms theorems : List MMUResolution.Binding) (nextSort nextTerm nextTheorem : Nat) (images tableSorts tableTheorems : Atom)
    (tableTerms formalArguments : List Atom) (sort ret value : Atom)
    (binary identifier arity count : Nat) (history stack heap dummies hypotheses saved arguments rest : List Atom)
    (values : List Preterm) (save : Bool)
    (resolverName tablesName stateName binaryName saveName : String)
    (resolverCaptured : applySubst bindings (.var resolverName) =
      MMBTheoremSignatureExecution.resolverValue published sorts terms theorems nextSort nextTerm nextTheorem images)
    (tablesCaptured : applySubst bindings (.var tablesName) =
      .expression [.symbol "MM0:MMBTables", tableSorts, listValue tableTerms, tableTheorems])
    (stateCaptured : applySubst bindings (.var stateName) = stateValue history.length arity count stack heap dummies hypotheses saved)
    (binaryCaptured : applySubst bindings (.var binaryName) = natural binary)
    (saveCaptured : applySubst bindings (.var saveName) = boolean save)
    (lookup : MMUResolution.lookup terms (natural binary) = some (natural identifier))
    (declared : tableTerms[binary]? = some (.expression [.symbol "MM0:MMBTerm", sort, listValue formalArguments, ret, value]))
    (popped : MMBTheoremCommandExecution.Pops .expressions formalArguments.length stack (some (arguments, rest)))
    (projected : MMBProofRunExecution.ExpressionClaims arguments (values.map Data.preterm))
    (built : ConstructedHistory history) (coherent : StateCoherent history stack heap hypotheses)
    (resolved : ResolvedHistory terms history) :
    let entry := applicationEntry history.length binary identifier arguments values
    PureReturns program bindings state (.expression [.symbol "mm0:mmb:proof-term",
      .var resolverName, .var tablesName, .var stateName, .var binaryName, .var saveName]) state
      (optionValue (some (stateValue (history.length + 1) arity count (entry :: rest)
        (if save then heap ++ [entry] else heap) dummies hypotheses saved))) ∧
    ConstructedHistory (history ++ [entry]) ∧
    StateCoherent (history ++ [entry]) (entry :: rest)
      (if save then heap ++ [entry] else heap) hypotheses ∧
    ResolvedHistory terms (history ++ [entry]) := by
  obtain ⟨computed, constructed, after⟩ := term_authorized_returns bindings state published sorts terms theorems
    nextSort nextTerm nextTheorem images tableSorts tableTheorems tableTerms formalArguments sort ret value
    binary identifier arity count history stack heap dummies hypotheses saved arguments rest values save
    resolverName tablesName stateName binaryName saveName resolverCaptured tablesCaptured stateCaptured binaryCaptured saveCaptured
    lookup declared popped projected built coherent
  exact ⟨computed, constructed, after, resolved.application binary identifier arguments values lookup⟩

end Mettapedia.Languages.MM0.MeTTa.MMBAllocationResolution
