import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ContextLaws

/-!
# Opening the generated dependent target continuation

Each rely contributes its actual code value and its membership evidence.
The target function is applied to those newly bound variables using the
original dependent application rules. The resulting syntax retains a typed
projection to the complete modal parameter context and every ordered value.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ContinuationSyntax

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open CubeEnrichment CubeNativeDeclarations

variable {D : CubeEnrichment.Signature} (vertex : Vertex D)

structure Result {n m : Nat} (context : ContextExpr (symbols D) m)
    (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n)) where
  size : Nat
  size_eq : size = m + 2 * relies.length
  scope : ContextExpr (symbols D) size
  formed : Derivation (Theory vertex) (.context scope)
  projection : Substitution (symbols D) m size
  projectionTyped : Derivation (Theory vertex) (.substitution scope context projection)
  output : TermExpr (symbols D) size
  outputTyped : Derivation (Theory vertex) (.term scope output (certifiedCode target sort size))
  values : Fin relies.length → TermExpr (symbols D) size
  valueTyped : ∀ position, Derivation (Theory vertex)
    (.term scope (values position) (codeType relies[position].1 size))

def formedAt {n m : Nat} (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n))
    (mapping : Substitution (symbols D) n m) {context : ContextExpr (symbols D) m}
    (formed : Derivation (Theory vertex) (.context context))
    (classifiers : ∀ position : Fin relies.length, Derivation (Theory vertex)
      (.term context (relies[position].2.substitute mapping) (codeType relies[position].1 m))) :
    Derivation (Theory vertex) (.type context (continuationAt target sort relies mapping)) := by
  rw [continuationAt_mapped]
  apply continuationFormed vertex target sort _ id formed
  intro position
  let original : Fin relies.length := ⟨position.val, by simpa only [List.length_map] using position.isLt⟩
  have equation :
      (relies.map (fun entry => (entry.1, entry.2.substitute mapping)))[position] =
        (relies[original].1, relies[original].2.substitute mapping) := by
    simp only [List.getElem_map, Fin.getElem_fin]
    rfl
  rw [equation, TermExpr.rename_identity]
  exact classifiers original

def membership {n m : Nat} (entry : D.Carrier × TermExpr (symbols D) n)
    (mapping : Substitution (symbols D) n m) : TypeExpr (symbols D) (m + 1) :=
  typingType entry.1 (.var 0) ((entry.2.substitute mapping).rename Fin.succ)

def nextContext {n m : Nat} (context : ContextExpr (symbols D) m)
    (entry : D.Carrier × TermExpr (symbols D) n) (mapping : Substitution (symbols D) n m) :
    ContextExpr (symbols D) (m + 2) :=
  .snoc (.snoc context (codeType entry.1 m)) (membership entry mapping)

structure Step {n m : Nat} (context : ContextExpr (symbols D) m)
    (target : D.Carrier) (sort : HSort)
    (entry : D.Carrier × TermExpr (symbols D) n)
    (remaining : List (D.Carrier × TermExpr (symbols D) n))
    (mapping : Substitution (symbols D) n m) where
  formed : Derivation (Theory vertex) (.context (nextContext context entry mapping))
  classifiers : ∀ position : Fin remaining.length, Derivation (Theory vertex)
    (.term (nextContext context entry mapping)
      (remaining[position].2.substitute (weakenTwice mapping)) (codeType remaining[position].1 (m + 2)))
  function : TermExpr (symbols D) (m + 2)
  typed : Derivation (Theory vertex) (.term (nextContext context entry mapping) function
    (continuationAt target sort remaining (weakenTwice mapping)))
  valueTyped : Derivation (Theory vertex)
    (.term (nextContext context entry mapping) (.var 1) (codeType entry.1 (m + 2)))
  projectionTyped : Derivation (Theory vertex) (.substitution (nextContext context entry mapping) context
    (fun position => .var position.succ.succ))

def openHead {n m : Nat} (target : D.Carrier) (sort : HSort)
    (entry : D.Carrier × TermExpr (symbols D) n)
    (remaining : List (D.Carrier × TermExpr (symbols D) n))
    (mapping : Substitution (symbols D) n m) {context : ContextExpr (symbols D) m}
    (formed : Derivation (Theory vertex) (.context context))
    (classifiers : ∀ position : Fin (entry :: remaining).length, Derivation (Theory vertex)
      (.term context ((entry :: remaining)[position].2.substitute mapping)
        (codeType (entry :: remaining)[position].1 m)))
    (function : TermExpr (symbols D) m)
    (typed : Derivation (Theory vertex)
      (.term context function (continuationAt target sort (entry :: remaining) mapping))) :
    Step vertex context target sort entry remaining mapping := by
  let domain := codeType entry.1 m
  let domainFormed := codeFormed vertex entry.1 formed
  let withValue := extendFormed vertex formed domainFormed
  have classifierThere := weakenTerm vertex (classifiers 0) domainFormed
  rw [codeType_rename] at classifierThere
  let evidenceFormed := typingFormed vertex entry.1 withValue (.var 0)
    ((entry.2.substitute mapping).rename Fin.succ)
    (codeVariable vertex entry.1 formed) classifierThere
  let withEvidence := extendFormed vertex withValue evidenceFormed
  have remainingTyped : ∀ position : Fin remaining.length, Derivation (Theory vertex)
      (.term (nextContext context entry mapping)
        (remaining[position].2.substitute (weakenTwice mapping)) (codeType remaining[position].1 (m + 2))) := by
    intro position
    have first := weakenTerm vertex (classifiers position.succ) domainFormed
    rw [codeType_rename] at first
    have second := weakenTerm vertex first evidenceFormed
    rw [codeType_rename] at second
    change Derivation (Theory vertex)
      (.term (nextContext context entry mapping)
        (((remaining[position].2.substitute mapping).rename Fin.succ).rename Fin.succ)
        (codeType remaining[position].1 (m + 2))) at second
    rw [TermExpr.rename_substitute, TermExpr.rename_substitute] at second
    exact second
  let remainingFormed := formedAt vertex target sort remaining (weakenTwice mapping)
    withEvidence remainingTyped
  let bodyFormed := deriveList
    (.piFormation (.snoc context domain) (membership entry mapping)
      (continuationAt target sort remaining (weakenTwice mapping)))
    (.cons evidenceFormed (.cons remainingFormed .nil))
  let first := applyVariable formed domainFormed bodyFormed typed
  let second := applyVariable withValue evidenceFormed remainingFormed first
  have firstValue := weakenTerm vertex (codeVariable vertex entry.1 formed) evidenceFormed
  rw [codeType_rename] at firstValue
  let firstWeakening := deriveList (.substitutionWeaken context domain) (.cons domainFormed .nil)
  let secondWeakening := deriveList (.substitutionWeaken (.snoc context domain) (membership entry mapping))
    (.cons evidenceFormed .nil)
  let toOriginal := deriveList (.substitutionCompose
    (nextContext context entry mapping) (.snoc context domain) context
    (fun position => .var position.succ) (fun position => .var position.succ))
    (.cons secondWeakening (.cons firstWeakening .nil))
  exact ⟨withEvidence, remainingTyped, _, second, firstValue, toOriginal⟩

def prepend {n m : Nat} {context : ContextExpr (symbols D) m} {target : D.Carrier} {sort : HSort}
    {entry : D.Carrier × TermExpr (symbols D) n}
    {remaining : List (D.Carrier × TermExpr (symbols D) n)}
    {mapping : Substitution (symbols D) n m}
    (step : Step vertex context target sort entry remaining mapping)
    (result : Result vertex (nextContext context entry mapping) target sort remaining) :
    Result vertex context target sort (entry :: remaining) := by
  let projection := composeSubstitution
    (fun position : Fin m => (.var position.succ.succ : TermExpr (symbols D) (m + 2)))
    result.projection
  let projectionTyped := deriveList (.substitutionCompose result.scope
    (nextContext context entry mapping) context result.projection
    (fun position => .var position.succ.succ))
    (.cons result.projectionTyped (.cons step.projectionTyped .nil))
  have supplied := deriveList (.substituteTerm result.scope
    (nextContext context entry mapping) result.projection
    (.var 1) (codeType entry.1 (m + 2)))
    (.cons result.projectionTyped (.cons step.valueTyped .nil))
  have suppliedTyped : Derivation (Theory vertex)
      (.term result.scope (result.projection 1) (codeType entry.1 result.size)) := by
    simpa only [RuleCode.conclusion, TermExpr.substitute, codeType_substitute] using supplied
  refine ⟨result.size, ?_, result.scope, result.formed, projection, projectionTyped,
    result.output, result.outputTyped, Fin.cons (result.projection 1) result.values, ?_⟩
  · have smaller := result.size_eq
    simp only [List.length_cons]
    omega
  · intro position
    refine Fin.cases ?_ ?_ position
    · exact suppliedTyped
    · intro rest
      exact result.valueTyped rest

def openAll {n m : Nat} (target : D.Carrier) (sort : HSort)
    (relies : List (D.Carrier × TermExpr (symbols D) n))
    (mapping : Substitution (symbols D) n m) {context : ContextExpr (symbols D) m}
    (formed : Derivation (Theory vertex) (.context context))
    (classifiers : ∀ position : Fin relies.length, Derivation (Theory vertex)
      (.term context (relies[position].2.substitute mapping) (codeType relies[position].1 m)))
    (function : TermExpr (symbols D) m)
    (typed : Derivation (Theory vertex)
      (.term context function (continuationAt target sort relies mapping))) :
    Result vertex context target sort relies := by
  cases relies with
  | nil =>
      exact ⟨m, by simp, context, formed, TermExpr.var,
        deriveList (.substitutionIdentity context) (.cons formed .nil),
        function, typed, Fin.elim0, fun position => position.elim0⟩
  | cons entry remaining =>
      let step := openHead vertex target sort entry remaining mapping formed classifiers function typed
      exact prepend vertex step
        (openAll target sort remaining (weakenTwice mapping) step.formed step.classifiers step.function step.typed)
termination_by relies.length

def initialMapping (interface : Interface D.Carrier) :
    Substitution (symbols D) (prefixSize interface) (arity interface) :=
  fun position => .var position.succ

def initialClassifiers (interface : Interface D.Carrier) :
    ∀ entry : Fin (relyArguments interface).length, Derivation (Theory vertex)
      (.term (parameters interface) ((relyArguments interface)[entry].2.substitute (initialMapping interface))
        (codeType (relyArguments interface)[entry].1 (arity interface))) := by
  intro entry
  let position : Fin interface.relies.length := ⟨entry.val, by simpa only [relyArguments, List.length_ofFn] using entry.isLt⟩
  have entryEq : (relyArguments interface)[entry] =
      (interface.relies[position].1, classifierValue interface.relies[position].1 interface.relies[position].2
        (.var (position.castAdd interface.indices.length))) := by
    change (List.ofFn (fun position : Fin interface.relies.length =>
      (interface.relies[position].1, classifierValue interface.relies[position].1 interface.relies[position].2
        (.var (position.castAdd interface.indices.length))))).get entry = _
    rw [List.get_ofFn]
    rfl
  rw [entryEq]
  have before := relyArgumentFormed vertex interface position
  have there := weakenTerm vertex before (targetParameterFormed vertex interface)
  rw [codeType_rename] at there
  change Derivation (Theory vertex) (.term (parameters interface)
    ((classifierValue interface.relies[position].1 interface.relies[position].2
      (.var (position.castAdd interface.indices.length))).substitute (fun position => .var position.succ))
      (codeType interface.relies[position].1 (arity interface)))
  rw [TermExpr.substitute_variables]
  exact there

def targetPosition (interface : Interface D.Carrier) : Fin (arity interface) :=
  (0 : Fin (prefixSize interface + 1))

def initialFunction (interface : Interface D.Carrier) :
    Derivation (Theory vertex) (.term (parameters interface) (.var (targetPosition interface))
      (continuationAt interface.target interface.resultSort (relyArguments interface) (initialMapping interface))) := by
  have tree := deriveList (.variable (parameters interface) (targetPosition interface))
    (.cons (parametersFormed vertex interface) .nil)
  change Derivation (Theory vertex) (.term (parameters interface) (.var (targetPosition interface))
    ((targetParameter interface).rename Fin.succ)) at tree
  rw [← TypeExpr.substitute_variables, targetParameter_substitute] at tree
  exact tree

def generated (interface : Interface D.Carrier) :
    Result vertex (parameters interface) interface.target interface.resultSort (relyArguments interface) :=
  openAll vertex interface.target interface.resultSort (relyArguments interface) (initialMapping interface)
    (parametersFormed vertex interface) (initialClassifiers vertex interface) (.var (targetPosition interface))
    (initialFunction vertex interface)

theorem generated_size (interface : Interface D.Carrier) :
    (generated vertex interface).size = arity interface + 2 * interface.relies.length := by
  simpa only [relyArguments, List.length_ofFn] using (generated vertex interface).size_eq

def indexParameterTerm (interface : Interface D.Carrier) (position : Fin interface.indices.length) :
    TermExpr (symbols D) (arity interface) :=
  .var (Fin.natAdd interface.relies.length position).succ

def indexParameterTyped (interface : Interface D.Carrier) (position : Fin interface.indices.length) :
    Derivation (Theory vertex) (.term (parameters interface) (indexParameterTerm interface position)
      (indexType interface.indices[position].1 interface.indices[position].2 (arity interface))) := by
  have before := vectorVariable vertex (prefixType interface) (prefixFormed vertex interface)
    (Fin.natAdd interface.relies.length position)
  have before' : Derivation (Theory vertex) (.term (parameterPrefix interface)
      (.var (Fin.natAdd interface.relies.length position))
      (indexType interface.indices[position].1 interface.indices[position].2 (prefixSize interface))) := by
    simpa only [prefixType, Fin.addCases_right, indexType_rename, parameterPrefix] using before
  have there := weakenTerm vertex before' (targetParameterFormed vertex interface)
  simpa only [TermExpr.rename, indexType_rename, parameters, arity, indexParameterTerm] using there

def indexRequestTerm (interface : Interface D.Carrier) (position : Fin interface.indices.length) :
    TermExpr (symbols D) (generated vertex interface).size :=
  (indexParameterTerm interface position).substitute (generated vertex interface).projection

def indexRequestTyped (interface : Interface D.Carrier) (position : Fin interface.indices.length) :
    Derivation (Theory vertex) (.term (generated vertex interface).scope (indexRequestTerm vertex interface position)
      (indexType interface.indices[position].1 interface.indices[position].2 (generated vertex interface).size)) := by
  have tree := deriveList (.substituteTerm (generated vertex interface).scope (parameters interface)
    (generated vertex interface).projection (indexParameterTerm interface position)
      (indexType interface.indices[position].1 interface.indices[position].2 (arity interface)))
    (.cons (generated vertex interface).projectionTyped (.cons (indexParameterTyped vertex interface position) .nil))
  simpa only [RuleCode.conclusion, indexType_substitute, indexRequestTerm] using tree

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ContinuationSyntax
