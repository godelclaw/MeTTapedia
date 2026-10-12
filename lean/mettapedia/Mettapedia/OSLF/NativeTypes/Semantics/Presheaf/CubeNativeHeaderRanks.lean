import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeFormation

/-! # Earlier-declaration evidence for generated cube headers -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeDeclarations

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open CubeEnrichment

variable {D : CubeEnrichment.Signature} (vertex : Vertex D)

@[simp] theorem before_transport {first second : Judgment (symbols D)}
    (equal : first = second) (tree : Derivation (Theory vertex) first) (bound : Nat) :
    (equal ▸ tree).before bound ↔ tree.before bound := by
  cases equal
  rfl

@[simp] theorem emptyFormed_before (bound : Nat) : (emptyFormed vertex).before bound :=
  deriveList_before .contextNil .nil bound True.intro True.intro

theorem codeFormed_before (carrier : D.Carrier) {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context)) (bound : Nat)
    (ordered : formed.before bound) (positive : 0 < bound) :
    (codeFormed vertex carrier formed).before bound := by
  have contextOrder := formed.before_judgment ordered
  exact deriveList_before (.typeFamily context (.code carrier) Fin.elim0) _ bound
    ⟨contextOrder, positive, fun position => Fin.elim0 position⟩
    ⟨ordered, emptyFormed_before vertex bound,
      deriveList_before (.substitutionNil context) _ bound
        ⟨contextOrder, True.intro, fun position => Fin.elim0 position⟩ ⟨ordered, True.intro⟩,
      True.intro⟩

theorem extendFormed_before {n : Nat} {context : ContextExpr (symbols D) n} {type : TypeExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context))
    (typed : Derivation (Theory vertex) (.type context type)) (bound : Nat)
    (contextOrder : formed.before bound) (typeOrder : typed.before bound) :
    (extendFormed vertex formed typed).before bound :=
  deriveList_before (.contextExtend context type) _ bound
    (typed.before_judgment typeOrder) ⟨contextOrder, typeOrder, True.intro⟩

theorem typingContextFormed_before (carrier : D.Carrier) (bound : Nat) (positive : 0 < bound) :
    (typingContextFormed vertex carrier).before bound := by
  let first := extendFormed vertex (emptyFormed vertex) (codeFormed vertex carrier (emptyFormed vertex))
  have firstOrder : first.before bound :=
    extendFormed_before vertex _ _ bound (emptyFormed_before vertex bound)
      (codeFormed_before vertex carrier _ bound (emptyFormed_before vertex bound) positive)
  exact extendFormed_before vertex first _ bound firstOrder
    (codeFormed_before vertex carrier first bound firstOrder positive)

theorem codeArgument_before (carrier : D.Carrier) {n m : Nat} {context : ContextExpr (symbols D) n}
    {target : ContextExpr (symbols D) m} {mapping : Substitution (symbols D) m n}
    {value : TermExpr (symbols D) n}
    (previous : Derivation (Theory vertex) (.substitution context target mapping))
    (formed : Derivation (Theory vertex) (.type target (codeType carrier m)))
    (typed : Derivation (Theory vertex) (.term context value (codeType carrier n))) (bound : Nat)
    (previousOrder : previous.before bound) (formedOrder : formed.before bound)
    (typedOrder : typed.before bound) :
    (codeArgument vertex carrier previous formed typed).before bound := by
  unfold codeArgument
  apply deriveList_before
  · have sourceOrder := (previous.before_judgment previousOrder).1
    have targetOrder := formed.before_judgment formedOrder
    have valueOrder := (typed.before_judgment typedOrder).2.1
    exact ⟨sourceOrder, targetOrder, fun position => by
      cases position using Fin.cases with
      | zero => exact valueOrder
      | succ earlier => exact (previous.before_judgment previousOrder).2.2 earlier⟩
  · simpa only [PremiseEvidence.before, before_transport] using
      And.intro previousOrder (And.intro formedOrder (And.intro typedOrder True.intro))

theorem typingArguments_before (carrier : D.Carrier) {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context)) (first second : TermExpr (symbols D) n)
    (firstTyped : Derivation (Theory vertex) (.term context first (codeType carrier n)))
    (secondTyped : Derivation (Theory vertex) (.term context second (codeType carrier n)))
    (bound : Nat) (formedOrder : formed.before bound)
    (firstOrder : firstTyped.before bound) (secondOrder : secondTyped.before bound)
    (positive : 0 < bound) :
    (typingArguments vertex carrier formed first second firstTyped secondTyped).before bound := by
  unfold typingArguments
  simp only [before_transport]
  have emptyOrder := emptyFormed_before vertex bound
  have codeOrder := codeFormed_before vertex carrier (emptyFormed vertex) bound emptyOrder positive
  have headerOrder := extendFormed_before vertex _ _ bound emptyOrder codeOrder
  have startOrder := deriveList_before (.substitutionNil context) (.cons formed .nil) bound
    ⟨formed.before_judgment formedOrder, True.intro, fun position => Fin.elim0 position⟩
    ⟨formedOrder, True.intro⟩
  apply codeArgument_before
  · exact codeArgument_before vertex carrier _ _ _ bound startOrder codeOrder secondOrder
  · exact codeFormed_before vertex carrier _ bound headerOrder positive
  · exact firstOrder

theorem typingFormed_before (carrier : D.Carrier) {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context)) (first second : TermExpr (symbols D) n)
    (firstTyped : Derivation (Theory vertex) (.term context first (codeType carrier n)))
    (secondTyped : Derivation (Theory vertex) (.term context second (codeType carrier n)))
    (bound : Nat) (formedOrder : formed.before bound)
    (firstOrder : firstTyped.before bound) (secondOrder : secondTyped.before bound)
    (positive : 2 < bound) :
    (typingFormed vertex carrier formed first second firstTyped secondTyped).before bound := by
  have zeroPositive : 0 < bound := Nat.lt_trans (by decide) positive
  apply deriveList_before
  · refine ⟨formed.before_judgment formedOrder, positive, ?_⟩
    intro position
    cases position using Fin.cases with
    | zero => exact (firstTyped.before_judgment firstOrder).2.1
    | succ previous =>
        cases previous using Fin.cases with
        | zero => exact (secondTyped.before_judgment secondOrder).2.1
        | succ impossible => exact Fin.elim0 impossible
  · exact ⟨formedOrder, typingContextFormed_before vertex carrier bound zeroPositive,
      typingArguments_before vertex carrier formed first second firstTyped secondTyped bound
        formedOrder firstOrder secondOrder zeroPositive, True.intro⟩

theorem sortFormed_before (carrier : D.Carrier) (sort : HSort) {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context)) (bound : Nat)
    (ordered : formed.before bound) (positive : 1 < bound) :
    (sortFormed vertex carrier sort formed).before bound := by
  unfold sortFormed
  simp only [before_transport]
  exact deriveList_before (.primitive context (.sort carrier sort) Fin.elim0) _ bound
    ⟨formed.before_judgment ordered, ⟨positive, (fun position => Fin.elim0 position)⟩,
      (by simpa only [Theory, signature, codeType_substitute] using
        codeType_before carrier n bound (Nat.lt_trans (by decide) positive))⟩
    ⟨ordered, emptyFormed_before vertex bound,
      codeFormed_before vertex carrier _ bound (emptyFormed_before vertex bound) (Nat.lt_trans (by decide) positive),
      deriveList_before (.substitutionNil context) _ bound
        ⟨formed.before_judgment ordered, True.intro, fun position => Fin.elim0 position⟩
        ⟨ordered, True.intro⟩, True.intro⟩

theorem codeVariable_before (carrier : D.Carrier) {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context)) (bound : Nat)
    (ordered : formed.before bound) (positive : 0 < bound) :
    (codeVariable vertex carrier formed).before bound := by
  unfold codeVariable
  simp only [before_transport]
  apply deriveList_before
  · exact ⟨⟨formed.before_judgment ordered, codeType_before carrier n bound positive⟩,
      True.intro, (by simpa only [Theory, signature, ContextExpr.lookup_zero, codeType_rename] using
        codeType_before carrier (n+1) bound positive)⟩
  · exact ⟨extendFormed_before vertex _ _ bound ordered
      (codeFormed_before vertex carrier formed bound ordered positive), True.intro⟩

theorem certifiedFormed_before (carrier : D.Carrier) (sort : HSort) {n : Nat}
    {context : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context)) (bound : Nat)
    (ordered : formed.before bound) (positive : 2 < bound) :
    (certifiedFormed vertex carrier sort formed).before bound := by
  have zeroPositive : 0 < bound := Nat.lt_trans (by decide) positive
  have onePositive : 1 < bound := Nat.lt_trans (by decide) positive
  have codeOrder := codeFormed_before vertex carrier formed bound ordered zeroPositive
  have extendedOrder := extendFormed_before vertex _ _ bound ordered codeOrder
  apply deriveList_before
  · exact ⟨formed.before_judgment ordered, certifiedCode_before carrier sort n bound positive⟩
  · exact ⟨codeOrder,
      typingFormed_before vertex carrier _ _ _ _ _ bound extendedOrder
        (codeVariable_before vertex carrier formed bound ordered zeroPositive)
        (sortFormed_before vertex carrier sort _ bound extendedOrder onePositive) positive,
      True.intro⟩



theorem vectorFormed_before {n : Nat} (types : Fin n → TypeExpr (symbols D) 0)
    (typesFormed : ∀ position {m : Nat} {context : ContextExpr (symbols D) m},
      Derivation (Theory vertex) (.context context) →
      Derivation (Theory vertex) (.type context ((types position).rename Fin.elim0)))
    (bound : Nat)
    (ordered : ∀ position {m : Nat} {context : ContextExpr (symbols D) m}
      (formed : Derivation (Theory vertex) (.context context)), formed.before bound →
      (typesFormed position formed).before bound) :
    (vectorFormed vertex types typesFormed).before bound := by
  induction n with
  | zero => exact emptyFormed_before vertex bound
  | succ n hypotheses =>
      apply extendFormed_before
      · exact hypotheses (fun position => types position.succ) (fun position => typesFormed position.succ)
          (fun position => ordered position.succ)
      · exact ordered 0 _ (hypotheses (fun position => types position.succ)
          (fun position => typesFormed position.succ) (fun position => ordered position.succ))

theorem parametersFormed_before (declaration : D.Former) (bound : Nat) (positive : 0 < bound) :
    (parametersFormed vertex declaration).before bound := by
  unfold parametersFormed
  apply vectorFormed_before
  intro position m context formed ordered
  simpa only [before_transport] using codeFormed_before vertex _ formed bound ordered positive

theorem formationParametersFormed_before (declaration : D.Former) (bound : Nat) (positive : 2 < bound) :
    (formationParametersFormed vertex declaration).before bound := by
  unfold formationParametersFormed
  apply vectorFormed_before
  intro position m context formed ordered
  simpa only [before_transport] using certifiedFormed_before vertex _ _ formed bound ordered positive

theorem vectorVariable_before {n : Nat} (types : Fin n → TypeExpr (symbols D) 0)
    (formed : Derivation (Theory vertex) (.context (vectorTelescope types))) (position : Fin n)
    (bound : Nat) (ordered : formed.before bound)
    (typeOrder : ((types position).rename (Fin.elim0 : Renaming 0 n)).before
      ranks.typeRank ranks.termRank ranks.predicateRank bound) :
    (vectorVariable vertex types formed position).before bound := by
  unfold vectorVariable
  simp only [before_transport]
  apply deriveList_before
  · exact ⟨formed.before_judgment ordered, True.intro, by rw [vectorLookup]; exact typeOrder⟩
  · exact ⟨ordered, True.intro⟩

theorem vectorArguments_before {n : Nat} {context : ContextExpr (symbols D) n}
    (formed : Derivation (Theory vertex) (.context context)) {m : Nat}
    (types : Fin m → TypeExpr (symbols D) 0)
    (typesFormed : ∀ position {length : Nat} {gamma : ContextExpr (symbols D) length},
      Derivation (Theory vertex) (.context gamma) →
      Derivation (Theory vertex) (.type gamma ((types position).rename Fin.elim0)))
    (mapping : Substitution (symbols D) m n)
    (typed : ∀ position, Derivation (Theory vertex) (.term context (mapping position)
      ((types position).rename Fin.elim0)))
    (bound : Nat) (formedOrder : formed.before bound)
    (typesOrder : ∀ position {length : Nat} {gamma : ContextExpr (symbols D) length}
      (tree : Derivation (Theory vertex) (.context gamma)), tree.before bound →
      (typesFormed position tree).before bound)
    (typedOrder : ∀ position, (typed position).before bound) :
    (vectorArguments vertex formed types typesFormed mapping typed).before bound := by
  induction m with
  | zero =>
      unfold vectorArguments
      simp only [before_transport]
      exact deriveList_before (.substitutionNil context) _ bound
        ⟨formed.before_judgment formedOrder, True.intro, fun position => Fin.elim0 position⟩
        ⟨formedOrder, True.intro⟩
  | succ m hypotheses =>
      unfold vectorArguments
      simp only [before_transport]
      apply deriveList_before
      · exact ⟨formed.before_judgment formedOrder,
          (vectorFormed vertex types typesFormed).before_judgment
            (vectorFormed_before vertex types typesFormed bound typesOrder),
          fun position => by
            cases position using Fin.cases with
            | zero => exact ((typed 0).before_judgment (typedOrder 0)).2.1
            | succ previous => exact ((typed previous.succ).before_judgment (typedOrder previous.succ)).2.1⟩
      · exact ⟨hypotheses (fun position => types position.succ) (fun position => typesFormed position.succ)
          (fun position => mapping position.succ) (fun position => typed position.succ)
          (fun position => typesOrder position.succ) (fun position => typedOrder position.succ),
          typesOrder 0 _ (vectorFormed_before vertex (fun position => types position.succ)
            (fun position => typesFormed position.succ) bound (fun position => typesOrder position.succ)),
          (by simpa only [before_transport] using typedOrder 0), True.intro⟩

theorem projectedCode_before (declaration : D.Former) (position : Fin (D.arity declaration))
    (bound : Nat) (positive : 2 < bound) :
    (projectedCode vertex declaration position).before bound := by
  have zeroPositive : 0 < bound := Nat.lt_trans (by decide) positive
  have onePositive : 1 < bound := Nat.lt_trans (by decide) positive
  have formedOrder := formationParametersFormed_before vertex declaration bound positive
  have codeOrder := codeFormed_before vertex (D.input declaration position) _ bound formedOrder zeroPositive
  have extendedOrder := extendFormed_before vertex _ _ bound formedOrder codeOrder
  unfold projectedCode
  apply deriveList_before
  · exact ⟨((formationParametersFormed vertex declaration).before_judgment formedOrder),
      ⟨codeType_before _ _ bound zeroPositive, ⟨positive, fun index => by
        cases index using Fin.cases with
        | zero => trivial
        | succ _ => exact sortCode_before _ _ _ bound onePositive⟩, True.intro⟩,
      codeType_before _ _ bound zeroPositive⟩
  · refine ⟨codeOrder, ?_, ?_, True.intro⟩
    · exact typingFormed_before vertex _ _ _ _ _ _ bound extendedOrder
        (codeVariable_before vertex _ _ bound formedOrder zeroPositive)
        (sortFormed_before vertex _ _ _ bound extendedOrder onePositive) positive
    · simp only [before_transport]
      apply vectorVariable_before
      · exact formedOrder
      · rw [certifiedCode_rename]
        exact certifiedCode_before _ _ _ bound positive

theorem formerResultFormed_before (declaration : D.Former) (bound : Nat) (positive : 0 < bound) :
    (formerResultFormed vertex declaration).before bound :=
  codeFormed_before vertex _ _ bound (parametersFormed_before vertex declaration bound positive) positive

theorem formedCodeFormed_before (declaration : D.Former) (bound : Nat) (positive : 2 < bound) :
    (formedCodeFormed vertex declaration).before bound := by
  have zeroPositive : 0 < bound := Nat.lt_trans (by decide) positive
  have onePositive : 1 < bound := Nat.lt_trans (by decide) positive
  have formedOrder := formationParametersFormed_before vertex declaration bound positive
  unfold formedCodeFormed
  simp only [before_transport]
  apply deriveList_before
  · refine ⟨((formationParametersFormed vertex declaration).before_judgment formedOrder),
      ⟨onePositive, ?_⟩, ?_⟩
    · intro position
      exact ((projectedCode vertex declaration position).before_judgment
        (projectedCode_before vertex declaration position bound positive)).2.1
    · simpa only [Theory, signature, codeType_substitute] using codeType_before _ _ bound zeroPositive
  · refine ⟨formedOrder, parametersFormed_before vertex declaration bound zeroPositive,
      formerResultFormed_before vertex declaration bound zeroPositive, ?_, True.intro⟩
    apply vectorArguments_before
    · exact formedOrder
    · intro position n context formed ordered
      simpa only [before_transport] using codeFormed_before vertex _ formed bound ordered zeroPositive
    · intro position
      simpa only [before_transport] using projectedCode_before vertex declaration position bound positive

theorem formationResultFormed_before (declaration : D.Former) (bound : Nat) (positive : 2 < bound) :
    (formationResultFormed vertex declaration).before bound :=
  typingFormed_before vertex _ _ _ _ _ _ bound
    (formationParametersFormed_before vertex declaration bound positive)
    (formedCodeFormed_before vertex declaration bound positive)
    (sortFormed_before vertex _ _ _ bound
      (formationParametersFormed_before vertex declaration bound positive) (Nat.lt_trans (by decide) positive))
    positive

/-- All headers are actual generated native formation trees using only earlier
symbols, including the code projections in formation-rule result types. -/
def headers : HeaderFormation (signature vertex) where
  typeHeader symbol := match symbol with
    | .code _ => emptyFormed vertex
    | .typing carrier => typingContextFormed vertex carrier
  typeHeader_before := by
    intro symbol
    cases symbol with
    | code => exact emptyFormed_before vertex 0
    | typing carrier => exact typingContextFormed_before vertex carrier 2 (by decide)
  termHeader symbol := match symbol with
    | .sort _ _ | .starBox _ => emptyFormed vertex
    | .former declaration => parametersFormed vertex declaration
    | .formation declaration => formationParametersFormed vertex declaration
  termHeader_before := by
    intro symbol
    cases symbol with
    | sort => exact emptyFormed_before vertex 1
    | starBox => exact emptyFormed_before vertex 3
    | former declaration => exact parametersFormed_before vertex declaration 1 (by decide)
    | formation declaration => exact formationParametersFormed_before vertex declaration 3 (by decide)
  termResult symbol := match symbol with
    | .sort carrier _ => codeFormed vertex carrier (emptyFormed vertex)
    | .former declaration => formerResultFormed vertex declaration
    | .starBox carrier => typingFormed vertex carrier (emptyFormed vertex)
        (sortCode carrier .star 0) (sortCode carrier .box 0)
        (sortFormed vertex carrier .star (emptyFormed vertex))
        (sortFormed vertex carrier .box (emptyFormed vertex))
    | .formation declaration => formationResultFormed vertex declaration
  termResult_before := by
    intro symbol
    cases symbol with
    | sort carrier sort => exact codeFormed_before vertex carrier _ 1 (emptyFormed_before vertex 1) (by decide)
    | former declaration => exact formerResultFormed_before vertex declaration 1 (by decide)
    | starBox carrier =>
        exact typingFormed_before vertex carrier _ _ _ _ _ 3 (emptyFormed_before vertex 3)
          (sortFormed_before vertex carrier .star _ 3 (emptyFormed_before vertex 3) (by decide))
          (sortFormed_before vertex carrier .box _ 3 (emptyFormed_before vertex 3) (by decide)) (by decide)
    | formation declaration => exact formationResultFormed_before vertex declaration 3 (by decide)
  predicateHeader symbol := nomatch symbol
  predicateHeader_before symbol := nomatch symbol

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeDeclarations
