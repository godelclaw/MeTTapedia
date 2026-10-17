import Mettapedia.Languages.HOLLight.ProofSystem
import Mettapedia.Logic.HOL.ContextualTrinity
import Mettapedia.Logic.HOL.ProofSyntaxHypothesisSubstitution
import Mettapedia.Logic.HOL.Syntax.DecidableEq
import Mettapedia.Logic.HOL.ProofSyntaxConstantSubstitution
import Mettapedia.Logic.HOL.ProofSyntaxTypeSubstitution

/-!
# Elaborating HOL Light proof graphs into retained natural-deduction proofs

An accepted HOL Light proof graph elaborates, by a computable function, into a
retained proof of the extensional HOL calculus (`ProofSyntax`) whose conclusion
is the translated conclusion and whose assumptions are among the translated
hypotheses.

* **Translation is computed** (`translate?`): one pass over the canonical term,
  exact for the compositional translation (`translate?_eq_some_iff`).
* **Each rule elaborates** (`elabInference`, `elabInference_correct`). `ASSUME`
  is a hypothesis; `REFL` and `BETA` are reflexivity and one beta rule;
  `TRANS`, `MK_COMB` and `EQ_MP` are equational rules on the equations the
  premises conclude; `DEDUCT_ANTISYM_RULE` discharges each conclusion from the
  other premise; `ABS` abstracts the free variable through the whole retained
  proof (`abstractProof`); `INST` and `INST_TYPE` retype and replace symbols
  in the whole proof (`elabSubstitution`).
* **The graph elaborates node by node** (`elabFrom`), following the checker's
  replay (`elabFrom_correct`), so every accepted graph elaborates
  (`elaborate_correct`).
* **The conclusion is restated with primitive equality.** The two translations
  of a term are computed together with their equation (`bridge`,
  `bridge_complete`); compositional translations are inverted computably
  (`untranslate_eq`); `elaborateProved_correct` gives a retained proof of the
  translation with primitive equality from the translated hypotheses.

Controls: the reflexivity graph elaborates to a proof without hypotheses, and a
graph citing a missing premise does not elaborate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

open Mettapedia.Logic

/-! ## Decidable types -/

instance Ty.instDecidableEqSame : DecidableEq Ty := fun left right =>
  if same : Ty.same left right = true then isTrue ((Ty.same_eq_true_iff left right).mp same)
  else isFalse fun equal => same ((Ty.same_eq_true_iff left right).mpr equal)

instance AtomicTy.instDecidableEq : DecidableEq AtomicTy := inferInstance

/-! ## Computed translation -/

/-- The typed variable at a de Bruijn index. -/
def varOfIndex : (Γ : HOL.Ctx AtomicTy) → Nat → Option (Σ τ : HOL.Ty AtomicTy, HOL.Var Γ τ)
  | [], _ => none
  | τ :: _, 0 => some ⟨τ, .vz⟩
  | _ :: Γ, index + 1 => (varOfIndex Γ index).map fun found => ⟨found.1, .vs found.2⟩

theorem varOfIndex_deBruijnIndex {Γ : HOL.Ctx AtomicTy} {τ : HOL.Ty AtomicTy}
    (x : HOL.Var Γ τ) : varOfIndex Γ (deBruijnIndex x) = some ⟨τ, x⟩ := by
  induction x with
  | vz => rfl
  | vs x ih => simp [varOfIndex, deBruijnIndex, ih]

theorem varOfIndex_sound : ∀ {Γ : HOL.Ctx AtomicTy} {index : Nat}
    {found : Σ τ : HOL.Ty AtomicTy, HOL.Var Γ τ},
    varOfIndex Γ index = some found → deBruijnIndex found.2 = index
  | [], _, _, h => by simp [varOfIndex] at h
  | _ :: _, 0, found, h => by
      simp only [varOfIndex, Option.some.injEq] at h
      subst h
      rfl
  | _ :: Γ, index + 1, found, h => by
      simp only [varOfIndex, Option.map_eq_some_iff] at h
      obtain ⟨inner, innerFound, rfl⟩ := h
      simp [deBruijnIndex, varOfIndex_sound innerFound]

/-- Apply a translated function to a translated argument when the types fit. -/
def applyTranslated {Γ : HOL.Ctx AtomicTy} :
    (functionType : HOL.Ty AtomicTy) → HOL.Term Symbol Γ functionType →
      (argumentType : HOL.Ty AtomicTy) → HOL.Term Symbol Γ argumentType →
        Option (Σ τ : HOL.Ty AtomicTy, HOL.Term Symbol Γ τ)
  | .arr domain codomain, function, argumentType, argument =>
      if same : argumentType = domain then some ⟨codomain, .app function (same ▸ argument)⟩
      else none
  | _, _, _, _ => none

/-- **The compositional translation, computed.** -/
def translate? : (Γ : HOL.Ctx AtomicTy) → DBTerm → Option (Σ τ : HOL.Ty AtomicTy, HOL.Term Symbol Γ τ)
  | _, .const constant annotation =>
      match equalityOperand? constant annotation with
      | some operand => some ⟨_, equalityLambda operand.toHOL⟩
      | none => some ⟨annotation.toHOL, .const (.constant constant annotation rfl)⟩
  | _, .free sourceVar => some ⟨sourceVar.ty.toHOL, .const (.variable sourceVar rfl)⟩
  | Γ, .bound index => (varOfIndex Γ index).map fun found => ⟨found.1, .var found.2⟩
  | Γ, .app function argument => do
      let ⟨functionType, function'⟩ ← translate? Γ function
      let ⟨argumentType, argument'⟩ ← translate? Γ argument
      applyTranslated functionType function' argumentType argument'
  | Γ, .abs domain body => do
      let ⟨bodyType, body'⟩ ← translate? (domain.toHOL :: Γ) body
      some ⟨.arr domain.toHOL bodyType, .lam body'⟩

theorem applyTranslated_sound {Γ : HOL.Ctx AtomicTy} {functionType argumentType : HOL.Ty AtomicTy}
    {function : HOL.Term Symbol Γ functionType} {argument : HOL.Term Symbol Γ argumentType}
    {result : Σ τ : HOL.Ty AtomicTy, HOL.Term Symbol Γ τ}
    (applied : applyTranslated functionType function argumentType argument = some result) :
    ∃ codomain, ∃ same : functionType = .arr argumentType codomain,
      result = ⟨codomain, .app (same ▸ function) argument⟩ := by
  cases functionType with
  | arr domain codomain =>
      simp only [applyTranslated] at applied
      split at applied
      · rename_i same
        subst same
        simp only [Option.some.injEq] at applied
        exact ⟨codomain, rfl, applied.symm⟩
      · simp at applied
  | _ => simp [applyTranslated] at applied

/-- **The computed translation is sound.** -/
theorem translate?_sound : ∀ {Γ : HOL.Ctx AtomicTy} {term : DBTerm}
    {result : Σ τ : HOL.Ty AtomicTy, HOL.Term Symbol Γ τ},
    translate? Γ term = some result → TranslatesCompositionally Γ term result.1 result.2
  | _, .const constant annotation, result, h => by
      simp only [translate?] at h
      split at h
      · rename_i operand recognized
        simp only [Option.some.injEq] at h
        subst h
        exact .equality recognized rfl
      · rename_i unrecognized
        simp only [Option.some.injEq] at h
        subst h
        exact .constant unrecognized rfl
  | _, .free sourceVar, result, h => by
      simp only [translate?, Option.some.injEq] at h
      subst h
      exact .free rfl
  | Γ, .bound index, result, h => by
      simp only [translate?, Option.map_eq_some_iff] at h
      obtain ⟨found, foundIndex, rfl⟩ := h
      rw [← varOfIndex_sound foundIndex]
      exact .bound found.2
  | Γ, .app function argument, result, h => by
      simp only [translate?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨functionType, function'⟩, functionFound, ⟨argumentType, argument'⟩,
        argumentFound, applied⟩ := h
      have shape := applyTranslated_sound applied
      clear applied
      obtain ⟨codomain, same, rfl⟩ := shape
      have functionTranslated := translate?_sound functionFound
      have argumentTranslated := translate?_sound argumentFound
      change functionType = .arr argumentType codomain at same
      change TranslatesCompositionally Γ function functionType function' at functionTranslated
      change TranslatesCompositionally Γ argument argumentType argument' at argumentTranslated
      subst same
      exact .app functionTranslated argumentTranslated
  | Γ, .abs domain body, result, h => by
      simp only [translate?, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨⟨bodyType, body'⟩, bodyFound, rfl⟩ := h
      exact .abs rfl (translate?_sound bodyFound)

/-- **The computed translation is complete.** -/
theorem translate?_complete {Γ : HOL.Ctx AtomicTy} {term : DBTerm} {τ : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol Γ τ} (translation : TranslatesCompositionally Γ term τ target) :
    translate? Γ term = some ⟨τ, target⟩ := by
  induction translation with
  | equality recognized typed =>
      subst typed
      simp [translate?, recognized]
  | constant unrecognized typed =>
      subst typed
      simp [translate?, unrecognized]
  | free typed =>
      subst typed
      rfl
  | bound x => simp [translate?, varOfIndex_deBruijnIndex]
  | app _ _ functionIh argumentIh =>
      simp [translate?, functionIh, argumentIh, applyTranslated]
  | abs typed _ ih =>
      subst typed
      simp [translate?, ih]

theorem translate?_eq_some_iff {Γ : HOL.Ctx AtomicTy} {term : DBTerm} {τ : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol Γ τ} :
    translate? Γ term = some ⟨τ, target⟩ ↔ TranslatesCompositionally Γ term τ target :=
  ⟨fun found => translate?_sound found, translate?_complete⟩

/-! ## Decidable symbols -/

instance Const.instDecidableEqSame : DecidableEq Const := fun left right =>
  if same : Const.same left right = true then isTrue ((Const.same_eq_true_iff left right).mp same)
  else isFalse fun equal => same ((Const.same_eq_true_iff left right).mpr equal)

instance SourceVar.instDecidableEqSame : DecidableEq SourceVar := fun left right =>
  if same : sourceVarSame left right = true then
    isTrue ((sourceVarSame_eq_true_iff left right).mp same)
  else isFalse fun equal => same ((sourceVarSame_eq_true_iff left right).mpr equal)

instance Symbol.instDecidableEq (τ : HOL.Ty AtomicTy) : DecidableEq (Symbol τ)
  | .constant name annotation _, .constant name' annotation' _ =>
      if same : name = name' ∧ annotation = annotation' then
        isTrue (by obtain ⟨rfl, rfl⟩ := same; rfl)
      else isFalse (by intro equal; cases equal; exact same ⟨rfl, rfl⟩)
  | .variable source _, .variable source' _ =>
      if same : source = source' then isTrue (by subst same; rfl)
      else isFalse (by intro equal; cases equal; exact same rfl)
  | .constant .., .variable .. => isFalse (by intro equal; cases equal)
  | .variable .., .constant .. => isFalse (by intro equal; cases equal)

end Mettapedia.Languages.OpenTheory

namespace Mettapedia.Logic.HOL.ProofSyntax

/-- Transport assumptions into any list that contains each of them. -/
def OccurrenceMap.ofMem {α : Type*} [DecidableEq α] {source target : List α}
    (contained : ∀ value ∈ source, value ∈ target) : OccurrenceMap source target where
  index position := ⟨target.idxOf (source.get position),
    List.idxOf_lt_length_of_mem (contained _ (List.get_mem source position))⟩
  get_eq position := by simp

end Mettapedia.Logic.HOL.ProofSyntax

namespace Mettapedia.Languages.OpenTheory

open Mettapedia.Logic

/-! ## Equations of the compositional translation -/

section Equations

variable {Γ : HOL.Ctx AtomicTy} {Δ : List (HOL.Formula Symbol Γ)}

/-- The eta-expanded equality applied to two arguments is their equation. -/
def equalityLambdaProof (Δ : List (HOL.Formula Symbol Γ)) {σ : HOL.Ty AtomicTy}
    (left right : HOL.Term Symbol Γ σ) :
    HOL.ProofSyntax Symbol Δ (.eq (.app (.app (equalityLambda σ) left) right) (.eq left right)) :=
  .eqTrans (.eqApp right (.beta left (.lam (.eq (.var (.vs .vz)) (.var .vz)))))
    ((congrArg (fun conclusion => HOL.ProofSyntax Symbol Δ
        (.eq (.app (.lam (.eq (HOL.weaken (σ := σ) left) (.var .vz))) right) conclusion))
      (show HOL.Term.eq (HOL.instantiate right (HOL.weaken (σ := σ) left)) right =
          HOL.Term.eq left right by rw [HOL.instantiate_weaken])).mp
      (.beta right (.eq (HOL.weaken (σ := σ) left) (.var .vz))))

/-- Read the equation out of an applied eta-expanded equality. -/
def toEquation {σ : HOL.Ty AtomicTy} {left right : HOL.Term Symbol Γ σ}
    (proof : HOL.ProofSyntax Symbol Δ (.app (.app (equalityLambda σ) left) right)) :
    HOL.ProofSyntax Symbol Δ (.eq left right) :=
  .impE (.eqPropEL (equalityLambdaProof Δ left right)) proof

/-- Write an equation as an applied eta-expanded equality. -/
def ofEquation {σ : HOL.Ty AtomicTy} {left right : HOL.Term Symbol Γ σ}
    (proof : HOL.ProofSyntax Symbol Δ (.eq left right)) :
    HOL.ProofSyntax Symbol Δ (.app (.app (equalityLambda σ) left) right) :=
  .impE (.eqPropER (equalityLambdaProof Δ left right)) proof

/-- The two sides of an applied eta-expanded equality, if the formula is one. -/
def equationView? : HOL.Formula Symbol Γ → Option (Σ σ : HOL.Ty AtomicTy, HOL.Term Symbol Γ σ × HOL.Term Symbol Γ σ)
  | @HOL.Term.app _ _ _ σ₂ _ (@HOL.Term.app _ _ _ σ₁ _ head left) right =>
      if same : σ₂ = σ₁ then
        if (HOL.Term.app (HOL.Term.app head left) right : HOL.Formula Symbol Γ) =
            .app (.app (equalityLambda σ₁) left) (same ▸ right) then
          some ⟨σ₁, left, same ▸ right⟩
        else none
      else none
  | _ => none

theorem equationView?_equalityLambda {σ : HOL.Ty AtomicTy} (left right : HOL.Term Symbol Γ σ) :
    equationView? (.app (.app (equalityLambda σ) left) right) = some ⟨σ, left, right⟩ := by
  simp [equationView?]

theorem equationView?_sound {formula : HOL.Formula Symbol Γ}
    {view : Σ σ : HOL.Ty AtomicTy, HOL.Term Symbol Γ σ × HOL.Term Symbol Γ σ}
    (found : equationView? formula = some view) :
    formula = .app (.app (equalityLambda view.1) view.2.1) view.2.2 := by
  unfold equationView? at found
  split at found
  · rename_i σ₂ σ₁ head left right
    split at found
    · rename_i same
      split at found
      · rename_i isEquality
        simp only [Option.some.injEq] at found
        subst found
        exact isEquality
      · cases found
    · cases found
  · cases found

end Equations

end Mettapedia.Languages.OpenTheory

namespace Mettapedia.Languages.HOLLight.RetainedElaboration

open Mettapedia.Languages.OpenTheory Mettapedia.Logic
open Mettapedia.Logic.HOL.ProofSyntax (OccurrenceMap)

/-- The structural equality of terms, which is computable. -/
local instance (priority := high) termDecidableEq {Γ : HOL.Ctx AtomicTy} {τ : HOL.Ty AtomicTy} :
    DecidableEq (HOL.Term Symbol Γ τ) :=
  Mettapedia.Logic.HOL.Term.instDecidableEq

/-! ## Retained sequents -/

/-- A retained natural-deduction proof of a closed sequent. -/
structure Retained where
  hypotheses : List (HOL.ClosedFormula Symbol)
  conclusion : HOL.ClosedFormula Symbol
  proof : HOL.ProofSyntax Symbol hypotheses conclusion

/-- A retained proof is correct for a theorem when it concludes the theorem's
translated conclusion from translated hypotheses of the theorem. -/
def Correct (out : Theorem) (retained : Retained) : Prop :=
  TranslatesCompositionally [] out.sequent.concl.term .prop retained.conclusion ∧
    ∀ ψ ∈ retained.hypotheses, ψ ∈ compositionalHypotheses out.sequent.hyp

/-- The translation of a closed term at the proposition type. -/
def translateFormula (term : DBTerm) : Option (HOL.ClosedFormula Symbol) :=
  match translate? [] term with
  | some ⟨.prop, formula⟩ => some formula
  | _ => none

theorem translateFormula_eq_some_iff {term : DBTerm} {formula : HOL.ClosedFormula Symbol} :
    translateFormula term = some formula ↔ TranslatesCompositionally [] term .prop formula := by
  rw [← translate?_eq_some_iff]
  unfold translateFormula
  split
  · rename_i found
    rw [found]
    simp
  · rename_i notProp
    constructor
    · intro impossible; cases impossible
    · intro found
      exact absurd found (notProp formula)

/-- Weaken into the left part of an appended assumption list. -/
def leftOf {Δ : List (HOL.ClosedFormula Symbol)} {φ : HOL.ClosedFormula Symbol}
    (proof : HOL.ProofSyntax Symbol Δ φ) (Δ' : List (HOL.ClosedFormula Symbol)) :
    HOL.ProofSyntax Symbol (Δ ++ Δ') φ :=
  HOL.ProofSyntax.mono (OccurrenceMap.ofMem fun _ member => List.mem_append_left _ member) proof

/-- Weaken into the right part of an appended assumption list. -/
def rightOf {Δ' : List (HOL.ClosedFormula Symbol)} {φ : HOL.ClosedFormula Symbol}
    (Δ : List (HOL.ClosedFormula Symbol)) (proof : HOL.ProofSyntax Symbol Δ' φ) :
    HOL.ProofSyntax Symbol (Δ ++ Δ') φ :=
  HOL.ProofSyntax.mono (OccurrenceMap.ofMem fun _ member => List.mem_append_right _ member) proof

/-- An equation with its proof. -/
abbrev EquationProof (Δ : List (HOL.ClosedFormula Symbol)) : Type :=
  Σ σ : HOL.Ty AtomicTy, Σ left : HOL.ClosedTerm Symbol σ, Σ right : HOL.ClosedTerm Symbol σ,
    HOL.ProofSyntax Symbol Δ (.eq left right)

/-- Read a retained proof of an applied eta-expanded equality as an equation. -/
def asEquation (retained : Retained) : Option (EquationProof retained.hypotheses) :=
  match found : equationView? retained.conclusion with
  | some view => some ⟨view.1, view.2.1, view.2.2,
      toEquation ((equationView?_sound found) ▸ retained.proof)⟩
  | none => none

theorem asEquation_of_conclusion {retained : Retained} {σ : HOL.Ty AtomicTy}
    {left right : HOL.ClosedTerm Symbol σ}
    (shape : retained.conclusion = .app (.app (equalityLambda σ) left) right) :
    ∃ proof, asEquation retained = some ⟨σ, left, right, proof⟩ := by
  obtain ⟨hypotheses, conclusion, proof⟩ := retained
  simp only at shape
  subst shape
  unfold asEquation
  split
  · rename_i view found
    rw [equationView?_equalityLambda] at found
    cases found
    exact ⟨_, rfl⟩
  · rename_i notFound
    rw [equationView?_equalityLambda] at notFound
    cases notFound

/-- A retained equation. -/
def ofEquationProof {Δ : List (HOL.ClosedFormula Symbol)} (equation : EquationProof Δ) : Retained :=
  ⟨Δ, .app (.app (equalityLambda equation.1) equation.2.1) equation.2.2.1,
    ofEquation equation.2.2.2⟩

/-- Transport an equation along an equality of types. -/
def castEquation {Δ : List (HOL.ClosedFormula Symbol)} {σ σ' : HOL.Ty AtomicTy} (same : σ = σ')
    {left right : HOL.ClosedTerm Symbol σ} (proof : HOL.ProofSyntax Symbol Δ (.eq left right)) :
    HOL.ProofSyntax Symbol Δ (.eq (same ▸ left) (same ▸ right)) := by
  subst same
  exact proof

/-! ## Rules without premises -/

/-- `ASSUME t`: `t ⊢ t`. -/
def elabAssume (term : CanonicalTerm) : Option Retained := do
  let formula ← translateFormula term.term
  pure ⟨[formula], formula, .hyp ⟨0, by simp⟩⟩

/-- A one-step conversion between two terms: reflexivity, or the beta
contraction of a redex. -/
def conversion? {σ : HOL.Ty AtomicTy} (left right : HOL.ClosedTerm Symbol σ) :
    Option (HOL.ProofSyntax Symbol [] (.eq left right)) :=
  if same : left = right then some (same ▸ .eqRefl left)
  else
    match left with
    | .app (.lam body) argument =>
        if contracted : HOL.instantiate argument body = right then
          some (contracted ▸ .beta argument body)
        else none
    | _ => none

/-- `REFL t` and `BETA`: the equation of a term with itself or with its
contractum. -/
def elabConversion (equation : DBTerm) : Option Retained := do
  let formula ← translateFormula equation
  match equationView? formula with
  | some ⟨_, left, right⟩ =>
      let proof ← conversion? left right
      pure (ofEquationProof ⟨_, left, right, proof⟩)
  | none => none

/-! ## Rules with premises -/

/-- `TRANS`. -/
def elabTrans (first second : Retained) : Option Retained := do
  let ⟨σ, left, middle, firstProof⟩ ← asEquation first
  let ⟨σ', middle', right, secondProof⟩ ← asEquation second
  if same : σ' = σ then
    if middles : same ▸ middle' = middle then
      pure (ofEquationProof ⟨σ, left, same ▸ right,
        .eqTrans (leftOf firstProof _) (rightOf _ (middles ▸ castEquation same secondProof))⟩)
    else none
  else none

/-- Combine an equation of functions and an equation of arguments. -/
def applyEquations {Δ Δ' : List (HOL.ClosedFormula Symbol)} :
    (functionType : HOL.Ty AtomicTy) → (function function' : HOL.ClosedTerm Symbol functionType) →
      HOL.ProofSyntax Symbol Δ (.eq function function') →
      (argumentType : HOL.Ty AtomicTy) → (argument argument' : HOL.ClosedTerm Symbol argumentType) →
      HOL.ProofSyntax Symbol Δ' (.eq argument argument') → Option Retained
  | .arr domain codomain, function, function', functionProof, argumentType, argument, argument',
      argumentProof =>
      if same : argumentType = domain then
        some (ofEquationProof ⟨codomain, .app function (same ▸ argument),
          .app function' (same ▸ argument'),
          .eqTrans (.eqApp (same ▸ argument) (leftOf functionProof _))
            (.eqAppArg function' (rightOf _ (castEquation same argumentProof)))⟩)
      else none
  | _, _, _, _, _, _, _, _ => none

/-- `MK_COMB`. -/
def elabMkComb (functions arguments : Retained) : Option Retained := do
  let ⟨functionType, function, function', functionProof⟩ ← asEquation functions
  let ⟨argumentType, argument, argument', argumentProof⟩ ← asEquation arguments
  applyEquations functionType function function' functionProof argumentType argument argument'
    argumentProof

/-- Use an equation of propositions to move a premise. -/
def moveAlong {Δ : List (HOL.ClosedFormula Symbol)} (premise : Retained) :
    (σ : HOL.Ty AtomicTy) → (left right : HOL.ClosedTerm Symbol σ) →
      HOL.ProofSyntax Symbol Δ (.eq left right) → Option Retained
  | .prop, left, right, equationProof =>
      if same : premise.conclusion = left then
        some ⟨Δ ++ premise.hypotheses, right,
          .impE (.eqPropEL (leftOf equationProof _)) (rightOf _ (same ▸ premise.proof))⟩
      else none
  | _, _, _, _ => none

/-- `EQ_MP`. -/
def elabEqMp (equation premise : Retained) : Option Retained := do
  let ⟨σ, left, right, equationProof⟩ ← asEquation equation
  moveAlong premise σ left right equationProof

/-- Discharge every occurrence of one assumption. -/
def discharge {Δ : List (HOL.ClosedFormula Symbol)} {ψ : HOL.ClosedFormula Symbol}
    (assumption : HOL.ClosedFormula Symbol) (proof : HOL.ProofSyntax Symbol Δ ψ) :
    HOL.ProofSyntax Symbol (Δ.filter (· ≠ assumption)) (.imp assumption ψ) :=
  .impI (HOL.ProofSyntax.mono (OccurrenceMap.ofMem fun value member => by
    by_cases same : value = assumption
    · subst same; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨member, by simpa using same⟩)) proof)

/-- `DEDUCT_ANTISYM_RULE`. -/
def elabDeductAntisym (first second : Retained) : Option Retained :=
  some ⟨first.hypotheses.filter (· ≠ second.conclusion) ++
      second.hypotheses.filter (· ≠ first.conclusion),
    .app (.app (equalityLambda .prop) first.conclusion) second.conclusion,
    ofEquation (.eqPropI (rightOf _ (discharge first.conclusion second.proof))
      (leftOf (discharge second.conclusion first.proof) _))⟩

/-! ## Abstracting a free variable -/

section Abstraction

variable {Γ : HOL.Ctx AtomicTy}

/-- Replace the symbol of a free variable by a new bound variable at depth
`Ξ`, computably. -/
def abstractSymbol (variable_ : SourceVar) :
    (Ξ : HOL.Ctx AtomicTy) → {τ : HOL.Ty AtomicTy} → HOL.Term Symbol (Ξ ++ Γ) τ →
      HOL.Term Symbol (Ξ ++ variable_.ty.toHOL :: Γ) τ
  | Ξ, _, .var index => .var (HOL.insertRen Ξ index)
  | Ξ, _, .const symbol =>
      if same : (⟨_, symbol⟩ : Σ τ, Symbol τ) = ⟨_, Symbol.ofVar variable_⟩ then
        cast (congrArg (HOL.Term Symbol (Ξ ++ variable_.ty.toHOL :: Γ))
          (congrArg Sigma.fst same).symm) (.var (HOL.varAtDepth Ξ))
      else .const symbol
  | Ξ, _, .app function argument => .app (abstractSymbol variable_ Ξ function)
      (abstractSymbol variable_ Ξ argument)
  | Ξ, _, .lam body => .lam (abstractSymbol variable_ (_ :: Ξ) body)
  | _, _, .top => .top
  | _, _, .bot => .bot
  | Ξ, _, .and left right => .and (abstractSymbol variable_ Ξ left) (abstractSymbol variable_ Ξ right)
  | Ξ, _, .or left right => .or (abstractSymbol variable_ Ξ left) (abstractSymbol variable_ Ξ right)
  | Ξ, _, .imp left right => .imp (abstractSymbol variable_ Ξ left) (abstractSymbol variable_ Ξ right)
  | Ξ, _, .not operand => .not (abstractSymbol variable_ Ξ operand)
  | Ξ, _, .eq left right => .eq (abstractSymbol variable_ Ξ left) (abstractSymbol variable_ Ξ right)
  | Ξ, _, .all body => .all (abstractSymbol variable_ (_ :: Ξ) body)
  | Ξ, _, .ex body => .ex (abstractSymbol variable_ (_ :: Ξ) body)

/-- The computed abstraction is the existing one. -/
theorem abstractSymbol_eq (variable_ : SourceVar) :
    ∀ (Ξ : HOL.Ctx AtomicTy) {τ : HOL.Ty AtomicTy} (term : HOL.Term Symbol (Ξ ++ Γ) τ),
      abstractSymbol variable_ Ξ term = HOL.abstractConstAt (Symbol.ofVar variable_) Ξ term
  | Ξ, _, .var index => by rw [abstractSymbol, HOL.abstractConstAt]
  | Ξ, _, .const symbol => by
      rw [abstractSymbol, HOL.abstractConstAt]
      by_cases same : (⟨_, symbol⟩ : Σ τ, Symbol τ) = ⟨_, Symbol.ofVar variable_⟩
      · rw [dif_pos same, dif_pos same]
      · rw [dif_neg same, dif_neg same]
  | Ξ, _, .app function argument => by
      rw [abstractSymbol, HOL.abstractConstAt, abstractSymbol_eq variable_ Ξ function,
        abstractSymbol_eq variable_ Ξ argument]
  | Ξ, _, .lam body => by
      rw [abstractSymbol, HOL.abstractConstAt, abstractSymbol_eq variable_ (_ :: Ξ) body]
  | _, _, .top => by rw [abstractSymbol, HOL.abstractConstAt]
  | _, _, .bot => by rw [abstractSymbol, HOL.abstractConstAt]
  | Ξ, _, .and left right => by
      rw [abstractSymbol, HOL.abstractConstAt, abstractSymbol_eq variable_ Ξ left, abstractSymbol_eq variable_ Ξ right]
  | Ξ, _, .or left right => by
      rw [abstractSymbol, HOL.abstractConstAt, abstractSymbol_eq variable_ Ξ left, abstractSymbol_eq variable_ Ξ right]
  | Ξ, _, .imp left right => by
      rw [abstractSymbol, HOL.abstractConstAt, abstractSymbol_eq variable_ Ξ left, abstractSymbol_eq variable_ Ξ right]
  | Ξ, _, .not operand => by
      rw [abstractSymbol, HOL.abstractConstAt, abstractSymbol_eq variable_ Ξ operand]
  | Ξ, _, .eq left right => by
      rw [abstractSymbol, HOL.abstractConstAt, abstractSymbol_eq variable_ Ξ left, abstractSymbol_eq variable_ Ξ right]
  | Ξ, _, .all body => by
      rw [abstractSymbol, HOL.abstractConstAt, abstractSymbol_eq variable_ (_ :: Ξ) body]
  | Ξ, _, .ex body => by
      rw [abstractSymbol, HOL.abstractConstAt, abstractSymbol_eq variable_ (_ :: Ξ) body]

theorem abstractSymbol_instantiate (variable_ : SourceVar) (Ξ : HOL.Ctx AtomicTy) {σ τ : HOL.Ty AtomicTy}
    (argument : HOL.Term Symbol (Ξ ++ Γ) σ) (body : HOL.Term Symbol ((σ :: Ξ) ++ Γ) τ) :
    abstractSymbol variable_ Ξ (HOL.instantiate argument body) =
      HOL.instantiate (abstractSymbol variable_ Ξ argument) (abstractSymbol variable_ (σ :: Ξ) body) := by
  rw [abstractSymbol_eq, abstractSymbol_eq, abstractSymbol_eq, HOL.abstractConstAt_instantiate]

theorem abstractSymbol_weaken (variable_ : SourceVar) (Ξ : HOL.Ctx AtomicTy) {ρ τ : HOL.Ty AtomicTy}
    (term : HOL.Term Symbol (Ξ ++ Γ) τ) :
    abstractSymbol variable_ (ρ :: Ξ) (HOL.weaken (σ := ρ) term) =
      HOL.weaken (σ := ρ) (abstractSymbol variable_ Ξ term) := by
  rw [abstractSymbol_eq, abstractSymbol_eq, HOL.abstractConstAt_weaken]

theorem abstractSymbol_weakenHyps (variable_ : SourceVar) (Ξ : HOL.Ctx AtomicTy) {σ : HOL.Ty AtomicTy}
    (Δ : List (HOL.Formula Symbol (Ξ ++ Γ))) :
    (HOL.weakenHyps (σ := σ) Δ).map (abstractSymbol variable_ (σ :: Ξ)) =
      HOL.weakenHyps (σ := σ) (Δ.map (abstractSymbol variable_ Ξ)) := by
  simp only [HOL.weakenHyps, List.map_map, Function.comp_def, abstractSymbol_weaken]

/-- Transport a proof along an unfolding of the abstraction. -/
local macro "unfolded" proof:term : term =>
  `(HOL.ProofSyntax.castIndices rfl (by simp only [abstractSymbol]) $proof)

/-- **Abstraction of a free variable in a retained proof.** Every rule and
every hypothesis occurrence is kept; the variable's symbol becomes a bound
variable throughout. -/
def abstractProof (variable_ : SourceVar) {Ξ : HOL.Ctx AtomicTy}
    {Δ : List (HOL.Formula Symbol (Ξ ++ Γ))} {φ : HOL.Formula Symbol (Ξ ++ Γ)} :
    HOL.ProofSyntax Symbol Δ φ →
      HOL.ProofSyntax Symbol (Δ.map (abstractSymbol variable_ Ξ)) (abstractSymbol variable_ Ξ φ)
  | .hyp occurrence => HOL.ProofSyntax.castIndices rfl (by simp)
      (HOL.ProofSyntax.hyp (Δ := Δ.map (abstractSymbol variable_ Ξ)) (occurrence.cast (by simp)))
  | .topI => unfolded .topI
  | .botE proof => .botE (unfolded (abstractProof variable_ proof))
  | .andI left right => unfolded (.andI (abstractProof variable_ left) (abstractProof variable_ right))
  | .andEL (ψ := ψ) proof => .andEL (ψ := abstractSymbol variable_ Ξ ψ) (unfolded (abstractProof variable_ proof))
  | .andER (φ := φ) proof => .andER (φ := abstractSymbol variable_ Ξ φ) (unfolded (abstractProof variable_ proof))
  | .orIL (ψ := ψ) proof => unfolded (.orIL (ψ := abstractSymbol variable_ Ξ ψ) (abstractProof variable_ proof))
  | .orIR (φ := φ) proof => unfolded (.orIR (φ := abstractSymbol variable_ Ξ φ) (abstractProof variable_ proof))
  | .orE (φ := φ) (ψ := ψ) cases left right => .orE (φ := abstractSymbol variable_ Ξ φ) (ψ := abstractSymbol variable_ Ξ ψ)
      (unfolded (abstractProof variable_ cases))
      (abstractProof variable_ left) (abstractProof variable_ right)
  | .impI proof => unfolded (.impI (abstractProof variable_ proof))
  | .impE (φ := φ) function argument => .impE (φ := abstractSymbol variable_ Ξ φ)
      (unfolded (abstractProof variable_ function))
      (abstractProof variable_ argument)
  | .notI proof => unfolded (.notI (unfolded (abstractProof variable_ proof)))
  | .notE (φ := φ) negative positive => unfolded (.notE (φ := abstractSymbol variable_ Ξ φ)
      (unfolded (abstractProof variable_ negative))
      (abstractProof variable_ positive))
  | .allI proof => unfolded (.allI (HOL.ProofSyntax.castIndices
      (abstractSymbol_weakenHyps variable_ Ξ _) rfl (abstractProof variable_ (Ξ := _ :: Ξ) proof)))
  | .allE term proof => HOL.ProofSyntax.castIndices rfl
      (abstractSymbol_instantiate variable_ Ξ term _).symm
      (.allE (abstractSymbol variable_ Ξ term) (unfolded (abstractProof variable_ proof)))
  | .exI term proof => unfolded (.exI (abstractSymbol variable_ Ξ term)
      (HOL.ProofSyntax.castIndices rfl (abstractSymbol_instantiate variable_ Ξ term _)
        (abstractProof variable_ proof)))
  | .exE (φ := φ) existsProof body => .exE (φ := abstractSymbol variable_ (_ :: Ξ) φ)
      (unfolded (abstractProof variable_ existsProof))
      (HOL.ProofSyntax.castIndices
        (by rw [List.map_cons, abstractSymbol_weakenHyps])
        (abstractSymbol_weaken variable_ Ξ _)
        (abstractProof variable_ (Ξ := _ :: Ξ) body))
  | .eqRefl term => unfolded (.eqRefl (abstractSymbol variable_ Ξ term))
  | .eqSymm (t := t) (u := u) proof => unfolded (.eqSymm (t := abstractSymbol variable_ Ξ t) (u := abstractSymbol variable_ Ξ u)
      (unfolded (abstractProof variable_ proof)))
  | .eqTrans (t := t) (u := u) (v := v) left right =>
      unfolded (.eqTrans (t := abstractSymbol variable_ Ξ t) (u := abstractSymbol variable_ Ξ u) (v := abstractSymbol variable_ Ξ v)
      (unfolded (abstractProof variable_ left))
      (unfolded (abstractProof variable_ right)))
  | .eqPropI (p := p) (q := q) forward backward => unfolded (.eqPropI (p := abstractSymbol variable_ Ξ p) (q := abstractSymbol variable_ Ξ q)
      (unfolded (abstractProof variable_ forward))
      (unfolded (abstractProof variable_ backward)))
  | .eqPropEL (p := p) (q := q) proof => unfolded (.eqPropEL (p := abstractSymbol variable_ Ξ p) (q := abstractSymbol variable_ Ξ q)
      (unfolded (abstractProof variable_ proof)))
  | .eqPropER (p := p) (q := q) proof => unfolded (.eqPropER (p := abstractSymbol variable_ Ξ p) (q := abstractSymbol variable_ Ξ q)
      (unfolded (abstractProof variable_ proof)))
  | .eqApp (f := f) (g := g) term proof => unfolded (.eqApp (f := abstractSymbol variable_ Ξ f) (g := abstractSymbol variable_ Ξ g)
      (abstractSymbol variable_ Ξ term)
      (unfolded (abstractProof variable_ proof)))
  | .eqAppArg (t := t) (u := u) function proof => unfolded (.eqAppArg (t := abstractSymbol variable_ Ξ t) (u := abstractSymbol variable_ Ξ u)
      (abstractSymbol variable_ Ξ function)
      (unfolded (abstractProof variable_ proof)))
  | .eqLam (t := t) (u := u) proof => unfolded (.eqLam (t := abstractSymbol variable_ (_ :: Ξ) t)
      (u := abstractSymbol variable_ (_ :: Ξ) u) (HOL.ProofSyntax.castIndices
      (abstractSymbol_weakenHyps variable_ Ξ _) (by simp only [abstractSymbol])
      (abstractProof variable_ (Ξ := _ :: Ξ) proof)))
  | .funExt (f := f) (g := g) proof => unfolded (.funExt (f := abstractSymbol variable_ Ξ f) (g := abstractSymbol variable_ Ξ g)
      (HOL.ProofSyntax.castIndices rfl
      (by simp only [abstractSymbol, abstractSymbol_weaken]; rfl) (abstractProof variable_ proof)))
  | .beta term body => HOL.ProofSyntax.castIndices rfl
      (by simp only [abstractSymbol, abstractSymbol_instantiate])
      (.beta (abstractSymbol variable_ Ξ term) (abstractSymbol variable_ (_ :: Ξ) body))
  | .eta function => HOL.ProofSyntax.castIndices rfl
      (by simp only [abstractSymbol, abstractSymbol_weaken]; rfl)
      (.eta (abstractSymbol variable_ Ξ function))

end Abstraction

/-- `ABS x`: abstract a free variable that occurs in no hypothesis. -/
def elabAbs (variable_ : SourceVar) (input : Retained) : Option Retained := do
  let ⟨σ, left, right, proof⟩ ← asEquation input
  if hypotheses : input.hypotheses.map (abstractSymbol (Γ := []) variable_ []) =
      HOL.weakenHyps (σ := variable_.ty.toHOL) input.hypotheses then
    some (ofEquationProof ⟨.arr variable_.ty.toHOL σ,
      .lam (abstractSymbol (Γ := []) variable_ [] left),
      .lam (abstractSymbol (Γ := []) variable_ [] right),
      .eqLam (HOL.ProofSyntax.castIndices hypotheses (by simp only [abstractSymbol])
        (abstractProof (Γ := []) variable_ (Ξ := []) proof))⟩)
  else none

/-! ## Substitution -/

/-- The closed term a substitution puts in place of a symbol, computed. -/
def symbolImage (substitution : TypeCorrectTermSubstitution) {τ : HOL.Ty AtomicTy}
    (symbol : Symbol τ) : HOL.ClosedTerm Symbol τ :=
  match translate? [] (substitution.raw.symbolReplacement symbol) with
  | some ⟨τ', image⟩ => if same : τ' = τ then same ▸ image else .const symbol
  | none => .const symbol

theorem symbolImage_eq (substitution : TypeCorrectTermSubstitution) {τ : HOL.Ty AtomicTy}
    (symbol : Symbol τ) : symbolImage substitution symbol = substitution.symbolImage symbol := by
  have specified := closedTranslation_spec (substitution.raw.symbolReplacement symbol)
    (TermSubst.symbolReplacement_translatable substitution.typeCorrect symbol)
  unfold symbolImage
  rw [translate?_complete specified]
  simp [TypeCorrectTermSubstitution.symbolImage]

/-- The target image of an OpenTheory substitution, computed. -/
def targetMap (substitution : TypeCorrectTermSubstitution) (formula : HOL.ClosedFormula Symbol) :
    HOL.ClosedFormula Symbol :=
  HOL.substConst (symbolImage substitution)
    (HOL.mapTypes substitution.raw.types.baseInstance substitution.raw.types.symbolInstance formula)

theorem targetMap_eq (substitution : TypeCorrectTermSubstitution) (formula : HOL.ClosedFormula Symbol) :
    targetMap substitution formula = substitution.targetMap formula := by
  unfold targetMap TypeCorrectTermSubstitution.targetMap
  congr 1
  funext τ symbol
  exact symbolImage_eq substitution symbol

theorem map_targetMap (substitution : TypeCorrectTermSubstitution) :
    ∀ formulas : List (HOL.ClosedFormula Symbol),
      (formulas.map (HOL.mapTypes substitution.raw.types.baseInstance
          substitution.raw.types.symbolInstance)).map (HOL.substConst (symbolImage substitution)) =
        formulas.map (targetMap substitution)
  | [] => rfl
  | head :: tail => congrArg (List.cons (targetMap substitution head)) (map_targetMap substitution tail)

/-- `INST` and `INST_TYPE`: retype and replace in the whole retained proof. -/
def elabSubstitution (substitution : TypeCorrectTermSubstitution) (input : Retained) : Retained :=
  ⟨input.hypotheses.map (targetMap substitution), targetMap substitution input.conclusion,
    HOL.ProofSyntax.castIndices (map_targetMap substitution input.hypotheses) rfl
      (HOL.ProofSyntax.substConst (symbolImage substitution)
        (HOL.ProofSyntax.mapTypes substitution.raw.types.baseInstance
          substitution.raw.types.symbolInstance input.proof))⟩

/-! ## Correctness of the rule elaborators -/

section Correctness

theorem ofEquationProof_conclusion {Δ : List (HOL.ClosedFormula Symbol)} (equation : EquationProof Δ) :
    (ofEquationProof equation).conclusion =
      .app (.app (equalityLambda equation.1) equation.2.1) equation.2.2.1 := rfl

theorem translation_type {term : CanonicalTerm} {σ : HOL.Ty AtomicTy} {target : HOL.ClosedTerm Symbol σ}
    (translation : TranslatesCompositionally [] term.term σ target) : term.ty.toHOL = σ :=
  CanonicalTerm.toHOL_ty_of_translation translation

theorem hypotheses_of_union_left {left right : Finset CanonicalTerm} {ψ : HOL.ClosedFormula Symbol}
    (member : ψ ∈ compositionalHypotheses left) : ψ ∈ compositionalHypotheses (left ∪ right) :=
  compositionalHypotheses_mono Finset.subset_union_left member

theorem hypotheses_of_union_right {left right : Finset CanonicalTerm} {ψ : HOL.ClosedFormula Symbol}
    (member : ψ ∈ compositionalHypotheses right) : ψ ∈ compositionalHypotheses (left ∪ right) :=
  compositionalHypotheses_mono Finset.subset_union_right member

/-- **`ASSUME` elaborates correctly.** -/
theorem elabAssume_correct {term : CanonicalTerm} {out : Theorem} (semantics : AssumeSemantics term out) :
    ∃ retained, elabAssume term = some retained ∧ Correct out retained := by
  obtain ⟨isBool, _, hypotheses, conclusion⟩ := semantics
  obtain ⟨φ, translated⟩ := CanonicalTerm.exists_formula isBool
  refine ⟨⟨[φ], φ, .hyp ⟨0, by simp⟩⟩, by simp [elabAssume, translateFormula_eq_some_iff.mpr translated], ?_, ?_⟩
  · rw [conclusion]; exact translated
  · intro ψ member
    simp only [List.mem_singleton] at member
    subst member
    rw [hypotheses]
    exact ⟨term, Finset.mem_singleton_self _, translated⟩

theorem conversion?_refl {σ : HOL.Ty AtomicTy} (term : HOL.ClosedTerm Symbol σ) :
    ∃ proof, conversion? term term = some proof := by
  simp [conversion?]

theorem conversion?_beta {σ τ : HOL.Ty AtomicTy} (body : HOL.Term Symbol [σ] τ)
    (argument : HOL.ClosedTerm Symbol σ) :
    ∃ proof, conversion? (.app (.lam body) argument) (HOL.instantiate argument body) = some proof := by
  unfold conversion?
  split
  · exact ⟨_, rfl⟩
  · simp

/-- An equation whose translation is an applied eta-expanded equality of two
convertible sides elaborates. -/
theorem elabConversion_correct {out : Theorem} {σ : HOL.Ty AtomicTy} {left right : HOL.ClosedTerm Symbol σ}
    (translated : TranslatesCompositionally [] out.sequent.concl.term .prop
      (.app (.app (equalityLambda σ) left) right))
    (converts : ∃ proof, conversion? left right = some proof) :
    ∃ retained, elabConversion out.sequent.concl.term = some retained ∧ Correct out retained := by
  obtain ⟨proof, found⟩ := converts
  refine ⟨ofEquationProof ⟨σ, left, right, proof⟩, ?_, translated, ?_⟩
  · simp [elabConversion, translateFormula_eq_some_iff.mpr translated, equationView?_equalityLambda, found]
  · intro ψ member
    simp [ofEquationProof] at member

/-- **`REFL` elaborates correctly.** -/
theorem elabRefl_correct {term : CanonicalTerm} {out : Theorem} (semantics : ReflSemantics term out) :
    ∃ retained, elabConversion out.sequent.concl.term = some retained ∧ Correct out retained := by
  obtain ⟨equality, ⟨_, equalityTerm⟩, _, _, conclusion⟩ := semantics
  obtain ⟨target, translated⟩ := term.exists_translation
  have whole := TranslatesCompositionally.equalityDB rfl translated translated
  rw [← equalityTerm, ← conclusion] at whole
  exact elabConversion_correct whole (conversion?_refl target)

/-- **`BETA` elaborates correctly.** -/
theorem elabBeta_correct {source : CheckedSourceTerm} {out : Theorem}
    (semantics : SourceBetaSemantics source out) :
    ∃ retained, elabConversion out.sequent.concl.term = some retained ∧ Correct out retained := by
  obtain ⟨_, reduced, equality, ⟨domain, body, argument, wholeTerm, reducedTerm⟩,
    ⟨_, equalityTerm⟩, _, _, conclusion⟩ := semantics
  obtain ⟨target, translated⟩ := source.canonical.exists_translation
  have redex := translated.of_term_eq wholeTerm
  cases redex with
  | app functionTranslated argumentTranslated =>
      cases functionTranslated with
      | abs typed bodyTranslated =>
          have contracted := TranslatesCompositionally.instantiateAt argumentTranslated
            (Ξ := []) bodyTranslated
          have reducedTranslated := contracted.of_term_eq reducedTerm.symm
          have whole := TranslatesCompositionally.equalityDB rfl translated reducedTranslated
          rw [← equalityTerm, ← conclusion] at whole
          exact elabConversion_correct whole (conversion?_beta _ _)

/-- A correct retained proof of an equation theorem reads as an equation of
the translated sides. -/
theorem equation_of_correct {thm : Theorem} {retained : Retained} (correct : Correct thm retained)
    {left right : CanonicalTerm}
    (view : CanonicalTerm.EqualityViewSemantics thm.sequent.concl left right) :
    ∃ (σ : HOL.Ty AtomicTy) (left' right' : HOL.ClosedTerm Symbol σ) (proof : _),
      left.ty.toHOL = σ ∧ TranslatesCompositionally [] left.term σ left' ∧
        TranslatesCompositionally [] right.term σ right' ∧
        asEquation retained = some ⟨σ, left', right', proof⟩ := by
  obtain ⟨σ, left', right', typed, leftTranslated, rightTranslated, shape⟩ :=
    (correct.1.of_term_eq view.2).equalityDB_inv
  obtain ⟨proof, found⟩ := asEquation_of_conclusion shape
  exact ⟨σ, left', right', proof, typed, leftTranslated, rightTranslated, found⟩

/-- **`TRANS` elaborates correctly.** -/
theorem elabTrans_correct {first second out : Theorem} (semantics : TransSemantics first second out)
    {firstRetained secondRetained : Retained} (firstCorrect : Correct first firstRetained)
    (secondCorrect : Correct second secondRetained) :
    ∃ retained, elabTrans firstRetained secondRetained = some retained ∧ Correct out retained := by
  obtain ⟨start, middle, middle', finish, equality, firstView, secondView, middles,
    ⟨_, equalityTerm⟩, _, hypotheses, conclusion⟩ := semantics
  subst middles
  obtain ⟨σ, start', middleTarget, firstProof, startTyped, startTranslated, middleTranslated,
    firstFound⟩ := equation_of_correct firstCorrect firstView
  obtain ⟨σ', middleTarget', finish', secondProof, _, middleTranslated', finishTranslated,
    secondFound⟩ := equation_of_correct secondCorrect secondView
  obtain ⟨types, middlesSame⟩ := middleTranslated.unique middleTranslated'
  subst types
  cases middlesSame
  refine ⟨ofEquationProof ⟨σ, start', finish',
    .eqTrans (leftOf firstProof _) (rightOf _ (castEquation rfl secondProof))⟩, ?_, ?_, ?_⟩
  · simp [elabTrans, firstFound, secondFound]
  · rw [conclusion, ofEquationProof_conclusion, equalityTerm]
    exact .equalityDB startTyped startTranslated finishTranslated
  · intro ψ member
    rw [hypotheses]
    simp only [ofEquationProof, List.mem_append] at member
    rcases member with inFirst | inSecond
    · exact hypotheses_of_union_left (firstCorrect.2 ψ inFirst)
    · exact hypotheses_of_union_right (secondCorrect.2 ψ inSecond)

/-- **`MK_COMB` elaborates correctly.** -/
theorem elabMkComb_correct {functions arguments out : Theorem}
    (semantics : AppSemantics functions arguments out)
    {functionRetained argumentRetained : Retained}
    (functionCorrect : Correct functions functionRetained)
    (argumentCorrect : Correct arguments argumentRetained) :
    ∃ retained, elabMkComb functionRetained argumentRetained = some retained ∧
      Correct out retained := by
  obtain ⟨functionLeft, functionRight, argumentLeft, argumentRight, applicationLeft,
    applicationRight, equality, functionView, argumentView,
    ⟨domain, codomain, destructed, domainSame, leftTerm⟩, ⟨_, _, _, _, rightTerm⟩,
    ⟨_, equalityTerm⟩, _, hypotheses, conclusion⟩ := semantics
  obtain ⟨σ, function, function', functionProof, functionTyped, functionTranslated,
    functionTranslated', functionFound⟩ := equation_of_correct functionCorrect functionView
  obtain ⟨ρ, argument, argument', argumentProof, argumentTyped, argumentTranslated,
    argumentTranslated', argumentFound⟩ := equation_of_correct argumentCorrect argumentView
  rw [Ty.eq_function_of_destFunction? destructed, Ty.toHOL_function] at functionTyped
  subst functionTyped
  rw [← domainSame] at argumentTyped
  subst argumentTyped
  have leftTranslated : TranslatesCompositionally [] applicationLeft.term codomain.toHOL
      (.app function argument) :=
    (TranslatesCompositionally.app functionTranslated argumentTranslated).of_term_eq leftTerm.symm
  have rightTranslated : TranslatesCompositionally [] applicationRight.term codomain.toHOL
      (.app function' argument') :=
    (TranslatesCompositionally.app functionTranslated' argumentTranslated').of_term_eq rightTerm.symm
  refine ⟨ofEquationProof ⟨codomain.toHOL, .app function argument, .app function' argument',
    .eqTrans (.eqApp argument (leftOf functionProof _))
      (.eqAppArg function' (rightOf _ (castEquation rfl argumentProof)))⟩, ?_, ?_, ?_⟩
  · simp [elabMkComb, functionFound, argumentFound, applyEquations]
  · rw [conclusion, ofEquationProof_conclusion, equalityTerm]
    exact .equalityDB (translation_type leftTranslated) leftTranslated rightTranslated
  · intro ψ member
    rw [hypotheses]
    simp only [ofEquationProof, List.mem_append] at member
    rcases member with inFirst | inSecond
    · exact hypotheses_of_union_left (functionCorrect.2 ψ inFirst)
    · exact hypotheses_of_union_right (argumentCorrect.2 ψ inSecond)

/-- **`EQ_MP` elaborates correctly.** -/
theorem elabEqMp_correct {equation premise out : Theorem}
    (semantics : EqMpSemantics equation premise out)
    {equationRetained premiseRetained : Retained}
    (equationCorrect : Correct equation equationRetained)
    (premiseCorrect : Correct premise premiseRetained) :
    ∃ retained, elabEqMp equationRetained premiseRetained = some retained ∧
      Correct out retained := by
  obtain ⟨left, right, view, matched, _, hypotheses, conclusion⟩ := semantics
  obtain ⟨σ, left', right', proof, _, leftTranslated, rightTranslated, found⟩ :=
    equation_of_correct equationCorrect view
  subst matched
  obtain ⟨types, sides⟩ := premiseCorrect.1.unique leftTranslated
  subst types
  cases sides
  refine ⟨⟨equationRetained.hypotheses ++ premiseRetained.hypotheses, right',
    .impE (.eqPropEL (leftOf proof _)) (rightOf _ premiseRetained.proof)⟩, ?_, ?_, ?_⟩
  · simp [elabEqMp, found, moveAlong]
  · rw [conclusion]
    exact rightTranslated
  · intro ψ member
    rw [hypotheses]
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact hypotheses_of_union_left (equationCorrect.2 ψ inFirst)
    · exact hypotheses_of_union_right (premiseCorrect.2 ψ inSecond)

theorem discharged_member {thm : Theorem} {retained : Retained} (correct : Correct thm retained)
    {other : CanonicalTerm} {otherFormula : HOL.ClosedFormula Symbol}
    (otherTranslated : TranslatesCompositionally [] other.term .prop otherFormula)
    {ψ : HOL.ClosedFormula Symbol} (member : ψ ∈ retained.hypotheses.filter (· ≠ otherFormula)) :
    ψ ∈ compositionalHypotheses (thm.sequent.hyp.erase other) := by
  obtain ⟨present, different⟩ := List.mem_filter.mp member
  obtain ⟨term, termMember, translated⟩ := correct.2 ψ present
  refine ⟨term, Finset.mem_erase.mpr ⟨?_, termMember⟩, translated⟩
  rintro rfl
  exact (by simpa using different : ψ ≠ otherFormula) (translated.unique_eq otherTranslated)

/-- **`DEDUCT_ANTISYM_RULE` elaborates correctly.** -/
theorem elabDeductAntisym_correct {first second out : Theorem}
    (semantics : DeductAntisymSemantics first second out)
    {firstRetained secondRetained : Retained} (firstCorrect : Correct first firstRetained)
    (secondCorrect : Correct second secondRetained) :
    ∃ retained, elabDeductAntisym firstRetained secondRetained = some retained ∧
      Correct out retained := by
  obtain ⟨equality, ⟨_, equalityTerm⟩, _, hypotheses, conclusion⟩ := semantics
  refine ⟨_, rfl, ?_, ?_⟩
  · change TranslatesCompositionally [] out.sequent.concl.term .prop
      (.app (.app (equalityLambda .prop) firstRetained.conclusion) secondRetained.conclusion)
    rw [conclusion, equalityTerm]
    exact .equalityDB (translation_type firstCorrect.1) firstCorrect.1 secondCorrect.1
  · intro ψ member
    rw [hypotheses]
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact hypotheses_of_union_left (discharged_member firstCorrect secondCorrect.1 inFirst)
    · exact hypotheses_of_union_right (discharged_member secondCorrect firstCorrect.1 inSecond)

/-- **`ABS` elaborates correctly.** -/
theorem elabAbs_correct {variable_ : SourceVar} {input out : Theorem}
    (semantics : AbsSemantics variable_ input out) {inputRetained : Retained}
    (inputCorrect : Correct input inputRetained) :
    ∃ retained, elabAbs variable_ inputRetained = some retained ∧ Correct out retained := by
  obtain ⟨fresh, left, right, leftAbs, rightAbs, equality, view, leftAbstraction,
    rightAbstraction, ⟨_, equalityTerm⟩, _, hypotheses, conclusion⟩ := semantics
  obtain ⟨σ, left', right', proof, _, leftTranslated, rightTranslated, found⟩ :=
    equation_of_correct inputCorrect view
  have leftAbsTranslated : TranslatesCompositionally [] leftAbs.term (.arr variable_.ty.toHOL σ)
      (.lam (abstractSymbol (Γ := []) variable_ [] left')) := by
    rw [abstractSymbol_eq]
    exact (TranslatesCompositionally.abs rfl
      (TranslatesCompositionally.closeFreeAt variable_ (Ξ := []) leftTranslated)).of_term_eq
        leftAbstraction.symm
  have rightAbsTranslated : TranslatesCompositionally [] rightAbs.term (.arr variable_.ty.toHOL σ)
      (.lam (abstractSymbol (Γ := []) variable_ [] right')) := by
    rw [abstractSymbol_eq]
    exact (TranslatesCompositionally.abs rfl
      (TranslatesCompositionally.closeFreeAt variable_ (Ξ := []) rightTranslated)).of_term_eq
        rightAbstraction.symm
  have weakened : inputRetained.hypotheses.map (abstractSymbol (Γ := []) variable_ []) =
      HOL.weakenHyps (σ := variable_.ty.toHOL) inputRetained.hypotheses := by
    unfold HOL.weakenHyps
    apply List.map_congr_left
    intro ψ member
    obtain ⟨term, termMember, translated⟩ := inputCorrect.2 ψ member
    rw [abstractSymbol_eq, HOL.abstractConstAt_noOccurrence [] ψ
      (translated.noConstOccurrence variable_ (fun occurs => fresh ⟨term, termMember, occurs⟩))]
    rfl
  refine ⟨ofEquationProof ⟨.arr variable_.ty.toHOL σ,
      .lam (abstractSymbol (Γ := []) variable_ [] left'),
      .lam (abstractSymbol (Γ := []) variable_ [] right'),
      .eqLam (HOL.ProofSyntax.castIndices weakened (by simp only [abstractSymbol])
        (abstractProof (Γ := []) variable_ (Ξ := []) proof))⟩, ?_, ?_, ?_⟩
  · simp only [elabAbs, found, Option.bind_eq_bind, Option.bind_some, dif_pos weakened]
  · rw [conclusion, equalityTerm]
    exact .equalityDB (translation_type leftAbsTranslated) leftAbsTranslated rightAbsTranslated
  · intro ψ member
    rw [hypotheses]
    exact inputCorrect.2 ψ member

/-- **Substitution elaborates correctly.** -/
theorem elabSubstitution_correct {substitution : TypeCorrectTermSubstitution} {input out : Theorem}
    (semantics : TheoremSubstitutionSemantics substitution input out) {inputRetained : Retained}
    (inputCorrect : Correct input inputRetained) :
    Correct out (elabSubstitution substitution inputRetained) := by
  obtain ⟨_, hypothesesMoved, conclusionMoved⟩ := semantics
  have hypotheses := ((applyHypotheses_semantics _ _).unique hypothesesMoved).symm
  constructor
  · change TranslatesCompositionally [] out.sequent.concl.term .prop
      (targetMap substitution inputRetained.conclusion)
    rw [targetMap_eq, conclusionMoved]
    exact inputCorrect.1.applyDB substitution
  · intro ψ' member
    obtain ⟨ψ, ψMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨term, termMember, translated⟩ := inputCorrect.2 ψ ψMember
    rw [hypotheses]
    refine ⟨substitution.apply term, Finset.mem_image_of_mem _ termMember, ?_⟩
    rw [targetMap_eq,
      (apply_eq_iff_termSubstitutionSemantics substitution term _).mp rfl]
    exact translated.applyDB substitution

end Correctness

/-! ## Nodes and graphs -/

open HOLLight.SourceSubstitution in
/-- Elaborate one inference from the retained proofs of its premises. -/
def elabInference : InferenceRequest → Theorem → List Retained → Option Retained
  | .refl _, out, [] => elabConversion out.sequent.concl.term
  | .trans _ _, _, [first, second] => elabTrans first second
  | .mkComb _ _, _, [functions, arguments] => elabMkComb functions arguments
  | .abs binder _, _, [input] => elabAbs binder input
  | .beta _, out, [] => elabConversion out.sequent.concl.term
  | .assume term, _, [] => elabAssume term
  | .eqMp _ _, _, [equation, premise] => elabEqMp equation premise
  | .deductAntisym _ _, _, [first, second] => elabDeductAntisym first second
  | .instType entries _, _, [input] => some (elabSubstitution (typeOnlySubstitution entries) input)
  | .inst entries _, _, [input] =>
      (admitTermSubstitution entries).map fun substitution => elabSubstitution substitution input
  | _, _, _ => none

/-- Elaborate one graph node. Axioms are not elaborated: the axiom-free
kernel has none. -/
def elabRequest : RuleRequest → Theorem → List Retained → Option Retained
  | .inference request, out, premises => elabInference request out premises
  | .axiom _, _, _ => none

open HOLLight.SourceSubstitution in
/-- **Every inference elaborates correctly** from correct premises. -/
theorem elabInference_correct {request : InferenceRequest} {out : Theorem}
    (semantics : request.Semantics out) {premises : List Retained}
    (premisesCorrect : List.Forall₂ Correct request.premises premises) :
    ∃ retained, elabInference request out premises = some retained ∧ Correct out retained := by
  cases request with
  | refl term =>
      cases premisesCorrect
      exact elabRefl_correct semantics
  | trans first second =>
      obtain _ | ⟨firstCorrect, _ | ⟨secondCorrect, rest⟩⟩ := premisesCorrect
      cases rest
      exact elabTrans_correct semantics firstCorrect secondCorrect
  | mkComb functions arguments =>
      obtain _ | ⟨firstCorrect, _ | ⟨secondCorrect, rest⟩⟩ := premisesCorrect
      cases rest
      exact elabMkComb_correct ((appSemantics_iff_coreStep _ _ _).mpr
        ((appSemantics_iff_coreStep _ _ _).mp semantics)) firstCorrect secondCorrect
  | abs binder input =>
      obtain _ | ⟨inputCorrect, rest⟩ := premisesCorrect
      cases rest
      exact elabAbs_correct semantics inputCorrect
  | beta term =>
      cases premisesCorrect
      exact elabBeta_correct semantics
  | assume term =>
      cases premisesCorrect
      exact elabAssume_correct semantics
  | eqMp equation premise =>
      obtain _ | ⟨firstCorrect, _ | ⟨secondCorrect, rest⟩⟩ := premisesCorrect
      cases rest
      exact elabEqMp_correct semantics firstCorrect secondCorrect
  | deductAntisym first second =>
      obtain _ | ⟨firstCorrect, _ | ⟨secondCorrect, rest⟩⟩ := premisesCorrect
      cases rest
      exact elabDeductAntisym_correct semantics firstCorrect secondCorrect
  | instType entries input =>
      obtain _ | ⟨inputCorrect, rest⟩ := premisesCorrect
      cases rest
      exact ⟨_, rfl, elabSubstitution_correct semantics inputCorrect⟩
  | inst entries input =>
      obtain _ | ⟨inputCorrect, rest⟩ := premisesCorrect
      cases rest
      obtain ⟨substitution, admitted, substituted⟩ := semantics
      exact ⟨_, by simp [elabInference, admitted], elabSubstitution_correct substituted inputCorrect⟩

/-- Elaborate the nodes of a graph in order, from the retained proofs of the
nodes already elaborated. -/
def elabFrom : Array Retained → List ProofExecution.Receipt → Option (Array Retained)
  | retained, [] => some retained
  | retained, node :: rest => do
      let premises ← DerivationGraph.lookupPremises retained node.parents
      let elaborated ← elabRequest node.witness node.conclusion premises
      elabFrom (retained.push elaborated) rest

/-- A cache of theorems and a cache of retained proofs that agree entry by
entry. -/
def Agree (theorems : Array Theorem) (retained : Array Retained) : Prop :=
  ∃ sizes : theorems.size = retained.size, ∀ (index : Nat) (bound : index < theorems.size),
    Correct theorems[index] (retained[index]'(sizes ▸ bound))

theorem Agree.lookup {theorems : Array Theorem} {retained : Array Retained}
    (agree : Agree theorems retained) :
    ∀ {indices : List Nat} {premises : List Theorem},
      DerivationGraph.lookupPremises theorems indices = some premises →
        ∃ premisesRetained, DerivationGraph.lookupPremises retained indices = some premisesRetained ∧
          List.Forall₂ Correct premises premisesRetained
  | [], premises, found => by
      simp only [DerivationGraph.lookupPremises, Option.some.injEq] at found
      subst found
      exact ⟨[], rfl, .nil⟩
  | index :: rest, premises, found => by
      simp only [DerivationGraph.lookupPremises, Option.bind_eq_bind, Option.bind_eq_some_iff,
        Option.pure_def, Option.some.injEq] at found
      obtain ⟨premise, premiseFound, others, othersFound, rfl⟩ := found
      obtain ⟨sizes, correct⟩ := agree
      obtain ⟨bound, rfl⟩ := Array.getElem?_eq_some_iff.mp premiseFound
      obtain ⟨othersRetained, othersRetainedFound, othersCorrect⟩ :=
        Agree.lookup ⟨sizes, correct⟩ othersFound
      refine ⟨retained[index]'(sizes ▸ bound) :: othersRetained, ?_, .cons (correct index bound)
        othersCorrect⟩
      simp [DerivationGraph.lookupPremises, othersRetainedFound,
        Array.getElem?_eq_getElem (sizes ▸ bound : index < retained.size)]

theorem Agree.push {theorems : Array Theorem} {retained : Array Retained}
    (agree : Agree theorems retained) {out : Theorem} {elaborated : Retained}
    (correct : Correct out elaborated) : Agree (theorems.push out) (retained.push elaborated) := by
  obtain ⟨sizes, entries⟩ := agree
  refine ⟨by simp [sizes], fun index bound => ?_⟩
  rcases Nat.lt_or_ge index theorems.size with earlier | later
  · simp only [Array.getElem_push, earlier, dif_pos, sizes ▸ earlier]
    exact entries index earlier
  · have last : index = theorems.size := by
      simp only [Array.size_push] at bound
      omega
    subst last
    convert correct using 1
    · simp
    · simp [sizes]

/-- **Graph elaboration follows graph replay.** -/
theorem elabFrom_correct :
    ∀ {nodes : List ProofExecution.Receipt} {theorems result : Array Theorem}
      {retained : Array Retained},
      Agree theorems retained →
      DerivationGraph.replayFrom (ruleWitness emptyAxiomPolicy) theorems nodes = some result →
        ∃ retainedResult, elabFrom retained nodes = some retainedResult ∧ Agree result retainedResult
  | [], theorems, result, retained, agree, replayed => by
      simp only [DerivationGraph.replayFrom, Option.some.injEq] at replayed
      subst replayed
      exact ⟨retained, rfl, agree⟩
  | node :: rest, theorems, result, retained, agree, replayed => by
      simp only [DerivationGraph.replayFrom, Option.bind_eq_bind, Option.bind_eq_some_iff] at replayed
      obtain ⟨next, stepped, restReplayed⟩ := replayed
      obtain ⟨found, checked, rfl⟩ :=
        (ProofSystem.node_replay_iff emptyAxiomPolicy theorems next node).mp stepped
      obtain ⟨premisesRetained, retainedFound, premisesCorrect⟩ := agree.lookup found
      have semantics := (RuleRequest.check_eq_some_iff emptyAxiomPolicy _ _).mp checked
      have elaborated : ∃ elaborated, elabRequest node.witness node.conclusion premisesRetained =
          some elaborated ∧ Correct node.conclusion elaborated := by
        revert semantics premisesCorrect
        cases node.witness with
        | «axiom» sequent =>
            intro _ semantics
            exact absurd semantics.2.1 (by simp [emptyAxiomPolicy])
        | inference request =>
            intro premisesCorrect semantics
            exact elabInference_correct semantics premisesCorrect
      obtain ⟨elaborated, elaboratedFound, elaboratedCorrect⟩ := elaborated
      obtain ⟨retainedResult, resultFound, resultAgree⟩ :=
        elabFrom_correct (agree.push elaboratedCorrect) restReplayed
      refine ⟨retainedResult, ?_, resultAgree⟩
      simp [elabFrom, retainedFound, elaboratedFound, resultFound]

/-- **The elaborator.** Elaborate an HOL Light proof graph and return the
retained proof at its root. -/
def elaborate (certificate : ProofSystem.Certificate) : Option Retained := do
  let retained ← elabFrom #[] certificate.1
  retained[certificate.2]?

/-- **Accepted graphs elaborate into correct retained proofs.** -/
theorem elaborate_correct {claim : Theorem} {certificate : ProofSystem.Certificate}
    (accepted : (ProofSystem.checker emptyAxiomPolicy).check claim certificate = true) :
    ∃ retained, elaborate certificate = some retained ∧ Correct claim retained := by
  obtain ⟨cache, replayed, found⟩ :=
    (ProofSystem.checker_check_iff emptyAxiomPolicy claim certificate).mp accepted
  obtain ⟨retained, elaborated, agree⟩ :=
    elabFrom_correct (retained := #[]) ⟨rfl, fun index bound => absurd bound (by simp)⟩ replayed
  obtain ⟨sizes, entries⟩ := agree
  obtain ⟨bound, rfl⟩ := Array.getElem?_eq_some_iff.mp found
  refine ⟨retained[certificate.2]'(sizes ▸ bound), ?_, entries _ bound⟩
  simp [elaborate, elaborated, Array.getElem?_eq_getElem (sizes ▸ bound : certificate.2 < retained.size)]

/-! ## From the compositional translation to the translation with primitive equality -/

/-- Congruence of equations. -/
def eqCongrProof {Γ : HOL.Ctx AtomicTy} {Δ : List (HOL.Formula Symbol Γ)} {τ : HOL.Ty AtomicTy}
    {left left' right right' : HOL.Term Symbol Γ τ}
    (lefts : HOL.ProofSyntax Symbol Δ (.eq left left'))
    (rights : HOL.ProofSyntax Symbol Δ (.eq right right')) :
    HOL.ProofSyntax Symbol Δ (.eq (.eq left right) (.eq left' right')) :=
  .eqPropI
    (.impI (.eqTrans (.eqTrans (.eqSymm (HOL.ProofSyntax.prepend _ lefts)) (.hyp ⟨0, by simp⟩))
      (HOL.ProofSyntax.prepend _ rights)))
    (.impI (.eqTrans (.eqTrans (HOL.ProofSyntax.prepend _ lefts) (.hyp ⟨0, by simp⟩))
      (.eqSymm (HOL.ProofSyntax.prepend _ rights))))

/-- Both translations of a term, with a proof that they are equal under any
assumptions. -/
abbrev Bridged (Γ : HOL.Ctx AtomicTy) : Type :=
  Σ τ : HOL.Ty AtomicTy, Σ primitive : HOL.Term Symbol Γ τ, Σ compositional : HOL.Term Symbol Γ τ,
    ∀ Δ : List (HOL.Formula Symbol Γ), HOL.ProofSyntax Symbol Δ (.eq primitive compositional)

/-- Bridge two applied translations. -/
def bridgeApp {Γ : HOL.Ctx AtomicTy} : Bridged Γ → Bridged Γ → Option (Bridged Γ)
  | ⟨.arr domain codomain, function, function', functionProof⟩, ⟨argumentType, argument, argument',
      argumentProof⟩ =>
      if same : argumentType = domain then
        some ⟨codomain, .app function (same ▸ argument), .app function' (same ▸ argument'),
          fun Δ => .eqTrans (.eqApp (same ▸ argument) (functionProof Δ))
            (.eqAppArg function' (castEquation' same (argumentProof Δ)))⟩
      else none
  | _, _ => none
where
  castEquation' {Δ : List (HOL.Formula Symbol Γ)} {σ σ' : HOL.Ty AtomicTy} (same : σ = σ')
      {left right : HOL.Term Symbol Γ σ} (proof : HOL.ProofSyntax Symbol Δ (.eq left right)) :
      HOL.ProofSyntax Symbol Δ (.eq (same ▸ left) (same ▸ right)) := by
    subst same
    exact proof

/-- Bridge an equality application. -/
def bridgeEquality {Γ : HOL.Ctx AtomicTy} (operand : HOL.Ty AtomicTy) :
    Bridged Γ → Bridged Γ → Option (Bridged Γ)
  | ⟨leftType, left, left', leftProof⟩, ⟨rightType, right, right', rightProof⟩ =>
      if leftSame : leftType = operand then
        if rightSame : rightType = operand then
          some ⟨.prop, .eq (leftSame ▸ left) (rightSame ▸ right),
            .app (.app (equalityLambda operand) (leftSame ▸ left')) (rightSame ▸ right'),
            fun Δ => .eqTrans (eqCongrProof (bridgeApp.castEquation' leftSame (leftProof Δ))
                (bridgeApp.castEquation' rightSame (rightProof Δ)))
              (.eqSymm (equalityLambdaProof Δ _ _))⟩
        else none
      else none

/-- **Both translations, computed together with their equation.** -/
def bridge : (Γ : HOL.Ctx AtomicTy) → DBTerm → Option (Bridged Γ)
  | Γ, .app function@(.app (.const name annotation) left) right =>
      match equalityOperand? name annotation with
      | some operand => do
          let left' ← bridge Γ left
          let right' ← bridge Γ right
          bridgeEquality operand.toHOL left' right'
      | none => do
          let function' ← bridge Γ function
          let right' ← bridge Γ right
          bridgeApp function' right'
  | Γ, .app function argument => do
      let function' ← bridge Γ function
      let argument' ← bridge Γ argument
      bridgeApp function' argument'
  | Γ, .abs domain body => do
      let ⟨bodyType, body, body', bodyProof⟩ ← bridge (domain.toHOL :: Γ) body
      some ⟨.arr domain.toHOL bodyType, .lam body, .lam body',
        fun Δ => .eqLam (bodyProof (HOL.weakenHyps Δ))⟩
  | Γ, term => do
      let ⟨τ, target⟩ ← translate? Γ term
      some ⟨τ, target, target, fun _ => .eqRefl target⟩

theorem bridge_atomic {Γ : HOL.Ctx AtomicTy} {term : DBTerm} {τ : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol Γ τ} (translated : translate? Γ term = some ⟨τ, target⟩)
    (atomic : bridge Γ term = (do
      let ⟨τ, target⟩ ← translate? Γ term
      some ⟨τ, target, target, fun _ => .eqRefl target⟩)) :
    bridge Γ term = some ⟨τ, target, target, fun _ => .eqRefl target⟩ := by
  rw [atomic, translated]
  rfl

theorem bridge_app_generic {Γ : HOL.Ctx AtomicTy} {function : DBTerm} (argument : DBTerm)
    (notEquality : function.equalityHeadOperand? = none) :
    bridge Γ (.app function argument) = (do
      let function' ← bridge Γ function
      let argument' ← bridge Γ argument
      bridgeApp function' argument') := by
  cases function with
  | app head left =>
      cases head with
      | const name annotation =>
          have unrecognized : equalityOperand? name annotation = none := notEquality
          conv_lhs => unfold bridge
          simp only [unrecognized]
      | _ => conv_lhs => unfold bridge
  | _ => conv_lhs => unfold bridge

theorem bridge_app_equality {Γ : HOL.Ctx AtomicTy} {name : Const} {annotation operand : Ty}
    (recognized : equalityOperand? name annotation = some operand) (left right : DBTerm) :
    bridge Γ (.app (.app (.const name annotation) left) right) = (do
      let left' ← bridge Γ left
      let right' ← bridge Γ right
      bridgeEquality operand.toHOL left' right') := by
  conv_lhs => unfold bridge
  simp only [recognized]

/-- What the bridge does on one term. -/
def BridgeComplete (term : DBTerm) : Prop :=
  ∀ {Γ : HOL.Ctx AtomicTy} {τ : HOL.Ty AtomicTy} {compositional : HOL.Term Symbol Γ τ},
    TranslatesCompositionally Γ term τ compositional →
      ∃ (primitive : HOL.Term Symbol Γ τ) (proof : _),
        bridge Γ term = some ⟨τ, primitive, compositional, proof⟩ ∧ Translates Γ term τ primitive

theorem bridge_complete_aux (term : DBTerm) :
    BridgeComplete term ∧ ∀ head argument, term = .app head argument → BridgeComplete argument := by
  induction term with
  | const name annotation =>
      refine ⟨fun {Γ τ compositional} translated => ?_, fun _ _ same => nomatch same⟩
      refine ⟨compositional, _, bridge_atomic (translate?_complete translated)
        (by unfold bridge; rfl), ?_⟩
      cases translated with
      | equality recognized typed => exact .equality recognized typed
      | constant unrecognized typed => exact .constant unrecognized typed
  | free variable_ =>
      refine ⟨fun {Γ τ compositional} translated => ?_, fun _ _ same => nomatch same⟩
      refine ⟨compositional, _, bridge_atomic (translate?_complete translated)
        (by unfold bridge; rfl), ?_⟩
      cases translated with
      | free typed => exact .free typed
  | bound index =>
      refine ⟨fun {Γ τ compositional} translated => ?_, fun _ _ same => nomatch same⟩
      refine ⟨compositional, _, bridge_atomic (translate?_complete translated)
        (by unfold bridge; rfl), ?_⟩
      generalize sameIndex : index = position at translated
      cases translated with
      | bound x => exact sameIndex ▸ .bound x
  | abs domain body bodyIh =>
      refine ⟨fun {Γ τ compositional} translated => ?_, fun _ _ same => nomatch same⟩
      cases translated with
      | abs typed bodyTranslated =>
          subst typed
          obtain ⟨body', bodyProof, bodyFound, bodyPrimitive⟩ := bodyIh.1 bodyTranslated
          exact ⟨_, fun Δ => .eqLam (bodyProof (HOL.weakenHyps Δ)), by simp [bridge, bodyFound],
            .abs rfl bodyPrimitive⟩
  | app function argument functionIh argumentIh =>
      refine ⟨fun {Γ τ compositional} translated => ?_, fun head argument' same => ?_⟩
      · cases translated with
        | @app _ _ _ σ _ function' argument' functionTranslated argumentTranslated =>
            obtain ⟨argumentPrimitive, argumentProof, argumentFound, argumentTranslates⟩ :=
              argumentIh.1 argumentTranslated
            cases equalityHead : function.equalityHeadOperand? with
            | some operand =>
                obtain ⟨name, annotation, left, rfl, recognized⟩ :=
                  DBTerm.equalityHeadOperand?_eq_some_iff.mp equalityHead
                cases functionTranslated with
                | app headTranslated leftTranslated =>
                    cases headTranslated with
                    | equality recognized' typed =>
                        rw [recognized] at recognized'
                        cases recognized'
                        subst typed
                        obtain ⟨leftPrimitive, leftProof, leftFound, leftTranslates⟩ :=
                          functionIh.2 _ _ rfl leftTranslated
                        refine ⟨_, fun Δ => .eqTrans
                            (eqCongrProof (bridgeApp.castEquation' rfl (leftProof Δ))
                              (bridgeApp.castEquation' rfl (argumentProof Δ)))
                            (.eqSymm (equalityLambdaProof Δ _ _)), ?_,
                          .equalityApp recognized rfl leftTranslates argumentTranslates⟩
                        rw [bridge_app_equality recognized, leftFound, argumentFound]
                        simp only [Option.bind_eq_bind, Option.bind_some]
                        unfold bridgeEquality
                        dsimp only
                        rw [dif_pos rfl, dif_pos rfl]
                    | constant unrecognized _ =>
                        rw [recognized] at unrecognized
                        cases unrecognized
            | none =>
                obtain ⟨functionPrimitive, functionProof, functionFound, functionTranslates⟩ :=
                  functionIh.1 functionTranslated
                refine ⟨_, fun Δ => .eqTrans (.eqApp argumentPrimitive (functionProof Δ))
                    (.eqAppArg function' (bridgeApp.castEquation' rfl (argumentProof Δ))), ?_,
                  .app equalityHead functionTranslates argumentTranslates⟩
                rw [bridge_app_generic argument equalityHead, functionFound, argumentFound]
                simp only [Option.bind_eq_bind, Option.bind_some]
                unfold bridgeApp
                dsimp only
                rw [dif_pos rfl]
      · cases same
        exact argumentIh.1

/-- **The bridge succeeds on every translatable term**, and its first
component is the translation with primitive equality. -/
theorem bridge_complete {term : DBTerm} : BridgeComplete term := (bridge_complete_aux term).1

/-- Read a compositionally translated term back as its canonical source. -/
def untranslate : {Γ : HOL.Ctx AtomicTy} → {τ : HOL.Ty AtomicTy} → HOL.Term Symbol Γ τ → DBTerm
  | _, _, .var x => .bound (deBruijnIndex x)
  | _, _, .const (.constant name annotation _) => .const name annotation
  | _, _, .const (.variable variable_ _) => .free variable_
  | _, _, .app function argument => .app (untranslate function) (untranslate argument)
  | Γ, .arr domain codomain, .lam body =>
      if same : codomain = .arr domain .prop then
        if (same ▸ (HOL.Term.lam body : HOL.Term Symbol Γ (.arr domain codomain))) =
            equalityLambda domain then
          .const Const.equality (Ty.equality (Ty.fromHOL domain))
        else .abs (Ty.fromHOL domain) (untranslate body)
      else .abs (Ty.fromHOL domain) (untranslate body)
  | _, _, _ => .bound 0

theorem no_equation_translation {Γ : HOL.Ctx AtomicTy} {term : DBTerm} {σ : HOL.Ty AtomicTy}
    {left right : HOL.Term Symbol Γ σ}
    (translated : TranslatesCompositionally Γ term .prop (.eq left right)) : False := by
  cases translated

theorem not_equalityLambda_body {Γ : HOL.Ctx AtomicTy} {σ : HOL.Ty AtomicTy} {term : DBTerm}
    {body : HOL.Term Symbol (σ :: Γ) (.arr σ .prop)}
    (translated : TranslatesCompositionally (σ :: Γ) term (.arr σ .prop) body)
    (shape : (HOL.Term.lam body : HOL.Term Symbol Γ (.arr σ (.arr σ .prop))) = equalityLambda σ) :
    False := by
  unfold equalityLambda at shape
  simp only [HOL.Term.lam.injEq] at shape
  subst shape
  cases translated with
  | abs _ inner => exact no_equation_translation inner

/-- **Untranslation inverts the compositional translation.** -/
theorem untranslate_eq {Γ : HOL.Ctx AtomicTy} {term : DBTerm} {τ : HOL.Ty AtomicTy}
    {target : HOL.Term Symbol Γ τ} (translated : TranslatesCompositionally Γ term τ target) :
    untranslate target = term := by
  induction translated with
  | @equality Γ name annotation operand σ recognized typed =>
      obtain ⟨rfl, rfl⟩ := (equalityOperand?_eq_some_iff _ _ _).mp recognized
      subst typed
      simp [untranslate, equalityLambda, Ty.fromHOL_toHOL]
  | constant unrecognized typed => rfl
  | free typed => rfl
  | bound x => rfl
  | app _ _ functionIh argumentIh => simp [untranslate, functionIh, argumentIh]
  | @abs Γ domain body σ τ body' typed bodyTranslated bodyIh =>
      subst typed
      unfold untranslate
      split
      · rename_i same
        subst same
        split
        · rename_i shape
          exact absurd shape (fun shape => not_equalityLambda_body bodyTranslated shape)
        · rw [Ty.fromHOL_toHOL, bodyIh]
      · rw [Ty.fromHOL_toHOL, bodyIh]

/-! ## Retained proofs of the translation with primitive equality -/

/-- The translation with primitive equality of a compositionally translated
closed formula, with their equation. -/
def primitiveHypothesis (formula : HOL.ClosedFormula Symbol) :
    Option (Σ primitive : HOL.ClosedFormula Symbol,
      ∀ Δ : List (HOL.ClosedFormula Symbol), HOL.ProofSyntax Symbol Δ (.eq primitive formula)) :=
  match bridge [] (untranslate formula) with
  | some ⟨.prop, primitive, compositional, proof⟩ =>
      if same : compositional = formula then some ⟨primitive, fun Δ => same ▸ proof Δ⟩ else none
  | _ => none

/-- The translation with primitive equality of a hypothesis, or the
hypothesis itself when it is not a translation. -/
def primitiveOf (formula : HOL.ClosedFormula Symbol) : HOL.ClosedFormula Symbol :=
  match primitiveHypothesis formula with
  | some found => found.1
  | none => formula

/-- A hypothesis occurrence found by membership. -/
def hypothesisOf {Δ : List (HOL.ClosedFormula Symbol)} {formula : HOL.ClosedFormula Symbol}
    (member : formula ∈ Δ) : HOL.ProofSyntax Symbol Δ formula :=
  HOL.ProofSyntax.castIndices rfl (by simp)
    (.hyp ⟨Δ.idxOf formula, List.idxOf_lt_length_of_mem member⟩)

/-- Derive a compositional hypothesis from its primitive form. -/
def fromPrimitive {Δ : List (HOL.ClosedFormula Symbol)} (formula : HOL.ClosedFormula Symbol)
    (member : primitiveOf formula ∈ Δ) : HOL.ProofSyntax Symbol Δ formula :=
  match found : primitiveHypothesis formula with
  | some ⟨primitive, proof⟩ =>
      .impE (.eqPropEL (proof Δ)) (hypothesisOf (by
        unfold primitiveOf at member
        rw [found] at member
        exact member))
  | none => hypothesisOf (by
      unfold primitiveOf at member
      rw [found] at member
      exact member)

/-- **Restate a retained proof with the translation with primitive
equality**, for the conclusion of a given source term. -/
def toPrimitive (conclusion : DBTerm) (retained : Retained) :
    Option (Mettapedia.Logic.HOL.ContextualTrinity.ProvedSequent (Const := Symbol) []) :=
  let hypotheses := retained.hypotheses.map primitiveOf
  let substitution : HOL.ProofSyntax.HypothesisSubstitution retained.hypotheses hypotheses :=
    fun occurrence => fromPrimitive _ (List.mem_map_of_mem (List.get_mem _ occurrence))
  match bridge [] conclusion with
  | some ⟨.prop, primitive, compositional, proof⟩ =>
      if same : compositional = retained.conclusion then
        some ⟨(hypotheses, primitive), .impE (.eqPropER (same ▸ proof hypotheses))
          (HOL.ProofSyntax.substituteHypotheses substitution retained.proof)⟩
      else none
  | _ => none

theorem primitiveOf_translated {term : CanonicalTerm} {formula : HOL.ClosedFormula Symbol}
    (translated : TranslatesCompositionally [] term.term .prop formula) :
    Translates [] term.term .prop (primitiveOf formula) := by
  obtain ⟨primitive, proof, found, primitiveTranslated⟩ := bridge_complete translated
  have source := untranslate_eq translated
  unfold primitiveOf primitiveHypothesis
  rw [source, found]
  simp only [dif_pos]
  exact primitiveTranslated

/-- **Conversion to the translation with primitive equality is correct.** -/
theorem toPrimitive_correct {out : Theorem} {retained : Retained} (correct : Correct out retained) :
    ∃ proved, toPrimitive out.sequent.concl.term retained = some proved ∧
      Translates [] out.sequent.concl.term .prop proved.1.2 ∧
      ∀ ψ ∈ proved.1.1, ψ ∈ translatedHypotheses out.sequent.hyp := by
  obtain ⟨primitive, proof, found, primitiveTranslated⟩ := bridge_complete correct.1
  refine ⟨⟨(retained.hypotheses.map primitiveOf, primitive), .impE (.eqPropER (proof _))
      (HOL.ProofSyntax.substituteHypotheses
        (fun occurrence => fromPrimitive _ (List.mem_map_of_mem (List.get_mem _ occurrence)))
        retained.proof)⟩, ?_, primitiveTranslated, ?_⟩
  · unfold toPrimitive
    rw [found]
    simp only [dif_pos]
  · intro ψ member
    obtain ⟨compositional, compositionalMember, rfl⟩ := List.mem_map.mp member
    obtain ⟨term, termMember, translated⟩ := correct.2 compositional compositionalMember
    exact ⟨term, termMember, primitiveOf_translated translated⟩

/-- **The elaborator, to retained proofs of the translated sequent.** -/
def elaborateProved (claim : Theorem) (certificate : ProofSystem.Certificate) :
    Option (Mettapedia.Logic.HOL.ContextualTrinity.ProvedSequent (Const := Symbol) []) := do
  let retained ← elaborate certificate
  toPrimitive claim.sequent.concl.term retained

/-- **Every accepted HOL Light graph elaborates, by a computable function, into
a retained natural-deduction proof** of its translated conclusion from its
translated hypotheses. -/
theorem elaborateProved_correct {claim : Theorem} {certificate : ProofSystem.Certificate}
    (accepted : (ProofSystem.checker emptyAxiomPolicy).check claim certificate = true) :
    ∃ proved, elaborateProved claim certificate = some proved ∧
      Translates [] claim.sequent.concl.term .prop proved.1.2 ∧
      ∀ ψ ∈ proved.1.1, ψ ∈ translatedHypotheses claim.sequent.hyp := by
  obtain ⟨retained, elaborated, correct⟩ := elaborate_correct accepted
  obtain ⟨proved, converted, translated, hypotheses⟩ := toPrimitive_correct correct
  exact ⟨proved, by simp [elaborateProved, elaborated, converted], translated, hypotheses⟩

namespace Controls

open ProofSystem.Controls ProofExecution.Controls

/-- **Positive control.** The one-node reflexivity graph elaborates to a
retained proof of its translated conclusion with no hypotheses. -/
theorem reflexivity_elaborated :
    ∃ proved, elaborateProved reflexivityTheorem reflexivityCertificate = some proved ∧
      Translates [] reflexivityTheorem.sequent.concl.term .prop proved.1.2 ∧ proved.1.1 = [] := by
  obtain ⟨proved, elaborated, translated, hypotheses⟩ := elaborateProved_correct reflexivity_accepted
  refine ⟨proved, elaborated, translated, List.eq_nil_iff_forall_not_mem.mpr fun ψ member => ?_⟩
  obtain ⟨term, termMember, _⟩ := hypotheses ψ member
  simp [reflexivityTheorem, Theorem.emptyResult] at termMember

/-- **Negative control.** A graph citing a premise that does not exist does not
elaborate. -/
theorem forward_reference_not_elaborated (claim : Theorem) :
    elaborateProved claim
      ([⟨reflexivityTheorem, .inference (.refl proposition), [0], ("authored", 0)⟩], 0) = none := by
  simp [elaborateProved, elaborate, elabFrom, DerivationGraph.lookupPremises]

end Controls

#print axioms elaborate_correct
#print axioms elaborateProved_correct
#print axioms Controls.reflexivity_elaborated

end Mettapedia.Languages.HOLLight.RetainedElaboration
