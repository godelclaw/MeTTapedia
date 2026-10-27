import Mettapedia.Logic.HOL.VectorRecursionProofs
import Mettapedia.Logic.HOL.PredicateProducts
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.AnnotatedPredicateRoots
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorJudgmentReplay

/-!
# Original open Vec computation rows as retained HOL proofs

The row endpoints retain the open element predicate and motive arguments.
Their underlying eliminator uses natural recursion at `vector ⇒ result`.
Its nil and cons equalities are derived from selection, natural recursion
and the constructor projections. The ordered background formulas remain
explicit; this file does not discharge them against a native source history.

The lexical reading here covers the lambda-free computation endpoints. It
supplies no universe interpretation or dependent vector membership theorem.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies

local infixr:60 " ⇒ " => HOL.Ty.arr

universe u v

structure Operations (Base : Type u) (Const : HOL.Ty Base → Type v) where
  number : HOL.Ty Base
  element : HOL.Ty Base
  vector : HOL.Ty Base
  result : HOL.Ty Base
  zero : HOL.ClosedTerm Const number
  successor : HOL.ClosedTerm Const (number ⇒ number)
  nil : HOL.ClosedTerm Const vector
  cons : HOL.ClosedTerm Const (number ⇒ element ⇒ vector ⇒ vector)
  head : HOL.ClosedTerm Const (vector ⇒ element)
  tail : HOL.ClosedTerm Const (vector ⇒ vector)
  selection : HOL.ClosedTerm Const (HOL.SelectionProofs.Selection (number ⇒ vector ⇒ result))

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

namespace Operations

variable (operations : Operations Base Const)

abbrev elementPredicate := operations.element ⇒ HOL.Ty.prop
abbrev motive := operations.number ⇒ operations.vector ⇒ operations.result ⇒ HOL.Ty.prop
abbrev method := HOL.VectorRecursionProofs.Method operations.number operations.element operations.vector operations.result
abbrev eliminatorType := operations.elementPredicate ⇒ operations.motive ⇒ operations.result ⇒
  operations.method ⇒ operations.number ⇒ operations.vector ⇒ operations.result

def nilCode : HOL.ClosedTerm Const (operations.elementPredicate ⇒ operations.vector) := .lam (HOL.weaken operations.nil)
def consCode : HOL.ClosedTerm Const
    (operations.elementPredicate ⇒ operations.number ⇒ operations.element ⇒ operations.vector ⇒ operations.vector) :=
  .lam (HOL.weaken operations.cons)

def recursion {Γ : HOL.Ctx Base} (base : HOL.Term Const Γ operations.result)
    (method : HOL.Term Const Γ operations.method) : HOL.Term Const Γ (operations.number ⇒ operations.vector ⇒ operations.result) :=
  HOL.VectorRecursionProofs.recursor (HOL.weakenCtx Γ operations.selection)
    (HOL.weakenCtx Γ operations.zero) (HOL.weakenCtx Γ operations.successor)
    (HOL.weakenCtx Γ operations.head) (HOL.weakenCtx Γ operations.tail) base method

@[simp] theorem subst_recursion {Γ Ξ : HOL.Ctx Base} (σ : HOL.Subst Const Γ Ξ)
    (base : HOL.Term Const Γ operations.result) (method : HOL.Term Const Γ operations.method) :
    HOL.subst σ (operations.recursion base method) = operations.recursion (HOL.subst σ base) (HOL.subst σ method) := by
  simp [recursion, HOL.subst_weakenCtx]

def eliminator {Γ : HOL.Ctx Base} : HOL.Term Const Γ operations.eliminatorType :=
  .lam (.lam (.lam (.lam (operations.recursion (.var (.vs .vz)) (.var .vz)))))

@[simp] theorem subst_eliminator {Γ Ξ : HOL.Ctx Base} (σ : HOL.Subst Const Γ Ξ) :
    HOL.subst σ (operations.eliminator (Γ := Γ)) = operations.eliminator (Γ := Ξ) := by
  simp [eliminator, HOL.subst, HOL.Subst.lift, HOL.Rename.weaken]

theorem weaken_eliminator (Γ : HOL.Ctx Base) :
    HOL.weakenCtx Γ (operations.eliminator (Γ := [])) = operations.eliminator (Γ := Γ) := by
  let ρ : HOL.Subst Const [] Γ := fun index => nomatch index
  exact (HOL.subst_weakenCtx ρ (operations.eliminator (Γ := []))).symm.trans
    (operations.subst_eliminator ρ)

def headLaw {Γ : HOL.Ctx Base} : HOL.Formula Const Γ :=
  .all (.all (.all (.eq
    (.app (HOL.weakenCtx (operations.vector :: operations.element :: operations.number :: Γ) operations.head)
      (.app (.app (.app (HOL.weakenCtx _ operations.cons) (.var (.vs (.vs .vz)))) (.var (.vs .vz))) (.var .vz)))
    (.var (.vs .vz)))))

def tailLaw {Γ : HOL.Ctx Base} : HOL.Formula Const Γ :=
  .all (.all (.all (.eq
    (.app (HOL.weakenCtx (operations.vector :: operations.element :: operations.number :: Γ) operations.tail)
      (.app (.app (.app (HOL.weakenCtx _ operations.cons) (.var (.vs (.vs .vz)))) (.var (.vs .vz))) (.var .vz)))
    (.var .vz))))

def closedAssumptions : List (HOL.ClosedFormula Const) :=
  [HOL.SelectionProofs.principle operations.selection,
   HOL.NaturalRecursionProofs.statement operations.zero operations.successor (operations.vector ⇒ operations.result),
   operations.headLaw, operations.tailLaw]

def lexicalReading : AnnotatedPredicateReading.LexicalReading Tower.Head Base Const where
  constCode? name :=
    if name = natName then some ⟨_, HOL.PredicateProducts.full operations.number⟩
    else if name = zeroName then some ⟨_, operations.zero⟩
    else if name = succName then some ⟨_, operations.successor⟩
    else if name = vnilName then some ⟨_, operations.nilCode⟩
    else if name = vconsName then some ⟨_, operations.consCode⟩
    else if name = vecEliminateName then some ⟨_, operations.eliminator⟩
    else none
  headCode? _ := none

variable {Γ : HOL.Ctx Base} {Δ : List (HOL.Formula Const Γ)}

def eliminator_apply (A : HOL.Term Const Γ operations.elementPredicate)
    (P : HOL.Term Const Γ operations.motive) (base : HOL.Term Const Γ operations.result)
    (method : HOL.Term Const Γ operations.method) :
    HOL.ProofSyntax Const Δ (.eq
      (.app (.app (.app (.app operations.eliminator A) P) base) method) (operations.recursion base method)) := by
  have first : HOL.ProofSyntax Const Δ (.eq (.app operations.eliminator A)
      (.lam (.lam (.lam (operations.recursion (.var (.vs .vz)) (.var .vz)))))) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (.beta A (.lam (σ := operations.motive) (.lam (.lam (operations.recursion (.var (.vs .vz)) (.var .vz))))))
    simp [eliminator, HOL.instantiate, HOL.subst, HOL.Subst.lift, HOL.Rename.weaken]
  have second : HOL.ProofSyntax Const Δ (.eq
      (.app (.lam (.lam (.lam (operations.recursion (.var (.vs .vz)) (.var .vz))))) P)
      (.lam (.lam (operations.recursion (.var (.vs .vz)) (.var .vz))))) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (.beta P (.lam (.lam (operations.recursion (.var (.vs .vz)) (.var .vz)))))
    simp [HOL.instantiate, HOL.subst, HOL.Subst.lift, HOL.Rename.weaken]
  have third : HOL.ProofSyntax Const Δ (.eq
      (.app (.lam (.lam (operations.recursion (.var (.vs .vz)) (.var .vz)))) base)
      (.lam (operations.recursion (HOL.weaken base) (.var .vz)))) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (.beta base (.lam (operations.recursion (.var (.vs .vz)) (.var .vz))))
    simp [HOL.instantiate, HOL.subst, HOL.Subst.lift, HOL.Subst.single]
    rfl
  have fourth : HOL.ProofSyntax Const Δ (.eq
      (.app (.lam (operations.recursion (HOL.weaken base) (.var .vz))) method) (operations.recursion base method)) := by
    apply HOL.ProofSyntax.castIndices rfl ?_ (.beta method (operations.recursion (HOL.weaken base) (.var .vz)))
    simp [HOL.instantiate, HOL.subst, HOL.Subst.single]
  exact .eqTrans (.eqApp method (.eqApp base (.eqApp P first)))
    (.eqTrans (.eqApp method (.eqApp base second)) (.eqTrans (.eqApp method third) fourth))

def cons_apply (A : HOL.Term Const Γ operations.elementPredicate)
    (index : HOL.Term Const Γ operations.number) (first : HOL.Term Const Γ operations.element)
    (rest : HOL.Term Const Γ operations.vector) :
    HOL.ProofSyntax Const Δ (.eq
      (.app (.app (.app (.app (HOL.weakenCtx Γ operations.consCode) A) index) first) rest)
      (.app (.app (.app (HOL.weakenCtx Γ operations.cons) index) first) rest)) := by
  have erased : HOL.ProofSyntax Const Δ (.eq (.app (HOL.weakenCtx Γ operations.consCode) A)
      (HOL.weakenCtx Γ operations.cons)) := by
    apply HOL.ProofSyntax.castIndices rfl ?_ (.beta A (HOL.weaken (HOL.weakenCtx Γ operations.cons)))
    have code : HOL.weakenCtx Γ operations.consCode = .lam (HOL.weaken (HOL.weakenCtx Γ operations.cons)) := by
      let ρ : HOL.Subst Const [] Γ := fun index => nomatch index
      calc
        _ = HOL.subst ρ operations.consCode := (HOL.subst_weakenCtx ρ operations.consCode).symm
        _ = _ := by
          simp only [consCode, HOL.subst, HOL.subst_weaken]
          apply congrArg HOL.Term.lam
          exact congrArg HOL.weaken (HOL.subst_weakenCtx ρ operations.cons)
    simp [code, HOL.instantiate]
  exact .eqApp rest (.eqApp first (.eqApp index erased))

def head_at (index : HOL.Term Const Γ operations.number) (first : HOL.Term Const Γ operations.element)
    (rest : HOL.Term Const Γ operations.vector) (law : HOL.ProofSyntax Const Δ operations.headLaw) :
    HOL.ProofSyntax Const Δ (.eq
      (.app (HOL.weakenCtx Γ operations.head)
        (.app (.app (.app (HOL.weakenCtx Γ operations.cons) index) first) rest)) first) := by
  apply HOL.ProofSyntax.castIndices rfl ?_ (.allE rest (.allE first (.allE index law)))
  simp [HOL.instantiate, HOL.subst, HOL.Subst.single, HOL.Subst.lift, HOL.Rename.weaken, HOL.subst_rename]
  constructor
  · rw [HOL.subst_comp]
    have identity : (HOL.Subst.comp (HOL.Subst.single rest)
        (fun {τ} (indexVar : HOL.Var Γ τ) => HOL.Term.var (.vs indexVar)) : HOL.Subst Const Γ Γ) = (fun {τ} (indexVar : HOL.Var Γ τ) => HOL.Term.var indexVar) := by
      funext type indexVar
      rfl
    rw [identity]
    exact HOL.subst_id index
  · exact HOL.subst_id first

def tail_at (index : HOL.Term Const Γ operations.number) (first : HOL.Term Const Γ operations.element)
    (rest : HOL.Term Const Γ operations.vector) (law : HOL.ProofSyntax Const Δ operations.tailLaw) :
    HOL.ProofSyntax Const Δ (.eq
      (.app (HOL.weakenCtx Γ operations.tail)
        (.app (.app (.app (HOL.weakenCtx Γ operations.cons) index) first) rest)) rest) := by
  apply HOL.ProofSyntax.castIndices rfl ?_ (.allE rest (.allE first (.allE index law)))
  simp [HOL.instantiate, HOL.subst, HOL.Subst.single, HOL.Subst.lift, HOL.Rename.weaken, HOL.subst_rename]
  constructor
  · rw [HOL.subst_comp]
    have identity : (HOL.Subst.comp (HOL.Subst.single rest)
        (fun {τ} (indexVar : HOL.Var Γ τ) => HOL.Term.var (.vs indexVar)) : HOL.Subst Const Γ Γ) = (fun {τ} (indexVar : HOL.Var Γ τ) => HOL.Term.var indexVar) := by
      funext type indexVar
      rfl
    rw [identity]
    exact HOL.subst_id index
  · exact HOL.subst_id first

def nilIota (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (base : HOL.Term Const Γ operations.result) (method : HOL.Term Const Γ operations.method)
    (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ operations.selection)))
    (recursionProof : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx Γ operations.zero) (HOL.weakenCtx Γ operations.successor) (operations.vector ⇒ operations.result))) :
    HOL.ProofSyntax Const Δ (.eq
      (.app (.app (.app (.app (.app (.app operations.eliminator A) P) base) method) (HOL.weakenCtx Γ operations.zero))
        (.app (HOL.weakenCtx Γ operations.nilCode) A)) base) :=
  .eqTrans (.eqApp (.app (HOL.weakenCtx Γ operations.nilCode) A)
    (.eqApp (HOL.weakenCtx Γ operations.zero) (operations.eliminator_apply A P base method)))
    (HOL.VectorRecursionProofs.atZero (HOL.weakenCtx Γ operations.selection)
      (HOL.weakenCtx Γ operations.zero) (HOL.weakenCtx Γ operations.successor)
      (HOL.weakenCtx Γ operations.head) (HOL.weakenCtx Γ operations.tail) base method
      (.app (HOL.weakenCtx Γ operations.nilCode) A) choice recursionProof)

def consIota (A : HOL.Term Const Γ operations.elementPredicate) (P : HOL.Term Const Γ operations.motive)
    (base : HOL.Term Const Γ operations.result) (method : HOL.Term Const Γ operations.method)
    (index : HOL.Term Const Γ operations.number) (first : HOL.Term Const Γ operations.element)
    (rest : HOL.Term Const Γ operations.vector)
    (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx Γ operations.selection)))
    (recursionProof : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx Γ operations.zero) (HOL.weakenCtx Γ operations.successor) (operations.vector ⇒ operations.result)))
    (headProof : HOL.ProofSyntax Const Δ operations.headLaw)
    (tailProof : HOL.ProofSyntax Const Δ operations.tailLaw) :
    HOL.ProofSyntax Const Δ (.eq
      (.app (.app (.app (.app (.app (.app operations.eliminator A) P) base) method)
        (.app (HOL.weakenCtx Γ operations.successor) index))
        (.app (.app (.app (.app (HOL.weakenCtx Γ operations.consCode) A) index) first) rest))
      (.app (.app (.app (.app method index) first) rest)
        (.app (.app (.app (.app (.app (.app operations.eliminator A) P) base) method) index) rest))) :=
  .eqTrans (.eqApp _ (.eqApp _ (operations.eliminator_apply A P base method)))
    (.eqTrans (.eqAppArg _ (operations.cons_apply A index first rest))
      (.eqTrans (HOL.VectorRecursionProofs.atCons (HOL.weakenCtx Γ operations.selection)
        (HOL.weakenCtx Γ operations.zero) (HOL.weakenCtx Γ operations.successor)
        (HOL.weakenCtx Γ operations.head) (HOL.weakenCtx Γ operations.tail) (HOL.weakenCtx Γ operations.cons)
        base method index first rest choice recursionProof (operations.head_at index first rest headProof)
        (operations.tail_at index first rest tailProof))
        (.eqAppArg _ (.eqSymm (.eqApp rest (.eqApp index (operations.eliminator_apply A P base method)))))))

def assumptions (Γ : HOL.Ctx Base) : List (HOL.Formula Const Γ) :=
  [HOL.SelectionProofs.principle (HOL.weakenCtx Γ operations.selection),
   HOL.NaturalRecursionProofs.statement (HOL.weakenCtx Γ operations.zero)
     (HOL.weakenCtx Γ operations.successor) (operations.vector ⇒ operations.result),
   operations.headLaw, operations.tailLaw]

theorem assumptions_substitute {Γ Ξ : HOL.Ctx Base} (σ : HOL.Subst Const Γ Ξ) :
    (operations.assumptions Γ).map (HOL.subst σ) = operations.assumptions Ξ := by
  simp only [assumptions, List.map_cons, List.map_nil]
  congr 1
  · simp [HOL.SelectionProofs.principle, HOL.SelectionProofs.instanceFormula,
      HOL.subst, HOL.subst_weaken, HOL.subst_weakenCtx, HOL.Subst.lift]
  · congr 1
    · simp [HOL.NaturalRecursionProofs.statement, HOL.NaturalRecursionProofs.subst_body,
        HOL.subst, HOL.subst_weaken, HOL.subst_weakenCtx, HOL.Subst.lift, HOL.Rename.weaken]
    · simp [headLaw, tailLaw, HOL.subst, HOL.subst_weakenCtx, HOL.Subst.lift, HOL.Rename.weaken]

theorem assumptions_eq_closed (Γ : HOL.Ctx Base) :
    operations.assumptions Γ = AnnotatedPredicateReading.assumptions operations.closedAssumptions Γ := by
  let ρ : HOL.Subst Const [] Γ := fun index => nomatch index
  calc
    _ = (operations.assumptions []).map (HOL.subst ρ) := (operations.assumptions_substitute ρ).symm
    _ = _ := by
      change operations.closedAssumptions.map (HOL.subst ρ) = operations.closedAssumptions.map (HOL.weakenCtx Γ)
      apply List.map_congr_left
      intro formula _
      exact HOL.subst_weakenCtx ρ formula

theorem eliminator_reads (Γ : HOL.Ctx Base) :
    AnnotatedPredicateReading.Reads operations.lexicalReading (.const vecEliminateName) (operations.eliminator (Γ := Γ)) := by
  rw [← operations.weaken_eliminator Γ]
  exact .constant rfl

#print axioms nilIota
#print axioms consIota
end Operations

inductive Row where
  | nil | cons
  deriving DecidableEq

namespace Row
variable (operations : Operations Base Const)

def parameters : Row → HOL.Ctx Base
  | .nil => [operations.method, operations.result, operations.motive, operations.elementPredicate]
  | .cons => [operations.vector, operations.element, operations.number, operations.method,
      operations.result, operations.motive, operations.elementPredicate]

def address : Row → Fin Checking.table.length
  | .nil => ⟨2, by decide⟩
  | .cons => ⟨3, by decide⟩

def rawLeft : (row : Row) → Tower.Tm (row.parameters operations).length
  | .nil => vecNilIotaLeft
  | .cons => vecConsIotaLeft

def rawRight : (row : Row) → Tower.Tm (row.parameters operations).length
  | .nil => vecNilIotaRight
  | .cons => vecConsIotaRight

def leftCode : (row : Row) → HOL.Term Const (row.parameters operations) operations.result
  | .nil => .app (.app (.app (.app (.app (.app operations.eliminator
      (.var (.vs (.vs (.vs .vz))))) (.var (.vs (.vs .vz)))) (.var (.vs .vz))) (.var .vz))
      (HOL.weakenCtx _ operations.zero))
      (.app (HOL.weakenCtx _ operations.nilCode) (.var (.vs (.vs (.vs .vz)))))
  | .cons => .app (.app (.app (.app (.app (.app operations.eliminator
      (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))) (.var (.vs (.vs (.vs (.vs (.vs .vz)))))))
      (.var (.vs (.vs (.vs (.vs .vz)))))) (.var (.vs (.vs (.vs .vz)))))
      (.app (HOL.weakenCtx _ operations.successor) (.var (.vs (.vs .vz)))))
      (.app (.app (.app (.app (HOL.weakenCtx _ operations.consCode)
        (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))) (.var (.vs (.vs .vz)))) (.var (.vs .vz))) (.var .vz))

def rightCode : (row : Row) → HOL.Term Const (row.parameters operations) operations.result
  | .nil => .var (.vs .vz)
  | .cons => .app (.app (.app (.app (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))))
      (.var (.vs .vz))) (.var .vz))
      (.app (.app (.app (.app (.app (.app operations.eliminator
        (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))) (.var (.vs (.vs (.vs (.vs (.vs .vz)))))))
        (.var (.vs (.vs (.vs (.vs .vz)))))) (.var (.vs (.vs (.vs .vz))))) (.var (.vs (.vs .vz)))) (.var .vz))

theorem left_reads (row : Row) :
    AnnotatedPredicateReading.Reads operations.lexicalReading (liftTm (row.rawLeft operations)) (row.leftCode operations) := by
  cases row <;> dsimp only [rawLeft, leftCode]
  all_goals repeat' first
    | apply AnnotatedPredicateReading.Reads.application
    | exact operations.eliminator_reads _
    | exact AnnotatedPredicateReading.Reads.constant rfl
    | (convert AnnotatedPredicateReading.Reads.var (lex := operations.lexicalReading) _ using 1; rfl)

theorem right_reads (row : Row) :
    AnnotatedPredicateReading.Reads operations.lexicalReading (liftTm (row.rawRight operations)) (row.rightCode operations) := by
  cases row <;> dsimp only [rawRight, rightCode]
  all_goals repeat' first
    | apply AnnotatedPredicateReading.Reads.application
    | exact operations.eliminator_reads _
    | exact AnnotatedPredicateReading.Reads.constant rfl
    | (convert AnnotatedPredicateReading.Reads.var (lex := operations.lexicalReading) _ using 1; rfl)

def proofFrom (row : Row) {Δ : List (HOL.Formula Const (row.parameters operations))}
    (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx _ operations.selection)))
    (recursion : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx _ operations.zero) (HOL.weakenCtx _ operations.successor) (operations.vector ⇒ operations.result)))
    (head : HOL.ProofSyntax Const Δ operations.headLaw) (tail : HOL.ProofSyntax Const Δ operations.tailLaw) :
    HOL.ProofSyntax Const Δ
    (.eq (row.leftCode operations) (row.rightCode operations)) := by
  cases row with
  | nil =>
    exact operations.nilIota (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))) (.var (.vs .vz))
      (.var .vz) choice recursion
  | cons =>
    exact operations.consIota (.var (.vs (.vs (.vs (.vs (.vs (.vs .vz)))))))
      (.var (.vs (.vs (.vs (.vs (.vs .vz)))))) (.var (.vs (.vs (.vs (.vs .vz)))))
      (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)
      choice recursion head tail

theorem proofFrom_free (row : Row) {Δ : List (HOL.Formula Const (row.parameters operations))}
    (choice : HOL.ProofSyntax Const Δ (HOL.SelectionProofs.principle (HOL.weakenCtx _ operations.selection)))
    (recursion : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.statement
      (HOL.weakenCtx _ operations.zero) (HOL.weakenCtx _ operations.successor) (operations.vector ⇒ operations.result)))
    (head : HOL.ProofSyntax Const Δ operations.headLaw) (tail : HOL.ProofSyntax Const Δ operations.tailLaw)
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree)
    (headFree : head.FunctionExtensionalityFree) (tailFree : tail.FunctionExtensionalityFree) :
    (row.proofFrom operations choice recursion head tail).FunctionExtensionalityFree := by
  cases row <;> simp [proofFrom, Operations.nilIota, Operations.consIota, Operations.eliminator_apply,
    Operations.cons_apply, Operations.head_at, Operations.tail_at,
    HOL.ProofSyntax.FunctionExtensionalityFree, HOL.VectorRecursionProofs.atZero_free,
    HOL.VectorRecursionProofs.atCons_free, choiceFree, recursionFree, headFree, tailFree]

def proof (row : Row) : HOL.ProofSyntax Const (operations.assumptions (row.parameters operations))
    (.eq (row.leftCode operations) (row.rightCode operations)) :=
  row.proofFrom operations
    (.hyp ⟨0, by simp [Operations.assumptions]⟩)
    (.hyp ⟨1, by simp [Operations.assumptions]⟩)
    (.hyp ⟨2, by simp [Operations.assumptions]⟩)
    (.hyp ⟨3, by simp [Operations.assumptions]⟩)

theorem proof_free (row : Row) : (row.proof operations).FunctionExtensionalityFree := by
  exact row.proofFrom_free operations _ _ _ _ True.intro True.intro True.intro True.intro

def template (profile : Programs.ComputationProfiles.Selection) (row : Row) :
    AnnotatedPredicateReading.Roots.Template operations.lexicalReading operations.closedAssumptions
      (Programs.Annotated.church profile).constantType where
  parameters := row.parameters operations
  carrier := operations.result
  rawLeft := row.rawLeft operations
  rawRight := row.rawRight operations
  leftCode := row.leftCode operations
  rightCode := row.rightCode operations
  leftRead := by
    have annotated : elabLeft (Programs.Annotated.church profile).constantType (row.rawLeft operations) =
        liftTm (row.rawLeft operations) := by cases row <;> apply elab_lamFree <;> rfl
    rw [annotated]
    exact row.left_reads operations
  rightRead := by
    have annotated : elabRight (Programs.Annotated.church profile).constantType (row.rawLeft operations)
        (row.rawRight operations) = liftTm (row.rawRight operations) := by cases row <;> apply elab_lamFree <;> rfl
    rw [annotated]
    exact row.right_reads operations
  proof := HOL.ProofSyntax.castIndices (operations.assumptions_eq_closed _) rfl (row.proof operations)

end Row

/-- The two entries cite the existing Vec rows, with their original addresses.
Natural rows require their own interpretation and are not supplied here. -/
def entries (operations : Operations Base Const) (profile : Programs.ComputationProfiles.Selection) :
    AnnotatedPredicateReading.Roots.Table operations.lexicalReading operations.closedAssumptions
      (Programs.Annotated.church profile).constantType Checking.table
  | ⟨2, _⟩ => some ⟨Row.template operations profile .nil, rfl⟩
  | ⟨3, _⟩ => some ⟨Row.template operations profile .cons, rfl⟩
  | _ => none

theorem entries_free (operations : Operations Base Const) (profile : Programs.ComputationProfiles.Selection)
    (address : Fin Checking.table.length) (entry)
    (known : entries operations profile address = some entry) : entry.template.proof.FunctionExtensionalityFree := by
  fin_cases address <;> simp only [entries] at known
  · cases known
  · cases known
  · cases known
    simpa only [Row.template, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using Row.proof_free operations .nil
  · cases known
    simpa only [Row.template, HOL.ProofSyntax.functionExtensionalityFree_castIndices] using Row.proof_free operations .cons

#print axioms Row.left_reads
#print axioms Row.right_reads
#print axioms Row.proof
#print axioms Row.proof_free
#print axioms entries
#print axioms entries_free
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorComputationRows
