import Mettapedia.Logic.HOL.FiniteConstructorReadout
import Mettapedia.Logic.HOL.ConstructorProjections
import Mettapedia.Logic.HOL.NaturalRecursionProofs

/-!
# Vector constructor programs in a recursive-space carrier

The cons payload uses the existing constructor encoder with fields in the
original index/head order. Its child function returns the tail at zero and
bottom at successors. Payload observation and the zero child equation derive
field injectivity from the underlying recursive-space constructor fact.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.RawVectorConstructors

universe u v

def fields {Base : Type u} (number element : Ty Base) : List (List (Ty Base)) := [[], [number, element]]

structure Signature (Base : Type u) (Const : Ty Base → Type v) where
  number : Ty Base
  element : Ty Base
  space : Ty Base
  zero : ClosedTerm Const number
  successor : ClosedTerm Const (number ⇒ number)
  bottom : ClosedTerm Const space
  construct : ClosedTerm Const (number ⇒ FiniteConstructorEncoding.payloadType (fields number element) ⇒
    (number ⇒ space) ⇒ space)
  selection : ClosedTerm Const (SelectionProofs.Selection (number ⇒ space))

namespace Signature

variable {Base : Type u} {Const : Ty Base → Type v} (signature : Signature Base Const)
    {Γ Ξ : Ctx Base}

def childStep : Term Const Γ (NaturalRecursionProofs.Method signature.number signature.space) :=
  .lam (.lam (weakenCtx _ signature.bottom))

def children (tail : Term Const Γ signature.space) : Term Const Γ (signature.number ⇒ signature.space) :=
  NaturalRecursionProofs.recursor (weakenCtx Γ signature.selection) (weakenCtx Γ signature.zero)
    (weakenCtx Γ signature.successor) tail signature.childStep

def nil : Term Const Γ signature.space :=
  ConstructorProjections.apply (weakenCtx Γ signature.construct) (weakenCtx Γ signature.zero)
    (FiniteConstructorEncoding.encode (fields signature.number signature.element) ⟨0, by change 0 < 2; decide⟩ PUnit.unit)
    (.lam (weakenCtx _ signature.bottom))

def consAt (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.space) : Term Const Γ signature.space :=
  ConstructorProjections.apply (weakenCtx Γ signature.construct) (.app (weakenCtx Γ signature.successor) (weakenCtx Γ signature.zero))
    (FiniteConstructorEncoding.encode (fields signature.number signature.element) ⟨1, by change 1 < 2; decide⟩ (index, head, PUnit.unit))
    (signature.children tail)

def cons : Term Const Γ (signature.number ⇒ signature.element ⇒ signature.space ⇒ signature.space) :=
  .lam (.lam (.lam (signature.consAt (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

@[simp] theorem subst_childStep (σ : Subst Const Γ Ξ) : subst σ (signature.childStep (Γ := Γ)) = signature.childStep := by
  simp [childStep, subst, subst_weakenCtx]

@[simp] theorem subst_children (σ : Subst Const Γ Ξ) (tail : Term Const Γ signature.space) :
    subst σ (signature.children tail) = signature.children (subst σ tail) := by
  simp [children, NaturalRecursionProofs.recursor, SelectionProofs.selected, subst, subst_weakenCtx]

@[simp] theorem subst_consAt (σ : Subst Const Γ Ξ) (index : Term Const Γ signature.number)
    (head : Term Const Γ signature.element) (tail : Term Const Γ signature.space) :
    subst σ (signature.consAt index head tail) = signature.consAt (subst σ index) (subst σ head) (subst σ tail) := by
  simp [consAt, FiniteConstructorEncoding.encode_subst, FiniteConstructorEncoding.substituteArguments,
    fields, subst, subst_weakenCtx]

@[simp] theorem subst_cons (σ : Subst Const Γ Ξ) : subst σ (signature.cons (Γ := Γ)) = signature.cons := by
  simp [cons, subst, Subst.lift, Rename.weaken]

variable {Δ : List (Formula Const Γ)}

def childStep_apply (prior : Term Const Γ signature.space) (index : Term Const Γ signature.number) :
    ProofSyntax Const Δ (.eq (.app (.app signature.childStep prior) index) (weakenCtx Γ signature.bottom)) := by
  have first : ProofSyntax Const Δ (.eq (.app signature.childStep prior)
      (.lam (weakenCtx _ signature.bottom))) := by
    apply ProofSyntax.castIndices rfl ?_ (.beta prior (.lam (σ := signature.number) (weakenCtx _ signature.bottom)))
    simp [childStep, instantiate, subst]
  have second : ProofSyntax Const Δ (.eq (.app (.lam (weakenCtx _ signature.bottom)) index)
      (weakenCtx Γ signature.bottom)) := by
    apply ProofSyntax.castIndices rfl ?_ (.beta index (weakenCtx _ signature.bottom))
    simp [instantiate]
  exact .eqTrans (.eqApp index first) second

def children_zero (tail : Term Const Γ signature.space)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ signature.selection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement (weakenCtx Γ signature.zero)
      (weakenCtx Γ signature.successor) signature.space)) :
    ProofSyntax Const Δ (.eq (.app (signature.children tail) (weakenCtx Γ signature.zero)) tail) :=
  NaturalRecursionProofs.atZero (weakenCtx Γ signature.selection) (weakenCtx Γ signature.zero)
    (weakenCtx Γ signature.successor) tail signature.childStep choice recursion

def children_successor (tail : Term Const Γ signature.space) (index : Term Const Γ signature.number)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ signature.selection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement (weakenCtx Γ signature.zero)
      (weakenCtx Γ signature.successor) signature.space)) :
    ProofSyntax Const Δ (.eq (.app (signature.children tail) (.app (weakenCtx Γ signature.successor) index))
      (weakenCtx Γ signature.bottom)) :=
  .eqTrans (NaturalRecursionProofs.atSuccessor (weakenCtx Γ signature.selection) (weakenCtx Γ signature.zero)
    (weakenCtx Γ signature.successor) tail signature.childStep index choice recursion)
    (signature.childStep_apply (.app (signature.children tail) index) index)

def cons_apply (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.space) :
    ProofSyntax Const Δ (.eq (.app (.app (.app signature.cons index) head) tail) (signature.consAt index head tail)) := by
  have first : ProofSyntax Const Δ (.eq (.app signature.cons index)
      (.lam (.lam (signature.consAt (weaken (weaken index)) (.var (.vs .vz)) (.var .vz))))) := by
    apply ProofSyntax.castIndices rfl ?_
      (.beta index (.lam (.lam (signature.consAt (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)))))
    simp [cons, instantiate, subst, Subst.single, Subst.lift, Rename.weaken]
    simp only [weaken, rename_comp, Rename.weaken]
  have second : ProofSyntax Const Δ
      (.eq (.app (.lam (.lam (signature.consAt (weaken (weaken index)) (.var (.vs .vz)) (.var .vz)))) head)
        (.lam (signature.consAt (weaken index) (weaken head) (.var .vz)))) := by
    apply ProofSyntax.castIndices rfl ?_
      (.beta head (.lam (signature.consAt (weaken (weaken index)) (.var (.vs .vz)) (.var .vz))))
    simp [instantiate, subst, Subst.single, Subst.lift]
    rfl
  have third : ProofSyntax Const Δ (.eq (.app (.lam (signature.consAt (weaken index) (weaken head) (.var .vz))) tail)
      (signature.consAt index head tail)) := by
    apply ProofSyntax.castIndices rfl ?_ (.beta tail (signature.consAt (weaken index) (weaken head) (.var .vz)))
    simp [instantiate, subst, Subst.single]
  exact .eqTrans (.eqApp tail (.eqApp head first)) (.eqTrans (.eqApp tail second) third)

def recover (index index' : Term Const Γ signature.number) (head head' : Term Const Γ signature.element)
    (tail tail' : Term Const Γ signature.space)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ signature.selection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement (weakenCtx Γ signature.zero)
      (weakenCtx Γ signature.successor) signature.space))
    (injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective (weakenCtx Γ signature.construct)))
    (same : ProofSyntax Const Δ (.eq (signature.consAt index' head' tail') (signature.consAt index head tail))) :
    ProofSyntax Const Δ (.and (.eq head' head) (.eq tail' tail)) := by
  let tag := Term.app (weakenCtx Γ signature.successor) (weakenCtx Γ signature.zero)
  let fields := RawVectorConstructors.fields signature.number signature.element
  let original := FiniteConstructorEncoding.encode fields ⟨1, by change 1 < 2; decide⟩ (index, head, PUnit.unit)
  let candidate := FiniteConstructorEncoding.encode fields ⟨1, by change 1 < 2; decide⟩ (index', head', PUnit.unit)
  have raw := ProofSyntax.impE
    (ConstructorProjections.compare (weakenCtx Γ signature.construct) tag tag original candidate
      (signature.children tail) (signature.children tail')
      (ConstructorProjections.specialize (weakenCtx Γ signature.construct) tag original (signature.children tail) injectivity)) same
  have headEqual := FiniteConstructorEncoding.recover_field fields ⟨1, by change 1 < 2; decide⟩ (.vs .vz)
    (index', head', PUnit.unit) (index, head, PUnit.unit) (ProofSyntax.andEL raw)
  have tailEqual := ProofSyntax.eqTrans (ProofSyntax.eqSymm (signature.children_zero tail' choice recursion))
    (ProofSyntax.eqTrans (ProofSyntax.eqApp (weakenCtx Γ signature.zero) (ProofSyntax.andER raw))
      (signature.children_zero tail choice recursion))
  exact .andI headEqual tailEqual

theorem children_zero_free (tail : Term Const Γ signature.space)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ signature.selection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement (weakenCtx Γ signature.zero)
      (weakenCtx Γ signature.successor) signature.space))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree) :
    (signature.children_zero tail choice recursion).FunctionExtensionalityFree := by
  exact NaturalRecursionProofs.computation_free _ _ _ _ _ choice recursion choiceFree recursionFree

theorem children_successor_free (tail : Term Const Γ signature.space) (index : Term Const Γ signature.number)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ signature.selection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement (weakenCtx Γ signature.zero)
      (weakenCtx Γ signature.successor) signature.space))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree) :
    (signature.children_successor tail index choice recursion).FunctionExtensionalityFree := by
  simp [children_successor, NaturalRecursionProofs.atSuccessor, childStep_apply,
    ProofSyntax.FunctionExtensionalityFree, NaturalRecursionProofs.computation_free, choiceFree, recursionFree]

theorem cons_apply_free (index : Term Const Γ signature.number) (head : Term Const Γ signature.element)
    (tail : Term Const Γ signature.space) :
    (signature.cons_apply (Δ := Δ) index head tail).FunctionExtensionalityFree := by
  simp [cons_apply, ProofSyntax.FunctionExtensionalityFree]

theorem recover_free (index index' : Term Const Γ signature.number) (head head' : Term Const Γ signature.element)
    (tail tail' : Term Const Γ signature.space)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ signature.selection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement (weakenCtx Γ signature.zero)
      (weakenCtx Γ signature.successor) signature.space))
    (injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective (weakenCtx Γ signature.construct)))
    (same : ProofSyntax Const Δ (.eq (signature.consAt index' head' tail') (signature.consAt index head tail)))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree)
    (injectivityFree : injectivity.FunctionExtensionalityFree) (sameFree : same.FunctionExtensionalityFree) :
    (signature.recover index index' head head' tail tail' choice recursion injectivity same).FunctionExtensionalityFree := by
  simp only [recover, ProofSyntax.FunctionExtensionalityFree]
  constructor
  · apply FiniteConstructorEncoding.recover_field_free
    simp [ConstructorProjections.compare, ConstructorProjections.specialize,
      ProofSyntax.FunctionExtensionalityFree, injectivityFree, sameFree]
  · refine ⟨children_zero_free signature _ _ _ choiceFree recursionFree, ?_,
      children_zero_free signature _ _ _ choiceFree recursionFree⟩
    simp [ConstructorProjections.compare, ConstructorProjections.specialize,
      ProofSyntax.FunctionExtensionalityFree, injectivityFree, sameFree]

def cons_components (index index' : Term Const Γ signature.number) (head head' : Term Const Γ signature.element)
    (tail tail' : Term Const Γ signature.space)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ signature.selection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement (weakenCtx Γ signature.zero)
      (weakenCtx Γ signature.successor) signature.space))
    (injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective (weakenCtx Γ signature.construct)))
    (same : ProofSyntax Const Δ (.eq
      (ConstructorProjections.apply signature.cons index' head' tail')
      (ConstructorProjections.apply signature.cons index head tail))) :
    ProofSyntax Const Δ (.and (.eq head' head) (.eq tail' tail)) :=
  signature.recover index index' head head' tail tail' choice recursion injectivity
    (.eqTrans (.eqSymm (signature.cons_apply index' head' tail'))
      (.eqTrans same (signature.cons_apply index head tail)))

theorem cons_components_free (index index' : Term Const Γ signature.number) (head head' : Term Const Γ signature.element)
    (tail tail' : Term Const Γ signature.space)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle (weakenCtx Γ signature.selection)))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement (weakenCtx Γ signature.zero)
      (weakenCtx Γ signature.successor) signature.space))
    (injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective (weakenCtx Γ signature.construct)))
    (same : ProofSyntax Const Δ (.eq
      (ConstructorProjections.apply signature.cons index' head' tail')
      (ConstructorProjections.apply signature.cons index head tail)))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree)
    (injectivityFree : injectivity.FunctionExtensionalityFree) (sameFree : same.FunctionExtensionalityFree) :
    (signature.cons_components index index' head head' tail tail' choice recursion injectivity same).FunctionExtensionalityFree := by
  apply signature.recover_free _ _ _ _ _ _ _ _ _ _ choiceFree recursionFree injectivityFree
  exact ⟨signature.cons_apply_free _ _ _, sameFree, signature.cons_apply_free _ _ _⟩

def assumptions (Γ : Ctx Base) : List (Formula Const Γ) :=
  [SelectionProofs.principle (weakenCtx Γ signature.selection),
   NaturalRecursionProofs.statement (weakenCtx Γ signature.zero) (weakenCtx Γ signature.successor) signature.space,
   ConstructorProjections.fieldInjective (weakenCtx Γ signature.construct)]

theorem assumptions_substitute (σ : Subst Const Γ Ξ) :
    (signature.assumptions Γ).map (subst σ) = signature.assumptions Ξ := by
  simp only [assumptions, List.map_cons, List.map_nil]
  congr 1
  · simp [SelectionProofs.principle, SelectionProofs.instanceFormula, subst, subst_weaken, subst_weakenCtx, Subst.lift]
  · congr 1
    · simp [NaturalRecursionProofs.statement, NaturalRecursionProofs.subst_body,
        subst, subst_weaken, subst_weakenCtx, Subst.lift, Rename.weaken]
    · simp [subst_weakenCtx]

theorem assumptions_weaken (Γ : Ctx Base) (type : Ty Base) :
    weakenHyps (σ := type) (signature.assumptions Γ) = signature.assumptions (type :: Γ) := by
  let ρ : Subst Const Γ (type :: Γ) := Subst.ofRename Rename.weaken
  calc
    _ = (signature.assumptions Γ).map (subst ρ) := by
      apply List.map_congr_left
      intro formula _
      exact (subst_ofRename Rename.weaken formula).symm
    _ = _ := signature.assumptions_substitute ρ

theorem rename_cons (ρ : Rename Base Γ Ξ) : rename ρ (signature.cons (Γ := Γ)) = signature.cons := by
  simpa only [subst_ofRename] using signature.subst_cons (Subst.ofRename ρ)

theorem weakenCtx_cons (context : Ctx Base) :
    HOL.weakenCtx context (signature.cons (Γ := [])) = signature.cons (Γ := context) := by
  induction context with
  | nil => rfl
  | cons type context ih =>
    rw [HOL.weakenCtx_cons, ih]
    exact signature.rename_cons Rename.weaken

/-- The actual encoded cons function inherits head/tail injectivity. The
background concerns only the natural child recursor and raw constructor. -/
def field_injective : ProofSyntax Const (signature.assumptions Γ) (ConstructorProjections.fieldInjective signature.cons) := by
  let Ω := signature.space :: signature.element :: signature.number ::
    signature.space :: signature.element :: signature.number :: Γ
  let n : Term Const Ω signature.number := .var (.vs (.vs (.vs (.vs (.vs .vz)))))
  let h : Term Const Ω signature.element := .var (.vs (.vs (.vs (.vs .vz))))
  let t : Term Const Ω signature.space := .var (.vs (.vs (.vs .vz)))
  let n' : Term Const Ω signature.number := .var (.vs (.vs .vz))
  let h' : Term Const Ω signature.element := .var (.vs .vz)
  let t' : Term Const Ω signature.space := .var .vz
  let equation := Term.eq (ConstructorProjections.apply signature.cons n' h' t')
    (ConstructorProjections.apply signature.cons n h t)
  have localProof : ProofSyntax Const (equation :: signature.assumptions Ω) (.and (.eq h' h) (.eq t' t)) :=
    signature.cons_components n n' h h' t t'
      (.hyp ⟨1, by simp [assumptions]⟩) (.hyp ⟨2, by simp [assumptions]⟩)
      (.hyp ⟨3, by simp [assumptions]⟩) (.hyp ⟨0, by simp⟩)
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  apply ProofSyntax.castIndices ?_ ?_ localProof
  · simp only [assumptions_weaken]
    simp only [equation, ConstructorProjections.apply, weaken, rename, rename_cons,
      Ω, n, h, t, n', h', t', Rename.weaken]
  · simp only [weaken, rename, h', h, t', t, Rename.weaken]

theorem field_injective_free : (signature.field_injective (Γ := Γ)).FunctionExtensionalityFree := by
  unfold field_injective
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact signature.cons_components_free _ _ _ _ _ _ _ _ _ _ True.intro True.intro True.intro True.intro

#print axioms subst_cons
#print axioms children_zero
#print axioms children_successor
#print axioms recover
#print axioms cons_components_free
#print axioms field_injective
#print axioms field_injective_free
end Signature
end Mettapedia.Logic.HOL.RawVectorConstructors
