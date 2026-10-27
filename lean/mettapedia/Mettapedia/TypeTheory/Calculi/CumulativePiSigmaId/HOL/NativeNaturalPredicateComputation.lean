import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalPredicateTelescope

/-!
# Retained root proofs for the original natural computation rows

The source reading keeps the curried declared eliminator and its original
method order. Finite beta proofs connect that term to the selected root
recursor; the root's recursion theorem then justifies the zero and successor
rows. The source rows are the independently typed original declarations.
This proves their explicit HOL equalities, not general normalization or a
soundness theorem for every dependent judgment.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading.Operations

open Mettapedia.Logic
universe u v
variable {Base : Type u} {Const : HOL.Ty Base → Type v}
    (operations : Operations Base Const) {Γ : HOL.Ctx Base}
    {Δ : List (HOL.Formula Const Γ)}

def flip_apply (method : HOL.Term Const Γ operations.methodType)
    (index : HOL.Term Const Γ operations.number) (value : HOL.Term Const Γ operations.result) :
    HOL.ProofSyntax Const Δ (.eq (.app (.app (operations.flip method) value) index)
      (.app (.app method index) value)) := by
  have first : HOL.ProofSyntax Const Δ
      (.eq (.app (operations.flip method) value)
        (.lam (.app (.app (HOL.weaken method) (.var .vz)) (HOL.weaken value)))) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (.beta value (.lam (.app (.app (HOL.weaken (HOL.weaken method)) (.var .vz)) (.var (.vs .vz)))))
    simp [flip, HOL.instantiate, HOL.subst, HOL.Subst.lift, HOL.Subst.single]
    rfl
  have second : HOL.ProofSyntax Const Δ
      (.eq (.app (.lam (.app (.app (HOL.weaken method) (.var .vz)) (HOL.weaken value))) index)
        (.app (.app method index) value)) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (.beta index (.app (.app (HOL.weaken method) (.var .vz)) (HOL.weaken value)))
    simp [HOL.instantiate, HOL.subst, HOL.Subst.single]
  exact .eqTrans (.eqApp index first) second

def eliminator_apply (family : HOL.Term Const Γ operations.motiveType)
    (base : HOL.Term Const Γ operations.result) (method : HOL.Term Const Γ operations.methodType) :
    HOL.ProofSyntax Const Δ
      (.eq (.app (.app (.app operations.eliminator family) base) method)
        (operations.recursion base method)) := by
  have first : HOL.ProofSyntax Const Δ
      (.eq (.app operations.eliminator family)
        (.lam (.lam (operations.recursion (.var (.vs .vz)) (.var .vz))))) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (.beta family (.lam (.lam (operations.recursion (.var (.vs .vz)) (.var .vz)))))
    simp [eliminator, HOL.instantiate, HOL.subst, subst_recursion, HOL.Subst.lift,
      HOL.Rename.weaken]
  have second : HOL.ProofSyntax Const Δ
      (.eq (.app (.lam (.lam (operations.recursion (.var (.vs .vz)) (.var .vz)))) base)
        (.lam (operations.recursion (HOL.weaken base) (.var .vz)))) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (.beta base (.lam (operations.recursion (.var (.vs .vz)) (.var .vz))))
    simp [HOL.instantiate, HOL.subst, subst_recursion, HOL.Subst.lift, HOL.Subst.single]
    rfl
  have third : HOL.ProofSyntax Const Δ
      (.eq (.app (.lam (operations.recursion (HOL.weaken base) (.var .vz))) method)
        (operations.recursion base method)) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (.beta method (operations.recursion (HOL.weaken base) (.var .vz)))
    simp [HOL.instantiate, subst_recursion, HOL.subst, HOL.Subst.single]
  exact .eqTrans (.eqApp method (.eqApp base first)) (.eqTrans (.eqApp method second) third)

def zeroIota (family : HOL.Term Const Γ operations.motiveType)
    (base : HOL.Term Const Γ operations.result) (method : HOL.Term Const Γ operations.methodType)
    (choice : HOL.ProofSyntax Const Δ
      (HOL.SelectionProofs.principle (HOL.weakenCtx Γ operations.selection)))
    (recursionProof : HOL.ProofSyntax Const Δ
      (HOL.NaturalRecursionProofs.statement (HOL.weakenCtx Γ operations.zero)
        (HOL.weakenCtx Γ operations.successor) operations.result)) :
    HOL.ProofSyntax Const Δ
      (.eq (.app (.app (.app (.app operations.eliminator family) base) method)
          (HOL.weakenCtx Γ operations.zero)) base) :=
  .eqTrans (.eqApp (HOL.weakenCtx Γ operations.zero) (operations.eliminator_apply family base method))
    (HOL.NaturalRecursionProofs.atZero (HOL.weakenCtx Γ operations.selection)
      (HOL.weakenCtx Γ operations.zero) (HOL.weakenCtx Γ operations.successor)
      base (operations.flip method) choice recursionProof)

def successorIota (family : HOL.Term Const Γ operations.motiveType)
    (base : HOL.Term Const Γ operations.result) (method : HOL.Term Const Γ operations.methodType)
    (index : HOL.Term Const Γ operations.number)
    (choice : HOL.ProofSyntax Const Δ
      (HOL.SelectionProofs.principle (HOL.weakenCtx Γ operations.selection)))
    (recursionProof : HOL.ProofSyntax Const Δ
      (HOL.NaturalRecursionProofs.statement (HOL.weakenCtx Γ operations.zero)
        (HOL.weakenCtx Γ operations.successor) operations.result)) :
    HOL.ProofSyntax Const Δ
      (.eq (.app (.app (.app (.app operations.eliminator family) base) method)
          (.app (HOL.weakenCtx Γ operations.successor) index))
        (.app (.app method index)
          (.app (.app (.app (.app operations.eliminator family) base) method) index))) :=
  .eqTrans (.eqApp (.app (HOL.weakenCtx Γ operations.successor) index)
    (operations.eliminator_apply family base method))
    (.eqTrans (HOL.NaturalRecursionProofs.atSuccessor (HOL.weakenCtx Γ operations.selection)
      (HOL.weakenCtx Γ operations.zero) (HOL.weakenCtx Γ operations.successor)
      base (operations.flip method) index choice recursionProof)
      (.eqTrans (operations.flip_apply method index (.app (operations.recursion base method) index))
        (.eqAppArg (.app method index)
          (.eqSymm (.eqApp index (operations.eliminator_apply family base method))))))

def zero_row_proof {Δ : List (HOL.Formula Const operations.parameters)}
    (choice : HOL.ProofSyntax Const Δ
      (HOL.SelectionProofs.principle (HOL.weakenCtx operations.parameters operations.selection)))
    (recursionProof : HOL.ProofSyntax Const Δ
      (HOL.NaturalRecursionProofs.statement (HOL.weakenCtx operations.parameters operations.zero)
        (HOL.weakenCtx operations.parameters operations.successor) operations.result)) :
    HOL.ProofSyntax Const Δ (.eq operations.zeroLeft operations.zeroRight) :=
  operations.zeroIota (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz) choice recursionProof

def successor_row_proof {Δ : List (HOL.Formula Const operations.successorParameters)}
    (choice : HOL.ProofSyntax Const Δ
      (HOL.SelectionProofs.principle (HOL.weakenCtx operations.successorParameters operations.selection)))
    (recursionProof : HOL.ProofSyntax Const Δ
      (HOL.NaturalRecursionProofs.statement (HOL.weakenCtx operations.successorParameters operations.zero)
        (HOL.weakenCtx operations.successorParameters operations.successor) operations.result)) :
    HOL.ProofSyntax Const Δ (.eq operations.successorLeft operations.successorRight) := by
  apply HOL.ProofSyntax.castIndices rfl ?_
    (operations.successorIota (.var (.vs (.vs (.vs .vz)))) (.var (.vs (.vs .vz)))
      (.var (.vs .vz)) (.var .vz) choice recursionProof)
  simp [successorLeft, successorRight, atParameters, HOL.weaken, HOL.rename, HOL.Rename.weaken]


theorem flip_apply_free (method : HOL.Term Const Γ operations.methodType)
    (index : HOL.Term Const Γ operations.number) (value : HOL.Term Const Γ operations.result) :
    (operations.flip_apply (Δ := Δ) method index value).FunctionExtensionalityFree := by
  simp [flip_apply, HOL.ProofSyntax.FunctionExtensionalityFree]

theorem eliminator_apply_free (family : HOL.Term Const Γ operations.motiveType)
    (base : HOL.Term Const Γ operations.result) (method : HOL.Term Const Γ operations.methodType) :
    (operations.eliminator_apply (Δ := Δ) family base method).FunctionExtensionalityFree := by
  simp [eliminator_apply, HOL.ProofSyntax.FunctionExtensionalityFree]

theorem zeroIota_free (family : HOL.Term Const Γ operations.motiveType)
    (base : HOL.Term Const Γ operations.result) (method : HOL.Term Const Γ operations.methodType)
    (choice : HOL.ProofSyntax Const Δ
      (HOL.SelectionProofs.principle (HOL.weakenCtx Γ operations.selection)))
    (recursionProof : HOL.ProofSyntax Const Δ
      (HOL.NaturalRecursionProofs.statement (HOL.weakenCtx Γ operations.zero)
        (HOL.weakenCtx Γ operations.successor) operations.result))
    (choiceFree : choice.FunctionExtensionalityFree)
    (recursionFree : recursionProof.FunctionExtensionalityFree) :
    (operations.zeroIota family base method choice recursionProof).FunctionExtensionalityFree := by
  simp [zeroIota, HOL.NaturalRecursionProofs.atZero, HOL.ProofSyntax.FunctionExtensionalityFree,
    eliminator_apply_free, HOL.NaturalRecursionProofs.computation_free, choiceFree, recursionFree]

theorem successorIota_free (family : HOL.Term Const Γ operations.motiveType)
    (base : HOL.Term Const Γ operations.result) (method : HOL.Term Const Γ operations.methodType)
    (index : HOL.Term Const Γ operations.number)
    (choice : HOL.ProofSyntax Const Δ
      (HOL.SelectionProofs.principle (HOL.weakenCtx Γ operations.selection)))
    (recursionProof : HOL.ProofSyntax Const Δ
      (HOL.NaturalRecursionProofs.statement (HOL.weakenCtx Γ operations.zero)
        (HOL.weakenCtx Γ operations.successor) operations.result))
    (choiceFree : choice.FunctionExtensionalityFree)
    (recursionFree : recursionProof.FunctionExtensionalityFree) :
    (operations.successorIota family base method index choice recursionProof).FunctionExtensionalityFree := by
  simp [successorIota, HOL.NaturalRecursionProofs.atSuccessor, HOL.ProofSyntax.FunctionExtensionalityFree,
    eliminator_apply_free, flip_apply_free, HOL.NaturalRecursionProofs.computation_free,
    choiceFree, recursionFree]

def method_at (family : HOL.Term Const Γ operations.motiveType)
    (method : HOL.Term Const Γ operations.methodType)
    (index : HOL.Term Const Γ operations.number) (value : HOL.Term Const Γ operations.result)
    (methodTyped : HOL.ProofSyntax Const Δ (.app (operations.methodPredicate family) method))
    (valueTyped : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.holds family index value)) :
    HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.holds family
      (.app (HOL.weakenCtx Γ operations.successor) index) (.app (.app method index) value)) := by
  have indexTyped : HOL.ProofSyntax Const Δ
      (.app (HOL.PredicateProducts.full operations.number) index) :=
    .impE (.eqPropER (.beta index .top)) .topI
  have first := HOL.PredicateProducts.eliminate (HOL.PredicateProducts.full operations.number)
    (HOL.PredicateProducts.pi (.app (HOL.weaken family) (.var .vz))
      (.app (HOL.weaken (HOL.weaken family))
        (.app (HOL.weakenCtx _ operations.successor) (.var (.vs .vz)))))
    method index methodTyped indexTyped
  have first' : HOL.ProofSyntax Const Δ
      (.app (HOL.PredicateProducts.pi (.app family index)
        (.app (HOL.weaken family) (.app (HOL.weakenCtx _ operations.successor) (HOL.weaken index))))
        (.app method index)) := by
    apply HOL.ProofSyntax.castIndices rfl ?_ first
    simp [HOL.instantiate, HOL.subst, HOL.Subst.single, HOL.Subst.lift]
    rfl
  apply HOL.ProofSyntax.castIndices rfl ?_
    (HOL.PredicateProducts.eliminate (.app family index)
      (.app (HOL.weaken family) (.app (HOL.weakenCtx _ operations.successor) (HOL.weaken index)))
      (.app method index) value first' valueTyped)
  simp [HOL.NaturalRecursionProofs.holds, HOL.instantiate, HOL.subst]

/-- The guarded interpretation of the original method type entails the
exact premise used by the root recursor, including its argument adapter. -/
def method_preserves (family : HOL.Term Const Γ operations.motiveType)
    (method : HOL.Term Const Γ operations.methodType)
    (methodTyped : HOL.ProofSyntax Const Δ (.app (operations.methodPredicate family) method)) :
    HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.methodPreserves
      (HOL.weakenCtx Γ operations.successor) (operations.flip method) family) := by
  apply HOL.ProofSyntax.allI
  apply HOL.ProofSyntax.allI
  apply HOL.ProofSyntax.impI
  let premise := HOL.NaturalRecursionProofs.holds (HOL.weaken (HOL.weaken family))
    (.var (.vs .vz)) (.var .vz)
  have imported : HOL.ProofSyntax Const (premise :: HOL.weakenHyps (HOL.weakenHyps Δ))
      (.app (operations.methodPredicate (HOL.weaken (HOL.weaken family)))
        (HOL.weaken (HOL.weaken method))) := by
    apply HOL.ProofSyntax.castIndices rfl ?_
      (HOL.ProofSyntax.prepend premise ((methodTyped.rename HOL.Rename.weaken).rename HOL.Rename.weaken))
    simp only [HOL.rename, rename_methodPredicate]
    rfl
  have applied := operations.method_at (HOL.weaken (HOL.weaken family))
    (HOL.weaken (HOL.weaken method)) (.var (.vs .vz)) (.var .vz) imported (.hyp 0)
  have adapted := HOL.ProofSyntax.impE
    (.eqPropER (.eqAppArg
      (.app (HOL.weaken (HOL.weaken family))
        (.app (HOL.weakenCtx _ operations.successor) (.var (.vs .vz))))
      (operations.flip_apply (HOL.weaken (HOL.weaken method)) (.var (.vs .vz)) (.var .vz)))) applied
  apply HOL.ProofSyntax.castIndices rfl ?_ adapted
  simp only [HOL.NaturalRecursionProofs.holds, HOL.weaken, rename_flip, HOL.rename_weakenCtx]

/-- The original method predicate and base guard type the curried declared
eliminator at its dependent result predicate. The root commitments remain
explicit retained proofs. -/
def result_typed (family : HOL.Term Const Γ operations.motiveType)
    (base : HOL.Term Const Γ operations.result) (method : HOL.Term Const Γ operations.methodType)
    (choice : HOL.ProofSyntax Const Δ
      (HOL.SelectionProofs.principle (HOL.weakenCtx Γ operations.selection)))
    (recursionProof : HOL.ProofSyntax Const Δ
      (HOL.NaturalRecursionProofs.statement (HOL.weakenCtx Γ operations.zero)
        (HOL.weakenCtx Γ operations.successor) operations.result))
    (inductionProof : HOL.ProofSyntax Const Δ
      (HOL.NaturalRecursionProofs.inductionPrinciple (HOL.weakenCtx Γ operations.zero)
        (HOL.weakenCtx Γ operations.successor)))
    (baseTyped : HOL.ProofSyntax Const Δ
      (HOL.NaturalRecursionProofs.holds family (HOL.weakenCtx Γ operations.zero) base))
    (methodTyped : HOL.ProofSyntax Const Δ (.app (operations.methodPredicate family) method)) :
    HOL.ProofSyntax Const Δ (.app (operations.resultPredicate family)
      (.app (.app (.app operations.eliminator family) base) method)) := by
  have every := HOL.NaturalRecursionProofs.dependent (HOL.weakenCtx Γ operations.selection)
    (HOL.weakenCtx Γ operations.zero) (HOL.weakenCtx Γ operations.successor)
    base (operations.flip method) family choice recursionProof inductionProof baseTyped
    (operations.method_preserves family method methodTyped)
  have atIndex := HOL.ContextualTrinity.instantiateFresh (every.rename HOL.Rename.weaken)
  have functionTyped : HOL.ProofSyntax Const Δ
      (.app (operations.resultPredicate family) (operations.recursion base method)) :=
    HOL.PredicateProducts.introduce (HOL.PredicateProducts.full operations.number)
      (.app (HOL.weaken family) (.var .vz)) (operations.recursion base method)
      (atIndex.prepend _)
  exact .impE (.eqPropER (.eqAppArg (operations.resultPredicate family)
    (operations.eliminator_apply family base method))) functionTyped

theorem method_at_free (family : HOL.Term Const Γ operations.motiveType)
    (method : HOL.Term Const Γ operations.methodType)
    (index : HOL.Term Const Γ operations.number) (value : HOL.Term Const Γ operations.result)
    (methodTyped : HOL.ProofSyntax Const Δ (.app (operations.methodPredicate family) method))
    (valueTyped : HOL.ProofSyntax Const Δ (HOL.NaturalRecursionProofs.holds family index value))
    (methodFree : methodTyped.FunctionExtensionalityFree)
    (valueFree : valueTyped.FunctionExtensionalityFree) :
    (operations.method_at family method index value methodTyped valueTyped).FunctionExtensionalityFree := by
  simp [method_at, HOL.ProofSyntax.FunctionExtensionalityFree,
    HOL.PredicateProducts.eliminate_free, methodFree, valueFree]

theorem method_preserves_free (family : HOL.Term Const Γ operations.motiveType)
    (method : HOL.Term Const Γ operations.methodType)
    (methodTyped : HOL.ProofSyntax Const Δ (.app (operations.methodPredicate family) method))
    (methodFree : methodTyped.FunctionExtensionalityFree) :
    (operations.method_preserves family method methodTyped).FunctionExtensionalityFree := by
  simp [method_preserves, HOL.ProofSyntax.FunctionExtensionalityFree,
    HOL.ProofSyntax.prepend, method_at_free, flip_apply_free, methodFree]

theorem result_typed_free (family : HOL.Term Const Γ operations.motiveType)
    (base : HOL.Term Const Γ operations.result) (method : HOL.Term Const Γ operations.methodType)
    (choice : HOL.ProofSyntax Const Δ
      (HOL.SelectionProofs.principle (HOL.weakenCtx Γ operations.selection)))
    (recursionProof : HOL.ProofSyntax Const Δ
      (HOL.NaturalRecursionProofs.statement (HOL.weakenCtx Γ operations.zero)
        (HOL.weakenCtx Γ operations.successor) operations.result))
    (inductionProof : HOL.ProofSyntax Const Δ
      (HOL.NaturalRecursionProofs.inductionPrinciple (HOL.weakenCtx Γ operations.zero)
        (HOL.weakenCtx Γ operations.successor)))
    (baseTyped : HOL.ProofSyntax Const Δ
      (HOL.NaturalRecursionProofs.holds family (HOL.weakenCtx Γ operations.zero) base))
    (methodTyped : HOL.ProofSyntax Const Δ (.app (operations.methodPredicate family) method))
    (choiceFree : choice.FunctionExtensionalityFree)
    (recursionFree : recursionProof.FunctionExtensionalityFree)
    (inductionFree : inductionProof.FunctionExtensionalityFree)
    (baseFree : baseTyped.FunctionExtensionalityFree)
    (methodFree : methodTyped.FunctionExtensionalityFree) :
    (operations.result_typed family base method choice recursionProof inductionProof baseTyped methodTyped).FunctionExtensionalityFree := by
  simp [result_typed, HOL.ProofSyntax.FunctionExtensionalityFree, HOL.ProofSyntax.prepend,
    HOL.PredicateProducts.introduce, HOL.PredicateProducts.beta_free, HOL.ContextualTrinity.instantiateFresh,
    HOL.ContextualTrinity.castConclusion, eliminator_apply_free,
    HOL.NaturalRecursionProofs.dependent, HOL.NaturalRecursionProofs.invariant_free,
    HOL.NaturalRecursionProofs.computation_free, method_preserves_free,
    choiceFree, recursionFree, inductionFree, baseFree, methodFree]

#print axioms result_typed_free
#print axioms result_typed
#print axioms method_at
#print axioms method_preserves
#print axioms eliminator_apply_free
#print axioms successorIota_free

#print axioms flip_apply
#print axioms eliminator_apply
#print axioms zero_row_proof
#print axioms successor_row_proof

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading.Operations
