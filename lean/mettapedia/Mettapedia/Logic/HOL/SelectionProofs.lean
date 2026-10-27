import Mettapedia.Logic.HOL.PredicateFixedPoint
import Mettapedia.Logic.HOL.ContextualTrinity

/-!
# Retained HOL proofs for selection from an inhabited specification

The selection principle and the existence of a witness are explicit proof
inputs. The output concerns the actual term obtained by applying the supplied
selection operator to the specification. No choice principle or existence
claim is added by the proof constructor itself.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.SelectionProofs

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {α : Ty Base}

abbrev Selection (α : Ty Base) := (α ⇒ .prop) ⇒ α

def instanceFormula (selection : Term Const Γ (Selection α))
    (predicate : Term Const Γ (α ⇒ .prop)) : Formula Const Γ :=
  .all (.imp (.app (weaken predicate) (.var .vz))
    (weaken (.app predicate (.app selection predicate))))

def principle (selection : Term Const Γ (Selection α)) : Formula Const Γ :=
  .all (instanceFormula (weaken selection) (.var .vz))

def inhabited (predicate : Term Const Γ (α ⇒ .prop)) : Formula Const Γ :=
  .ex (.app (weaken predicate) (.var .vz))

def selected (selection : Term Const Γ (Selection α))
    (body : Formula Const (α :: Γ)) : Term Const Γ α :=
  .app selection (.lam body)

@[simp] theorem subst_instanceFormula {Γ' : Ctx Base} (substitution : Subst Const Γ Γ')
    (selection : Term Const Γ (Selection α)) (predicate : Term Const Γ (α ⇒ .prop)) :
    HOL.subst substitution (instanceFormula selection predicate) =
      instanceFormula (HOL.subst substitution selection) (HOL.subst substitution predicate) := by
  simp [instanceFormula, HOL.subst, weaken, HOL.subst_rename, HOL.rename_subst,
    Subst.lift, Rename.weaken]
  simp only [HOL.rename, HOL.rename_subst]

variable {Δ : List (Formula Const Γ)}

def specialize (selection : Term Const Γ (Selection α))
    (predicate : Term Const Γ (α ⇒ .prop))
    (justified : ProofSyntax Const Δ (principle selection)) :
    ProofSyntax Const Δ (instanceFormula selection predicate) := by
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.allE predicate justified)
  simp [instantiate, subst_instanceFormula, HOL.subst, Subst.single]

def selectInhabited (selection : Term Const Γ (Selection α))
    (predicate : Term Const Γ (α ⇒ .prop))
    (justified : ProofSyntax Const Δ (principle selection))
    (existsWitness : ProofSyntax Const Δ (inhabited predicate)) :
    ProofSyntax Const Δ (.app predicate (.app selection predicate)) := by
  apply ProofSyntax.exE existsWitness
  have allInstances := PredicateFixedPoint.weakenProof (σ := α) (specialize selection predicate justified)
  have atWitness : ProofSyntax Const (weakenHyps (σ := α) Δ)
      (.imp (.app (weaken predicate) (.var .vz))
        (weaken (.app predicate (.app selection predicate)))) := by
    apply ProofSyntax.castIndices rfl
      (ContextualTrinity.instantiate_vz_rename_lift_weaken _) (ProofSyntax.allE (.var .vz) allInstances)
  exact .impE (atWitness.prepend _) (.hyp 0)

def lambdaAtVariable (body : Formula Const (α :: Γ))
    {assumptions : List (Formula Const (α :: Γ))} :
    ProofSyntax Const assumptions (.eq (.app (weaken (.lam body)) (.var .vz)) body) := by
  apply ProofSyntax.castIndices rfl ?_
    (ProofSyntax.beta (.var .vz) (HOL.rename (Rename.lift Rename.weaken) body))
  simp only [weaken, HOL.rename, ContextualTrinity.instantiate_vz_rename_lift_weaken]

/-- The selected term satisfies the original binder body, with its actual
capture-avoiding instantiation retained in the conclusion. -/
def specification (selection : Term Const Γ (Selection α))
    (body : Formula Const (α :: Γ))
    (justified : ProofSyntax Const Δ (principle selection))
    (existsWitness : ProofSyntax Const Δ (.ex body)) :
    ProofSyntax Const Δ (instantiate (selected selection body) body) := by
  have appliedExists : ProofSyntax Const Δ (inhabited (.lam body)) := by
    apply ProofSyntax.exE existsWitness
    apply ProofSyntax.exI (.var .vz)
    have applied : ProofSyntax Const (body :: weakenHyps (σ := α) Δ)
        (.app (weaken (.lam body)) (.var .vz)) :=
      .impE (.eqPropER (lambdaAtVariable body)) (.hyp 0)
    exact ProofSyntax.castIndices rfl
      (ContextualTrinity.instantiate_vz_rename_lift_weaken
        (.app (weaken (.lam body)) (.var .vz))).symm applied
  exact .impE (.eqPropEL (ProofSyntax.beta (selected selection body) body))
    (selectInhabited selection (.lam body) justified appliedExists)

set_option backward.isDefEq.respectTransparency false in
theorem specialize_free (selection : Term Const Γ (Selection α))
    (predicate : Term Const Γ (α ⇒ .prop))
    (justified : ProofSyntax Const Δ (principle selection))
    (free : justified.FunctionExtensionalityFree) :
    (specialize selection predicate justified).FunctionExtensionalityFree := by
  simpa [specialize, ProofSyntax.FunctionExtensionalityFree] using free

set_option backward.isDefEq.respectTransparency false in
theorem selectInhabited_free (selection : Term Const Γ (Selection α))
    (predicate : Term Const Γ (α ⇒ .prop))
    (justified : ProofSyntax Const Δ (principle selection))
    (existsWitness : ProofSyntax Const Δ (inhabited predicate))
    (choiceFree : justified.FunctionExtensionalityFree)
    (existenceFree : existsWitness.FunctionExtensionalityFree) :
    (selectInhabited selection predicate justified existsWitness).FunctionExtensionalityFree := by
  simp [selectInhabited, ProofSyntax.FunctionExtensionalityFree, ProofSyntax.prepend,
    PredicateFixedPoint.weakenProof, specialize_free selection predicate justified choiceFree,
    existenceFree]

set_option backward.isDefEq.respectTransparency false in
theorem specification_free (selection : Term Const Γ (Selection α))
    (body : Formula Const (α :: Γ))
    (justified : ProofSyntax Const Δ (principle selection))
    (existsWitness : ProofSyntax Const Δ (.ex body))
    (choiceFree : justified.FunctionExtensionalityFree)
    (existenceFree : existsWitness.FunctionExtensionalityFree) :
    (specification selection body justified existsWitness).FunctionExtensionalityFree := by
  unfold specification
  constructor
  · trivial
  · apply selectInhabited_free _ _ _ _ choiceFree
    simp [ProofSyntax.FunctionExtensionalityFree, lambdaAtVariable, existenceFree]

/-- A closed proof over the displayed assumptions, suitable for later
application to checked source facts. -/
def implication (selection : Term Const Γ (Selection α))
    (body : Formula Const (α :: Γ)) :
    ProofSyntax Const [] (.imp (principle selection)
      (.imp (.ex body) (instantiate (selected selection body) body))) :=
  .impI (.impI (specification selection body (.hyp 1) (.hyp 0)))

theorem implication_free (selection : Term Const Γ (Selection α))
    (body : Formula Const (α :: Γ)) : (implication selection body).FunctionExtensionalityFree := by
  exact specification_free (Δ := [.ex body, principle selection])
    selection body (.hyp 1) (.hyp 0) trivial trivial

#print axioms specialize
#print axioms selectInhabited
#print axioms specification
#print axioms implication_free

end Mettapedia.Logic.HOL.SelectionProofs
