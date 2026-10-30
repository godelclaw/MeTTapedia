import Mettapedia.Logic.HOL.ConstructorProjections

/-!
# Full constructor injectivity supplies field injectivity

The premise has the six-quantifier, Boolean-equivalence shape of the
recursive-space constructor theorem. The retained proof extracts the two
fields required by the projection construction and keeps the first-argument
equality available in the stronger source statement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.ConstructorInjectivity
open ConstructorProjections
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {first second third carrier : Ty Base}

def atImage (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) : Formula Const Γ :=
  .all (.all (.all (.eq
    (.eq (weaken (weaken (weaken (apply constructor a b c))))
      (apply (weaken (weaken (weaken constructor))) (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz)))
    (.and (.eq (weaken (weaken (weaken a))) (.var (.vs (.vs .vz))))
      (.and (.eq (weaken (weaken (weaken b))) (.var (.vs .vz)))
        (.eq (weaken (weaken (weaken c))) (.var .vz)))))))

def statement (constructor : Term Const Γ (Constructor first second third carrier)) : Formula Const Γ :=
  .all (.all (.all (atImage (weaken (weaken (weaken constructor)))
    (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

@[simp] theorem subst_atImage (σ : Subst Const Γ Ξ)
    (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third) :
    subst σ (atImage constructor a b c) = atImage (subst σ constructor) (subst σ a) (subst σ b) (subst σ c) := by
  simp [atImage, subst, subst_weaken, Subst.lift, Rename.weaken]

@[simp] theorem subst_statement (σ : Subst Const Γ Ξ)
    (constructor : Term Const Γ (Constructor first second third carrier)) :
    subst σ (statement constructor) = statement (subst σ constructor) := by
  simp [statement, subst, subst_weaken, Subst.lift, Rename.weaken]

theorem rename_statement (ρ : Rename Base Γ Ξ)
    (constructor : Term Const Γ (Constructor first second third carrier)) :
    rename ρ (statement constructor) = statement (rename ρ constructor) := by
  simpa only [subst_ofRename] using subst_statement (Subst.ofRename ρ) constructor

private theorem subst_vars {τ : Ty Base} (term : Term Const Γ τ) :
    subst (fun {σ} (index : Var Γ σ) => Term.var index) term = term := subst_id term

private theorem subst_drop_shift {α τ : Ty Base} (value : Term Const Γ α) (term : Term Const Γ τ) :
    subst (Subst.comp (Subst.single value) (fun index => Term.var (.vs index))) term = term := by
  have identity : (Subst.comp (Subst.single value) (fun index => Term.var (.vs index)) : Subst Const Γ Γ) =
      (fun {σ} (index : Var Γ σ) => Term.var index) := by
    funext type index
    rfl
  rw [identity]
  exact subst_id term

variable {Δ : List (Formula Const Γ)}

def specialize (constructor : Term Const Γ (Constructor first second third carrier))
    (a : Term Const Γ first) (b : Term Const Γ second) (c : Term Const Γ third)
    (proof : ProofSyntax Const Δ (statement constructor)) : ProofSyntax Const Δ (atImage constructor a b c) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE c (.allE b (.allE a proof)))
  simp [instantiate, subst, subst_weaken, Subst.single, Subst.lift, Rename.weaken,
    subst_rename, subst_comp, subst_drop_shift, subst_vars]

def compare (constructor : Term Const Γ (Constructor first second third carrier))
    (a a' : Term Const Γ first) (b b' : Term Const Γ second) (c c' : Term Const Γ third)
    (proof : ProofSyntax Const Δ (atImage constructor a b c)) :
    ProofSyntax Const Δ (.eq (.eq (apply constructor a b c) (apply constructor a' b' c'))
      (.and (.eq a a') (.and (.eq b b') (.eq c c')))) := by
  apply ProofSyntax.castIndices rfl ?_ (.allE c' (.allE b' (.allE a' proof)))
  simp [instantiate, subst, subst_weaken, Subst.single, Subst.lift, Rename.weaken,
    subst_rename, subst_comp, subst_drop_shift, subst_vars]

/-- Reversing the order of specialization matches the projection interface's
candidate-to-original equation without changing the supplied source fact. -/
def fields (constructor : Term Const Γ (Constructor first second third carrier)) :
    ProofSyntax Const Δ (.imp (statement constructor) (fieldInjective constructor)) := by
  let Ω := third :: second :: first :: third :: second :: first :: Γ
  let a : Term Const Ω first := .var (.vs (.vs (.vs (.vs (.vs .vz)))))
  let b : Term Const Ω second := .var (.vs (.vs (.vs (.vs .vz))))
  let c : Term Const Ω third := .var (.vs (.vs (.vs .vz)))
  let a' : Term Const Ω first := .var (.vs (.vs .vz))
  let b' : Term Const Ω second := .var (.vs .vz)
  let c' : Term Const Ω third := .var .vz
  let constructor' : Term Const Ω (Constructor first second third carrier) :=
    weaken (weaken (weaken (weaken (weaken (weaken constructor)))))
  apply ProofSyntax.impI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  change ProofSyntax Const _ (.and (.eq b' b) (.eq c' c))
  refine .andER (.impE (.eqPropEL (compare constructor' a' a b' b c' c
    (specialize constructor' a' b' c' ?_))) (.hyp 0))
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.hyp ⟨1, by simp [weakenHyps]⟩)
  simp [constructor', weakenHyps, weaken, rename_statement]

theorem fields_free (constructor : Term Const Γ (Constructor first second third carrier)) :
    (fields (Δ := Δ) constructor).FunctionExtensionalityFree := by
  simp [fields, compare, specialize, ProofSyntax.FunctionExtensionalityFree]

#print axioms fields
#print axioms fields_free
end Mettapedia.Logic.HOL.ConstructorInjectivity
