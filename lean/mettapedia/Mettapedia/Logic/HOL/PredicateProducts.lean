import Mettapedia.Logic.HOL.ContextualTrinity
import Mettapedia.Logic.HOL.PredicateFixedPoint
import Mettapedia.Logic.HOL.ProofSyntaxCongruence

/-!
# Dependent products of HOL predicate families

A predicate on the domain and an open predicate on the codomain describe
guarded dependent functions in a fixed simple function carrier. Membership
quantifies over admitted domain values and retains the domain guard. This
does not assume that either the domain or any codomain fibre is inhabited.
The constructions retain the ambient context and use the existing binder
substitution operations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.PredicateProducts

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
    {Γ Ξ : Ctx Base} {σ τ : Ty Base}

def full (type : Ty Base) : Term Const Γ (type ⇒ .prop) := .lam .top

def membership (domain : Term Const Γ (σ ⇒ .prop))
    (family : Term Const (σ :: Γ) (τ ⇒ .prop))
    (function : Term Const Γ (σ ⇒ τ)) : Formula Const Γ :=
  .all (.imp (.app (weaken domain) (.var .vz))
    (.app family (.app (weaken function) (.var .vz))))

/-- The predicate code for a dependent product. -/
def pi (domain : Term Const Γ (σ ⇒ .prop))
    (family : Term Const (σ :: Γ) (τ ⇒ .prop)) : Term Const Γ ((σ ⇒ τ) ⇒ .prop) :=
  .lam (.all (.imp (.app (weaken (weaken domain)) (.var .vz))
    (.app (HOL.rename (Rename.lift Rename.weaken) family)
      (.app (.var (.vs .vz)) (.var .vz)))))

@[simp] theorem rename_full (ρ : Rename Base Γ Ξ) (type : Ty Base) :
    HOL.rename ρ (full (Const := Const) type) = full type := rfl

@[simp] theorem subst_full (θ : Subst Const Γ Ξ) (type : Ty Base) :
    HOL.subst θ (full (Const := Const) type) = full type := rfl

@[simp] theorem rename_pi (ρ : Rename Base Γ Ξ)
    (domain : Term Const Γ (σ ⇒ .prop)) (family : Term Const (σ :: Γ) (τ ⇒ .prop)) :
    HOL.rename ρ (pi domain family) =
      pi (HOL.rename ρ domain) (HOL.rename (Rename.lift ρ) family) := by
  simp only [pi, HOL.rename, weaken, HOL.rename_comp]
  congr 4
  apply HOL.rename_ext
  intro type index
  cases index <;> rfl

@[simp] theorem subst_pi (θ : Subst Const Γ Ξ)
    (domain : Term Const Γ (σ ⇒ .prop)) (family : Term Const (σ :: Γ) (τ ⇒ .prop)) :
    HOL.subst θ (pi domain family) =
      pi (HOL.subst θ domain) (HOL.subst (Subst.lift θ) family) := by
  simp only [pi, HOL.subst, Subst.lift, weaken, HOL.subst_rename, HOL.rename_subst]
  congr 4
  apply HOL.subst_ext
  intro type index
  cases index <;> simp [HOL.rename_comp, Rename.weaken, Rename.lift]

def beta {Δ : List (Formula Const Γ)}
    (domain : Term Const Γ (σ ⇒ .prop))
    (family : Term Const (σ :: Γ) (τ ⇒ .prop))
    (function : Term Const Γ (σ ⇒ τ)) :
    ProofSyntax Const Δ (.eq (.app (pi domain family) function)
      (membership domain family function)) := by
  have familyCancel : HOL.subst (Subst.lift (Subst.single function))
      (HOL.rename (Rename.lift Rename.weaken) family) = family := by
    rw [HOL.subst_rename]
    trans HOL.subst Subst.id family
    · apply HOL.subst_ext
      intro type index
      cases index <;> rfl
    · exact HOL.subst_id family
  have domainCancel : HOL.subst (Subst.lift (σ := σ) (Subst.single function))
      (weaken (weaken domain)) = weaken domain := by
    rw [HOL.subst_weaken]
    exact congrArg weaken (instantiate_weaken function domain)
  apply ProofSyntax.castIndices rfl ?_
    (.beta function (.all (.imp (.app (weaken (weaken domain)) (.var .vz))
      (.app (HOL.rename (Rename.lift Rename.weaken) family)
        (.app (.var (.vs .vz)) (.var .vz))))))
  simp only [pi, membership, instantiate, HOL.subst, familyCancel, domainCancel,
    Subst.lift, Subst.single]
  rfl

theorem beta_free {Δ : List (Formula Const Γ)}
    (domain : Term Const Γ (σ ⇒ .prop))
    (family : Term Const (σ :: Γ) (τ ⇒ .prop))
    (function : Term Const Γ (σ ⇒ τ)) :
    (beta (Δ := Δ) domain family function).FunctionExtensionalityFree := by
  simp [beta, ProofSyntax.FunctionExtensionalityFree]

def introduce {Δ : List (Formula Const Γ)}
    (domain : Term Const Γ (σ ⇒ .prop))
    (family : Term Const (σ :: Γ) (τ ⇒ .prop))
    (function : Term Const Γ (σ ⇒ τ))
    (body : ProofSyntax Const (.app (weaken domain) (.var .vz) :: weakenHyps Δ)
      (.app family (.app (weaken function) (.var .vz)))) :
    ProofSyntax Const Δ (.app (pi domain family) function) :=
  .impE (.eqPropER (beta domain family function)) (.allI (.impI body))

def eliminate {Δ : List (Formula Const Γ)}
    (domain : Term Const Γ (σ ⇒ .prop))
    (family : Term Const (σ :: Γ) (τ ⇒ .prop))
    (function : Term Const Γ (σ ⇒ τ)) (argument : Term Const Γ σ)
    (functionTyped : ProofSyntax Const Δ (.app (pi domain family) function))
    (argumentTyped : ProofSyntax Const Δ (.app domain argument)) :
    ProofSyntax Const Δ (.app (instantiate argument family) (.app function argument)) := by
  have all := ProofSyntax.impE (.eqPropEL (beta domain family function)) functionTyped
  have atArgument := ProofSyntax.allE argument all
  have step : ProofSyntax Const Δ (.imp (.app domain argument)
      (.app (instantiate argument family) (.app function argument))) := by
    apply ProofSyntax.castIndices rfl ?_ atArgument
    change Term.imp (.app (instantiate argument (weaken domain)) argument)
      (.app (instantiate argument family) (.app (instantiate argument (weaken function)) argument)) = _
    rw [instantiate_weaken, instantiate_weaken]

  exact .impE step argumentTyped

theorem introduce_free {Δ : List (Formula Const Γ)}
    (domain : Term Const Γ (σ ⇒ .prop))
    (family : Term Const (σ :: Γ) (τ ⇒ .prop))
    (function : Term Const Γ (σ ⇒ τ))
    (body : ProofSyntax Const (.app (weaken domain) (.var .vz) :: weakenHyps Δ)
      (.app family (.app (weaken function) (.var .vz))))
    (free : body.FunctionExtensionalityFree) :
    (introduce domain family function body).FunctionExtensionalityFree := by
  simp [introduce, ProofSyntax.FunctionExtensionalityFree, beta_free, free]

theorem eliminate_free {Δ : List (Formula Const Γ)}
    (domain : Term Const Γ (σ ⇒ .prop))
    (family : Term Const (σ :: Γ) (τ ⇒ .prop))
    (function : Term Const Γ (σ ⇒ τ)) (argument : Term Const Γ σ)
    (functionTyped : ProofSyntax Const Δ (.app (pi domain family) function))
    (argumentTyped : ProofSyntax Const Δ (.app domain argument))
    (functionFree : functionTyped.FunctionExtensionalityFree)
    (argumentFree : argumentTyped.FunctionExtensionalityFree) :
    (eliminate domain family function argument functionTyped argumentTyped).FunctionExtensionalityFree := by
  simp [eliminate, ProofSyntax.FunctionExtensionalityFree, beta_free, functionFree, argumentFree]

/-- Equality of the domain and open family induces equality of their
dependent-product predicates. The family remains under its actual binder. -/
def congruence {Δ : List (Formula Const Γ)}
    {domain domain' : Term Const Γ (σ ⇒ .prop)}
    {family family' : Term Const (σ :: Γ) (τ ⇒ .prop)}
    (domains : ProofSyntax Const Δ (.eq domain domain'))
    (families : ProofSyntax Const (weakenHyps (σ := σ) Δ) (.eq family family')) :
    ProofSyntax Const Δ (.eq (pi domain family) (pi domain' family')) := by
  apply ProofSyntax.eqLam
  apply ContextualTrinity.allCongr
  apply ProofSyntax.impCongr
  · exact .eqApp (.var .vz)
      (PredicateFixedPoint.weakenProof (σ := σ)
        (PredicateFixedPoint.weakenProof (σ := σ ⇒ τ) domains))
  · exact .eqApp (.app (.var (.vs .vz)) (.var .vz))
      (ProofSyntax.castIndices
        (ExtDerivation.rename_weakenHyps (σ := σ) (Rename.weaken (σ := σ ⇒ τ)) Δ).symm rfl
        (ProofSyntax.rename (Rename.lift (Rename.weaken (σ := σ ⇒ τ))) families))

theorem congruence_free {Δ : List (Formula Const Γ)}
    {domain domain' : Term Const Γ (σ ⇒ .prop)}
    {family family' : Term Const (σ :: Γ) (τ ⇒ .prop)}
    (domains : ProofSyntax Const Δ (.eq domain domain'))
    (families : ProofSyntax Const (weakenHyps (σ := σ) Δ) (.eq family family'))
    (domainsFree : domains.FunctionExtensionalityFree) (familiesFree : families.FunctionExtensionalityFree) :
    (congruence domains families).FunctionExtensionalityFree := by
  simp [congruence, ProofSyntax.FunctionExtensionalityFree, ContextualTrinity.allCongr,
    ContextualTrinity.allImp, ContextualTrinity.instantiateFresh, ContextualTrinity.castConclusion,
    ProofSyntax.impCongr, ContextualTrinity.castEq, ContextualTrinity.holeCongr,
    PredicateFixedPoint.weakenProof, domainsFree, familiesFree]

#print axioms congruence
#print axioms congruence_free
#print axioms rename_pi
#print axioms subst_pi
#print axioms beta
#print axioms introduce
#print axioms eliminate

end Mettapedia.Logic.HOL.PredicateProducts
