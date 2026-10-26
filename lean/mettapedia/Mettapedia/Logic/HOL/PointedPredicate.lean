import Mettapedia.Logic.HOL.PredicateFixedPoint

/-!
# Guarded predicate carriers with retained HOL witnesses

The functional encoding distinguishes an absent point from present values.
For any predicate, the absent point supplies a closed-hypothesis witness for
its pointed carrier. It does not prove the original predicate inhabited.
The presence predicate remains explicit, including in the empty case.

Separation and injectivity use application congruence and explicit beta
proofs. They require no function-extensionality axiom. Native declaration
formation and the interpretation of this syntax have their own interfaces.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.PointedPredicate
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
variable {α : Ty Base}
abbrev Carrier (α : Ty Base) := (α ⇒ .prop) ⇒ .prop

def none (α : Ty Base) : Term Const Γ (Carrier α) := .lam .bot

def some (value : Term Const Γ α) : Term Const Γ (Carrier α) :=
  .lam (.app (.var .vz) (weaken value))

def present (property : Term Const Γ (α ⇒ .prop)) (value : Term Const Γ (Carrier α)) : Formula Const Γ :=
  .ex (.and (.app (weaken property) (.var .vz)) (.eq (weaken value) (some (.var .vz))))

def admitted (property : Term Const Γ (α ⇒ .prop)) (value : Term Const Γ (Carrier α)) : Formula Const Γ :=
  .or (.eq value (none α)) (present property value)

@[simp] theorem rename_none {Ξ : Ctx Base} (ρ : Rename Base Γ Ξ) (α : Ty Base) :
    rename ρ (none (Const := Const) α) = none α := rfl

@[simp] theorem rename_some {Ξ : Ctx Base} (ρ : Rename Base Γ Ξ) (value : Term Const Γ α) :
    rename ρ (some value) = some (rename ρ value) := by
  simp [some, rename, Rename.lift]

@[simp] theorem subst_none {Ξ : Ctx Base} (θ : Subst Const Γ Ξ) (α : Ty Base) :
    subst θ (none (Const := Const) α) = none α := rfl

@[simp] theorem subst_some {Ξ : Ctx Base} (θ : Subst Const Γ Ξ) (value : Term Const Γ α) :
    subst θ (some value) = some (subst θ value) := by
  simp [some, subst, Subst.lift]

@[simp] theorem subst_admitted {Ξ : Ctx Base} (θ : Subst Const Γ Ξ)
    (property : Term Const Γ (α ⇒ .prop)) (value : Term Const Γ (Carrier α)) :
    subst θ (admitted property value) = admitted (subst θ property) (subst θ value) := by
  simp [admitted, present, subst, Subst.lift]

variable {Δ : List (Formula Const Γ)}

def none_admitted (property : Term Const Γ (α ⇒ .prop)) :
    ProofSyntax Const Δ (admitted property (none α)) := .orIL (.eqRefl (none α))

def existence (property : Term Const Γ (α ⇒ .prop)) :
    ProofSyntax Const Δ (.ex (admitted (weaken property) (.var .vz))) := by
  refine .exI (none α) ?_
  apply ProofSyntax.castIndices rfl ?_ (none_admitted property)
  simp [instantiate, subst_admitted, subst, Subst.single]

def predicate (property : Term Const Γ (α ⇒ .prop)) : Term Const Γ (Carrier α ⇒ .prop) :=
  .lam (admitted (weaken property) (.var .vz))

def witness (property : Term Const Γ (α ⇒ .prop)) :
    ProofSyntax Const Δ (.app (predicate property) (none α)) := by
  have beta : ProofSyntax Const Δ
      (.eq (.app (predicate property) (none α)) (admitted property (none α))) := by
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.beta (none α) (admitted (weaken property) (.var .vz)))
    simp [predicate, instantiate, subst_admitted, subst, Subst.single]
  exact .impE (.eqPropER beta) (none_admitted property)

def some_beta (value : Term Const Γ α) (property : Term Const Γ (α ⇒ .prop)) :
    ProofSyntax Const Δ (.eq (.app (some value) property) (.app property value)) := by
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.beta property (.app (.var .vz) (weaken value)))
  simp [some, instantiate, subst, Subst.single]

def none_beta (property : Term Const Γ (α ⇒ .prop)) :
    ProofSyntax Const Δ (.eq (.app (none α) property) .bot) := .beta property .bot

def some_ne_none (value : Term Const Γ α) :
    ProofSyntax Const Δ (.not (.eq (some value) (none α))) := by
  refine .notI ?_
  let yes : Term Const Γ (α ⇒ .prop) := .lam .top
  have applied : ProofSyntax Const (.eq (some value) (none α) :: Δ)
      (.eq (.app (some value) yes) (.app (none α) yes)) :=
    .eqApp yes (.hyp ⟨0, by simp⟩)
  have left : ProofSyntax Const (.eq (some value) (none α) :: Δ)
      (.eq (.app (some value) yes) .top) :=
    .eqTrans (some_beta value yes) (.beta value .top)
  have right : ProofSyntax Const (.eq (some value) (none α) :: Δ)
      (.eq (.app (none α) yes) .bot) := none_beta yes
  exact .impE (.eqPropEL (.eqTrans (.eqSymm left) (.eqTrans applied right))) .topI

def equalityPredicate (value : Term Const Γ α) : Term Const Γ (α ⇒ .prop) :=
  .lam (.eq (.var .vz) (weaken value))

def equality_beta (first second : Term Const Γ α) :
    ProofSyntax Const Δ (.eq (.app (equalityPredicate first) second) (.eq second first)) := by
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.beta second (.eq (.var .vz) (weaken first)))
  simp [equalityPredicate, instantiate, subst, Subst.single]

def some_injective (first second : Term Const Γ α)
    (same : ProofSyntax Const Δ (.eq (some first) (some second))) :
    ProofSyntax Const Δ (.eq first second) := by
  let property := equalityPredicate first
  have applied : ProofSyntax Const Δ
      (.eq (.app (some first) property) (.app (some second) property)) := .eqApp property same
  have left : ProofSyntax Const Δ (.eq (.app (some first) property) (.eq first first)) :=
    .eqTrans (some_beta first property) (equality_beta first first)
  have right : ProofSyntax Const Δ (.eq (.app (some second) property) (.eq second first)) :=
    .eqTrans (some_beta second property) (equality_beta first second)
  exact .eqSymm (.impE (.eqPropEL (.eqTrans (.eqSymm left) (.eqTrans applied right))) (.eqRefl first))

def none_not_present (property : Term Const Γ (α ⇒ .prop)) :
    ProofSyntax Const Δ (.not (present property (none α))) := by
  refine .notI (.exE (.hyp ⟨0, by simp⟩) ?_)
  let premise : Formula Const (α :: Γ) :=
    .and (.app (weaken property) (.var .vz)) (.eq (weaken (none α)) (some (.var .vz)))
  let assumptions := premise :: weakenHyps (present property (none α) :: Δ)
  have same : ProofSyntax Const assumptions (.eq (some (.var .vz)) (none α)) := by
    apply ProofSyntax.castIndices rfl ?_
      (ProofSyntax.eqSymm (ProofSyntax.andER (ProofSyntax.hyp (Const := Const)
        (Δ := assumptions) ⟨0, by simp [assumptions]⟩)))
    simp [weaken]
  exact .notE (some_ne_none (.var .vz)) same

def falseProperty (α : Ty Base) : Term Const Γ (α ⇒ .prop) := .lam .bot

def false_not_present (value : Term Const Γ (Carrier α)) :
    ProofSyntax Const Δ (.not (present (falseProperty α) value)) := by
  refine .notI (.exE (.hyp ⟨0, by simp⟩) ?_)
  let premise : Formula Const (α :: Γ) :=
    .and (.app (weaken (falseProperty α)) (.var .vz)) (.eq (weaken value) (some (.var .vz)))
  let assumptions := premise :: weakenHyps (present (falseProperty α) value :: Δ)
  have member : ProofSyntax Const assumptions (.app (weaken (falseProperty α)) (.var .vz)) :=
    .andEL (.hyp ⟨0, by simp [assumptions]⟩)
  exact .impE (.eqPropEL (.beta (.var .vz) .bot)) member

def existence_schema (α : Ty Base) :
    ProofSyntax Const ([] : List (Formula Const []))
      (.all (.ex (admitted (.var (.vs .vz) : Term Const [Carrier α, α ⇒ .prop] (α ⇒ .prop)) (.var .vz)))) :=
  .allI (existence (.var .vz))

set_option backward.isDefEq.respectTransparency false in
theorem existence_schema_functionExtensionalityFree (α : Ty Base) :
    ProofSyntax.FunctionExtensionalityFree (existence_schema (Const := Const) α) := by
  simp [existence_schema, existence, none_admitted, ProofSyntax.FunctionExtensionalityFree]

set_option backward.isDefEq.respectTransparency false in
theorem witness_functionExtensionalityFree (property : Term Const Γ (α ⇒ .prop)) :
    ProofSyntax.FunctionExtensionalityFree (witness (Δ := Δ) property) := by
  simp [witness, none_admitted, ProofSyntax.FunctionExtensionalityFree]


set_option backward.isDefEq.respectTransparency false in
theorem some_ne_none_functionExtensionalityFree (value : Term Const Γ α) :
    ProofSyntax.FunctionExtensionalityFree (some_ne_none (Δ := Δ) value) := by
  simp [some_ne_none, some_beta, none_beta, ProofSyntax.FunctionExtensionalityFree]

set_option backward.isDefEq.respectTransparency false in
theorem some_injective_functionExtensionalityFree (first second : Term Const Γ α)
    (same : ProofSyntax Const Δ (.eq (some first) (some second)))
    (free : ProofSyntax.FunctionExtensionalityFree same) :
    ProofSyntax.FunctionExtensionalityFree (some_injective first second same) := by
  simp [some_injective, some_beta, equality_beta, ProofSyntax.FunctionExtensionalityFree, free]

def separation_schema (α : Ty Base) : ProofSyntax Const ([] : List (Formula Const []))
    (.all (.not (.eq (some (.var .vz)) (none α)))) := .allI (some_ne_none (.var .vz))

def injectivity_schema (α : Ty Base) : ProofSyntax Const ([] : List (Formula Const []))
    (.all (.all (.imp (.eq (some (.var (.vs .vz))) (some (.var .vz)))
      (.eq (.var (.vs .vz) : Term Const [α, α] α) (.var .vz))))) :=
  .allI (.allI (.impI (some_injective (.var (.vs .vz)) (.var .vz) (.hyp ⟨0, by simp⟩))))

theorem separation_schema_functionExtensionalityFree (α : Ty Base) :
    ProofSyntax.FunctionExtensionalityFree (separation_schema (Const := Const) α) :=
  some_ne_none_functionExtensionalityFree (.var .vz)

theorem injectivity_schema_functionExtensionalityFree (α : Ty Base) :
    ProofSyntax.FunctionExtensionalityFree (injectivity_schema (Const := Const) α) := by
  let first : Term Const [α, α] α := .var (.vs .vz)
  let second : Term Const [α, α] α := .var .vz
  let hypothesis : ProofSyntax Const [.eq (some first) (some second)] (.eq (some first) (some second)) :=
    .hyp (Δ := [.eq (some first) (some second)]) ⟨0, Nat.zero_lt_succ 0⟩
  change ProofSyntax.FunctionExtensionalityFree (some_injective first second hypothesis)
  exact some_injective_functionExtensionalityFree first second hypothesis trivial

#print axioms separation_schema
#print axioms injectivity_schema

#print axioms existence_schema
#print axioms existence_schema_functionExtensionalityFree
#print axioms witness
#print axioms some_ne_none
#print axioms some_injective
#print axioms none_not_present
#print axioms false_not_present
end Mettapedia.Logic.HOL.PointedPredicate
