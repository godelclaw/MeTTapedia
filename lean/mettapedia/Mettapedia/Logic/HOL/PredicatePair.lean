import Mettapedia.Logic.HOL.FiniteConstructorReadout

/-!
# Predicate observations of encoded index/value pairs

The pair is the existing one-constructor, two-field function encoding.
Its predicate observation computes both original fields, and equal pairs
have equal components. The full function carrier also contains non-pairs;
the always-false function is explicitly separated from every encoded pair.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.PredicatePair
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {index value : Ty Base}

abbrev Pair (index value : Ty Base) := (index ⇒ value ⇒ .prop) ⇒ .prop
abbrev Relation (index value : Ty Base) := index ⇒ value ⇒ .prop

def pair (first : Term Const Γ index) (second : Term Const Γ value) : Term Const Γ (Pair index value) :=
  encode [[index, value]] ⟨0, by simp⟩ (first, second, PUnit.unit)

def holds (relation : Term Const Γ (Relation index value))
    (first : Term Const Γ index) (second : Term Const Γ value) : Formula Const Γ :=
  .app (.app relation first) second

@[simp] theorem subst_pair (substitution : Subst Const Γ Ξ)
    (first : Term Const Γ index) (second : Term Const Γ value) :
    subst substitution (pair first second) = pair (subst substitution first) (subst substitution second) := by
  simp [pair, encode_subst, substituteArguments]

@[simp] theorem rename_pair (rho : Rename Base Γ Ξ)
    (first : Term Const Γ index) (second : Term Const Γ value) :
    rename rho (pair first second) = pair (rename rho first) (rename rho second) := by
  simpa only [subst_ofRename] using subst_pair (Subst.ofRename rho) first second

@[simp] theorem subst_holds (substitution : Subst Const Γ Ξ)
    (relation : Term Const Γ (Relation index value))
    (first : Term Const Γ index) (second : Term Const Γ value) :
    subst substitution (holds relation first second) =
      holds (subst substitution relation) (subst substitution first) (subst substitution second) := rfl

variable {Δ : List (Formula Const Γ)}

def observe (first : Term Const Γ index) (second : Term Const Γ value)
    (relation : Term Const Γ (Relation index value)) :
    ProofSyntax Const Δ (.eq (.app (pair first second) relation) (holds relation first second)) :=
  encode_beta [[index, value]] ⟨0, by simp⟩ (first, second, PUnit.unit) (relation, PUnit.unit)

theorem observe_free (first : Term Const Γ index) (second : Term Const Γ value)
    (relation : Term Const Γ (Relation index value)) :
    (observe (Δ := Δ) first second relation).FunctionExtensionalityFree :=
  encode_beta_free _ _ _ _

def first_equal (first first' : Term Const Γ index) (second second' : Term Const Γ value)
    (equal : ProofSyntax Const Δ (.eq (pair first second) (pair first' second'))) :
    ProofSyntax Const Δ (.eq first first') := by
  apply ProofSyntax.castIndices rfl ?_
    (recover_field [[index, value]] ⟨0, by simp⟩ (Var.vz : Var [index, value] index)
      (first, second, PUnit.unit) (first', second', PUnit.unit) equal)
  rfl

def second_equal (first first' : Term Const Γ index) (second second' : Term Const Γ value)
    (equal : ProofSyntax Const Δ (.eq (pair first second) (pair first' second'))) :
    ProofSyntax Const Δ (.eq second second') := by
  apply ProofSyntax.castIndices rfl ?_
    (recover_field [[index, value]] ⟨0, by simp⟩ (Var.vs Var.vz : Var [index, value] value)
      (first, second, PUnit.unit) (first', second', PUnit.unit) equal)
  rfl

def view (relation : Term Const Γ (Relation index value)) : Term Const Γ (Pair index value ⇒ .prop) :=
  .lam (.app (.var .vz) (weaken relation))

@[simp] theorem subst_view (substitution : Subst Const Γ Ξ)
    (relation : Term Const Γ (Relation index value)) :
    subst substitution (view relation) = view (subst substitution relation) := by
  simp [view, subst, subst_weaken, Subst.lift]

@[simp] theorem rename_view (rho : Rename Base Γ Ξ)
    (relation : Term Const Γ (Relation index value)) :
    rename rho (view relation) = view (rename rho relation) := by
  simpa only [subst_ofRename] using subst_view (Subst.ofRename rho) relation

def view_pair (relation : Term Const Γ (Relation index value))
    (first : Term Const Γ index) (second : Term Const Γ value) :
    ProofSyntax Const Δ (.eq (.app (view relation) (pair first second)) (holds relation first second)) := by
  have outer : ProofSyntax Const Δ (.eq (.app (view relation) (pair first second))
      (.app (pair first second) relation)) := by
    apply ProofSyntax.castIndices rfl ?_ (.beta (pair first second) (.app (.var .vz) (weaken relation)))
    simp [view, instantiate, subst, Subst.single]
    exact instantiate_weaken _ _
  exact .eqTrans outer (observe first second relation)

theorem view_pair_free (relation : Term Const Γ (Relation index value))
    (first : Term Const Γ index) (second : Term Const Γ value) :
    (view_pair (Δ := Δ) relation first second).FunctionExtensionalityFree := by
  simp [view_pair, ProofSyntax.FunctionExtensionalityFree, observe_free]

def property_of_equal_pair (relation : Term Const Γ (Relation index value))
    (point : Term Const Γ (Pair index value)) (first : Term Const Γ index) (second : Term Const Γ value)
    (equal : ProofSyntax Const Δ (.eq point (pair first second)))
    (property : ProofSyntax Const Δ (holds relation first second)) :
    ProofSyntax Const Δ (.app (view relation) point) :=
  .impE (.eqPropER (.eqTrans (.eqAppArg (view relation) equal) (view_pair relation first second))) property

theorem property_of_equal_pair_free (relation : Term Const Γ (Relation index value))
    (point : Term Const Γ (Pair index value)) (first : Term Const Γ index) (second : Term Const Γ value)
    (equal : ProofSyntax Const Δ (.eq point (pair first second)))
    (property : ProofSyntax Const Δ (holds relation first second))
    (equalFree : equal.FunctionExtensionalityFree) (propertyFree : property.FunctionExtensionalityFree) :
    (property_of_equal_pair relation point first second equal property).FunctionExtensionalityFree := by
  simp [property_of_equal_pair, ProofSyntax.FunctionExtensionalityFree, view_pair_free, equalFree, propertyFree]

def junk : Term Const Γ (Pair index value) := .lam .bot

def pair_not_junk (first : Term Const Γ index) (second : Term Const Γ value) :
    ProofSyntax Const Δ (.not (.eq (pair first second) (junk (index := index) (value := value)))) := by
  let always : Term Const Γ (Relation index value) := .lam (.lam .top)
  have actual : ProofSyntax Const (.eq (pair first second) junk :: Δ)
      (.eq (.app (pair first second) always) .top) :=
    .eqTrans (observe first second always)
      (.eqTrans (.eqApp second (.beta first (.lam .top))) (.beta second .top))
  have unused : ProofSyntax Const (.eq (pair first second) junk :: Δ)
      (.eq (.app junk always) .bot) := .beta always .bot
  exact .notI (.impE (.eqPropEL (.eqTrans (.eqSymm actual)
    (.eqTrans (.eqApp always (.hyp 0)) unused))) .topI)

theorem pair_not_junk_free (first : Term Const Γ index) (second : Term Const Γ value) :
    (pair_not_junk (Δ := Δ) first second).FunctionExtensionalityFree := by
  simp [pair_not_junk, ProofSyntax.FunctionExtensionalityFree, observe_free]

#print axioms subst_pair
#print axioms observe_free
#print axioms first_equal
#print axioms second_equal
#print axioms pair_not_junk_free
end Mettapedia.Logic.HOL.PredicatePair
