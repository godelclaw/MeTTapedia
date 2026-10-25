import Mettapedia.Languages.Megalodon.HenkinEqualityInterpretation
import Mettapedia.Logic.HOL.ContextualTrinity
import Mettapedia.Logic.HOL.ProofSyntaxHypothesisSubstitution

/-!
# Retained comparison of primitive and binary-relation HOL equality

The actual Megalodon relation definition is compared with primitive equality
by source proof trees. One direction transports both relation arguments. The
other instantiates the quantified relation with a typed equality test and
uses its explicit beta equations. No semantic-validity or full-domain premise
is used to construct these proofs.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.Megalodon.RelationEqualityComparison
open Mettapedia.Logic.HOL
open HenkinEqualityInterpretation
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {gamma : Ctx Base} {type : Ty Base}
variable {assumptions : List (Formula Const gamma)}

def body (first second : Term Const gamma type) : Formula Const gamma :=
  .all (.imp
    (.app (.app (.var .vz) (weaken first)) (weaken second))
    (.app (.app (.var .vz) (weaken second)) (weaken first)))

def equalityBeta (first second : Term Const gamma type) :
    ProofSyntax Const assumptions (.eq (equalityFormula first second) (body first second)) := by
  apply ProofSyntax.eqTrans (ProofSyntax.eqApp second (ProofSyntax.beta first _))
  refine ProofSyntax.castIndices rfl ?_
    (ProofSyntax.beta second (.all (.imp
      (.app (.app (.var .vz) (weaken (weaken first))) (.var (.vs .vz)))
      (.app (.app (.var .vz) (.var (.vs .vz))) (weaken (weaken first))))))
  simp [body, instantiate, subst, Subst.single, Subst.lift, weaken, subst_rename, Rename.weaken]
  exact subst_ofRename (fun {_} index => Var.vs index) first

def primitiveToRelation (first second : Term Const gamma type) :
    ProofSyntax Const [] (.imp (.eq first second) (equalityFormula first second)) := by
  apply ProofSyntax.impI
  apply ProofSyntax.impE (ProofSyntax.eqPropER (equalityBeta first second))
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let relation : Term Const ((type ⇒ type ⇒ .prop) :: gamma) (type ⇒ type ⇒ .prop) := .var .vz
  have firstArgument := ProofSyntax.eqApp (weaken second)
    (ProofSyntax.eqAppArg relation (ProofSyntax.hyp (Const := Const)
      (Δ := .app (.app relation (weaken first)) (weaken second) :: weakenHyps [.eq first second]) 1))
  have secondArgument := ProofSyntax.eqAppArg (.app relation (weaken second))
    (ProofSyntax.eqSymm (ProofSyntax.hyp (Const := Const)
      (Δ := .app (.app relation (weaken first)) (weaken second) :: weakenHyps [.eq first second]) 1))
  exact .impE (.eqPropEL (.eqTrans firstArgument secondArgument)) (.hyp 0)

def tester (first : Term Const gamma type) : Term Const gamma (type ⇒ type ⇒ .prop) :=
  .lam (.lam (.eq (weaken (weaken first)) (.var (.vs .vz))))

def testerBeta (first left right : Term Const gamma type) :
    ProofSyntax Const assumptions (.eq (.app (.app (tester first) left) right) (.eq first left)) := by
  apply ProofSyntax.eqTrans (ProofSyntax.eqApp right (ProofSyntax.beta left _))
  refine ProofSyntax.castIndices rfl ?_ (ProofSyntax.beta right (.eq (weaken first) (weaken left)))
  simp [instantiate, subst, Subst.single, Subst.lift, weaken, subst_rename, Rename.weaken]
  exact ⟨(subst_ofRename (fun {_} index => Var.vs index) first).symm, subst_id first, subst_id left⟩

theorem instantiate_relation (first second : Term Const gamma type)
    (relation : Term Const gamma (type ⇒ type ⇒ .prop)) :
    instantiate relation (.imp
      (.app (.app (.var .vz) (weaken first)) (weaken second))
      (.app (.app (.var .vz) (weaken second)) (weaken first))) =
    .imp (.app (.app relation first) second) (.app (.app relation second) first) := by
  change Term.imp
    (.app (.app relation (instantiate relation (weaken first))) (instantiate relation (weaken second)))
    (.app (.app relation (instantiate relation (weaken second))) (instantiate relation (weaken first))) = _
  rw [instantiate_weaken, instantiate_weaken]

def relationToPrimitive (first second : Term Const gamma type) :
    ProofSyntax Const [] (.imp (equalityFormula first second) (.eq first second)) := by
  apply ProofSyntax.impI
  let selected := ProofSyntax.allE (tester first)
    (ProofSyntax.impE (ProofSyntax.eqPropEL (equalityBeta first second))
      (ProofSyntax.hyp (Const := Const) (Δ := [equalityFormula first second]) 0))
  have specialized : ProofSyntax Const [equalityFormula first second]
      (.imp (.app (.app (tester first) first) second) (.app (.app (tester first) second) first)) :=
    ProofSyntax.castIndices rfl (instantiate_relation first second (tester first)) selected
  exact .impE (.eqPropEL (testerBeta first second first))
    (.impE specialized (.impE (.eqPropER (testerBeta first first second)) (.eqRefl first)))

def equation (first second : Term Const gamma type) :
    ProofSyntax Const assumptions (.eq (.eq first second) (equalityFormula first second)) :=
  .eqPropI ((primitiveToRelation first second).mono (ProofSyntax.emptyOccurrenceMap _))
    ((relationToPrimitive first second).mono (ProofSyntax.emptyOccurrenceMap _))

def ofPrimitive {first second : Term Const gamma type}
    (proof : ProofSyntax Const assumptions (.eq first second)) :
    ProofSyntax Const assumptions (equalityFormula first second) := .impE (.eqPropEL (equation first second)) proof

def toPrimitive {first second : Term Const gamma type}
    (proof : ProofSyntax Const assumptions (equalityFormula first second)) :
    ProofSyntax Const assumptions (.eq first second) := .impE (.eqPropER (equation first second)) proof

def pointwiseToPrimitive {domain result : Ty Base} {first second : Term Const gamma (domain ⇒ result)}
    (proof : ProofSyntax Const assumptions
      (.all (equalityFormula (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz))))) :
    ProofSyntax Const assumptions
      (.all (.eq (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz)))) := by
  apply ProofSyntax.allI
  let relationBody : Formula Const (domain :: gamma) :=
    equalityFormula (.app (weaken first) (.var .vz)) (.app (weaken second) (.var .vz))
  have selected := ProofSyntax.allE (.var .vz) (proof.rename (Rename.weaken (σ := domain)))
  have restored : ProofSyntax Const (weakenHyps (σ := domain) assumptions) relationBody :=
    ProofSyntax.castIndices rfl (ContextualTrinity.instantiate_vz_rename_lift_weaken relationBody) selected
  exact toPrimitive restored

theorem roundTrip_changes_proof (value : Term Const gamma type) :
    toPrimitive (ofPrimitive (ProofSyntax.eqRefl (Δ := []) value)) ≠ ProofSyntax.eqRefl value := by
  intro same
  have observation := congrArg ProofSyntax.rootObservation same
  cases observation

#print axioms equalityBeta
#print axioms primitiveToRelation
#print axioms relationToPrimitive
#print axioms equation
#print axioms roundTrip_changes_proof
end Mettapedia.Languages.Megalodon.RelationEqualityComparison
