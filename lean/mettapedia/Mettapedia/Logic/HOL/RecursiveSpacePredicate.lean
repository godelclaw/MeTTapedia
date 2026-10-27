import Mettapedia.Logic.HOL.PositivePredicate
import Mettapedia.Logic.HOL.TypeSubstitutionSemantics
import Mettapedia.Logic.HOL.ConstantSubstitutionSemantics
import Mettapedia.Logic.HOL.PredicateFixedPointSemantics

/-!
# Positive indexed-family predicates over recursive-space operations

A layer exposes its tag, payload and natural-indexed child function as three
typed arguments. Shape and edge guards are fixed parameters. Active children
must satisfy the recursive predicate; inactive positions must contain bottom.
The positive syntax compiles monotonicity and fixed-point proofs directly.
Datatype-specific guards remain explicit inputs to this operator.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate

universe u v w
variable {Base : Type u} {Const : Ty Base → Type v}

structure Signature (Const : Ty Base → Type v) where
  number : Ty Base
  payload : Ty Base
  space : Ty Base
  bottom : ClosedTerm Const space
  construct : ClosedTerm Const (number ⇒ payload ⇒ (number ⇒ space) ⇒ space)
  validShape : ClosedTerm Const (number ⇒ payload ⇒ .prop)
  active : ClosedTerm Const (payload ⇒ number ⇒ .prop)
  validEdge : ClosedTerm Const (payload ⇒ number ⇒ space ⇒ .prop)

namespace Signature

variable (signature : Signature Const)

def code : PositivePredicate.Code Const signature.space [signature.space] :=
  .ex (domain := signature.number) (.ex (domain := signature.payload)
    (.ex (domain := signature.number ⇒ signature.space)
      (.conj
        (.atom (.app (.app (weakenCtx _ signature.validShape) (.var (.vs (.vs .vz)))) (.var (.vs .vz))))
        (.conj
          (.atom (.eq (.var (.vs (.vs (.vs .vz))))
            (.app (.app (.app (weakenCtx _ signature.construct) (.var (.vs (.vs .vz))))
              (.var (.vs .vz))) (.var .vz))))
          (.all (domain := signature.number)
            (.conj
              (.guard (.app (.app (weakenCtx _ signature.active) (.var (.vs (.vs .vz)))) (.var .vz))
                (.conj
                  (.atom (.app (.app (.app (weakenCtx _ signature.validEdge) (.var (.vs (.vs .vz))))
                    (.var .vz)) (.app (.var (.vs .vz)) (.var .vz))))
                  (.member (.app (.var (.vs .vz)) (.var .vz)))))
              (.atom (.imp
                (.not (.app (.app (weakenCtx _ signature.active) (.var (.vs (.vs .vz)))) (.var .vz)))
                (.eq (.app (.var (.vs .vz)) (.var .vz)) (weakenCtx _ signature.bottom))))))))))

def operator : ClosedTerm Const (PredicateFixedPoint.Operator signature.space) := signature.code.operator

/-- Replace the three fixed guards by typed terms while retaining the
constructor algebra, payload and slot types. -/
def withGuards
    (shape : ClosedTerm Const (signature.number ⇒ signature.payload ⇒ .prop))
    (active : ClosedTerm Const (signature.payload ⇒ signature.number ⇒ .prop))
    (edge : ClosedTerm Const (signature.payload ⇒ signature.number ⇒ signature.space ⇒ .prop)) : Signature Const :=
  { signature with validShape := shape, active := active, validEdge := edge }

def monotonicity : ProofSyntax Const ([] : List (ClosedFormula Const))
    (PredicateFixedPoint.monotone signature.operator) := signature.code.operator_monotone

def fixedPoint : ProofSyntax Const ([] : List (ClosedFormula Const))
    (PredicateFixedPoint.equation signature.operator) := signature.code.fixed_point

theorem monotonicity_functionExtensionalityFree :
    ProofSyntax.FunctionExtensionalityFree signature.monotonicity :=
  signature.code.operator_monotone_functionExtensionalityFree

theorem fixedPoint_functionExtensionalityFree :
    ProofSyntax.FunctionExtensionalityFree signature.fixedPoint :=
  signature.code.fixed_point_functionExtensionalityFree

variable (model : HenkinModel.{u,v,w} Base Const) (full : model.FullDomains)

def denotes {type : Ty Base} (term : ClosedTerm Const type) : Ty.denote model.Carrier type :=
  model.denote term (fun index => nomatch index)

theorem denote_closed {type : Ty Base} (term : ClosedTerm Const type) (valuation : model.Valuation []) :
    model.denote term valuation = denotes model term := by
  apply congrArg (model.denote term)
  funext type index
  exact nomatch index

include full

theorem operator_meaning (predicate : Ty.denote model.Carrier (signature.space ⇒ .prop))
    (point : Ty.denote model.Carrier signature.space) :
    (denotes model signature.operator predicate point).down ↔
      ∃ tag payload children,
        (denotes model signature.validShape tag payload).down ∧
        point = denotes model signature.construct tag payload children ∧
        ∀ position,
          ((denotes model signature.active payload position).down →
            (denotes model signature.validEdge payload position (children position)).down ∧
              (predicate (children position)).down) ∧
          (¬ (denotes model signature.active payload position).down →
            children position = denotes model signature.bottom) := by
  have admitted : ∀ type value, model.adm type value := full
  simp only [operator,PositivePredicate.Code.operator,code,PositivePredicate.Code.rename,
    PositivePredicate.Code.interpret,denotes,HenkinModel.denote,PreModel.denote,
    HOL.rename,PreModel.extend,rename_weakenCtx,HenkinModel.denote_weakenCtx,
    Rename.lift]
  simp only [model.eqv_iff_eq_of_fullDomains full,admitted,true_and,forall_true_left]
  rfl

/-- Guard equalities preserve the actual generated positive operator. -/
theorem withGuards_operator_denote
    (shape : ClosedTerm Const (signature.number ⇒ signature.payload ⇒ .prop))
    (active : ClosedTerm Const (signature.payload ⇒ signature.number ⇒ .prop))
    (edge : ClosedTerm Const (signature.payload ⇒ signature.number ⇒ signature.space ⇒ .prop))
    (shapeMeaning : denotes model shape = denotes model signature.validShape)
    (activeMeaning : denotes model active = denotes model signature.active)
    (edgeMeaning : denotes model edge = denotes model signature.validEdge) :
    denotes model (signature.withGuards shape active edge).operator = denotes model signature.operator := by
  funext predicate point
  apply ULift.ext
  apply propext
  rw [(signature.withGuards shape active edge).operator_meaning model full,
    signature.operator_meaning model full]
  simp only [withGuards, shapeMeaning, activeMeaning, edgeMeaning]

/-- Installed guards with the same denotations preserve the least predicate,
including its inactive-slot padding condition. -/
theorem withGuards_least_denote
    (shape : ClosedTerm Const (signature.number ⇒ signature.payload ⇒ .prop))
    (active : ClosedTerm Const (signature.payload ⇒ signature.number ⇒ .prop))
    (edge : ClosedTerm Const (signature.payload ⇒ signature.number ⇒ signature.space ⇒ .prop))
    (shapeMeaning : denotes model shape = denotes model signature.validShape)
    (activeMeaning : denotes model active = denotes model signature.active)
    (edgeMeaning : denotes model edge = denotes model signature.validEdge) :
    denotes model (PredicateFixedPoint.least (signature.withGuards shape active edge).operator) =
      denotes model (PredicateFixedPoint.least signature.operator) := by
  have operators := signature.withGuards_operator_denote model full shape active edge shapeMeaning activeMeaning edgeMeaning
  funext point
  apply ULift.ext
  apply propext
  simp only [denotes, PredicateFixedPoint.least_denote]
  change (∀ predicate, model.adm _ predicate →
    (∀ value, model.adm signature.space value →
      (denotes model (signature.withGuards shape active edge).operator predicate value).down → (predicate value).down) →
    (predicate point).down) ↔ _
  rw [operators]
  rfl

end Signature

#print axioms Signature.monotonicity
#print axioms Signature.fixedPoint
#print axioms Signature.operator_meaning
#print axioms Signature.withGuards_operator_denote
#print axioms Signature.withGuards_least_denote

end Mettapedia.Logic.HOL.RecursiveSpacePredicate
