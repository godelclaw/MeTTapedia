import Mettapedia.Logic.HOL.NaturalRecursionProofs
import Mettapedia.Logic.HOL.ProofSyntaxCongruence

/-!
# Length-indexed vector recursion from natural recursion

The natural recursor operates at the function carrier `vector ⇒ result`.
At zero it returns the supplied base value; at a successor it applies the
source-ordered method to the predecessor, head, tail and recursive result.
The computation proofs retain their natural-recursion and constructor-
projection premises. No vector recursion equation is assumed.

These equations concern a total carrier operation. Dependent result typing
still requires the vector membership guards and their elimination laws.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorRecursionProofs

universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
    {number element vector result : Ty Base}

abbrev Method (number element vector result : Ty Base) :=
  number ⇒ element ⇒ vector ⇒ result ⇒ result

def constant (base : Term Const Γ result) : Term Const Γ (vector ⇒ result) :=
  .lam (weaken base)

def stepBody (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (method : Term Const Γ (Method number element vector result))
    (previous : Term Const Γ (vector ⇒ result)) (index : Term Const Γ number)
    (value : Term Const Γ vector) : Term Const Γ result :=
  .app (.app (.app (.app method index) (.app head value)) (.app tail value))
    (.app previous (.app tail value))

def stepAt (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (method : Term Const Γ (Method number element vector result))
    (previous : Term Const Γ (vector ⇒ result)) (index : Term Const Γ number) :
    Term Const Γ (vector ⇒ result) :=
  .lam (stepBody (weaken head) (weaken tail) (weaken method) (weaken previous) (weaken index) (.var .vz))

def stepFor (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (method : Term Const Γ (Method number element vector result))
    (previous : Term Const Γ (vector ⇒ result)) : Term Const Γ (number ⇒ vector ⇒ result) :=
  .lam (stepAt (weaken head) (weaken tail) (weaken method) (weaken previous) (.var .vz))

def step (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (method : Term Const Γ (Method number element vector result)) :
    Term Const Γ (NaturalRecursionProofs.Method number (vector ⇒ result)) :=
  .lam (stepFor (weaken head) (weaken tail) (weaken method) (.var .vz))

def recursor (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ vector ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (base : Term Const Γ result) (method : Term Const Γ (Method number element vector result)) :
    Term Const Γ (number ⇒ vector ⇒ result) :=
  NaturalRecursionProofs.recursor selection zero successor (constant base) (step head tail method)

@[simp] theorem subst_constant (σ : Subst Const Γ Ξ) (base : Term Const Γ result) :
    subst σ (constant (vector := vector) base) = constant (subst σ base) := by
  simp [constant, subst]

@[simp] theorem subst_stepBody (σ : Subst Const Γ Ξ)
    (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (method : Term Const Γ (Method number element vector result))
    (previous : Term Const Γ (vector ⇒ result)) (index : Term Const Γ number)
    (value : Term Const Γ vector) :
    subst σ (stepBody head tail method previous index value) =
      stepBody (subst σ head) (subst σ tail) (subst σ method) (subst σ previous) (subst σ index) (subst σ value) := rfl

@[simp] theorem subst_stepAt (σ : Subst Const Γ Ξ)
    (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (method : Term Const Γ (Method number element vector result))
    (previous : Term Const Γ (vector ⇒ result)) (index : Term Const Γ number) :
    subst σ (stepAt head tail method previous index) =
      stepAt (subst σ head) (subst σ tail) (subst σ method) (subst σ previous) (subst σ index) := by
  simp [stepAt, subst, subst_weaken, Subst.lift]

@[simp] theorem subst_stepFor (σ : Subst Const Γ Ξ)
    (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (method : Term Const Γ (Method number element vector result))
    (previous : Term Const Γ (vector ⇒ result)) :
    subst σ (stepFor head tail method previous) =
      stepFor (subst σ head) (subst σ tail) (subst σ method) (subst σ previous) := by
  simp [stepFor, subst, subst_weaken, Subst.lift]

@[simp] theorem subst_step (σ : Subst Const Γ Ξ)
    (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (method : Term Const Γ (Method number element vector result)) :
    subst σ (step head tail method) = step (subst σ head) (subst σ tail) (subst σ method) := by
  simp [step, subst, subst_weaken, Subst.lift]

@[simp] theorem subst_recursor (σ : Subst Const Γ Ξ)
    (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ vector ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (base : Term Const Γ result) (method : Term Const Γ (Method number element vector result)) :
    subst σ (recursor selection zero successor head tail base method) =
      recursor (subst σ selection) (subst σ zero) (subst σ successor)
        (subst σ head) (subst σ tail) (subst σ base) (subst σ method) := by
  simp [recursor, NaturalRecursionProofs.recursor, SelectionProofs.selected, subst]

variable {Δ : List (Formula Const Γ)}

def constant_apply (base : Term Const Γ result) (value : Term Const Γ vector) :
    ProofSyntax Const Δ (.eq (.app (constant base) value) base) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta value (weaken base))
  simp [constant, instantiate]

def step_apply (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (method : Term Const Γ (Method number element vector result))
    (previous : Term Const Γ (vector ⇒ result)) (index : Term Const Γ number)
    (value : Term Const Γ vector) :
    ProofSyntax Const Δ (.eq (.app (.app (.app (step head tail method) previous) index) value)
      (stepBody head tail method previous index value)) := by
  have first : ProofSyntax Const Δ
      (.eq (.app (step head tail method) previous) (stepFor head tail method previous)) := by
    apply ProofSyntax.castIndices rfl ?_
      (.beta previous (stepFor (weaken head) (weaken tail) (weaken method) (.var .vz)))
    simp [step, instantiate, subst, Subst.single]
  have second : ProofSyntax Const Δ
      (.eq (.app (stepFor head tail method previous) index) (stepAt head tail method previous index)) := by
    apply ProofSyntax.castIndices rfl ?_
      (.beta index (stepAt (weaken head) (weaken tail) (weaken method) (weaken previous) (.var .vz)))
    simp [stepFor, instantiate, subst, Subst.single]
  have third : ProofSyntax Const Δ
      (.eq (.app (stepAt head tail method previous index) value) (stepBody head tail method previous index value)) := by
    apply ProofSyntax.castIndices rfl ?_
      (.beta value (stepBody (weaken head) (weaken tail) (weaken method) (weaken previous) (weaken index) (.var .vz)))
    simp [stepAt, instantiate, subst, Subst.single]
  exact .eqTrans (.eqApp value (.eqApp index first)) (.eqTrans (.eqApp value second) third)

def atZero (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ vector ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (base : Term Const Γ result) (method : Term Const Γ (Method number element vector result))
    (value : Term Const Γ vector)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement zero successor (vector ⇒ result))) :
    ProofSyntax Const Δ (.eq (.app (.app (recursor selection zero successor head tail base method) zero) value) base) :=
  .eqTrans (.eqApp value (NaturalRecursionProofs.atZero selection zero successor
    (constant base) (step head tail method) choice recursion)) (constant_apply base value)

def atSuccessor (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ vector ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (base : Term Const Γ result) (method : Term Const Γ (Method number element vector result))
    (index : Term Const Γ number) (value : Term Const Γ vector)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement zero successor (vector ⇒ result))) :
    ProofSyntax Const Δ (.eq
      (.app (.app (recursor selection zero successor head tail base method) (.app successor index)) value)
      (stepBody head tail method (.app (recursor selection zero successor head tail base method) index) index value)) :=
  .eqTrans (.eqApp value (NaturalRecursionProofs.atSuccessor selection zero successor
    (constant base) (step head tail method) index choice recursion))
    (step_apply head tail method (.app (recursor selection zero successor head tail base method) index) index value)

/-- Constructor projections suffice to derive the cons computation row. The
recursive call retains the supplied tail and predecessor index. -/
def atCons (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ vector ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (cons : Term Const Γ (number ⇒ element ⇒ vector ⇒ vector))
    (base : Term Const Γ result) (method : Term Const Γ (Method number element vector result))
    (index : Term Const Γ number) (first : Term Const Γ element) (rest : Term Const Γ vector)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement zero successor (vector ⇒ result)))
    (headProof : ProofSyntax Const Δ (.eq (.app head (.app (.app (.app cons index) first) rest)) first))
    (tailProof : ProofSyntax Const Δ (.eq (.app tail (.app (.app (.app cons index) first) rest)) rest)) :
    ProofSyntax Const Δ (.eq
      (.app (.app (recursor selection zero successor head tail base method) (.app successor index))
        (.app (.app (.app cons index) first) rest))
      (.app (.app (.app (.app method index) first) rest)
        (.app (.app (recursor selection zero successor head tail base method) index) rest))) :=
  .eqTrans (atSuccessor selection zero successor head tail base method index
    (.app (.app (.app cons index) first) rest) choice recursion)
    (ProofSyntax.appCongr (ProofSyntax.appCongr (.eqAppArg (.app method index) headProof) tailProof)
      (.eqAppArg (.app (recursor selection zero successor head tail base method) index) tailProof))

theorem step_apply_free (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (method : Term Const Γ (Method number element vector result))
    (previous : Term Const Γ (vector ⇒ result)) (index : Term Const Γ number) (value : Term Const Γ vector) :
    (step_apply (Δ := Δ) head tail method previous index value).FunctionExtensionalityFree := by
  simp [step_apply, ProofSyntax.FunctionExtensionalityFree]

theorem atZero_free (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ vector ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (base : Term Const Γ result) (method : Term Const Γ (Method number element vector result))
    (value : Term Const Γ vector)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement zero successor (vector ⇒ result)))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree) :
    (atZero selection zero successor head tail base method value choice recursion).FunctionExtensionalityFree := by
  simp [atZero, constant_apply, NaturalRecursionProofs.atZero, ProofSyntax.FunctionExtensionalityFree,
    NaturalRecursionProofs.computation_free, choiceFree, recursionFree]

theorem atCons_free (selection : Term Const Γ (SelectionProofs.Selection (number ⇒ vector ⇒ result)))
    (zero : Term Const Γ number) (successor : Term Const Γ (number ⇒ number))
    (head : Term Const Γ (vector ⇒ element)) (tail : Term Const Γ (vector ⇒ vector))
    (cons : Term Const Γ (number ⇒ element ⇒ vector ⇒ vector))
    (base : Term Const Γ result) (method : Term Const Γ (Method number element vector result))
    (index : Term Const Γ number) (first : Term Const Γ element) (rest : Term Const Γ vector)
    (choice : ProofSyntax Const Δ (SelectionProofs.principle selection))
    (recursion : ProofSyntax Const Δ (NaturalRecursionProofs.statement zero successor (vector ⇒ result)))
    (headProof : ProofSyntax Const Δ (.eq (.app head (.app (.app (.app cons index) first) rest)) first))
    (tailProof : ProofSyntax Const Δ (.eq (.app tail (.app (.app (.app cons index) first) rest)) rest))
    (choiceFree : choice.FunctionExtensionalityFree) (recursionFree : recursion.FunctionExtensionalityFree)
    (headFree : headProof.FunctionExtensionalityFree) (tailFree : tailProof.FunctionExtensionalityFree) :
    (atCons selection zero successor head tail cons base method index first rest choice recursion headProof tailProof).FunctionExtensionalityFree := by
  simp [atCons, atSuccessor, ProofSyntax.appCongr, NaturalRecursionProofs.atSuccessor,
    ProofSyntax.FunctionExtensionalityFree, step_apply_free, NaturalRecursionProofs.computation_free,
    choiceFree, recursionFree, headFree, tailFree]

#print axioms subst_recursor
#print axioms atZero
#print axioms atCons
#print axioms atCons_free
end Mettapedia.Logic.HOL.VectorRecursionProofs
