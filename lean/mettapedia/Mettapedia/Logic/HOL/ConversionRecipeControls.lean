import Mettapedia.Logic.HOL.ConversionRecipes

/-!
# Conversion-policy and elaboration controls

These controls use two base sorts, genuine typed constants, conversions
under binders and logical retyping. Policies differ while their target is
the same retained HOL calculus. Distinct receipts remain distinct recipes,
and an arbitrary producer earns no authority from suggesting one.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.ConversionRecipes.Controls

inductive SortName where
  | first
  | second
  deriving DecidableEq

abbrev A : Ty SortName := .base .first
abbrev B : Ty SortName := .base .second

inductive Constant : Ty SortName → Type where
  | valueA : Constant A
  | valueB : Constant B
  | functionA : Constant (A ⇒ A)
  | otherFunctionA : Constant (A ⇒ A)
  | functionB : Constant (B ⇒ B)
  | fromBToA : Constant (B ⇒ A)
  | fromAToB : Constant (A ⇒ B)
  deriving DecidableEq

def functionA : ClosedTerm Constant (A ⇒ A) := .const .functionA
def otherFunctionA : ClosedTerm Constant (A ⇒ A) := .const .otherFunctionA
def functionB : ClosedTerm Constant (B ⇒ B) := .const .functionB

def expand {Γ : Ctx SortName} {σ τ : Ty SortName}
    (function : Term Constant Γ (σ ⇒ τ)) : Term Constant Γ (σ ⇒ τ) :=
  .lam (.app (weaken function) (.var .vz))

def equations : List (DefiningEquation Constant) :=
  [ConversionElaborationControls.etaEquation A A,
   ConversionElaborationControls.etaEquation B B]

def licensed : EquationProofs equations :=
  (ConversionElaborationControls.etaProofs A A).append
    (ConversionElaborationControls.etaProofs B B)

def firstOnly : Policy SortName equations.length where
  beta τ := decide (τ = A)
  eta σ τ := decide (σ = A ∧ τ = A)
  equation _ := false

def betaOnly : Policy SortName equations.length := .betaOnly _
def betaEta : Policy SortName equations.length := .betaEta _
def all : Policy SortName equations.length := .all _

def etaA : Recipe equations [] (A ⇒ A) :=
  .leaf (expand functionA) functionA (.eta functionA)

def etaB : Recipe equations [] (B ⇒ B) :=
  .leaf (expand functionB) functionB (.eta functionB)

def singletonSub {Γ : Ctx SortName} {τ : Ty SortName}
    (term : Term Constant Γ τ) : Subst Constant [τ] Γ
  | _, .vz => term
  | _, .vs impossible => nomatch impossible

def equationA : Recipe equations [] (A ⇒ A) :=
  .leaf (expand functionA) functionA (.equation ⟨0, by decide⟩ (singletonSub functionA) rfl)

def equationBWrongSource : Recipe equations [] (B ⇒ B) :=
  .leaf functionB functionB (.equation ⟨1, by decide⟩ (singletonSub functionB) rfl)

def redexA : ClosedTerm Constant A := .app (.lam (.var .vz)) (.const .valueA)
def redexB : ClosedTerm Constant B := .app (.lam (.var .vz)) (.const .valueB)

def betaA : Recipe equations [] A := .leaf redexA (.const .valueA) (.beta [])
def betaB : Recipe equations [] B := .leaf redexB (.const .valueB) (.beta [])

def actualExecution : ContextualTrinity.Execution redexA (.const .valueA) := by
  change ContextualTrinity.Execution
    (.app (.lam (.var .vz : Term Constant [A] A)) (.const Constant.valueA))
    (.const Constant.valueA)
  exact .step (.beta (.var .vz) (.const Constant.valueA)) (.done (.const Constant.valueA))

def hiddenBSource : ClosedTerm Constant A := .app (.const .fromBToA) redexB
def hiddenBTarget : ClosedTerm Constant A := .app (.const .fromBToA) (.const .valueB)
def hiddenASource : ClosedTerm Constant B := .app (.const .fromAToB) redexA
def hiddenATarget : ClosedTerm Constant B := .app (.const .fromAToB) (.const .valueA)

def inside : Term Constant [A ⇒ A] (A ⇒ A) := expand (.var .vz)

def binderEta : Recipe equations [] ((A ⇒ A) ⇒ (A ⇒ A)) :=
  .leaf (.lam inside) (.lam (.var .vz)) (.lam inside (.eta (.var .vz)))

def holeBody : Formula Constant [(A ⇒ A), (A ⇒ A)] :=
  .eq (.var .vz) (.var (.vs .vz))

def quantifiedSource : ClosedFormula Constant := .all (.eq inside (.var .vz))
def quantifiedTarget : ClosedFormula Constant := .all (σ := A ⇒ A) (.eq (.var .vz) (.var .vz))

def quantifiedEta : Recipe equations [] .prop :=
  .leaf quantifiedSource quantifiedTarget
    (.all (.eq inside (.var .vz)) (.congr holeBody inside (.eta (.var .vz))))

/-- A logical conclusion is obtained through checked equality elimination,
with the original empty assumption list and quantified type intact. -/
def quantifiedProof : ProofSyntax Constant [] quantifiedSource :=
  convertProof licensed betaEta (source := quantifiedTarget) (target := quantifiedSource)
    (.symm quantifiedEta) (by decide)
    (.allI (.eqRefl (.var .vz)))

def directQuantifiedProof : ProofSyntax Constant [] quantifiedSource :=
  .allI (.eta (.var .vz))

def detourA : Recipe equations [] (A ⇒ A) := .trans etaA (.refl functionA)

def badJoin : Recipe equations [] (A ⇒ A) := .trans etaA (.refl otherFunctionA)

def mixedProducer (_claim : ClosedTerm Constant (A ⇒ A) × ClosedTerm Constant (A ⇒ A)) :
    List (Recipe equations [] (A ⇒ A)) := [badJoin, etaA, etaA]

def submittedProof : ProofSyntax Constant [] (.eq (expand functionA) functionA) :=
  elaborateSubmission licensed betaEta mixedProducer (expand functionA) functionA etaA
    (by
      apply (Mettapedia.GSLT.LanguageDef.HeuristicEvidence.mem_screen _ _ _ _).2
      exact ⟨List.mem_cons_of_mem _ List.mem_cons_self, by decide⟩) []

def proofNodes {Γ : Ctx SortName} {τ : Ty SortName} (policy : Policy SortName equations.length)
    (source target : Term Constant Γ τ) (recipe : Recipe equations Γ τ) : Nat :=
  ((elaborate? licensed policy source target recipe []).map ProofSyntax.nodeCount).getD 0

/-- The two routes agree at their endpoint equality, but their submitted
declaration and primitive-rule witnesses are still distinguishable. -/
theorem eta_and_equation_recipes_distinct : etaA ≠ equationA := by
  intro equal
  cases equal

theorem etaProofNodes : proofNodes betaEta (expand functionA) functionA etaA = 1 := by decide +kernel

theorem detourProofNodes : proofNodes betaEta (expand functionA) functionA detourA = 3 := by decide +kernel

/-- Same conclusion does not mean the same retained proof or size. -/
theorem proof_costs_differ :
    proofNodes betaEta (expand functionA) functionA etaA <
      proofNodes betaEta (expand functionA) functionA detourA := by
  rw [etaProofNodes, detourProofNodes]
  decide

theorem beta_extends_eta : betaOnly.Extends betaEta := by
  constructor
  · intro τ _; rfl
  · intro σ τ impossible; cases impossible
  · intro index impossible; cases impossible

theorem first_extends_all : firstOnly.Extends all := by
  constructor <;> intros <;> rfl

/-- Eta policy growth is directional: the beta profile cannot reflect the
eta permission on the first sort. -/
theorem eta_does_not_extend_beta : ¬ betaEta.Extends betaOnly := by
  intro extension
  have impossible := extension.eta A A rfl
  cases impossible

theorem joinedObservation :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      (theory equations (firstOnly.join betaOnly) [] (A ⇒ A))).satisfies (S := ())
        (expand functionA) (nativeType equations (firstOnly.join betaOnly) functionA).pred := by
  apply observed_mono (Policy.extends_join_left firstOnly betaOnly)
  exact (observed_iff_accepted licensed firstOnly _ _).2 ⟨etaA, by decide⟩

def verdicts : List (String × Bool) :=
  [("policy beta first sort", (checker licensed firstOnly [] A).check (redexA, .const .valueA) betaA),
   ("policy maintained execution compiles", (checker licensed betaOnly [] A).check
      (redexA, .const .valueA) (executionRecipe equations actualExecution)),
   ("policy beta second sort refuses", !((checker licensed firstOnly [] B).check (redexB, .const .valueB) betaB)),
   ("policy inner disallowed redex refuses", !((checker licensed firstOnly [] A).check
      (hiddenBSource, hiddenBTarget) (.leaf hiddenBSource hiddenBTarget (.beta [.argument])))),
   ("policy inner allowed redex survives outer sort", (checker licensed firstOnly [] B).check
      (hiddenASource, hiddenATarget) (.leaf hiddenASource hiddenATarget (.beta [.argument]))),
   ("policy eta first sort", (checker licensed firstOnly [] (A ⇒ A)).check (expand functionA, functionA) etaA),
   ("policy eta second sort refuses", !((checker licensed firstOnly [] (B ⇒ B)).check (expand functionB, functionB) etaB)),
   ("policy beta profile refuses eta evidence", !((checker licensed betaOnly [] (A ⇒ A)).check
      (expand functionA, functionA) etaA)),
   ("policy eta enabled on both sorts", (checker licensed betaEta [] (B ⇒ B)).check (expand functionB, functionB) etaB),
   ("policy licensed equation", (checker licensed all [] (A ⇒ A)).check (expand functionA, functionA) equationA),
   ("policy theorem does not enable submitted equation", !((checker licensed betaEta [] (A ⇒ A)).check
      (expand functionA, functionA) equationA)),
   ("policy equation source mismatch", !((checker licensed all [] (B ⇒ B)).check
      (functionB, functionB) equationBWrongSource)),
   ("policy eta under lambda", (checker licensed betaEta [] ((A ⇒ A) ⇒ (A ⇒ A))).check
      (.lam inside, .lam (.var .vz)) binderEta),
   ("policy disabled eta under lambda", !((checker licensed betaOnly [] ((A ⇒ A) ⇒ (A ⇒ A))).check
      (.lam inside, .lam (.var .vz)) binderEta)),
   ("policy eta under quantifier and equality", (checker licensed betaEta [] .prop).check
      (quantifiedSource, quantifiedTarget) quantifiedEta),
   ("policy changed root refuses", !((checker licensed betaEta [] (A ⇒ A)).check
      (expand functionA, otherFunctionA) etaA)),
   ("policy mismatched intermediate refuses", !((checker licensed betaEta [] (A ⇒ A)).check
      (expand functionA, otherFunctionA) badJoin)),
   ("policy bad beta position refuses", !((checker licensed betaEta [] A).check
      (redexA, .const .valueA) (.leaf redexA (.const .valueA) (.beta [.body])))),
   ("policy eta proof recording", proofNodes betaEta (expand functionA) functionA etaA == 1),
   ("policy declaration proof recording", proofNodes all (expand functionA) functionA equationA == 1),
   ("policy same equality larger retained proof", proofNodes betaEta (expand functionA) functionA detourA == 3),
   ("policy quantified logical evidence", quantifiedProof.nodeCount > directQuantifiedProof.nodeCount),
   ("policy duplicate suggestions retained", (Mettapedia.GSLT.LanguageDef.HeuristicEvidence.screen
      (checker licensed betaEta [] (A ⇒ A)) (expand functionA, functionA)
      (mixedProducer (expand functionA, functionA))).length == 2),
   ("policy selected suggestion carries proof", submittedProof.nodeCount == 1),
   ("policy empty suggestion is not refutation", (Mettapedia.GSLT.LanguageDef.HeuristicEvidence.screen
      (checker licensed betaEta [] (A ⇒ A)) (expand functionA, functionA) []).isEmpty),
   ("policy recording refuses bad suggestion", (elaborate? licensed betaEta
      (expand functionA) otherFunctionA badJoin []).isNone)]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

end Mettapedia.Logic.HOL.ConversionRecipes.Controls
