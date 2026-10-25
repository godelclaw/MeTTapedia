import Mettapedia.Languages.Megalodon.HOLProofInference
import Mettapedia.Languages.Megalodon.ImpredicativeLogicalProofs

/-!
# Typed HOL readings of native logical proof combinators

The source formulas below use the original HOL constructors. Their computed
canonical codes are the exact propositions inferred for the existing native
proof programs. Universal elimination then instantiates these closed schemas
with arbitrary typed source arguments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HOLProofTemplates

open Mettapedia.Logic.HOL
open MathdataKernel HenkinTermInterpretation HOLTermEncoding HOLNormalForms HOLProofInference

variable {environment : Environment} {gamma : Ctx Base}

def falsityEliminationFormula : Formula (Constant environment) gamma :=
  .all (.imp .bot (.var .vz))

def conjunctionIntroductionFormula : Formula (Constant environment) gamma :=
  .all (.all (.imp (.var (.vs .vz))
    (.imp (.var .vz) (.and (.var (.vs .vz)) (.var .vz)))))

theorem falsityElimination_code :
    normalFormCode (falsityEliminationFormula (environment := environment) (gamma := gamma)) =
      ImpredicativeLogicalProofs.falsityEliminationStatement := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [falsityEliminationFormula, native, encode, expandEquality,
    ImpredicativeConnectives.expandInline, ImpredicativeConnectives.falsity,
    erase, variableIndex, reifyType, Tm.normalize, Tm.normalizeOne,
    ImpredicativeLogicalProofs.falsityEliminationStatement, ImpredicativeLogicalProofs.falsity]

theorem conjunctionIntroduction_code :
    normalFormCode (conjunctionIntroductionFormula (environment := environment) (gamma := gamma)) =
      ImpredicativeLogicalProofs.conjunctionIntroductionStatement := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [conjunctionIntroductionFormula, native, encode, expandEquality,
    ImpredicativeConnectives.expandInline, ImpredicativeConnectives.conjunctionFormula,
    weaken, Rename.weaken, erase, variableIndex, reifyType,
    Tm.normalize, Tm.normalizeOne, Tm.shift,
    ImpredicativeLogicalProofs.conjunctionIntroductionStatement, ImpredicativeLogicalProofs.conjunction]

theorem falsityElimination_infers (depth : Nat)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions ImpredicativeLogicalProofs.falsityElimination falsityEliminationFormula := by
  refine ⟨32, ?_⟩
  rw [falsityElimination_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (ImpredicativeLogicalProofs.falsityElimination_infers environment depth
      (gamma.map reifyType) (assumptions.map normalFormCode))

theorem conjunctionIntroduction_infers (depth : Nat)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions ImpredicativeLogicalProofs.conjunctionIntroduction
      conjunctionIntroductionFormula := by
  refine ⟨32, ?_⟩
  rw [conjunctionIntroduction_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (ImpredicativeLogicalProofs.conjunctionIntroduction_infers environment depth
      (gamma.map reifyType) (assumptions.map normalFormCode))

#print axioms falsityElimination_code
#print axioms conjunctionIntroduction_code
#print axioms falsityElimination_infers
#print axioms conjunctionIntroduction_infers


def conjunctionLeftFormula : Formula (Constant environment) gamma :=
  .all (.all (.imp (.and (.var (.vs .vz)) (.var .vz)) (.var (.vs .vz))))

theorem conjunctionLeft_code :
    normalFormCode (conjunctionLeftFormula (environment := environment) (gamma := gamma)) =
      ImpredicativeLogicalProofs.conjunctionLeftStatement := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [conjunctionLeftFormula, native, encode, expandEquality,
    ImpredicativeConnectives.expandInline, ImpredicativeConnectives.conjunctionFormula,
    weaken, Rename.weaken, erase, variableIndex, reifyType,
    Tm.normalize, Tm.normalizeOne, Tm.shift,
    ImpredicativeLogicalProofs.conjunctionLeftStatement, ImpredicativeLogicalProofs.conjunction]

theorem conjunctionLeft_infers (depth : Nat)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions ImpredicativeLogicalProofs.conjunctionLeft
      (conjunctionLeftFormula) := by
  refine ⟨32, ?_⟩
  rw [conjunctionLeft_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (ImpredicativeLogicalProofs.conjunctionLeft_infers environment depth
      (gamma.map reifyType) (assumptions.map normalFormCode))

def conjunctionRightFormula : Formula (Constant environment) gamma :=
  .all (.all (.imp (.and (.var (.vs .vz)) (.var .vz)) (.var .vz)))

theorem conjunctionRight_code :
    normalFormCode (conjunctionRightFormula (environment := environment) (gamma := gamma)) =
      ImpredicativeLogicalProofs.conjunctionRightStatement := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [conjunctionRightFormula, native, encode, expandEquality,
    ImpredicativeConnectives.expandInline, ImpredicativeConnectives.conjunctionFormula,
    weaken, Rename.weaken, erase, variableIndex, reifyType,
    Tm.normalize, Tm.normalizeOne, Tm.shift,
    ImpredicativeLogicalProofs.conjunctionRightStatement, ImpredicativeLogicalProofs.conjunction]

theorem conjunctionRight_infers (depth : Nat)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions ImpredicativeLogicalProofs.conjunctionRight
      (conjunctionRightFormula) := by
  refine ⟨32, ?_⟩
  rw [conjunctionRight_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (ImpredicativeLogicalProofs.conjunctionRight_infers environment depth
      (gamma.map reifyType) (assumptions.map normalFormCode))

def disjunctionLeftFormula : Formula (Constant environment) gamma :=
  .all (.all (.imp (.var (.vs .vz)) (.or (.var (.vs .vz)) (.var .vz))))

theorem disjunctionLeft_code :
    normalFormCode (disjunctionLeftFormula (environment := environment) (gamma := gamma)) =
      ImpredicativeLogicalProofs.disjunctionLeftStatement := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [disjunctionLeftFormula, native, encode, expandEquality,
    ImpredicativeConnectives.expandInline, ImpredicativeConnectives.disjunctionFormula,
    weaken, Rename.weaken, erase, variableIndex, reifyType,
    Tm.normalize, Tm.normalizeOne, Tm.shift,
    ImpredicativeLogicalProofs.disjunctionLeftStatement, ImpredicativeLogicalProofs.disjunction]

theorem disjunctionLeft_infers (depth : Nat)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions ImpredicativeLogicalProofs.disjunctionLeft
      (disjunctionLeftFormula) := by
  refine ⟨32, ?_⟩
  rw [disjunctionLeft_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (ImpredicativeLogicalProofs.disjunctionLeft_infers environment depth
      (gamma.map reifyType) (assumptions.map normalFormCode))

def disjunctionRightFormula : Formula (Constant environment) gamma :=
  .all (.all (.imp (.var .vz) (.or (.var (.vs .vz)) (.var .vz))))

theorem disjunctionRight_code :
    normalFormCode (disjunctionRightFormula (environment := environment) (gamma := gamma)) =
      ImpredicativeLogicalProofs.disjunctionRightStatement := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [disjunctionRightFormula, native, encode, expandEquality,
    ImpredicativeConnectives.expandInline, ImpredicativeConnectives.disjunctionFormula,
    weaken, Rename.weaken, erase, variableIndex, reifyType,
    Tm.normalize, Tm.normalizeOne, Tm.shift,
    ImpredicativeLogicalProofs.disjunctionRightStatement, ImpredicativeLogicalProofs.disjunction]

theorem disjunctionRight_infers (depth : Nat)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions ImpredicativeLogicalProofs.disjunctionRight
      (disjunctionRightFormula) := by
  refine ⟨32, ?_⟩
  rw [disjunctionRight_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (ImpredicativeLogicalProofs.disjunctionRight_infers environment depth
      (gamma.map reifyType) (assumptions.map normalFormCode))

def disjunctionEliminationFormula : Formula (Constant environment) gamma :=
  .all (.all (.all
    (.imp (.or (.var (.vs (.vs .vz))) (.var (.vs .vz)))
      (.imp (.imp (.var (.vs (.vs .vz))) (.var .vz))
        (.imp (.imp (.var (.vs .vz)) (.var .vz)) (.var .vz))))))

theorem disjunctionElimination_code :
    normalFormCode (disjunctionEliminationFormula (environment := environment) (gamma := gamma)) =
      ImpredicativeLogicalProofs.disjunctionEliminationStatement := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [disjunctionEliminationFormula, native, encode, expandEquality,
    ImpredicativeConnectives.expandInline, ImpredicativeConnectives.disjunctionFormula,
    weaken, Rename.weaken, erase, variableIndex, reifyType,
    Tm.normalize, Tm.normalizeOne, Tm.shift,
    ImpredicativeLogicalProofs.disjunctionEliminationStatement, ImpredicativeLogicalProofs.disjunction]

theorem disjunctionElimination_infers (depth : Nat)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions ImpredicativeLogicalProofs.disjunctionElimination
      (disjunctionEliminationFormula) := by
  refine ⟨32, ?_⟩
  rw [disjunctionElimination_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (ImpredicativeLogicalProofs.disjunctionElimination_infers environment depth
      (gamma.map reifyType) (assumptions.map normalFormCode))

def existentialIntroductionFormula (domain : Ty Base) : Formula (Constant environment) gamma :=
  .all (σ := domain ⇒ .prop) (.all (σ := domain)
    (.imp (.app (.var (.vs .vz)) (.var .vz))
      (.ex (σ := domain) (.app (.var (.vs (.vs .vz))) (.var .vz)))))

theorem existentialIntroduction_code (domain : Ty Base) :
    normalFormCode (existentialIntroductionFormula domain (environment := environment) (gamma := gamma)) =
      ImpredicativeLogicalProofs.existentialIntroductionStatement (reifyType domain) := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [existentialIntroductionFormula, native, encode, expandEquality,
    ImpredicativeConnectives.expandInline, ImpredicativeConnectives.existentialInline,
    rename, Rename.lift, Rename.weaken, erase, variableIndex, reifyType,
    Tm.normalize, Tm.normalizeOne, Tm.shift,
    ImpredicativeLogicalProofs.existentialIntroductionStatement, ImpredicativeLogicalProofs.existential]

theorem existentialIntroduction_infers (depth : Nat) (domain : Ty Base)
    (formed : (reifyType domain).plainWellFormed depth = true)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions (ImpredicativeLogicalProofs.existentialIntroduction (reifyType domain))
      (existentialIntroductionFormula domain) := by
  refine ⟨32, ?_⟩
  rw [existentialIntroduction_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (ImpredicativeLogicalProofs.existentialIntroduction_infers environment depth (reifyType domain) formed
      (gamma.map reifyType) (assumptions.map normalFormCode))

def existentialEliminationFormula (domain : Ty Base) : Formula (Constant environment) gamma :=
  .all (σ := domain ⇒ .prop) (.all (σ := .prop)
    (.imp (.ex (σ := domain) (.app (.var (.vs (.vs .vz))) (.var .vz)))
      (.imp (.all (σ := domain)
        (.imp (.app (.var (.vs (.vs .vz))) (.var .vz)) (.var (.vs .vz))))
        (.var .vz))))

theorem existentialElimination_code (domain : Ty Base) :
    normalFormCode (existentialEliminationFormula domain (environment := environment) (gamma := gamma)) =
      ImpredicativeLogicalProofs.existentialEliminationStatement (reifyType domain) := by
  apply normalFormCode_of_normalizes (fuel := 32)
  simp [existentialEliminationFormula, native, encode, expandEquality,
    ImpredicativeConnectives.expandInline, ImpredicativeConnectives.existentialInline,
    rename, Rename.lift, Rename.weaken, erase, variableIndex, reifyType,
    Tm.normalize, Tm.normalizeOne, Tm.shift,
    ImpredicativeLogicalProofs.existentialEliminationStatement, ImpredicativeLogicalProofs.existential]

theorem existentialElimination_infers (depth : Nat) (domain : Ty Base)
    (formed : (reifyType domain).plainWellFormed depth = true)
    (assumptions : List (Formula (Constant environment) gamma)) :
    Infers depth assumptions (ImpredicativeLogicalProofs.existentialElimination (reifyType domain))
      (existentialEliminationFormula domain) := by
  refine ⟨32, ?_⟩
  rw [existentialElimination_code]
  exact ProofJudgment.proves_of_infer (context := context depth assumptions)
    (ImpredicativeLogicalProofs.existentialElimination_infers environment depth (reifyType domain) formed
      (gamma.map reifyType) (assumptions.map normalFormCode))

#print axioms conjunctionLeft_code
#print axioms conjunctionLeft_infers
#print axioms conjunctionRight_code
#print axioms conjunctionRight_infers
#print axioms disjunctionLeft_code
#print axioms disjunctionLeft_infers
#print axioms disjunctionRight_code
#print axioms disjunctionRight_infers
#print axioms disjunctionElimination_code
#print axioms disjunctionElimination_infers
#print axioms existentialIntroduction_code
#print axioms existentialIntroduction_infers
#print axioms existentialElimination_code
#print axioms existentialElimination_infers

end Mettapedia.Languages.Megalodon.HOLProofTemplates
