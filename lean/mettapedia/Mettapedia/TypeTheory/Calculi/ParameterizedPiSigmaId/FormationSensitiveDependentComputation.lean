import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.SigmaConversionBoundary
import Mettapedia.TypeTheory.ContextualDependentSequencing

/-!
# Effectful selection of formation-sensitive dependent pairs

The answer types of the existing contextual program carry complete native
formation-sensitive judgments. A selected admitted value `a : A` indexes the
continuation's admitted result `b : B[a]`; independently admitted Sigma
formation then licenses the existing native pair constructor.

The isolated-world handler retains the selected branch, final state and
ordered deferred intents. Renaming and substitution below concern native
values and their judgments, not effectful substitutions of an object-language
CBPV calculus. No new evaluator, total type checker, conversion qualification
or adoption of this candidate judgment is asserted.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitive.DependentComputation

open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
open Mettapedia.TypeTheory.ContextualComputationKleisli.Program (bindSigma)
open Mettapedia.TypeTheory.ContextualDependentSequencing

variable {Head : Type} {R : Rules Head} {n m : Nat}
variable {Γ : Ctx Head n} {Δ : Ctx Head m} {A : Tm Head n} {B : Tm Head (n + 1)}

/-- An existing native term with its full formation-sensitive admission. -/
abbrev TypedValue (R : Rules Head) (Γ : Ctx Head n) (A : Tm Head n) :=
  { term : Tm Head n // Judgment R Γ term A }

namespace TypedValue

def rename {ρ : Ren n m} (target : ContextFormation R Δ) (compatible : CtxRen Γ Δ ρ)
    (value : TypedValue R Γ A) : TypedValue R Δ (Presentation.rename ρ A) :=
  ⟨Presentation.rename ρ value.val, target, value.property.typing.renameTyping compatible⟩

def substitute {σ : Sub Head n m} (target : ContextFormation R Δ) (typed : CtxMor R Γ Δ σ)
    (value : TypedValue R Γ A) : TypedValue R Δ (subst σ A) :=
  ⟨subst σ value.val, value.property.substitute target typed⟩

/-- Reindex the dependent fibre using the actual capture-avoiding law. -/
def renameFibre {ρ : Ren n m} (target : ContextFormation R Δ) (compatible : CtxRen Γ Δ ρ)
    (first : TypedValue R Γ A) (second : TypedValue R Γ (inst0 first.val B)) :
    TypedValue R Δ (inst0 (Presentation.rename ρ first.val)
      (Presentation.rename (liftRen ρ) B)) :=
  ⟨Presentation.rename ρ second.val, target, by
    have typing := second.property.typing.renameTyping compatible
    rw [rename_inst0] at typing
    exact typing⟩

/-- Typed substitution transports the fibre at the selected native value. -/
def substituteFibre {σ : Sub Head n m} (target : ContextFormation R Δ) (typed : CtxMor R Γ Δ σ)
    (first : TypedValue R Γ A) (second : TypedValue R Γ (inst0 first.val B)) :
    TypedValue R Δ (inst0 (subst σ first.val) (subst (liftSub σ) B)) :=
  ⟨subst σ second.val, target, by
    have typing := second.property.typing.substitute typed
    rw [subst_inst0] at typing
    exact typing⟩

end TypedValue

/-- Native pair introduction requires independently admitted Sigma formation. -/
def sigmaPair {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) (first : TypedValue R Γ A)
    (second : TypedValue R Γ (inst0 first.val B)) : TypedValue R Γ (.sigma A B) :=
  ⟨.pair first.val second.val, formed.context,
    .pairIntro formed.typing universeWitness first.property.typing second.property.typing⟩

theorem rename_sigmaPair {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) {ρ : Ren n m}
    (target : ContextFormation R Δ) (compatible : CtxRen Γ Δ ρ)
    (first : TypedValue R Γ A) (second : TypedValue R Γ (inst0 first.val B)) :
    TypedValue.rename target compatible (sigmaPair formed universeWitness first second) =
      sigmaPair ⟨target, formed.typing.renameTyping compatible⟩ universeWitness
        (TypedValue.rename target compatible first)
        (TypedValue.renameFibre target compatible first second) := by
  apply Subtype.ext
  rfl

theorem substitute_sigmaPair {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) {σ : Sub Head n m}
    (target : ContextFormation R Δ) (typed : CtxMor R Γ Δ σ)
    (first : TypedValue R Γ A) (second : TypedValue R Γ (inst0 first.val B)) :
    TypedValue.substitute target typed (sigmaPair formed universeWitness first second) =
      sigmaPair (formed.substitute target typed) universeWitness
        (TypedValue.substitute target typed first)
        (TypedValue.substituteFibre target typed first second) := by
  apply Subtype.ext
  rfl

section Effects

variable {State Intent : Type}

/-- Existing dependent sequencing followed by native pair introduction. -/
def sigmaProgram {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) (indices : Program State (TypedValue R Γ A) Intent)
    (next : (first : TypedValue R Γ A) → Program State (TypedValue R Γ (inst0 first.val B)) Intent) :
    Program State (TypedValue R Γ (.sigma A B)) Intent :=
  Program.map (fun value => sigmaPair formed universeWitness value.1 value.2)
    (bindSigma indices next)

/-- Each selected world supplies its own continuation state and branch. Its
intents precede the continuation's intents, and its index remains in the pair. -/
theorem runWorldsAt_sigmaProgram {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) (indices : Program State (TypedValue R Γ A) Intent)
    (next : (first : TypedValue R Γ A) → Program State (TypedValue R Γ (inst0 first.val B)) Intent)
    (state : State) (branch : BranchTrace) :
    runWorldsAt (sigmaProgram formed universeWitness indices next) state branch =
      (runWorldsAt indices state branch).flatMap fun prior =>
        (runWorldsAt (next prior.answer) prior.state prior.branch).map fun suffix =>
          { branch := suffix.branch,
            answer := sigmaPair formed universeWitness prior.answer suffix.answer,
            state := suffix.state, intents := prior.intents ++ suffix.intents } := by
  rw [sigmaProgram, runWorldsAt_map, runWorldsAt_bindSigma]
  simp only [List.map_flatMap, List.map_map, Function.comp_def,
    WorldResult.mapAnswer, WorldResult.prependIntents]

/-- Forgetting the answer's admission evidence still yields an admitted
native term at every result of the actual contextual execution. -/
theorem result_judgment {u : Head} (formed : Judgment R Γ (.sigma A B) (.head u))
    (universeWitness : R.isUniverse u) (indices : Program State (TypedValue R Γ A) Intent)
    (next : (first : TypedValue R Γ A) → Program State (TypedValue R Γ (inst0 first.val B)) Intent)
    (state : State) (branch : BranchTrace)
    (output : WorldResult State (Tm Head n) Intent)
    (retained : output ∈ runWorldsAt
      (Program.map Subtype.val (sigmaProgram formed universeWitness indices next)) state branch) :
    Judgment R Γ output.answer (.sigma A B) := by
  rw [runWorldsAt_map] at retained
  obtain ⟨typedOutput, _, equality⟩ := List.mem_map.mp retained
  subst output
  exact typedOutput.answer.property

end Effects

/-! ## Certificate-indexed native identity families

A named data type and an actually typed two-argument checker determine the
native family `Sigma receipt : Data, Id Data (checker claim receipt) claim`.
The packing function is constructed in the original scoped syntax, with
actual Pi/Sigma/Id formation and lambda/application typing. Its two beta
steps retain the supplied receipt and equality proof. These constructions
provide no semantic authority for the checker or its computation rules.
-/

namespace ReceiptPacking

variable {Head : Type} {R : Rules Head} {n : Nat}

def dataType (name : DeclName) : Tm Head n := .const name

def checkerType (name : DeclName) : Tm Head n :=
  .pi (dataType name) (.pi (dataType name) (dataType name))

def equalityType (name : DeclName) (checker claim receipt : Tm Head n) : Tm Head n :=
  .id (dataType name) (.app (.app checker claim) receipt) claim

def receiptBody (name : DeclName) (checker claim : Tm Head n) : Tm Head (n + 1) :=
  equalityType name (rename wk checker) (rename wk claim) (.var 0)

def family (name : DeclName) (checker claim : Tm Head n) : Tm Head n :=
  .sigma (dataType name) (receiptBody name checker claim)

def packType (name : DeclName) (checker claim : Tm Head n) : Tm Head n :=
  .pi (dataType name) (.pi (receiptBody name checker claim)
    (rename wk (rename wk (family name checker claim))))

def pack : Tm Head n := .lam (.lam (.pair (.var 1) (.var 0)))

private theorem data_formed (name : DeclName) {u : Head}
    (formed : Typing R .nil (dataType name) (.head u)) (context : Ctx Head n) :
    Typing R context (dataType name) (.head u) := by
  simpa only [dataType, rename] using
    formed.renameTyping (Δ := context) (ρ := Fin.elim0) (fun i => Fin.elim0 i)

theorem equality_formed (name : DeclName) {context : Ctx Head n} {u : Head}
    {checker claim receipt : Tm Head n}
    (formed : Typing R .nil (dataType name) (.head u)) (universeWitness : R.isUniverse u)
    (checkerTyped : Typing R context checker (checkerType name))
    (claimTyped : Typing R context claim (dataType name))
    (receiptTyped : Typing R context receipt (dataType name)) :
    Typing R context (equalityType name checker claim receipt) (.head u) := by
  have first : Typing R context (.app checker claim) (.pi (dataType name) (dataType name)) := by
    simpa only [checkerType, inst0, subst, dataType] using Typing.appElim checkerTyped claimTyped
  have second : Typing R context (.app (.app checker claim) receipt) (dataType name) := by
    simpa only [inst0, subst, dataType] using Typing.appElim first receiptTyped
  exact .idForm (data_formed name formed context) universeWitness second claimTyped

theorem family_formed (name : DeclName) {context : Ctx Head n} {u v : Head}
    {checker claim : Tm Head n}
    (formed : Typing R .nil (dataType name) (.head u))
    (universeWitness : R.isUniverse u) (joined : R.join u u v)
    (checkerTyped : Typing R context checker (checkerType name))
    (claimTyped : Typing R context claim (dataType name)) :
    Typing R context (family name checker claim) (.head v) := by
  apply Typing.sigmaForm (data_formed name formed context) universeWitness
  · apply equality_formed name formed universeWitness
    · simpa only [checkerType, dataType, rename] using checkerTyped.weaken (extension := dataType name)
    · simpa only [dataType, rename] using claimTyped.weaken (extension := dataType name)
    · exact .var 0
  · exact universeWitness
  · exact joined

theorem body_inst0 (name : DeclName) (checker claim receipt : Tm Head n) :
    inst0 receipt (receiptBody name checker claim) = equalityType name checker claim receipt := by
  simp only [receiptBody, equalityType, dataType, inst0, subst]
  change Tm.id (.const name)
    (.app (.app (inst0 receipt (rename wk checker)) (inst0 receipt (rename wk claim))) receipt)
    (inst0 receipt (rename wk claim)) = _
  simp only [inst0_rename_wk]

theorem family_rename {m : Nat} (rho : Ren n m) (name : DeclName) (checker claim : Tm Head n) :
    rename rho (family name checker claim) = family name (rename rho checker) (rename rho claim) := by
  simp only [family, receiptBody, equalityType, dataType, rename]
  have shift (term : Tm Head n) :
      rename (liftRen rho) (rename wk term) = rename wk (rename rho term) := by
    rw [rename_comp, rename_comp]
    rfl
  rw [shift checker, shift claim]
  rfl

theorem receiptBody_formed (name : DeclName) {context : Ctx Head n} {u : Head}
    {checker claim : Tm Head n}
    (formed : Typing R .nil (dataType name) (.head u))
    (universeWitness : R.isUniverse u)
    (checkerTyped : Typing R context checker (checkerType name))
    (claimTyped : Typing R context claim (dataType name)) :
    Typing R (.snoc context (dataType name)) (receiptBody name checker claim) (.head u) := by
  apply equality_formed name formed universeWitness
  · simpa only [checkerType, dataType, rename] using checkerTyped.weaken (extension := dataType name)
  · simpa only [dataType, rename] using claimTyped.weaken (extension := dataType name)
  · exact .var 0

theorem packType_formed (name : DeclName) {context : Ctx Head n} {u v w z : Head}
    {checker claim : Tm Head n}
    (formed : Typing R .nil (dataType name) (.head u))
    (uUniverse : R.isUniverse u) (vUniverse : R.isUniverse v) (wUniverse : R.isUniverse w)
    (familyJoin : R.join u u v) (innerJoin : R.join u v w) (outerJoin : R.join u w z)
    (checkerTyped : Typing R context checker (checkerType name))
    (claimTyped : Typing R context claim (dataType name)) :
    Typing R context (packType name checker claim) (.head z) := by
  have receiptFormed := receiptBody_formed name formed uUniverse checkerTyped claimTyped
  have familyFormed := family_formed name formed uUniverse familyJoin checkerTyped claimTyped
  have lifted := (familyFormed.weaken (extension := dataType name)).weaken
    (extension := receiptBody name checker claim)
  apply Typing.piForm (data_formed name formed context) uUniverse
  · exact .piForm receiptFormed uUniverse (by simpa only [rename] using lifted) vUniverse innerJoin
  · exact wUniverse
  · exact outerJoin

theorem pack_typed (name : DeclName) {context : Ctx Head n} {u v w z : Head}
    {checker claim : Tm Head n}
    (formed : Typing R .nil (dataType name) (.head u))
    (uUniverse : R.isUniverse u) (vUniverse : R.isUniverse v)
    (wUniverse : R.isUniverse w) (zUniverse : R.isUniverse z)
    (familyJoin : R.join u u v) (innerJoin : R.join u v w) (outerJoin : R.join u w z)
    (checkerTyped : Typing R context checker (checkerType name))
    (claimTyped : Typing R context claim (dataType name)) :
    Typing R context pack (packType name checker claim) := by
  have receiptFormed := receiptBody_formed name formed uUniverse checkerTyped claimTyped
  have familyFormed := family_formed name formed uUniverse familyJoin checkerTyped claimTyped
  have lifted := (familyFormed.weaken (extension := dataType name)).weaken
    (extension := receiptBody name checker claim)
  have liftedFormed : Typing R
      (.snoc (.snoc context (dataType name)) (receiptBody name checker claim))
      (rename wk (rename wk (family name checker claim))) (.head v) := by
    simpa only [rename] using lifted
  have innerFormed : Typing R (.snoc context (dataType name))
      (.pi (receiptBody name checker claim) (rename wk (rename wk (family name checker claim))))
      (.head w) :=
    .piForm receiptFormed uUniverse liftedFormed vUniverse innerJoin
  apply Typing.lamIntro
    (packType_formed name formed uUniverse vUniverse wUniverse familyJoin innerJoin outerJoin
      checkerTyped claimTyped) zUniverse
  apply Typing.lamIntro innerFormed wUniverse
  rw [family_rename, family_rename]
  rw [family_rename, family_rename] at liftedFormed
  apply Typing.pairIntro liftedFormed vUniverse (Typing.var 1)
  rw [body_inst0]
  simpa [Ctx.lookup, receiptBody, equalityType, dataType, rename, wk] using
    (Typing.var (R := R)
      (Γ := .snoc (.snoc context (dataType name)) (receiptBody name checker claim)) 0)

theorem supplied_pair_typed (name : DeclName) {context : Ctx Head n} {u v : Head}
    {checker claim receipt equality : Tm Head n}
    (formed : Typing R .nil (dataType name) (.head u))
    (uUniverse : R.isUniverse u) (vUniverse : R.isUniverse v) (familyJoin : R.join u u v)
    (checkerTyped : Typing R context checker (checkerType name))
    (claimTyped : Typing R context claim (dataType name))
    (receiptTyped : Typing R context receipt (dataType name))
    (equalityTyped : Typing R context equality (equalityType name checker claim receipt)) :
    Typing R context (.pair receipt equality) (family name checker claim) := by
  apply Typing.pairIntro (family_formed name formed uUniverse familyJoin checkerTyped claimTyped)
    vUniverse receiptTyped
  rw [body_inst0]
  exact equalityTyped

theorem pack_two_steps (receipt equality : Tm Head n) :
    ∃ middle, Step R.headEq (.app (.app pack receipt) equality) middle R.computation ∧
      Step R.headEq middle (.pair receipt equality) R.computation := by
  refine ⟨.app (.lam (.pair (rename wk receipt) (.var 0))) equality, ?_, ?_⟩
  · apply Step.congAppFun
    have beta := Step.betaPi (root := R.computation) (headEq := R.headEq)
      (.lam (.pair (.var (Fin.succ 0)) (.var 0))) receipt
    have opened : inst0 receipt (.lam (.pair (.var (Fin.succ 0)) (.var 0))) =
        .lam (.pair (rename wk receipt) (.var 0)) := rfl
    rw [opened] at beta
    simpa only [pack, Fin.succ_zero_eq_one] using beta
  · have beta := Step.betaPi (root := R.computation) (headEq := R.headEq)
      (.pair (rename wk receipt) (.var 0)) equality
    change StepCore R.computation R.headEq _ (.pair (inst0 equality (rename wk receipt)) equality) at beta
    rw [inst0_rename_wk] at beta
    exact beta

theorem family_substitute {m : Nat} (sigma : Sub Head n m) (name : DeclName)
    (checker claim : Tm Head n) :
    subst sigma (family name checker claim) = family name (subst sigma checker) (subst sigma claim) := by
  simp only [family, receiptBody, equalityType, dataType, subst]
  have shift (term : Tm Head n) :
      subst (liftSub sigma) (rename wk term) = rename wk (subst sigma term) := by
    rw [subst_rename, rename_subst]
    rfl
  rw [shift checker, shift claim]
  rfl

theorem pack_codomain_open (name : DeclName) (checker claim receipt : Tm Head n) :
    inst0 receipt (.pi (receiptBody name checker claim)
      (rename wk (rename wk (family name checker claim)))) =
        .pi (equalityType name checker claim receipt) (rename wk (family name checker claim)) := by
  change Tm.pi (inst0 receipt (receiptBody name checker claim))
    (subst (liftSub (subst0 receipt)) (rename wk (rename wk (family name checker claim)))) = _
  rw [body_inst0]
  congr 1
  rw [subst_rename, subst_rename]
  change subst (renSub wk) (family name checker claim) = _
  exact subst_renSub wk _

theorem pack_application_typed (name : DeclName) {context : Ctx Head n} {u v w z : Head}
    {checker claim receipt equality : Tm Head n}
    (formed : Typing R .nil (dataType name) (.head u))
    (uUniverse : R.isUniverse u) (vUniverse : R.isUniverse v)
    (wUniverse : R.isUniverse w) (zUniverse : R.isUniverse z)
    (familyJoin : R.join u u v) (innerJoin : R.join u v w) (outerJoin : R.join u w z)
    (checkerTyped : Typing R context checker (checkerType name))
    (claimTyped : Typing R context claim (dataType name))
    (receiptTyped : Typing R context receipt (dataType name))
    (equalityTyped : Typing R context equality (equalityType name checker claim receipt)) :
    Typing R context (.app (.app pack receipt) equality) (family name checker claim) := by
  have function := pack_typed name formed uUniverse vUniverse wUniverse zUniverse
    familyJoin innerJoin outerJoin checkerTyped claimTyped
  have first := Typing.appElim function receiptTyped
  change Typing R context (.app pack receipt)
    (inst0 receipt (.pi (receiptBody name checker claim)
      (rename wk (rename wk (family name checker claim))))) at first
  rw [pack_codomain_open] at first
  simpa only [inst0_rename_wk] using Typing.appElim first equalityTyped

#print axioms pack_application_typed
#print axioms family_substitute
#print axioms pack_typed
#print axioms supplied_pair_typed
#print axioms pack_two_steps

#print axioms family_formed
#print axioms family_rename

end ReceiptPacking


#print axioms rename_sigmaPair
#print axioms substitute_sigmaPair
#print axioms runWorldsAt_sigmaProgram
#print axioms result_judgment

end FormationSensitive.DependentComputation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
