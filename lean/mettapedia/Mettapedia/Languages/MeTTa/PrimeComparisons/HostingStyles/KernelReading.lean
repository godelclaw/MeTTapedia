import Mettapedia.Languages.MeTTa.PrimeCandidates.Language
import Mettapedia.Logic.HostingStyles.ReductionRank
import Mettapedia.Logic.HostingStyles.TermsAloneHosting

/-!
# The kernel reading of the candidate

`PrimeCandidates.Language.kernelGSLT model` assembles a selected base host, a
revision-keyed Need layer and structural quotation into one theory given by
its terms.  Read through its contexts it has the hole alone
(`GSLT.termsAlone`).  This module says what that theory hosts.

* **What the nucleus adds is bounded.**  For the query-first models, where
  the base is the query-first Zero kernel, the assembled kernel has a rank at
  most three (`queryFirstKernelRank`, `queryFirstKernelRank_le`): no
  reduction has four steps, and no cyclic reduction has an image in it.
  Three steps are attained by every evaluation request
  (`queryFirstKernel_steps_three`).
* **The nucleus adds no cyclic reduction.**  For every model, a rank on the
  base that its static equivalence keeps gives a rank on the kernel
  (`kernelRankOfBaseRank`), and a cyclic reduction of the base is one of the
  kernel (`kernel_cycle_of_base`).
* **What the kernel hosts, it hosts through its base.**  A step out of a
  term of the base is a step of the base or the demand of an evaluation
  request (`kernel_step_of_base`).  So a theory that the base hosts by terms
  that are never requests is hosted by the kernel
  (`kernel_hosting_of_base`).  Placing a guest theory beside the base
  (`withGuest`) makes the kernel host the guest (`guestMap_hosting`); the map
  is exhausting onto the region of its image and not onto the kernel
  (`guestMap_not_exhausting`).
* **Where data that does not reduce lives.**  A value and a quoted name of
  the reflection layer have no step, for every model (`kernelValues`,
  `kernelNames`): they are inert data indexed by all patterns.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles


open Mettapedia.GSLT
open Mettapedia.GSLT.Dynamics.OccurrenceSemantics
open Mettapedia.GSLT.Dynamics.ProofRelevantNeed
open Mettapedia.GSLT.Dynamics.OperationalRegion
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.Language
open Mettapedia.Languages.MeTTa.PrimeCandidates.UniversalName
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Steps out of the base -/

/-- **A step of the kernel out of a term of its base is a step of the base,
or the demand of an evaluation request.** -/
theorem kernel_step_of_base (model : Model) {term : model.base.host.Term}
    {next : (kernelGSLT model).Term} (step : (kernelGSLT model).Step (.inl term) next) :
    (∃ baseNext, next = .inl baseNext ∧ model.base.host.Step term baseNext) ∨
      ∃ space subject, model.base.host.Equiv term
        (model.base.occurrenceEmbedding.toFun (.request space subject)) := by
  cases step with
  | left baseStep => exact .inl ⟨_, rfl, baseStep⟩
  | leftToRight crossing =>
      obtain ⟨space, subject, isRequest, _⟩ := crossing
      exact .inr ⟨space, subject, isRequest⟩

/-- **The kernel hosts what its base hosts away from the requests**: a
hosting map on terms into the base whose images are never evaluation requests
is, followed by the inclusion of the base, a hosting map into the kernel. -/
theorem kernel_hosting_of_base (model : Model) {source : GSLT.{0}}
    (term : source.Term → model.base.host.Term)
    (term_resp : ∀ {first second : source.Term}, source.equations.r first second →
      model.base.host.equations.r (term first) (term second))
    (hosting : (ContextMap.ofTerms (source := source) (target := model.base.host.termsAlone)
      PUnit.unit term term_resp).Hosting)
    (apart : ∀ origin space subject, ¬ model.base.host.Equiv (term origin)
      (model.base.occurrenceEmbedding.toFun (.request space subject))) :
    (ContextMap.ofTerms (source := source) (target := (kernelGSLT model).termsAlone) PUnit.unit
      (fun origin => (Sum.inl (term origin) : (kernelGSLT model).Term))
      (fun related => GSLT.SumEquiv.left (term_resp related))).Hosting := by
  obtain ⟨reflectsEquations, preserves, reflects⟩ :=
    (ContextMap.ofTerms_hosting_iff (source := source) (target := model.base.host.termsAlone)
      PUnit.unit term term_resp).mp hosting
  refine (ContextMap.ofTerms_hosting_iff (source := source)
    (target := (kernelGSLT model).termsAlone) PUnit.unit
    (fun origin => (Sum.inl (term origin) : (kernelGSLT model).Term))
    (fun related => GSLT.SumEquiv.left (term_resp related))).mpr ⟨?_, ?_, ?_⟩
  · intro first second related
    cases related with
    | left baseRelated => exact reflectsEquations first second baseRelated
  · intro first next step
    exact GSLT.InteractingStep.left (preserves first next step)
  · intro first next step
    rcases kernel_step_of_base model step with ⟨baseNext, rfl, baseStep⟩ | ⟨space, subject, isRequest⟩
    · obtain ⟨sourceNext, sourceStep, related⟩ := reflects first baseNext baseStep
      exact ⟨sourceNext, sourceStep, GSLT.SumEquiv.left related⟩
    · exact (apart first space subject isRequest).elim

/-! ## A guest beside the base -/

/-- **A candidate assembly with a guest theory beside its base host.**  The
occurrence source, its embedding and the revision authority are those of the
model.  The bag observation gives a term of the guest the empty bag: the
observation of the assembly does not see the guest. -/
def withGuest (model : Model) (guest : GSLT.{0}) : Model where
  base :=
    { Space := model.base.Space
      source := model.base.source
      host := GSLT.disjointSum guest model.base.host
      occurrenceEmbedding :=
        (GSLT.disjointSumRight guest model.base.host).comp model.base.occurrenceEmbedding }
  observation :=
    { meaning := Sum.elim (fun _ => 0) model.observation.meaning
      elaboration :=
        { elaborate := Sum.elim (fun _ => some 0) model.observation.elaboration.elaborate
          equation := fun equivalent => by
            cases equivalent with
            | left _ => rfl
            | right component => exact model.observation.elaboration.equation component
          rewrite := fun step => by
            cases step with
            | left _ => rfl
            | right component => exact model.observation.elaboration.rewrite component }
      elaborates := fun term => by
        cases term with
        | inl _ => rfl
        | inr term => exact model.observation.elaborates term
      occurrenceMeaning := fun term => model.observation.occurrenceMeaning term }
  revisionAuthority := model.revisionAuthority

/-- The guest, in the kernel of the assembly that carries it. -/
def guestMap (model : Model) (guest : GSLT.{0}) :
    ContextMap guest.termsAlone (kernelGSLT (withGuest model guest)).termsAlone :=
  ContextMap.ofTerms (source := guest) (target := (kernelGSLT (withGuest model guest)).termsAlone)
    PUnit.unit (fun term => (Sum.inl (Sum.inl term) : (kernelGSLT (withGuest model guest)).Term))
    (fun related => GSLT.SumEquiv.left (GSLT.SumEquiv.left related))

/-- **The kernel of an assembly hosts the guest placed beside its base.** -/
theorem guestMap_hosting (model : Model) (guest : GSLT.{0}) : (guestMap model guest).Hosting := by
  refine kernel_hosting_of_base (withGuest model guest) (source := guest)
    (fun term => (Sum.inl term : (GSLT.disjointSum guest model.base.host).Term))
    (fun related => GSLT.SumEquiv.left related) ?_ ?_
  · refine (ContextMap.ofTerms_hosting_iff (source := guest)
      (target := (GSLT.disjointSum guest model.base.host).termsAlone) PUnit.unit
      (fun term => (Sum.inl term : (GSLT.disjointSum guest model.base.host).Term))
      (fun related => GSLT.SumEquiv.left related)).mpr ⟨?_, ?_, ?_⟩
    · intro first second related
      cases related with
      | left guestRelated => exact guestRelated
    · intro first next step
      exact GSLT.SumStep.left step
    · intro first next step
      cases step with
      | left guestStep => exact ⟨_, guestStep, GSLT.SumEquiv.left (guest.equations.iseqv.refl _)⟩
  · intro origin space subject isRequest
    cases isRequest

/-- **Negative**: the guest does not exhaust the kernel that hosts it; a
value of the reflection layer is outside every image. -/
theorem guestMap_not_exhausting (model : Model) (guest : GSLT.{0}) :
    ¬ (guestMap model guest).Exhausting := by
  intro exhausting
  obtain ⟨origin, related⟩ :=
    (ContextMap.ofTerms_exhausting_iff (source := guest)
      (target := kernelGSLT (withGuest model guest))
      (fun term => (Sum.inl (Sum.inl term) : (kernelGSLT (withGuest model guest)).Term))
      (fun related => GSLT.SumEquiv.left (GSLT.SumEquiv.left related))).mp exhausting
      (Sum.inr (Sum.inl (ReflectionTerm.value (.apply "prime-unit" []))))
  cases related

/-! ## The query-first kernel has a rank -/

/-- The rank of a term of the reflection layer. -/
def reflectionRank {model : Model} : ReflectionTerm model → Nat
  | .evaluate _ _ => 3
  | .drop _ => 1
  | .quoted _ => 0
  | .value _ => 0

/-- The rank of a term of the Need layer. -/
def needRank {model : Model} : NeedTerm model → Nat
  | .request _ _ => 2
  | .answer _ _ _ _ _ => 1

/-- The rank of a term of the query-first Zero kernel. -/
def zeroRank {zero : MeTTaZero.Model} : (MeTTaZero.kernelGSLT zero).Term → Nat
  | .inl (.request _ _ _) => 1
  | .inl (.answer _ _ _ _ _) => 0
  | .inr (.request _ _) => 3
  | .inr (.answer _ _ _ _) => 0

/-- The rank of a term of the kernel assembled over a query-first model. -/
def queryFirstRank (model : QueryFirstModel) :
    (kernelGSLT model.toAssemblyModel).Term → Nat :=
  Sum.elim zeroRank (Sum.elim reflectionRank needRank)

/-- **Every step of the kernel over a query-first model lowers the rank.** -/
theorem queryFirst_step_lowers (model : QueryFirstModel)
    {source target : (kernelGSLT model.toAssemblyModel).Term}
    (step : (kernelGSLT model.toAssemblyModel).Step source target) :
    queryFirstRank model target < queryFirstRank model source := by
  cases step with
  | left baseStep =>
      cases baseStep with
      | left queryStep => cases queryStep; exact (by decide : (0 : Nat) < 1)
      | right evaluationStep => cases evaluationStep; exact (by decide : (0 : Nat) < 3)
  | right runtimeStep =>
      cases runtimeStep with
      | left reflectionStep => cases reflectionStep; exact (by decide : (0 : Nat) < 1)
      | right needStep => cases needStep; exact (by decide : (1 : Nat) < 2)
      | leftToRight crossing => cases crossing; exact (by decide : (2 : Nat) < 3)
      | rightToLeft crossing => exact crossing.elim
  | leftToRight crossing =>
      obtain ⟨space, subject, isRequest, isNeed⟩ := crossing
      cases isRequest with
      | right evaluationSame =>
          cases evaluationSame
          cases isNeed with
          | right needSame =>
              cases needSame
              exact (by decide : (2 : Nat) < 3)
  | rightToLeft crossing =>
      obtain ⟨space, subject, occurrence, result, isAnswer, isReturn⟩ := crossing
      cases isAnswer with
      | right needSame =>
          cases needSame
          cases isReturn with
          | right evaluationSame =>
              cases evaluationSame
              exact (by decide : (0 : Nat) < 1)

/-- **The kernel over a query-first model has a rank.** -/
def queryFirstKernelRank (model : QueryFirstModel) :
    (kernelGSLT model.toAssemblyModel).termsAlone.Rank where
  rank := fun term => queryFirstRank model term
  lowers := fun step => queryFirst_step_lowers model step

/-- **Its rank is at most three.** -/
theorem queryFirstKernelRank_le (model : QueryFirstModel)
    (term : (kernelGSLT model.toAssemblyModel).Term) : queryFirstRank model term ≤ 3 := by
  rcases term with (query | evaluation) | reflection | need
  · cases query
    · exact (by decide : (1 : Nat) ≤ 3)
    · exact (by decide : (0 : Nat) ≤ 3)
  · cases evaluation
    · exact (by decide : (3 : Nat) ≤ 3)
    · exact (by decide : (0 : Nat) ≤ 3)
  · cases reflection
    · exact (by decide : (0 : Nat) ≤ 3)
    · exact (by decide : (1 : Nat) ≤ 3)
    · exact (by decide : (0 : Nat) ≤ 3)
    · exact (by decide : (3 : Nat) ≤ 3)
  · cases need
    · exact (by decide : (2 : Nat) ≤ 3)
    · exact (by decide : (1 : Nat) ≤ 3)

/-- **No reduction of the kernel over a query-first model has four steps.** -/
theorem queryFirstKernel_not_steps_four (model : QueryFirstModel)
    {term final : (kernelGSLT model.toAssemblyModel).Term} :
    ¬ (kernelGSLT model.toAssemblyModel).termsAlone.Steps (interface := PUnit.unit) 4 term final := by
  intro steps
  have counted := (queryFirstKernelRank model).steps_le steps
  have top := queryFirstKernelRank_le model term
  have unfolded : (queryFirstKernelRank model).rank (interface := PUnit.unit) term =
      queryFirstRank model term := rfl
  omega

/-- **Positive**: every evaluation request of the kernel over a query-first
model has a reduction of three steps, through the Need layer: the bound is
attained as soon as the model has a space. -/
theorem queryFirstKernel_steps_three (model : QueryFirstModel) (space : model.Space)
    (subject : Pattern) :
    ∃ final : (kernelGSLT model.toAssemblyModel).Term,
      (kernelGSLT model.toAssemblyModel).termsAlone.Steps (interface := PUnit.unit) 3
        ((evaluationKernelEmbedding model.toAssemblyModel).toFun (.request space subject))
        final := by
  have nonempty : MeTTaZero.evaluateOne model.zero space subject ≠ 0 := by
    by_cases unknown : MeTTaZero.interpretedResults model.zero space subject = 0
    · rw [MeTTaZero.evaluateOne_of_uninterpreted _ _ _ unknown]
      exact Multiset.singleton_ne_zero _
    · rw [MeTTaZero.evaluateOne_of_interpreted _ _ _ unknown]
      exact unknown
  obtain ⟨result, member⟩ := Multiset.exists_mem_of_ne_zero nonempty
  have copy : 0 < Multiset.count result
      (model.toAssemblyModel.base.source.occurrences space subject) :=
    Multiset.count_pos.mpr member
  exact ⟨_, .succ (evaluation_enters_need model.toAssemblyModel space subject)
    (.succ (((needEmbedding model.toAssemblyModel).step_iff _ _).2
        (RevisionedOccurrenceStep.found copy))
      (.succ (need_returns_evaluation model.toAssemblyModel space subject 0 result) (.zero _)))⟩

/-! ## The nucleus adds no cyclic reduction -/

/-- The rank of a term of the kernel, from a rank on the terms of its base:
a term of the base keeps three times its rank, and the Need request, the Need
answer and the evaluation of a name are placed around the base request and
the base answer that they stand between. -/
def kernelRankOfBase (model : Model) (baseRank : model.base.host.Term → Nat) :
    (kernelGSLT model).Term → Nat
  | .inl term => 3 * baseRank term + 2
  | .inr (.inl (.evaluate space name)) =>
      3 * baseRank (model.base.occurrenceEmbedding.toFun (.request space (Name.unquote name))) + 2
  | .inr (.inl (.drop _)) => 1
  | .inr (.inl (.quoted _)) => 0
  | .inr (.inl (.value _)) => 0
  | .inr (.inr (.request space subject)) =>
      3 * baseRank (model.base.occurrenceEmbedding.toFun (.request space subject)) + 1
  | .inr (.inr (.answer space subject _ occurrence result)) =>
      3 * baseRank
        (model.base.occurrenceEmbedding.toFun (.answer space subject occurrence result)) + 3

/-- **Every step of the kernel lowers the rank built from a rank of its
base**, when the steps of the base lower that rank and its static equivalence
keeps it. -/
theorem kernel_step_lowers_of_base (model : Model) (baseRank : model.base.host.Term → Nat)
    (lowers : ∀ {term next : model.base.host.Term}, model.base.host.Step term next →
      baseRank next < baseRank term)
    (respects : ∀ {first second : model.base.host.Term}, model.base.host.Equiv first second →
      baseRank first = baseRank second)
    {source target : (kernelGSLT model).Term} (step : (kernelGSLT model).Step source target) :
    kernelRankOfBase model baseRank target < kernelRankOfBase model baseRank source := by
  cases step with
  | left baseStep =>
      have lowered := lowers baseStep
      simp only [kernelRankOfBase]
      omega
  | right runtimeStep =>
      cases runtimeStep with
      | left reflectionStep =>
          cases reflectionStep
          exact Nat.zero_lt_one
      | right needStep =>
          cases needStep with
          | found copy =>
              have lowered := lowers
                ((model.base.occurrenceEmbedding.step_iff _ _).mpr (OccurrenceStep.found copy))
              simp only [kernelRankOfBase]
              omega
      | leftToRight crossing =>
          cases crossing
          simp only [kernelRankOfBase, Name.unquote_quote]
          omega
      | rightToLeft crossing => exact crossing.elim
  | leftToRight crossing =>
      obtain ⟨space, subject, isRequest, isNeed⟩ := crossing
      cases isNeed with
      | right needSame =>
          cases needSame
          have same := respects isRequest
          simp only [kernelRankOfBase]
          omega
  | rightToLeft crossing =>
      obtain ⟨space, subject, occurrence, result, isAnswer, isReturn⟩ := crossing
      cases isAnswer with
      | right needSame =>
          cases needSame
          have same := respects isReturn
          simp only [kernelRankOfBase]
          omega

/-- **The kernel has a rank whenever its base has one that its static
equivalence keeps**: the Need layer and the reflection layer add no cyclic
reduction. -/
def kernelRankOfBaseRank (model : Model) (baseRank : model.base.host.Term → Nat)
    (lowers : ∀ {term next : model.base.host.Term}, model.base.host.Step term next →
      baseRank next < baseRank term)
    (respects : ∀ {first second : model.base.host.Term}, model.base.host.Equiv first second →
      baseRank first = baseRank second) : (kernelGSLT model).termsAlone.Rank where
  rank := fun term => kernelRankOfBase model baseRank term
  lowers := fun step => kernel_step_lowers_of_base model baseRank lowers respects step

/-- Conversely a cyclic reduction of the base is one of the kernel. -/
theorem kernel_cycle_of_base (model : Model) {term : model.base.host.Term}
    (cycle : Relation.TransGen model.base.host.rewrites term term) :
    Relation.TransGen (kernelGSLT model).rewrites (.inl term) (.inl term) := by
  have lifted : ∀ {final : model.base.host.Term}, Relation.TransGen model.base.host.rewrites term final →
      Relation.TransGen (kernelGSLT model).rewrites (.inl term) (.inl final) := by
    intro final steps
    induction steps with
    | single step => exact .single (GSLT.InteractingStep.left step)
    | tail _ step ih => exact ih.tail (GSLT.InteractingStep.left step)
  exact lifted cycle

/-! ## Where data that does not reduce lives -/

/-- A value of the reflection layer, in the kernel. -/
def kernelValue (model : Model) (pattern : Pattern) : (kernelGSLT model).Term :=
  .inr (.inl (.value pattern))

/-- A quoted name of the reflection layer, in the kernel. -/
def kernelName (model : Model) (pattern : Pattern) : (kernelGSLT model).Term :=
  .inr (.inl (.quoted (Name.quote pattern)))

/-- **The values of the reflection layer are inert data**, one for each
pattern, in the kernel of every model. -/
def kernelValues (model : Model) : (kernelGSLT model).termsAlone.InertData Pattern where
  interface := PUnit.unit
  datum := kernelValue model
  normal := fun pattern next step => by
    cases step with
    | right runtimeStep =>
        cases runtimeStep with
        | left reflectionStep => cases reflectionStep
        | leftToRight crossing => cases crossing
    | rightToLeft crossing =>
        obtain ⟨_, _, _, _, isAnswer, _⟩ := crossing
        cases isAnswer
  apart := fun first second related => by
    cases related with
    | right runtimeRelated =>
        cases runtimeRelated with
        | left reflectionRelated =>
            have same : ReflectionTerm.value first = ReflectionTerm.value second := reflectionRelated
            exact ReflectionTerm.value.inj same

/-- **The quoted names of the reflection layer are inert data** too: quoting
does not evaluate. -/
def kernelNames (model : Model) : (kernelGSLT model).termsAlone.InertData Pattern where
  interface := PUnit.unit
  datum := kernelName model
  normal := fun pattern next step => by
    cases step with
    | right runtimeStep =>
        cases runtimeStep with
        | left reflectionStep => cases reflectionStep
        | leftToRight crossing => cases crossing
    | rightToLeft crossing =>
        obtain ⟨_, _, _, _, isAnswer, _⟩ := crossing
        cases isAnswer
  apart := fun first second related => by
    cases related with
    | right runtimeRelated =>
        cases runtimeRelated with
        | left reflectionRelated =>
            have same : ReflectionTerm.quoted (model := model) (Name.quote first) =
                ReflectionTerm.quoted (Name.quote second) := reflectionRelated
            exact congrArg Name.unquote (ReflectionTerm.quoted.inj same)

/-- **Negative**: a dropping of a name is not inert; it reduces to the value
of what the name quotes. -/
theorem kernelDrop_step (model : Model) (pattern : Pattern) :
    (kernelGSLT model).Step (.inr (.inl (.drop (Name.quote pattern)))) (kernelValue model pattern) :=
  GSLT.InteractingStep.right (GSLT.InteractingStep.left (ReflectionStep.dropQuote pattern))

#print axioms kernel_step_of_base
#print axioms kernel_hosting_of_base
#print axioms withGuest
#print axioms guestMap_hosting
#print axioms guestMap_not_exhausting
#print axioms queryFirst_step_lowers
#print axioms queryFirstKernelRank
#print axioms queryFirstKernelRank_le
#print axioms queryFirstKernel_not_steps_four
#print axioms queryFirstKernel_steps_three
#print axioms kernel_step_lowers_of_base
#print axioms kernelRankOfBaseRank
#print axioms kernel_cycle_of_base
#print axioms kernelValues
#print axioms kernelNames

end Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
