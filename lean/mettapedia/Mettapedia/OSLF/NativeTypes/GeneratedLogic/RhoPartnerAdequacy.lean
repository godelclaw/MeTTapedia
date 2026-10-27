import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ForwardEquivalence
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ContextLabels
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.RhoCanonicalForms
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CanonicalPartnerCoalgebra
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical

/-!
# ρ's parallel partners at the front door

A ρ process meets its environment only in parallel composition, so the contexts that can enable its steps are the
parallel partners: the context `{x, Q}` with a closed process `Q` beside the hole (`partnerLabel`). The front door reads
ρ in its own reading (`Rho.reading`), and there:

- **A plain step between closed processes is a step of ρ's calculus modulo its equations** (`step_any_iff`), the
  established `rhoLanguageDefGSLT.Step`.
- **A step in a partner's context is a partner-labelled step** (`step_partner_iff`): the process beside the partner
  steps, the transition `ParallelContextAdequacy.partnerSystem` labels by the partner.
- **Partner steps are finitely many up to the equations** (`finiteUpTo`), by the complete canonical successor sets of
  `CanonicalPartnerCoalgebra`, and they keep the closed processes (`closedUnder`).
- So **two closed processes have the same native types under parallel partners exactly when they are forward
  bisimilar under partners** (`agree_iff_forwardBisimilar`), by the forward Hennessy–Milner theorem, though ρ has
  infinitely many predecessors up to its equations (`BackwardNotImageFinite`).
- **That bisimilarity is ρ's partner bisimilarity** (`forwardBisimilar_iff_partnerBisimilar`). The front door's
  context-labelled native types of ρ therefore characterize it (`agree_iff_partnerBisimilar`), the same equivalence
  `ParallelContextAdequacy.partnerFormulaNativeTypes_equivalent_iff_bisimilar` characterizes by partner formulas.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho.Partners

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT (RhoProcess rhoLanguageDefGSLT)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelContextAdequacy (par partnerSystem)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LexCanonical (RhoShaped RhoShapedList proc_rhoShaped)
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.DerivedContextualStep (RhoStep)

/-- **The front door of ρ**, in its own reading. -/
abbrev frontDoor : NativeStructure Pattern := referenceStructure RelationEnv.empty rhoCalc reading

/-! ## Closed processes -/

theorem process_closed (term : RhoProcess) : process term.1 = true :=
  (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit_exact term.1).mpr term.2

/-- An admitted process as a closed ρ process. -/
def ofProcess {term : Pattern} (admitted : process term = true) : RhoProcess :=
  ⟨term, (Mettapedia.OSLF.NativeTypes.Instances.Rho.Canonical.admit_exact term).mp admitted⟩

theorem isState_of_process {term : Pattern} (admitted : process term = true) : IsState term :=
  ⟨closed_of_process admitted, (canonical RelationEnv.empty).object (domain_of_process admitted)⟩

theorem objectEquivalent_iff_processes {first second : Pattern} (firstAdmitted : process first = true)
    (secondAdmitted : process second = true) :
    ObjectEquivalent RelationEnv.empty rhoCalc reading first second ↔
      Canonical.canonicalize first = Canonical.canonicalize second :=
  objectEquivalent_iff (domain_of_process firstAdmitted) (domain_of_process secondAdmitted)

/-! ## Plain steps are ρ's steps modulo its equations -/

/-- **A plain step between closed processes is a step of ρ modulo its equations.** -/
theorem step_any_iff (source target : RhoProcess) :
    frontDoor.step source.1 .any target.1 ↔ rhoLanguageDefGSLT.Step source target := by
  constructor
  · rintro ⟨-, -, redex, contractum, witness, before, -, valid, -, after, -⟩
    have redexProcess := process_invariant (process_closed source) before
    have contractumProcess := process_of_step redexProcess valid.2
    exact ⟨ofProcess redexProcess, ofProcess contractumProcess, canonicalize_eq_of_objectEquivalent before, valid.2,
      canonicalize_eq_of_objectEquivalent after⟩
  · rintro ⟨redex, contractum, before, reduces, after⟩
    exact ⟨isState_of_process (process_closed source), isState_of_process (process_closed target), redex.1,
      contractum.1, .base [],
      (objectEquivalent_iff_processes (process_closed source) (process_closed redex)).mpr before,
      isState_of_process (process_closed redex), ⟨rfl, reduces⟩, isState_of_process (process_closed contractum),
      (objectEquivalent_iff_processes (process_closed contractum) (process_closed target)).mpr after, rfl⟩

/-! ## Partners -/

/-- The name of the hole of a parallel context. -/
abbrev hole : String := "x"

mutual
theorem avoidsHole_of_rhoShaped {name : String} : ∀ {pattern : Pattern}, RhoShaped pattern → avoidsHole name pattern = true
  | _, .bvar _ => rfl
  | _, .apply _ arguments => by
    simp only [avoidsHole]
    exact avoidsHoleList_of_rhoShaped arguments
  | _, .lambda body => by
    simp only [avoidsHole]
    exact avoidsHole_of_rhoShaped body
  | _, .bag elements => by
    simp only [avoidsHole, Bool.and_eq_true]
    exact ⟨avoidsHoleList_of_rhoShaped elements, rfl⟩

theorem avoidsHoleList_of_rhoShaped {name : String} :
    ∀ {patterns : List Pattern}, RhoShapedList patterns → avoidsHoleList name patterns = true
  | _, .nil => rfl
  | _, .cons head tail => by
    simp only [avoidsHoleList, Bool.and_eq_true]
    exact ⟨avoidsHole_of_rhoShaped head, avoidsHoleList_of_rhoShaped tail⟩
end

/-- A closed process mentions no hole. -/
theorem avoidsHole_process (term : RhoProcess) : avoidsHole hole term.1 = true :=
  avoidsHole_of_rhoShaped (proc_rhoShaped (Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho.procWellSorted_of_process
    (process_closed term)).1)

/-- The one-hole shape of a partner's context: the hole beside the partner, in a parallel bag. -/
def partnerShape (partner : RhoProcess) : OneHoleContext := .collection .hashBag [] .hole [partner.1] none

/-- **A partner's context**: the hole beside the partner. -/
def partnerContext (partner : RhoProcess) : Pattern := (partnerShape partner).fill (.fvar hole)

/-- **The label of a partner**: a step of the process beside the partner. -/
abbrev partnerLabel (partner : RhoProcess) : StepLabel := .context hole (partnerContext partner) .any

theorem partnerContext_eq (partner : RhoProcess) :
    partnerContext partner = .collection .hashBag [.fvar hole, partner.1] none :=
  rfl

theorem shape_avoids (partner : RhoProcess) : contextAvoidsHole hole (partnerShape partner) = true := by
  simp [partnerShape, contextAvoidsHole, avoidsHoleList, avoidsHole_process partner]

/-- **Placing a process beside the partner is their parallel composition.** -/
theorem plug_partner (partner source : RhoProcess) :
    plug hole (partnerContext partner) source.1 = (par source partner).1 :=
  plug_fill (partnerShape partner) (shape_avoids partner) (closed_of_process (process_closed source))

/-- **Whether a label is a partner's**: a context label whose context is a closed process beside the hole, read
plainly. -/
def isPartnerLabel : StepLabel → Bool
  | .context name (.collection .hashBag [.fvar name', partner] none) .any =>
    name == hole && name' == hole && process partner
  | _ => false

theorem isPartnerLabel_partnerLabel (partner : RhoProcess) : isPartnerLabel (partnerLabel partner) = true := by
  simp [isPartnerLabel, partnerLabel, partnerContext_eq, process_closed partner]

theorem exists_of_isPartnerLabel {label : StepLabel} (partnerOf : isPartnerLabel label = true) :
    ∃ partner : RhoProcess, label = partnerLabel partner := by
  match label, partnerOf with
  | .context name (.collection .hashBag [.fvar name', partner] none) .any, partnerOf =>
    simp only [isPartnerLabel, Bool.and_eq_true, beq_iff_eq] at partnerOf
    obtain ⟨⟨rfl, rfl⟩, admitted⟩ := partnerOf
    exact ⟨ofProcess admitted, rfl⟩

/-- **A step in a partner's context is a partner-labelled step**: the process beside the partner steps. -/
theorem step_partner_iff (partner source target : RhoProcess) :
    frontDoor.step source.1 (partnerLabel partner) target.1 ↔ (partnerSystem PEmpty.{1} (fun atom => atom.elim)).act partner source target := by
  change _ ↔ rhoLanguageDefGSLT.Step (par source partner) target
  rw [← step_any_iff, step_context_iff]
  constructor
  · rintro ⟨-, presentation, presents, -, step⟩
    have presentationProcess := process_invariant (process_closed source) presents
    have same : (par (ofProcess presentationProcess) partner).1 = plug hole (partnerContext partner) presentation :=
      (plug_partner partner (ofProcess presentationProcess)).symm
    rw [← same] at step
    have equivalent : ObjectEquivalent RelationEnv.empty rhoCalc reading (par (ofProcess presentationProcess) partner).1
        (par source partner).1 := by
      refine (objectEquivalent_iff_processes (process_closed _) (process_closed _)).mpr ?_
      exact ParallelContextAdequacy.par_equiv_left partner
        ((canonicalize_eq_of_objectEquivalent presents).symm : rhoLanguageDefGSLT.Equiv (ofProcess presentationProcess) source)
    exact (referenceStructure_saturated RelationEnv.empty rhoCalc reading).stepSource
      (Indistinct.of_states (isState_of_process (process_closed _)) (isState_of_process (process_closed _)) equivalent)
      step
  · intro step
    refine ⟨isState_of_process (process_closed source), source.1, Relation.EqvGen.refl _,
      isState_of_process (process_closed source), ?_⟩
    rw [plug_partner]
    exact step

/-! ## Finitely many partner steps, keeping the processes -/

/-- The region of closed processes. -/
abbrev processes (term : Pattern) : Prop := process term = true

/-- **Partner steps keep the closed processes.** -/
theorem closedUnder : frontDoor.ClosedUnder isPartnerLabel processes := by
  intro source label target sourceIn partnerOf step
  obtain ⟨partner, rfl⟩ := exists_of_isPartnerLabel partnerOf
  obtain ⟨-, -, redex, contractum, witness, ⟨presentation, presents, -, -, placed⟩, -, valid, -, after, -⟩ := step
  have presentationProcess := process_invariant sourceIn presents
  rw [show presentation = (ofProcess presentationProcess).1 from rfl, plug_partner] at placed
  have redexProcess := process_invariant (process_closed _) placed
  exact process_invariant (process_of_step redexProcess valid.2) after

/-- **Partner steps are finitely many up to the equations**, by the complete canonical successor sets. -/
theorem finiteUpTo : frontDoor.FiniteUpTo isPartnerLabel processes (Indistinct RelationEnv.empty rhoCalc reading) := by
  intro source sourceIn label partnerOf
  obtain ⟨partner, rfl⟩ := exists_of_isPartnerLabel partnerOf
  let start := ofProcess sourceIn
  let listed := ((CanonicalPartnerCoalgebra.successors (CanonicalBag.fromProcess start)
    (CanonicalBag.fromProcess partner)).toList).map fun bag => (CanonicalBag.toProcess bag).1
  refine ⟨listed, ?_, ?_⟩
  · intro target member
    obtain ⟨bag, bagMember, rfl⟩ := List.mem_map.mp member
    have inSuccessors := Finset.mem_toList.mp bagMember
    rw [← CanonicalBag.fromProcess_toProcess bag] at inSuccessors
    exact (step_partner_iff partner start (CanonicalBag.toProcess bag)).mpr
      ((CanonicalPartnerCoalgebra.mem_successors_iff_public start partner _).mp inSuccessors)
  · intro target step
    have targetIn := closedUnder sourceIn (isPartnerLabel_partnerLabel partner) step
    let reached := ofProcess targetIn
    have partnerStep := (step_partner_iff partner start reached).mp step
    have inSuccessors := (CanonicalPartnerCoalgebra.mem_successors_iff_public start partner reached).mpr partnerStep
    refine ⟨(CanonicalBag.toProcess (CanonicalBag.fromProcess reached)).1,
      List.mem_map.mpr ⟨_, Finset.mem_toList.mpr inSuccessors, rfl⟩, ?_⟩
    refine Indistinct.of_states (isState_of_process targetIn) (isState_of_process (process_closed _)) ?_
    refine (objectEquivalent_iff_processes targetIn (process_closed _)).mpr ?_
    rw [CanonicalBag.toProcess_fromProcess]
    exact (Canonical.canonicalize_idempotent target).symm

/-! ## The characterization -/

/-- **Two closed processes have the same native types under parallel partners exactly when they are forward
bisimilar under partners.** -/
theorem agree_iff_forwardBisimilar (first second : RhoProcess) :
    frontDoor.AgreeOn (Formula.forwardOn isPartnerLabel) first.1 second.1 ↔
      frontDoor.ForwardBisimilar isPartnerLabel first.1 second.1 :=
  NativeStructure.agree_iff_forwardBisimilar (referenceStructure_saturated RelationEnv.empty rhoCalc reading)
    finiteUpTo closedUnder (process_closed first) (process_closed second)

/-- **Forward bisimilarity under partners is ρ's partner bisimilarity.** -/
theorem forwardBisimilar_iff_partnerBisimilar (first second : RhoProcess) :
    frontDoor.ForwardBisimilar isPartnerLabel first.1 second.1 ↔
      (partnerSystem PEmpty.{1} (fun atom => atom.elim)).Bisimilar first second := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    refine ⟨fun left right => relation left.1 right.1, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, related⟩
    · intro left right relatedHere partner left' step
      obtain ⟨next, step', relatedNext⟩ := bisimulation.forth relatedHere (isPartnerLabel_partnerLabel partner)
        ((step_partner_iff partner left left').mpr step)
      have nextIn := closedUnder (process_closed right) (isPartnerLabel_partnerLabel partner) step'
      exact ⟨ofProcess nextIn, (step_partner_iff partner right (ofProcess nextIn)).mp step', relatedNext⟩
    · intro left right relatedHere partner right' step
      obtain ⟨next, step', relatedNext⟩ := bisimulation.back relatedHere (isPartnerLabel_partnerLabel partner)
        ((step_partner_iff partner right right').mpr step)
      have nextIn := closedUnder (process_closed left) (isPartnerLabel_partnerLabel partner) step'
      exact ⟨ofProcess nextIn, (step_partner_iff partner left (ofProcess nextIn)).mp step', relatedNext⟩
  · rintro ⟨relation, ⟨forth, back, -⟩, related⟩
    refine ⟨fun left right => ∃ (leftProcess : process left = true) (rightProcess : process right = true),
      relation (ofProcess leftProcess) (ofProcess rightProcess), ⟨?_, ?_⟩,
        process_closed first, process_closed second, related⟩
    · rintro left right label next ⟨leftProcess, rightProcess, relatedHere⟩ partnerOf step
      obtain ⟨partner, rfl⟩ := exists_of_isPartnerLabel partnerOf
      have nextIn := closedUnder leftProcess partnerOf step
      obtain ⟨next', step', relatedNext⟩ := forth relatedHere partner
        ((step_partner_iff partner (ofProcess leftProcess) (ofProcess nextIn)).mp step)
      exact ⟨next'.1, (step_partner_iff partner (ofProcess rightProcess) next').mpr step', nextIn,
        process_closed next', relatedNext⟩
    · rintro left right label next' ⟨leftProcess, rightProcess, relatedHere⟩ partnerOf step
      obtain ⟨partner, rfl⟩ := exists_of_isPartnerLabel partnerOf
      have nextIn := closedUnder rightProcess partnerOf step
      obtain ⟨next, step', relatedNext⟩ := back relatedHere partner
        ((step_partner_iff partner (ofProcess rightProcess) (ofProcess nextIn)).mp step)
      exact ⟨next.1, (step_partner_iff partner (ofProcess leftProcess) next).mpr step', process_closed next, nextIn,
        relatedNext⟩

/-- **The front door's context-labelled native types of ρ characterize its partner bisimilarity**: two closed
processes satisfy the same forward formulas under parallel partners exactly when they are partner bisimilar. -/
theorem agree_iff_partnerBisimilar (first second : RhoProcess) :
    frontDoor.AgreeOn (Formula.forwardOn isPartnerLabel) first.1 second.1 ↔
      (partnerSystem PEmpty.{1} (fun atom => atom.elim)).Bisimilar first second :=
  (agree_iff_forwardBisimilar first second).trans (forwardBisimilar_iff_partnerBisimilar first second)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.Rho.Partners
