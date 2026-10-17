import Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily.Presentations
import Mettapedia.OSLF.NativeTypes.SortProfiles.Inhabitation
import Mettapedia.OSLF.Framework.TypeSynthesis
import Mettapedia.Languages.MeTTa.HE.HELanguageDef

open Mettapedia.OSLF.Framework

/-!
# The equation-application site of HE MeTTa, end to end

HE MeTTa evaluates a call by querying the space for equations `(= lhs rhs)`
whose left side matches the call, and continuing with the instantiated right
side. This module follows that site through the generated hypercube.

**The machine presentation hides the redex.** In `mettaHE` the rule
`MC_Equation` rewrites the state `⟨mettacall(atom, ty) | space | out⟩`; the
equation lookup is the premise `eqQueryResult(space, atom, rhs)`. Its sites
therefore see the call as one undivided metavariable `atom`: the site at the
call has the interface (no index; rely `ty`, `space`, `out`; hole `Atom`;
target `State`) (`machine_call_interface`). The space is a rely variable: the
generated modality quantifies over programs. The answer `rhs` is a
target-only (ambient) variable (`machine_answer_is_ambient`). In the paper's
completion of the machine no carrier has a closed type at any vertex
(`machine_top_untyped`): every target is a state, and no slot ranges over
states. Constructor types of the machine's nullary atoms are the only seeds
(`machine_seeded_types`).

**The program presentation displays it.** Read a program's equations as
rewrites over the ground-atom codec (`programLanguage`). The head of a call
`(f $x)` is then a displayed occurrence whose context is the call with the
argument as its only rely variable: the interface of the beta site of the
lambda calculus, over the carrier of atoms (`head_site_interface`). Its local
cube is the lambda cube (`head_site_slots`, eight based choices), and closed
types at that carrier exist exactly at the vertices with polymorphism
(`head_site_cube`). The argument position has no rely variable: it generates
only the target axis (`argument_site_interface`). Reading the head as a
constructor label instead removes the head occurrence, and with it every
product-shaped site (`label_reading_has_no_head_site`).

**May against must.** The generated types are may-types. In the sample
program `(g a)` steps to `b` and to `c` (`call_successors`), so it has the
possibility of reaching `b` while not every successor is `b`
(`may_not_must`). Without the third equation every successor is `b`
(`prefix_must`): adding an equation to the space keeps every may-fact and
can break a must-fact (`adding_equation_breaks_must`). A call with no
equation has no successor: every must-claim holds of it vacuously and no
may-claim does (`stuck_call_vacuous`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily.EquationSite

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge.GroundData (schema)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.Framework.RedexPosition (fvarNames)
open Mettapedia.OSLF.Framework.TypeSynthesis (langReduces mem_rootFrontier_iff_langReducesUsing)
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Generation.Occurrences
open Mettapedia.OSLF.NativeTypes.SortProfiles
open Mettapedia.OSLF.NativeTypes.SortProfiles.Inhabitation
open Mettapedia.Logic.LP.HypotheticalPropositional
open Mettapedia.Languages.MeTTa.HE.LanguageDef (mettaHE)

/-! ## The machine presentation -/

/-- The rule continuing a call with the right side of a matching equation. -/
def machineEquationRule : RewriteRule := mettaHE.rewrites[53]'(by decide)

theorem machineEquationRule_name : machineEquationRule.name = "MC_Equation" := by decide

/-- The equation lookup is a premise, not a displayed occurrence. -/
theorem machine_lookup_is_premise :
    Premise.relationQuery "eqQueryResult" [.fvar "space", .fvar "atom", .fvar "rhs"] ∈
      machineEquationRule.premises := by
  decide

/-- The site at the call: the call is the bare metavariable `atom`. -/
def machineCallSite : Site where
  context := .apply "State" [] (.apply "MettaCall" [] .hole [.fvar "ty"]) [.fvar "space", .fvar "out"]
  focus := .fvar "atom"
  declaration := 53
  rule := machineEquationRule

theorem machine_call_generated : machineCallSite ∈ generate mettaHE :=
  (generate_spec _ _).mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr rfl,
    Selects.apply (Selects.apply Selects.here)⟩

theorem machine_call_rely : machineCallSite.relyNames = ["ty", "space", "out"] := by
  decide +kernel

theorem machine_answer_is_ambient :
    SiteInterfaces.ambientNames machineCallSite = ["atom", "rhs"] := by
  decide +kernel

/-- **The machine's call site.** No index; the expected type, the space and
the output as rely; an atom in the hole; a state as target. -/
theorem machine_call_interface :
    interfaceOf? mettaHE machineCallSite =
      some ⟨[], [.base "Atom", .base "Space", .base "Atom"], .base "Atom", .base "State"⟩ := by
  decide +kernel

/-- **No closed type at any vertex of the machine's completion.** -/
theorem machine_top_untyped :
    ∀ carrier ∈ carriers mettaHE, ¬ Derives (paperTop mettaHE) ∅ (carrier, .star) := by
  decide +kernel

/-- Constructor types of the nullary atoms type every carrier of the machine. -/
theorem machine_seeded_types :
    ∀ carrier ∈ carriers mettaHE, Derives (seeded mettaHE (paperOrigin mettaHE)) ∅ (carrier, .star) := by
  decide +kernel

/-! ## The program presentation -/

/-- The sample program as an operational presentation. -/
def program : LanguageDef := programLanguage "metta-program" sampleProgram

/-- `(= (f $x) (g $x))`, the first equation. -/
def forwarding : RewriteRule := equationRule 0 (call "f" (.var "x")) (call "g" (.var "x"))

/-- The head of `(f $x)`, in the call context. -/
def headSite : Site where
  context := .apply "ground-atom-expression-v1" []
    (.collection .vec [] .hole [.fvar "x"] none) []
  focus := schema (.symbol "f")
  declaration := 0
  rule := forwarding

theorem head_site_generated : headSite ∈ generate program :=
  (generate_spec _ _).mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr rfl,
    Selects.apply (Selects.collection Selects.here)⟩

/-- **The head of a call is a beta site.** -/
theorem head_site_interface :
    interfaceOf? program headSite = some (betaInterface (.base "GroundAtom")) := by
  decide +kernel

theorem head_site_slots : SiteInterfaces.slotCount headSite = 2 := by decide +kernel

theorem head_site_based_choices :
    (SiteInterfaces.basedChoices (SiteInterfaces.slotCount headSite)).card = 8 := by
  rw [head_site_slots]
  exact SiteInterfaces.lambda_cube_count

/-- **The head site's cube is the lambda cube**: closed types at atoms exist
exactly at the vertices with polymorphism. -/
theorem head_site_cube :
    ∀ choice ∈ productProfiles.sublists,
      (Derives (productClauses (.base "GroundAtom") choice) ∅ (.base "GroundAtom", .star) ↔
        (.box, .star) ∈ choice) := by
  decide +kernel

/-- The argument of `(f $x)`: no rely variable, so no dependency axis. -/
def argumentSite : Site where
  context := .apply "ground-atom-expression-v1" []
    (.collection .vec [schema (.symbol "f")] .hole [] none) []
  focus := .fvar "x"
  declaration := 0
  rule := forwarding

theorem argument_site_generated : argumentSite ∈ generate program :=
  (generate_spec _ _).mpr ⟨List.mk_mem_zipIdx_iff_getElem?.mpr rfl,
    Selects.apply (Selects.collection Selects.here)⟩

theorem argument_site_interface :
    interfaceOf? program argumentSite =
      some ⟨[], [], .base "GroundAtom", .base "GroundAtom"⟩ := by
  decide +kernel

/-- A unary constructor of atoms. -/
def unaryLabel (label : String) : GrammarRule where
  label := label
  category := "Atom"
  params := [.simple "x" (.base "Atom")]
  syntaxPattern := []

/-- `(= (f $x) (g $x))` with the heads read as constructor labels. -/
def labelForwarding : RewriteRule where
  name := "equation-0"
  typeContext := [("x", .base "Atom")]
  premises := []
  left := .apply "f" [.fvar "x"]
  right := .apply "g" [.fvar "x"]

/-- The same equation with the head read as a constructor label. -/
def labelReading : LanguageDef where
  name := "metta-program-by-labels"
  types := ["Atom"]
  terms := [unaryLabel "f", unaryLabel "g"]
  equations := []
  rewrites := [labelForwarding]

/-- **Representation decides the site.** With heads as labels, no site has a
rely variable: the product-shaped site is gone. -/
theorem label_reading_has_no_head_site :
    ∀ site ∈ generate labelReading, site.relyNames = [] := by
  decide +kernel

/-! ## May against must -/

theorem program_noncontextual :
    ∀ rule ∈ program.rewrites, Mettapedia.OSLF.MeTTaIL.ContextualStep.NoncontextualPremises rule.premises := by
  intro rule member
  simp only [program, programLanguage, List.mem_map] at member
  obtain ⟨_, _, rfl⟩ := member
  exact .nil

theorem prefix_noncontextual :
    ∀ rule ∈ (programLanguage "metta-program" sampleProgramPrefix).rewrites,
      Mettapedia.OSLF.MeTTaIL.ContextualStep.NoncontextualPremises rule.premises := by
  intro rule member
  simp only [programLanguage, List.mem_map] at member
  obtain ⟨_, _, rfl⟩ := member
  exact .nil

/-- The successors of a source, computed by the root frontier. -/
theorem steps_iff (language : LanguageDef)
    (noncontextual : ∀ rule ∈ language.rewrites, Mettapedia.OSLF.MeTTaIL.ContextualStep.NoncontextualPremises rule.premises)
    (source target : Pattern) :
    langReduces language source target ↔
      target ∈ rewriteStepWithPremisesUsing RelationEnv.empty language source :=
  (mem_rootFrontier_iff_langReducesUsing _ _ noncontextual source target).symm

theorem call_successors :
    rewriteStepWithPremisesUsing RelationEnv.empty program (schema (call "g" (.symbol "a"))) =
      [schema (.symbol "b"), schema (.symbol "c")] := by
  decide +kernel

/-- **May, not must.** `(g a)` may reach `b`, and not every successor is `b`. -/
theorem may_not_must :
    (∃ target, langReduces program (schema (call "g" (.symbol "a"))) target ∧
        target = schema (.symbol "b")) ∧
      ¬ ∀ target, langReduces program (schema (call "g" (.symbol "a"))) target →
        target = schema (.symbol "b") := by
  refine ⟨⟨_, (steps_iff _ program_noncontextual _ _).mpr (by rw [call_successors]; simp), rfl⟩, ?_⟩
  intro must
  have reaches : langReduces program (schema (call "g" (.symbol "a"))) (schema (.symbol "c")) :=
    (steps_iff _ program_noncontextual _ _).mpr (by rw [call_successors]; simp)
  have := must _ reaches
  revert this
  decide +kernel

theorem prefix_successors :
    rewriteStepWithPremisesUsing RelationEnv.empty (programLanguage "metta-program" sampleProgramPrefix)
        (schema (call "g" (.symbol "a"))) = [schema (.symbol "b")] := by
  decide +kernel

/-- Without the third equation, every successor of `(g a)` is `b`. -/
theorem prefix_must :
    ∀ target, langReduces (programLanguage "metta-program" sampleProgramPrefix)
      (schema (call "g" (.symbol "a"))) target → target = schema (.symbol "b") := by
  intro target step
  have := (steps_iff _ prefix_noncontextual _ _).mp step
  rw [prefix_successors] at this
  simpa using this

/-- **Adding an equation keeps may-facts and breaks a must-fact.** Every
successor in the prefix program is a successor in the full program, while the
must-claim that holds of the prefix fails of the full program. -/
theorem adding_equation_breaks_must :
    (∀ target, langReduces (programLanguage "metta-program" sampleProgramPrefix)
        (schema (call "g" (.symbol "a"))) target →
      langReduces program (schema (call "g" (.symbol "a"))) target) ∧
    (∀ target, langReduces (programLanguage "metta-program" sampleProgramPrefix)
        (schema (call "g" (.symbol "a"))) target → target = schema (.symbol "b")) ∧
    ¬ (∀ target, langReduces program (schema (call "g" (.symbol "a"))) target →
        target = schema (.symbol "b")) := by
  refine ⟨fun target step => ?_, prefix_must, may_not_must.2⟩
  have inPrefix := (steps_iff _ prefix_noncontextual _ _).mp step
  rw [prefix_successors] at inPrefix
  apply (steps_iff _ program_noncontextual _ _).mpr
  rw [call_successors]
  simp at inPrefix
  simp [inPrefix]

theorem stuck_successors :
    rewriteStepWithPremisesUsing RelationEnv.empty program (schema (call "h" (.symbol "a"))) = [] := by
  decide +kernel

/-- **A call with no equation**: every must-claim holds vacuously, no may-claim. -/
theorem stuck_call_vacuous (claim : Pattern → Prop) :
    (∀ target, langReduces program (schema (call "h" (.symbol "a"))) target → claim target) ∧
      ¬ ∃ target, langReduces program (schema (call "h" (.symbol "a"))) target ∧ claim target := by
  have none : ∀ target, ¬ langReduces program (schema (call "h" (.symbol "a"))) target := by
    intro target step
    have := (steps_iff _ program_noncontextual _ _).mp step
    rw [stuck_successors] at this
    cases this
  exact ⟨fun target step => absurd step (none target), fun ⟨target, step, _⟩ => none target step⟩

end Mettapedia.OSLF.NativeTypes.Instances.MeTTaFamily.EquationSite
