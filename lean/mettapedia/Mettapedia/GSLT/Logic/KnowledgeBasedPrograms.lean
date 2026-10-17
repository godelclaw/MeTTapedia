import Mettapedia.GSLT.Logic.KripkeFixedPoint

/-!
# Knowledge-based programs as lazy epistemic inquiry

A knowledge-based program (Fagin, Halpern, Moses and Vardi, *Reasoning About
Knowledge*, chapter 7) prescribes an action by a test on what the agent
knows: "ask if I do not already know the answer".  Whether the agent knows
something can depend on what the agents do, so a program is implemented by a
protocol that agrees with the program evaluated in the system the protocol
itself generates: an implementation is a fixed point, and a program can have
none, one or several.

Here the knowledge tests are three-valued approximations: a test is *known*,
*refuted* or *undetermined*, evaluated by the strong Kleene clauses over the
worlds the agent cannot tell apart.  The judgments "agent `i` performs action
`a` in local state `ℓ`" form a system of Kripke's partial truth
(`Mettapedia.GSLT.KripkeTruth`), and its jump is monotone in information.

* **Translation** (`Context.system`): a program and a finite epistemic frame
  give a Kripke system; knowing `φ` at a world is the conjunction of `φ` over
  the worlds with the same local state.
* **Implementations are the two-valued fixed points** (`implementation_fixed`).
* **The grounded decisions never commit early** (`least_le_implementation`,
  `stage_sound`): every decision the inquiry has made at any finite stage is
  made by every implementation.  Inquiry is lazy: a decision is made exactly
  when finite evidence for it exists (`KripkeTruth.System.mem_least_iff_evidence`),
  and a decision once made is never retracted (`KripkeTruth.System.stage_mono`).
* **Zero, one and several implementations**:
  - `Examples.Liar`: "act if I know I will not act" has no implementation;
  - `Examples.Ask`: "ask if I know neither the answer nor its negation" has
    exactly one, decided by the inquiry;
  - `Examples.Teller`: "act if I know I will act" has two, and the grounded
    inquiry leaves the act undetermined.
* **A decided inquiry has exactly one implementation**
  (`implementation_eq_of_decided`): when the grounded decisions cover every
  judgment, every implementation is the grounded one.
* **Inquiry may never end** (`Examples.Relay`): in an infinite relay, agent
  `n + 1` acts when it knows agent `n` acted.  Every agent's act is decided at
  a finite stage and no finite stage decides them all.
* **Knowledge is the interior of an observer's partition** (`knows`): what an
  observer knows is the largest set of worlds below a proposition that the
  observer cannot split.  It satisfies the S5 laws (`knows_le`, `knows_knows`,
  `not_knows_le_knows_not_knows`), so knowledge-based tests are observer-indexed
  truth in the sense of the bubbles of `Mettapedia.GSLT.ObserverBubble`.

The least-fixed-point treatment of knowledge-based programs is that of Knapp,
Mühlberger and Reus, *Interpreting knowledge-based programs* (ESOP 2023), who
obtain it by a must/cannot analysis over reachable states and show that the
least constructive fixed point bounds every solution and, when decided, gives
a unique one.  The development here is the one-round case, obtained from
Kripke's construction, together with the infinite relay.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.KnowledgeBasedPrograms

open Mettapedia.GSLT.KripkeTruth

universe u

/-- The conjunction of a list of strong Kleene formulas, with a true base
fact for the empty list. -/
def bigConj {Judgment Base : Type*} (top : Base) :
    List (Formula Judgment Base) → Formula Judgment Base
  | [] => .base top
  | formula :: rest =>
      match rest with
      | [] => formula
      | _ :: _ => .conj formula (bigConj top rest)

/-- World-relative epistemic formulas. -/
inductive EFormula (Agent Fact Act : Type*)
  | fact (fact : Fact)
  | does (agent : Agent) (act : Act)
  | neg (formula : EFormula Agent Fact Act)
  | conj (first second : EFormula Agent Fact Act)
  | disj (first second : EFormula Agent Fact Act)
  | knows (agent : Agent) (formula : EFormula Agent Fact Act)

/-- A finite epistemic frame: an enumeration of the worlds, what each agent
observes at each world, and which facts hold where. -/
structure Context (Agent World Local Fact : Type*) where
  worlds : List World
  localState : Agent → World → Local
  factHolds : World → Fact → Bool

namespace Context

variable {Agent World Local Fact Act : Type*} [DecidableEq Local]
variable (context : Context Agent World Local Fact)

/-- Judgments: an agent performs an action in a local state. -/
abbrev Judgment (Agent Local Act : Type*) := Agent × Local × Act

/-- Base facts: a fact at a world, or the true fact `none`. -/
abbrev Base (World Fact : Type*) := Option (World × Fact)

/-- The worlds an agent cannot tell apart from a local state. -/
def classOf (agent : Agent) (state : Local) : List World :=
  context.worlds.filter fun world => context.localState agent world = state

/-- Translate an epistemic formula at a world. -/
def translate : World → EFormula Agent Fact Act →
    Formula (Judgment Agent Local Act) (Base World Fact)
  | world, .fact fact => .base (some (world, fact))
  | world, .does agent act => .truth (agent, context.localState agent world, act)
  | world, .neg formula => .neg (translate world formula)
  | world, .conj first second => .conj (translate world first) (translate world second)
  | world, .disj first second => .disj (translate world first) (translate world second)
  | world, .knows agent formula =>
      bigConj none ((context.classOf agent (context.localState agent world)).map
        fun other => translate other formula)

/-- **The Kripke system of a knowledge-based program**: agent `i` performs `a`
in local state `ℓ` when the program's test for `a` holds at every world of
that local state. -/
def system (program : Agent → Act → EFormula Agent Fact Act) :
    System (Judgment Agent Local Act) (Base World Fact) where
  spec := fun ⟨agent, state, act⟩ =>
    bigConj none ((context.classOf agent state).map fun world =>
      context.translate world (program agent act))
  baseHolds
    | none => True
    | some (world, fact) => context.factHolds world fact = true
  baseFails
    | none => False
    | some (world, fact) => context.factHolds world fact = false
  base_consistent
    | none => fun _ fails => fails
    | some (world, fact) => fun holds fails => by
        change context.factHolds world fact = true at holds
        change context.factHolds world fact = false at fails
        rw [holds] at fails
        exact Bool.noConfusion fails

/-- Boolean values of base facts. -/
def baseValue : Base World Fact → Bool
  | none => true
  | some (world, fact) => context.factHolds world fact

end Context

/-! ## Implementations -/

section Implementations

variable {Judgment : Type*} {Base : Type*} (system : System Judgment Base)

/-- The three-valued valuation of a protocol. -/
def toValuation (protocol : Judgment → Bool) : Valuation Judgment :=
  ⟨{judgment | protocol judgment = true}, {judgment | protocol judgment = false}⟩

/-- **An implementation** of a program: a protocol that agrees with the
program's tests evaluated in the protocol itself. -/
def IsImplementation (baseValue : Base → Bool) (protocol : Judgment → Bool) : Prop :=
  ∀ judgment, protocol judgment = System.evalBool baseValue protocol (system.spec judgment)

/-- Base facts are bivalent and read by `baseValue`. -/
def BaseAgrees (baseValue : Base → Bool) : Prop :=
  ∀ fact, (system.baseHolds fact ↔ baseValue fact = true) ∧
    (system.baseFails fact ↔ baseValue fact = false)

theorem eval_toValuation {baseValue : Base → Bool} (agrees : BaseAgrees system baseValue)
    (protocol : Judgment → Bool) :
    ∀ formula : Formula Judgment Base,
      ((system.eval (toValuation protocol) formula).1 ↔
          System.evalBool baseValue protocol formula = true) ∧
        ((system.eval (toValuation protocol) formula).2 ↔
          System.evalBool baseValue protocol formula = false)
  | .base fact => agrees fact
  | .truth _ => ⟨Iff.rfl, Iff.rfl⟩
  | .neg formula => by
      have ih := eval_toValuation agrees protocol formula
      simp only [System.eval, System.evalBool, Bool.not_eq_true', Bool.not_eq_false']
      exact ⟨ih.2, ih.1⟩
  | .conj first second => by
      have ihFirst := eval_toValuation agrees protocol first
      have ihSecond := eval_toValuation agrees protocol second
      simp only [System.eval, System.evalBool, Bool.and_eq_true, Bool.and_eq_false_iff]
      exact ⟨and_congr ihFirst.1 ihSecond.1, or_congr ihFirst.2 ihSecond.2⟩
  | .disj first second => by
      have ihFirst := eval_toValuation agrees protocol first
      have ihSecond := eval_toValuation agrees protocol second
      simp only [System.eval, System.evalBool, Bool.or_eq_true, Bool.or_eq_false_iff]
      exact ⟨or_congr ihFirst.1 ihSecond.1, and_congr ihFirst.2 ihSecond.2⟩

/-- **Implementations are two-valued fixed points of the jump.** -/
theorem implementation_fixed {baseValue : Base → Bool} (agrees : BaseAgrees system baseValue)
    {protocol : Judgment → Bool} (implements : IsImplementation system baseValue protocol) :
    (system.jump (toValuation protocol)).Le (toValuation protocol) ∧
      (toValuation protocol).Le (system.jump (toValuation protocol)) := by
  have both := fun judgment =>
    eval_toValuation system agrees protocol (system.spec judgment)
  refine ⟨⟨fun judgment held => ?_, fun judgment failed => ?_⟩,
    ⟨fun judgment held => ?_, fun judgment failed => ?_⟩⟩
  · change protocol judgment = true
    rw [implements judgment]
    exact (both judgment).1.1 held
  · change protocol judgment = false
    rw [implements judgment]
    exact (both judgment).2.1 failed
  · change (system.eval (toValuation protocol) (system.spec judgment)).1
    rw [(both judgment).1, ← implements judgment]
    exact held
  · change (system.eval (toValuation protocol) (system.spec judgment)).2
    rw [(both judgment).2, ← implements judgment]
    exact failed

/-- **The grounded decisions are made by every implementation.** -/
theorem least_le_implementation {baseValue : Base → Bool} (agrees : BaseAgrees system baseValue)
    {protocol : Judgment → Bool} (implements : IsImplementation system baseValue protocol) :
    system.least.Le (toValuation protocol) :=
  system.least_le (implementation_fixed system agrees implements).1

/-- **Inquiry never commits early**: a decision made at any finite stage is
made by every implementation. -/
theorem stage_sound {baseValue : Base → Bool} (agrees : BaseAgrees system baseValue)
    {protocol : Judgment → Bool} (implements : IsImplementation system baseValue protocol)
    (n : ℕ) : (system.stage n).Le (toValuation protocol) :=
  Valuation.le_trans (system.stage_le_least n) (least_le_implementation system agrees implements)

/-- **A decided inquiry has exactly one implementation**: when the grounded
decisions cover every judgment, every implementation agrees with them. -/
theorem implementation_eq_of_decided {baseValue : Base → Bool} (agrees : BaseAgrees system baseValue)
    (decided : ∀ judgment, judgment ∈ system.least.holds ∨ judgment ∈ system.least.fails)
    {protocol : Judgment → Bool} (implements : IsImplementation system baseValue protocol)
    (judgment : Judgment) :
    protocol judgment = true ↔ judgment ∈ system.least.holds := by
  have below := least_le_implementation system agrees implements
  constructor
  · intro held
    rcases decided judgment with inLeast | failed
    · exact inLeast
    · have : protocol judgment = false := below.2 failed
      rw [held] at this
      exact Bool.noConfusion this
  · intro inLeast
    exact below.1 inLeast

end Implementations

/-! ## Knowledge as the interior of an observer's partition -/

section Knowledge

variable {World : Type*} (observes : Setoid World)

/-- What an observer knows of a proposition: the worlds all of whose
indistinguishable worlds satisfy it. -/
def knows (proposition : Set World) : Set World :=
  {world | ∀ other, observes.r world other → other ∈ proposition}

/-- Truth: what is known holds. -/
theorem knows_le (proposition : Set World) : knows observes proposition ⊆ proposition :=
  fun world known => known world (observes.iseqv.refl world)

/-- Positive introspection. -/
theorem knows_knows (proposition : Set World) :
    knows observes (knows observes proposition) = knows observes proposition := by
  apply Set.Subset.antisymm (knows_le observes _)
  intro world known other related further relatedFurther
  exact known further (observes.iseqv.trans related relatedFurther)

/-- Negative introspection. -/
theorem not_knows_le_knows_not_knows (proposition : Set World) :
    (knows observes proposition)ᶜ ⊆ knows observes (knows observes proposition)ᶜ := by
  intro world unknown other related knownOther
  apply unknown
  intro further relatedFurther
  exact knownOther further (observes.iseqv.trans (observes.iseqv.symm related) relatedFurther)

/-- Knowledge is monotone. -/
theorem knows_mono {first second : Set World} (le : first ⊆ second) :
    knows observes first ⊆ knows observes second :=
  fun _ known other related => le (known other related)

/-- What is known is invariant under the observer's indistinguishability. -/
theorem knows_invariant (proposition : Set World) {world other : World}
    (related : observes.r world other) :
    world ∈ knows observes proposition ↔ other ∈ knows observes proposition :=
  ⟨fun known further relatedFurther =>
      known further (observes.iseqv.trans related relatedFurther),
    fun known further relatedFurther =>
      known further (observes.iseqv.trans (observes.iseqv.symm related) relatedFurther)⟩

end Knowledge

theorem Context.baseAgrees {Agent World Local Fact Act : Type*} [DecidableEq Local]
    (context : Context Agent World Local Fact) (program : Agent → Act → EFormula Agent Fact Act) :
    BaseAgrees (context.system program) context.baseValue := by
  intro fact
  cases fact with
  | none => simp [Context.system, Context.baseValue]
  | some pair =>
      obtain ⟨world, fact⟩ := pair
      simp [Context.system, Context.baseValue]

/-! ## Zero, one and several implementations -/

namespace Examples

/-- One agent, one action. -/
inductive Act
  | act
  deriving DecidableEq

/-- A frame with one world and one local state. -/
def single : Context Unit Unit Unit Empty where
  worlds := [()]
  localState _ _ := ()
  factHolds _ fact := fact.elim

/-- The judgment "the agent acts". -/
abbrev acts : Context.Judgment Unit Unit Act := ((), (), .act)

namespace Liar

/-- **Act if I know I will not act.** -/
def program : Unit → Act → EFormula Unit Empty Act :=
  fun _ _ => .knows () (.neg (.does () .act))

theorem spec_eq : (single.system program).spec acts = .neg (.truth acts) := rfl

/-- **No implementation.** -/
theorem no_implementation :
    ¬ ∃ protocol, IsImplementation (single.system program) single.baseValue protocol :=
  fun ⟨protocol, implements⟩ =>
    (single.system program).no_two_valued_fixedPoint (liar := acts) spec_eq single.baseValue
      ⟨protocol, implements⟩

/-- The grounded inquiry leaves the act undetermined. -/
theorem undetermined : acts ∉ (single.system program).least.holds ∧
    acts ∉ (single.system program).least.fails :=
  (single.system program).liar_not_mem_least spec_eq

end Liar

namespace Teller

/-- **Act if I know I will act.** -/
def program : Unit → Act → EFormula Unit Empty Act :=
  fun _ _ => .knows () (.does () .act)

theorem spec_eq : (single.system program).spec acts = .truth acts := rfl

/-- **Two implementations**: always acting and never acting. -/
theorem two_implementations :
    IsImplementation (single.system program) single.baseValue (fun _ => true) ∧
      IsImplementation (single.system program) single.baseValue (fun _ => false) := by
  constructor
  · rintro ⟨_, _, _⟩
    rfl
  · rintro ⟨_, _, _⟩
    rfl

/-- The grounded inquiry leaves the act undetermined. -/
theorem undetermined : acts ∉ (single.system program).least.holds ∧
    acts ∉ (single.system program).least.fails :=
  (single.system program).truthTeller_not_mem_least spec_eq

end Teller

namespace Ask

/-- The answer: is it sunny? -/
inductive World
  | sunny
  | rainy
  deriving DecidableEq

/-- The asker does not observe the weather; the observer does. -/
inductive Agent
  | asker
  | observer
  deriving DecidableEq

/-- The fact "it is sunny". -/
inductive Fact
  | isSunny
  deriving DecidableEq

/-- Two worlds; the asker's local state is the same in both. -/
def frame : Context Agent World (Option World) Fact where
  worlds := [.sunny, .rainy]
  localState agent world := match agent with
    | .asker => none
    | .observer => some world
  factHolds world _ := match world with
    | .sunny => true
    | .rainy => false

/-- **Ask if I know neither the answer nor its negation.** -/
def program : Agent → Act → EFormula Agent Fact Act :=
  fun agent _ => .neg (.disj (.knows agent (.fact .isSunny))
    (.knows agent (.neg (.fact .isSunny))))

/-- The asker asks. -/
abbrev asks : Context.Judgment Agent (Option World) Act := (.asker, none, .act)

/-- The observer, in the sunny world, does not ask. -/
abbrev observerSunny : Context.Judgment Agent (Option World) Act :=
  (.observer, some .sunny, .act)

/-- The unique implementation: the informed observer does not ask, the
uninformed asker does.  A local state no world produces is decided vacuously. -/
def protocol : Context.Judgment Agent (Option World) Act → Bool
  | (.observer, some _, _) => false
  | _ => true

/-- **Exactly one implementation.** -/
theorem implementation : IsImplementation (frame.system program) frame.baseValue protocol := by
  rintro ⟨agent, state, action⟩
  cases agent <;> cases action <;> rcases state with _ | _ | _ <;> rfl

theorem unique_implementation (other : Context.Judgment Agent (Option World) Act → Bool)
    (implements : IsImplementation (frame.system program) frame.baseValue other) :
    other = protocol := by
  funext judgment
  obtain ⟨agent, state, action⟩ := judgment
  rw [implements]
  cases agent <;> cases action <;> rcases state with _ | _ | _ <;> rfl

/-- **The inquiry decides it**: by the third stage the asker asks and the
informed observer does not. -/
theorem decided : asks ∈ ((frame.system program).stage 3).holds ∧
    observerSunny ∈ ((frame.system program).stage 3).fails := by
  constructor
  · show (System.eval _ _ _).1
    simp [Context.system, frame, program, Context.classOf, Context.translate, bigConj,
      System.eval, System.stage, System.jump, Valuation.bottom]
  · show (System.eval _ _ _).2
    simp [Context.system, frame, program, Context.classOf, Context.translate, bigConj,
      System.eval, System.stage, System.jump, Valuation.bottom]

end Ask

namespace Relay

/-- Agent `n + 1` acts when it knows agent `n` acted; agent `0` acts. -/
def system : System ℕ Unit where
  spec
    | 0 => .base ()
    | n + 1 => .truth n
  baseHolds _ := True
  baseFails _ := False
  base_consistent _ _ fails := fails

theorem not_held_at_stage (n : ℕ) : n ∉ (system.stage n).holds := by
  induction n with
  | zero => exact fun held => held
  | succ n ih =>
      intro held
      exact ih held

theorem held_at_stage (n : ℕ) : n ∈ (system.stage (n + 1)).holds := by
  induction n with
  | zero => trivial
  | succ n ih => exact ih

/-- **Inquiry that never ends**: every agent's act is decided at a finite stage,
and no finite stage decides them all. -/
theorem never_ends :
    (∀ n, n ∈ system.least.holds) ∧ ∀ k, ∃ n, n ∉ (system.stage k).holds :=
  ⟨fun n => (system.stage_le_least (n + 1)).1 (held_at_stage n),
    fun k => ⟨k, not_held_at_stage k⟩⟩

end Relay

end Examples

end Mettapedia.GSLT.KnowledgeBasedPrograms
