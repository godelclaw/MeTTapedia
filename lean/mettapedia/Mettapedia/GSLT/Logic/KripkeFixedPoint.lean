import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Card
import Mettapedia.TypeTheory.Authority
import Mettapedia.Logic.Diagonal.Lawvere

/-!
# The partial escape: Kripke's least fixed point in the knowledge order

Judgments may speak about the truth of judgments.  Each judgment has a
specification, a strong Kleene formula over base facts and over the truth of
judgments.  A *valuation* is a three-valued assignment, presented as the set of
judgments held and the set of judgments failed; valuations are ordered by
inclusion of both sets, the *knowledge order* (undetermined below determined).
The *jump* evaluates every specification in a valuation.

* The jump is monotone (`jump_mono`), and the least fixed point exists as the
  intersection of all pre-fixed points (`least`, `jump_least_le`,
  `le_jump_least`, `least_le`), built without choice.
* **Duality** (`jump_dual_le`): the dual of a sound valuation (swap the two
  sets and complement them) is a pre-fixed point.  Hence the least fixed point
  lies below its own dual, which is consistency (`least_consistent`).
* **The diagonal stays undetermined** (`liar_undetermined`): a judgment whose
  specification is the negation of its own truth is neither held nor failed by
  any sound, consistent valuation, in particular by the least fixed point.
* **Leastness matters** (`truthTeller_not_mem_least`): a judgment specifying
  only its own truth is undetermined in the least fixed point; the concrete
  system below shows it held in one fixed point and failed in another.
* **Tarski** (`no_two_valued_fixedPoint`): with a liar, no two-valued valuation
  satisfies every specification; Boolean negation has no fixed point, while
  strong Kleene negation fixes `none` (`kleeneNot_none`,
  `liar_status_eq_none`).  This is the Lawvere obstruction and its escape.
* **The dual escape** (Fitting's conflation): with bivalent base facts the jump
  commutes with the dual (`jump_dual`), so the dual of the least fixed point is
  the greatest fixed point (`jump_greatest`, `le_greatest`).  There every
  judgment is held or failed (`greatest_complete`), and a judgment is undetermined
  in the least fixed point exactly when it is both held and failed in the
  greatest (`undetermined_least_iff_both_greatest`); the liar is both
  (`liar_both_greatest`).  The paracomplete escape (neither) and the
  paraconsistent escape (both) are one ungrounded status read through the dual.

**Outcomes.**  The verdict of a valuation is an `Outcome`: `established` on
held judgments, `refuted` on failed ones, `outsideFragment` (ungrounded)
elsewhere.  The least fixed point's verdicts are sound for the authority of
grounded truth (`groundedAuthority`), knowledge-below the verdicts of every
consistent pre-fixed valuation (`verdict_least_knowledgeLE`), and the liar's
verdict is `outsideFragment` (`verdict_liar_outside`).  Authority refinement is
a special case of the knowledge order (`knowledgeLE_of_authorityRefines`).

**Three readings of grounded truth.**  The least fixed point is the union of the
stages of the jump (`mem_least_iff_exists_stage`) and is derivability by well-founded
evidence trees (`mem_least_iff_evidence`); evidence of height `n` is decided at stage
`n + 1` and conversely (`mem_stage_succ_iff_evidence`).  Two evidence trees can give
one verdict (`Controls.twoEvidence_ne`).  **Circular justification** is the greatest
fixed point: every sound valuation lies below it (`le_greatest`), and with bivalent
base facts it is the union of the sound valuations (`mem_greatest_iff_sound`).  The
liar justifies both verdicts by itself (`liar_selfJustifying`) and has well-founded
evidence for neither (`liar_noEvidence`).  **The gap is invisible from inside**: no
formula holds exactly where a judgment is undetermined (`undetermined_not_definable`),
and the true statement that the liar is not true is not held by the least fixed point
(`liar_revenge`); it is made one level up.

**Finite systems are decided.**  For finitely many judgments the stages reach the least
fixed point after at most twice as many jumps as there are judgments (`stage_eq_least`),
and the Boolean iteration of the jump (`groundedDecide`) returns exactly its verdicts
(`groundedDecide_spec`); the concrete system below is decided by the kernel
(`Example.decided_verdicts`).

Base facts are three-valued too (`baseHolds`, `baseFails`, disjoint), so a
bubble's own budgeted verdicts can ground the system.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.KripkeTruth

open Mettapedia.TypeTheory.AuthorityTheory

universe u v

/-- Strong Kleene formulas over base facts and the truth of judgments. -/
inductive Formula (Judgment : Type u) (Base : Type v) where
  | base (fact : Base)
  | truth (judgment : Judgment)
  | neg (formula : Formula Judgment Base)
  | conj (first second : Formula Judgment Base)
  | disj (first second : Formula Judgment Base)

/-- A three-valued valuation: the judgments held and the judgments failed. -/
structure Valuation (Judgment : Type u) where
  holds : Set Judgment
  fails : Set Judgment

namespace Valuation

variable {Judgment : Type u}

/-- **The knowledge order**: everything determined stays determined the same
way. -/
def Le (first second : Valuation Judgment) : Prop :=
  first.holds ⊆ second.holds ∧ first.fails ⊆ second.fails

theorem le_refl (valuation : Valuation Judgment) : valuation.Le valuation :=
  ⟨fun _ member => member, fun _ member => member⟩

theorem le_trans {first second third : Valuation Judgment} (h : first.Le second)
    (h' : second.Le third) : first.Le third :=
  ⟨fun _ member => h'.1 (h.1 member), fun _ member => h'.2 (h.2 member)⟩

/-- No judgment is both held and failed. -/
def Consistent (valuation : Valuation Judgment) : Prop :=
  ∀ judgment, judgment ∈ valuation.holds → judgment ∉ valuation.fails

/-- The dual valuation: hold what is not failed, fail what is not held. -/
def dual (valuation : Valuation Judgment) : Valuation Judgment :=
  ⟨{judgment | judgment ∉ valuation.fails}, {judgment | judgment ∉ valuation.holds}⟩

/-- A valuation is consistent exactly when it lies below its dual. -/
theorem consistent_iff_le_dual (valuation : Valuation Judgment) :
    valuation.Consistent ↔ valuation.Le valuation.dual :=
  ⟨fun consistent => ⟨fun judgment held => consistent judgment held,
      fun judgment failed held => consistent judgment held failed⟩,
    fun le _ held failed => le.1 held failed⟩

end Valuation

/-- A system of self-referential judgments over three-valued base facts. -/
structure System (Judgment : Type u) (Base : Type v) where
  spec : Judgment → Formula Judgment Base
  baseHolds : Base → Prop
  baseFails : Base → Prop
  base_consistent : ∀ fact, baseHolds fact → ¬ baseFails fact

namespace System

variable {Judgment : Type u} {Base : Type v}

/-- Strong Kleene evaluation, as the pair (holds, fails). -/
def eval (system : System Judgment Base) (valuation : Valuation Judgment) :
    Formula Judgment Base → Prop × Prop
  | .base fact => (system.baseHolds fact, system.baseFails fact)
  | .truth judgment => (judgment ∈ valuation.holds, judgment ∈ valuation.fails)
  | .neg formula => ((eval system valuation formula).2, (eval system valuation formula).1)
  | .conj first second =>
      ((eval system valuation first).1 ∧ (eval system valuation second).1,
        (eval system valuation first).2 ∨ (eval system valuation second).2)
  | .disj first second =>
      ((eval system valuation first).1 ∨ (eval system valuation second).1,
        (eval system valuation first).2 ∧ (eval system valuation second).2)

/-- Evaluation is monotone in the knowledge order. -/
theorem eval_mono (system : System Judgment Base) {first second : Valuation Judgment}
    (le : first.Le second) :
    ∀ formula : Formula Judgment Base,
      ((system.eval first formula).1 → (system.eval second formula).1) ∧
        ((system.eval first formula).2 → (system.eval second formula).2)
  | .base _ => ⟨id, id⟩
  | .truth _ => ⟨fun held => le.1 held, fun failed => le.2 failed⟩
  | .neg formula =>
      let ih := eval_mono system le formula
      ⟨ih.2, ih.1⟩
  | .conj first second =>
      let ihFirst := eval_mono system le first
      let ihSecond := eval_mono system le second
      ⟨fun held => ⟨ihFirst.1 held.1, ihSecond.1 held.2⟩,
        fun failed => failed.elim (fun f => Or.inl (ihFirst.2 f)) (fun f => Or.inr (ihSecond.2 f))⟩
  | .disj first second =>
      let ihFirst := eval_mono system le first
      let ihSecond := eval_mono system le second
      ⟨fun held => held.elim (fun h => Or.inl (ihFirst.1 h)) (fun h => Or.inr (ihSecond.1 h)),
        fun failed => ⟨ihFirst.2 failed.1, ihSecond.2 failed.2⟩⟩

/-- **Duality of evaluation**: what holds in the dual does not fail in the
valuation, and what fails in the dual does not hold in it. -/
theorem eval_dual (system : System Judgment Base) (valuation : Valuation Judgment) :
    ∀ formula : Formula Judgment Base,
      ((system.eval valuation.dual formula).1 → ¬ (system.eval valuation formula).2) ∧
        ((system.eval valuation.dual formula).2 → ¬ (system.eval valuation formula).1)
  | .base fact =>
      ⟨fun held failed => system.base_consistent fact held failed,
        fun failed held => system.base_consistent fact held failed⟩
  | .truth _ => ⟨fun held => held, fun failed => failed⟩
  | .neg formula =>
      let ih := eval_dual system valuation formula
      ⟨ih.2, ih.1⟩
  | .conj first second =>
      let ihFirst := eval_dual system valuation first
      let ihSecond := eval_dual system valuation second
      ⟨fun held failed => failed.elim (ihFirst.1 held.1) (ihSecond.1 held.2),
        fun failed held => failed.elim (fun f => ihFirst.2 f held.1)
          (fun f => ihSecond.2 f held.2)⟩
  | .disj first second =>
      let ihFirst := eval_dual system valuation first
      let ihSecond := eval_dual system valuation second
      ⟨fun held failed => held.elim (fun h => ihFirst.1 h failed.1)
          (fun h => ihSecond.1 h failed.2),
        fun failed held => held.elim (ihFirst.2 failed.1) (ihSecond.2 failed.2)⟩

variable (system : System Judgment Base)

/-- **The jump**: evaluate every specification. -/
def jump (valuation : Valuation Judgment) : Valuation Judgment :=
  ⟨{judgment | (system.eval valuation (system.spec judgment)).1},
    {judgment | (system.eval valuation (system.spec judgment)).2}⟩

theorem jump_mono {first second : Valuation Judgment} (le : first.Le second) :
    (system.jump first).Le (system.jump second) :=
  ⟨fun judgment held => (system.eval_mono le (system.spec judgment)).1 held,
    fun judgment failed => (system.eval_mono le (system.spec judgment)).2 failed⟩

/-- A valuation is sound when everything it determines is confirmed by the
jump. -/
def Sound (valuation : Valuation Judgment) : Prop :=
  valuation.Le (system.jump valuation)

/-- **The dual of a sound valuation is a pre-fixed point.** -/
theorem jump_dual_le {valuation : Valuation Judgment} (sound : system.Sound valuation) :
    (system.jump valuation.dual).Le valuation.dual :=
  ⟨fun judgment held failed =>
      (system.eval_dual valuation (system.spec judgment)).1 held (sound.2 failed),
    fun judgment failed held =>
      (system.eval_dual valuation (system.spec judgment)).2 failed (sound.1 held)⟩

/-! ## The least fixed point -/

/-- **The least fixed point**: what every pre-fixed valuation holds, and what
every pre-fixed valuation fails. -/
def least : Valuation Judgment :=
  ⟨{judgment | ∀ valuation : Valuation Judgment, (system.jump valuation).Le valuation →
      judgment ∈ valuation.holds},
    {judgment | ∀ valuation : Valuation Judgment, (system.jump valuation).Le valuation →
      judgment ∈ valuation.fails}⟩

/-- The least fixed point lies below every pre-fixed valuation. -/
theorem least_le {valuation : Valuation Judgment} (pre : (system.jump valuation).Le valuation) :
    system.least.Le valuation :=
  ⟨fun _ held => held valuation pre, fun _ failed => failed valuation pre⟩

theorem jump_least_le : (system.jump system.least).Le system.least :=
  ⟨fun _ held _ pre => pre.1 ((system.jump_mono (system.least_le pre)).1 held),
    fun _ failed _ pre => pre.2 ((system.jump_mono (system.least_le pre)).2 failed)⟩

theorem le_jump_least : system.least.Le (system.jump system.least) :=
  system.least_le (system.jump_mono system.jump_least_le)

/-- The least fixed point is sound. -/
theorem least_sound : system.Sound system.least := system.le_jump_least

/-- **Consistency of the least fixed point**, from duality. -/
theorem least_consistent : system.least.Consistent :=
  (Valuation.consistent_iff_le_dual _).mpr
    (system.least_le (system.jump_dual_le system.least_sound))

/-! ## The diagonal and the truth-teller -/

/-- **The diagonal stays undetermined**: a judgment whose specification negates
its own truth is neither held nor failed by any sound, consistent valuation. -/
theorem liar_undetermined {liar : Judgment} (isLiar : system.spec liar = .neg (.truth liar))
    {valuation : Valuation Judgment} (sound : system.Sound valuation)
    (consistent : valuation.Consistent) :
    liar ∉ valuation.holds ∧ liar ∉ valuation.fails := by
  constructor
  · intro held
    have jumped := sound.1 held
    change (system.eval valuation (system.spec liar)).1 at jumped
    rw [isLiar] at jumped
    exact consistent liar held jumped
  · intro failed
    have jumped := sound.2 failed
    change (system.eval valuation (system.spec liar)).2 at jumped
    rw [isLiar] at jumped
    exact consistent liar jumped failed

theorem liar_not_mem_least {liar : Judgment} (isLiar : system.spec liar = .neg (.truth liar)) :
    liar ∉ system.least.holds ∧ liar ∉ system.least.fails :=
  system.liar_undetermined isLiar system.least_sound system.least_consistent

/-- **A truth-teller is ungrounded**: undetermined in the least fixed point. -/
theorem truthTeller_not_mem_least {teller : Judgment}
    (isTeller : system.spec teller = .truth teller) :
    teller ∉ system.least.holds ∧ teller ∉ system.least.fails := by
  let removed : Valuation Judgment :=
    ⟨{judgment | judgment ∈ system.least.holds ∧ judgment ≠ teller},
      {judgment | judgment ∈ system.least.fails ∧ judgment ≠ teller}⟩
  have below : removed.Le system.least := ⟨fun _ held => held.1, fun _ failed => failed.1⟩
  have pre : (system.jump removed).Le removed := by
    constructor
    · intro judgment held
      refine ⟨system.jump_least_le.1 ((system.jump_mono below).1 held), ?_⟩
      rintro rfl
      change (system.eval removed (system.spec judgment)).1 at held
      rw [isTeller] at held
      exact held.2 rfl
    · intro judgment failed
      refine ⟨system.jump_least_le.2 ((system.jump_mono below).2 failed), ?_⟩
      rintro rfl
      change (system.eval removed (system.spec judgment)).2 at failed
      rw [isTeller] at failed
      exact failed.2 rfl
  have le := system.least_le pre
  exact ⟨fun held => (le.1 held).2 rfl, fun failed => (le.2 failed).2 rfl⟩

/-! ## Two values: Tarski, and the Kleene escape -/

/-- Two-valued evaluation, given Boolean truth values of base facts. -/
def evalBool (baseValue : Base → Bool) (valuation : Judgment → Bool) :
    Formula Judgment Base → Bool
  | .base fact => baseValue fact
  | .truth judgment => valuation judgment
  | .neg formula => !(evalBool baseValue valuation formula)
  | .conj first second => evalBool baseValue valuation first && evalBool baseValue valuation second
  | .disj first second => evalBool baseValue valuation first || evalBool baseValue valuation second

/-- **Tarski's undefinability**: with a liar, no two-valued valuation satisfies
every specification, because Boolean negation has no fixed point. -/
theorem no_two_valued_fixedPoint {liar : Judgment} (isLiar : system.spec liar = .neg (.truth liar))
    (baseValue : Base → Bool) :
    ¬ ∃ valuation : Judgment → Bool,
      ∀ judgment, valuation judgment = evalBool baseValue valuation (system.spec judgment) := by
  rintro ⟨valuation, fixed⟩
  have atLiar := fixed liar
  rw [isLiar] at atLiar
  exact Mettapedia.Logic.Diagonal.bool_not_fixedPointFree (valuation liar) atLiar.symm

end System

/-- Strong Kleene negation on statuses. -/
def kleeneNot : Option Bool → Option Bool
  | some value => some (!value)
  | none => none

/-- **Strong Kleene negation has a fixed point**, the undetermined status. -/
theorem kleeneNot_none : kleeneNot none = none := rfl

/-- It is the only one. -/
theorem kleeneNot_fixed_iff (status : Option Bool) : kleeneNot status = status ↔ status = none := by
  cases status with
  | none => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | some value => cases value <;> simp [kleeneNot]

/-- The status of a judgment in a valuation. -/
def status {Judgment : Type u} (valuation : Valuation Judgment)
    [DecidablePred (· ∈ valuation.holds)]
    [DecidablePred (· ∈ valuation.fails)] (judgment : Judgment) : Option Bool :=
  if judgment ∈ valuation.holds then some true
  else if judgment ∈ valuation.fails then some false else none

/-- The liar's status in a sound consistent valuation is the Kleene fixed point
`none`. -/
theorem liar_status_eq_none {Judgment : Type u} {Base : Type v} (system : System Judgment Base)
    {liar : Judgment} (isLiar : system.spec liar = .neg (.truth liar))
    {valuation : Valuation Judgment} [DecidablePred (· ∈ valuation.holds)]
    [DecidablePred (· ∈ valuation.fails)] (sound : system.Sound valuation)
    (consistent : valuation.Consistent) : status valuation liar = none := by
  obtain ⟨notHeld, notFailed⟩ := system.liar_undetermined isLiar sound consistent
  simp [status, notHeld, notFailed]

/-! ## Verdicts as outcomes -/

section Outcomes

variable {Established : Sort u} {Refuted : Sort v} {Boundary : Type u} {Incomplete : Type v}

/-- **The knowledge order on outcomes**: every decided answer is kept. -/
def KnowledgeLE {Established' Refuted' : Sort*} {Boundary' Incomplete' : Type*}
    (first : Outcome Established Refuted Boundary Incomplete)
    (second : Outcome Established' Refuted' Boundary' Incomplete') : Prop :=
  ∀ answer, first.asBool = some answer → second.asBool = some answer

/-- Refinement by a stronger authority is a knowledge increase. -/
theorem knowledgeLE_of_authorityRefines
    {first second : Outcome Established Refuted Boundary Incomplete}
    (refines : Outcome.AuthorityRefines first second) : KnowledgeLE first second := by
  intro answer decided
  cases refines <;> simp_all [Outcome.asBool]

end Outcomes

namespace System

variable {Judgment : Type u} {Base : Type v} (system : System Judgment Base)

/-- **The authority of grounded truth**: a judgment holds when the least fixed
point holds it; evidence is membership in the held set, obstruction membership
in the failed set, sound by consistency. -/
def groundedAuthority : Authority.{u, 0, 0} Judgment where
  Holds judgment := judgment ∈ system.least.holds
  Evidence judgment := judgment ∈ system.least.holds
  Obstruction judgment := judgment ∈ system.least.fails
  evidenceSound _ held := held
  obstructionSound judgment failed held := system.least_consistent judgment held failed

/-- The verdict of a valuation on a judgment.  Membership in a valuation is
not decidable in general, so the case split is classical. -/
noncomputable def verdict (valuation : Valuation Judgment) (judgment : Judgment) :
    Outcome (judgment ∈ valuation.holds) (judgment ∈ valuation.fails) Unit Empty := by
  classical
  exact if held : judgment ∈ valuation.holds then .established held
    else if failed : judgment ∈ valuation.fails then .refuted failed
    else .outsideFragment ()

/-- The least fixed point's verdict is an authorised outcome of grounded
truth. -/
noncomputable def groundedVerdict (judgment : Judgment) :
    AuthorizedOutcome system.groundedAuthority Unit Empty judgment :=
  verdict system.least judgment

theorem verdict_asBool_eq_some_true {valuation : Valuation Judgment} {judgment : Judgment} :
    (verdict valuation judgment).asBool = some true ↔ judgment ∈ valuation.holds := by
  unfold verdict
  by_cases held : judgment ∈ valuation.holds
  · simp [held, Outcome.asBool]
  · by_cases failed : judgment ∈ valuation.fails
    · simp [held, failed, Outcome.asBool]
    · simp [held, failed, Outcome.asBool]

theorem verdict_asBool_eq_some_false {valuation : Valuation Judgment} {judgment : Judgment}
    (consistent : valuation.Consistent) :
    (verdict valuation judgment).asBool = some false ↔ judgment ∈ valuation.fails := by
  unfold verdict
  by_cases held : judgment ∈ valuation.holds
  · simp [held, Outcome.asBool, consistent judgment held]
  · by_cases failed : judgment ∈ valuation.fails
    · simp [held, failed, Outcome.asBool]
    · simp [held, failed, Outcome.asBool]

/-- **The least fixed point is knowledge-below every consistent pre-fixed
valuation**, verdict by verdict. -/
theorem verdict_least_knowledgeLE {valuation : Valuation Judgment}
    (pre : (system.jump valuation).Le valuation) (consistent : valuation.Consistent)
    (judgment : Judgment) :
    KnowledgeLE (verdict system.least judgment) (verdict valuation judgment) := by
  intro answer decided
  cases answer with
  | true =>
      exact verdict_asBool_eq_some_true.mpr ((system.least_le pre).1
        (verdict_asBool_eq_some_true.mp decided))
  | false =>
      exact (verdict_asBool_eq_some_false consistent).mpr ((system.least_le pre).2
        ((verdict_asBool_eq_some_false system.least_consistent).mp decided))

/-- **The diagonal's verdict is `outsideFragment`.** -/
theorem verdict_liar_outside {liar : Judgment} (isLiar : system.spec liar = .neg (.truth liar)) :
    verdict system.least liar = .outsideFragment () := by
  obtain ⟨notHeld, notFailed⟩ := system.liar_not_mem_least isLiar
  unfold verdict
  simp [notHeld, notFailed]

end System

/-! ## The greatest fixed point: the dual of the least

With bivalent base facts the jump commutes with the dual valuation.  The dual of the
least fixed point is then the greatest fixed point, every judgment is held or failed
there, and a judgment left undetermined by the least fixed point is both held and
failed by the greatest.  The two non-classical values of Belnap's square, neither and
both, are the two readings of one ungrounded judgment, exchanged by the dual. -/

namespace Valuation

variable {Judgment : Type u}

theorem ext' {first second : Valuation Judgment} (holds : first.holds = second.holds)
    (fails : first.fails = second.fails) : first = second := by
  cases first
  cases second
  simp_all

theorem le_antisymm {first second : Valuation Judgment} (le : first.Le second)
    (ge : second.Le first) : first = second :=
  ext' (Set.Subset.antisymm le.1 ge.1) (Set.Subset.antisymm le.2 ge.2)

/-- The dual is an involution. -/
theorem dual_dual (valuation : Valuation Judgment) : valuation.dual.dual = valuation := by
  apply ext' <;> ext judgment <;> simp [dual]

/-- The dual reverses the knowledge order. -/
theorem dual_le_dual {first second : Valuation Judgment} (le : first.Le second) :
    second.dual.Le first.dual :=
  ⟨fun _ notFailed failed => notFailed (le.2 failed), fun _ notHeld held => notHeld (le.1 held)⟩

end Valuation

namespace System

variable {Judgment : Type u} {Base : Type v} (system : System Judgment Base)

/-- Every base fact holds or fails. -/
def Bivalent : Prop :=
  ∀ fact, system.baseHolds fact ∨ system.baseFails fact

variable {system}

/-- With bivalent base facts, evaluating in the dual valuation is the dual of
evaluating in the valuation. -/
theorem eval_dual_iff (bivalent : system.Bivalent) (valuation : Valuation Judgment) :
    ∀ formula : Formula Judgment Base,
      ((system.eval valuation.dual formula).1 ↔ ¬ (system.eval valuation formula).2) ∧
        ((system.eval valuation.dual formula).2 ↔ ¬ (system.eval valuation formula).1)
  | .base fact =>
      ⟨⟨fun held failed => system.base_consistent fact held failed,
          fun notFailed => (bivalent fact).resolve_right notFailed⟩,
        ⟨fun failed held => system.base_consistent fact held failed,
          fun notHeld => (bivalent fact).resolve_left notHeld⟩⟩
  | .truth _ => ⟨Iff.rfl, Iff.rfl⟩
  | .neg formula =>
      let ih := eval_dual_iff bivalent valuation formula
      ⟨ih.2, ih.1⟩
  | .conj first second => by
      have ihFirst := eval_dual_iff bivalent valuation first
      have ihSecond := eval_dual_iff bivalent valuation second
      change ((system.eval valuation.dual first).1 ∧ (system.eval valuation.dual second).1 ↔
          ¬ ((system.eval valuation first).2 ∨ (system.eval valuation second).2)) ∧
        ((system.eval valuation.dual first).2 ∨ (system.eval valuation.dual second).2 ↔
          ¬ ((system.eval valuation first).1 ∧ (system.eval valuation second).1))
      rw [ihFirst.1, ihFirst.2, ihSecond.1, ihSecond.2, not_or, not_and_or]
      exact ⟨Iff.rfl, Iff.rfl⟩
  | .disj first second => by
      have ihFirst := eval_dual_iff bivalent valuation first
      have ihSecond := eval_dual_iff bivalent valuation second
      change ((system.eval valuation.dual first).1 ∨ (system.eval valuation.dual second).1 ↔
          ¬ ((system.eval valuation first).2 ∧ (system.eval valuation second).2)) ∧
        ((system.eval valuation.dual first).2 ∧ (system.eval valuation.dual second).2 ↔
          ¬ ((system.eval valuation first).1 ∨ (system.eval valuation second).1))
      rw [ihFirst.1, ihFirst.2, ihSecond.1, ihSecond.2, not_or, not_and_or]
      exact ⟨Iff.rfl, Iff.rfl⟩

/-- **The jump commutes with the dual** when base facts are bivalent. -/
theorem jump_dual (bivalent : system.Bivalent) (valuation : Valuation Judgment) :
    system.jump valuation.dual = (system.jump valuation).dual := by
  apply Valuation.ext' <;> ext judgment
  · exact (eval_dual_iff bivalent valuation (system.spec judgment)).1
  · exact (eval_dual_iff bivalent valuation (system.spec judgment)).2

variable (system)

/-- The least fixed point is a fixed point. -/
theorem jump_least : system.jump system.least = system.least :=
  Valuation.le_antisymm system.jump_least_le system.le_jump_least

/-- **The greatest fixed point**: the dual of the least. -/
def greatest : Valuation Judgment := system.least.dual

variable {system}

theorem jump_greatest (bivalent : system.Bivalent) :
    system.jump system.greatest = system.greatest := by
  rw [greatest, jump_dual bivalent, jump_least]

/-- **Every sound valuation lies below the dual of the least**, in particular every
fixed point.  No bivalence is needed: the dual of a sound valuation is a pre-fixed
point (`jump_dual_le`), so it lies above the least fixed point. -/
theorem le_greatest {valuation : Valuation Judgment} (sound : system.Sound valuation) :
    valuation.Le system.greatest := by
  have below : system.least.Le valuation.dual := system.least_le (system.jump_dual_le sound)
  have reversed := Valuation.dual_le_dual below
  rwa [Valuation.dual_dual] at reversed

/-- With bivalent base facts the greatest fixed point is sound. -/
theorem greatest_sound (bivalent : system.Bivalent) : system.Sound system.greatest := by
  unfold Sound
  rw [jump_greatest bivalent]
  exact Valuation.le_refl _

/-- Every judgment is held or failed by the greatest fixed point. -/
theorem greatest_complete (judgment : Judgment) :
    judgment ∈ system.greatest.holds ∨ judgment ∈ system.greatest.fails := by
  by_cases failed : judgment ∈ system.least.fails
  · exact Or.inr fun held => system.least_consistent judgment held failed
  · exact Or.inl failed

/-- **Neither in the least exactly when both in the greatest.** -/
theorem undetermined_least_iff_both_greatest (judgment : Judgment) :
    (judgment ∉ system.least.holds ∧ judgment ∉ system.least.fails) ↔
      (judgment ∈ system.greatest.holds ∧ judgment ∈ system.greatest.fails) :=
  ⟨fun ⟨notHeld, notFailed⟩ => ⟨notFailed, notHeld⟩,
    fun ⟨notFailed, notHeld⟩ => ⟨notHeld, notFailed⟩⟩

/-- **The liar is both held and failed by the greatest fixed point.** -/
theorem liar_both_greatest {liar : Judgment} (isLiar : system.spec liar = .neg (.truth liar)) :
    liar ∈ system.greatest.holds ∧ liar ∈ system.greatest.fails :=
  (undetermined_least_iff_both_greatest liar).mp (system.liar_not_mem_least isLiar)

end System

/-! ## Three readings of grounded truth: stages, evidence and the fixed point

The least fixed point is read in three ways, and the three readings agree on every
verdict.

* **By stages.** The stages of the jump from the empty valuation increase
  (`stage_mono`) and stay below the least fixed point (`stage_le_least`); a judgment is
  held or failed by the least fixed point exactly when some stage holds or fails it
  (`mem_least_iff_exists_stage`).
* **By evidence.** `Evidence` is the inductive family of well-founded derivations:
  base facts at the leaves, a truth node unfolding a judgment into its specification,
  and one node for each strong Kleene clause.  Evidence is sound (`Evidence.takes_least`)
  and complete (`exists_evidence`), so a judgment is held exactly when its specification
  has evidence (`mem_least_iff_evidence`).  The height of an evidence tree counts truth
  nodes along its longest branch, and a judgment is decided at stage `n + 1` exactly
  when its specification has evidence of height at most `n`
  (`mem_stage_succ_iff_evidence`).
* **By the fixed point** itself.

Each comparison forgets in one direction: two different evidence trees can give one
verdict (`Controls.twoEvidence_ne`).

**Circular justification.** A sound valuation justifies each of its verdicts by its own
verdicts, possibly in a circle.  Every sound valuation lies below the greatest fixed
point (`le_greatest`), so with bivalent base facts a judgment is held or failed by the
greatest fixed point exactly when some circular justification holds or fails it
(`mem_greatest_iff_sound`).  The liar justifies both verdicts by itself
(`liar_selfJustifying`) and has well-founded evidence for neither (`liar_noEvidence`):
a derivation of a verdict on a loop through truth and negation alone would descend
forever (`noEvidence_of_closed`).  Grounded truth is well-founded evidence; the greatest
fixed point is circular justification.
-/

namespace Valuation

variable {Judgment : Type u}

/-- Membership by polarity: `true` reads the held set, `false` the failed set. -/
def Mem (valuation : Valuation Judgment) (judgment : Judgment) : Bool → Prop
  | true => judgment ∈ valuation.holds
  | false => judgment ∈ valuation.fails

theorem Le.mem {first second : Valuation Judgment} (le : first.Le second)
    {judgment : Judgment} : ∀ {polarity : Bool},
      first.Mem judgment polarity → second.Mem judgment polarity
  | true, held => le.1 held
  | false, failed => le.2 failed

/-- The empty valuation, which determines nothing. -/
def bottom : Valuation Judgment := ⟨∅, ∅⟩

theorem bottom_le (valuation : Valuation Judgment) : bottom.Le valuation :=
  ⟨fun _ member => absurd member (Set.notMem_empty _),
    fun _ member => absurd member (Set.notMem_empty _)⟩

/-- A consistent valuation never holds and fails a judgment at once. -/
theorem Consistent.not_mem_both {valuation : Valuation Judgment}
    (consistent : valuation.Consistent) (judgment : Judgment) :
    ¬ (valuation.Mem judgment true ∧ valuation.Mem judgment false) :=
  fun ⟨held, failed⟩ => consistent judgment held failed

end Valuation

namespace System

variable {Judgment : Type u} {Base : Type v} (system : System Judgment Base)

/-- A formula takes a polarity in a valuation: `true` when it holds, `false` when it
fails. -/
def Takes (valuation : Valuation Judgment) (formula : Formula Judgment Base) : Bool → Prop
  | true => (system.eval valuation formula).1
  | false => (system.eval valuation formula).2

variable {system}

theorem takes_truth {valuation : Valuation Judgment} {judgment : Judgment} :
    ∀ {polarity : Bool},
      system.Takes valuation (.truth judgment) polarity ↔ valuation.Mem judgment polarity
  | true => Iff.rfl
  | false => Iff.rfl

theorem takes_neg {valuation : Valuation Judgment} {formula : Formula Judgment Base} :
    ∀ {polarity : Bool},
      system.Takes valuation (.neg formula) polarity ↔ system.Takes valuation formula (!polarity)
  | true => Iff.rfl
  | false => Iff.rfl

theorem mem_jump {valuation : Valuation Judgment} {judgment : Judgment} :
    ∀ {polarity : Bool},
      (system.jump valuation).Mem judgment polarity ↔
        system.Takes valuation (system.spec judgment) polarity
  | true => Iff.rfl
  | false => Iff.rfl

theorem takes_mono {first second : Valuation Judgment} (le : first.Le second)
    {formula : Formula Judgment Base} : ∀ {polarity : Bool},
      system.Takes first formula polarity → system.Takes second formula polarity
  | true => (system.eval_mono le formula).1
  | false => (system.eval_mono le formula).2

variable (system)

/-- The least fixed point holds a judgment exactly when it holds its specification. -/
theorem mem_least_iff {judgment : Judgment} {polarity : Bool} :
    system.least.Mem judgment polarity ↔
      system.Takes system.least (system.spec judgment) polarity := by
  rw [← mem_jump, system.jump_least]

/-! ### Stages -/

/-- **The stages of the jump** from the empty valuation. -/
def stage : ℕ → Valuation Judgment
  | 0 => Valuation.bottom
  | n + 1 => system.jump (stage n)

theorem stage_le_least : ∀ n, (system.stage n).Le system.least
  | 0 => Valuation.bottom_le _
  | n + 1 => Valuation.le_trans (system.jump_mono (stage_le_least n)) system.jump_least_le

theorem stage_le_succ : ∀ n, (system.stage n).Le (system.stage (n + 1))
  | 0 => Valuation.bottom_le _
  | n + 1 => system.jump_mono (stage_le_succ n)

theorem stage_mono {m n : ℕ} (le : m ≤ n) : (system.stage m).Le (system.stage n) := by
  induction n, le using Nat.le_induction with
  | base => exact Valuation.le_refl _
  | succ n _ ih => exact Valuation.le_trans ih (system.stage_le_succ n)

/-! ### Evidence -/

/-- **Evidence** that a formula takes a polarity: a well-founded derivation whose leaves
are base facts, whose truth nodes unfold a judgment into its specification, and whose
other nodes are the strong Kleene clauses. -/
inductive Evidence : Formula Judgment Base → Bool → Type (max u v)
  | baseHolds {fact : Base} (holds : system.baseHolds fact) : Evidence (.base fact) true
  | baseFails {fact : Base} (fails : system.baseFails fact) : Evidence (.base fact) false
  | truth {judgment : Judgment} {polarity : Bool}
      (body : Evidence (system.spec judgment) polarity) : Evidence (.truth judgment) polarity
  | neg {formula : Formula Judgment Base} {polarity : Bool}
      (body : Evidence formula (!polarity)) : Evidence (.neg formula) polarity
  | conjHolds {first second : Formula Judgment Base}
      (left : Evidence first true) (right : Evidence second true) :
      Evidence (.conj first second) true
  | conjFailsLeft {first second : Formula Judgment Base} (left : Evidence first false) :
      Evidence (.conj first second) false
  | conjFailsRight {first second : Formula Judgment Base} (right : Evidence second false) :
      Evidence (.conj first second) false
  | disjHoldsLeft {first second : Formula Judgment Base} (left : Evidence first true) :
      Evidence (.disj first second) true
  | disjHoldsRight {first second : Formula Judgment Base} (right : Evidence second true) :
      Evidence (.disj first second) true
  | disjFails {first second : Formula Judgment Base}
      (left : Evidence first false) (right : Evidence second false) :
      Evidence (.disj first second) false

variable {system}

/-- The height of an evidence tree: the number of truth nodes on its longest branch. -/
def Evidence.height : {formula : Formula Judgment Base} → {polarity : Bool} →
    system.Evidence formula polarity → ℕ
  | _, _, .baseHolds _ => 0
  | _, _, .baseFails _ => 0
  | _, _, .truth body => body.height + 1
  | _, _, .neg body => body.height
  | _, _, .conjHolds left right => max left.height right.height
  | _, _, .conjFailsLeft left => left.height
  | _, _, .conjFailsRight right => right.height
  | _, _, .disjHoldsLeft left => left.height
  | _, _, .disjHoldsRight right => right.height
  | _, _, .disjFails left right => max left.height right.height

/-- **Evidence of height `n` is decided at stage `n`.** -/
theorem Evidence.takes_stage : {formula : Formula Judgment Base} → {polarity : Bool} →
    (evidence : system.Evidence formula polarity) →
      system.Takes (system.stage evidence.height) formula polarity
  | _, _, .baseHolds holds => holds
  | _, _, .baseFails fails => fails
  | _, _, .truth body => takes_truth.mpr (mem_jump.mpr body.takes_stage)
  | _, _, .neg body => takes_neg.mpr body.takes_stage
  | _, _, .conjHolds left right =>
      ⟨takes_mono (system.stage_mono (le_max_left _ _)) left.takes_stage,
        takes_mono (system.stage_mono (le_max_right _ _)) right.takes_stage⟩
  | _, _, .conjFailsLeft left => Or.inl left.takes_stage
  | _, _, .conjFailsRight right => Or.inr right.takes_stage
  | _, _, .disjHoldsLeft left => Or.inl left.takes_stage
  | _, _, .disjHoldsRight right => Or.inr right.takes_stage
  | _, _, .disjFails left right =>
      ⟨takes_mono (system.stage_mono (le_max_left _ _)) left.takes_stage,
        takes_mono (system.stage_mono (le_max_right _ _)) right.takes_stage⟩

/-- **Soundness of evidence**: evidence for a polarity is confirmed by the least fixed
point. -/
theorem Evidence.takes_least {formula : Formula Judgment Base} {polarity : Bool}
    (evidence : system.Evidence formula polarity) :
    system.Takes system.least formula polarity :=
  takes_mono (system.stage_le_least _) evidence.takes_stage

variable (system)

/-- **Completeness by stages**: whatever a stage decides has evidence of height at most
the stage. -/
theorem exists_evidence_of_takes_stage : ∀ (n : ℕ) (formula : Formula Judgment Base)
    (polarity : Bool), system.Takes (system.stage n) formula polarity →
      ∃ evidence : system.Evidence formula polarity, evidence.height ≤ n
  | _, .base _, true, holds => ⟨.baseHolds holds, Nat.zero_le _⟩
  | _, .base _, false, fails => ⟨.baseFails fails, Nat.zero_le _⟩
  | 0, .truth _, true, member => nomatch member
  | 0, .truth _, false, member => nomatch member
  | n + 1, .truth judgment, true, member => by
      obtain ⟨body, height⟩ :=
        exists_evidence_of_takes_stage n (system.spec judgment) true member
      exact ⟨.truth body, Nat.succ_le_succ height⟩
  | n + 1, .truth judgment, false, member => by
      obtain ⟨body, height⟩ :=
        exists_evidence_of_takes_stage n (system.spec judgment) false member
      exact ⟨.truth body, Nat.succ_le_succ height⟩
  | n, .neg formula, true, takes => by
      obtain ⟨body, height⟩ := exists_evidence_of_takes_stage n formula false takes
      exact ⟨.neg body, height⟩
  | n, .neg formula, false, takes => by
      obtain ⟨body, height⟩ := exists_evidence_of_takes_stage n formula true takes
      exact ⟨.neg body, height⟩
  | n, .conj first second, true, ⟨left, right⟩ => by
      obtain ⟨leftEvidence, leftHeight⟩ := exists_evidence_of_takes_stage n first true left
      obtain ⟨rightEvidence, rightHeight⟩ :=
        exists_evidence_of_takes_stage n second true right
      exact ⟨.conjHolds leftEvidence rightEvidence, max_le leftHeight rightHeight⟩
  | n, .conj first second, false, takes => by
      rcases takes with left | right
      · obtain ⟨evidence, height⟩ := exists_evidence_of_takes_stage n first false left
        exact ⟨.conjFailsLeft evidence, height⟩
      · obtain ⟨evidence, height⟩ := exists_evidence_of_takes_stage n second false right
        exact ⟨.conjFailsRight evidence, height⟩
  | n, .disj first second, true, takes => by
      rcases takes with left | right
      · obtain ⟨evidence, height⟩ := exists_evidence_of_takes_stage n first true left
        exact ⟨.disjHoldsLeft evidence, height⟩
      · obtain ⟨evidence, height⟩ := exists_evidence_of_takes_stage n second true right
        exact ⟨.disjHoldsRight evidence, height⟩
  | n, .disj first second, false, ⟨left, right⟩ => by
      obtain ⟨leftEvidence, leftHeight⟩ := exists_evidence_of_takes_stage n first false left
      obtain ⟨rightEvidence, rightHeight⟩ :=
        exists_evidence_of_takes_stage n second false right
      exact ⟨.disjFails leftEvidence rightEvidence, max_le leftHeight rightHeight⟩

/-- **A judgment is decided at stage `n + 1` exactly when its specification has evidence
of height at most `n`.** -/
theorem mem_stage_succ_iff_evidence {n : ℕ} {judgment : Judgment} {polarity : Bool} :
    (system.stage (n + 1)).Mem judgment polarity ↔
      ∃ evidence : system.Evidence (system.spec judgment) polarity, evidence.height ≤ n :=
  ⟨fun member => system.exists_evidence_of_takes_stage n _ _ (mem_jump.mp member),
    fun ⟨evidence, height⟩ =>
      mem_jump.mpr (takes_mono (system.stage_mono height) evidence.takes_stage)⟩

/-- The valuation of the judgments whose specifications have evidence. -/
def evidenced : Valuation Judgment :=
  ⟨{judgment | Nonempty (system.Evidence (system.spec judgment) true)},
    {judgment | Nonempty (system.Evidence (system.spec judgment) false)}⟩

theorem evidence_of_takes_evidenced : ∀ (formula : Formula Judgment Base) (polarity : Bool),
    system.Takes system.evidenced formula polarity → Nonempty (system.Evidence formula polarity)
  | .base _, true, holds => ⟨.baseHolds holds⟩
  | .base _, false, fails => ⟨.baseFails fails⟩
  | .truth _, true, ⟨body⟩ => ⟨.truth body⟩
  | .truth _, false, ⟨body⟩ => ⟨.truth body⟩
  | .neg formula, true, takes =>
      let ⟨body⟩ := evidence_of_takes_evidenced formula false takes
      ⟨.neg body⟩
  | .neg formula, false, takes =>
      let ⟨body⟩ := evidence_of_takes_evidenced formula true takes
      ⟨.neg body⟩
  | .conj first second, true, ⟨left, right⟩ =>
      let ⟨leftEvidence⟩ := evidence_of_takes_evidenced first true left
      let ⟨rightEvidence⟩ := evidence_of_takes_evidenced second true right
      ⟨.conjHolds leftEvidence rightEvidence⟩
  | .conj first _, false, .inl left =>
      let ⟨evidence⟩ := evidence_of_takes_evidenced first false left
      ⟨.conjFailsLeft evidence⟩
  | .conj _ second, false, .inr right =>
      let ⟨evidence⟩ := evidence_of_takes_evidenced second false right
      ⟨.conjFailsRight evidence⟩
  | .disj first _, true, .inl left =>
      let ⟨evidence⟩ := evidence_of_takes_evidenced first true left
      ⟨.disjHoldsLeft evidence⟩
  | .disj _ second, true, .inr right =>
      let ⟨evidence⟩ := evidence_of_takes_evidenced second true right
      ⟨.disjHoldsRight evidence⟩
  | .disj first second, false, ⟨left, right⟩ =>
      let ⟨leftEvidence⟩ := evidence_of_takes_evidenced first false left
      let ⟨rightEvidence⟩ := evidence_of_takes_evidenced second false right
      ⟨.disjFails leftEvidence rightEvidence⟩

/-- The evidenced valuation is a pre-fixed point. -/
theorem jump_evidenced_le : (system.jump system.evidenced).Le system.evidenced :=
  ⟨fun judgment takes => system.evidence_of_takes_evidenced (system.spec judgment) true takes,
    fun judgment takes => system.evidence_of_takes_evidenced (system.spec judgment) false takes⟩

/-- **Completeness of evidence**: whatever the least fixed point confirms has evidence. -/
theorem exists_evidence {formula : Formula Judgment Base} {polarity : Bool}
    (takes : system.Takes system.least formula polarity) :
    Nonempty (system.Evidence formula polarity) :=
  system.evidence_of_takes_evidenced formula polarity
    (takes_mono (system.least_le system.jump_evidenced_le) takes)

/-- **Grounded truth is well-founded evidence.** -/
theorem takes_least_iff_evidence {formula : Formula Judgment Base} {polarity : Bool} :
    system.Takes system.least formula polarity ↔ Nonempty (system.Evidence formula polarity) :=
  ⟨system.exists_evidence, fun ⟨evidence⟩ => evidence.takes_least⟩

/-- **A judgment is held (failed) by the least fixed point exactly when its specification
has evidence of holding (failing).** -/
theorem mem_least_iff_evidence {judgment : Judgment} {polarity : Bool} :
    system.least.Mem judgment polarity ↔
      Nonempty (system.Evidence (system.spec judgment) polarity) :=
  system.mem_least_iff.trans system.takes_least_iff_evidence

/-- **The least fixed point is the union of the stages.** -/
theorem mem_least_iff_exists_stage {judgment : Judgment} {polarity : Bool} :
    system.least.Mem judgment polarity ↔ ∃ n, (system.stage n).Mem judgment polarity := by
  constructor
  · intro member
    obtain ⟨evidence⟩ := system.mem_least_iff_evidence.mp member
    exact ⟨evidence.height + 1, system.mem_stage_succ_iff_evidence.mpr ⟨evidence, le_refl _⟩⟩
  · rintro ⟨n, member⟩
    exact (system.stage_le_least n).mem member

/-! ### Finite systems: the stages reach the least fixed point -/

/-- A stage that the jump does not move is the least fixed point. -/
theorem stage_eq_least_of_fixed {n : ℕ} (fixed : system.stage (n + 1) = system.stage n) :
    system.stage n = system.least :=
  Valuation.le_antisymm (system.stage_le_least n)
    (system.least_le (by
      change (system.stage (n + 1)).Le (system.stage n)
      rw [fixed]
      exact Valuation.le_refl _))

/-- Once the stages stop moving they stay. -/
theorem stage_stable {n : ℕ} (fixed : system.stage (n + 1) = system.stage n) :
    ∀ m, n ≤ m → system.stage m = system.stage n := by
  intro m le
  induction m, le using Nat.le_induction with
  | base => rfl
  | succ m _ ih =>
      change system.jump (system.stage m) = system.stage n
      rw [ih]
      exact fixed

section Finite

variable [Finite Judgment]

/-- The number of verdicts a valuation gives. -/
noncomputable def verdictCount (valuation : Valuation Judgment) : ℕ :=
  valuation.holds.ncard + valuation.fails.ncard

omit [Finite Judgment] in
theorem verdictCount_le (valuation : Valuation Judgment) [Finite Judgment] :
    verdictCount valuation ≤ 2 * Nat.card Judgment := by
  unfold verdictCount
  have holds := Set.ncard_le_card valuation.holds
  have fails := Set.ncard_le_card valuation.fails
  omega

/-- A strict increase in the knowledge order adds a verdict. -/
theorem verdictCount_lt {first second : Valuation Judgment} (le : first.Le second)
    (different : first ≠ second) : verdictCount first < verdictCount second := by
  unfold verdictCount
  have holdsLe := Set.ncard_le_ncard le.1 (Set.toFinite _)
  have failsLe := Set.ncard_le_ncard le.2 (Set.toFinite _)
  by_cases sameHolds : first.holds = second.holds
  · have differentFails : first.fails ≠ second.fails :=
      fun sameFails => different (Valuation.ext' sameHolds sameFails)
    have := Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨le.2, differentFails⟩)
      (Set.toFinite _)
    omega
  · have := Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨le.1, sameHolds⟩)
      (Set.toFinite _)
    omega

theorem le_verdictCount_stage {n : ℕ}
    (moving : ∀ m < n, system.stage m ≠ system.stage (m + 1)) :
    n ≤ verdictCount (system.stage n) := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      have previous := ih (fun m lt => moving m (Nat.lt_succ_of_lt lt))
      have step := verdictCount_lt (system.stage_le_succ n) (moving n (Nat.lt_succ_self n))
      omega

/-- **Finite systems reach their grounded truth in finitely many jumps**: at most twice
the number of judgments. -/
theorem stage_eq_least :
    system.stage (2 * Nat.card Judgment) = system.least := by
  by_cases moving : ∀ m < 2 * Nat.card Judgment + 1, system.stage m ≠ system.stage (m + 1)
  · have := system.le_verdictCount_stage moving
    have := verdictCount_le (system.stage (2 * Nat.card Judgment + 1))
    omega
  · push Not at moving
    obtain ⟨m, lt, same⟩ := moving
    rw [system.stage_stable same.symm _ (Nat.le_of_lt_succ lt)]
    exact system.stage_eq_least_of_fixed same.symm

end Finite

/-! ### Deciding grounded truth -/

section Decide

variable [DecidablePred system.baseHolds] [DecidablePred system.baseFails]

/-- Strong Kleene evaluation over decided verdicts, as a pair of Booleans. -/
def evalDecide (verdict : Judgment → Bool × Bool) : Formula Judgment Base → Bool × Bool
  | .base fact => (decide (system.baseHolds fact), decide (system.baseFails fact))
  | .truth judgment => verdict judgment
  | .neg formula => ((evalDecide verdict formula).2, (evalDecide verdict formula).1)
  | .conj first second =>
      ((evalDecide verdict first).1 && (evalDecide verdict second).1,
        (evalDecide verdict first).2 || (evalDecide verdict second).2)
  | .disj first second =>
      ((evalDecide verdict first).1 || (evalDecide verdict second).1,
        (evalDecide verdict first).2 && (evalDecide verdict second).2)

/-- The stages of the jump, decided. -/
def stageDecide : ℕ → Judgment → Bool × Bool
  | 0 => fun _ => (false, false)
  | n + 1 => fun judgment => system.evalDecide (stageDecide n) (system.spec judgment)

/-- Decided verdicts that agree with a valuation. -/
def Decides (valuation : Valuation Judgment) (verdict : Judgment → Bool × Bool) : Prop :=
  ∀ judgment, ((verdict judgment).1 = true ↔ judgment ∈ valuation.holds) ∧
    ((verdict judgment).2 = true ↔ judgment ∈ valuation.fails)

theorem evalDecide_spec {valuation : Valuation Judgment} {verdict : Judgment → Bool × Bool}
    (decides : Decides valuation verdict) : ∀ formula : Formula Judgment Base,
      ((system.evalDecide verdict formula).1 = true ↔ (system.eval valuation formula).1) ∧
        ((system.evalDecide verdict formula).2 = true ↔ (system.eval valuation formula).2)
  | .base _ => ⟨decide_eq_true_iff, decide_eq_true_iff⟩
  | .truth judgment => decides judgment
  | .neg formula =>
      let ih := evalDecide_spec decides formula
      ⟨ih.2, ih.1⟩
  | .conj first second => by
      have ihFirst := evalDecide_spec decides first
      have ihSecond := evalDecide_spec decides second
      simp only [evalDecide, eval, Bool.and_eq_true, Bool.or_eq_true]
      exact ⟨and_congr ihFirst.1 ihSecond.1, or_congr ihFirst.2 ihSecond.2⟩
  | .disj first second => by
      have ihFirst := evalDecide_spec decides first
      have ihSecond := evalDecide_spec decides second
      simp only [evalDecide, eval, Bool.and_eq_true, Bool.or_eq_true]
      exact ⟨or_congr ihFirst.1 ihSecond.1, and_congr ihFirst.2 ihSecond.2⟩

/-- The decided stages agree with the stages. -/
theorem stageDecide_spec : ∀ n, Decides (system.stage n) (system.stageDecide n)
  | 0 => fun _ => ⟨⟨fun bad => (nomatch bad), fun member => absurd member (Set.notMem_empty _)⟩,
      ⟨fun bad => (nomatch bad), fun member => absurd member (Set.notMem_empty _)⟩⟩
  | n + 1 => fun judgment => system.evalDecide_spec (stageDecide_spec n) (system.spec judgment)

/-- **Grounded truth of a finite system, decided**: iterate the decided jump twice the
number of judgments times. -/
def groundedDecide [Fintype Judgment] : Judgment → Bool × Bool :=
  system.stageDecide (2 * Fintype.card Judgment)

/-- **The decision procedure is correct**: it returns exactly the verdicts of the least
fixed point. -/
theorem groundedDecide_spec [Fintype Judgment] : Decides system.least system.groundedDecide := by
  have reaches := system.stage_eq_least
  rw [Nat.card_eq_fintype_card] at reaches
  rw [← reaches]
  exact system.stageDecide_spec _

end Decide

/-! ### Loops through truth and negation have no evidence -/

/-- **No well-founded evidence on an ungrounded loop.**  If every formula of a set is a
truth node whose judgment's specification is in the set, or a negation of a formula in
the set, then no formula of the set has evidence: a derivation would descend forever. -/
theorem noEvidence_of_closed {loop : Set (Formula Judgment Base)}
    (closed : ∀ formula ∈ loop,
      (∃ judgment, formula = .truth judgment ∧ system.spec judgment ∈ loop) ∨
        (∃ body, formula = .neg body ∧ body ∈ loop)) :
    ∀ {formula : Formula Judgment Base} {polarity : Bool},
      formula ∈ loop → IsEmpty (system.Evidence formula polarity) := by
  intro formula polarity member
  refine ⟨fun evidence => ?_⟩
  induction evidence with
  | baseHolds _ =>
      rcases closed _ member with ⟨_, same, _⟩ | ⟨_, same, _⟩ <;> cases same
  | baseFails _ =>
      rcases closed _ member with ⟨_, same, _⟩ | ⟨_, same, _⟩ <;> cases same
  | truth _ ih =>
      rcases closed _ member with ⟨_, same, inLoop⟩ | ⟨_, same, _⟩
      · cases same
        exact ih inLoop
      · cases same
  | neg _ ih =>
      rcases closed _ member with ⟨_, same, _⟩ | ⟨_, same, inLoop⟩
      · cases same
      · cases same
        exact ih inLoop
  | conjHolds _ _ _ _ =>
      rcases closed _ member with ⟨_, same, _⟩ | ⟨_, same, _⟩ <;> cases same
  | conjFailsLeft _ _ =>
      rcases closed _ member with ⟨_, same, _⟩ | ⟨_, same, _⟩ <;> cases same
  | conjFailsRight _ _ =>
      rcases closed _ member with ⟨_, same, _⟩ | ⟨_, same, _⟩ <;> cases same
  | disjHoldsLeft _ _ =>
      rcases closed _ member with ⟨_, same, _⟩ | ⟨_, same, _⟩ <;> cases same
  | disjHoldsRight _ _ =>
      rcases closed _ member with ⟨_, same, _⟩ | ⟨_, same, _⟩ <;> cases same
  | disjFails _ _ _ _ =>
      rcases closed _ member with ⟨_, same, _⟩ | ⟨_, same, _⟩ <;> cases same

variable {system}

/-- **The liar has no well-founded evidence**, for either verdict.  This is read off the
evidence alone, without the fixed point. -/
theorem liar_noEvidence {liar : Judgment} (isLiar : system.spec liar = .neg (.truth liar))
    (polarity : Bool) : IsEmpty (system.Evidence (system.spec liar) polarity) := by
  refine system.noEvidence_of_closed (loop := {.neg (.truth liar), .truth liar}) ?_ ?_
  · intro formula member
    rcases member with rfl | rfl
    · exact Or.inr ⟨.truth liar, rfl, Or.inr rfl⟩
    · exact Or.inl ⟨liar, rfl, by rw [isLiar]; exact Or.inl rfl⟩
  · rw [isLiar]
    exact Or.inl rfl

/-- **The truth-teller has no well-founded evidence**, for either verdict. -/
theorem teller_noEvidence {teller : Judgment} (isTeller : system.spec teller = .truth teller)
    (polarity : Bool) : IsEmpty (system.Evidence (system.spec teller) polarity) := by
  refine system.noEvidence_of_closed (loop := {.truth teller}) ?_ ?_
  · intro formula member
    rcases member with rfl
    exact Or.inl ⟨teller, rfl, by rw [isTeller]; rfl⟩
  · rw [isTeller]
    rfl

/-! ### The gap is invisible from inside -/

variable (system) in
/-- **No formula defines a gap.**  No strong Kleene formula holds exactly at the
valuations that leave a given judgment undetermined: evaluation is monotone in the
knowledge order, and deciding the judgment only adds information. -/
theorem undetermined_not_definable (judgment : Judgment) :
    ¬ ∃ formula : Formula Judgment Base, ∀ valuation : Valuation Judgment,
      (system.eval valuation formula).1 ↔
        (judgment ∉ valuation.holds ∧ judgment ∉ valuation.fails) := by
  rintro ⟨formula, defines⟩
  have atBottom : (system.eval Valuation.bottom formula).1 :=
    (defines Valuation.bottom).mpr
      ⟨fun member => absurd member (Set.notMem_empty _),
        fun member => absurd member (Set.notMem_empty _)⟩
  have decided : (Valuation.bottom : Valuation Judgment).Le ⟨{judgment}, ∅⟩ :=
    Valuation.bottom_le _
  have atDecided := (system.eval_mono decided formula).1 atBottom
  exact ((defines ⟨{judgment}, ∅⟩).mp atDecided).1 rfl

/-- **Revenge.**  The least fixed point does not hold the liar, and it does not hold the
sentence that says so either: "the liar is not true" is the liar's own specification,
which holds only where the liar fails.  The fact that the liar is not true is stated one
level up. -/
theorem liar_revenge {liar : Judgment} (isLiar : system.spec liar = .neg (.truth liar)) :
    liar ∉ system.least.holds ∧ ¬ system.Takes system.least (.neg (.truth liar)) true :=
  ⟨(system.liar_not_mem_least isLiar).1, (system.liar_not_mem_least isLiar).2⟩

/-! ### Circular justification and the greatest fixed point -/

/-- **The greatest fixed point is circular justification**: with bivalent base facts, a
judgment is held (failed) by the greatest fixed point exactly when some sound valuation
holds (fails) it. -/
theorem mem_greatest_iff_sound (bivalent : system.Bivalent) {judgment : Judgment}
    {polarity : Bool} :
    system.greatest.Mem judgment polarity ↔
      ∃ valuation : Valuation Judgment, system.Sound valuation ∧ valuation.Mem judgment polarity :=
  ⟨fun member => ⟨system.greatest, greatest_sound bivalent, member⟩,
    fun ⟨_, sound, member⟩ => (le_greatest sound).mem member⟩

/-- **The liar justifies both verdicts by itself**: the valuation holding and failing the
liar and nothing else is sound. -/
theorem liar_selfJustifying {liar : Judgment} (isLiar : system.spec liar = .neg (.truth liar)) :
    system.Sound ⟨{liar}, {liar}⟩ := by
  constructor
  · intro judgment held
    rcases held with rfl
    change (system.eval _ (system.spec judgment)).1
    rw [isLiar]
    exact rfl
  · intro judgment failed
    rcases failed with rfl
    change (system.eval _ (system.spec judgment)).2
    rw [isLiar]
    exact rfl

/-- **The truth-teller justifies either verdict by itself**, consistently. -/
theorem teller_selfJustifying {teller : Judgment} (isTeller : system.spec teller = .truth teller) :
    system.Sound ⟨{teller}, ∅⟩ ∧ system.Sound ⟨∅, {teller}⟩ := by
  refine ⟨⟨fun judgment held => ?_, fun _ failed => absurd failed (Set.notMem_empty _)⟩,
    ⟨fun _ held => absurd held (Set.notMem_empty _), fun judgment failed => ?_⟩⟩
  · rcases held with rfl
    change (system.eval _ (system.spec judgment)).1
    rw [isTeller]
    exact rfl
  · rcases failed with rfl
    change (system.eval _ (system.spec judgment)).2
    rw [isTeller]
    exact rfl

end System

/-! ## A concrete system -/

namespace Example

/-- Judgments: a grounded fact, its ascriptions, a liar, a truth-teller, and
strong Kleene compounds mixing them. -/
inductive Sentence where
  | fact
  | factTrue
  | factTrueTrue
  | liar
  | teller
  | liarOrFact
  | liarAndNotFact
  | liarOrNotFact
  deriving DecidableEq

instance : Fintype Sentence where
  elems := {.fact, .factTrue, .factTrueTrue, .liar, .teller, .liarOrFact, .liarAndNotFact,
    .liarOrNotFact}
  complete sentence := by cases sentence <;> simp

/-- The base: one true fact. -/
def system : System Sentence Unit where
  spec
    | .fact => .base ()
    | .factTrue => .truth .fact
    | .factTrueTrue => .truth .factTrue
    | .liar => .neg (.truth .liar)
    | .teller => .truth .teller
    | .liarOrFact => .disj (.truth .liar) (.truth .fact)
    | .liarAndNotFact => .conj (.truth .liar) (.neg (.truth .fact))
    | .liarOrNotFact => .disj (.truth .liar) (.neg (.truth .fact))
  baseHolds _ := True
  baseFails _ := False
  base_consistent _ _ failed := failed

/-- The grounded part: held and failed judgments of the least fixed point. -/
def groundedHolds : Set Sentence := {.fact, .factTrue, .factTrueTrue, .liarOrFact}

def groundedFails : Set Sentence := {.liarAndNotFact}

/-- The grounded valuation is a fixed point. -/
theorem grounded_fixed :
    (system.jump ⟨groundedHolds, groundedFails⟩).Le ⟨groundedHolds, groundedFails⟩ ∧
      system.Sound ⟨groundedHolds, groundedFails⟩ := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> intro sentence <;> cases sentence <;>
    simp [System.jump, System.eval, system, groundedHolds,
      groundedFails, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- A grounded judgment is established by the least fixed point: the base
fact, its iterated ascriptions, and a disjunction whose other disjunct is the
liar. -/
theorem fact_chain_held :
    Sentence.factTrueTrue ∈ system.least.holds ∧ Sentence.liarOrFact ∈ system.least.holds := by
  constructor
  · intro valuation pre
    have fact : Sentence.fact ∈ valuation.holds := pre.1 (by
      change (system.eval valuation (system.spec .fact)).1
      exact trivial)
    have factTrue : Sentence.factTrue ∈ valuation.holds := pre.1 fact
    exact pre.1 factTrue
  · intro valuation pre
    have fact : Sentence.fact ∈ valuation.holds := pre.1 (by
      change (system.eval valuation (system.spec .fact)).1
      exact trivial)
    exact pre.1 (Or.inr fact)

/-- A conjunction with a failed conjunct is refuted even though its other
conjunct is the liar. -/
theorem liarAndNotFact_failed : Sentence.liarAndNotFact ∈ system.least.fails := by
  intro valuation pre
  have fact : Sentence.fact ∈ valuation.holds := pre.1 (by
    change (system.eval valuation (system.spec .fact)).1
    exact trivial)
  exact pre.2 (Or.inr fact)

/-- The least fixed point is exactly the grounded valuation. -/
theorem least_eq_grounded :
    system.least.holds = groundedHolds ∧ system.least.fails = groundedFails := by
  have le := system.least_le grounded_fixed.1
  have ge : (⟨groundedHolds, groundedFails⟩ : Valuation Sentence).Le system.least := by
    obtain ⟨chain, disjunction⟩ := fact_chain_held
    constructor
    · intro sentence member
      simp only [groundedHolds, Set.mem_insert_iff, Set.mem_singleton_iff] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact fun valuation pre => pre.1 (by
          change (system.eval valuation (system.spec .fact)).1
          exact trivial)
      · exact fun valuation pre => pre.1 (pre.1 (by
          change (system.eval valuation (system.spec .fact)).1
          exact trivial))
      · exact chain
      · exact disjunction
    · intro sentence member
      simp only [groundedFails, Set.mem_singleton_iff] at member
      subst member
      exact liarAndNotFact_failed
  exact ⟨Set.Subset.antisymm le.1 ge.1, Set.Subset.antisymm le.2 ge.2⟩

/-- The truth-teller held, over the grounded valuation. -/
def tellerHeld : Valuation Sentence := ⟨insert .teller groundedHolds, groundedFails⟩

/-- The truth-teller failed, over the grounded valuation. -/
def tellerFailed : Valuation Sentence := ⟨groundedHolds, insert .teller groundedFails⟩

/-- **The truth-teller is held in one fixed point and failed in another**: the
choice is not grounded, and the least fixed point leaves it undetermined. -/
theorem teller_both_ways :
    ((system.jump tellerHeld).Le tellerHeld ∧ system.Sound tellerHeld ∧
        tellerHeld.Consistent ∧ Sentence.teller ∈ tellerHeld.holds) ∧
      ((system.jump tellerFailed).Le tellerFailed ∧ system.Sound tellerFailed ∧
        tellerFailed.Consistent ∧ Sentence.teller ∈ tellerFailed.fails) := by
  refine ⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩, ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_, ?_⟩⟩ <;>
    first
    | (intro sentence; cases sentence <;>
        simp [System.jump, System.eval, system, tellerHeld, tellerFailed, groundedHolds,
          groundedFails, Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff])
    | simp [tellerHeld, tellerFailed, groundedHolds, groundedFails, Set.mem_insert_iff,
        Set.mem_singleton_iff]

/-- The liar's verdict is `outsideFragment`, while the grounded fact is
established. -/
theorem verdicts :
    System.verdict system.least Sentence.liar = .outsideFragment () ∧
      (System.verdict system.least Sentence.factTrueTrue).asBool = some true ∧
      (System.verdict system.least Sentence.liarAndNotFact).asBool = some false ∧
      Sentence.teller ∉ system.least.holds ∧ Sentence.teller ∉ system.least.fails ∧
      Sentence.liarOrNotFact ∉ system.least.holds ∧
      Sentence.liarOrNotFact ∉ system.least.fails := by
  obtain ⟨holdsEq, failsEq⟩ := least_eq_grounded
  refine ⟨system.verdict_liar_outside rfl,
    System.verdict_asBool_eq_some_true.mpr fact_chain_held.1,
    (System.verdict_asBool_eq_some_false system.least_consistent).mpr liarAndNotFact_failed,
    ?_, ?_, ?_, ?_⟩ <;> simp [holdsEq, failsEq, groundedHolds, groundedFails]

theorem bivalent : system.Bivalent := fun _ => Or.inl trivial

instance : DecidablePred system.baseHolds := fun _ => instDecidableTrue
instance : DecidablePred system.baseFails := fun _ => instDecidableFalse

/-- **Grounded truth, computed by the kernel**: the twice-ascribed fact is held, the
mixed conjunction is failed, and the liar and the truth-teller get no verdict. -/
theorem decided_verdicts :
    system.groundedDecide .factTrueTrue = (true, false) ∧
      system.groundedDecide .liarAndNotFact = (false, true) ∧
      system.groundedDecide .liar = (false, false) ∧
      system.groundedDecide .teller = (false, false) := by
  decide

/-- **The ungrounded judgments are both in the greatest fixed point, the grounded
ones keep their single value**: the liar, the truth-teller and the disjunction of
the liar with a false judgment are held and failed; the grounded fact is held and
not failed. -/
theorem greatest_values :
    (Sentence.liar ∈ system.greatest.holds ∧ Sentence.liar ∈ system.greatest.fails) ∧
      (Sentence.teller ∈ system.greatest.holds ∧ Sentence.teller ∈ system.greatest.fails) ∧
      (Sentence.liarOrNotFact ∈ system.greatest.holds ∧
        Sentence.liarOrNotFact ∈ system.greatest.fails) ∧
      (Sentence.fact ∈ system.greatest.holds ∧ Sentence.fact ∉ system.greatest.fails) ∧
      system.jump system.greatest = system.greatest := by
  obtain ⟨holdsEq, failsEq⟩ := least_eq_grounded
  refine ⟨system.liar_both_greatest rfl, ?_, ?_, ?_, System.jump_greatest bivalent⟩ <;>
    simp [System.greatest, Valuation.dual, holdsEq, failsEq, groundedHolds, groundedFails]

/-- **Explicit evidence** for the twice-ascribed fact: two truth nodes over a base
leaf. -/
def factTrueTrue_evidence : system.Evidence (system.spec .factTrueTrue) true :=
  .truth (.truth (.baseHolds trivial))

theorem factTrueTrue_evidence_height : factTrueTrue_evidence.height = 2 := rfl

/-- **Time.** The twice-ascribed fact is decided at stage three and not before: its
evidence has two truth nodes. -/
theorem factTrueTrue_stage :
    Sentence.factTrueTrue ∈ (system.stage 3).holds ∧
      Sentence.factTrueTrue ∉ (system.stage 2).holds :=
  ⟨trivial, fun member => absurd member (Set.notMem_empty Sentence.fact)⟩

/-- The liar and the truth-teller have no evidence; the disjunction of the liar with the
fact has evidence through the fact only. -/
theorem evidence_controls :
    IsEmpty (system.Evidence (system.spec .liar) true) ∧
      IsEmpty (system.Evidence (system.spec .liar) false) ∧
      IsEmpty (system.Evidence (system.spec .teller) true) ∧
      Nonempty (system.Evidence (system.spec .liarOrFact) true) :=
  ⟨System.liar_noEvidence rfl true, System.liar_noEvidence rfl false,
    System.teller_noEvidence rfl true, ⟨.disjHoldsRight (.truth (.baseHolds trivial))⟩⟩

end Example

/-! ## Controls: evidence is finer than the verdict -/

namespace Controls

/-- One judgment whose specification is the disjunction of a true base fact with
itself. -/
def twice : System Unit Unit where
  spec _ := .disj (.base ()) (.base ())
  baseHolds _ := True
  baseFails _ := False
  base_consistent _ _ failed := failed

/-- Evidence through the left disjunct. -/
def leftEvidence : twice.Evidence (twice.spec ()) true := .disjHoldsLeft (.baseHolds trivial)

/-- Evidence through the right disjunct. -/
def rightEvidence : twice.Evidence (twice.spec ()) true := .disjHoldsRight (.baseHolds trivial)

/-- **Two different evidence trees for one held judgment**: the map from evidence to
verdicts is not injective. -/
theorem twoEvidence_ne : leftEvidence ≠ rightEvidence := by
  unfold leftEvidence rightEvidence
  intro same
  cases same

theorem twice_held : () ∈ twice.least.holds :=
  twice.mem_least_iff_evidence.mpr ⟨leftEvidence⟩

end Controls

#print axioms System.le_greatest
#print axioms System.mem_least_iff_evidence
#print axioms System.mem_least_iff_exists_stage
#print axioms System.mem_stage_succ_iff_evidence
#print axioms System.noEvidence_of_closed
#print axioms System.liar_noEvidence
#print axioms System.teller_noEvidence
#print axioms System.mem_greatest_iff_sound
#print axioms System.liar_selfJustifying
#print axioms System.teller_selfJustifying
#print axioms System.undetermined_not_definable
#print axioms System.stage_eq_least
#print axioms System.groundedDecide_spec
#print axioms Example.decided_verdicts
#print axioms System.liar_revenge
#print axioms Example.factTrueTrue_stage
#print axioms Example.evidence_controls
#print axioms Controls.twoEvidence_ne

end Mettapedia.GSLT.KripkeTruth
