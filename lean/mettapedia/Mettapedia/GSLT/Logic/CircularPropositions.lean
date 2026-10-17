import Mathlib.Data.PFunctor.Univariate.M
import Mettapedia.GSLT.Logic.KripkeFixedPoint
import Mettapedia.Logic.Diagonal.Provability

/-!
# Circular propositions: one universe for sentences, evidence and meaning

Self-reference without coding.  A **circular proposition** is a possibly non-well-founded
tree of strong Kleene connectives over base facts, with a truth node `truth p` saying that
`p` is true (`Proposition`, the final coalgebra of `signature`).  A system of
self-referential judgments is a system of equations, and it has exactly one solution among
circular propositions: its unfolding (`System.unfold`, `System.unfold_unique`).  This is the
solution lemma of anti-founded sets, for this signature.

**One universe.**  The circular propositions are themselves the judgments of one system
(`universal`), whose specification of a proposition is its root connective applied to the
truth of its parts.  Its grounded truth agrees with every system's: a formula of a system
holds or fails in that system's least fixed point exactly when its unfolding does in the
universal one (`System.unfold_mem_least`).  Grounded verdicts are therefore properties of
propositions, not of presentations: morphisms of systems preserve and reflect them
(`System.Hom.mem_least_iff`).  In the universal system grounded truth is, as in every
system, exactly well-founded evidence (`System.mem_least_iff_evidence`), so sentences,
their evidence and their meaning live over one carrier and refer to one another through
the truth node.

**What the universe holds.**
* Literal self-reference: the self-negating proposition (`neg selfNegation =
  selfNegation`) and the falsity liar (`neg (truth falsityLiar) = falsityLiar`) exist and
  are the unique solutions of their equations (`selfNegation_unique`,
  `falsityLiar_unique`).  Two liars calling each other false unfold to the falsity liar
  (`Controls.mutualLiars_unfold`).
* Grounded truth is consistent (`System.least_consistent`), leaves the liars undetermined
  (`selfNegation_undetermined`, `Controls.falsityLiar_undetermined`), and is compositional
  for strong Kleene negation (`mem_least_neg`): its status map sends negation to Kleene
  negation (`groundedStatus_neg`) and the self-negating proposition to the Kleene fixed
  point `none` (`groundedStatus_selfNegation`).

**What it cannot hold.**
* **No two-valued meaning**: no Boolean valuation commutes with negation
  (`no_boolean_valuation`).  The self-negating proposition would be a fixed point of
  Boolean negation, which has none.  This is the negative reading of the diagonal, with the
  fixed point supplied by finality instead of by a code map.
* **No classical deduction**: every Hilbert system over circular propositions with the
  material conditional proves every proposition (`hilbert_trivial`).  Each proposition `q`
  has a literal Curry proposition `curryProposition q = imp (curryProposition q) q`, and
  Curry's paradox is Löb's theorem for the identity operator
  (`Mettapedia.Logic.Diagonal.ProvabilityStage.curry`).
* Grounded truth escapes by not being classical: the axiom K is not grounded at the
  self-negating proposition (`least_not_axiomK`).

`strangeLoop` states all of this at once.  Over countable base facts the universe reads
faithfully into the hypersets, with grounded truth and falsity as hypersets of the same
universe (`Mettapedia.GSLT.KripkeTruth.hypersetUniverse`, in the module of circular
hypersets).

So the consistent loop is partial.  With coded self-reference in arithmetic
(`Mettapedia.Logic.Diagonal.Arithmetic`), the diagonal reaches only the provability
predicate, classical deduction stays consistent, and the limit is the second
incompleteness theorem instead.

References: P. Aczel, *Non-Well-Founded Sets*; J. Barwise and J. Etchemendy, *The Liar: An
Essay on Truth and Circularity*; J. Barwise and L. Moss, *Vicious Circles*; S. Kripke,
*Outline of a Theory of Truth*; H. B. Curry, *The Inconsistency of Certain Formal Logics*.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.KripkeTruth

open Mettapedia.Logic.Diagonal

universe u u' v w

/-! ## The signature and the universe -/

/-- The connective at the root of a circular proposition. -/
inductive Node (Base : Type v) where
  | base (fact : Base)
  | truth
  | neg
  | conj
  | disj

/-- The positions of the parts below a root. -/
def Node.Part {Base : Type v} : Node Base → Type
  | .base _ => Empty
  | .truth => Unit
  | .neg => Unit
  | .conj => Bool
  | .disj => Bool

/-- The polynomial functor of strong Kleene propositions with a truth node. -/
abbrev signature (Base : Type v) : PFunctor.{v, 0} := ⟨Node Base, Node.Part⟩

/-- **Circular propositions**: the final coalgebra of the signature, trees of connectives
with no well-foundedness condition. -/
abbrev Proposition (Base : Type v) : Type v := (signature Base).M

namespace Proposition

variable {Base : Type v}

/-- A base fact. -/
def base (fact : Base) : Proposition Base := PFunctor.M.mk ⟨.base fact, Empty.elim⟩

/-- "`p` is true." -/
def truth (p : Proposition Base) : Proposition Base := PFunctor.M.mk ⟨.truth, fun _ => p⟩

/-- Negation. -/
def neg (p : Proposition Base) : Proposition Base := PFunctor.M.mk ⟨.neg, fun _ => p⟩

/-- Conjunction. -/
def conj (p q : Proposition Base) : Proposition Base :=
  PFunctor.M.mk ⟨.conj, fun side => cond side p q⟩

/-- Disjunction. -/
def disj (p q : Proposition Base) : Proposition Base :=
  PFunctor.M.mk ⟨.disj, fun side => cond side p q⟩

/-- The material conditional. -/
def imp (p q : Proposition Base) : Proposition Base := disj (neg p) q

/-- The specification of a root connective with given parts: the connective applied to
the truth of the parts. -/
def specOf : (node : Node Base) → (Node.Part node → Proposition Base) →
    Formula (Proposition Base) Base
  | .base fact, _ => .base fact
  | .truth, part => .truth (part ())
  | .neg, part => .neg (.truth (part ()))
  | .conj, part => .conj (.truth (part true)) (.truth (part false))
  | .disj, part => .disj (.truth (part true)) (.truth (part false))

/-- The specification of a circular proposition. -/
def spec (p : Proposition Base) : Formula (Proposition Base) Base :=
  specOf (PFunctor.M.dest p).1 (PFunctor.M.dest p).2

theorem spec_base (fact : Base) : spec (base fact) = .base fact := rfl

theorem spec_truth (p : Proposition Base) : spec (truth p) = .truth p := rfl

theorem spec_neg (p : Proposition Base) : spec (neg p) = .neg (.truth p) := rfl

theorem spec_conj (p q : Proposition Base) : spec (conj p q) = .conj (.truth p) (.truth q) :=
  rfl

theorem spec_disj (p q : Proposition Base) : spec (disj p q) = .disj (.truth p) (.truth q) :=
  rfl

end Proposition

open Proposition

/-- Three-valued, consistent base facts: what a system needs besides its specification. -/
structure World (Base : Type v) where
  holds : Base → Prop
  fails : Base → Prop
  consistent : ∀ fact, holds fact → ¬ fails fact

/-- **The universal system**: the circular propositions as judgments. -/
def universal {Base : Type v} (world : World Base) : System (Proposition Base) Base where
  spec := Proposition.spec
  baseHolds := world.holds
  baseFails := world.fails
  base_consistent := world.consistent

section Universal

variable {Base : Type v} (world : World Base)

theorem universal_spec (p : Proposition Base) : (universal world).spec p = p.spec := rfl

/-- **Grounded truth is compositional for strong Kleene negation**: a negation holds
exactly when its argument fails. -/
theorem mem_least_neg (p : Proposition Base) (polarity : Bool) :
    (universal world).least.Mem (neg p) polarity ↔ (universal world).least.Mem p (!polarity) :=
  (universal world).mem_least_iff.trans (System.takes_neg.trans System.takes_truth)

/-- A truth node is grounded exactly as its argument. -/
theorem mem_least_truth (p : Proposition Base) (polarity : Bool) :
    (universal world).least.Mem (truth p) polarity ↔ (universal world).least.Mem p polarity :=
  (universal world).mem_least_iff.trans System.takes_truth

end Universal

/-! ## Unfolding: the solution lemma -/

namespace System

variable {Judgment : Type u} {Base : Type v} (system : System Judgment Base)

/-- The world of base facts of a system. -/
def world : World Base := ⟨system.baseHolds, system.baseFails, system.base_consistent⟩

/-- One step of unfolding: the root connective of a formula and its parts.  The part of a
truth node is the specification of its judgment. -/
def unfoldStep : Formula Judgment Base → signature Base (Formula Judgment Base)
  | .base fact => ⟨.base fact, Empty.elim⟩
  | .truth judgment => ⟨.truth, fun _ => system.spec judgment⟩
  | .neg formula => ⟨.neg, fun _ => formula⟩
  | .conj first second => ⟨.conj, fun side => cond side first second⟩
  | .disj first second => ⟨.disj, fun side => cond side first second⟩

/-- **Unfolding**: the circular proposition that a formula of the system expresses. -/
def unfold : Formula Judgment Base → Proposition Base := PFunctor.M.corec system.unfoldStep

theorem dest_unfold (formula : Formula Judgment Base) :
    PFunctor.M.dest (system.unfold formula) =
      (signature Base).map system.unfold (system.unfoldStep formula) :=
  PFunctor.M.dest_corec _ _

/-- **The solution lemma**: unfolding is the only map into circular propositions that
commutes with one step of unfolding. -/
theorem unfold_unique (solution : Formula Judgment Base → Proposition Base)
    (commutes : ∀ formula, PFunctor.M.dest (solution formula) =
      (signature Base).map solution (system.unfoldStep formula)) :
    solution = system.unfold :=
  PFunctor.M.corec_unique _ _ commutes

theorem unfold_eq (formula : Formula Judgment Base) :
    system.unfold formula =
      PFunctor.M.mk ((signature Base).map system.unfold (system.unfoldStep formula)) := by
  rw [← system.dest_unfold, PFunctor.M.mk_dest]

theorem unfold_base (fact : Base) : system.unfold (.base fact) = base fact := by
  rw [unfold_eq]
  unfold base
  congr 1
  simp only [unfoldStep]
  exact congrArg (Sigma.mk _) (funext fun impossible => nomatch impossible)

theorem unfold_truth (judgment : Judgment) :
    system.unfold (.truth judgment) = truth (system.unfold (system.spec judgment)) := by
  rw [unfold_eq]
  rfl

theorem unfold_neg (formula : Formula Judgment Base) :
    system.unfold (.neg formula) = neg (system.unfold formula) := by
  rw [unfold_eq]
  rfl

theorem unfold_conj (first second : Formula Judgment Base) :
    system.unfold (.conj first second) = conj (system.unfold first) (system.unfold second) := by
  rw [unfold_eq]
  unfold conj
  congr 1
  simp only [unfoldStep]
  exact congrArg (Sigma.mk _) (funext fun side => by cases side <;> rfl)

theorem unfold_disj (first second : Formula Judgment Base) :
    system.unfold (.disj first second) = disj (system.unfold first) (system.unfold second) := by
  rw [unfold_eq]
  unfold disj
  congr 1
  simp only [unfoldStep]
  exact congrArg (Sigma.mk _) (funext fun side => by cases side <;> rfl)

/-! ## Grounded truth is a property of the unfolded proposition -/

/-- The valuation of the judgments whose specifications unfold to grounded propositions. -/
def unfoldedValuation : Valuation Judgment :=
  ⟨{judgment | (universal system.world).least.Mem (system.unfold (system.spec judgment)) true},
    {judgment | (universal system.world).least.Mem (system.unfold (system.spec judgment)) false}⟩

theorem unfoldedValuation_mem {judgment : Judgment} :
    ∀ {polarity : Bool}, system.unfoldedValuation.Mem judgment polarity ↔
      (universal system.world).least.Mem (system.unfold (system.spec judgment)) polarity
  | true => Iff.rfl
  | false => Iff.rfl

theorem least_mem_unfold_of_takes : ∀ (formula : Formula Judgment Base) (polarity : Bool),
    system.Takes system.unfoldedValuation formula polarity →
      (universal system.world).least.Mem (system.unfold formula) polarity
  | .base fact, true, holds => by
      rw [(universal system.world).mem_least_iff, universal_spec, unfold_base, spec_base]
      exact holds
  | .base fact, false, fails => by
      rw [(universal system.world).mem_least_iff, universal_spec, unfold_base, spec_base]
      exact fails
  | .truth judgment, polarity, takes => by
      rw [unfold_truth, mem_least_truth]
      exact system.unfoldedValuation_mem.mp (takes_truth.mp takes)
  | .neg formula, polarity, takes => by
      rw [unfold_neg, mem_least_neg]
      exact least_mem_unfold_of_takes formula (!polarity) (takes_neg.mp takes)
  | .conj first second, true, takes => by
      rw [(universal system.world).mem_least_iff, universal_spec, unfold_conj, spec_conj]
      exact ⟨least_mem_unfold_of_takes first true takes.1,
        least_mem_unfold_of_takes second true takes.2⟩
  | .conj first second, false, takes => by
      rw [(universal system.world).mem_least_iff, universal_spec, unfold_conj, spec_conj]
      rcases takes with left | right
      · exact Or.inl (least_mem_unfold_of_takes first false left)
      · exact Or.inr (least_mem_unfold_of_takes second false right)
  | .disj first second, true, takes => by
      rw [(universal system.world).mem_least_iff, universal_spec, unfold_disj, spec_disj]
      rcases takes with left | right
      · exact Or.inl (least_mem_unfold_of_takes first true left)
      · exact Or.inr (least_mem_unfold_of_takes second true right)
  | .disj first second, false, takes => by
      rw [(universal system.world).mem_least_iff, universal_spec, unfold_disj, spec_disj]
      exact ⟨least_mem_unfold_of_takes first false takes.1,
        least_mem_unfold_of_takes second false takes.2⟩

theorem jump_unfoldedValuation_le :
    (system.jump system.unfoldedValuation).Le system.unfoldedValuation :=
  ⟨fun judgment takes => system.least_mem_unfold_of_takes (system.spec judgment) true takes,
    fun judgment takes => system.least_mem_unfold_of_takes (system.spec judgment) false takes⟩

/-- The valuation of the propositions all of whose presentations in the system are
grounded. -/
def presentedValuation : Valuation (Proposition Base) :=
  ⟨{p | ∀ formula, system.unfold formula = p → system.Takes system.least formula true},
    {p | ∀ formula, system.unfold formula = p → system.Takes system.least formula false}⟩

theorem presentedValuation_mem {p : Proposition Base} :
    ∀ {polarity : Bool}, system.presentedValuation.Mem p polarity ↔
      ∀ formula, system.unfold formula = p → system.Takes system.least formula polarity
  | true => Iff.rfl
  | false => Iff.rfl

theorem takes_of_presented : ∀ (formula : Formula Judgment Base) (polarity : Bool),
    (universal system.world).Takes system.presentedValuation
        (Proposition.spec (system.unfold formula)) polarity →
      system.Takes system.least formula polarity
  | .base fact, true, holds => by
      rw [unfold_base, spec_base] at holds
      exact holds
  | .base fact, false, fails => by
      rw [unfold_base, spec_base] at fails
      exact fails
  | .truth judgment, polarity, takes => by
      rw [unfold_truth, spec_truth, takes_truth, presentedValuation_mem] at takes
      exact takes_truth.mpr (system.mem_least_iff.mpr (takes (system.spec judgment) rfl))
  | .neg formula, polarity, takes => by
      rw [unfold_neg, spec_neg, takes_neg, takes_truth, presentedValuation_mem] at takes
      exact takes_neg.mpr (takes formula rfl)
  | .conj first second, true, takes => by
      rw [unfold_conj, spec_conj] at takes
      exact ⟨takes.1 first rfl, takes.2 second rfl⟩
  | .conj first second, false, takes => by
      rw [unfold_conj, spec_conj] at takes
      rcases takes with left | right
      · exact Or.inl (left first rfl)
      · exact Or.inr (right second rfl)
  | .disj first second, true, takes => by
      rw [unfold_disj, spec_disj] at takes
      rcases takes with left | right
      · exact Or.inl (left first rfl)
      · exact Or.inr (right second rfl)
  | .disj first second, false, takes => by
      rw [unfold_disj, spec_disj] at takes
      exact ⟨takes.1 first rfl, takes.2 second rfl⟩

theorem jump_presentedValuation_le :
    ((universal system.world).jump system.presentedValuation).Le system.presentedValuation := by
  constructor
  · intro p takes formula unfolds
    subst unfolds
    exact system.takes_of_presented formula true takes
  · intro p takes formula unfolds
    subst unfolds
    exact system.takes_of_presented formula false takes

/-- **Transport.**  A formula of a system holds (fails) in the system's least fixed point
exactly when its unfolding holds (fails) in the universal system's. -/
theorem unfold_mem_least {formula : Formula Judgment Base} {polarity : Bool} :
    (universal system.world).least.Mem (system.unfold formula) polarity ↔
      system.Takes system.least formula polarity := by
  constructor
  · intro member
    exact system.presentedValuation_mem.mp
      (((universal system.world).least_le system.jump_presentedValuation_le).mem member)
      formula rfl
  · intro takes
    exact system.least_mem_unfold_of_takes formula polarity
      (takes_mono (system.least_le system.jump_unfoldedValuation_le) takes)

/-- **A judgment's grounded verdict is the verdict of the proposition it unfolds to.** -/
theorem mem_least_iff_unfold {judgment : Judgment} {polarity : Bool} :
    system.least.Mem judgment polarity ↔
      (universal system.world).least.Mem (system.unfold (.truth judgment)) polarity :=
  takes_truth.symm.trans system.unfold_mem_least.symm

end System

/-! ## Morphisms of systems -/

namespace Formula

variable {Judgment : Type u} {Judgment' : Type u'} {Base : Type v}

/-- Renaming the judgments of a formula. -/
def rename (map : Judgment → Judgment') : Formula Judgment Base → Formula Judgment' Base
  | .base fact => .base fact
  | .truth judgment => .truth (map judgment)
  | .neg formula => .neg (formula.rename map)
  | .conj first second => .conj (first.rename map) (second.rename map)
  | .disj first second => .disj (first.rename map) (second.rename map)

end Formula

namespace System

variable {Judgment : Type u} {Judgment' : Type u'} {Base : Type v}

/-- A **morphism of systems**: a renaming of judgments that commutes with specification,
over one world of base facts. -/
structure Hom (source : System Judgment Base) (target : System Judgment' Base) where
  map : Judgment → Judgment'
  spec_map : ∀ judgment, target.spec (map judgment) = (source.spec judgment).rename map
  world_eq : target.world = source.world

variable {source : System Judgment Base} {target : System Judgment' Base}

/-- **Unfolding is natural**: a morphism does not change the propositions expressed. -/
theorem Hom.unfold_rename (hom : Hom source target) :
    (fun formula => target.unfold (formula.rename hom.map)) = source.unfold := by
  apply source.unfold_unique
  intro formula
  cases formula with
  | base fact =>
      change PFunctor.M.dest (target.unfold (.base fact)) = _
      rw [target.dest_unfold]
      simp only [unfoldStep]
      exact congrArg (Sigma.mk _) (funext fun impossible => nomatch impossible)
  | truth judgment =>
      change PFunctor.M.dest (target.unfold (.truth (hom.map judgment))) = _
      rw [target.dest_unfold]
      simp only [unfoldStep, hom.spec_map]
      rfl
  | neg formula =>
      change PFunctor.M.dest (target.unfold (.neg (formula.rename hom.map))) = _
      rw [target.dest_unfold]
      rfl
  | conj first second =>
      change PFunctor.M.dest (target.unfold (.conj (first.rename hom.map)
        (second.rename hom.map))) = _
      rw [target.dest_unfold]
      simp only [unfoldStep]
      exact congrArg (Sigma.mk _) (funext fun side => by cases side <;> rfl)
  | disj first second =>
      change PFunctor.M.dest (target.unfold (.disj (first.rename hom.map)
        (second.rename hom.map))) = _
      rw [target.dest_unfold]
      simp only [unfoldStep]
      exact congrArg (Sigma.mk _) (funext fun side => by cases side <;> rfl)

/-- **Grounded verdicts are invariant under morphisms**: they are preserved and
reflected. -/
theorem Hom.mem_least_iff (hom : Hom source target) {judgment : Judgment} {polarity : Bool} :
    target.least.Mem (hom.map judgment) polarity ↔ source.least.Mem judgment polarity := by
  rw [target.mem_least_iff_unfold, source.mem_least_iff_unfold, hom.world_eq]
  have same := congrFun hom.unfold_rename (.truth judgment)
  exact Iff.of_eq (congrArg (fun p => (universal source.world).least.Mem p polarity) same)

end System

/-! ## Literal self-reference -/

section Liars

variable {Base : Type v}

/-- One state, a negation of itself. -/
def selfNegationStep : Unit → signature Base Unit := fun _ => ⟨.neg, fun _ => ()⟩

/-- **The self-negating proposition.** -/
def selfNegation : Proposition Base := PFunctor.M.corec selfNegationStep ()

theorem neg_selfNegation : neg (selfNegation : Proposition Base) = selfNegation := by
  unfold selfNegation
  conv_rhs => rw [PFunctor.M.corec_def (F := signature Base)]
  rfl

/-- **The self-negating proposition is unique**: it is the only solution of
`p = neg p`. -/
theorem selfNegation_unique {p : Proposition Base} (fixed : neg p = p) : p = selfNegation := by
  have unique := PFunctor.M.corec_unique (selfNegationStep (Base := Base)) (fun _ => p) (by
      intro _
      conv_lhs => rw [← fixed]
      rfl)
  exact congrFun unique ()

theorem neg_injective : Function.Injective (neg : Proposition Base → Proposition Base) := by
  intro p q same
  have dests : (⟨.neg, fun _ => p⟩ : signature Base (Proposition Base)) = ⟨.neg, fun _ => q⟩ :=
    congrArg PFunctor.M.dest same
  exact congrFun (eq_of_heq (Sigma.mk.inj_iff.mp dests).2) ()

theorem spec_selfNegation :
    Proposition.spec (selfNegation : Proposition Base) = .neg (.truth selfNegation) := by
  conv_lhs => rw [← neg_selfNegation]
  exact spec_neg selfNegation

/-- The falsity liar, built from two states: a negation over a truth node over the
start. -/
def falsityLiarStep : Bool → signature Base Bool
  | false => ⟨.neg, fun _ => true⟩
  | true => ⟨.truth, fun _ => false⟩

/-- **The falsity liar**: "this proposition is false", `neg (truth falsityLiar)`. -/
def falsityLiar : Proposition Base := PFunctor.M.corec falsityLiarStep false

theorem neg_truth_falsityLiar :
    neg (truth (falsityLiar : Proposition Base)) = falsityLiar := by
  have atTrue : PFunctor.M.corec (falsityLiarStep (Base := Base)) true = truth falsityLiar := by
    rw [PFunctor.M.corec_def (F := signature Base)]
    rfl
  unfold falsityLiar
  conv_rhs => rw [PFunctor.M.corec_def (F := signature Base)]
  change neg (truth falsityLiar) = neg (PFunctor.M.corec falsityLiarStep true)
  rw [atTrue]

/-- **The falsity liar is unique**: it is the only solution of `p = neg (truth p)`. -/
theorem falsityLiar_unique {p : Proposition Base} (fixed : neg (truth p) = p) :
    p = falsityLiar := by
  have unique := PFunctor.M.corec_unique (falsityLiarStep (Base := Base))
    (fun side => cond side (truth p) p) (by
      intro side
      cases side
      · change PFunctor.M.dest p = _
        conv_lhs => rw [← fixed]
        rfl
      · rfl)
  exact congrFun unique false

variable (world : World Base)

/-- The self-negating proposition is a liar of the universal system. -/
theorem selfNegation_isLiar :
    (universal world).spec selfNegation = .neg (.truth selfNegation) := by
  rw [universal_spec]
  exact spec_selfNegation

/-- **The self-negating proposition is undetermined** by grounded truth. -/
theorem selfNegation_undetermined :
    selfNegation ∉ (universal world).least.holds ∧ selfNegation ∉ (universal world).least.fails :=
  (universal world).liar_not_mem_least (selfNegation_isLiar world)

/-- The grounded status of a circular proposition. -/
noncomputable def groundedStatus (p : Proposition Base) : Option Bool := by
  classical
  exact status (universal world).least p

theorem groundedStatus_eq_some_true {p : Proposition Base} :
    groundedStatus world p = some true ↔ p ∈ (universal world).least.holds := by
  classical
  unfold groundedStatus status
  by_cases held : p ∈ (universal world).least.holds
  · simp [held]
  · by_cases failed : p ∈ (universal world).least.fails <;> simp [held, failed]

theorem groundedStatus_eq_some_false {p : Proposition Base} :
    groundedStatus world p = some false ↔ p ∈ (universal world).least.fails := by
  classical
  unfold groundedStatus status
  by_cases held : p ∈ (universal world).least.holds
  · simp [held, (universal world).least_consistent p held]
  · by_cases failed : p ∈ (universal world).least.fails <;> simp [held, failed]

theorem groundedStatus_eq_none {p : Proposition Base} :
    groundedStatus world p = none ↔
      p ∉ (universal world).least.holds ∧ p ∉ (universal world).least.fails := by
  classical
  unfold groundedStatus status
  by_cases held : p ∈ (universal world).least.holds
  · simp [held]
  · by_cases failed : p ∈ (universal world).least.fails <;> simp [held, failed]

/-- **Grounded truth sends negation to Kleene negation.** -/
theorem groundedStatus_neg (p : Proposition Base) :
    groundedStatus world (neg p) = kleeneNot (groundedStatus world p) := by
  have holds := mem_least_neg world p true
  have fails := mem_least_neg world p false
  change neg p ∈ (universal world).least.holds ↔ p ∈ (universal world).least.fails at holds
  change neg p ∈ (universal world).least.fails ↔ p ∈ (universal world).least.holds at fails
  rcases hstatus : groundedStatus world p with _ | value
  · obtain ⟨notHeld, notFailed⟩ := (groundedStatus_eq_none world).mp hstatus
    exact (groundedStatus_eq_none world).mpr ⟨fun h => notFailed (holds.mp h),
      fun h => notHeld (fails.mp h)⟩
  · cases value with
    | true =>
        exact (groundedStatus_eq_some_false world).mpr
          (fails.mpr ((groundedStatus_eq_some_true world).mp hstatus))
    | false =>
        exact (groundedStatus_eq_some_true world).mpr
          (holds.mpr ((groundedStatus_eq_some_false world).mp hstatus))

/-- **The self-negating proposition takes the Kleene fixed point.** -/
theorem groundedStatus_selfNegation : groundedStatus world selfNegation = none :=
  (groundedStatus_eq_none world).mpr (selfNegation_undetermined world)

end Liars

/-! ## What the universe cannot hold -/

section Limits

variable {Base : Type v}

/-- **No two-valued meaning.**  No Boolean valuation of circular propositions commutes
with negation: the self-negating proposition would be a fixed point of Boolean
negation. -/
theorem no_boolean_valuation :
    ¬ ∃ value : Proposition Base → Bool, ∀ p, value (neg p) = !value p := by
  rintro ⟨value, commutes⟩
  have fixed := commutes selfNegation
  rw [neg_selfNegation] at fixed
  exact bool_not_fixedPointFree (value selfNegation) fixed.symm

/-- A step function on seeds, where seeds that are already propositions unfold as
themselves. -/
def seedStep {σ : Type w} (fresh : σ → signature Base (σ ⊕ Proposition Base)) :
    σ ⊕ Proposition Base → signature Base (σ ⊕ Proposition Base) :=
  Sum.elim fresh fun p => (signature Base).map Sum.inr (PFunctor.M.dest p)

/-- **Seeds that are propositions unfold to themselves.** -/
theorem corec_seedStep_inr {σ : Type w} (fresh : σ → signature Base (σ ⊕ Proposition Base))
    (p : Proposition Base) : PFunctor.M.corec (seedStep fresh) (.inr p) = p := by
  have copy : (fun p => PFunctor.M.corec (seedStep fresh) (.inr p)) =
      PFunctor.M.corec PFunctor.M.dest := by
    apply PFunctor.M.corec_unique
    intro p
    show PFunctor.M.dest (PFunctor.M.corec (seedStep fresh) (.inr p)) = _
    rw [PFunctor.M.dest_corec]
    show (signature Base).map (PFunctor.M.corec (seedStep fresh))
      ((signature Base).map Sum.inr (PFunctor.M.dest p)) = _
    generalize PFunctor.M.dest p = parts
    obtain ⟨node, children⟩ := parts
    rfl
  have identity : (fun p : Proposition Base => p) = PFunctor.M.corec PFunctor.M.dest := by
    apply PFunctor.M.corec_unique
    intro p
    show PFunctor.M.dest p = (signature Base).map (fun p => p) (PFunctor.M.dest p)
    generalize PFunctor.M.dest p = parts
    obtain ⟨node, children⟩ := parts
    rfl
  exact congrFun (copy.trans identity.symm) p

/-- The fresh states of a Curry proposition: the conditional and its negated
antecedent. -/
def curryFresh (q : Proposition Base) : Bool → signature Base (Bool ⊕ Proposition Base)
  | false => ⟨.disj, fun side => cond side (.inl true) (.inr q)⟩
  | true => ⟨.neg, fun _ => .inl false⟩

/-- **The Curry proposition** of `q`: "if this proposition holds, then `q`". -/
def curryProposition (q : Proposition Base) : Proposition Base :=
  PFunctor.M.corec (seedStep (curryFresh q)) (.inl false)

theorem curryProposition_eq (q : Proposition Base) :
    curryProposition q = imp (curryProposition q) q := by
  have atNeg : PFunctor.M.corec (seedStep (curryFresh q)) (.inl true) =
      neg (curryProposition q) := by
    rw [PFunctor.M.corec_def (F := signature Base)]
    rfl
  conv_lhs => rw [curryProposition, PFunctor.M.corec_def (F := signature Base)]
  unfold imp disj
  congr 1
  simp only [seedStep, Sum.elim_inl, curryFresh]
  refine congrArg (Sigma.mk _) (funext fun side => ?_)
  cases side
  · exact corec_seedStep_inr (curryFresh q) q
  · exact atNeg

/-- **Curry's paradox for circular propositions.**  Every Hilbert system over circular
propositions with the material conditional, closed under modus ponens and containing the
axioms K and S, proves every proposition. -/
theorem hilbert_trivial (Proves : Proposition Base → Prop)
    (modusPonens : ∀ {a b : Proposition Base}, Proves (imp a b) → Proves a → Proves b)
    (axiomK : ∀ a b : Proposition Base, Proves (imp a (imp b a)))
    (axiomS : ∀ a b c : Proposition Base,
      Proves (imp (imp a (imp b c)) (imp (imp a b) (imp a c))))
    (q : Proposition Base) : Proves q := by
  let stage := ProvabilityStage.ofHilbert Proves imp q modusPonens axiomK axiomS
  have identity := ProvabilityStage.hilbert_identity modusPonens axiomK axiomS
  refine ProvabilityStage.curry (stage := stage) (fun _ => rfl) (fun c => ?_) q
  refine ⟨curryProposition c, ?_⟩
  change Proves (imp (curryProposition c) (imp (curryProposition c) c)) ∧
    Proves (imp (imp (curryProposition c) c) (curryProposition c))
  rw [← curryProposition_eq]
  exact ⟨identity _, identity _⟩

/-- The fresh state of "this proposition, or `q`". -/
def orSelfFresh (q : Proposition Base) : Unit → signature Base (Unit ⊕ Proposition Base) :=
  fun _ => ⟨.disj, fun side => cond side (.inr q) (.inl ())⟩

/-- **"`q`, or this proposition"**: a circular proposition whose second disjunct is
itself. -/
def orSelf (q : Proposition Base) : Proposition Base :=
  PFunctor.M.corec (seedStep (orSelfFresh q)) (.inl ())

theorem orSelf_eq (q : Proposition Base) : orSelf q = disj q (orSelf q) := by
  conv_lhs => rw [orSelf, PFunctor.M.corec_def (F := signature Base)]
  unfold disj
  congr 1
  simp only [seedStep, Sum.elim_inl, orSelfFresh]
  refine congrArg (Sigma.mk _) (funext fun side => ?_)
  cases side
  · rfl
  · exact corec_seedStep_inr (orSelfFresh q) q

variable (world : World Base)

/-- **A circular proposition can be grounded.**  "`q`, or this proposition" holds whenever
`q` holds: groundedness is a property of evidence, not of the shape of the proposition. -/
theorem orSelf_held {q : Proposition Base} (held : q ∈ (universal world).least.holds) :
    orSelf q ∈ (universal world).least.holds := by
  rw [orSelf_eq]
  change (universal world).least.Mem (disj q (orSelf q)) true
  rw [(universal world).mem_least_iff, universal_spec, spec_disj]
  exact Or.inl held

/-- **Grounded truth is not classical**: the axiom K is not grounded at the
self-negating proposition. -/
theorem least_not_axiomK :
    ¬ ∀ a b : Proposition Base, (universal world).least.Mem (imp a (imp b a)) true := by
  intro axiomK
  obtain ⟨notHeld, _⟩ := selfNegation_undetermined world
  have negHeld : neg selfNegation ∈ (universal world).least.holds → False := by
    rw [neg_selfNegation]
    exact notHeld
  have grounded := axiomK selfNegation selfNegation
  rw [(universal world).mem_least_iff] at grounded
  change neg selfNegation ∈ (universal world).least.holds ∨
    imp selfNegation selfNegation ∈ (universal world).least.holds at grounded
  rcases grounded with left | right
  · exact negHeld left
  · have unfolded := ((universal world).mem_least_iff
      (judgment := imp selfNegation selfNegation) (polarity := true)).mp right
    change neg selfNegation ∈ (universal world).least.holds ∨
      selfNegation ∈ (universal world).least.holds at unfolded
    rcases unfolded with negSelf | self
    · exact negHeld negSelf
    · exact notHeld self

end Limits

/-! ## The strange loop, in one statement -/

section StrangeLoop

variable {Base : Type v}

/-- **The consistent strange loop.**  Over a world of base facts, the universe of circular
propositions
* receives every system of self-referential judgments over that world, by the unique
  solution of its equations, preserving and reflecting every grounded verdict;
* has consistent grounded truth, which is exactly well-founded evidence, and which leaves
  the self-negating proposition undetermined;
* admits no Boolean valuation commuting with negation, and no Hilbert system for the
  material conditional other than the trivial one. -/
theorem strangeLoop (world : World Base) :
    (∀ {Judgment : Type u} (system : System Judgment Base), system.world = world →
      (∀ solution : Formula Judgment Base → Proposition Base,
          (∀ formula, PFunctor.M.dest (solution formula) =
            (signature Base).map solution (system.unfoldStep formula)) →
          solution = system.unfold) ∧
        ∀ (judgment : Judgment) (polarity : Bool), system.least.Mem judgment polarity ↔
          (universal world).least.Mem (system.unfold (.truth judgment)) polarity) ∧
      (universal world).least.Consistent ∧
      (∀ (p : Proposition Base) (polarity : Bool), (universal world).least.Mem p polarity ↔
        Nonempty ((universal world).Evidence ((universal world).spec p) polarity)) ∧
      (selfNegation ∉ (universal world).least.holds ∧
        selfNegation ∉ (universal world).least.fails) ∧
      (¬ ∃ value : Proposition Base → Bool, ∀ p, value (neg p) = !value p) ∧
      (∀ Proves : Proposition Base → Prop,
        (∀ {a b : Proposition Base}, Proves (imp a b) → Proves a → Proves b) →
        (∀ a b : Proposition Base, Proves (imp a (imp b a))) →
        (∀ a b c : Proposition Base,
          Proves (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))) →
        ∀ q, Proves q) := by
  refine ⟨fun system sameWorld => ⟨system.unfold_unique, fun judgment polarity => ?_⟩,
    (universal world).least_consistent,
    fun _ _ => (universal world).mem_least_iff_evidence,
    selfNegation_undetermined world, no_boolean_valuation,
    fun Proves modusPonens axiomK axiomS q => hilbert_trivial Proves modusPonens axiomK axiomS q⟩
  subst sameWorld
  exact system.mem_least_iff_unfold

end StrangeLoop

/-! ## Controls -/

namespace Controls

/-- A liar calling itself false, and two liars calling each other false. -/
inductive LiarJudgment where
  | single
  | left
  | right

/-- The liars, over one true base fact. -/
def liars : System LiarJudgment Unit where
  spec
    | .single => .neg (.truth .single)
    | .left => .neg (.truth .right)
    | .right => .neg (.truth .left)
  baseHolds _ := True
  baseFails _ := False
  base_consistent _ _ failed := failed

/-- Collapse every liar onto the single one. -/
def collapse : liars.Hom liars where
  map _ := .single
  spec_map judgment := by cases judgment <;> rfl
  world_eq := rfl

/-- **Two mutual liars are one proposition**, the single liar. -/
theorem mutualLiars_unfold :
    liars.unfold (.truth .left) = liars.unfold (.truth .single) ∧
      liars.unfold (.truth .right) = liars.unfold (.truth .single) :=
  ⟨(congrFun collapse.unfold_rename (.truth .left)).symm,
    (congrFun collapse.unfold_rename (.truth .right)).symm⟩

/-- **The single liar unfolds to the falsity liar.** -/
theorem single_unfold : liars.unfold (liars.spec .single) = falsityLiar := by
  apply falsityLiar_unique
  conv_rhs => rw [show liars.spec .single = .neg (.truth .single) from rfl, liars.unfold_neg,
    liars.unfold_truth]

/-- **The falsity liar is undetermined** by grounded truth, read off the single liar of a
system through the transport theorem. -/
theorem falsityLiar_undetermined :
    falsityLiar ∉ (universal liars.world).least.holds ∧
      falsityLiar ∉ (universal liars.world).least.fails := by
  obtain ⟨notHeld, notFailed⟩ := liars.liar_not_mem_least (liar := .single) rfl
  rw [← single_unfold]
  constructor
  · intro held
    exact notHeld (liars.mem_least_iff.mpr
      ((liars.unfold_mem_least (formula := liars.spec .single) (polarity := true)).mp held))
  · intro failed
    exact notFailed (liars.mem_least_iff.mpr
      ((liars.unfold_mem_least (formula := liars.spec .single) (polarity := false)).mp failed))

/-- **Different circles, different propositions**: the falsity liar is not the
self-negating proposition, although both are undetermined. -/
theorem falsityLiar_ne_selfNegation : (falsityLiar : Proposition Unit) ≠ selfNegation := by
  intro same
  have negs : neg (truth (falsityLiar : Proposition Unit)) = neg selfNegation := by
    rw [neg_truth_falsityLiar, neg_selfNegation, same]
  have atChild := neg_injective negs
  have heads := congrArg (fun p => (PFunctor.M.dest p).1) atChild
  rw [← neg_selfNegation] at heads
  change Node.truth = Node.neg at heads
  cases heads

/-- A grounded proposition: the truth of a true base fact holds. -/
theorem truth_base_held :
    truth (base ()) ∈ (universal liars.world).least.holds := by
  have := (mem_least_truth liars.world (base ()) true).mpr
  apply this
  rw [(universal liars.world).mem_least_iff, universal_spec, spec_base]
  exact trivial

end Controls

#print axioms System.unfold_unique
#print axioms System.unfold_mem_least
#print axioms System.mem_least_iff_unfold
#print axioms System.Hom.mem_least_iff
#print axioms selfNegation_unique
#print axioms falsityLiar_unique
#print axioms selfNegation_undetermined
#print axioms groundedStatus_neg
#print axioms groundedStatus_selfNegation
#print axioms no_boolean_valuation
#print axioms curryProposition_eq
#print axioms hilbert_trivial
#print axioms least_not_axiomK
#print axioms Controls.mutualLiars_unfold
#print axioms Controls.falsityLiar_undetermined
#print axioms Controls.falsityLiar_ne_selfNegation
#print axioms strangeLoop
#print axioms orSelf_held

end Mettapedia.GSLT.KripkeTruth
