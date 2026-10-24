import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Occupancy
import Mettapedia.Languages.ProcessCalculi.RhoCombinators.NormalForm

/-!
# Termination without the opener, and the weight the bound needs

Without the opener every reduction sequence is finite, and the bound is a count
of the atoms sitting at the top level.  This module proves that, and fixes the
count.

The natural measure — *the number of non-message atoms* — does not work, and
`nonMessageCount_not_strictly_decreasing` exhibits the rule that defeats it:
the two re-addressing routers and the synchroniser consume themselves and
produce a forwarder, so they replace one non-message atom with another and the
count is unchanged.  Every other rule but the opener's does consume one and
produce none.

`weight` repairs it by charging two for the three atoms that produce a
forwarder and one for every other non-message atom.  Then every rule but the
opener's strictly decreases the weight (`weight_lt_of_step`), and a reduction
sequence is no longer than the weight it starts from
(`chain_length_le_weight`).

The hypotheses are where this connects to the expressiveness lattice: the bound
holds of a term that *occupies a rule-closed point omitting the opener*.
Occupancy is decidable by one traversal (`Occupancy.occ_par`) and reduction
keeps a term inside a rule-closed point (`Occupancy.occ_step`), so the
occupancy check is itself the certificate that reduction from the checked term
terminates — and, being a bound rather than an abstract finiteness claim, it
says in how many steps.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## Two counts -/

/-- The number of atoms at the top level that are not messages.  This is the
measure that does not work. -/
def nonMessageCount : Comb → Nat
  | nil => 0
  | par p q => nonMessageCount p + nonMessageCount q
  | mm _ _ => 0
  | dd _ _ _ => 1
  | kk _ => 1
  | fw _ _ => 1
  | bl _ _ => 1
  | br _ _ => 1
  | sy _ _ _ => 1
  | ev _ => 1
  | qq _ _ => 1
  | consPar _ _ _ => 1
  | consMsg _ _ _ => 1
  | consDup _ _ _ _ => 1
  | consSyn _ _ _ _ => 1

/-- **The weight.**  Two for the atoms whose rule produces a forwarder, one for
every other non-message atom, nothing for a message.  A message's payload is
not charged, so the weight is a property of the top level only. -/
def weight : Comb → Nat
  | nil => 0
  | par p q => weight p + weight q
  | mm _ _ => 0
  | dd _ _ _ => 1
  | kk _ => 1
  | fw _ _ => 1
  | bl _ _ => 2
  | br _ _ => 2
  | sy _ _ _ => 2
  | ev _ => 1
  | qq _ _ => 1
  | consPar _ _ _ => 1
  | consMsg _ _ _ => 1
  | consDup _ _ _ _ => 1
  | consSyn _ _ _ _ => 1

/-- Structural congruence preserves the weight, the monoid laws being exactly
the laws of addition the weight uses. -/
theorem weight_cong {p q : Comb} (h : Cong p q) : weight p = weight q := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | parNil p => simp [weight]
  | parComm p q => simp [weight, Nat.add_comm]
  | parAssoc p q r => simp [weight, Nat.add_assoc]
  | parLeft q _ ih => simp [weight, ih]
  | parRight p _ ih => simp [weight, ih]

/-! ## The natural measure fails -/

/-- **A rule that leaves the non-message atom count alone.**  The outward
binder consumes itself and produces a forwarder, so one non-message atom
becomes one non-message atom.  The same happens for the inward binder and the
synchroniser, so a bound on reduction length cannot be the count of
non-message atoms. -/
theorem nonMessageCount_not_strictly_decreasing :
    ∃ p q : Comb, Step Cong p q ∧ nonMessageCount q = nonMessageCount p := by
  refine ⟨par (br nil nil) (mm nil nil), fw nil nil, ?_, by decide⟩
  exact Step.ofMinus (StepMinus.bindOut nil nil (Cong.refl nil))

/-- And likewise for the inward binder. -/
theorem nonMessageCount_not_strictly_decreasing_bindIn :
    ∃ p q : Comb, Step Cong p q ∧ nonMessageCount q = nonMessageCount p := by
  refine ⟨par (bl nil nil) (mm nil nil), fw nil nil, ?_, by decide⟩
  exact Step.ofMinus (StepMinus.bindIn nil nil (Cong.refl nil))

/-- And for the synchroniser. -/
theorem nonMessageCount_not_strictly_decreasing_sync :
    ∃ p q : Comb, Step Cong p q ∧ nonMessageCount q = nonMessageCount p := by
  refine ⟨par (sy nil nil nil) (mm nil nil), fw nil nil, ?_, by decide⟩
  exact Step.ofMinus (StepMinus.synchronise nil nil nil (Cong.refl nil))

/-! ## The weight strictly decreases -/

/-- Occupancy of a point omitting the opener rules out the opening rule, which
is the one rule whose right-hand side is an arbitrary process. -/
theorem not_occ_ev {admitted : Finset Shape} (noOpener : Shape.ev ∉ admitted)
    {a : Comb} (occupied : Occ admitted (ev a)) : False := by
  cases occupied with
  | ev shape _ => exact noOpener shape

theorem weight_lt_of_stepMinus {admitted : Finset Shape} (noOpener : Shape.ev ∉ admitted)
    {p q : Comb} (occupied : Occ admitted p) (step : StepMinus Cong p q) :
    weight q < weight p := by
  induction step with
  | duplicate b c v _ => simp [weight]
  | discard v _ => simp [weight]
  | forward b v _ => simp [weight]
  | bindOut b v _ => simp [weight]
  | bindIn b v _ => simp [weight]
  | synchronise b c v _ => simp [weight]
  | opening p _ =>
      exact absurd ((occ_par _ _ _).mp occupied).1 (fun h => not_occ_ev noOpener h)
  | release b p _ => simp [weight]
  | parLeft r _ ih =>
      have parts := (occ_par _ _ _).mp occupied
      simp only [weight]
      exact Nat.add_lt_add_right (ih parts.1) _
  | congruent hc₁ _ hc₂ ih =>
      rw [weight_cong hc₁, ← weight_cong hc₂]
      exact ih (occ_cong hc₁ occupied)

/-- **Every rule but the opener's strictly decreases the weight.**  The three
atoms that produce a forwarder pay two and leave one behind; every other rule
consumes a non-message atom and produces only messages. -/
theorem weight_lt_of_step {admitted : Finset Shape} (noOpener : Shape.ev ∉ admitted)
    {p q : Comb} (occupied : Occ admitted p) (step : Step Cong p q) :
    weight q < weight p := by
  induction step with
  | ofMinus minus => exact weight_lt_of_stepMinus noOpener occupied minus
  | buildPar c p q _ _ => simp [weight]
  | buildMsg c u v _ _ => simp [weight]
  | buildDup e p q r _ _ _ => simp [weight]
  | buildSyn e p q r _ _ _ => simp [weight]
  | parLeft r _ ih =>
      have parts := (occ_par _ _ _).mp occupied
      simp only [weight]
      exact Nat.add_lt_add_right (ih parts.1) _
  | congruent hc₁ _ hc₂ ih =>
      rw [weight_cong hc₁, ← weight_cong hc₂]
      exact ih (occ_cong hc₁ occupied)

/-! ## The bound -/

/-- A reduction sequence of a stated length. -/
inductive Chain : Comb → Nat → Prop where
  | nil (p : Comb) : Chain p 0
  | cons {p q : Comb} {n : Nat} : Step Cong p q → Chain q n → Chain p (n + 1)

/-- **Reduction terminates, with a bound.**  From a term occupying a
rule-closed point that omits the opener, no reduction sequence is longer than
the term's weight.  So the occupancy check on that point is the certificate
that reduction from the checked term stops, and it says when. -/
theorem chain_length_le_weight {admitted : Finset Shape}
    (closed : RuleClosed admitted) (noOpener : Shape.ev ∉ admitted)
    {p : Comb} {n : Nat} (occupied : Occ admitted p) (chain : Chain p n) :
    n ≤ weight p := by
  induction chain with
  | nil p => exact Nat.zero_le _
  | cons step rest ih =>
      have next := occ_step closed occupied step
      have drop := weight_lt_of_step noOpener occupied step
      exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (ih next) drop)

/-- The opener is what the bound excludes, and it is excluded for a reason: its
right-hand side is an arbitrary process, so nothing about the redex bounds what
replaces it. -/
theorem opener_unbounds {a p : Comb} :
    StepMinus Cong (par (ev a) (mm a p)) p :=
  StepMinus.opening p (Cong.refl a)

/-! ## Controls -/

namespace TerminationControls

open Controls (openerPoint)

/-- A point of the lattice omitting the opener, and closed under reduction. -/
def boundedPoint : Finset Shape :=
  latticePoint ∅ {Shape.consPar}

theorem boundedPoint_ruleClosed : RuleClosed boundedPoint := by decide

theorem boundedPoint_omits_opener : Shape.ev ∉ boundedPoint := by decide

/-- The weight charges the outward binder two and the forwarder it becomes
one, which is the whole content of the repair. -/
theorem weight_binder_exceeds_forwarder :
    weight (br nil nil) = 2 ∧ weight (fw nil nil) = 1 := by
  exact ⟨by decide, by decide⟩

/-- The two counts disagree exactly there. -/
theorem counts_disagree_on_binder :
    nonMessageCount (br nil nil) = 1 ∧ weight (br nil nil) = 2 := by
  exact ⟨by decide, by decide⟩

/-- A relay occupying the bounded point admits no sequence longer than its
weight. -/
theorem relay_bounded {n : Nat}
    (chain : Chain (par (br nil nil) (mm nil nil)) n) : n ≤ 2 := by
  have occupied : Occ boundedPoint (par (br nil nil) (mm nil nil)) := by decide
  have bound := chain_length_le_weight boundedPoint_ruleClosed
    boundedPoint_omits_opener occupied chain
  simpa [weight] using bound

/-! ## Constructed duplication defeats a syntactic absence test -/

namespace ConstructedDuplication

/-- Six channel names; any closed terms will do. -/
def sourceName : Comb := kk nil
def copyName : Comb := kk (kk nil)
def firstInput : Comb := kk (kk (kk nil))
def secondInput : Comb := ev nil
def thirdInput : Comb := ev (ev nil)
def constructorOutput : Comb := fw nil nil

/-- Code that reconstructs a duplicator and the opener of the next round. -/
def rebuildCode : Comb :=
  par (consDup firstInput secondInput thirdInput constructorOutput)
    (par (mm firstInput sourceName)
      (par (mm secondInput copyName)
        (par (mm thirdInput sourceName) (par (ev constructorOutput) (ev copyName)))))

/-- Start: two copies of the code and one opener; no duplicator anywhere. -/
def duplicationFreeStart : Comb :=
  par (mm copyName rebuildCode) (par (mm sourceName rebuildCode) (ev copyName))

theorem duplicationFreeStart_has_no_dd : Shape.dd ∉ atomsStar duplicationFreeStart := by decide

theorem duplicationFreeStart_has_constructor_and_opener :
    Shape.consDup ∈ atomsStar duplicationFreeStart ∧
      Shape.ev ∈ atomsStar duplicationFreeStart := by decide

/-- The opener at the copy channel activates one copy of the code. -/
private theorem open_code : Step Cong duplicationFreeStart (par rebuildCode (mm sourceName rebuildCode)) := by
  refine Step.congruent (p' := par (par (ev copyName) (mm copyName rebuildCode)) (mm sourceName rebuildCode))
    (q' := par rebuildCode (mm sourceName rebuildCode)) ?_ ?_ (Cong.refl _)
  · exact cong_of_perm (by decide)
  · exact Step.parLeft _ (Step.ofMinus (StepMinus.opening rebuildCode (Cong.refl copyName)))

/-- Step 2: the duplicator constructor builds the quotation of `dd sourceName copyName sourceName`. -/
private theorem construct_duplicator : Step Cong (par rebuildCode (mm sourceName rebuildCode))
    (par (mm constructorOutput (dd sourceName copyName sourceName)) (par (par (ev constructorOutput) (ev copyName)) (mm sourceName rebuildCode))) := by
  refine Step.congruent
    (p' := par (par (consDup firstInput secondInput thirdInput constructorOutput) (par (mm firstInput sourceName) (par (mm secondInput copyName) (mm thirdInput sourceName))))
              (par (par (ev constructorOutput) (ev copyName)) (mm sourceName rebuildCode)))
    (q' := par (mm constructorOutput (dd sourceName copyName sourceName)) (par (par (ev constructorOutput) (ev copyName)) (mm sourceName rebuildCode))) ?_ ?_ (Cong.refl _)
  · exact cong_of_perm (by decide)
  · exact Step.parLeft _ (Step.buildDup constructorOutput sourceName copyName sourceName (Cong.refl firstInput) (Cong.refl secondInput) (Cong.refl thirdInput))

/-- Step 3: the opener at `constructorOutput` erects the live duplicator. -/
private theorem open_duplicator : Step Cong (par (mm constructorOutput (dd sourceName copyName sourceName)) (par (par (ev constructorOutput) (ev copyName)) (mm sourceName rebuildCode)))
    (par (dd sourceName copyName sourceName) (par (ev copyName) (mm sourceName rebuildCode))) := by
  refine Step.congruent
    (p' := par (par (ev constructorOutput) (mm constructorOutput (dd sourceName copyName sourceName))) (par (ev copyName) (mm sourceName rebuildCode)))
    (q' := par (dd sourceName copyName sourceName) (par (ev copyName) (mm sourceName rebuildCode))) ?_ ?_ (Cong.refl _)
  · exact cong_of_perm (by decide)
  · exact Step.parLeft _ (Step.ofMinus (StepMinus.opening (dd sourceName copyName sourceName) (Cong.refl constructorOutput)))

/-- Step 4: the duplicator copies the code message to `copyName` and back to `sourceName`. -/
private theorem duplicate_code : Step Cong (par (dd sourceName copyName sourceName) (par (ev copyName) (mm sourceName rebuildCode))) duplicationFreeStart := by
  refine Step.congruent
    (p' := par (par (dd sourceName copyName sourceName) (mm sourceName rebuildCode)) (ev copyName))
    (q' := par (par (mm copyName rebuildCode) (mm sourceName rebuildCode)) (ev copyName)) ?_ ?_ ?_
  · exact cong_of_perm (by decide)
  · exact Step.parLeft _ (Step.ofMinus (StepMinus.duplicate copyName sourceName rebuildCode (Cong.refl sourceName)))
  · exact cong_of_perm (by decide)

/-- The initially duplicator-free term returns to itself in four steps of the
full calculus. Its constructor creates the duplicator used by the final step. -/
theorem duplicationFreeStart_cycles : Relation.TransGen (Step Cong) duplicationFreeStart duplicationFreeStart :=
  Relation.TransGen.head open_code (Relation.TransGen.head construct_duplicator
    (Relation.TransGen.head open_duplicator (Relation.TransGen.single duplicate_code)))

/-- The same initially duplicator-free term admits arbitrarily many complete
rounds. The absence of a live duplicator is not a reduction-closed capability
restriction when code can build and open it. -/
theorem duplicationFreeStart_unbounded (rounds : Nat) :
    Chain duplicationFreeStart (4 * rounds) := by
  induction rounds with
  | zero => exact .nil _
  | succ rounds ih =>
      simpa only [Nat.mul_succ] using
        (Chain.cons open_code (Chain.cons construct_duplicator
          (Chain.cons open_duplicator (Chain.cons duplicate_code ih))))

/-- Strong normalization, read as accessibility of reversed reduction, fails
for the initially `dd`-free control. -/
theorem duplicationFreeStart_not_accessible :
    ¬ Acc (fun next current => Step Cong current next) duplicationFreeStart := by
  intro accessible
  have irrefl : ∀ (term : Comb),
      Acc (Relation.TransGen (fun next current => Step Cong current next)) term →
      ¬ Relation.TransGen (fun next current => Step Cong current next) term term := by
    intro term access
    induction access with
    | intro term _ ih =>
        intro loop
        exact ih term loop loop
  exact irrefl _ accessible.transGen
    (Relation.transGen_swap.mpr duplicationFreeStart_cycles)

end ConstructedDuplication

end TerminationControls

end Mettapedia.Languages.ProcessCalculi.RhoCombinators

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.weight_cong
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.nonMessageCount_not_strictly_decreasing
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.weight_lt_of_step
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.chain_length_le_weight
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.TerminationControls.relay_bounded

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.TerminationControls.ConstructedDuplication.duplicationFreeStart_has_no_dd
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.TerminationControls.ConstructedDuplication.duplicationFreeStart_cycles
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.TerminationControls.ConstructedDuplication.duplicationFreeStart_unbounded
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.TerminationControls.ConstructedDuplication.duplicationFreeStart_not_accessible
