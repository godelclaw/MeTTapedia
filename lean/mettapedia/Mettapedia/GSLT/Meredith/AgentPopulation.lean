import Mettapedia.GSLT.Meredith.InteractiveGSLT
import Mettapedia.GSLT.Meredith.Bisimulation
import Mettapedia.GSLT.Meredith.WeaknessBridge
import Mettapedia.GSLT.Meredith.RhoExample

/-! # Agent Population

A population of agents modeled as bisimulation classes of GSLT processes,
with interaction witnesses tracked between ordered pairs. -/

namespace Mettapedia.GSLT.Meredith

open Bisimulation

/-- Classical (noncomputable) decidability of equality for bisimulation quotients. -/
noncomputable instance bisimQuotientDecidableEq (S : GSLT) : DecidableEq (BisimQuotient S) :=
  Classical.decEq _

/-! # Agent Population -/

/-- An agent population: a finite set of agents (bisimulation classes)
    and a function assigning interaction witnesses to each ordered pair. -/
structure AgentPopulation (S : GSLT) (W : Type*) where
  agents : Finset (BisimQuotient S)
  interactions : BisimQuotient S → BisimQuotient S → List W

/-- A cost-tracked agent population using RhoDirectCutWitness as witness type. -/
structure CostTrackedAgentPopulation (S : GSLT) extends
    AgentPopulation S RhoExample.RhoDirectCutWitness

/-- An empty agent population: no agents, no interactions. -/
def emptyAgentPopulation (S : GSLT) (W : Type*) : AgentPopulation S W where
  agents := ∅
  interactions := fun _ _ => []

/-- A singleton agent population: one agent, no interactions. -/
def singletonAgentPopulation (S : GSLT) [DecidableEq (BisimQuotient S)]
    (a : BisimQuotient S) (W : Type*) : AgentPopulation S W where
  agents := {a}
  interactions := fun _ _ => []

/-- A two-agent population with a single directed interaction. -/
def twoAgentPopulation (S : GSLT) [DecidableEq (BisimQuotient S)]
    (W : Type*) (a b : BisimQuotient S) (_hab : a ≠ b) (w : W) :
    AgentPopulation S W where
  agents := {a, b}
  interactions := fun x y =>
    if x = a ∧ y = b then [w] else []

/-- Count total interaction witnesses across all agent pairs. -/
noncomputable def countInteractions (S : GSLT) (W : Type*)
    (pop : AgentPopulation S W) : Nat :=
  pop.agents.sum (fun a =>
    pop.agents.sum (fun b =>
      (pop.interactions a b).length))

/-! ## Concrete Example: ρ-Calculus Agent Population -/

/-- The empty cost-tracked agent population for the ρ-calculus. -/
def emptyRhoCostTrackedPopulation : CostTrackedAgentPopulation RhoExample.rhoGSLT where
  agents := ∅
  interactions := fun _ _ => []

/-- The empty population has zero interactions. -/
theorem countInteractions_empty (S : GSLT) (W : Type*) :
    countInteractions S W (emptyAgentPopulation S W) = 0 := by
  simp [countInteractions, emptyAgentPopulation]

/-- A singleton population has zero interactions. -/
theorem countInteractions_singleton (S : GSLT) [DecidableEq (BisimQuotient S)] (W : Type*) (a : BisimQuotient S) :
    countInteractions S W (singletonAgentPopulation S a W) = 0 := by
  simp [countInteractions, singletonAgentPopulation]

/-- A two-agent population with one directed interaction has exactly one. -/
theorem countInteractions_two (S : GSLT) [DecidableEq (BisimQuotient S)]
    (W : Type*) (a b : BisimQuotient S) (hab : a ≠ b) (w : W) :
    countInteractions S W (twoAgentPopulation S W a b hab w) = 1 := by
  simp [countInteractions, twoAgentPopulation, hab, hab.symm]

/-- Whether a population has any interactions at all. -/
noncomputable def hasInteractions (S : GSLT) (W : Type*)
    (pop : AgentPopulation S W) : Bool :=
  countInteractions S W pop > 0

/-- An empty population has no interactions. -/
theorem hasInteractions_empty (S : GSLT) (W : Type*) :
    hasInteractions S W (emptyAgentPopulation S W) = false := by
  simp [hasInteractions, countInteractions_empty]

/-- A singleton population has no interactions. -/
theorem hasInteractions_singleton (S : GSLT) [DecidableEq (BisimQuotient S)]
    (W : Type*) (a : BisimQuotient S) :
    hasInteractions S W (singletonAgentPopulation S a W) = false := by
  simp [hasInteractions, countInteractions_singleton]

/-- Two-agent population: has interactions (one from a to b). -/
theorem hasInteractions_two (S : GSLT) [DecidableEq (BisimQuotient S)]
    (W : Type*) (a b : BisimQuotient S) (hab : a ≠ b) (w : W) :
    hasInteractions S W (twoAgentPopulation S W a b hab w) = true := by
  simp [hasInteractions, countInteractions_two]

/-- The empty ρ-cost-tracked population has zero interactions. -/
theorem countInteractions_emptyRhoCostTracked :
    countInteractions RhoExample.rhoGSLT RhoExample.RhoDirectCutWitness
      emptyRhoCostTrackedPopulation.toAgentPopulation = 0 := by
  simp [countInteractions, emptyRhoCostTrackedPopulation]

/-- The empty ρ-cost-tracked population has no interactions. -/
theorem hasInteractions_emptyRhoCostTracked :
    hasInteractions RhoExample.rhoGSLT RhoExample.RhoDirectCutWitness
      emptyRhoCostTrackedPopulation.toAgentPopulation = false := by
  simp [hasInteractions, countInteractions_emptyRhoCostTracked]

/-- A singleton cost-tracked population for the ρ-calculus. -/
noncomputable def singletonRhoCostTrackedPopulation (a : BisimQuotient RhoExample.rhoGSLT) :
    CostTrackedAgentPopulation RhoExample.rhoGSLT :=
  { agents := {a}
    interactions := fun _ _ => [] }

/-- A singleton cost-tracked population has zero interactions. -/
theorem countInteractions_singletonRhoCostTracked (a : BisimQuotient RhoExample.rhoGSLT) :
    countInteractions RhoExample.rhoGSLT RhoExample.RhoDirectCutWitness
      (singletonRhoCostTrackedPopulation a).toAgentPopulation = 0 := by
  simp [countInteractions, singletonRhoCostTrackedPopulation]

/-- A singleton cost-tracked population has no interactions. -/
theorem hasInteractions_singletonRhoCostTracked (a : BisimQuotient RhoExample.rhoGSLT) :
    hasInteractions RhoExample.rhoGSLT RhoExample.RhoDirectCutWitness
      (singletonRhoCostTrackedPopulation a).toAgentPopulation = false := by
  simp [hasInteractions, countInteractions_singletonRhoCostTracked]

/-- A two-agent cost-tracked population for the ρ-calculus (no interactions). -/
noncomputable def twoRhoCostTrackedPopulation
    (a b : BisimQuotient RhoExample.rhoGSLT) (_hab : a ≠ b) :
    CostTrackedAgentPopulation RhoExample.rhoGSLT :=
  { agents := {a, b}
    interactions := fun _ _ => [] }

/-- A two-agent cost-tracked population has zero interactions. -/
theorem countInteractions_twoRhoCostTracked
    (a b : BisimQuotient RhoExample.rhoGSLT) (hab : a ≠ b) :
    countInteractions RhoExample.rhoGSLT RhoExample.RhoDirectCutWitness
      (twoRhoCostTrackedPopulation a b hab).toAgentPopulation = 0 := by
  simp [countInteractions, twoRhoCostTrackedPopulation]

/-- A two-agent cost-tracked population has no interactions. -/
theorem hasInteractions_twoRhoCostTracked
    (a b : BisimQuotient RhoExample.rhoGSLT) (hab : a ≠ b) :
    hasInteractions RhoExample.rhoGSLT RhoExample.RhoDirectCutWitness
      (twoRhoCostTrackedPopulation a b hab).toAgentPopulation = false := by
  simp [hasInteractions, countInteractions_twoRhoCostTracked]

/-- Two bisimulation classes are distinguished when they are distinct. -/
def IsDistinguishedClass (S : GSLT) (a b : BisimQuotient S) : Prop := a ≠ b

/-- A consciousness candidate: a cluster of bisimulation classes containing a
self that distinguishes itself from an environment outside the cluster. -/
structure ConsciousnessCandidate (S : GSLT) where
  cluster : Set (BisimQuotient S)
  self : BisimQuotient S
  self_mem : self ∈ cluster
  env : BisimQuotient S
  env_not_mem : env ∉ cluster
  selfDistinguishing : IsDistinguishedClass S self env

/-- The self of a consciousness candidate is never its environment. -/
theorem ConsciousnessCandidate.self_ne_env {S : GSLT}
    (c : ConsciousnessCandidate S) : c.self ≠ c.env :=
  c.selfDistinguishing

/-- A coherent consciousness candidate: a consciousness candidate equipped with
quantale-valued evidence whose non-distinction weakness (self-similarity)
meets a coherence threshold. -/
structure CoherentCandidate (S : GSLT) (Q : Type*)
    [Fintype (BisimQuotient S)] [DecidableEq (BisimQuotient S)]
    [Monoid Q] [CompleteLattice Q] extends ConsciousnessCandidate S where
  evidence : WeaknessBridge.GSLTEvidence (BisimQuotient S) Q
  threshold : Q
  coherent : threshold ≤ WeaknessBridge.nonDistinctionWeakness evidence

/-- A coherent candidate still distinguishes its self from its environment. -/
theorem CoherentCandidate.self_ne_env {S : GSLT} {Q : Type*}
    [Fintype (BisimQuotient S)] [DecidableEq (BisimQuotient S)]
    [Monoid Q] [CompleteLattice Q]
    (c : CoherentCandidate S Q) : c.self ≠ c.env :=
  c.selfDistinguishing

/-- A toy finite GSLT on `Bool`: `true` can loop, `false` is stuck.
Equations are plain equality; the single rewrite rule is `true → true`. -/
def toyGSLT : GSLT where
  Term := Bool
  equations := { r := Eq, iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩ }
  rewrites := fun t u => t = true ∧ u = true
  rewrites_resp_left := by
    intro t t' u h hstep
    cases h
    exact ⟨u, hstep, rfl⟩
  rewrites_resp_right := by
    intro t u u' hstep h
    cases h
    exact hstep

/-- In the toy GSLT, `true` steps to itself. -/
theorem toy_step_true : toyGSLT.Step true true := ⟨rfl, rfl⟩

/-- In the toy GSLT, `false` is stuck: it admits no step. -/
theorem toy_false_stuck : ∀ u, ¬ toyGSLT.Step false u :=
  fun _ h => Bool.noConfusion h.1

/-- `true` and `false` are not bisimilar in the toy GSLT: `true` can step
but `false` cannot answer. -/
theorem toy_not_bisim : ¬ toyGSLT.Bisimilar true false := by
  rintro ⟨R, ⟨hfwd, _⟩, hR⟩
  obtain ⟨u', hstep, _⟩ := hfwd hR toy_step_true
  exact toy_false_stuck u' hstep

/-- The bisimulation classes of `true` and `false` are distinct. -/
theorem toy_classes_ne :
    toBisimClass toyGSLT true ≠ toBisimClass toyGSLT false := fun h =>
  toy_not_bisim (Quotient.exact h)

/-- A concrete consciousness candidate: in the toy GSLT, the class of the
looping term `true` distinguishes itself from the stuck environment `false`. -/
def toyCandidate : ConsciousnessCandidate toyGSLT where
  cluster := {toBisimClass toyGSLT true}
  self := toBisimClass toyGSLT true
  self_mem := Set.mem_singleton _
  env := toBisimClass toyGSLT false
  env_not_mem := fun h => toy_classes_ne (Set.mem_singleton_iff.mp h).symm
  selfDistinguishing := toy_classes_ne

instance : Fintype toyGSLT.Term := inferInstanceAs (Fintype Bool)

/-- The toy GSLT has a finite bisimulation quotient (classically). -/
noncomputable instance : Fintype (BisimQuotient toyGSLT) := by
  classical
  exact Quotient.fintype _

noncomputable instance : DecidableEq (BisimQuotient toyGSLT) :=
  Classical.decEq _

/-- With uniform unit evidence, the non-distinction weakness over the toy
quotient is exactly `1`: the diagonal event is nonempty and every product is `1`. -/
theorem toy_nonDistinctionWeakness_eq_one :
    WeaknessBridge.nonDistinctionWeakness
      (⟨fun _ => 1⟩ : WeaknessBridge.GSLTEvidence (BisimQuotient toyGSLT) ENNReal) = 1 := by
  unfold WeaknessBridge.nonDistinctionWeakness WeaknessBridge.gsltWeakness
    Mettapedia.Algebra.QuantaleWeakness.weakness
  apply le_antisymm
  · apply sSup_le
    rintro x ⟨p, _, rfl⟩
    simp [WeaknessBridge.GSLTEvidence.toWeightFn]
  · apply le_sSup
    exact ⟨(toBisimClass toyGSLT true, toBisimClass toyGSLT true),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
      by simp [WeaknessBridge.GSLTEvidence.toWeightFn]⟩

/-- A concrete coherent candidate with a *non-trivial* threshold: uniform
`ENNReal` evidence gives non-distinction weakness exactly `1`, and the
candidate is coherent at that exact level. -/
noncomputable def toyCoherent : CoherentCandidate toyGSLT ENNReal :=
  { toyCandidate with
    evidence := ⟨fun _ => 1⟩
    threshold := 1
    coherent := le_of_eq toy_nonDistinctionWeakness_eq_one.symm }

/-- Non-uniform evidence: the self-class weighs `2`, every other class `1`. -/
noncomputable def toyEvidence2 :
    WeaknessBridge.GSLTEvidence (BisimQuotient toyGSLT) ENNReal :=
  ⟨fun c => if c = toBisimClass toyGSLT true then 2 else 1⟩

/-- With non-uniform weighting the non-distinction weakness rises to `4`:
the self-diagonal pair contributes `2·2`, so the measure genuinely varies. -/
theorem toy_nonDistinctionWeakness_two_eq_four :
    WeaknessBridge.nonDistinctionWeakness toyEvidence2 = 4 := by
  unfold WeaknessBridge.nonDistinctionWeakness WeaknessBridge.gsltWeakness
    Mettapedia.Algebra.QuantaleWeakness.weakness
  apply le_antisymm
  · apply sSup_le
    rintro x ⟨p, _, rfl⟩
    simp only [toyEvidence2, WeaknessBridge.GSLTEvidence.toWeightFn]
    split_ifs <;> norm_num
  · apply le_sSup
    exact ⟨(toBisimClass toyGSLT true, toBisimClass toyGSLT true),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
      by simp only [toyEvidence2, WeaknessBridge.GSLTEvidence.toWeightFn]; norm_num⟩

/-- Monotonicity: pointwise larger evidence yields larger non-distinction weakness. -/
theorem nonDistinctionWeakness_mono {U : Type*} [Fintype U] [DecidableEq U]
    (ev₁ ev₂ : WeaknessBridge.GSLTEvidence U ENNReal)
    (h : ∀ c, ev₁.weight c ≤ ev₂.weight c) :
    WeaknessBridge.nonDistinctionWeakness ev₁ ≤
      WeaknessBridge.nonDistinctionWeakness ev₂ := by
  unfold WeaknessBridge.nonDistinctionWeakness WeaknessBridge.gsltWeakness
    Mettapedia.Algebra.QuantaleWeakness.weakness
  apply sSup_le
  rintro x ⟨p, hp, rfl⟩
  refine le_trans ?_ (le_sSup ⟨p, hp, rfl⟩)
  simp only [WeaknessBridge.GSLTEvidence.toWeightFn]
  exact mul_le_mul' (h _) (h _)

open RhoExample
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## A finite fragment of the ρ-calculus

We carve out a two-term fragment of the real ρ-calculus: a COMM redex and its
reduct. The GSLT structure is pulled back along the embedding. -/

/-- Two-term fragment: a COMM redex and its reduct. -/
inductive FragTerm : Type
  | redex
  | reduct
  deriving DecidableEq, Fintype

/-- Embed the fragment into ρ-calculus patterns. -/
def fragEmbed : FragTerm → Pattern
  | .redex => .collection .hashBag
      [.apply "POutput" [nilProcess, nilProcess],
       .apply "PInput" [nilProcess, .lambda none nilProcess]] none
  | .reduct => .collection .hashBag [semanticCommSubst nilProcess nilProcess] none

/-- The fragment GSLT: equations and rewrites pulled back along `fragEmbed`.
All dynamics are genuine ρ-calculus dynamics. -/
def fragGSLT : GSLT where
  Term := FragTerm
  equations := Setoid.comap fragEmbed rhoEquivSetoid
  rewrites t u := rhoRewrites (fragEmbed t) (fragEmbed u)
  rewrites_resp_left := by
    intro t tt u h hstep
    obtain ⟨r⟩ := hstep
    exact ⟨u,
      ⟨Reduces.equiv (StructuralCongruence.symm _ _ h) r (StructuralCongruence.refl _)⟩,
      StructuralCongruence.refl _⟩
  rewrites_resp_right := by
    intro t u uu hstep h
    obtain ⟨r⟩ := hstep
    exact ⟨Reduces.equiv (StructuralCongruence.refl _) r h⟩

/-- The fragment really steps: the COMM redex reduces to its reduct,
via the genuine ρ-calculus COMM rule. -/
theorem frag_step : fragGSLT.Step .redex .reduct :=
  ⟨Reduces.comm⟩

instance : Fintype fragGSLT.Term := inferInstanceAs (Fintype FragTerm)

/-- The fragment has a finite bisimulation quotient (classically). -/
noncomputable instance : Fintype (BisimQuotient fragGSLT) := by
  classical
  exact Quotient.fintype _

noncomputable instance : DecidableEq (BisimQuotient fragGSLT) :=
  Classical.decEq _

/-- COMM substitution of nil into nil is nil. -/
theorem frag_subst_nil : semanticCommSubst nilProcess nilProcess = nilProcess := rfl

/-- The reduct is stuck: its bag is SC-equivalent to the empty bag. -/
theorem frag_reduct_stuck (u : FragTerm) : ¬ fragGSLT.rewrites .reduct u := by
  intro hstep
  obtain ⟨r⟩ := hstep
  have hsub := frag_subst_nil
  have hsc : StructuralCongruence (.collection .hashBag [] none) (fragEmbed .reduct) := by
    show StructuralCongruence (.collection .hashBag [] none)
      (.collection .hashBag [semanticCommSubst nilProcess nilProcess] none)
    rw [hsub]
    exact StructuralCongruence.trans _ _ _ StructuralCongruence.par_empty
      (StructuralCongruence.symm _ _ (StructuralCongruence.par_singleton _))
  exact emptyBag_SC_irreducible hsc r

/-- The COMM redex and its reduct are not bisimilar: the redex steps, the reduct is stuck. -/
theorem frag_not_bisim : ¬ fragGSLT.Bisimilar .redex .reduct := by
  rintro ⟨R, ⟨hfwd, _⟩, hR⟩
  obtain ⟨u', hstep, _⟩ := hfwd hR frag_step
  exact frag_reduct_stuck u' hstep

/-- The bisimulation classes of the redex and reduct are distinct. -/
theorem frag_classes_ne :
    toBisimClass fragGSLT .redex ≠ toBisimClass fragGSLT .reduct := fun h =>
  frag_not_bisim (Quotient.exact h)

/-- A consciousness candidate living inside the real ρ-calculus: the class of
the COMM redex distinguishes itself from its stuck reduct environment. -/
def fragCandidate : ConsciousnessCandidate fragGSLT where
  cluster := {toBisimClass fragGSLT .redex}
  self := toBisimClass fragGSLT .redex
  self_mem := Set.mem_singleton _
  env := toBisimClass fragGSLT .reduct
  env_not_mem := fun h => frag_classes_ne (Set.mem_singleton_iff.mp h).symm
  selfDistinguishing := frag_classes_ne

/-- Uniform evidence over the fragment's bisimulation quotient. -/
noncomputable def fragEvidence :
    WeaknessBridge.GSLTEvidence (BisimQuotient fragGSLT) ENNReal :=
  ⟨fun _ => 1⟩

/-- With uniform unit evidence, the fragment's non-distinction weakness is exactly `1`. -/
theorem frag_nonDistinctionWeakness_eq_one :
    WeaknessBridge.nonDistinctionWeakness fragEvidence = 1 := by
  unfold WeaknessBridge.nonDistinctionWeakness WeaknessBridge.gsltWeakness
    Mettapedia.Algebra.QuantaleWeakness.weakness
  apply le_antisymm
  · apply sSup_le
    rintro x ⟨p, _, rfl⟩
    simp [fragEvidence, WeaknessBridge.GSLTEvidence.toWeightFn]
  · apply le_sSup
    exact ⟨(toBisimClass fragGSLT .redex, toBisimClass fragGSLT .redex),
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩,
      by simp [fragEvidence, WeaknessBridge.GSLTEvidence.toWeightFn]⟩

/-- A coherent consciousness candidate living inside the real ρ-calculus:
the COMM redex's class, certified coherent (trivial threshold for now). -/
noncomputable def fragCoherent : CoherentCandidate fragGSLT ENNReal :=
  { fragCandidate with
    evidence := fragEvidence
    threshold := 1
    coherent := le_of_eq frag_nonDistinctionWeakness_eq_one.symm }

end Mettapedia.GSLT.Meredith
