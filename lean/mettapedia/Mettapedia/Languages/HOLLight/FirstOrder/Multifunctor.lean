import Mettapedia.Languages.HOLLight.FirstOrder.GraphSimulation
import Mettapedia.GSLT.LanguageDef.CertificateGSLTFreeMulticategory
import Mettapedia.Logic.RuleMulticategoryGraphs

/-!
# HOL Light's rule multicategory in its first-order calculus

HOL Light's kernel presents the free cartesian multicategory on its accepted
rule requests (`RuleWitness.signature (ruleWitness policy)`); its first-order
calculus presents the free cartesian multicategory on its rule applications
(`CertificateGSLT.ruleSignature`). Each HOL Light rule instance is translated
by the existing node step `ruleProof`, run on the canonical premise context
and checked by the calculus; the computable decoder turns the accepted raw
proof into a typed open derivation.

By freeness this determines a multifunctor (`translation`) over the rendering
of theorems as judgments. It preserves derivability (`translation_derivable`)
and, for admitted axiom lists, reflects it (`translation_reflects`): the
first-order calculus derives the rendering of a sequent exactly when HOL Light
derives a theorem with that sequent. Composite derivations are translated by
substitution into the rule images, so the translation of a proof tree is
determined by the translations of its rule instances.

The proof-graph translation `GraphSimulation.graphTranslate` realizes the same
rule images node by node with shared lemmas. Its exact agreement with this
multifunctor on unfolded graphs is not proved here.
-/

namespace Mettapedia.Languages.HOLLight.FirstOrder

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Logic
open Mettapedia.Logic.RuleSignature (Term Interpretation liftFunctor)
open Mettapedia.Languages.OpenTheory
open Mettapedia.GSLT.LanguageDef (ValidatedCalculusLanguageDef)

/-- The rendered judgment of a HOL Light theorem. -/
def renderTheorem (claim : Theorem) : Pattern := sequentJ claim.sequent

/-- Move a term from the mapped list context to the composite context. -/
def reindexMap {S : RuleSignature.{0, 0} Pattern} {α : Type} (f : α → Pattern) (l : List α)
    {b : Pattern} (t : Term S (l.map f).get b) : Term S (f ∘ l.get) b :=
  t.subst fun i =>
    (show f (l.get (Fin.cast (by simp) i)) = (l.map f).get i by simp) ▸
      Term.var (S := S) (Γ := f ∘ l.get) (Fin.cast (by simp) i)

section Calculus

variable {axioms : List Sequent} {definition : ValidatedCalculusLanguageDef}
  (calculus : definition.1 = holCalculus axioms)
  {policy : AxiomPolicy} [DecidablePred policy] (inList : ∀ sequent, policy sequent → sequent ∈ axioms)

include calculus inList in
/-- The node step accepts the rendering of every accepted rule instance on the
canonical premise context. -/
theorem generator_accepted (premises : List Theorem) (conclusion : Theorem)
    (rule : (ruleWitness policy).signature premises conclusion) :
    checkOpenRaw definition (premises.map renderTheorem) (renderTheorem conclusion)
      (ruleProof calculus (context := premises.map renderTheorem) (List.range premises.length)
        rule.1) = true := by
  obtain ⟨request, accepted⟩ := rule
  obtain ⟨same, semantics⟩ :=
    (RuleRequest.isInstance_eq_true_iff policy request premises conclusion).mp accepted
  subst same
  apply ruleProof_accepted calculus inList (List.range request.premises.length) request semantics
  intro index
  have position : (List.range request.premises.length).getD index 0 = index := by
    rw [List.getD_eq_getElem _ _ (by simp), List.getElem_range]
  rw [position, List.getElem?_map]
  simp [renderTheorem]

/-- The translation of one HOL Light rule instance: an open derivation of its
rendered conclusion from its rendered premises. -/
def generatorImage (premises : List Theorem) (conclusion : Theorem)
    (rule : (ruleWitness policy).signature premises conclusion) :
    Term (ruleSignature definition) (renderTheorem ∘ premises.get) (renderTheorem conclusion) :=
  reindexMap renderTheorem premises
    (decodeOpen definition (premises.map renderTheorem) (renderTheorem conclusion)
      (ruleProof calculus (context := premises.map renderTheorem) (List.range premises.length) rule.1)
      (generator_accepted calculus inList premises conclusion rule)).toTerm

/-- HOL Light's rule instances interpreted in the first-order calculus. -/
def interpretation :
    Interpretation (ruleWitness policy).signature (RuleSignature.free (ruleSignature definition))
      renderTheorem :=
  fun premises conclusion rule => generatorImage calculus inList premises conclusion rule

/-- **The translation multifunctor** from HOL Light's free rule multicategory to
the free multicategory of its first-order calculus. -/
def translation :
    (RuleSignature.free (ruleWitness policy).signature).Functor
      (RuleSignature.free (ruleSignature definition)) renderTheorem :=
  liftFunctor (interpretation calculus inList)

/-- The multifunctor is determined by its rule images. -/
theorem translation_unique
    (F : (RuleSignature.free (ruleWitness policy).signature).Functor
      (RuleSignature.free (ruleSignature definition)) renderTheorem)
    (onRules : ∀ premises conclusion (rule : (ruleWitness policy).signature premises conclusion),
      F.map (RuleSignature.gen rule) = generatorImage calculus inList premises conclusion rule) :
    F = translation calculus inList :=
  RuleSignature.universal.injective (funext fun premises => funext fun conclusion =>
    funext fun rule => (onRules premises conclusion rule).trans
      (RuleSignature.lift_gen (interpretation calculus inList) rule).symm)

include calculus inList in
/-- **Derivability is preserved.** -/
theorem translation_derivable {claim : Theorem} (derived : Derives (Rule policy) claim) :
    RuleSignature.Derivable (ruleSignature definition) (renderTheorem claim) :=
  RuleSignature.Derivable.map (interpretation calculus inList)
    ((RuleWitness.derivable_iff_derives (ruleWitness policy) claim).mpr derived)

/-- Closed derivations of the free multicategory are closed calculus derivations. -/
theorem derivable_iff_nonempty_derivation (goal : Pattern) :
    RuleSignature.Derivable (ruleSignature definition) goal ↔ Nonempty (Derivation definition goal) := by
  constructor
  · rintro ⟨t⟩
    let reclosed : Term (ruleSignature definition) ([] : List Pattern).get goal :=
      (RuleSignature.free (ruleSignature definition)).reclose t
    exact ⟨(ClassifyingContext.closedDerivationEquiv definition goal).symm
      (OpenDerivationList.cons (termToOpen reclosed) .nil)⟩
  · rintro ⟨derivation⟩
    have open_ : OpenDerivation definition [] goal := OpenDerivation.ofClosed derivation
    exact ⟨(RuleSignature.free (ruleSignature definition)).reclose open_.toTerm⟩

omit [DecidablePred policy] in
include calculus in
/-- **Derivability is reflected** for admitted axiom lists: a rendered sequent
derivable in the first-order calculus is the sequent of a HOL Light theorem. -/
theorem translation_reflects
    (admitted : ∀ sequent ∈ axioms, sequent.hyp = ∅ ∧ policy sequent ∧ sequent.IsBool)
    (inList : ∀ sequent, policy sequent → sequent ∈ axioms) (sequent : Sequent)
    (derivable : RuleSignature.Derivable (ruleSignature definition) (sequentJ sequent)) :
    ∃ out : Theorem, Derives (Rule policy) out ∧ out.sequent = sequent :=
  (holCalculus_exact calculus policy admitted inList sequent).mp
    ((derivable_iff_nonempty_derivation (sequentJ sequent)).mp derivable)

/-- **Shared translation of HOL Light graphs.** Every accepted HOL Light proof
graph translates node by node, one rule image per node, and the value at every
node is the multifunctor image of that node's unfolded derivation. Sharing is
preserved by the translation and commutes with it. -/
theorem shared_translation {Origin : Type} {nodes : List (Logic.DerivationGraph.Node Theorem RuleRequest Origin)}
    {cache : Array Theorem} (accepted : Logic.DerivationGraph.replay (ruleWitness policy) nodes = some cache) :
    ∃ terms : Array (Σ b, Term (ruleWitness policy).signature CartesianMulticategory.closedContext b),
      Logic.DerivationGraph.replayWith (RuleWitness.termStep (ruleWitness policy)) #[] nodes = some terms ∧
      terms.map Sigma.fst = cache ∧
      Logic.DerivationGraph.replayWith
          (RuleWitness.liftStep (ruleWitness policy) (interpretation calculus inList)) #[] nodes =
        some (terms.map (RuleWitness.liftEntry (ruleWitness policy) (interpretation calculus inList))) :=
  RuleWitness.shared_translation (ruleWitness policy) (interpretation calculus inList) accepted

include calculus in
/-- The declared translation time of the proof-graph translation charges at least
the weight of every lemma it writes, so it cannot be a zero clock. It remains a
declared account: its comparison and sorting terms are not derived from an
execution. -/
theorem graphTime_ge_weight : ∀ (earlier : List Pattern) (nodes : List ProofExecution.Receipt),
    Mettapedia.Languages.MM0.Translation.CalculusSimulation.lemmasWeight
        (graphLemmas calculus earlier nodes) ≤ graphTime calculus earlier nodes
  | _, [] => by
      simp [graphLemmas, Mettapedia.Languages.MM0.Translation.CalculusSimulation.lemmasWeight,
        graphTime]
  | earlier, node :: rest => by
      have later := graphTime_ge_weight (earlier ++ [sequentJ node.conclusion.sequent]) rest
      simp only [graphLemmas, Mettapedia.Languages.MM0.Translation.CalculusSimulation.lemmasWeight,
        graphTime]
      omega

end Calculus

namespace Kernel

open CalculusControls

/-- The translation multifunctor for HOL Light's bare kernel. -/
def translation :
    (RuleSignature.free (ruleWitness emptyAxiomPolicy).signature).Functor
      (RuleSignature.free (ruleSignature validated)) renderTheorem :=
  FirstOrder.translation (axioms := []) (definition := validated) rfl
    (policy := emptyAxiomPolicy) (fun _ impossible => impossible.elim)

/-- Positive control: `⊢ p = p` by `REFL` has a translated first-order derivation. -/
theorem reflexivity_translated :
    RuleSignature.Derivable (ruleSignature validated)
      (renderTheorem ProofExecution.Controls.reflexivityTheorem) := by
  apply FirstOrder.translation_derivable (axioms := []) (definition := validated) rfl
    (policy := emptyAxiomPolicy) (fun _ impossible => impossible.elim)
  exact (ProofSystem.checker_authority emptyAxiomPolicy).sound _ _
    ProofSystem.Controls.reflexivity_accepted

/-- Negative control: the rendering of `⊢ F` is not derivable in the first-order
calculus, since HOL Light's kernel does not derive it. -/
theorem falsity_not_translated :
    ¬ RuleSignature.Derivable (ruleSignature validated) (sequentJ ⟨∅, falsity⟩) := by
  intro derivable
  obtain ⟨out, derived, same⟩ := FirstOrder.translation_reflects (axioms := [])
    (definition := validated) rfl (policy := emptyAxiomPolicy)
    (fun _ member => absurd member (List.not_mem_nil)) (fun _ impossible => impossible.elim)
    ⟨∅, falsity⟩ derivable
  exact falsity_not_derivable (derives_shared emptyAxiomPolicy derived) same

end Kernel

end Mettapedia.Languages.HOLLight.FirstOrder
