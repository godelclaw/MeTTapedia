import Mettapedia.Languages.HOLLight.ChronologicalDriver

/-!
# Exact chronological controller correspondence

The actual task controller simulates the existing recursive source compiler by
mutual induction. Every admitted source in the proven first-order host region
completes within its syntax-derived task budget and returns exactly the original
compiler certificate. Saved roots and child/lemma occurrence order are retained.

The task count and emitted node count have linear bounds in the original encoded
input. Source admission and original binary-machine execution cost remain
separate obligations; one closing task can emit and replay many HOL requests.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.ChronologicalDriver.Correctness

open Mettapedia.Logic
open Mettapedia.Languages.MM0.Translation.CalculusSimulation
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.InferenceHosting
open Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation
open Mettapedia.Languages.HOLLight.InferenceCompiler

variable (definition : ValidatedCalculusLanguageDef)

mutual
  def visitBudget : RawOpenProof → Nat
    | .premise _ => 1
    | .node _ proofs => 2 + childrenBudget proofs
  termination_by proof => sizeOf proof
  def childrenBudget : List RawOpenProof → Nat
    | [] => 0
    | proof :: proofs => visitBudget proof + childrenBudget proofs
  termination_by proofs => sizeOf proofs
end

def lemmaBudget : Lemmas → Nat
  | [] => 0
  | (_, proof) :: rest => visitBudget proof + 1 + lemmaBudget rest

def totalBudget (source : LemmaCertificate) : Nat :=
  lemmaBudget source.1 + visitBudget source.2 + 1

mutual
  def visitSites (site : Site) : RawOpenProof → List Site
    | .premise _ => [site]
    | .node _ proofs => childrenSites site 0 proofs ++ [site]
  termination_by proof => sizeOf proof
  def childrenSites (site : Site) : Nat → List RawOpenProof → List Site
    | _, [] => []
    | index, proof :: proofs =>
        visitSites ⟨site.origin, site.path ++ [index]⟩ proof ++ childrenSites site (index + 1) proofs
  termination_by _ proofs => sizeOf proofs
end

def goals {checkedPrefix : Prefix definition} (claims : List (Claim definition checkedPrefix)) : List Pattern :=
  claims.map (fun claim => claim.goal)
def roots {checkedPrefix : Prefix definition} (claims : List (Claim definition checkedPrefix)) : List Nat :=
  claims.map (fun claim => claim.root)
def sites (state : State definition) : List Site := state.occurrences.map Prod.fst

@[simp] theorem goals_keep {before after : Prefix definition} (kept : KeepsOld before.val after.val)
    (claims : List (Claim definition before)) :
    goals definition (claims.map (Claim.keep definition kept)) = goals definition claims := by
  simp only [goals, List.map_map, Function.comp_def, Claim.keep_goal]

@[simp] theorem roots_keep {before after : Prefix definition} (kept : KeepsOld before.val after.val)
    (claims : List (Claim definition before)) :
    roots definition (claims.map (Claim.keep definition kept)) = roots definition claims :=
  kept_root_vector definition kept claims

theorem claimAt_complete (checkedPrefix : Prefix definition) (goal : Pattern) (root : Nat)
    (out : Theorem) (found : checkedPrefix.val.cache[root]? = some out)
    (valid : hasClaim goal out = true) :
    ∃ claim, claimAt? definition checkedPrefix goal root = some claim ∧
      claim.goal = goal ∧ claim.root = root ∧ claim.out = out := by
  refine ⟨⟨goal, root, out, found, valid⟩, ?_, rfl, rfl, rfl⟩
  unfold claimAt?
  split
  next missing => simp [missing] at found
  next actual selected =>
    have same : actual = out := Option.some.inj (selected.symm.trans found)
    subst actual
    simp only [valid, ↓reduceDIte]

theorem lookup_claim_roots (checkedPrefix : Prefix definition)
    (claims : List (Claim definition checkedPrefix)) :
    DerivationGraph.lookupPremises checkedPrefix.val.cache (roots definition claims) =
      some (claims.map (fun claim => claim.out)) := by
  induction claims with
  | nil => rfl
  | cons claim claims ih =>
      simp only [roots, List.map_cons, DerivationGraph.lookupPremises, claim.found]
      simp only [roots] at ih
      simp only [ih]
      rfl

theorem selected_goals {checkedPrefix : Prefix definition} (claims : List (Claim definition checkedPrefix))
    (premises tail : List Pattern) (ordered : goals definition claims = premises.reverse ++ tail) :
    goals definition ((claims.take premises.length).reverse) = premises := by
  simp only [goals, List.map_reverse, List.map_take]
  rw [← goals, ordered]
  simp

theorem dropped_goals {checkedPrefix : Prefix definition} (claims : List (Claim definition checkedPrefix))
    (premises tail : List Pattern) (ordered : goals definition claims = premises.reverse ++ tail) :
    goals definition (claims.drop premises.length) = tail := by
  simp only [goals, List.map_drop]
  rw [← goals, ordered]
  simp

theorem selected_roots {checkedPrefix : Prefix definition} (claims : List (Claim definition checkedPrefix))
    (childRoots tail : List Nat) (ordered : roots definition claims = childRoots.reverse ++ tail) :
    roots definition ((claims.take childRoots.length).reverse) = childRoots := by
  simp only [roots, List.map_reverse, List.map_take]
  rw [← roots, ordered]
  simp

theorem dropped_roots {checkedPrefix : Prefix definition} (claims : List (Claim definition checkedPrefix))
    (childRoots tail : List Nat) (ordered : roots definition claims = childRoots.reverse ++ tail) :
    roots definition (claims.drop childRoots.length) = tail := by
  simp only [roots, List.map_drop]
  rw [← roots, ordered]
  simp


theorem goals_length {checkedPrefix : Prefix definition}
    (claims : List (Claim definition checkedPrefix)) :
    (goals definition claims).length = claims.length := List.length_map _

theorem roots_length {checkedPrefix : Prefix definition}
    (claims : List (Claim definition checkedPrefix)) :
    (roots definition claims).length = claims.length := List.length_map _

theorem extend_complete (before : Prefix definition) (childRoots : List Nat)
    (block : ProofSystem.Certificate) (after : ProofExecution.State) (root : Nat)
    (emitted : GraphExpansion.emitBlock (policy (inferenceRules definition.1))
      childRoots block before.val = some (after, root)) :
    ∃ extension, extend? definition before childRoots block = some extension ∧
      extension.after.val = after ∧ extension.root = root := by
  unfold extend?
  split
  next missing => simp [missing] at emitted
  next actualAfter actualRoot selected =>
    have same : (actualAfter, actualRoot) = (after, root) := Option.some.inj (selected.symm.trans emitted)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
    exact ⟨_, rfl, rfl, rfl⟩

theorem checkOpenRawChildren_length (context : List Pattern) :
    ∀ (childGoals : List Pattern) (proofs : List RawOpenProof),
      checkOpenRawChildren definition context childGoals proofs = true → childGoals.length = proofs.length
  | [], [], _ => rfl
  | _ :: _, [], accepted => by simp [checkOpenRawChildren] at accepted
  | [], _ :: _, accepted => by simp [checkOpenRawChildren] at accepted
  | _ :: childGoals, _ :: proofs, accepted => by
      simp only [checkOpenRawChildren, Bool.and_eq_true] at accepted
      exact congrArg Nat.succ (checkOpenRawChildren_length context childGoals proofs accepted.2)

end Mettapedia.Languages.HOLLight.ChronologicalDriver.Correctness

namespace Mettapedia.Languages.HOLLight.ChronologicalDriver.Correctness

open Mettapedia.Logic Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.CertificateGSLT Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.InferenceHosting
open Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation
open Mettapedia.Languages.HOLLight.InferenceCompiler

variable (definition : ValidatedCalculusLanguageDef)

theorem close_step (state : State definition) (goal : Pattern) (ruleInstance : RuleInstance)
    (premises : List Pattern) (site : Site) (rest : List Task)
    (childRoots tailRoots : List Nat) (tailGoals : List Pattern)
    (inputs : List Theorem) (block : ProofSystem.Certificate)
    (after : ProofExecution.State) (root : Nat) (out : Theorem)
    (work : state.todo = .close goal ruleInstance premises site :: rest)
    (orderedGoals : goals definition state.values = premises.reverse ++ tailGoals)
    (orderedRoots : roots definition state.values = childRoots.reverse ++ tailRoots)
    (arity : childRoots.length = premises.length)
    (selected : DerivationGraph.lookupPremises state.checkedPrefix.val.cache childRoots = some inputs)
    (generated : InferenceRuleExpansion.emitRule? definition ruleInstance inputs site.origin = some block)
    (emitted : GraphExpansion.emitBlock (policy (inferenceRules definition.1)) childRoots block
      state.checkedPrefix.val = some (after, root))
    (found : after.cache[root]? = some out) (valid : hasClaim goal out = true) :
    ∃ next, step definition (.running state) = .running next ∧
      next.checkedPrefix.val = after ∧ next.todo = rest ∧
      goals definition next.values = goal :: tailGoals ∧
      roots definition next.values = root :: tailRoots ∧
      goals definition next.saved = goals definition state.saved ∧
      roots definition next.saved = roots definition state.saved ∧
      sites definition next = sites definition state ++ [site] := by
  have enough : premises.length ≤ state.values.length := by
    have lengths := congrArg List.length orderedGoals
    simp only [goals_length, List.length_append, List.length_reverse] at lengths
    omega
  let chosen := (state.values.take premises.length).reverse
  have chosenGoals : goals definition chosen = premises := selected_goals definition _ _ _ orderedGoals
  have chosenRoots : roots definition chosen = childRoots := by
    simpa only [arity] using selected_roots definition state.values childRoots tailRoots orderedRoots
  have chosenInputs : chosen.map (fun claim => claim.out) = inputs := by
    have lookup := lookup_claim_roots definition state.checkedPrefix chosen
    rw [chosenRoots, selected] at lookup
    exact Option.some.inj lookup.symm
  obtain ⟨extension, extended, afterEq, rootEq⟩ :=
    extend_complete definition state.checkedPrefix childRoots block after root emitted
  have found' : extension.after.val.cache[extension.root]? = some out := by simpa [afterEq, rootEq] using found
  obtain ⟨claim, claimed, claimGoal, claimRoot, _⟩ :=
    claimAt_complete definition extension.after goal extension.root out found' valid
  let base : State definition :=
    { checkedPrefix := extension.after
      todo := rest
      values := (state.values.drop premises.length).map (Claim.keep definition extension.kept)
      saved := state.saved.map (Claim.keep definition extension.kept)
      occurrences := state.occurrences.map fun occurrence =>
        (occurrence.1, Claim.keep definition extension.kept occurrence.2) }
  refine ⟨remember definition base site claim rest, ?_, afterEq, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · have chosenGoals' := chosenGoals
    have chosenRoots' := chosenRoots
    have chosenInputs' := chosenInputs
    simp only [goals, chosen] at chosenGoals'
    simp only [roots, chosen] at chosenRoots'
    simp only [chosen] at chosenInputs'
    simp only [step, work, enough, ↓reduceIte, chosenGoals', chosenInputs', generated,
      chosenRoots', extended, claimed]
    rfl
  · simp only [remember, base, goals, List.map_cons, claimGoal]
    rw [← goals, goals_keep, dropped_goals definition _ _ _ orderedGoals]
  · simp only [remember, base, roots, List.map_cons, claimRoot, rootEq]
    rw [← roots, roots_keep]
    simpa only [arity] using congrArg (List.cons root)
      (dropped_roots definition state.values childRoots tailRoots orderedRoots)
  · exact goals_keep definition extension.kept state.saved
  · exact roots_keep definition extension.kept state.saved
  · simp only [sites, remember, base, List.map_append, List.map_cons, List.map_nil,
      List.map_map, Function.comp_def]

end Mettapedia.Languages.HOLLight.ChronologicalDriver.Correctness

namespace Mettapedia.Languages.HOLLight.ChronologicalDriver.Correctness

open Mettapedia.Logic Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight.InferenceCompiler
open Mettapedia.Languages.HOLLight.InferenceHosting
open Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation

variable (definition : ValidatedCalculusLanguageDef)

mutual
  theorem visit_simulation :
    ∀ (goal : Pattern) (proof : RawOpenProof) (state : State definition)
      (site : Site) (rest : List Task) (after : ProofExecution.State) (root : Nat),
      state.todo = .visit goal proof site :: rest →
      checkOpenRaw definition (goals definition state.saved) goal proof = true →
      compileOpenWith definition (InferenceRuleExpansion.emitRule? definition)
        (roots definition state.saved) site.origin goal proof state.checkedPrefix.val = some (after, root) →
      ∃ next, run definition (visitBudget proof) (.running state) = .running next ∧
        next.checkedPrefix.val = after ∧ next.todo = rest ∧
        goals definition next.values = goal :: goals definition state.values ∧
        roots definition next.values = root :: roots definition state.values ∧
        goals definition next.saved = goals definition state.saved ∧
        roots definition next.saved = roots definition state.saved ∧
        sites definition next = sites definition state ++ visitSites site proof
    | goal, .premise index, state, site, rest, after, root, work, accepted, compiled => by
        cases savedFound : state.saved[index]? with
        | none => simp [checkOpenRaw, goals, List.getElem?_map, savedFound] at accepted
        | some claim =>
            have same : claim.goal = goal := by
              simpa [checkOpenRaw, goals, List.getElem?_map, savedFound] using accepted
            have equality : (state.checkedPrefix.val, claim.root) = (after, root) := by
              simpa [compileOpenWith, roots, List.getElem?_map, savedFound, claim.found,
                ← same, claim.represents] using compiled
            obtain ⟨afterEq, rootEq⟩ := Prod.mk.inj equality
            refine ⟨remember definition state site claim rest, ?_, afterEq, rfl, ?_, ?_, rfl, rfl, ?_⟩
            · simp only [visitBudget, run, step, work, savedFound, same, ↓reduceIte]
            · simp only [remember, goals, List.map_cons, same]
            · simp only [remember, roots, List.map_cons, rootEq]
            · simp only [remember, sites, List.map_append, List.map_cons, List.map_nil, visitSites]
    | goal, .node ruleInstance proofs, state, site, rest, after, root, work, accepted, compiled => by
        cases instantiated : instantiateRule? definition ruleInstance with
        | none => simp [checkOpenRaw, instantiated] at accepted
        | some pair =>
            obtain ⟨premises, conclusion⟩ := pair
            simp only [checkOpenRaw, instantiated, Bool.and_eq_true, decide_eq_true_eq] at accepted
            obtain ⟨sameGoal, childrenAccepted⟩ := accepted
            cases childrenEmitted : compileChildrenWith definition (InferenceRuleExpansion.emitRule? definition)
                (roots definition state.saved) site.origin premises proofs state.checkedPrefix.val with
            | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted] at compiled
            | some pair =>
                obtain ⟨middle, childRoots⟩ := pair
                cases selected : DerivationGraph.lookupPremises middle.cache childRoots with
                | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted, selected] at compiled
                | some inputs =>
                    cases generated : InferenceRuleExpansion.emitRule? definition ruleInstance inputs site.origin with
                    | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted, selected, generated] at compiled
                    | some block =>
                        cases emitted : GraphExpansion.emitBlock (policy (inferenceRules definition.1)) childRoots block middle with
                        | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted, selected, generated, emitted] at compiled
                        | some pair =>
                            obtain ⟨actual, actualRoot⟩ := pair
                            cases found : actual.cache[actualRoot]? with
                            | none => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted, selected, generated, emitted, found] at compiled
                            | some out =>
                                cases valid : hasClaim goal out with
                                | false => simp [compileOpenWith, instantiated, sameGoal, childrenEmitted, selected, generated, emitted, found, valid] at compiled
                                | true =>
                                    have equality : (actual, actualRoot) = (after, root) := by
                                      simpa [compileOpenWith, instantiated, sameGoal, childrenEmitted, selected, generated, emitted, found, valid] using compiled
                                    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equality
                                    have arity : premises.length = proofs.length :=
                                      checkOpenRawChildren_length definition _ _ _ childrenAccepted
                                    let queued : State definition := { state with todo := children site 0 (premises.zip proofs) ++ .close goal ruleInstance premises site :: rest }
                                    have first : step definition (.running state) = .running queued := by
                                      simp only [step, work, instantiated, sameGoal, ↓reduceIte, arity]
                                      rfl
                                    obtain ⟨visited, ranChildren, prefixEq, visitedWork, visitedGoals, visitedRoots,
                                      savedGoals, savedRoots, visitedSites⟩ :=
                                      children_simulation premises proofs queued site 0
                                        (.close goal ruleInstance premises site :: rest) middle childRoots rfl childrenAccepted childrenEmitted
                                    have rootsArity : childRoots.length = premises.length := by
                                      have represented := compileChildrenWith_represents definition (InferenceRuleExpansion.emitRule? definition)
                                        (roots definition state.saved) site.origin [] premises proofs state.checkedPrefix.val
                                        middle childRoots state.checkedPrefix.property childrenEmitted
                                      exact represented.length_eq.symm
                                    obtain ⟨next, closed, finalPrefix, finalWork, finalGoals, finalRoots,
                                      finalSavedGoals, finalSavedRoots, finalSites⟩ :=
                                      close_step definition visited goal ruleInstance premises site rest childRoots
                                        (roots definition state.values) (goals definition state.values) inputs block actual actualRoot out
                                        visitedWork visitedGoals visitedRoots rootsArity
                                        (by simpa only [prefixEq] using selected) generated
                                        (by simpa only [prefixEq] using emitted) found valid
                                    refine ⟨next, ?_, finalPrefix, finalWork, finalGoals, finalRoots, ?_, ?_, ?_⟩
                                    · rw [visitBudget, show 2 + childrenBudget proofs = (childrenBudget proofs + 1) + 1 by omega, run]
                                      rw [first, run_add, ranChildren]
                                      simpa only [run] using closed
                                    · exact finalSavedGoals.trans savedGoals
                                    · exact finalSavedRoots.trans savedRoots
                                    · rw [finalSites, visitedSites, visitSites, List.append_assoc]
                                      rfl
  termination_by _ proof _ _ _ _ _ _ _ _ => sizeOf proof

  theorem children_simulation :
    ∀ (childGoals : List Pattern) (proofs : List RawOpenProof) (state : State definition)
      (site : Site) (index : Nat) (rest : List Task) (after : ProofExecution.State) (childRoots : List Nat),
      state.todo = children site index (childGoals.zip proofs) ++ rest →
      checkOpenRawChildren definition (goals definition state.saved) childGoals proofs = true →
      compileChildrenWith definition (InferenceRuleExpansion.emitRule? definition)
        (roots definition state.saved) site.origin childGoals proofs state.checkedPrefix.val = some (after, childRoots) →
      ∃ next, run definition (childrenBudget proofs) (.running state) = .running next ∧
        next.checkedPrefix.val = after ∧ next.todo = rest ∧
        goals definition next.values = childGoals.reverse ++ goals definition state.values ∧
        roots definition next.values = childRoots.reverse ++ roots definition state.values ∧
        goals definition next.saved = goals definition state.saved ∧
        roots definition next.saved = roots definition state.saved ∧
        sites definition next = sites definition state ++ childrenSites site index proofs
    | [], [], state, site, index, rest, after, childRoots, work, _, compiled => by
        have equality : (state.checkedPrefix.val, []) = (after, childRoots) := by
          simpa only [compileChildrenWith, Option.some.injEq] using compiled
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj equality
        exact ⟨state, by simp only [childrenBudget, run], rfl, work, rfl, rfl, rfl, rfl, by simp [childrenSites]⟩
    | goal :: childGoals, proof :: proofs, state, site, index, rest, after, childRoots, work, accepted, compiled => by
        simp only [checkOpenRawChildren, Bool.and_eq_true] at accepted
        cases emitted : compileOpenWith definition (InferenceRuleExpansion.emitRule? definition)
            (roots definition state.saved) site.origin goal proof state.checkedPrefix.val with
        | none => simp [compileChildrenWith, emitted] at compiled
        | some pair =>
            obtain ⟨middle, root⟩ := pair
            cases rested : compileChildrenWith definition (InferenceRuleExpansion.emitRule? definition)
                (roots definition state.saved) site.origin childGoals proofs middle with
            | none => simp [compileChildrenWith, emitted, rested] at compiled
            | some pair =>
                obtain ⟨actual, tailRoots⟩ := pair
                have equality : (actual, root :: tailRoots) = (after, childRoots) := by
                  simpa [compileChildrenWith, emitted, rested] using compiled
                obtain ⟨rfl, rfl⟩ := Prod.mk.inj equality
                obtain ⟨visited, firstRun, prefixEq, firstWork, firstGoals, firstRoots, savedGoals, savedRoots, firstSites⟩ :=
                  visit_simulation goal proof state ⟨site.origin, site.path ++ [index]⟩
                    (children site (index + 1) (childGoals.zip proofs) ++ rest) middle root
                    (by simpa only [List.zip_cons_cons, children, List.cons_append] using work) accepted.1 emitted
                obtain ⟨next, tailRun, finalPrefix, finalWork, finalGoals, finalRoots,
                  finalSavedGoals, finalSavedRoots, finalSites⟩ :=
                  children_simulation childGoals proofs visited site (index + 1) rest actual tailRoots firstWork
                    (by simpa only [savedGoals] using accepted.2)
                    (by simpa only [savedRoots, prefixEq] using rested)
                refine ⟨next, ?_, finalPrefix, finalWork, ?_, ?_,
                  finalSavedGoals.trans savedGoals, finalSavedRoots.trans savedRoots, ?_⟩
                · rw [childrenBudget, run_add, firstRun, tailRun]
                · rw [finalGoals, firstGoals, List.reverse_cons, List.append_assoc]
                  rfl
                · rw [finalRoots, firstRoots, List.reverse_cons, List.append_assoc]
                  rfl
                · rw [finalSites, firstSites, childrenSites, List.append_assoc]
    | [], _ :: _, _, _, _, _, _, _, _, accepted, _ => by simp [checkOpenRawChildren] at accepted
    | _ :: _, [], _, _, _, _, _, _, _, accepted, _ => by simp [checkOpenRawChildren] at accepted
  termination_by _ proofs _ _ _ _ _ _ _ _ _ => sizeOf proofs
end

end Mettapedia.Languages.HOLLight.ChronologicalDriver.Correctness

namespace Mettapedia.Languages.HOLLight.ChronologicalDriver.Correctness

open Mettapedia.Logic Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight.InferenceCompiler
open Mettapedia.Languages.MM0.Translation.CalculusSimulation

variable (definition : ValidatedCalculusLanguageDef)

def lemmaSites : Nat → Lemmas → List Site
  | _, [] => []
  | index, (_, proof) :: lemmas => visitSites ⟨("lemma", index), []⟩ proof ++ lemmaSites (index + 1) lemmas

theorem singleton_claim {checkedPrefix : Prefix definition}
    (claims : List (Claim definition checkedPrefix)) (goal : Pattern)
    (single : goals definition claims = [goal]) :
    ∃ claim, claims = [claim] ∧ claim.goal = goal := by
  cases claims with
  | nil => simp [goals] at single
  | cons claim tail =>
      simp only [goals, List.map_cons, List.cons.injEq] at single
      have tailNil : tail = [] := List.map_eq_nil_iff.mp single.2
      subst tail
      exact ⟨claim, rfl, single.1⟩

theorem lemmas_simulation :
    ∀ (lemmas : Lemmas) (state : State definition) (index : Nat) (rest : List Task)
      (after : ProofExecution.State) (savedRoots : List Nat),
      state.todo = lemmaTasks index lemmas ++ rest →
      state.values = [] → state.saved.length = index →
      checkLemmas definition (goals definition state.saved) lemmas = true →
      compileLemmasWith definition (InferenceRuleExpansion.emitRule? definition) index
        (roots definition state.saved) lemmas state.checkedPrefix.val = some (after, savedRoots) →
      ∃ next, run definition (lemmaBudget lemmas) (.running state) = .running next ∧
        next.checkedPrefix.val = after ∧ next.todo = rest ∧ next.values = [] ∧
        goals definition next.saved = goals definition state.saved ++ lemmas.map Prod.fst ∧
        roots definition next.saved = savedRoots ∧
        sites definition next = sites definition state ++ lemmaSites index lemmas
  | [], state, index, rest, after, savedRoots, work, empty, _, _, compiled => by
      have equality : (state.checkedPrefix.val, roots definition state.saved) = (after, savedRoots) := by
        simpa only [compileLemmasWith, Option.some.injEq] using compiled
      obtain ⟨afterEq, rootsEq⟩ := Prod.mk.inj equality
      refine ⟨state, rfl, afterEq, work, empty, ?_, rootsEq, ?_⟩
      · simp
      · simp [lemmaSites]
  | (goal, proof) :: lemmas, state, index, rest, after, savedRoots, work, empty, indexEq, accepted, compiled => by
      simp only [checkLemmas, Bool.and_eq_true] at accepted
      cases emitted : compileOpenWith definition (InferenceRuleExpansion.emitRule? definition)
          (roots definition state.saved) ("lemma", index) goal proof state.checkedPrefix.val with
      | none => simp [compileLemmasWith, emitted] at compiled
      | some pair =>
          obtain ⟨middle, root⟩ := pair
          have rested : compileLemmasWith definition (InferenceRuleExpansion.emitRule? definition) (index + 1)
              (roots definition state.saved ++ [root]) lemmas middle = some (after, savedRoots) := by
            simpa [compileLemmasWith, emitted] using compiled
          obtain ⟨visited, firstRun, prefixEq, firstWork, firstGoals, firstRoots, savedGoals, savedRootsEq, firstSites⟩ :=
            visit_simulation definition goal proof state ⟨("lemma", index), []⟩
              (.save goal index :: lemmaTasks (index + 1) lemmas ++ rest) middle root
              (by simpa only [lemmaTasks, List.cons_append] using work) accepted.1 emitted
          have singletonGoals : goals definition visited.values = [goal] := by simpa only [empty, goals, List.map_nil] using firstGoals
          obtain ⟨claim, single, claimGoal⟩ := singleton_claim definition visited.values goal singletonGoals
          have claimRoot : claim.root = root := by
            simpa only [single, empty, roots, List.map_cons, List.map_nil, List.cons.injEq, and_true] using firstRoots
          have savedLength : visited.saved.length = index := by
            have lengths := congrArg List.length savedGoals
            simpa only [goals_length, indexEq] using lengths
          let saved : State definition :=
            { visited with
              todo := lemmaTasks (index + 1) lemmas ++ rest
              values := []
              saved := visited.saved ++ [claim] }
          have saveStep : step definition (.running visited) = .running saved := by
            simp only [step, firstWork, List.cons_append, single, claimGoal, savedLength, and_self, ↓reduceIte]
            rfl
          have saveGoals : goals definition saved.saved = goals definition state.saved ++ [goal] := by
            simp only [saved, goals, List.map_append, List.map_cons, List.map_nil, claimGoal]
            rw [← goals, savedGoals]
            rfl
          have saveRoots : roots definition saved.saved = roots definition state.saved ++ [root] := by
            simp only [saved, roots, List.map_append, List.map_cons, List.map_nil, claimRoot]
            rw [← roots, savedRootsEq]
            rfl
          obtain ⟨next, tailRun, finalPrefix, finalWork, finalEmpty, finalSavedGoals, finalSavedRoots, finalSites⟩ :=
            lemmas_simulation lemmas saved (index + 1) rest after savedRoots rfl rfl
              (by simp only [saved, List.length_append, List.length_cons, List.length_nil, savedLength])
              (by simpa only [saveGoals] using accepted.2)
              (by simpa only [saveRoots, saved, prefixEq] using rested)
          refine ⟨next, ?_, finalPrefix, finalWork, finalEmpty, ?_, finalSavedRoots, ?_⟩
          · rw [lemmaBudget, run_add, run_add, firstRun]
            simp only [run, saveStep]
            exact tailRun
          · rw [finalSavedGoals, saveGoals, List.map_cons, List.append_assoc]
            rfl
          · rw [finalSites]
            change sites definition visited ++ lemmaSites (index + 1) lemmas = _
            rw [firstSites, lemmaSites, List.append_assoc]

end Mettapedia.Languages.HOLLight.ChronologicalDriver.Correctness

namespace Mettapedia.Languages.HOLLight.ChronologicalDriver.Correctness

open Mettapedia.Logic Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight.InferenceCompiler
open Mettapedia.Languages.MM0.Translation.CalculusSimulation

variable (definition : ValidatedCalculusLanguageDef)

/-- The journal records each original occurrence, in lemma order and then root
postorder. Equal proof values and repeated saved roots retain separate sites. -/
def sourceSites (source : LemmaCertificate) : List Site :=
  lemmaSites 0 source.1 ++ visitSites ⟨("root", 0), []⟩ source.2

/-- Compare actual task execution with the successful recursive compiler,
including the exact graph and original chronological occurrence order. -/
theorem compileShared_simulation (goal : Pattern) (source : LemmaCertificate)
    (accepted : sharedSourceCheck definition goal source = true)
    (certificate : ProofSystem.Certificate)
    (compiled : compileShared definition goal source = some certificate) :
    ∃ (state : State definition) (claim : Claim definition state.checkedPrefix),
      run definition (totalBudget source) (start definition goal source) = .done state claim ∧
      result definition goal (.done state claim) = some certificate ∧
      claim.goal = goal ∧ goals definition state.saved = source.1.map Prod.fst ∧
      sites definition state = sourceSites source := by
  have admitted : checkLemmas definition [] source.1 = true ∧
      checkOpenRaw definition (source.1.map Prod.fst) goal source.2 = true := by
    simpa only [sharedSourceCheck, Bool.and_eq_true] using accepted
  have compiled' : compileSharedWith definition (InferenceRuleExpansion.emitRule? definition)
      goal source = some certificate := by
    simpa only [compileShared, accepted, Bool.true_eq, ↓reduceIte] using compiled
  cases lemmasEmitted : compileLemmasWith definition (InferenceRuleExpansion.emitRule? definition)
      0 [] source.1 (initialState definition.1) with
  | none => simp [compileSharedWith, lemmasEmitted] at compiled'
  | some pair =>
      obtain ⟨middle, context⟩ := pair
      cases rootEmitted : compileOpenWith definition (InferenceRuleExpansion.emitRule? definition)
          context ("root", 0) goal source.2 middle with
      | none => simp [compileSharedWith, lemmasEmitted, rootEmitted] at compiled'
      | some pair =>
          obtain ⟨after, root⟩ := pair
          have certificateEq : GraphExpansion.finish after root = certificate := by
            simpa [compileSharedWith, lemmasEmitted, rootEmitted] using compiled'
          let initial : State definition :=
            { checkedPrefix := seed definition
              todo := lemmaTasks 0 source.1 ++ [.visit goal source.2 ⟨("root", 0), []⟩, .finish goal]
              values := [], saved := [], occurrences := [] }
          obtain ⟨lemmasDone, ranLemmas, lemmaPrefix, lemmaWork, lemmaEmpty, savedGoals, savedRoots, lemmaSitesEq⟩ :=
            lemmas_simulation definition source.1 initial 0
              [.visit goal source.2 ⟨("root", 0), []⟩, .finish goal] middle context rfl rfl rfl
              admitted.1 lemmasEmitted
          obtain ⟨state, ranRoot, rootPrefix, rootWork, rootGoals, rootRoots, finalSavedGoals, _, rootSitesEq⟩ :=
            visit_simulation definition goal source.2 lemmasDone ⟨("root", 0), []⟩ [.finish goal] after root
              lemmaWork (by rw [savedGoals]; exact admitted.2)
              (by simpa only [savedRoots, lemmaPrefix] using rootEmitted)
          have singletonGoals : goals definition state.values = [goal] := by
            simpa only [lemmaEmpty, goals, List.map_nil] using rootGoals
          obtain ⟨claim, single, claimGoal⟩ := singleton_claim definition state.values goal singletonGoals
          have claimRoot : claim.root = root := by
            simpa only [single, lemmaEmpty, roots, List.map_cons, List.map_nil, List.cons.injEq, and_true] using rootRoots
          have finishStep : step definition (.running state) = .done state claim := by
            simp only [step, rootWork, single, claimGoal, ↓reduceIte]
          refine ⟨state, claim, ?_, ?_, claimGoal, ?_, ?_⟩
          · simp only [start, accepted, ↓reduceIte]
            change run definition (lemmaBudget source.1 + visitBudget source.2 + 1) (.running initial) = _
            rw [run_add, run_add, ranLemmas, ranRoot]
            simpa only [run] using finishStep
          · have valid : hasClaim goal claim.out = true := claimGoal ▸ claim.represents
            simp only [result, valid, ↓reduceIte, rootPrefix, claimRoot, certificateEq]
          · rw [finalSavedGoals, savedGoals]
            rfl
          · rw [rootSitesEq, lemmaSitesEq]
            rfl

/-- Every admitted source completes the actual controller within its exact
syntax-derived task budget in the proven first-order host region. -/
theorem admitted_source_completes (firstOrder : FirstOrderCalculus definition.1)
    (goal : Pattern) (source : LemmaCertificate)
    (accepted : sharedSourceCheck definition goal source = true) :
    ∃ (certificate : ProofSystem.Certificate) (state : State definition)
      (claim : Claim definition state.checkedPrefix),
      compileShared definition goal source = some certificate ∧
      run definition (totalBudget source) (start definition goal source) = .done state claim ∧
      result definition goal (.done state claim) = some certificate ∧
      claim.goal = goal ∧ goals definition state.saved = source.1.map Prod.fst ∧
      sites definition state = sourceSites source := by
  obtain ⟨certificate, compiled⟩ := compileShared_preserves definition firstOrder goal source accepted
  obtain ⟨state, claim, ran, published, claimGoal, savedGoals, journal⟩ :=
    compileShared_simulation definition goal source accepted certificate compiled
  exact ⟨certificate, state, claim, compiled, ran, published, claimGoal, savedGoals, journal⟩

/-- Success and refusal agree with the original compiler, at the exact
controller budget; the compiler is a specification, never a controller callback. -/
theorem result_exact (firstOrder : FirstOrderCalculus definition.1)
    (goal : Pattern) (source : LemmaCertificate) :
    result definition goal (run definition (totalBudget source) (start definition goal source)) =
      compileShared definition goal source := by
  cases accepted : sharedSourceCheck definition goal source with
  | false =>
      rw [refused_source_no_result definition goal source accepted,
        compileShared_refused definition goal source accepted]
  | true =>
      obtain ⟨certificate, state, claim, compiled, ran, published, _⟩ :=
        admitted_source_completes definition firstOrder goal source accepted
      rw [ran, published, compiled]

end Mettapedia.Languages.HOLLight.ChronologicalDriver.Correctness

namespace Mettapedia.Languages.HOLLight.ChronologicalDriver.Correctness

open Mettapedia.Logic Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.CertificateGSLT Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight.InferenceCompiler
open Mettapedia.Languages.MM0.Translation.CalculusSimulation

mutual
  theorem visitBudget_le_weight (proof : RawOpenProof) :
      visitBudget proof ≤ 2 * CertificateDataEncoding.proofWeight proof := by
    cases proof with
    | premise index =>
        simp only [visitBudget, CertificateDataEncoding.proofWeight]
        omega
    | node ruleInstance proofs =>
        have rest := childrenBudget_le_weight proofs
        simp only [visitBudget, CertificateDataEncoding.proofWeight]
        omega
  termination_by sizeOf proof

  theorem childrenBudget_le_weight (proofs : List RawOpenProof) :
      childrenBudget proofs ≤ 2 * CertificateDataEncoding.proofsWeight proofs := by
    cases proofs with
    | nil => simp [childrenBudget, CertificateDataEncoding.proofsWeight]
    | cons proof proofs =>
        have first := visitBudget_le_weight proof
        have rest := childrenBudget_le_weight proofs
        simp only [childrenBudget, CertificateDataEncoding.proofsWeight]
        omega
  termination_by sizeOf proofs
end

theorem lemmaBudget_le_weight (lemmas : Lemmas) :
    lemmaBudget lemmas ≤ 2 * CertificateDataEncoding.lemmasWeight lemmas := by
  induction lemmas with
  | nil => simp [lemmaBudget, CertificateDataEncoding.lemmasWeight]
  | cons item lemmas ih =>
      obtain ⟨goal, proof⟩ := item
      have first := visitBudget_le_weight proof
      simp only [lemmaBudget, CertificateDataEncoding.lemmasWeight]
      omega

/-- A linear bound on controller tasks in the ORIGINAL finite-alphabet input.
This does not charge source admission or the physical work performed by close. -/
theorem totalBudget_encoded_bound (goal : Pattern) (source : LemmaCertificate) :
    totalBudget source ≤ 2 * ProofSystems.encodedSize CertificateDataEncoding.inputEncoding (goal, source) := by
  have earlier := lemmaBudget_le_weight source.1
  have later := visitBudget_le_weight source.2
  have storage := CertificateDataEncoding.inputBitWeight_le_encoded goal source
  simp only [CertificateDataEncoding.inputBitWeight, CertificateDataEncoding.inputWeight,
    CertificateDataEncoding.sharedWeight] at storage
  simp only [totalBudget]
  simp only [ProofSystems.encodedSize, CertificateDataEncoding.inputEncoding]
  omega

variable (definition : ValidatedCalculusLanguageDef)

/-- Longer resumptions publish exactly the same certificate. -/
theorem result_extra_budget (firstOrder : FirstOrderCalculus definition.1)
    (goal : Pattern) (source : LemmaCertificate) (extra : Nat) :
    result definition goal (run definition (totalBudget source + extra) (start definition goal source)) =
      compileShared definition goal source := by
  cases accepted : sharedSourceCheck definition goal source with
  | false =>
      rw [refused_source_no_result definition goal source accepted,
        compileShared_refused definition goal source accepted]
  | true =>
      obtain ⟨certificate, state, claim, compiled, ran, published, _⟩ :=
        admitted_source_completes definition firstOrder goal source accepted
      rw [run_add, ran, run_done, published, compiled]

/-- The exact task result inherits the compiler's proved physical node bound. -/
theorem completed_certificate_node_bound (firstOrder : FirstOrderCalculus definition.1)
    (goal : Pattern) (source : LemmaCertificate) (certificate : ProofSystem.Certificate)
    (published : result definition goal (run definition (totalBudget source) (start definition goal source)) =
      some certificate) :
    certificate.1.length ≤ definition.1.rules.length + 8 * localNodeFactor definition.1 *
      ProofSystems.encodedSize CertificateDataEncoding.inputEncoding (goal, source) := by
  rw [result_exact definition firstOrder goal source] at published
  exact compileShared_encoded_node_bound definition goal source published

theorem zero_budget_no_result (goal : Pattern) (source : LemmaCertificate) :
    result definition goal (run definition 0 (start definition goal source)) = none := by
  simp only [run, start]
  split <;> rfl

namespace Controls

open Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation.Controls
open Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayPresentation

def binderSource : LemmaCertificate :=
  ([], .node ⟨dataRule.id, [binderValue]⟩ [])

theorem binder_source_admitted : sharedSourceCheck dataCalculus (judgmentP binderValue) binderSource = true := by
  decide +kernel

theorem binder_exact_completion :
    result dataCalculus (judgmentP binderValue)
      (run dataCalculus 3 (start dataCalculus (judgmentP binderValue) binderSource)) =
      compileShared dataCalculus (judgmentP binderValue) binderSource := by
  simpa only [totalBudget, binderSource, lemmaBudget, visitBudget, childrenBudget] using
    result_exact dataCalculus dataCalculus_firstOrder (judgmentP binderValue) binderSource

def repeatedLemmaSource : LemmaCertificate :=
  ([(judgmentP binderValue, .node ⟨dataRule.id, [binderValue]⟩ []),
    (judgmentP binderValue, .premise 0)], .premise 1)

theorem repeated_lemma_admitted :
    sharedSourceCheck dataCalculus (judgmentP binderValue) repeatedLemmaSource = true := by
  decide +kernel

theorem repeated_lemma_completes :
    ∃ (certificate : ProofSystem.Certificate) (state : State dataCalculus)
      (claim : Claim dataCalculus state.checkedPrefix),
      compileShared dataCalculus (judgmentP binderValue) repeatedLemmaSource = some certificate ∧
      run dataCalculus (totalBudget repeatedLemmaSource)
        (start dataCalculus (judgmentP binderValue) repeatedLemmaSource) = .done state claim ∧
      result dataCalculus (judgmentP binderValue) (.done state claim) = some certificate ∧
      claim.goal = judgmentP binderValue ∧
      goals dataCalculus state.saved = repeatedLemmaSource.1.map Prod.fst ∧
      sites dataCalculus state = sourceSites repeatedLemmaSource :=
  admitted_source_completes dataCalculus dataCalculus_firstOrder _ _ repeated_lemma_admitted

theorem repeated_lemma_sites : sourceSites repeatedLemmaSource =
    [⟨("lemma", 0), []⟩, ⟨("lemma", 1), []⟩, ⟨("root", 0), []⟩] := by
  simp [sourceSites, repeatedLemmaSource, lemmaSites, visitSites, childrenSites]

theorem repeated_lemma_budget : totalBudget repeatedLemmaSource = 7 := by
  simp [totalBudget, repeatedLemmaSource, lemmaBudget, visitBudget, childrenBudget]

def futureSource : LemmaCertificate :=
  ([(judgmentP binderValue, .premise 0)], .premise 0)

theorem future_source_refused : sharedSourceCheck dataCalculus (judgmentP binderValue) futureSource = false := by
  decide +kernel

theorem future_no_result (budget : Nat) :
    result dataCalculus (judgmentP binderValue)
      (run dataCalculus budget (start dataCalculus (judgmentP binderValue) futureSource)) = none :=
  refused_source_no_result dataCalculus _ _ future_source_refused budget

def unusedBadLemmaSource : LemmaCertificate :=
  ([(judgmentP binderValue, .premise 99)], .node ⟨dataRule.id, [binderValue]⟩ [])

theorem unused_bad_lemma_refused :
    sharedSourceCheck dataCalculus (judgmentP binderValue) unusedBadLemmaSource = false := by
  decide +kernel

theorem unused_bad_lemma_no_result (budget : Nat) :
    result dataCalculus (judgmentP binderValue)
      (run dataCalculus budget (start dataCalculus (judgmentP binderValue) unusedBadLemmaSource)) = none :=
  refused_source_no_result dataCalculus _ _ unused_bad_lemma_refused budget

end Controls

end Mettapedia.Languages.HOLLight.ChronologicalDriver.Correctness

namespace Mettapedia.Languages.HOLLight.ChronologicalDriver.Correctness.Controls

open Mettapedia.Logic Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker Mettapedia.GSLT.LanguageDef.CertificateGSLT
open Mettapedia.Languages.HOLLight.InferenceCompiler
open Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation.Controls
open Mettapedia.GSLT.LanguageDef.BootstrapCell.ReplayPresentation
open Mettapedia.Languages.MM0.Translation.CalculusSimulation

def twoChildRule : RuleSchema where
  id := ⟨"two"⟩
  metavariables := [("first", 0), ("second", 0)]
  premises := [judgmentP (.fvar "first"), judgmentP (.fvar "second")]
  conclusion := judgmentP (.fvar "second")

def twoChildCalculus : ValidatedCalculusLanguageDef :=
  ⟨modusPonens [dataRule, twoChildRule], by decide +kernel⟩

theorem twoChild_firstOrder : FirstOrderCalculus twoChildCalculus.1 :=
  firstOrderCheck_sound (by decide +kernel)

def secondValue : Pattern := .apply "Unicode-λ\x00" []

def orderedChildSource : LemmaCertificate :=
  ([(judgmentP binderValue, .node ⟨dataRule.id, [binderValue]⟩ []),
    (judgmentP secondValue, .node ⟨dataRule.id, [secondValue]⟩ [])],
    .node ⟨twoChildRule.id, [binderValue, secondValue]⟩ [.premise 0, .premise 1])

def repeatedChildSource : LemmaCertificate :=
  ([(judgmentP binderValue, .node ⟨dataRule.id, [binderValue]⟩ [])],
    .node ⟨twoChildRule.id, [binderValue, binderValue]⟩ [.premise 0, .premise 0])

theorem ordered_child_admitted :
    sharedSourceCheck twoChildCalculus (judgmentP secondValue) orderedChildSource = true := by
  decide +kernel

theorem repeated_child_admitted :
    sharedSourceCheck twoChildCalculus (judgmentP binderValue) repeatedChildSource = true := by
  decide +kernel

theorem ordered_child_exact :
    result twoChildCalculus (judgmentP secondValue)
      (run twoChildCalculus (totalBudget orderedChildSource)
        (start twoChildCalculus (judgmentP secondValue) orderedChildSource)) =
      compileShared twoChildCalculus (judgmentP secondValue) orderedChildSource :=
  result_exact twoChildCalculus twoChild_firstOrder _ _

theorem repeated_child_completes :
    ∃ (certificate : ProofSystem.Certificate) (state : State twoChildCalculus)
      (claim : Claim twoChildCalculus state.checkedPrefix),
      compileShared twoChildCalculus (judgmentP binderValue) repeatedChildSource = some certificate ∧
      run twoChildCalculus (totalBudget repeatedChildSource)
        (start twoChildCalculus (judgmentP binderValue) repeatedChildSource) = .done state claim ∧
      result twoChildCalculus (judgmentP binderValue) (.done state claim) = some certificate ∧
      claim.goal = judgmentP binderValue ∧
      goals twoChildCalculus state.saved = repeatedChildSource.1.map Prod.fst ∧
      sites twoChildCalculus state = sourceSites repeatedChildSource :=
  admitted_source_completes twoChildCalculus twoChild_firstOrder _ _ repeated_child_admitted

theorem repeated_child_sites : sourceSites repeatedChildSource =
    [⟨("lemma", 0), []⟩, ⟨("root", 0), [0]⟩, ⟨("root", 0), [1]⟩, ⟨("root", 0), []⟩] := by
  simp [sourceSites, repeatedChildSource, lemmaSites, visitSites, childrenSites]

theorem repeated_child_budget : totalBudget repeatedChildSource = 8 := by
  simp [totalBudget, repeatedChildSource, lemmaBudget, visitBudget, childrenBudget]

def reorderedChildSource : LemmaCertificate :=
  (orderedChildSource.1,
    .node ⟨twoChildRule.id, [binderValue, secondValue]⟩ [.premise 1, .premise 0])

theorem reordered_child_refused :
    sharedSourceCheck twoChildCalculus (judgmentP secondValue) reorderedChildSource = false := by
  decide +kernel

theorem reordered_child_no_result (budget : Nat) :
    result twoChildCalculus (judgmentP secondValue)
      (run twoChildCalculus budget (start twoChildCalculus (judgmentP secondValue) reorderedChildSource)) = none :=
  refused_source_no_result twoChildCalculus _ _ reordered_child_refused budget

def missingChildSource : LemmaCertificate :=
  (orderedChildSource.1, .node ⟨twoChildRule.id, [binderValue, secondValue]⟩ [.premise 0])

theorem missing_child_refused :
    sharedSourceCheck twoChildCalculus (judgmentP secondValue) missingChildSource = false := by
  decide +kernel

def excessChildSource : LemmaCertificate :=
  (orderedChildSource.1,
    .node ⟨twoChildRule.id, [binderValue, secondValue]⟩ [.premise 0, .premise 1, .premise 1])

theorem excess_child_refused :
    sharedSourceCheck twoChildCalculus (judgmentP secondValue) excessChildSource = false := by
  decide +kernel

end Mettapedia.Languages.HOLLight.ChronologicalDriver.Correctness.Controls

namespace Mettapedia.Languages.HOLLight.ChronologicalDriver.Correctness

open Mettapedia.Logic Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.GSLT.LanguageDef
open Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight.InferenceCompiler
open Mettapedia.Languages.HOLLight.InferenceHosting
open Mettapedia.Languages.HOLLight.FirstOrder.InferenceTranslation
open Mettapedia.Languages.MM0.Translation.CalculusSimulation

variable (definition : ValidatedCalculusLanguageDef)

/-- Exact source admission, success/refusal, rather than existence of a different
HOL proof of the same encoded claim. -/
theorem result_exists_iff (firstOrder : FirstOrderCalculus definition.1)
    (goal : Pattern) (source : LemmaCertificate) :
    sharedSourceCheck definition goal source = true ↔
      ∃ certificate, result definition goal
        (run definition (totalBudget source) (start definition goal source)) = some certificate := by
  rw [result_exact definition firstOrder goal source]
  exact compileShared_iff definition firstOrder goal source

/-- The completed actual controller simultaneously returns the exact original
compiler graph, preserves original occurrence order, and earns the independent
kernel readout and linear task/node accounts. Binary execution cost is separate. -/
theorem admitted_source_contract (firstOrder : FirstOrderCalculus definition.1)
    (goal : Pattern) (source : LemmaCertificate)
    (accepted : sharedSourceCheck definition goal source = true) :
    ∃ (certificate : ProofSystem.Certificate) (state : State definition)
      (claim : Claim definition state.checkedPrefix),
      compileShared definition goal source = some certificate ∧
      run definition (totalBudget source) (start definition goal source) = .done state claim ∧
      result definition goal (.done state claim) = some certificate ∧
      claim.goal = goal ∧ goals definition state.saved = source.1.map Prod.fst ∧
      sites definition state = sourceSites source ∧
      totalBudget source ≤ 2 * ProofSystems.encodedSize CertificateDataEncoding.inputEncoding (goal, source) ∧
      certificate.1.length ≤ definition.1.rules.length + 8 * localNodeFactor definition.1 *
        ProofSystems.encodedSize CertificateDataEncoding.inputEncoding (goal, source) ∧
      ∃ out, (ProofSystem.checker (policy (inferenceRules definition.1))).check out certificate = true ∧
        out.sequent.hyp = ∅ ∧ out.sequent.concl = compileClaim goal := by
  obtain ⟨certificate, state, claim, compiled, ran, published, claimGoal, savedGoals, journal⟩ :=
    admitted_source_completes definition firstOrder goal source accepted
  exact ⟨certificate, state, claim, compiled, ran, published, claimGoal, savedGoals, journal,
    totalBudget_encoded_bound goal source,
    compileShared_encoded_node_bound definition goal source compiled,
    result_checked definition goal (.done state claim) published⟩

end Mettapedia.Languages.HOLLight.ChronologicalDriver.Correctness
