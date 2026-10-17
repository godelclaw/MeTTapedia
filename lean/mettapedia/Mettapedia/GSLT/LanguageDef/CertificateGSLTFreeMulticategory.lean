import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingCategory
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOpenChecker
import Mettapedia.Logic.RuleMulticategory

/-!
# Authored calculi present free cartesian multicategories

The rule instances of a validated calculus are explicit instances with their
declarative application (`ruleSignature`). Its existing open derivations, with
ordered premise contexts and substitution, are exactly the free cartesian
multicategory on that signature, restricted to list-shaped contexts:

* `OpenDerivation.termEquiv` identifies open derivations with terms of the free
  multicategory, and `OpenDerivation.toTerm_bind` shows that this identification
  carries substitution to substitution;
* `interpret` and `interpret_unique` give the universal property for open
  derivations themselves: every interpretation of the rule instances in a
  cartesian multicategory extends uniquely along the identification.

`decodeOpen` is a computable elaborator from accepted raw open proofs to typed
open derivations; it is the data-level form of
`checkOpenRaw_exact_derivation`.

Consequently the classifying category of every authored calculus — VibeITP,
projected Metamath snapshots and HOL Light's first-order calculus among them — is
the category of contexts of a free cartesian multicategory. Its binary products
are context concatenation (`ClassifyingContext.concatIsLimit`).
-/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Logic (RuleSignature CartesianMulticategory)

/-- The rule instances of a validated calculus. -/
def ruleSignature (definition : ValidatedCalculusLanguageDef) : RuleSignature.{0, 0} Pattern :=
  fun premises conclusion =>
    {ruleInstance : RuleInstance // RuleApplication definition ruleInstance premises conclusion}

variable {definition : ValidatedCalculusLanguageDef}

open Mettapedia.Logic.RuleSignature (Term)

mutual

/-- An open derivation as a term of the free multicategory. -/
def OpenDerivation.toTerm {context : List Pattern} :
    {goal : Pattern} → OpenDerivation definition context goal →
      Term (ruleSignature definition) context.get goal
  | _, .assumption index => .var index
  | _, .byRule ruleInstance application children =>
      .node ⟨ruleInstance, application⟩ children.toTerms

/-- An ordered derivation vector as a family of terms. -/
def OpenDerivationList.toTerms {context : List Pattern} :
    {goals : List Pattern} → OpenDerivationList definition context goals →
      (p : Fin goals.length) → Term (ruleSignature definition) context.get (goals.get p)
  | _, .nil => fun p => p.elim0
  | _, .cons (premise := premise) (premises := premises) head tail => fun p =>
      Fin.cases (motive := fun q : Fin (premises.length + 1) =>
          Term (ruleSignature definition) context.get ((premise :: premises).get q))
        head.toTerm tail.toTerms p

end

/-- A term of the free multicategory as an open derivation. -/
def termToOpen {context : List Pattern} :
    {goal : Pattern} → Term (ruleSignature definition) context.get goal →
      OpenDerivation definition context goal
  | _, .var index => .assumption index
  | _, .node rule children =>
      .byRule rule.1 rule.2 (OpenDerivationList.ofFn _ fun p => termToOpen (children p))

theorem OpenDerivationList.toTerms_get {context : List Pattern} :
    ∀ {goals : List Pattern} (derivations : OpenDerivationList definition context goals)
      (p : Fin goals.length), derivations.toTerms p = (derivations.get p).toTerm
  | _, .nil, p => p.elim0
  | _, .cons head tail, p => by
      refine Fin.cases ?_ (fun q => ?_) p
      · rfl
      · exact OpenDerivationList.toTerms_get tail q

theorem OpenDerivationList.toTerms_ofFn {context : List Pattern} :
    ∀ (goals : List Pattern)
      (entries : (p : Fin goals.length) → OpenDerivation definition context (goals.get p)),
      (OpenDerivationList.ofFn goals entries).toTerms = fun p => (entries p).toTerm
  | [], _ => funext fun p => p.elim0
  | _ :: goals, entries => by
      funext p
      refine Fin.cases ?_ (fun q => ?_) p
      · rfl
      · exact congrFun (OpenDerivationList.toTerms_ofFn goals fun q => entries q.succ) q

theorem termToOpen_toTerm {context : List Pattern} :
    ∀ {goal : Pattern} (t : Term (ruleSignature definition) context.get goal),
      (termToOpen t).toTerm = t
  | _, .var _ => rfl
  | _, .node rule children => by
      change Term.node ⟨rule.1, rule.2⟩ (OpenDerivationList.ofFn _ fun p => termToOpen (children p)).toTerms =
        Term.node rule children
      rw [OpenDerivationList.toTerms_ofFn]
      congr 1
      funext p
      exact termToOpen_toTerm (children p)

mutual

theorem OpenDerivation.toTerm_termToOpen {context : List Pattern} :
    ∀ {goal : Pattern} (d : OpenDerivation definition context goal), termToOpen d.toTerm = d
  | _, .assumption _ => rfl
  | _, .byRule ruleInstance application children => by
      change OpenDerivation.byRule ruleInstance application
          (OpenDerivationList.ofFn _ fun p => termToOpen (children.toTerms p)) = _
      rw [OpenDerivationList.ofFn_toTerms children]

theorem OpenDerivationList.ofFn_toTerms {context : List Pattern} :
    ∀ {goals : List Pattern} (derivations : OpenDerivationList definition context goals),
      OpenDerivationList.ofFn goals (fun p => termToOpen (derivations.toTerms p)) = derivations
  | _, .nil => rfl
  | _, .cons head tail => by
      change OpenDerivationList.cons (termToOpen head.toTerm)
          (OpenDerivationList.ofFn _ fun q => termToOpen (tail.toTerms q)) = _
      rw [OpenDerivation.toTerm_termToOpen head, OpenDerivationList.ofFn_toTerms tail]

end

/-- **Open derivations are free-multicategory terms.** -/
def OpenDerivation.termEquiv (context : List Pattern) (goal : Pattern) :
    OpenDerivation definition context goal ≃ Term (ruleSignature definition) context.get goal where
  toFun d := d.toTerm
  invFun t := termToOpen t
  left_inv d := OpenDerivation.toTerm_termToOpen d
  right_inv t := termToOpen_toTerm t

mutual

/-- **Substitution is preserved.** Plugging derivation vectors corresponds to
simultaneous substitution of terms. -/
theorem OpenDerivation.toTerm_bind {sourceContext targetContext : List Pattern} :
    ∀ {goal : Pattern} (d : OpenDerivation definition sourceContext goal)
      (environment : OpenDerivationList definition targetContext sourceContext),
      (d.bind environment).toTerm = d.toTerm.subst environment.toTerms
  | _, .assumption index, environment => by
      change (environment.get index).toTerm = environment.toTerms index
      rw [OpenDerivationList.toTerms_get]
  | _, .byRule ruleInstance application children, environment => by
      change Term.node ⟨ruleInstance, application⟩ (children.bind environment).toTerms =
        Term.node ⟨ruleInstance, application⟩ (fun p => (children.toTerms p).subst environment.toTerms)
      congr 1
      funext p
      exact OpenDerivationList.toTerms_bind children environment p

theorem OpenDerivationList.toTerms_bind {sourceContext targetContext : List Pattern} :
    ∀ {goals : List Pattern} (derivations : OpenDerivationList definition sourceContext goals)
      (environment : OpenDerivationList definition targetContext sourceContext)
      (p : Fin goals.length),
      (derivations.bind environment).toTerms p = (derivations.toTerms p).subst environment.toTerms
  | _, .nil, _, p => p.elim0
  | _, .cons head tail, environment, p => by
      refine Fin.cases ?_ (fun q => ?_) p
      · exact OpenDerivation.toTerm_bind head environment
      · exact OpenDerivationList.toTerms_bind tail environment q

end

/-- Premise assumptions correspond to variables. -/
theorem assumptionEnvironment_toTerms (context : List Pattern) :
    (assumptionEnvironment definition context).toTerms = fun p => Term.var p := by
  rw [assumptionEnvironment, OpenDerivationList.toTerms_ofFn]
  rfl

/-! ## Computable decoding of checked raw open proofs -/

mutual

/-- Decode an accepted raw open proof into a typed open derivation. -/
def decodeOpen (definition : ValidatedCalculusLanguageDef) (context : List Pattern) :
    (goal : Pattern) → (proof : RawOpenProof) →
      checkOpenRaw definition context goal proof = true → OpenDerivation definition context goal
  | goal, .premise index, checked =>
      if bound : index < context.length then
        if same : context.get ⟨index, bound⟩ = goal then
          same ▸ OpenDerivation.assumption ⟨index, bound⟩
        else
          absurd checked (by
            simp only [checkOpenRaw, List.getElem?_eq_getElem bound]
            simpa using same)
      else
        absurd checked (by simp [checkOpenRaw, List.getElem?_eq_none (Nat.le_of_not_lt bound)])
  | goal, .node ruleInstance children, checked =>
      match instantiated : instantiateRule? definition ruleInstance with
      | none => absurd checked (by simp [checkOpenRaw, instantiated])
      | some (premises, conclusion) =>
          have parts : conclusion = goal ∧
              checkOpenRawChildren definition context premises children = true := by
            simpa [checkOpenRaw, instantiated, Bool.and_eq_true] using checked
          parts.1 ▸ OpenDerivation.byRule ruleInstance
            (instantiateRule?_eq_some_iff_application.mp instantiated)
            (decodeChildren definition context premises children parts.2)
  termination_by _ proof => sizeOf proof

/-- Decode an accepted ordered child list. -/
def decodeChildren (definition : ValidatedCalculusLanguageDef) (context : List Pattern) :
    (goals : List Pattern) → (proofs : List RawOpenProof) →
      checkOpenRawChildren definition context goals proofs = true →
        OpenDerivationList definition context goals
  | [], [], _ => .nil
  | goal :: goals, proof :: proofs, checked =>
      have parts : checkOpenRaw definition context goal proof = true ∧
          checkOpenRawChildren definition context goals proofs = true := by
        simpa [checkOpenRawChildren, Bool.and_eq_true] using checked
      .cons (decodeOpen definition context goal proof parts.1)
        (decodeChildren definition context goals proofs parts.2)
  | [], _ :: _, checked => absurd checked (by simp [checkOpenRawChildren])
  | _ :: _, [], checked => absurd checked (by simp [checkOpenRawChildren])
  termination_by _ proofs => sizeOf proofs

end

/-! ## The universal property for open derivations -/

variable {Sorts' : Type u} {M : CartesianMulticategory.{u, w} Sorts'} {obj : Pattern → Sorts'}

/-- Interpret open derivations in any cartesian multicategory from an
interpretation of the rule instances. -/
def interpret (φ : RuleSignature.Interpretation (ruleSignature definition) M obj)
    {context : List Pattern} {goal : Pattern} (d : OpenDerivation definition context goal) :
    M.Hom (obj ∘ context.get) (obj goal) :=
  d.toTerm.lift φ

/-- Interpretation preserves substitution. -/
theorem interpret_bind (φ : RuleSignature.Interpretation (ruleSignature definition) M obj)
    {sourceContext targetContext : List Pattern} {goal : Pattern}
    (d : OpenDerivation definition sourceContext goal)
    (environment : OpenDerivationList definition targetContext sourceContext) :
    interpret φ (d.bind environment) =
      M.subst (interpret φ d) (fun i => interpret φ (environment.get i)) := by
  unfold interpret
  rw [OpenDerivation.toTerm_bind, Term.lift_subst]
  congr 1
  funext i
  rw [OpenDerivationList.toTerms_get]

/-- **Uniqueness.** Any assignment on open derivations that agrees with the
generators, sends assumptions to variables and preserves substitution is the
interpretation. -/
theorem interpret_unique (φ : RuleSignature.Interpretation (ruleSignature definition) M obj)
    (G : ∀ {context : List Pattern} {goal : Pattern},
      OpenDerivation definition context goal → M.Hom (obj ∘ context.get) (obj goal))
    (onAssumption : ∀ {context : List Pattern} (index : Fin context.length),
      G (OpenDerivation.assumption (definition := definition) index) =
        M.var (Γ := obj ∘ context.get) index)
    (onRule : ∀ {context : List Pattern} {premises : List Pattern} {conclusion : Pattern}
      (ruleInstance : RuleInstance) (application : RuleApplication definition ruleInstance premises conclusion)
      (children : OpenDerivationList definition context premises),
      G (.byRule ruleInstance application children) =
        M.subst (φ premises conclusion ⟨ruleInstance, application⟩) (fun p => G (children.get p)))
    {context : List Pattern} {goal : Pattern} (d : OpenDerivation definition context goal) :
    G d = interpret φ d := by
  have main : ∀ {goal : Pattern} (t : Term (ruleSignature definition) context.get goal),
      G (termToOpen t) = t.lift φ := by
    intro goal t
    induction t with
    | var index => exact onAssumption index
    | node rule children ih =>
        change G (OpenDerivation.byRule rule.1 rule.2
          (OpenDerivationList.ofFn _ fun p => termToOpen (children p))) = _
        rw [onRule]
        change _ = M.subst (φ _ _ rule) (fun p => (children p).lift φ)
        congr 1
        funext p
        rw [OpenDerivationList.get_ofFn]
        exact ih p
  have := main d.toTerm
  rwa [OpenDerivation.toTerm_termToOpen] at this

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
