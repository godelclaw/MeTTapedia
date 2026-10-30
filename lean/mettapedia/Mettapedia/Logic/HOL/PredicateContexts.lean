import Mettapedia.Logic.HOL.CheckableFragment
import Mettapedia.Logic.HOL.ProofSyntaxHypothesisSubstitution
import Mettapedia.Logic.HOL.PredicateProducts
import Mettapedia.Logic.HOL.Soundness

/-!
# Predicate-guarded HOL contexts

A telescope assigns a predicate to each binder in its preceding context.
Its hypotheses retain one guard per variable occurrence. A substitution
realizer supplies proofs only for these variable guards; hypothesis
substitution then transports arbitrary retained derivations. Empty guards
are allowed and do not imply an inhabited context.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.PredicateContexts
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v}

inductive Telescope (Const : Ty Base → Type v) : Ctx Base → Type (max u v) where
  | nil : Telescope Const []
  | snoc {Γ : Ctx Base} {type : Ty Base} (prior : Telescope Const Γ)
      (domain : Term Const Γ (type ⇒ .prop)) : Telescope Const (type :: Γ)

namespace Telescope
variable {Γ Ξ Ω : Ctx Base} {type : Ty Base}

def hypotheses : {Γ : Ctx Base} → Telescope Const Γ → List (Formula Const Γ)
  | _, .nil => []
  | _, .snoc prior domain => .app (weaken domain) (.var .vz) :: weakenHyps prior.hypotheses

@[simp] theorem hypotheses_length (context : Telescope Const Γ) : context.hypotheses.length = Γ.length := by
  induction context with
  | nil => rfl
  | snoc prior domain ih => simp [hypotheses, weakenHyps, ih]

def domain : {Γ : Ctx Base} → Telescope Const Γ → {type : Ty Base} →
    Var Γ type → Term Const Γ (type ⇒ .prop)
  | _, .nil, _, index => nomatch index
  | _, .snoc _ predicate, _, .vz => weaken predicate
  | _, .snoc prior _, _, .vs index => weaken (prior.domain index)

def guard (context : Telescope Const Γ) (index : Var Γ type) : Formula Const Γ :=
  .app (context.domain index) (.var index)

def occurrence (context : Telescope Const Γ) (index : Var Γ type) : Fin context.hypotheses.length :=
  index.toFin.cast context.hypotheses_length.symm

theorem hypotheses_get (context : Telescope Const Γ) (index : Var Γ type) :
    context.hypotheses.get (context.occurrence index) = context.guard index := by
  induction context with
  | nil => cases index
  | snoc prior predicate ih =>
      cases index with
      | vz => rfl
      | vs index =>
          simpa [hypotheses, occurrence, guard, domain, weakenHyps, weaken, rename,
            Var.toFin, Rename.weaken, List.get_eq_getElem] using congrArg (weaken (σ := _)) (ih index)

/-- The actual occurrence in the telescope supplies its variable guard. -/
def variableProof (context : Telescope Const Γ) (index : Var Γ type) :
    ProofSyntax Const context.hypotheses (context.guard index) :=
  ProofSyntax.castIndices rfl (context.hypotheses_get index) (.hyp (context.occurrence index))

def Realizes (context : Telescope Const Γ) (substitution : Subst Const Γ Ξ)
    (assumptions : List (Formula Const Ξ)) :=
  ∀ {type} (index : Var Γ type), ProofSyntax Const assumptions (subst substitution (context.guard index))

namespace Realizes
variable {context : Telescope Const Γ} {target : Telescope Const Ξ}
  {substitution : Subst Const Γ Ξ} {assumptions : List (Formula Const Ξ)}

def hypotheses (realizer : context.Realizes substitution assumptions) :
    ProofSyntax.HypothesisSubstitution (context.hypotheses.map (subst substitution)) assumptions :=
  fun occurrence => by
    let position : Fin Γ.length := occurrence.cast (by simp)
    let index := Var.ofFin Γ position
    have selected := context.hypotheses_get index
    apply ProofSyntax.castIndices rfl ?_ (realizer index)
    simp only [List.get_eq_getElem, List.getElem_map]
    rw [← selected]
    simp [Telescope.occurrence, index, position, CheckableFragment.Var.toFin_ofFin, List.get_eq_getElem]

theorem hypotheses_free (realizer : context.Realizes substitution assumptions)
    (free : ∀ {type} (index : Var Γ type), (realizer index).FunctionExtensionalityFree) :
    ∀ occurrence, (hypotheses realizer occurrence).FunctionExtensionalityFree := by
  intro occurrence
  simpa only [hypotheses, ProofSyntax.functionExtensionalityFree_castIndices] using
    free (Var.ofFin Γ (occurrence.cast (by simp)))

/-- Guard evidence for the variables is sufficient for every retained rule. -/
def transport (realizer : context.Realizes substitution assumptions)
    {formula : Formula Const Γ} (proof : ProofSyntax Const context.hypotheses formula) :
    ProofSyntax Const assumptions (subst substitution formula) :=
  ProofSyntax.substituteHypotheses realizer.hypotheses (ProofSyntax.subst substitution proof)

def identity (context : Telescope Const Γ) : context.Realizes Subst.id context.hypotheses :=
  fun index => ProofSyntax.castIndices rfl (subst_id _).symm (context.variableProof index)

def comp {next : Subst Const Ξ Ω} {later : List (Formula Const Ω)}
    (first : context.Realizes substitution target.hypotheses)
    (second : target.Realizes next later) : context.Realizes (Subst.comp next substitution) later :=
  fun index => ProofSyntax.castIndices rfl (subst_comp _ _ _) (second.transport (first index))

def lift (realizer : context.Realizes substitution target.hypotheses)
    (predicate : Term Const Γ (type ⇒ .prop)) :
    (context.snoc predicate).Realizes (Subst.lift substitution)
      (target.snoc (subst substitution predicate)).hypotheses := by
  intro carrier index
  cases index with
  | vz =>
      simpa [guard, domain, subst, subst_weaken, Subst.lift] using
        (target.snoc (subst substitution predicate)).variableProof Var.vz
  | vs prior =>
      refine ProofSyntax.castIndices ?_ ?_
        (ProofSyntax.prepend (.app (weaken (subst substitution predicate)) (.var .vz))
          (ProofSyntax.rename Rename.weaken (realizer prior)))
      · rfl
      · simp only [guard, domain, subst, subst_weaken, Subst.lift]
        rfl

end Realizes

/-- Abstract a body whose type guard is proved in the extended telescope. -/
def lambdaMember {result : Ty Base} (context : Telescope Const Γ)
    (predicate : Term Const Γ (type ⇒ .prop)) (family : Term Const (type :: Γ) (result ⇒ .prop))
    (body : Term Const (type :: Γ) result)
    (typed : ProofSyntax Const (context.snoc predicate).hypotheses (.app family body)) :
    ProofSyntax Const context.hypotheses (.app (PredicateProducts.pi predicate family) (.lam body)) := by
  have cancels : instantiate (.var (.vz : Var (type :: Γ) type))
      (rename (Rename.lift Rename.weaken) body) = body := by
    rw [instantiate, subst_rename]
    trans subst Subst.id body
    · apply subst_ext
      intro carrier index
      cases index <;> rfl
    · exact subst_id body
  let computation : ProofSyntax Const (context.snoc predicate).hypotheses
      (.eq (.app (weaken (.lam body)) (.var .vz)) body) :=
    ProofSyntax.castIndices rfl (congrArg (Term.eq (.app (weaken (.lam body)) (.var .vz))) cancels)
      (.beta (.var .vz) (rename (Rename.lift Rename.weaken) body))
  apply PredicateProducts.introduce predicate family (.lam body)
  exact .impE (.eqPropER (.eqAppArg family computation)) typed

theorem lambdaMember_free {result : Ty Base} (context : Telescope Const Γ)
    (predicate : Term Const Γ (type ⇒ .prop)) (family : Term Const (type :: Γ) (result ⇒ .prop))
    (body : Term Const (type :: Γ) result)
    (typed : ProofSyntax Const (context.snoc predicate).hypotheses (.app family body))
    (free : typed.FunctionExtensionalityFree) :
    (context.lambdaMember predicate family body typed).FunctionExtensionalityFree := by
  apply PredicateProducts.introduce_free
  simpa [ProofSyntax.FunctionExtensionalityFree, ProofSyntax.functionExtensionalityFree_castIndices] using free

def Satisfies (model : HenkinModel.{u,v,w} Base Const) (context : Telescope Const Γ)
    (values : model.Valuation Γ) : Prop := Soundness.SatisfiesHyps model values context.hypotheses

theorem satisfies_snoc (model : HenkinModel.{u,v,w} Base Const) (context : Telescope Const Γ)
    (predicate : Term Const Γ (type ⇒ .prop)) (values : model.Valuation Γ)
    (value : Ty.denote model.Carrier type) :
    (context.snoc predicate).Satisfies model (model.extend values value) ↔
      context.Satisfies model values ∧ (model.denote predicate values value).down := by
  constructor
  · intro holds
    constructor
    · intro formula member
      have guard := holds (weaken formula) (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨formula, member, rfl⟩))
      simpa only [Soundness.denote_weaken] using guard
    · have guard := holds _ List.mem_cons_self
      change (model.denote (weaken predicate) (model.extend values value) value).down at guard
      simpa only [Soundness.denote_weaken] using guard
  · rintro ⟨prior, present⟩ formula member
    rcases List.mem_cons.mp member with rfl | member
    · change (model.denote (weaken predicate) (model.extend values value) value).down
      simpa only [Soundness.denote_weaken] using present
    · obtain ⟨before, inside, rfl⟩ := List.mem_map.mp member
      simpa only [Soundness.denote_weaken] using prior before inside

theorem satisfies_variable (model : HenkinModel.{u,v,w} Base Const) (context : Telescope Const Γ)
    (values : model.Valuation Γ) (holds : context.Satisfies model values) (index : Var Γ type) :
    (model.denote (context.guard index) values).down := by
  apply holds
  rw [← context.hypotheses_get index]
  exact List.get_mem _ _

theorem Realizes.satisfies_subst (model : HenkinModel.{u,v,w} Base Const)
    (respects : model.FunctionsRespectEqv) {context : Telescope Const Γ}
    {substitution : Subst Const Γ Ξ} {assumptions : List (Formula Const Ξ)}
    (realizer : context.Realizes substitution assumptions) (values : model.Valuation Ξ)
    (admitted : model.ValuationAdmissible values) (holds : Soundness.SatisfiesHyps model values assumptions) :
    context.Satisfies model (Soundness.substVal model substitution values) := by
  intro formula member
  obtain ⟨position, selected⟩ := List.mem_iff_get.mp member
  let occurrence : Fin (context.hypotheses.map (subst substitution)).length := position.cast (by simp)
  have derived := Soundness.extDerivation_sound (realizer.hypotheses occurrence).erase respects admitted holds
  have selected' : (context.hypotheses.map (subst substitution)).get occurrence = subst substitution formula := by
    simpa [occurrence, List.get_eq_getElem] using congrArg (subst substitution) selected
  rw [selected', Soundness.denote_subst] at derived
  exact derived

#print axioms hypotheses_get
#print axioms Realizes.transport
#print axioms Realizes.comp
#print axioms Realizes.lift
#print axioms Realizes.satisfies_subst
#print axioms lambdaMember_free
#print axioms satisfies_snoc
end Telescope
end Mettapedia.Logic.HOL.PredicateContexts
