import Mettapedia.Logic.HOL.ConstantSubstitutionSemantics
import Mettapedia.Logic.HOL.ImpredicativeConnectives
import Mettapedia.Logic.HOL.TypeSubstitutionModelCoherence

/-!
# A definitional extension of a Henkin model

A fresh typed constant can be interpreted by a closed term of the old
signature. The extension retains the old carriers, admissible domains, and
the meanings of every old term. Its new constant has the body's denotation
by construction, using the established closed-term substitution reduct.

This is a semantic model of a definition, not an assumption that an arbitrary
interpretation of a fresh symbol happens to respect it.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v v' w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Extend an indexed HOL constant signature by one new symbol at `target`. -/
inductive DefinedConst (Const : Ty Base → Type v) (target : Ty Base) :
    Ty Base → Type (max u v) where
  | old {type : Ty Base} : Const type → DefinedConst Const target type
  | defined : DefinedConst Const target target

namespace DefinedConst

/-- Instantiation maps the fresh symbol to the same fresh definition at its
instantiated type; old symbols follow the supplied signature map. -/
def typeInstance {Base' : Type u} {Const' : Ty Base' → Type v'} {target : Ty Base}
    (substitution : Base → Ty Base')
    (symbols : ∀ {type}, Const type → Const' (Ty.substitute substitution type)) :
    ∀ {type}, DefinedConst Const target type →
      DefinedConst Const' (Ty.substitute substitution target) (Ty.substitute substitution type)
  | _, .old symbol => .old (symbols symbol)
  | _, .defined => .defined

/-- Eliminate the fresh symbol by its closed defining body. -/
def expansion {target : Ty Base} (body : ClosedTerm Const target) :
    ∀ {type : Ty Base}, DefinedConst Const target type → ClosedTerm Const type
  | _, .old symbol => .const symbol
  | _, .defined => body

/-- The old syntax is embedded without changing its variables or formers. -/
def embed {target : Ty Base} {gamma : Ctx Base} {type : Ty Base}
    (term : Term Const gamma type) : Term (DefinedConst Const target) gamma type :=
  mapConst DefinedConst.old term

/-- Expanding a term from the old signature recovers it exactly. -/
theorem expansion_embed {target : Ty Base} (body : ClosedTerm Const target)
    {gamma : Ctx Base} {type : Ty Base} (term : Term Const gamma type) :
    substConst (expansion body) (embed (target := target) term) = term := by
  induction term with
  | const symbol => simp [embed, expansion, substConst]
  | _ => simp_all [embed, mapConst, substConst]

/-- Derived logical connectives commute with embedding an old signature into
its definitional extension. -/
theorem expand_embed {target : Ty Base}
    {gamma : Ctx Base} {type : Ty Base} (term : Term Const gamma type) :
    ImpredicativeConnectives.expand (embed (target := target) term) =
      embed (target := target) (ImpredicativeConnectives.expand term) := by
  induction term <;>
    simp_all [embed, mapConst, ImpredicativeConnectives.expand,
      ImpredicativeConnectives.truth, ImpredicativeConnectives.falsity,
      ImpredicativeConnectives.conjunction, ImpredicativeConnectives.disjunction,
      ImpredicativeConnectives.existential]

end DefinedConst

namespace HenkinModel

/-- A genuine model of a definitional extension; no new closure hypothesis is
needed because the defining body was already a typed closed source term. -/
def definitionExtension (M : HenkinModel.{u, v, w} Base Const)
    {target : Ty Base} (body : ClosedTerm Const target) :
    HenkinModel.{u, max u v, w} Base (DefinedConst Const target) :=
  constantSubstitutionReduct (DefinedConst.expansion body) M

@[simp] theorem definitionExtension_carrier (M : HenkinModel.{u, v, w} Base Const)
    {target : Ty Base} (body : ClosedTerm Const target) :
    (M.definitionExtension body).Carrier = M.Carrier := rfl

/-- Old constant meanings survive the definitional extension. -/
@[simp] theorem definitionExtension_old (M : HenkinModel.{u, v, w} Base Const)
    {target type : Ty Base} (body : ClosedTerm Const target) (symbol : Const type) :
    (M.definitionExtension body).constDen (DefinedConst.old symbol) =
      M.constDen symbol := rfl

/-- The fresh constant denotes the defining closed term. -/
@[simp] theorem definitionExtension_defined (M : HenkinModel.{u, v, w} Base Const)
    {target : Ty Base} (body : ClosedTerm Const target) :
    (M.definitionExtension body).constDen DefinedConst.defined =
      M.denote body (fun index => nomatch index) := rfl

/-- Conservative denotation for every old term, including open terms and
derived HOL connectives, at the same valuation. -/
theorem definitionExtension_embed (M : HenkinModel.{u, v, w} Base Const)
    {target : Ty Base} (body : ClosedTerm Const target)
    {gamma : Ctx Base} {type : Ty Base} (term : Term Const gamma type)
    (valuation : M.Valuation gamma) :
    (M.definitionExtension body).denote (DefinedConst.embed (target := target) term)
      valuation = M.denote term valuation := by
  change (constantSubstitutionReduct (DefinedConst.expansion body) M).denote
    (DefinedConst.embed (target := target) term) valuation = M.denote term valuation
  exact (denote_substConst (DefinedConst.expansion body) M
    (DefinedConst.embed (target := target) term) valuation).symm.trans
      (congrArg (fun t => M.denote t valuation) (DefinedConst.expansion_embed body term))

/-- Every old sentence keeps its truth value. Thus old theorem and axiom
validity is not silently strengthened or weakened by adding the definition. -/
theorem definitionExtension_models_embed (M : HenkinModel.{u, v, w} Base Const)
    {target : Ty Base} (body : ClosedTerm Const target)
    (formula : ClosedFormula Const) :
    (M.definitionExtension body).models (DefinedConst.embed (target := target) formula) ↔
      M.models formula :=
  Iff.of_eq (congrArg ULift.down
    (M.definitionExtension_embed body formula (fun index => nomatch index)))

/-- The actual defining equation, with the old body embedded into the
extended signature. -/
def definitionEquation {target : Ty Base} (body : ClosedTerm Const target) :
    ClosedFormula (DefinedConst Const target) :=
  .eq (.const DefinedConst.defined) (DefinedConst.embed body)

theorem definitionExtension_models_equation (M : HenkinModel.{u, v, w} Base Const)
    {target : Ty Base} (body : ClosedTerm Const target) :
    (M.definitionExtension body).models (definitionEquation body) := by
  apply (models_substConst (DefinedConst.expansion body) M (definitionEquation body)).mp
  simp only [definitionEquation, substConst, DefinedConst.expansion,
    DefinedConst.expansion_embed, weakenCtx_nil]
  exact M.eqv_refl (M.term_closed body (fun index => nomatch index)
    (by intro type index; nomatch index))

set_option backward.isDefEq.respectTransparency false in
/-- Extending by the actual instantiated body commutes with reindexing the
model. This is equality of the constructed model data, including the new
constant's value, rather than merely agreement on old sentences. -/
theorem definitionExtension_typeReduct {Base' : Type u} {Const' : Ty Base' → Type v'}
    (substitution : Base → Ty Base')
    (symbols : ∀ {type}, Const type → Const' (Ty.substitute substitution type))
    (M : HenkinModel.{u, v', w} Base' Const') (full : M.FullDomains)
    {target : Ty Base} (body : ClosedTerm Const target) :
    (standardTypeReduct substitution symbols M).definitionExtension body =
      standardTypeReduct substitution (DefinedConst.typeInstance substitution symbols)
        (M.definitionExtension (mapTypes substitution symbols body)) := by
  have extendedFull :
      ((standardTypeReduct substitution symbols M).definitionExtension body).FullDomains :=
    (constantSubstitutionReduct_fullDomains_iff (DefinedConst.expansion body) _).mpr
      (standardTypeReduct_fullDomains substitution symbols M)
  rw [← standard_eq_of_fullDomains _ extendedFull]
  apply standard_ext rfl
  intro type symbol
  cases symbol with
  | old constant => rfl
  | defined =>
    simp only [DefinedConst.typeInstance, definitionExtension_defined,
      definitionExtension_carrier]
    let valuation : M.Valuation ([].map (Ty.substitute substitution)) :=
      fun index => nomatch index
    have preserved := denote_mapTypes substitution symbols M full body valuation
    apply heq_of_eq
    calc
      _ = (standardTypeReduct substitution symbols M).denote body
          (typeReductValuation substitution symbols M valuation) :=
        denote_closed_valuation_eq _ body _ _
      _ = (Ty.denoteSubstituteEquiv substitution M.Carrier target).symm
          (M.denote (mapTypes substitution symbols body) valuation) :=
        (Ty.denoteSubstituteEquiv substitution M.Carrier target).eq_symm_apply.mpr preserved
      _ = _ := congrArg (Ty.denoteSubstituteEquiv substitution M.Carrier target).symm
        (denote_closed_valuation_eq M (mapTypes substitution symbols body) _ _)

/-- The defining equation and every extended-language sentence obey the
satisfaction condition of this same extension/reindexing construction. -/
theorem definitionExtension_models_typeReduct {Base' : Type u}
    {Const' : Ty Base' → Type v'} (substitution : Base → Ty Base')
    (symbols : ∀ {type}, Const type → Const' (Ty.substitute substitution type))
    (M : HenkinModel.{u, v', w} Base' Const') (full : M.FullDomains)
    {target : Ty Base} (body : ClosedTerm Const target)
    (sentence : ClosedFormula (DefinedConst Const target)) :
    ((standardTypeReduct substitution symbols M).definitionExtension body).models sentence ↔
      (M.definitionExtension (mapTypes substitution symbols body)).models
        (mapTypes substitution (DefinedConst.typeInstance substitution symbols) sentence) := by
  rw [definitionExtension_typeReduct substitution symbols M full body]
  exact models_mapTypes substitution (DefinedConst.typeInstance substitution symbols) _
    ((constantSubstitutionReduct_fullDomains_iff
      (DefinedConst.expansion (mapTypes substitution symbols body)) M).mpr full) sentence

/-- Freshness and typing alone do not force an arbitrary interpretation of a
new symbol to respect a proposed definition. Interpreting it as false cannot
validate the proposal that its body is true. -/
theorem unrelated_extension_disagrees (M : HenkinModel.{u, v, w} Base Const) :
    (M.definitionExtension (.bot : ClosedTerm Const .prop)).constDen
        (DefinedConst.defined : DefinedConst Const .prop .prop) ≠
      M.denote (.top : ClosedTerm Const .prop) (fun index => nomatch index) := by
  intro equal
  have contradiction : False = True := by
    exact congrArg ULift.down equal
  exact (contradiction.symm ▸ True.intro)

end HenkinModel

#print axioms DefinedConst.expansion_embed
#print axioms DefinedConst.expand_embed
#print axioms HenkinModel.definitionExtension
#print axioms HenkinModel.definitionExtension_embed
#print axioms HenkinModel.definitionExtension_models_embed
#print axioms HenkinModel.unrelated_extension_disagrees

end Mettapedia.Logic.HOL
