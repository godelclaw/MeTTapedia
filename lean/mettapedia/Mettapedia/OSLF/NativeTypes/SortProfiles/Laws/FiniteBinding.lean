import Mettapedia.GSLT.LanguageDef.BindingSignatureValuation
import Mettapedia.OSLF.Syntax.BindingSchemaInterpretation
import Mettapedia.OSLF.Framework.ModalHypercube

open Mettapedia.OSLF.Framework

/-!
# Finite sort-law checks in the actual binding valuation model

Base carrier values are the two code sorts. Arrow carriers retain complete
functions. Metavariables range over complete functions on their declared
dependency contexts, including nonconstant functions. The checker enumerates
that finite space and evaluates the existing binding interpretation.

Collection lists and unbounded multiple-binder sequences do not acquire a
false finite instance. Their type status is explicitly outside this finite
valuation fragment. Constructor meanings are semantic input, not assumed
equation-satisfaction predicates.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FreeBindingTerms
open Mettapedia.OSLF.Binding.BindingEquationInterpretation
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

abbrev Base (_ : String) := HSort
abbrev Value := Valuation.Value Base
abbrev Context (language : LanguageDef) := Valuation.Context language Base
abbrev Constructors (language : LanguageDef) := Valuation.Constructors language Base

def finiteType : TypeExpr → Bool
  | .base _ => true
  | .arrow domain codomain => finiteType domain && finiteType codomain
  | .multiBinder _ | .collection _ _ => false

def finiteContext (types : List TypeExpr) : Bool := types.all finiteType

def finiteMetaContext (metas : List (List TypeExpr × TypeExpr)) : Bool :=
  metas.all fun entry => finiteContext entry.1 && finiteType entry.2

theorem finiteMetaContext_member (metas : List (List TypeExpr × TypeExpr))
    (admitted : finiteMetaContext metas = true) (entry : List TypeExpr × TypeExpr)
    (member : entry ∈ metas) : finiteContext entry.1 = true ∧ finiteType entry.2 = true := by
  have checked := List.all_eq_true.mp admitted entry member
  simpa only [Bool.and_eq_true] using checked

mutual

@[instance_reducible] def valueFintype : (type : TypeExpr) → finiteType type = true → Fintype (Value type)
  | .base _, _ => inferInstanceAs (Fintype HSort)
  | .arrow domain codomain, admitted => by
      have both : finiteType domain = true ∧ finiteType codomain = true := by simpa [finiteType] using admitted
      letI := valueFintype domain both.1
      letI := valueDecidableEq domain both.1
      letI := valueFintype codomain both.2
      exact inferInstanceAs (Fintype (Value domain → Value codomain))
  | .multiBinder _, admitted => by cases admitted
  | .collection _ _, admitted => by cases admitted

@[instance_reducible] def valueDecidableEq : (type : TypeExpr) → finiteType type = true → DecidableEq (Value type)
  | .base _, _ => inferInstanceAs (DecidableEq HSort)
  | .arrow domain codomain, admitted => by
      have both : finiteType domain = true ∧ finiteType codomain = true := by simpa [finiteType] using admitted
      letI := valueFintype domain both.1
      letI := valueDecidableEq codomain both.2
      exact inferInstanceAs (DecidableEq (Value domain → Value codomain))
  | .multiBinder _, admitted => by cases admitted
  | .collection _ _, admitted => by cases admitted

end

@[instance_reducible] def contextFintype (language : LanguageDef) :
    (types : List TypeExpr) → finiteContext types = true → Fintype (Context language types)
  | [], _ => inferInstanceAs (Fintype PUnit)
  | type :: types, admitted => by
      have both : finiteType type = true ∧ finiteContext types = true := by
        simpa only [finiteContext, List.all_cons, Bool.and_eq_true] using admitted
      letI := valueFintype type both.1
      letI := contextFintype language types both.2
      exact inferInstanceAs (Fintype (Value type × Context language types))

@[instance_reducible] def contextDecidableEq (language : LanguageDef) :
    (types : List TypeExpr) → finiteContext types = true → DecidableEq (Context language types)
  | [], _ => inferInstanceAs (DecidableEq PUnit)
  | type :: types, admitted => by
      have both : finiteType type = true ∧ finiteContext types = true := by
        simpa only [finiteContext, List.all_cons, Bool.and_eq_true] using admitted
      letI := valueDecidableEq type both.1
      letI := contextDecidableEq language types both.2
      exact inferInstanceAs (DecidableEq (Value type × Context language types))

abbrev MetaFunctions (language : LanguageDef) (metas : List (MetaArity (signatureOf language))) : Type :=
  (index : Fin metas.length) → Context language (metas.get index).1 → Value (metas.get index).2

@[instance_reducible] def metaFunctionsFintype (language : LanguageDef) (metas : List (MetaArity (signatureOf language)))
    (admitted : finiteMetaContext metas = true) : Fintype (MetaFunctions language metas) := by
  letI : ∀ index : Fin metas.length, Fintype (Context language (metas.get index).1) := fun index =>
    contextFintype language (metas.get index).1
      (finiteMetaContext_member metas admitted _ (List.get_mem metas index)).1
  letI : ∀ index : Fin metas.length, DecidableEq (Context language (metas.get index).1) := fun index =>
    contextDecidableEq language (metas.get index).1
      (finiteMetaContext_member metas admitted _ (List.get_mem metas index)).1
  letI : ∀ index : Fin metas.length, Fintype (Value (metas.get index).2) := fun index =>
    valueFintype (metas.get index).2
      (finiteMetaContext_member metas admitted _ (List.get_mem metas index)).2
  exact inferInstance

def value (language : LanguageDef) (constructors : Constructors language)
    (metas : List (MetaArity (signatureOf language)))
    (functions : MetaFunctions language metas) {bound : List TypeExpr} {type : TypeExpr}
    (term : Term (withMetas (signatureOf language) metas) bound type)
    (environment : Context language bound) : Value type :=
  Valuation.readContext constructors
    (interpretSchema (Valuation.algebra constructors)
      (fun index => Valuation.ofFunction constructors (functions index)) term) environment

def Satisfies (language : LanguageDef) (constructors : Constructors language)
    (metas : List (MetaArity (signatureOf language)))
    {bound : List TypeExpr} {type : TypeExpr}
    (left right : Term (withMetas (signatureOf language) metas) bound type) : Prop :=
  ∀ functions : MetaFunctions language metas, ∀ environment : Context language bound,
    value language constructors metas functions left environment =
      value language constructors metas functions right environment

def check (language : LanguageDef) (constructors : Constructors language)
    (metas : List (MetaArity (signatureOf language)))
    {bound : List TypeExpr} {type : TypeExpr}
    (left right : Term (withMetas (signatureOf language) metas) bound type)
    (metaFinite : finiteMetaContext metas = true) (boundFinite : finiteContext bound = true)
    (resultFinite : finiteType type = true) : Bool :=
  letI := metaFunctionsFintype language metas metaFinite
  letI := contextFintype language bound boundFinite
  letI := valueDecidableEq type resultFinite
  decide (∀ functions : MetaFunctions language metas, ∀ environment : Context language bound,
    value language constructors metas functions left environment =
      value language constructors metas functions right environment)

theorem check_iff (language : LanguageDef) (constructors : Constructors language)
    (metas : List (MetaArity (signatureOf language)))
    {bound : List TypeExpr} {type : TypeExpr}
    (left right : Term (withMetas (signatureOf language) metas) bound type)
    (metaFinite : finiteMetaContext metas = true) (boundFinite : finiteContext bound = true)
    (resultFinite : finiteType type = true) :
    check language constructors metas left right metaFinite boundFinite resultFinite = true ↔
      Satisfies language constructors metas left right := by
  let := metaFunctionsFintype language metas metaFinite
  let := contextFintype language bound boundFinite
  let := valueDecidableEq type resultFinite
  unfold check Satisfies
  exact decide_eq_true_iff

theorem list_carriers_not_admitted (kind : CollType) (element : TypeExpr) :
    finiteType (.collection kind element) = false := rfl

theorem unbounded_binder_sequences_not_admitted (domain : TypeExpr) :
    finiteType (.multiBinder domain) = false := rfl

end Mettapedia.OSLF.NativeTypes.SortProfiles.Laws.FiniteBinding
