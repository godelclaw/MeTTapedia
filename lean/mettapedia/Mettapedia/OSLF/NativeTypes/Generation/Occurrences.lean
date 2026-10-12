import Mettapedia.OSLF.Framework.RedexPosition
import Mettapedia.OSLF.MeTTaIL.GeneralTypedSites

open Mettapedia.OSLF.Framework

/-!
# Complete authored input to native type generation

The derivative enumerates every one-hole decomposition of every original
rewrite. Declaration positions remain distinct even when two declarations
have equal bodies. Its specification is the independently inductive `Selects`
judgment, which includes single and multiple binders, explicit substitutions
and ordered collection occurrences. Equations never discard structural sites.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.Occurrences

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.OSLF.Framework.RedexPosition

mutual

/-- Actual focus terms occurring in a syntax tree, before duplicate removal. -/
def subterms : Pattern → List Pattern
  | .bvar index => [.bvar index]
  | .fvar name => [.fvar name]
  | .apply constructor arguments =>
      .apply constructor arguments :: subtermsList arguments
  | .lambda binder body => .lambda binder body :: subterms body
  | .multiLambda arity binders body =>
      .multiLambda arity binders body :: subterms body
  | .subst body replacement => .subst body replacement :: (subterms body ++ subterms replacement)
  | .collection kind elements rest =>
      .collection kind elements rest :: subtermsList elements

def subtermsList : List Pattern → List Pattern
  | [] => []
  | pattern :: patterns => subterms pattern ++ subtermsList patterns

end

theorem subtermsList_append (left right : List Pattern) :
    subtermsList (left ++ right) = subtermsList left ++ subtermsList right := by
  induction left with
  | nil => rfl
  | cons pattern patterns ih => simp only [List.cons_append, subtermsList, ih, List.append_assoc]

theorem selected_focus_mem_subterms {focus host : Pattern} {context : OneHoleContext}
    (selected : Selects focus context host) : focus ∈ subterms host := by
  induction selected with
  | here => cases focus <;> simp [subterms]
  | apply _ ih => simp [subterms, subtermsList_append, subtermsList, ih]
  | lambda _ ih => simp [subterms, ih]
  | multiLambda _ ih => simp [subterms, ih]
  | substBody _ ih => simp [subterms, ih]
  | substReplacement _ ih => simp [subterms, ih]
  | collection _ ih => simp [subterms, subtermsList_append, subtermsList, ih]

structure Decomposition where
  context : OneHoleContext
  focus : Pattern
  deriving DecidableEq, Repr

/-- Enumerate each distinct focus once, then its independently certified
zipper derivative. Equal subterms at different addresses remain distinct. -/
def decompositions (host : Pattern) : List Decomposition :=
  (subterms host).eraseDups.flatMap fun focus =>
    (zippersAt focus host).map fun context => ⟨context, focus⟩

theorem decompositions_spec (host : Pattern) (site : Decomposition) :
    site ∈ decompositions host ↔ Selects site.focus site.context host := by
  constructor
  · intro member
    obtain ⟨focus, _, member⟩ := List.mem_flatMap.mp member
    obtain ⟨context, selected, equality⟩ := List.mem_map.mp member
    cases equality
    exact zippersAt_sound selected
  · intro selected
    apply List.mem_flatMap.mpr
    refine ⟨site.focus, ?_, ?_⟩
    · simpa only [List.mem_eraseDups] using selected_focus_mem_subterms selected
    · exact List.mem_map.mpr ⟨site.context, zippersAt_complete selected, rfl⟩

structure Site extends Decomposition where
  declaration : Nat
  rule : RewriteRule
  deriving Repr

/-- Every original authored rewrite at every one-hole position. -/
def generate (language : LanguageDef) : List Site :=
  language.rewrites.zipIdx.flatMap fun (rule, index) =>
    (decompositions rule.left).map fun site => ⟨site, index, rule⟩

theorem generate_spec (language : LanguageDef) (site : Site) :
    site ∈ generate language ↔
      (site.rule, site.declaration) ∈ language.rewrites.zipIdx ∧
      Selects site.focus site.context site.rule.left := by
  constructor
  · intro member
    obtain ⟨⟨rule, index⟩, origin, member⟩ := List.mem_flatMap.mp member
    obtain ⟨decomposition, occurs, equality⟩ := List.mem_map.mp member
    cases equality
    exact ⟨origin, (decompositions_spec _ _).mp occurs⟩
  · rintro ⟨origin, selected⟩
    exact List.mem_flatMap.mpr ⟨(site.rule, site.declaration), origin,
      List.mem_map.mpr ⟨site.toDecomposition, (decompositions_spec _ _).mpr selected, rfl⟩⟩

theorem generated_source_reconstructed {language : LanguageDef} {site : Site}
    (member : site ∈ generate language) : site.context.fill site.focus = site.rule.left :=
  ((generate_spec _ _).mp member).2.fill_eq

def Site.position (site : Site) : Position := contextAddress site.context

/-- Exactly the free metavariable names of the context, with no free name
contributed by the placeholder used to read the hole. -/
def contextNames (context : OneHoleContext) : List String :=
  fvarNames (context.fill (.bvar 0))

def Site.relyNames (site : Site) : List String :=
  ((contextNames site.context).filter fun name =>
    !(fvarNames site.focus).contains name).eraseDups

def Site.hiddenNames (site : Site) : List String :=
  ((fvarNames site.focus).filter fun name =>
    !(contextNames site.context).contains name).eraseDups

inductive LocalSlot where
  | rely (name : String)
  | output
  deriving DecidableEq, Repr

def Site.localSlots (site : Site) : List LocalSlot :=
  site.relyNames.map LocalSlot.rely ++ [.output]

theorem rely_names_spec (site : Site) (name : String) :
    name ∈ site.relyNames ↔ name ∈ contextNames site.context ∧
      name ∉ fvarNames site.focus := by
  simp [Site.relyNames, List.mem_filter]

theorem hidden_names_spec (site : Site) (name : String) :
    name ∈ site.hiddenNames ↔ name ∈ fvarNames site.focus ∧
      name ∉ contextNames site.context := by
  simp [Site.hiddenNames, List.mem_filter]

theorem localSlots_length (site : Site) :
    site.localSlots.length = site.relyNames.length + 1 := by
  simp [Site.localSlots]

theorem equations_preserve_generated_sites (language : LanguageDef)
    (equations : List Equation) :
    generate {language with equations := equations} = generate language := rfl

/-- The independently selected ordinary address reads back the chosen focus.
The binder's body address is retained, rather than pruning deep positions. -/
theorem selected_subtermAt {focus host : Pattern} {context : OneHoleContext}
    (selected : Selects focus context host) :
    subtermAt host (contextAddress context) = some focus := by
  induction selected with
  | here => rfl
  | @apply innerHost inner constructor before after _ ih =>
      simpa [subtermAt, childAt, children, contextAddress,
        List.getElem?_append] using ih
  | lambda _ ih => simpa [subtermAt, childAt, children, contextAddress] using ih
  | multiLambda _ ih => simpa [subtermAt, childAt, children, contextAddress] using ih
  | substBody _ ih => simpa [subtermAt, childAt, children, contextAddress] using ih
  | substReplacement _ ih => simpa [subtermAt, childAt, children, contextAddress] using ih
  | @collection inner innerHost kind before after rest _ ih =>
      simpa [subtermAt, childAt, children, contextAddress,
        List.getElem?_append] using ih

theorem generated_focus_readback {language : LanguageDef} {site : Site}
    (member : site ∈ generate language) :
    subtermAt site.rule.left site.position = some site.focus :=
  selected_subtermAt ((generate_spec _ _).mp member).2

end Mettapedia.OSLF.NativeTypes.Generation.Occurrences
