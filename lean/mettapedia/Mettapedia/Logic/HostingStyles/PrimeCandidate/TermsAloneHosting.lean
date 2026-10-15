import Mettapedia.GSLT.Contexts.TermsAlone
import Mettapedia.GSLT.Contexts.ReductionProfiles

/-!
# Hosting on terms alone: restriction, the region of the image, inert data

A theory whose contexts use each hole once, or that has no context but the
hole, receives no map from a theory that discards or copies.  For such a host
the sources are taken by their terms (`GSLT.termsAlone`).  Three
constructions for that level:

* **Restriction.**  A map of theories restricts to the terms of each
  interface of its source (`ContextMap.onTerms`), and a hosting map stays
  hosting (`ContextMap.Hosting.onTerms`, `ContextMap.Hosting.betweenTerms`):
  hosting with all contexts implies hosting on terms alone.
* **The region of the image.**  A hosting map on terms is exhausting onto
  the region of the host that its image spans (`GSLT.region`,
  `ContextMap.ontoImage_hosting`, `ContextMap.ontoImage_exhausting`), and it
  is exhausting into a host given by its terms alone exactly when every term
  of the host is an image, up to the static equivalence
  (`ContextMap.ofTerms_exhausting_iff`).
* **Inert data.**  A family of terms of one interface, none with a step, no
  two identified (`ContextTheory.InertData`), hosts every theory without
  reduction whose classes it codes (`ContextTheory.InertData.codeMap_hosting`).
  This is where a calculus keeps a proof system.
-/

set_option autoImplicit false
set_option linter.dupNamespace false

namespace Mettapedia.GSLT

universe u v

/-! ## Restriction to the terms of an interface -/

namespace ContextMap

variable {source target : ContextTheory.{u}} (map : ContextMap source target)

/-- **A map of theories, on the terms of one interface of its source.** -/
def onTerms (interface : source.Interface) : ContextMap (source.gslt interface).termsAlone target :=
  ContextMap.ofTerms (source := source.gslt interface) (map.interface interface) map.term
    map.term_resp

/-- **A hosting map is hosting on the terms of each interface.** -/
theorem Hosting.onTerms {map : ContextMap source target} (hosting : map.Hosting)
    (interface : source.Interface) :
    (map.onTerms interface).Hosting := by
  rw [hosting_iff] at hosting
  exact (ofTerms_hosting_iff (source := source.gslt interface) _ _ _).mpr
    ⟨fun _ _ related => hosting.1 related,
      fun _ _ step => map.preservesRewrites_of_transitions hosting.2.1 step,
      fun _ _ step => map.reflectsRewrites_of_transitions hosting.2.2 step⟩

/-- A map of theories, from the terms of one interface of its source to the
terms of the image of that interface. -/
def betweenTerms (interface : source.Interface) :
    ContextMap (source.gslt interface).termsAlone
      (target.gslt (map.interface interface)).termsAlone :=
  ContextMap.ofTerms (source := source.gslt interface)
    (target := (target.gslt (map.interface interface)).termsAlone) PUnit.unit map.term map.term_resp

/-- A hosting map is hosting between the terms of an interface and the terms
of its image. -/
theorem Hosting.betweenTerms {map : ContextMap source target} (hosting : map.Hosting)
    (interface : source.Interface) :
    (map.betweenTerms interface).Hosting := by
  rw [hosting_iff] at hosting
  exact (ofTerms_hosting_iff (source := source.gslt interface)
    (target := (target.gslt (map.interface interface)).termsAlone) PUnit.unit map.term
    map.term_resp).mpr
    ⟨fun _ _ related => hosting.1 related,
      fun _ _ step => map.preservesRewrites_of_transitions hosting.2.1 step,
      fun _ _ step => map.reflectsRewrites_of_transitions hosting.2.2 step⟩

end ContextMap

/-! ## Regions -/

/-- **A region of a theory given by its terms**: the terms of a class, with
the static equivalence and the reduction between them. -/
def GSLT.region (theory : GSLT.{u}) (member : theory.Term → Prop) : GSLT.{u} where
  Term := {term : theory.Term // member term}
  equations :=
    ⟨fun first second => theory.equations.r first.1 second.1,
      fun _ => theory.equations.iseqv.refl _,
      fun related => theory.equations.iseqv.symm related,
      fun first second => theory.equations.iseqv.trans first second⟩
  rewrites := fun term next => theory.rewrites term.1 next.1
  rewrites_resp_left := fun {_ _ next} equivalent step => by
    obtain ⟨other, moved, related⟩ := theory.rewrites_resp_left equivalent step
    exact ⟨next, theory.rewrites_resp_right moved (theory.equations.iseqv.symm related),
      theory.equations.iseqv.refl _⟩
  rewrites_resp_right := fun step equivalent => theory.rewrites_resp_right step equivalent

namespace ContextMap

variable {source : GSLT.{u}} {target : ContextTheory.{u}} (point : target.Interface)
  (term : source.Term → target.Term point)

/-- The terms of the host that are images, up to the static equivalence. -/
def ImageClass (candidate : target.Term point) : Prop :=
  ∃ origin : source.Term, (target.equations point).r candidate (term origin)

variable (term_resp : ∀ {first second : source.Term}, source.equations.r first second →
  (target.equations point).r (term first) (term second))

/-- **A map on terms, onto the region of the host that its image spans.** -/
def ontoImage :
    ContextMap source.termsAlone ((target.gslt point).region (ImageClass point term)).termsAlone :=
  ContextMap.ofTerms (source := source)
    (target := ((target.gslt point).region (ImageClass point term)).termsAlone) PUnit.unit
    (fun origin => ⟨term origin, origin, (target.equations point).iseqv.refl _⟩) term_resp

/-- A hosting map on terms is hosting onto the region of its image. -/
theorem ontoImage_hosting (hosting : (ofTerms point term term_resp).Hosting) :
    (ontoImage point term term_resp).Hosting := by
  obtain ⟨reflectsEquations, preserves, reflects⟩ :=
    (ofTerms_hosting_iff point term term_resp).mp hosting
  refine (ofTerms_hosting_iff (source := source)
    (target := ((target.gslt point).region (ImageClass point term)).termsAlone) PUnit.unit
    (fun origin => ⟨term origin, origin, (target.equations point).iseqv.refl _⟩) term_resp).mpr
    ⟨reflectsEquations, preserves, fun first next step => ?_⟩
  exact reflects first next.1 step

/-- **A map on terms is exhausting onto the region of its image**: that
region of the host has nothing the source lacks. -/
theorem ontoImage_exhausting : (ontoImage point term term_resp).Exhausting := by
  intro arity holes result observer
  cases observer with
  | hole position only =>
      refine ⟨.hole position only, fun filling => ?_⟩
      exact ((target.gslt point).region (ImageClass point term)).equations.iseqv.symm
        ((ontoImage point term term_resp).equivariant (.hole position only) filling)
  | constant value empty =>
      obtain ⟨candidate, origin, related⟩ := value
      refine ⟨.constant origin empty, fun filling => ?_⟩
      refine ((target.gslt point).region (ImageClass point term)).equations.iseqv.trans
        (((target.gslt point).region (ImageClass point term)).equations.iseqv.symm
          ((ontoImage point term term_resp).equivariant (.constant origin empty) filling)) ?_
      exact (target.equations point).iseqv.symm related

end ContextMap

/-- **A map between theories given by their terms alone is exhausting
exactly when every term of the target is an image**, up to the static
equivalence. -/
theorem ContextMap.ofTerms_exhausting_iff {source target : GSLT.{u}}
    (term : source.Term → target.Term)
    (term_resp : ∀ {first second : source.Term}, source.equations.r first second →
      target.equations.r (term first) (term second)) :
    (ContextMap.ofTerms (source := source) (target := target.termsAlone) PUnit.unit term
        term_resp).Exhausting ↔
      ∀ candidate : target.Term, ∃ origin, target.equations.r candidate (term origin) := by
  constructor
  · intro exhausting candidate
    exact ContextMap.Exhausting.term_surjective _ exhausting (origin := PUnit.unit) candidate
  · intro surjective arity holes result observer
    cases observer with
    | hole position only => exact ⟨.hole position only, fun _ => target.equations.iseqv.refl _⟩
    | constant value empty =>
        obtain ⟨origin, related⟩ := surjective value
        exact ⟨.constant origin empty, fun _ => target.equations.iseqv.symm related⟩

/-! ## Inert data -/

namespace ContextTheory

/-- **Inert data** in a theory: a family of terms of one interface, none of
which has a step, no two of which the static equivalence identifies. -/
structure InertData (theory : ContextTheory.{u}) (Index : Type v) where
  /-- The interface at which the data live. -/
  interface : theory.Interface
  /-- The datum of an index. -/
  datum : Index → theory.Term interface
  normal : ∀ (index : Index) (next : theory.Term interface), ¬ theory.rewrites (datum index) next
  apart : ∀ first second : Index,
    (theory.equations interface).r (datum first) (datum second) → first = second

namespace InertData

variable {theory : ContextTheory.{u}} {Index Other : Type v} (data : theory.InertData Index)

/-- Inert data along an injection of indices. -/
def reindex (rename : Other → Index) (injective : Function.Injective rename) :
    theory.InertData Other where
  interface := data.interface
  datum := fun index => data.datum (rename index)
  normal := fun index => data.normal (rename index)
  apart := fun _ _ related => injective (data.apart _ _ related)

variable {source : GSLT.{u}} (code : source.Term → Index)

/-- The map that sends a term to the datum of its code. -/
def codeMap
    (respects : ∀ {first second : source.Term}, source.equations.r first second →
      code first = code second) : ContextMap source.termsAlone theory :=
  ContextMap.ofTerms data.interface (fun term => data.datum (code term)) fun related =>
    ContextMap.equations_of_eq (congrArg data.datum (respects related))

/-- **Inert data host every theory without reduction whose classes they
code.** -/
theorem codeMap_hosting
    (respects : ∀ {first second : source.Term}, source.equations.r first second →
      code first = code second)
    (reflects : ∀ first second : source.Term, code first = code second →
      source.equations.r first second)
    (static : ∀ term next : source.Term, ¬ source.rewrites term next) :
    (data.codeMap code respects).Hosting :=
  (ContextMap.ofTerms_hosting_iff data.interface (fun term => data.datum (code term))
    (fun related => ContextMap.equations_of_eq (congrArg data.datum (respects related)))).mpr
    ⟨fun first second related => reflects first second (data.apart _ _ related),
      fun first next step => (static first next step).elim,
      fun first next step => (data.normal (code first) next step).elim⟩

end InertData

end ContextTheory

#print axioms ContextMap.Hosting.onTerms
#print axioms ContextMap.Hosting.betweenTerms
#print axioms GSLT.region
#print axioms ContextMap.ontoImage_hosting
#print axioms ContextMap.ontoImage_exhausting
#print axioms ContextMap.ofTerms_exhausting_iff
#print axioms ContextTheory.InertData.codeMap_hosting

end Mettapedia.GSLT
