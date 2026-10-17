import Mettapedia.Logic.HostingStyles.AmbientSpace.Atoms

/-!
# The image of a context of λΠ terms, in every candidate that carries atoms

A context of λΠ terms (`TermContext`) is a term with named holes.  In a
language that declares application, abstraction and product as the candidate
does (`CarriesAtoms`), it has an image among the contexts of every reading in
which the holes of atoms are free (`AtomsFree`): the pattern of the same
shape, a hole a hole (`shapeContextAt`).

The image is given for any choice of what stands at the leaves of the context
that are no holes, its sorts, constants and variables (`leaf`): the plain atom
of the leaf, for a reading of terms as atoms; the atom of the leaf in a run,
for a reading of terms as located atoms.  What the image does to its fillings
is the pattern `shapePatternAt` (`act_shapeContextAt`); with plain atoms at
the leaves and atoms of terms with free variables below the width in the
holes, that pattern is the atom of the filled context (`shapePatternAt_atoms`).

This is the construction `atomContextAt` of the module
`AtomsReduce.ScopedContexts`, for an arbitrary presentation that carries atoms
and for arbitrary leaves.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientSpace

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (TermContext)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings

/-! ## Three contexts of a presentation that carries atoms -/

/-- **A hole for atoms beneath `width` binders, placed beneath `extra` more.**
What fills it is read there as it is written. -/
def placedHoleOf (presentation : ValidatedLanguageDef) (width extra : Nat) :
    Contexts.Context presentation (fun _ : Unit => atomInterface width)
      (atomInterface (width + extra)) where
  shape := .hole ()
  linear := MultiHoleContext.linear_hole
  sorted := fun {target} morphism filling => by
    have extended := wellSorted_extendOuter (filling ()).2
      (List.replicate extra (mapTypeExpr morphism.symbols (.base "Atom")))
    have stage : ((atomInterface (width + extra)).map morphism.symbols).stage =
        ((atomInterface width).map morphism.symbols).stage ++
          List.replicate extra (mapTypeExpr morphism.symbols (.base "Atom")) := by
      show (List.replicate (width + extra) (TypeExpr.base "Atom")).map
          (mapTypeExpr morphism.symbols) =
        (List.replicate width (TypeExpr.base "Atom")).map (mapTypeExpr morphism.symbols) ++
          List.replicate extra (mapTypeExpr morphism.symbols (.base "Atom"))
      simp only [List.replicate_add, List.map_append, List.map_replicate]
    show OpenPatternWellSorted target.language FreeTypeContext.empty
      ((atomInterface (width + extra)).map morphism.symbols).stage
      ((atomInterface width).map morphism.symbols).type (filling ()).1
    rw [stage]
    exact extended

/-- Filling the placed hole returns what fills it, as it is written. -/
theorem fill_placedHoleOf (presentation : ValidatedLanguageDef) (width extra : Nat)
    (filling : (index : Unit) → Contexts.Term presentation.language (atomInterface width)) :
    ((placedHoleOf presentation width extra).fill filling).1 = (filling ()).1 :=
  rfl

/-- **The application of an atom to an atom, as a context of two holes.** -/
def applicationContextOf (presentation : ValidatedLanguageDef)
    (carries : CarriesAtoms presentation.language) (stage : List TypeExpr) :
    Contexts.Context presentation
      (fun _ : Bool => (⟨.base "Atom", stage⟩ : Contexts.Interface)) ⟨.base "Atom", stage⟩ :=
  binaryContext presentation (fun _ => "Atom") (rule := applicationConstructor)
    (firstName := "f") (secondName := "a") (carries _ (by decide)) rfl rfl stage

theorem fill_applicationContextOf (presentation : ValidatedLanguageDef)
    (carries : CarriesAtoms presentation.language) (stage : List TypeExpr)
    (filling : (index : Bool) → Contexts.Term presentation.language ⟨.base "Atom", stage⟩) :
    ((applicationContextOf presentation carries stage).fill filling).1 =
      .apply "App" [(filling false).1, (filling true).1] :=
  rfl

/-! ## The image of a context -/

variable {declared : Contexts.Interface → Prop}

/-- **The image of a context of terms**, beneath `extra` of its binders: the
pattern of the same shape, as a context of a reading in which the holes of
atoms are free.  A hole is placed as it is, beneath the binders above it; a
sort, a constant and a variable of the context are what `leaf` says. -/
def shapeContextAt (presentation : ValidatedLanguageDef)
    (carries : CarriesAtoms presentation.language) (base : BasePremiseEvaluator)
    (free : AtomsFree declared) (width : Nat)
    (leaf : (extra : Nat) → LF.Term →
      Contexts.Term presentation.language (atomInterface (width + extra)))
    {slots : Type} : (extra : Nat) → TermContext slots →
      (contextTheory base presentation).RegionContext declared
        (fun _ : slots => atomInterface width) (atomInterface (width + extra))
  | extra, .hole slot =>
      ContextTheory.RegionContext.substitute
        (ContextTheory.RegionContext.ofContext (theory := contextTheory base presentation)
          (declared := declared) (placedHoleOf presentation width extra) fun _ _ => free _)
        (fun _ : Unit => ContextTheory.RegionContext.project
          (theory := contextTheory base presentation) (declared := declared)
          (fun _ : slots => atomInterface width) slot fun _ => free _)
        fun _ => free _
  | extra, .srt sort =>
      ContextTheory.discardingConstant (theory := contextTheory base presentation)
        (declared := declared) (fun _ : slots => atomInterface width) (fun _ => free _)
        (leaf extra (.srt sort))
  | extra, .con name =>
      ContextTheory.discardingConstant (theory := contextTheory base presentation)
        (declared := declared) (fun _ : slots => atomInterface width) (fun _ => free _)
        (leaf extra (.con name))
  | extra, .var index =>
      ContextTheory.discardingConstant (theory := contextTheory base presentation)
        (declared := declared) (fun _ : slots => atomInterface width) (fun _ => free _)
        (leaf extra (.var index))
  | extra, .app function argument =>
      ContextTheory.RegionContext.substitute
        (ContextTheory.RegionContext.ofContext (theory := contextTheory base presentation)
          (declared := declared)
          (applicationContextOf presentation carries
            (List.replicate (width + extra) (.base "Atom")))
          fun _ _ => free _)
        (fun index : Bool =>
          bif index then shapeContextAt presentation carries base free width leaf extra argument
          else shapeContextAt presentation carries base free width leaf extra function)
        fun _ => free _
  | extra, .lam domain body =>
      ContextTheory.RegionContext.substitute
        (ContextTheory.RegionContext.ofContext (theory := contextTheory base presentation)
          (declared := declared)
          (binderContext presentation "Atom" "Atom" (rule := abstractionConstructor)
            (name := "a") (binder := "x") (bodyName := "body") (carries _ (by decide)) rfl rfl
            (List.replicate (width + extra) (.base "Atom")))
          fun _ index => by cases index <;> exact free _)
        (fun index : Bool =>
          match index with
          | false => shapeContextAt presentation carries base free width leaf extra domain
          | true => shapeContextAt presentation carries base free width leaf (extra + 1) body)
        fun _ => free _
  | extra, .pi domain body =>
      ContextTheory.RegionContext.substitute
        (ContextTheory.RegionContext.ofContext (theory := contextTheory base presentation)
          (declared := declared)
          (binderContext presentation "Atom" "Atom" (rule := productConstructor)
            (name := "a") (binder := "x") (bodyName := "body") (carries _ (by decide)) rfl rfl
            (List.replicate (width + extra) (.base "Atom")))
          fun _ index => by cases index <;> exact free _)
        (fun index : Bool =>
          match index with
          | false => shapeContextAt presentation carries base free width leaf extra domain
          | true => shapeContextAt presentation carries base free width leaf (extra + 1) body)
        fun _ => free _

/-- **What the image of a context does to its fillings, as a pattern**: the
leaves and the fillings in the shape of the context. -/
def shapePatternAt {slots : Type} (leaf : Nat → LF.Term → Pattern) (hole : slots → Pattern) :
    Nat → TermContext slots → Pattern
  | _, .hole slot => hole slot
  | extra, .srt sort => leaf extra (.srt sort)
  | extra, .con name => leaf extra (.con name)
  | extra, .var index => leaf extra (.var index)
  | extra, .app function argument =>
      .apply "App" [shapePatternAt leaf hole extra function, shapePatternAt leaf hole extra argument]
  | extra, .lam domain body =>
      .apply "Lam" [shapePatternAt leaf hole extra domain,
        .lambda none (shapePatternAt leaf hole (extra + 1) body)]
  | extra, .pi domain body =>
      .apply "Pi" [shapePatternAt leaf hole extra domain,
        .lambda none (shapePatternAt leaf hole (extra + 1) body)]

/-- **The image of a context, filled, is the pattern of its shape.** -/
theorem act_shapeContextAt (presentation : ValidatedLanguageDef)
    (carries : CarriesAtoms presentation.language) (base : BasePremiseEvaluator)
    (free : AtomsFree declared) (width : Nat)
    (leaf : (extra : Nat) → LF.Term →
      Contexts.Term presentation.language (atomInterface (width + extra)))
    {slots : Type}
    (filling : slots → Contexts.Term presentation.language (atomInterface width)) :
    ∀ (context : TermContext slots) (extra : Nat),
      ((shapeContextAt presentation carries base free width leaf extra context).act filling).1 =
        shapePatternAt (fun extra term => (leaf extra term).1) (fun slot => (filling slot).1)
          extra context := by
  intro context
  induction context with
  | hole slot => intro extra; rfl
  | srt sort => intro extra; rfl
  | con name => intro extra; rfl
  | var index => intro extra; rfl
  | app function argument ihFunction ihArgument =>
      intro extra
      show Pattern.apply "App"
          [((shapeContextAt presentation carries base free width leaf extra function).act
              filling).1,
            ((shapeContextAt presentation carries base free width leaf extra argument).act
              filling).1] = _
      rw [ihFunction extra, ihArgument extra]
      rfl
  | lam domain body ihDomain ihBody =>
      intro extra
      show Pattern.apply "Lam"
          [((shapeContextAt presentation carries base free width leaf extra domain).act
              filling).1,
            .lambda none ((shapeContextAt presentation carries base free width leaf (extra + 1)
              body).act filling).1] = _
      rw [ihDomain extra, ihBody (extra + 1)]
      rfl
  | pi domain body ihDomain ihBody =>
      intro extra
      show Pattern.apply "Pi"
          [((shapeContextAt presentation carries base free width leaf extra domain).act
              filling).1,
            .lambda none ((shapeContextAt presentation carries base free width leaf (extra + 1)
              body).act filling).1] = _
      rw [ihDomain extra, ihBody (extra + 1)]
      rfl

/-- **With plain atoms at the leaves and atoms of terms with free variables
below the width in the holes, the pattern is the atom of the filled
context.** -/
theorem shapePatternAt_atoms {slots : Type} (width : Nat) (filling : slots → LF.Term)
    (within : ∀ slot, LF.WellScoped width (filling slot)) :
    ∀ (context : TermContext slots) (extra : Nat),
      shapePatternAt (fun extra term => atomAt (width + extra) term)
          (fun slot => atomAt width (filling slot)) extra context =
        atomAt (width + extra) (context.fill filling) := by
  intro context
  induction context with
  | hole slot =>
      intro extra
      exact (atomAt_of_wellScoped (within slot) extra).symm
  | srt sort => intro extra; rfl
  | con name => intro extra; rfl
  | var index => intro extra; rfl
  | app function argument ihFunction ihArgument =>
      intro extra
      simp only [shapePatternAt, TermContext.fill, atomAt, ihFunction extra, ihArgument extra]
  | lam domain body ihDomain ihBody =>
      intro extra
      have inner := ihBody (extra + 1)
      simp only [shapePatternAt, TermContext.fill, atomAt, ihDomain extra, inner]
      rfl
  | pi domain body ihDomain ihBody =>
      intro extra
      have inner := ihBody (extra + 1)
      simp only [shapePatternAt, TermContext.fill, atomAt, ihDomain extra, inner]
      rfl

/-- **Negative**: a leaf that is no hole does not read the fillings.  The
image of the context that is a constant returns its leaf, whatever fills the
holes. -/
theorem shapePatternAt_constant {slots : Type} (leaf : Nat → LF.Term → Pattern)
    (first second : slots → Pattern) (extra : Nat) (name : String) :
    shapePatternAt leaf first extra (.con name) = shapePatternAt leaf second extra (.con name) :=
  rfl

#print axioms placedHoleOf
#print axioms applicationContextOf
#print axioms shapeContextAt
#print axioms act_shapeContextAt
#print axioms shapePatternAt_atoms

end Mettapedia.Logic.HostingStyles.AmbientSpace
