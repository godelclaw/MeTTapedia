import Mathlib.Logic.Function.Basic
import Mathlib.Logic.IsEmpty.Basic

/-!
# Expressive power: eliminable constructs and abstraction-preserving translations

Felleisen (*On the expressive power of programming languages*, 1991) compares a
language with a conservative extension of it.  The new constructs are
*eliminable* when some translation into the smaller language is the identity on
it, is homomorphic in its constructs, and preserves the observation of every
program (Definition 3.3); they are *macro-eliminable* when each new construct
is moreover translated by a fixed syntactic abstraction (Definition 3.11).
Mitchell (*On abstraction and the expressive power of programming languages*,
1993) compares languages by compositional translations that preserve
observational equivalence ("abstraction-preserving reductions").

A language is given here by its phrases, the contexts that complete a phrase to
a program, and an observation of programs.  This module proves:

* an elimination carries equivalent phrases of the extension to equivalent
  phrases of the base (`Elimination.equiv_map`);
* a compositional, observation-preserving translation reflects equivalence
  (adequacy, `Reduction.equiv_of_map_equiv`; Schmidt-Schauß, Niehren,
  Schwinghammer and Sabel, 2008, Proposition 3.3);
* a macro elimination is therefore fully abstract (`MacroElimination.equiv_iff`)
  and is an abstraction-preserving reduction in Mitchell's sense
  (`MacroElimination.toReduction`, `MacroElimination.abstractionPreserving`);
* Felleisen's Theorem 3.14(i): a macro elimination exists only if the
  extension leaves the equivalence of the base unchanged
  (`MacroElimination.embed_equiv_iff`, `isEmpty_macroElimination_of_split`);
* **reflection trivialises both notions**: when some context of the base reads
  back the phrase in its hole, contextual equivalence of the extension is
  equality (`equiv_eq_of_quotes`; Wand, *The theory of fexprs is trivial*,
  1998, for the λ-calculus with fexprs), and no proper extension has any
  elimination at all (`isEmpty_elimination_of_quotes`).

The last point is why every separation proved for MeTTa-family calculi states
its observer: a quotation observer separates everything, including pure
syntactic sugar.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Expressiveness

universe u u' w

/-- A programming language seen through its program contexts: phrases,
contexts that complete a phrase to a program, and an observation of programs
(for Felleisen, whether the program terminates). -/
structure Language (O : Type w) where
  Phrase : Type u
  Context : Type u
  plug : Context → Phrase → Phrase
  observe : Phrase → O

variable {O : Type w}

namespace Language

/-- Operational equivalence: no context tells the two phrases apart
(Felleisen, Definition 3.5). -/
def Equiv (L : Language.{u} O) (first second : L.Phrase) : Prop :=
  ∀ context : L.Context, L.observe (L.plug context first) = L.observe (L.plug context second)

variable {L : Language.{u} O}

theorem Equiv.refl (phrase : L.Phrase) : L.Equiv phrase phrase :=
  fun _ => rfl

theorem Equiv.symm {first second : L.Phrase} (equivalent : L.Equiv first second) :
    L.Equiv second first :=
  fun context => (equivalent context).symm

theorem Equiv.trans {first second third : L.Phrase} (left : L.Equiv first second)
    (right : L.Equiv second third) : L.Equiv first third :=
  fun context => (left context).trans (right context)

end Language

open Language

/-- `L₁` conservatively extends `L₀` (Felleisen, Definition 3.2): phrases and
contexts embed, filling commutes with the embedding, and a program of `L₀` is
observed in `L₁` as in `L₀`. -/
structure Extension (L₀ : Language.{u} O) (L₁ : Language.{u'} O) where
  embed : L₀.Phrase → L₁.Phrase
  embedContext : L₀.Context → L₁.Context
  plug_embed : ∀ (context : L₀.Context) (phrase : L₀.Phrase),
    L₁.plug (embedContext context) (embed phrase) = embed (L₀.plug context phrase)
  observe_embed : ∀ phrase : L₀.Phrase, L₁.observe (embed phrase) = L₀.observe phrase

variable {L₀ : Language.{u} O} {L₁ : Language.{u'} O}

/-- An **elimination** of the new constructs (Felleisen, Definition 3.3): a
translation into `L₀` (condition E1) that is the identity on `L₀` and is
homomorphic in the constructs of `L₀`, hence commutes with filling a context
of `L₀` (E2), and that preserves the observation of every program (E3).  The
translation of a phrase built from new constructs is otherwise arbitrary. -/
structure Elimination (X : Extension L₀ L₁) where
  map : L₁.Phrase → L₀.Phrase
  map_embed : ∀ phrase : L₀.Phrase, map (X.embed phrase) = phrase
  map_plug_embed : ∀ (context : L₀.Context) (phrase : L₁.Phrase),
    map (L₁.plug (X.embedContext context) phrase) = L₀.plug context (map phrase)
  observe_map : ∀ phrase : L₁.Phrase, L₀.observe (map phrase) = L₁.observe phrase

/-- A **macro elimination** (Felleisen, Definition 3.11): each new construct is
translated by a fixed syntactic abstraction.  The proofs use the consequence
that Felleisen's Translation Lemma derives from this: every context of `L₁`
has a translated context of `L₀`, and the translation of a filled context is
the translated context filled with the translated phrase. -/
structure MacroElimination (X : Extension L₀ L₁) extends Elimination X where
  mapContext : L₁.Context → L₀.Context
  map_plug : ∀ (context : L₁.Context) (phrase : L₁.Phrase),
    map (L₁.plug context phrase) = L₀.plug (mapContext context) (map phrase)

/-- A **reduction** of `L₁` to `L₀`: a compositional translation that preserves
the observation of programs. -/
structure Reduction (L₁ : Language.{u'} O) (L₀ : Language.{u} O) where
  map : L₁.Phrase → L₀.Phrase
  mapContext : L₁.Context → L₀.Context
  map_plug : ∀ (context : L₁.Context) (phrase : L₁.Phrase),
    map (L₁.plug context phrase) = L₀.plug (mapContext context) (map phrase)
  observe_map : ∀ phrase : L₁.Phrase, L₀.observe (map phrase) = L₁.observe phrase

/-- Mitchell's **abstraction-preserving** reductions: equivalent phrases are
carried to equivalent phrases.  Together with adequacy
(`Reduction.equiv_of_map_equiv`) this is full abstraction. -/
def Reduction.AbstractionPreserving (R : Reduction L₁ L₀) : Prop :=
  ∀ first second : L₁.Phrase, L₁.Equiv first second → L₀.Equiv (R.map first) (R.map second)

section Elimination

variable {X : Extension L₀ L₁}

/-- What an `L₀` context observes of a translated phrase is what its embedding
observes of the phrase in `L₁`. -/
theorem Elimination.observe_plug_map (Φ : Elimination X) (context : L₀.Context)
    (phrase : L₁.Phrase) :
    L₀.observe (L₀.plug context (Φ.map phrase)) =
      L₁.observe (L₁.plug (X.embedContext context) phrase) := by
  rw [← Φ.map_plug_embed, Φ.observe_map]

/-- **An elimination preserves equivalence**: phrases that no context of the
extension tells apart are translated to phrases that no context of the base
tells apart.  Abstraction present in `L₁` must survive in `L₀`. -/
theorem Elimination.equiv_map (Φ : Elimination X) {first second : L₁.Phrase}
    (equivalent : L₁.Equiv first second) : L₀.Equiv (Φ.map first) (Φ.map second) := by
  intro context
  rw [Φ.observe_plug_map, Φ.observe_plug_map]
  exact equivalent (X.embedContext context)

end Elimination

section Reduction

/-- **Adequacy**: a compositional, observation-preserving translation reflects
equivalence. -/
theorem Reduction.equiv_of_map_equiv (R : Reduction L₁ L₀) {first second : L₁.Phrase}
    (equivalent : L₀.Equiv (R.map first) (R.map second)) : L₁.Equiv first second := by
  intro context
  rw [← R.observe_map, ← R.observe_map, R.map_plug, R.map_plug]
  exact equivalent (R.mapContext context)

end Reduction

section Macro

variable {X : Extension L₀ L₁}

/-- The reduction underlying a macro elimination. -/
def MacroElimination.toReduction (Φ : MacroElimination X) : Reduction L₁ L₀ where
  map := Φ.map
  mapContext := Φ.mapContext
  map_plug := Φ.map_plug
  observe_map := Φ.observe_map

/-- **A macro elimination is fully abstract.** -/
theorem MacroElimination.equiv_iff (Φ : MacroElimination X) (first second : L₁.Phrase) :
    L₁.Equiv first second ↔ L₀.Equiv (Φ.map first) (Φ.map second) :=
  ⟨Φ.toElimination.equiv_map, Φ.toReduction.equiv_of_map_equiv⟩

/-- **A macro elimination is an abstraction-preserving reduction** in Mitchell's
sense: for conservative extensions, Felleisen's macro-expressibility is a
special case of Mitchell's notion. -/
theorem MacroElimination.abstractionPreserving (Φ : MacroElimination X) :
    Φ.toReduction.AbstractionPreserving :=
  fun _ _ equivalent => Φ.toElimination.equiv_map equivalent

/-- **Felleisen, Theorem 3.14(i).** If the new constructs are macro-eliminable,
the extension neither breaks nor creates an equivalence between phrases of the
base. -/
theorem MacroElimination.embed_equiv_iff (Φ : MacroElimination X) (first second : L₀.Phrase) :
    L₁.Equiv (X.embed first) (X.embed second) ↔ L₀.Equiv first second := by
  rw [Φ.equiv_iff, Φ.map_embed, Φ.map_embed]

/-- Felleisen's method for non-expressibility: an extension that separates two
phrases the base cannot separate has no macro elimination. -/
theorem isEmpty_macroElimination_of_split {first second : L₀.Phrase}
    (equivalent : L₀.Equiv first second)
    (separated : ¬ L₁.Equiv (X.embed first) (X.embed second)) :
    IsEmpty (MacroElimination X) :=
  ⟨fun Φ => separated ((Φ.embed_equiv_iff first second).mpr equivalent)⟩

/-- Dually, an extension that identifies two phrases the base separates has no
macro elimination. -/
theorem isEmpty_macroElimination_of_merge {first second : L₀.Phrase}
    (separated : ¬ L₀.Equiv first second)
    (equivalent : L₁.Equiv (X.embed first) (X.embed second)) :
    IsEmpty (MacroElimination X) :=
  ⟨fun Φ => separated ((Φ.embed_equiv_iff first second).mp equivalent)⟩

end Macro

section Reflection

variable (X : Extension L₀ L₁)

/-- A context of `L₀` **quotes** its hole when observing the filled context in
`L₁` determines the phrase in the hole. -/
def Quotes (quotation : L₀.Context) : Prop :=
  Function.Injective fun phrase : L₁.Phrase => L₁.observe (L₁.plug (X.embedContext quotation) phrase)

variable {X}

/-- **Reflection trivialises equivalence**: in the presence of a quotation,
equivalent phrases of the extension are equal. -/
theorem equiv_eq_of_quotes {quotation : L₀.Context} (quotes : Quotes X quotation)
    {first second : L₁.Phrase} (equivalent : L₁.Equiv first second) : first = second :=
  quotes (equivalent (X.embedContext quotation))

/-- **Reflection rules out every elimination.**  If some context of the base
quotes its hole, then no extension that adds a phrase outside the base has an
elimination, not even one that is not a macro.  Felleisen's Theorem 3.8 is the
method; the quotation is the distinguishing context for every translation at
once. -/
theorem isEmpty_elimination_of_quotes {quotation : L₀.Context} (quotes : Quotes X quotation)
    (proper : ∃ phrase : L₁.Phrase, ∀ base : L₀.Phrase, X.embed base ≠ phrase) :
    IsEmpty (Elimination X) := by
  refine ⟨fun Φ => ?_⟩
  obtain ⟨phrase, outside⟩ := proper
  refine outside (Φ.map phrase) (quotes ?_).symm
  show L₁.observe (L₁.plug (X.embedContext quotation) phrase) =
    L₁.observe (L₁.plug (X.embedContext quotation) (X.embed (Φ.map phrase)))
  rw [X.plug_embed, X.observe_embed, ← Φ.observe_plug_map]

end Reflection

end Mettapedia.GSLT.Expressiveness
