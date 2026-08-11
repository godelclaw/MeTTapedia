import Mathlib.Data.Finset.Basic

/-!
# Heterogeneous finite-profile transfer words

A realized source corridor is a composite `M₁ ⋯ Mₙ`; it need not be a
power of one transfer matrix.  This light module records the support semantics
of such a word and the exact deletion principle used by compositional pumping.

The relevance predicate is not supplied by fiat.  A seam state is relevant
precisely when the left and right contexts of the shortened word can actually
use it.  If the removed middle word returns every such state to itself, any
accepting path through the shortened word lifts through the original word.
Contrapositively, rejection of the original word survives deletion.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CorridorTransferWord

universe u

/-- Exact support semantics of a word of possibly different one-step
relations.  The empty word is the identity relation. -/
def ExactTransferWord {Profile : Type u} :
    List (Profile → Profile → Prop) → Profile → Profile → Prop
  | [], start, finish => start = finish
  | step :: rest, start, finish =>
      ∃ middle, step start middle ∧ ExactTransferWord rest middle finish

@[simp]
theorem exactTransferWord_nil_iff
    {Profile : Type u} (start finish : Profile) :
    ExactTransferWord [] start finish ↔ start = finish :=
  Iff.rfl

@[simp]
theorem exactTransferWord_cons_iff
    {Profile : Type u} (step : Profile → Profile → Prop)
    (rest : List (Profile → Profile → Prop)) (start finish : Profile) :
    ExactTransferWord (step :: rest) start finish ↔
      ∃ middle, step start middle ∧ ExactTransferWord rest middle finish :=
  Iff.rfl

/-- Support composition is concatenation of transfer words. -/
theorem exactTransferWord_append_iff
    {Profile : Type u}
    (left right : List (Profile → Profile → Prop))
    (start finish : Profile) :
    ExactTransferWord (left ++ right) start finish ↔
      ∃ middle,
        ExactTransferWord left start middle ∧
          ExactTransferWord right middle finish := by
  induction left generalizing start with
  | nil =>
      constructor
      · intro hpath
        exact ⟨start, rfl, hpath⟩
      · rintro ⟨middle, hstart, hpath⟩
        simpa only [ExactTransferWord] using hstart.symm ▸ hpath
  | cons step rest ih =>
      constructor
      · rintro ⟨next, hstep, hrest⟩
        rcases (ih next).1 hrest with ⟨middle, hleft, hright⟩
        exact ⟨middle, ⟨next, hstep, hleft⟩, hright⟩
      · rintro ⟨middle, ⟨next, hstep, hleft⟩, hright⟩
        exact ⟨next, hstep, (ih next).2 ⟨middle, hleft, hright⟩⟩

/-- Acceptance of a heterogeneous transfer word from a finite initial
support into an arbitrary terminal predicate. -/
def TransferWordAccepts
    {Profile : Type u} (steps : List (Profile → Profile → Prop))
    (initial : Finset Profile) (isAccepting : Profile → Prop) : Prop :=
  ∃ start ∈ initial,
    ∃ finish, ExactTransferWord steps start finish ∧ isAccepting finish

/-- A seam profile is relevant exactly when it lies on an accepting path of
the shortened left/right context. -/
def SeamRelevantToContext
    {Profile : Type u}
    (left right : List (Profile → Profile → Prop))
    (initial : Finset Profile) (isAccepting : Profile → Prop)
    (seam : Profile) : Prop :=
  (∃ start ∈ initial, ExactTransferWord left start seam) ∧
    ∃ finish, ExactTransferWord right seam finish ∧ isAccepting finish

/-- The removed middle word supports the identity on every seam state that
the surrounding accepting context can use. -/
def TransferWordSupportsContextIdentity
    {Profile : Type u}
    (left middle right : List (Profile → Profile → Prop))
    (initial : Finset Profile) (isAccepting : Profile → Prop) : Prop :=
  ∀ seam,
    SeamRelevantToContext left right initial isAccepting seam →
      ExactTransferWord middle seam seam

/-- Insert a context-supported identity word into an accepted shortened
word.  This is the forward implication whose contrapositive powers reductive
descent. -/
theorem transferWordAccepts_insert_of_contextIdentity
    {Profile : Type u}
    (left middle right : List (Profile → Profile → Prop))
    (initial : Finset Profile) (isAccepting : Profile → Prop)
    (hmiddle : TransferWordSupportsContextIdentity
      left middle right initial isAccepting)
    (hshort : TransferWordAccepts (left ++ right) initial isAccepting) :
    TransferWordAccepts (left ++ middle ++ right) initial isAccepting := by
  rcases hshort with ⟨start, hstart, finish, hpath, haccepting⟩
  rcases (exactTransferWord_append_iff left right start finish).1 hpath with
    ⟨seam, hleft, hright⟩
  have hrelevant : SeamRelevantToContext
      left right initial isAccepting seam :=
    ⟨⟨start, hstart, hleft⟩, ⟨finish, hright, haccepting⟩⟩
  have hloop : ExactTransferWord middle seam seam :=
    hmiddle seam hrelevant
  refine ⟨start, hstart, finish, ?_, haccepting⟩
  apply (exactTransferWord_append_iff (left ++ middle) right start finish).2
  refine ⟨seam, ?_, hright⟩
  exact (exactTransferWord_append_iff left middle start seam).2
    ⟨seam, hleft, hloop⟩

/-- Source-facing rejection polarity: if the original composite is rejected,
then deleting a middle word that acts as identity on every context-relevant
seam state leaves a rejected shorter composite. -/
theorem not_transferWordAccepts_erase_of_contextIdentity
    {Profile : Type u}
    (left middle right : List (Profile → Profile → Prop))
    (initial : Finset Profile) (isAccepting : Profile → Prop)
    (hmiddle : TransferWordSupportsContextIdentity
      left middle right initial isAccepting)
    (hfull : ¬ TransferWordAccepts
      (left ++ middle ++ right) initial isAccepting) :
    ¬ TransferWordAccepts (left ++ right) initial isAccepting := by
  intro hshort
  exact hfull (transferWordAccepts_insert_of_contextIdentity
    left middle right initial isAccepting hmiddle hshort)

end GoertzelV24CorridorTransferWord

end Mettapedia.GraphTheory.FourColor
