import Mettapedia.OSLF.Syntax.ScopedBindingEquationEventPresheaf
import Mettapedia.TypeTheory.DisplayedPresheafEvidenceUniversal

/-!+# Native dependent possibilities of permitted binding events

The independently constructed event presheaf supplies the actual source and
target maps. Pullback of a target family checks its dependent postcondition;
the dependent sum along the source map retains the complete event and the
supplied target certificate. Its action transports both under substitution.
The existing universal sum contract applies to these earned endpoint maps.

This construction is for small authored rule indices in the common small
presheaf category. It does not erase the firing to transition support or
construct a target certificate from a behavioral approximation.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEquationNativePossibility

open _root_.CategoryTheory ScopedEncoding ScopedEquationEvents
open Mettapedia.TypeTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafEvidenceTransport DisplayedPresheafEvidenceUniversal

variable {S : Signature} {M : List (MetaArity S)} {Index : Type}
  (E : List (EqAxiom S M)) (rules : Index → UnpositionedRewrite (withMetas S M))
  (permission : PositionPermission S) (sort : S.Srt)

def values : (Syntactic.Ctxt S)ᵒᵖ ⥤ Type :=
  ContextualEquationClassEvents.termQPresheaf E sort ⋙ uliftFunctor.{0,0}

/-- The full dependent target family is consulted at every event endpoint. -/
def certified (postcondition : DisplayedFamily (values E sort)) :
    DisplayedFamily (eventPresheaf rules permission sort) :=
  reindexDisplayed (targetNatural rules permission E sort) postcondition

/-- Native existential possibility, with its event and certificate retained. -/
def possibilities (postcondition : DisplayedFamily (values E sort)) :
    DisplayedFamily (values E sort) :=
  transport (sourceNatural rules permission E sort) (certified E rules permission sort postcondition)

variable {E rules permission sort}

def retain (postcondition : DisplayedFamily (values E sort))
    (point : (eventPresheaf rules permission sort).Elements)
    (certificate : (certified E rules permission sort postcondition).obj point) :
    (possibilities E rules permission sort postcondition).obj
      ((sourceNatural rules permission E sort).mapElements.obj point) :=
  (unit (sourceNatural rules permission E sort)
    (certified E rules permission sort postcondition)).app point certificate

variable (postcondition : DisplayedFamily (values E sort))

def receiptEvent {point : (values E sort).Elements}
    (receipt : (possibilities E rules permission sort postcondition).obj point) :
    (eventPresheaf rules permission sort).obj point.1 := receipt.val.1

def receiptTarget {point : (values E sort).Elements}
    (receipt : (possibilities E rules permission sort postcondition).obj point) :
    (values E sort).obj point.1 :=
  (targetNatural rules permission E sort).app point.1 (receiptEvent postcondition receipt)

def receiptCertificate {point : (values E sort).Elements}
    (receipt : (possibilities E rules permission sort postcondition).obj point) :
    postcondition.obj ⟨point.1, receiptTarget postcondition receipt⟩ := receipt.val.2

theorem receipt_source_square {point : (values E sort).Elements}
    (receipt : (possibilities E rules permission sort postcondition).obj point) :
    (sourceNatural rules permission E sort).app point.1 (receiptEvent postcondition receipt) =
      point.2 := receipt.property

theorem retain_event (point : (eventPresheaf rules permission sort).Elements)
    (certificate : (certified E rules permission sort postcondition).obj point) :
    receiptEvent postcondition (retain postcondition point certificate) = point.2 := rfl

theorem retain_certificate (point : (eventPresheaf rules permission sort).Elements)
    (certificate : (certified E rules permission sort postcondition).obj point) :
    receiptCertificate postcondition (retain postcondition point certificate) = certificate := rfl

/-- The complete event map, including its binder path, is the first readout
of native certificate substitution. -/
theorem reindex_event {before after : (values E sort).Elements}
    (change : before ⟶ after)
    (receipt : (possibilities E rules permission sort postcondition).obj before) :
    receiptEvent postcondition
        ((possibilities E rules permission sort postcondition).map change receipt) =
      (receiptEvent postcondition receipt).map after.1.unop.vars change.val.unop := rfl

theorem reindex_target {before after : (values E sort).Elements}
    (change : before ⟶ after)
    (receipt : (possibilities E rules permission sort postcondition).obj before) :
    receiptTarget postcondition
        ((possibilities E rules permission sort postcondition).map change receipt) =
      (values E sort).map change.val (receiptTarget postcondition receipt) :=
  ConcreteCategory.congr_hom
    ((targetNatural rules permission E sort).naturality change.val)
    (receiptEvent postcondition receipt)

/-- The dependent certificate follows its actual arrow of event elements;
the comparison does not discard its potentially varying target index. -/
theorem reindex_certificate {before after : (values E sort).Elements}
    (change : before ⟶ after)
    (receipt : (possibilities E rules permission sort postcondition).obj before) :
    HEq
      (receiptCertificate postcondition
        ((possibilities E rules permission sort postcondition).map change receipt))
      ((certified E rules permission sort postcondition).map
        (CategoryOfElements.homMk
          (⟨before.1, receipt.val.1⟩ : (eventPresheaf rules permission sort).Elements)
          (⟨after.1, (eventPresheaf rules permission sort).map change.val receipt.val.1⟩ :
            (eventPresheaf rules permission sort).Elements)
          change.val rfl) receipt.val.2) := HEq.rfl

theorem inhabited_iff (point : (values E sort).Elements) :
    Nonempty ((possibilities E rules permission sort postcondition).obj point) ↔
      ∃ event : (eventPresheaf rules permission sort).obj point.1,
        (sourceNatural rules permission E sort).app point.1 event = point.2 ∧
          Nonempty (postcondition.obj
            ⟨point.1, (targetNatural rules permission E sort).app point.1 event⟩) := by
  constructor
  · rintro ⟨receipt⟩
    exact ⟨receiptEvent postcondition receipt, receipt_source_square postcondition receipt,
      ⟨receiptCertificate postcondition receipt⟩⟩
  · rintro ⟨event, sourceEq, ⟨certificate⟩⟩
    exact ⟨⟨⟨event, certificate⟩, sourceEq⟩⟩

def specificationEquivalence (specification : DisplayedFamily (values E sort)) :
    ((possibilities E rules permission sort postcondition) ⟶ specification) ≃
      ((certified E rules permission sort postcondition) ⟶
        reindexDisplayed (sourceNatural rules permission E sort) specification) :=
  specificationEquiv (sourceNatural rules permission E sort)
    (certified E rules permission sort postcondition) specification

theorem elimination_computes {specification : DisplayedFamily (values E sort)}
    (body : certified E rules permission sort postcondition ⟶
      reindexDisplayed (sourceNatural rules permission E sort) specification)
    (point : (eventPresheaf rules permission sort).Elements)
    (certificate : (certified E rules permission sort postcondition).obj point) :
    (descend (sourceNatural rules permission E sort) body).app
        ((sourceNatural rules permission E sort).mapElements.obj point)
        (retain postcondition point certificate) = body.app point certificate :=
  descend_unit _ body point certificate

end Mettapedia.OSLF.Binding.ScopedEquationNativePossibility
