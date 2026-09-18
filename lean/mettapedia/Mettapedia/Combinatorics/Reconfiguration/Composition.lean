import Mettapedia.Combinatorics.Reconfiguration.Completability

/-!
# Composing reconfiguration systems across an interface

Lemma 8.18 of Goertzel's v23 manuscript composes *local Kempe reachability
with fixed input* (LKR_in) across an interface: tangles `X : S → Z` and
`Y : Z → T`, each satisfying LKR_in, give `Y ∘ X` satisfying LKR_in when `Y` is
transparent in the sense of Lemma 8.15.  Its proof is a fibration argument:

* `Total` is the set of colourings of `Y ∘ X`, `Base` the set of colourings of
  `X`, and `proj` is restriction to `X`; the input word on `S` is a label on
  `Base`;
* the fibres of `proj` are connected: two composite colourings with the same
  restriction to `X` differ only inside `Y`, with the interface `Z` fixed, and
  are joined by LKR_in of `Y`;
* every move of `X` must lift to the composite (Step 1 of the proof).

The lifting step is where the manuscript's argument fails.  It prepares the `Y`
side (interface pairing control, Lemmas 8.16 and 8.17) so that the composite
two-colour component through the switched `X`-component meets `X` in exactly
that component.  The kernel-checked finite fact
`GoertzelLemma814.lemma818_pointwise_lift_preparation_obstruction` exhibits, for
two canonical three-cell gadgets glued in series, an input-avoiding upstream
switch for which no downstream extension with the same interface colours has
the pairing the preparation requires.  That refutes a step of the proof, not
the composite statement: LKR_in of the two-gadget composite holds
(`GoertzelLemma818LengthTwoTTRealAudit.ttChainLKRInAudit_ok`).

The module `Reconfiguration.TauTauLifting` sharpens the obstruction: the
upstream colouring produced by that switch has no downstream extension at all,
so step lifting in the form the proof uses — every move of `X` lifts — is
false for the two-gadget composite, whatever preparation is attempted.  The
module `Kempe.TauSeries` checks the same on the line graph of the composite,
with genuine Kempe switches.  A lifting hypothesis can only be asked of moves
whose target extends.

This file therefore states the composition theorem with the lifting
hypothesis explicit and restricted to such moves (`ImageStep`).  From it,
connected far-side fibres, and connectivity of the extendable part of the near
side through such moves, the composite has connected input fibres
(`fibresConnected_of_parts`).  The lifting hypothesis is necessary: it follows
from the conclusion (`liftsImageSteps_of_fibresConnected`).  Nothing here
derives it from transparency, and no such derivation is claimed.
-/

namespace Mettapedia.Combinatorics.Reconfiguration

open Relation

universe u v w

variable {Total : Type u} {Base : Type v}
  (totalStep : Total → Total → Prop) (baseStep : Base → Base → Prop)
  (proj : Total → Base)

/-- Base moves whose target lies over some total state: the moves of the near
side that stay among colourings extending across the interface. -/
def ImageStep (b b' : Base) : Prop :=
  baseStep b b' ∧ ∃ y, proj y = b'

variable {totalStep baseStep proj}

theorem ImageStep.base {b b' : Base} (h : ImageStep baseStep proj b b') :
    baseStep b b' :=
  h.1

/-- Lifting every base move lifts, in particular, every move into the image. -/
theorem LiftsSteps.imageStep (h : LiftsSteps totalStep baseStep proj) :
    LiftsSteps totalStep (ImageStep baseStep proj) proj :=
  h.mono fun _ _ hb => hb.base

/-- Under lifting of every base move, a base path from a projection never
leaves the image, so it is a path of image moves. -/
theorem LiftsSteps.reflTransGen_imageStep (h : LiftsSteps totalStep baseStep proj)
    {x : Total} {b : Base} (hpath : ReflTransGen baseStep (proj x) b) :
    ReflTransGen (ImageStep baseStep proj) (proj x) b := by
  induction hpath with
  | refl => exact ReflTransGen.refl
  | @tail c d hxc hcd ih =>
      exact ih.tail ⟨hcd, h.exists_proj_eq (hxc.tail hcd)⟩

/-- **Composition theorem.**  Suppose

* `hfar`: the fibres of `proj` are connected (the far side is connected with the
  interface fixed);
* `hlift`: every near-side move from a projection to a state that extends
  lifts to a total path (the explicit lifting hypothesis);
* `hnear`: any two extendable near-side states with the same input label are
  joined by near-side moves through extendable states.

Then the total system is connected within each input label class. -/
theorem fibresConnected_of_parts {γ : Type w} (input : Base → γ)
    (hfar : FibresConnected totalStep proj)
    (hlift : LiftsSteps totalStep (ImageStep baseStep proj) proj)
    (hnear : ∀ x y : Total, input (proj x) = input (proj y) →
      ReflTransGen (ImageStep baseStep proj) (proj x) (proj y)) :
    FibresConnected totalStep (input ∘ proj) :=
  fun x y hxy => (Fibration.mk hfar hlift).reach (hnear x y hxy)

/-- **The manuscript's shape.**  If every near-side move lifts, near-side fibre
connectivity is enough, because lifted paths never leave the image. -/
theorem fibresConnected_of_parts_of_liftsSteps {γ : Type w} (input : Base → γ)
    (hfar : FibresConnected totalStep proj)
    (hlift : LiftsSteps totalStep baseStep proj)
    (hnear : FibresConnected baseStep input) :
    FibresConnected totalStep (input ∘ proj) :=
  fibresConnected_of_parts input hfar hlift.imageStep fun x y hxy =>
    hlift.reflTransGen_imageStep (hnear (proj x) (proj y) hxy)

/-- **The lifting hypothesis is necessary.**  If near-side moves preserve the
input label and the composite is connected within each input class, every
near-side move into the image lifts. -/
theorem liftsImageSteps_of_fibresConnected {γ : Type w} (input : Base → γ)
    (hinput : ∀ b b', baseStep b b' → input b = input b')
    (h : FibresConnected totalStep (input ∘ proj)) :
    LiftsSteps totalStep (ImageStep baseStep proj) proj := by
  rintro x b ⟨hstep, y, rfl⟩
  exact ⟨y, rfl, h x y (hinput _ _ hstep)⟩

/-- Given connected far-side fibres, near-side moves that preserve the input
label, and an extendable near side connected through image moves, the composite
has connected input fibres exactly when the lifting hypothesis holds. -/
theorem fibresConnected_iff_of_parts {γ : Type w} (input : Base → γ)
    (hinput : ∀ b b', baseStep b b' → input b = input b')
    (hfar : FibresConnected totalStep proj)
    (hnear : ∀ x y : Total, input (proj x) = input (proj y) →
      ReflTransGen (ImageStep baseStep proj) (proj x) (proj y)) :
    FibresConnected totalStep (input ∘ proj) ↔
      LiftsSteps totalStep (ImageStep baseStep proj) proj :=
  ⟨liftsImageSteps_of_fibresConnected input hinput,
    fun hlift => fibresConnected_of_parts input hfar hlift hnear⟩

/-- **Completability composes** under the same explicit lifting hypothesis: the
near side reaches a base target through extendable states, and the fibre over
a base target completes on the far side. -/
theorem completable_of_parts {targetUp : Set Total} {targetDown : Set Base}
    (hlift : LiftsSteps totalStep (ImageStep baseStep proj) proj)
    (hnear : ∀ x, ∃ b ∈ targetDown, ReflTransGen (ImageStep baseStep proj) (proj x) b)
    (hfar : ∀ x, proj x ∈ targetDown → ∃ y ∈ targetUp, ReflTransGen totalStep x y) :
    Completable totalStep targetUp :=
  hlift.completable hnear hfar

end Mettapedia.Combinatorics.Reconfiguration
