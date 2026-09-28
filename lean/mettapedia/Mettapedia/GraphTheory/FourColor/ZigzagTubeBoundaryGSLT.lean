import Mettapedia.GSLT.Core.BoundaryCertificateComposition
import Mettapedia.GSLT.Core.ProofRelevantPresentation
import Mettapedia.GraphTheory.FourColor.ZigzagTubeFiniteNormalization

/-!
# Exact boundary elimination for compositional tube families

Events retain literal open tangles, with a separate constructor for the
five-port tube family. Normalization caps each marked tube at four rings.
One finite certificate supplies witness transports for every length; the
generic boundary theorem composes them through arbitrary finite routes.

Nonempty chains realize those routes as literal serially glued tangles.
Their actual colourings are equivalent to the route witnesses. Arbitrary
boundary predicates, including compatibility with an exterior, survive
normalization. This does not assert equality of colouring counts.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagTubeBoundaryGSLT

open Mettapedia.GSLT Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.ProofRelevantPresentation Mettapedia.GSLT.RelationalRouteSemantics
open Mettapedia.GSLT.LooseRelationEquipment
open ZigzagRing OpenTangleWitnessComposition GoertzelV24OpenTangleComposition

noncomputable section

/-- The universe accommodates events that contain their vertex and dart types. -/
abbrev Interface := ULift.{1} Nat

inductive Event : Interface → Interface → Type 1
  | piece {a b : Interface} (tangle : HiddenTangle (Fin a.down) (Fin b.down)) : Event a b
  | fiveTube (lengthIndex : Nat) : Event ⟨5⟩ ⟨5⟩

def theory : GSLT where
  Term := Interface
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun a b => Nonempty (Event a b)
  rewrites_resp_left := by
    intro a a' b equal event
    subst a'
    exact ⟨b, event, rfl⟩
  rewrites_resp_right := by
    intro a b b' event equal
    subst b'
    exact event

def presentation : StepPresentation theory where
  Evidence := Event
  erases_iff := fun _ _ => Iff.rfl

def Event.realize : {a b : Interface} → Event a b → HiddenTangle (Fin a.down) (Fin b.down)
  | _, _, .piece tangle => tangle
  | _, _, .fiveTube n => tube 5 n

def colouring : Semantics Event where
  State width := Fin width.down → Color
  step event := colourRelation event.realize.data

def normalizeEvent : {a b : Interface} → Event a b → Event a b
  | _, _, .piece tangle => .piece tangle
  | _, _, .fiveTube n => .fiveTube (min n 3)

/-- Both directions use actual ring-colouring witnesses. -/
def reduction : colouring.BoundaryReduction where
  normalize := normalizeEvent
  forward event := by
    cases event with
    | piece tangle => exact Cell.id _
    | fiveTube n => exact fiveTubeNormalizeCell n
  backward event := by
    cases event with
    | piece tangle => exact Cell.id _
    | fiveTube n => exact fiveTubeReconstructCell n

theorem route_boundary_iff {a b : Interface} (path : Route Event a b)
    (outside : colouring.State a → colouring.State b → Prop) :
    (∃ x y, colouring.Supports path x y ∧ outside x y) ↔
      (∃ x y, colouring.Supports (reduction.route path) x y ∧ outside x y) :=
  reduction.boundary_predicate_iff path outside

theorem route_context_iff {a b c d : Interface} (initial : Route Event a b)
    (middle : Route Event b c) (final : Route Event c d)
    (x : colouring.State a) (z : colouring.State d) :
    colouring.Supports ((initial.append middle).append final) x z ↔
      colouring.Supports ((initial.append (reduction.route middle)).append final) x z :=
  reduction.in_context_iff initial middle final x z

/-- Nonempty chains have a literal graph realization; an empty route needs
no artificial graph identity with merged boundary ports. -/
inductive Chain : Interface → Interface → Type 1
  | single {a b : Interface} (event : Event a b) : Chain a b
  | cons {a b c : Interface} (event : Event a b) (rest : Chain b c) : Chain a c

def Chain.route : {a b : Interface} → Chain a b → Route Event a b
  | _, b, .single event => .cons event (.refl b)
  | _, _, .cons event rest => .cons event rest.route

def Chain.realize : {a b : Interface} → Chain a b → HiddenTangle (Fin a.down) (Fin b.down)
  | _, _, .single event => event.realize
  | _, _, .cons event rest =>
      ⟨_, _, TwoSidedOpenTangleData.serialCompose event.realize.data rest.realize.data
        (Equiv.refl _)⟩

def Chain.normalize : {a b : Interface} → Chain a b → Chain a b
  | _, _, .single event => .single (normalizeEvent event)
  | _, _, .cons event rest => .cons (normalizeEvent event) rest.normalize

theorem Chain.normalize_route {a b : Interface} (chain : Chain a b) :
    chain.normalize.route = reduction.route chain.route := by
  induction chain with
  | single => rfl
  | cons event rest ih => exact congrArg (Route.cons (normalizeEvent event)) ih

/-- Exact adequacy: routes retain the colouring witnesses of their actual
glued graph, not only the dimensions of their interfaces. -/
def Chain.witnessEquiv {a b : Interface} (chain : Chain a b)
    (x : Fin a.down → Color) (y : Fin b.down → Color) :
    colourRelation chain.realize.data x y ≃ colouring.Witness chain.route x y := by
  induction chain with
  | single event => exact (compIdentityRight (colouring.step event) x y).symm
  | cons event rest ih =>
      exact (serialEquiv event.realize.data rest.realize.data x y).trans
        (Equiv.sigmaCongrRight fun z => Equiv.prodCongr (Equiv.refl _) (ih z y))

theorem Chain.supports_realize_iff {a b : Interface} (chain : Chain a b)
    (x : Fin a.down → Color) (y : Fin b.down → Color) :
    colouring.Supports chain.route x y ↔ chain.realize.Accepts x y :=
  ((chain.witnessEquiv x y).nonempty_congr).symm.trans
    (nonempty_colourRelation_iff _ x y)

/-- A whole class of composites is normalized using the same local
certificate, with every intervening arbitrary piece retained. -/
theorem Chain.normalize_accepts_iff {a b : Interface} (chain : Chain a b)
    (x : Fin a.down → Color) (y : Fin b.down → Color) :
    chain.realize.Accepts x y ↔ chain.normalize.realize.Accepts x y := by
  rw [← chain.supports_realize_iff, ← chain.normalize.supports_realize_iff,
    chain.normalize_route]
  exact reduction.supports_iff chain.route x y

theorem Chain.normalize_boundary_iff {a b : Interface} (chain : Chain a b)
    (outside : (Fin a.down → Color) → (Fin b.down → Color) → Prop) :
    (∃ x y, chain.realize.Accepts x y ∧ outside x y) ↔
      (∃ x y, chain.normalize.realize.Accepts x y ∧ outside x y) := by
  simp only [chain.normalize_accepts_iff]

end
end Mettapedia.GraphTheory.FourColor.ZigzagTubeBoundaryGSLT
