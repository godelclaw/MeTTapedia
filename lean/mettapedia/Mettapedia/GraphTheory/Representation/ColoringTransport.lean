import Mettapedia.GraphTheory.Representation.RepresentationGSLT
import Mettapedia.GSLT.Core.RelationalRouteSemantics
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Colouring witnesses transported through graph representations

Every admitted representation conversion preserves the independently denoted
simple graph. The transport below retains the actual vertex-colour function,
including every prescribed boundary value, and is invertible. Consequently it
preserves boundary support and finite colouring counts.

The relational route interpretation also lifts every chosen representation
path from any existing colouring. This totality concerns changes of layout of
the same simple graph. It supplies neither an initial colouring nor a theorem
about arbitrary graph-construction steps. Rotation order, multigraph edge
occurrences and Tait colourings require additional representation contracts.
-/

namespace Mettapedia.GraphTheory.Representation.ColoringTransport

open RepresentationGSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.RelationalRouteSemantics

universe u v w

/-- Change the graph proof, retaining each vertex's actual assigned colour. -/
def colouringEquiv {V : Type u} {Palette : Type v} {first second : SimpleGraph V}
    (same : first = second) : first.Coloring Palette ≃ second.Coloring Palette where
  toFun colouring := .mk colouring fun adjacent => colouring.valid (same.symm ▸ adjacent)
  invFun colouring := .mk colouring fun adjacent => colouring.valid (same ▸ adjacent)
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl

@[simp] theorem colouringEquiv_apply {V : Type u} {Palette : Type v}
    {first second : SimpleGraph V} (same : first = second)
    (colouring : first.Coloring Palette) (vertex : V) :
    colouringEquiv same colouring vertex = colouring vertex := rfl

/-- Prescribed colours at named vertices. Ports need not be distinct. -/
def BoundaryColouring {V : Type u} {Palette : Type v} {Port : Type w}
    (graph : SimpleGraph V) (ports : Port → V) (word : Port → Palette) :=
  {colouring : graph.Coloring Palette // ∀ port, colouring (ports port) = word port}

/-- The full boundary fibre is preserved, including multiplicities of
distinct colouring functions. -/
def boundaryEquiv {V : Type u} {Palette : Type v} {Port : Type w}
    {first second : SimpleGraph V} (same : first = second)
    (ports : Port → V) (word : Port → Palette) :
    BoundaryColouring first ports word ≃ BoundaryColouring second ports word where
  toFun colouring := ⟨colouringEquiv same colouring.val, colouring.property⟩
  invFun colouring := ⟨colouringEquiv same.symm colouring.val, colouring.property⟩
  left_inv _ := by apply Subtype.ext; ext; rfl
  right_inv _ := by apply Subtype.ext; ext; rfl

variable {n : Nat} {Palette : Type} {Port : Type w}

def pathColouringEquiv {source target : State n}
    (path : (theory n).RewritePath source target) :
    source.denote.Coloring Palette ≃ target.denote.Coloring Palette :=
  colouringEquiv (path_commutes path)

def pathBoundaryEquiv {source target : State n}
    (path : (theory n).RewritePath source target)
    (ports : Port → Fin n) (word : Port → Palette) :
    BoundaryColouring source.denote ports word ≃
      BoundaryColouring target.denote ports word :=
  boundaryEquiv (path_commutes path) ports word

/-- Every total layout conversion transports the actual prescribed-boundary
colourings, without choosing a new assignment. -/
def convertBoundaryEquiv (source : State n) (target : Layout)
    (ports : Port → Fin n) (word : Port → Palette) :
    BoundaryColouring source.denote ports word ≃
      BoundaryColouring (materialize target (canonicalMatrix source)).denote ports word :=
  pathBoundaryEquiv (convertPath source target) ports word

theorem path_boundary_support_iff {source target : State n}
    (path : (theory n).RewritePath source target)
    (ports : Port → Fin n) (word : Port → Palette) :
    Nonempty (BoundaryColouring source.denote ports word) ↔
      Nonempty (BoundaryColouring target.denote ports word) :=
  (pathBoundaryEquiv path ports word).nonempty_congr

/-- For finite palettes these are the exact numbers of boundary-compatible
colourings. `Nat.card` also gives the same value on both sides in general. -/
theorem path_boundary_card_eq {source target : State n}
    (path : (theory n).RewritePath source target)
    (ports : Port → Fin n) (word : Port → Palette) :
    Nat.card (BoundaryColouring source.denote ports word) =
      Nat.card (BoundaryColouring target.denote ports word) :=
  Nat.card_congr (pathBoundaryEquiv path ports word)

theorem convert_colorable_iff (source : State n) (target : Layout) (colours : Nat) :
    source.denote.Colorable colours ↔
      (materialize target (canonicalMatrix source)).denote.Colorable colours :=
  (pathColouringEquiv (Palette := Fin colours) (convertPath source target)).nonempty_congr

/-- Concatenated conversions act as the composite of their colouring maps. -/
theorem append_colour_transport {first middle last : State n}
    (earlier : (theory n).RewritePath first middle)
    (later : (theory n).RewritePath middle last) (colouring : first.denote.Coloring Palette) :
    pathColouringEquiv (appendPath earlier later) colouring =
      pathColouringEquiv later (pathColouringEquiv earlier colouring) := by
  ext
  rfl

/-- Different conversion histories preserve the same assignment. -/
theorem path_independent {source target : State n}
    (first second : (theory n).RewritePath source target)
    (colouring : source.denote.Coloring Palette) :
    pathColouringEquiv first colouring = pathColouringEquiv second colouring := by
  ext
  rfl

abbrev Event (source target : State n) := PLift (Step source target)

def interpretation (Palette : Type) (n : Nat) : Semantics (@Event n) where
  State representation := representation.denote.Coloring Palette
  step _ first second := PLift (∀ vertex, second vertex = first vertex)

/-- Retain the itinerary of a representation conversion in the generic route
language used for graph constructions and constraint-bearing executions. -/
def route : {source target : State n} →
    (theory n).RewritePath source target → Route (@Event n) source target
  | _, _, .nil state => .refl state
  | _, _, .cons step rest => .cons ⟨step⟩ (route rest)

/-- Every colouring lifts along each chosen representation route. The input
colouring is an explicit premise, and all intermediate colourings are data. -/
def liftPath : {source target : State n} →
    (path : (theory n).RewritePath source target) →
    (colouring : source.denote.Coloring Palette) →
    Σ result : target.denote.Coloring Palette,
      (interpretation Palette n).Witness (route path) colouring result
  | _, _, .nil _, colouring => ⟨colouring, ⟨⟨rfl⟩⟩⟩
  | _, _, .cons step rest, colouring =>
      let middle := colouringEquiv (step_commutes step) colouring
      let tail := liftPath rest middle
      ⟨tail.1, ⟨middle, ⟨fun _ => rfl⟩, tail.2⟩⟩

/-- The constructed terminal witness keeps every original colour. -/
theorem liftPath_preserves_colour : {source target : State n} →
    (path : (theory n).RewritePath source target) →
    (colouring : source.denote.Coloring Palette) →
    (vertex : Fin n) → (liftPath path colouring).1 vertex = colouring vertex
  | _, _, .nil _, _, _ => rfl
  | _, _, .cons step rest, colouring, vertex =>
      liftPath_preserves_colour rest (colouringEquiv (step_commutes step) colouring) vertex

end Mettapedia.GraphTheory.Representation.ColoringTransport
