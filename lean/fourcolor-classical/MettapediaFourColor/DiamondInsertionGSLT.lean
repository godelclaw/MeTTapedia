import MettapediaFourColor.DiamondInsertion

/-!
# Compatible choices along the two diamond insertions

The first interface retains both alternatives for configuration 2, together
with the possible contracted branch at the second insertion. The first step
assembles configuration 2 when needed; the second produces an actual reference
colouring of configuration 4. Thus every final colouring has a compatible
history. This does not choose a colouring compatible with every exterior.
-/

namespace FourColor.DiamondInsertionGSLT

open DiamondConfigurations DiamondInsertion
open Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision
open Mettapedia.GSLT Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.RelationalRouteSemantics Mettapedia.GSLT.ProofRelevantPresentation
open Mettapedia.GSLT.LooseRelationEquipment

inductive Interface where
  | alternatives
  | firstInserted
  | reference

def State : Interface → Type
  | .alternatives =>
    (graph001.Coloring (Fin 4) ⊕ EqualChoice graph001 0 1 6 (by decide)) ⊕
      EqualChoice graph002 4 5 9 (by decide)
  | .firstInserted =>
    graph002.Coloring (Fin 4) ⊕ EqualChoice graph002 4 5 9 (by decide)
  | .reference => {k : (cfmap cf004).Dart → Color // (cfmap cf004).map.Coloring k}

inductive Event : Interface → Interface → Type where
  | first : Event .alternatives .firstInserted
  | second : Event .firstInserted .reference

def theory : GSLT where
  Term := Interface
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := Nonempty (Event source target)
  rewrites_resp_left := by
    intro source source' target equal step
    subst source'
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    intro source target target' step equal
    subst target'
    exact step

def presentation : StepPresentation theory where
  Evidence := Event
  erases_iff := fun _ _ => Iff.rfl

noncomputable def execute : {a b : Interface} → Event a b → State a ≃ State b
  | _, _, .first => alternatives12.sumCongr (Equiv.refl _)
  | _, _, .second => referenceAlternatives24

noncomputable def semantics : Semantics Event where
  State := State
  step event x y := EqWitness (execute event x) y

def route : Route Event .alternatives .reference :=
  .cons .first (.cons .second (.refl _))

/-- Both intermediate colouring data and their compatibility are retained. -/
noncomputable def witness (x : State .alternatives) :
    semantics.Witness route x (referenceAlternatives14 x) :=
  ⟨execute .first x, ⟨⟨rfl⟩⟩,
    execute .second (execute .first x), ⟨⟨rfl⟩⟩, ⟨⟨rfl⟩⟩⟩

theorem supported_iff (x : State .alternatives) (y : State .reference) :
    semantics.Supports route x y ↔ referenceAlternatives14 x = y := by
  constructor
  · rintro ⟨⟨middle, first, last, second, final⟩⟩
    have hfirst := first.down.down
    have hsecond := second.down.down
    have hfinal := final.down.down
    exact (congrArg (execute .second) hfirst).trans (hsecond.trans hfinal)
  · intro h
    subst y
    exact ⟨witness x⟩

/-- Every actual reference colouring admits a compatible two-step history. -/
theorem every_coloring (y : State .reference) :
    ∃ x, semantics.Supports route x y :=
  ⟨referenceAlternatives14.symm y,
    (supported_iff _ _).mpr (referenceAlternatives14.apply_symm_apply y)⟩

/-- External observations restrict the successful histories exactly. -/
theorem viable_iff (accepts : State .reference → Prop) :
    (∃ x, semantics.Viable route accepts x) ↔ ∃ y, accepts y := by
  constructor
  · rintro ⟨x, y, _, hy⟩
    exact ⟨y, hy⟩
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx⟩ := every_coloring y
    exact ⟨x, y, hx, hy⟩

/-- A concrete starting colouring, checked on the actual configuration graph. -/
def seed : graph001.Coloring (Fin 4) :=
  .mk (ConfigurationTable.lookup "ABABCBCDAD") (by decide +kernel)

set_option maxRecDepth 32768 in
/-- A complete successful history, including its actual reference-map output. -/
noncomputable def constructed :
    Σ y : State .reference, semantics.Witness route (.inl (.inl seed)) y :=
  ⟨referenceAlternatives14 (.inl (.inl seed)), witness (.inl (.inl seed))⟩

end FourColor.DiamondInsertionGSLT
