import Mettapedia.Logic.WorldModel.Indexed.Doctrine
import Mettapedia.PLN.WorldModel.WorldModelProfiles
import Mettapedia.PLN.WorldModel.PLNWorldModelGeneric

/-!
# The one-world base gives back the fixed-question calculus

Over a base with one world and only its identity, the doctrine has one fibre.
This file proves that this fibre is equivalent to the category whose objects
are the binary world models `BinaryWorldModel State Query` and whose morphisms
are the existing `WorldModelHom`, with `WorldModelHom.id` and
`WorldModelHom.comp` (`fibreAtPoint`).  The existing joint-evidence profile
model is the terminal object of that category (`jointProfile_isTerminal`),
which is the categorical reading of `toJointEvidenceProfile` and
`jointEvidenceProfile_terminal`.

The bridge holds exactly for zero-preserving extraction.  An
`AdditiveWorldModel` need not preserve zero: extraction constantly equal to
the absorbing evidence `(⊤, ⊤)` is additive, yet no additive monoid map
reproduces it (`absorbingModel_not_profileHom`), so such a model is not an
object of the slice.
-/

set_option autoImplicit false

open CategoryTheory Opposite

namespace Mettapedia.Logic.WorldModel.Indexed.FixedQueryBridge

open scoped ENNReal
open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.Evidence
open Mettapedia.PLN.WorldModel
open Mettapedia.PLN.WorldModel.WorldModelProfiles
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric

/-- A binary world model over a fixed question type, with its state type
bundled. -/
structure BinaryModel (Query : Type) where
  /-- The state type. -/
  State : Type
  [evidenceType : EvidenceType State]
  [worldModel : BinaryWorldModel State Query]

attribute [instance] BinaryModel.evidenceType BinaryModel.worldModel

variable {Query : Type}

/-- Morphisms of world models are determined by their state maps. -/
theorem worldModelHom_ext {X Y : BinaryModel Query}
    {f g : WorldModelHom X.State Y.State Query} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Binary world models over `Query` with the existing morphisms. -/
instance : Category (BinaryModel Query) where
  Hom X Y := WorldModelHom X.State Y.State Query
  id X := WorldModelHom.id X.State Query
  comp f g := WorldModelHom.comp g f
  id_comp _ := worldModelHom_ext rfl
  comp_id _ := worldModelHom_ext rfl
  assoc _ _ _ := worldModelHom_ext rfl

/-- Answer profiles for the fixed question type. -/
noncomputable abbrev profiles (Query : Type) : AddCommMonCat := AddCommMonCat.of (Query → BinaryEvidence)

/-- A binary world model as an object of the slice over the profiles: its
evidence extraction bundled as one additive map. -/
noncomputable def toSlice : BinaryModel Query ⥤ Over (profiles Query) where
  obj X := Over.mk (AddCommMonCat.ofHom
    (BinaryWorldModel.evidenceProfileHom (State := X.State) (Query := Query)) :
      AddCommMonCat.of X.State ⟶ profiles Query)
  map {X Y} f := Over.homMk (AddCommMonCat.ofHom f.hom)
    (AddCommMonCat.hom_ext (AddMonoidHom.ext fun W => funext fun q => f.comm W q))

instance : (toSlice (Query := Query)).Faithful where
  map_injective {X Y} f g h := by
    exact worldModelHom_ext (congrArg (fun k => k.left.hom) h)

instance : (toSlice (Query := Query)).Full where
  map_surjective {X Y} φ :=
    ⟨{ hom := φ.left.hom
       comm := fun W q => by
         have := congrArg (fun k : AddCommMonCat.of X.State ⟶ profiles Query => k.hom W q)
           (Over.w φ)
         exact this },
     Over.OverMorphism.ext (AddCommMonCat.hom_ext rfl)⟩

/-- Every object of the slice is the bundle of a binary world model. -/
noncomputable def ofSlice (Y : Over (profiles Query)) : BinaryModel Query :=
  letI : EvidenceType Y.left := {}
  { State := Y.left
    worldModel := BinaryWorldModel.ofProfileHom Y.hom.hom }

instance : (toSlice (Query := Query)).EssSurj where
  mem_essImage Y := ⟨ofSlice Y, ⟨Over.isoMk (Iso.refl _)
    (AddCommMonCat.hom_ext (AddMonoidHom.ext fun _ => rfl))⟩⟩

instance : (toSlice (Query := Query)).IsEquivalence where

/-- Binary world models with `WorldModelHom` form the slice of commutative
monoids over the answer profiles. -/
noncomputable def sliceEquivalence : BinaryModel Query ≌ Over (profiles Query) :=
  (toSlice (Query := Query)).asEquivalence

/-- The base with one world and only its identity. -/
abbrev Point := Discrete PUnit.{1}

/-- The profile functor of the one-world base: one fixed question type and binary
evidence. -/
noncomputable abbrev pointProfiles (Query : Type) : Pointᵒᵖ ⥤ AddCommMonCat :=
  profileFunctor ((Functor.const Point).obj Query)
    ((Functor.const Pointᵒᵖ).obj (AddCommMonCat.of BinaryEvidence))

/-- **The fixed-question calculus is the fibre over the one-world base.** -/
noncomputable def fibreAtPoint :
    BinaryModel Query ≌ (worldOf (pointProfiles Query)).Fiber ⟨PUnit.unit⟩ :=
  sliceEquivalence.trans (fibreEquivalence (pointProfiles Query) ⟨PUnit.unit⟩)

/-- The joint-evidence profile model, bundled. -/
noncomputable def jointProfile (Query : Type) : BinaryModel Query :=
  ⟨JointEvidenceProfile Query⟩

/-- The existing joint-evidence profile model is terminal among binary world
models: `toJointEvidenceProfile` is the unique morphism into it. -/
noncomputable def jointProfile_isTerminal : Limits.IsTerminal (jointProfile Query) :=
  Limits.IsTerminal.ofUniqueHom
    (fun X => (toJointEvidenceProfile (State := X.State) (Query := Query) :
      WorldModelHom X.State (JointEvidenceProfile Query) Query))
    (fun X f => worldModelHom_ext (by
      ext W
      funext q
      exact jointEvidenceProfile_terminal (State := X.State) (Query := Query) f W q))

/-! ## Additive extraction without the zero law is not in the slice -/

/-- The absorbing binary evidence: infinite positive and negative counts. -/
noncomputable def absorbing : BinaryEvidence := ⟨⊤, ⊤⟩

theorem absorbing_add_absorbing : absorbing + absorbing = absorbing := by
  simp [absorbing, BinaryEvidence.hplus_def]

/-- Extraction constantly equal to the absorbing evidence is additive. -/
@[instance_reducible] noncomputable def absorbingModel : AdditiveWorldModel BinaryEvidence Unit BinaryEvidence where
  extract _ _ := absorbing
  extract_add _ _ _ := absorbing_add_absorbing.symm

/-- The absorbing model's extraction is reproduced by no additive monoid map:
it is not an object of the slice over the profiles. -/
theorem absorbingModel_not_profileHom :
    ¬ ∃ F : BinaryEvidence →+ (Unit → BinaryEvidence), ∀ W q,
      F W q = AdditiveWorldModel.extract (State := BinaryEvidence) (Query := Unit)
        (Ev := BinaryEvidence) (self := absorbingModel) W q := by
  rintro ⟨F, hF⟩
  have h0 := hF 0 ()
  rw [map_zero] at h0
  have hpos := congrArg BinaryEvidence.pos h0
  exact ENNReal.zero_ne_top hpos

/-- Positive control: the joint profile model is zero-preserving, its
extraction is an additive monoid map. -/
theorem jointProfile_profileHom :
    ∃ F : (Query → BinaryEvidence) →+ (Query → BinaryEvidence), ∀ W q,
      F W q = BinaryWorldModel.evidence (State := JointEvidenceProfile Query)
        (Query := Query) W q :=
  ⟨AddMonoidHom.id _, fun _ _ => rfl⟩

end Mettapedia.Logic.WorldModel.Indexed.FixedQueryBridge
