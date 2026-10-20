import Mettapedia.TypeTheory.NaturalAlgebra
import Mettapedia.TypeTheory.MaterialSets.Hypersets.NaturalOrdinalModel
import Mettapedia.SetTheory.Surreal.IntegerArithmetic

/-!
# Universal recursion for material and surreal natural numbers

The material algebra uses the actual empty hyperset and von Neumann successor
`insert x x`. The surreal algebra uses actual surreal zero and Conway addition
of one, restricted to the image of the natural sign expansions. Their existing
representation theorems establish initiality. The comparison maps below are
then obtained from initiality, with compatibility with those representations
proved afterwards.

The chosen inverses are noncomputable. Operational evaluation should run on an
executable representation and use these isomorphisms for semantic transport;
the results do not assert that arbitrary hypersets or surreals can be decoded.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NaturalRepresentations

open NaturalAlgebra
open MaterialSets.Hypersets

open Mettapedia.SetTheory.SignExpansion

universe u v

abbrev MaterialNatural := {value : HSet.{u} // value ∈ NaturalOrdinalModel.naturals}

def materialAlgebra : Algebra MaterialNatural.{u} where
  zero := ⟨∅, NaturalOrdinalModel.zero_member_naturals⟩
  succ := fun value => ⟨insert value.val value.val,
    NaturalOrdinalModel.successor_member_naturals value.property⟩

def materialRepresentation : Representation materialAlgebra.{u} where
  encode := NaturalOrdinalModel.naturalMembers
  bijective := ⟨NaturalOrdinalModel.naturalMembers_injective, NaturalOrdinalModel.naturalMembers_surjective⟩
  map_zero := Subtype.ext NaturalOrdinalModel.ordinal_zero
  map_succ := fun count => Subtype.ext (NaturalOrdinalModel.ordinal_successor count)

theorem material_initial : IsInitial.{u + 1, v} materialAlgebra.{u} :=
  materialRepresentation.initial

noncomputable def natMaterialIso : Iso natAlgebra materialAlgebra.{u} :=
  materialRepresentation.canonicalIso

theorem natMaterialIso_encode (count : Nat) :
    natMaterialIso.toEquiv count = (NaturalOrdinalModel.naturalMembers count : MaterialNatural.{u}) :=
  materialRepresentation.canonicalIso_encode count

theorem natMaterialIso_val (count : Nat) :
    (natMaterialIso.toEquiv count).val = (NaturalOrdinalModel.ordinal count : HSet.{u}) :=
  congrArg Subtype.val (natMaterialIso_encode count)

abbrev SurrealNatural :=
  {value : Mettapedia.SetTheory.SignExpansion.Surreal // ∃ count : Nat, Surreal.ofNat count = value}

noncomputable def surrealAlgebra : Algebra SurrealNatural where
  zero := ⟨0, ⟨0, Surreal.ofNat_zero⟩⟩
  succ := fun value => ⟨Surreal.add value.val (Surreal.ofNat 1), by
    obtain ⟨count, same⟩ := value.property
    exact ⟨count + 1, (Surreal.add_ofNat_one count).symm.trans
      (congrArg (fun x => Surreal.add x (Surreal.ofNat 1)) same)⟩⟩

noncomputable def surrealEncode (count : Nat) : SurrealNatural :=
  ⟨Surreal.ofNat count, ⟨count, rfl⟩⟩

theorem surrealEncode_injective : Function.Injective surrealEncode :=
  fun _ _ same => Surreal.ofNat_injective (congrArg Subtype.val same)

theorem surrealEncode_surjective : Function.Surjective surrealEncode := by
  intro value
  obtain ⟨count, same⟩ := value.property
  exact ⟨count, Subtype.ext same⟩

noncomputable def surrealRepresentation : Representation surrealAlgebra where
  encode := surrealEncode
  bijective := ⟨surrealEncode_injective, surrealEncode_surjective⟩
  map_zero := Subtype.ext Surreal.ofNat_zero
  map_succ := fun count => Subtype.ext (Surreal.add_ofNat_one count).symm

theorem surreal_initial : IsInitial.{1, v} surrealAlgebra :=
  surrealRepresentation.initial

noncomputable def natSurrealIso : Iso natAlgebra surrealAlgebra :=
  surrealRepresentation.canonicalIso

theorem natSurrealIso_encode (count : Nat) :
    natSurrealIso.toEquiv count = surrealEncode count :=
  surrealRepresentation.canonicalIso_encode count

theorem natSurrealIso_val (count : Nat) :
    (natSurrealIso.toEquiv count).val = Surreal.ofNat count :=
  congrArg Subtype.val (natSurrealIso_encode count)

/-- The comparison uses the two universal properties directly. -/
noncomputable def materialSurrealIso : Iso materialAlgebra.{u} surrealAlgebra :=
  isoOfInitial material_initial surreal_initial material_initial surreal_initial

theorem materialSurrealIso_encode (count : Nat) :
    materialSurrealIso.toEquiv (NaturalOrdinalModel.naturalMembers count : MaterialNatural.{u}) =
      surrealEncode count := by
  have same : Hom.comp materialSurrealIso.toHom materialRepresentation.encodeHom =
      surrealRepresentation.encodeHom :=
    (initialHom_unique nat_initial surrealAlgebra _).trans
      (initialHom_unique nat_initial surrealAlgebra _).symm
  exact congrArg (fun f : Hom natAlgebra surrealAlgebra => f count) same

/-- The triangle comparing all three representations commutes by uniqueness. -/
theorem comparison_triangle :
    natMaterialIso.trans materialSurrealIso = natSurrealIso := by
  apply Iso.ext
  intro count
  change materialSurrealIso.toEquiv (natMaterialIso.toEquiv count) = _
  rw [natMaterialIso_encode, materialSurrealIso_encode, natSurrealIso_encode]

theorem material_successor_is_insert (value : MaterialNatural.{u}) :
    (materialAlgebra.succ value).val = insert value.val value.val := rfl

theorem surreal_successor_is_add_one (value : SurrealNatural) :
    (surrealAlgebra.succ value).val = Surreal.add value.val (Surreal.ofNat 1) := rfl

namespace Controls

theorem material_zero_ne_successor_zero :
    materialAlgebra.{u}.zero ≠ materialAlgebra.succ materialAlgebra.zero := by
  intro same
  have distinct := NaturalOrdinalModel.Controls.zero_one_distinguished.{u}
  apply distinct
  calc
    NaturalOrdinalModel.ordinal 0 = (materialAlgebra.zero : MaterialNatural.{u}).val :=
      NaturalOrdinalModel.ordinal_zero
    _ = (materialAlgebra.succ materialAlgebra.zero).val := congrArg Subtype.val same
    _ = NaturalOrdinalModel.ordinal 1 := by
      rw [NaturalOrdinalModel.ordinal_successor, NaturalOrdinalModel.ordinal_zero]
      rfl

theorem surreal_zero_ne_successor_zero :
    surrealAlgebra.zero ≠ surrealAlgebra.succ surrealAlgebra.zero := by
  intro same
  have mapped := congrArg natSurrealIso.toEquiv.symm same
  have zero : natSurrealIso.toEquiv.symm surrealAlgebra.zero = 0 :=
    natSurrealIso.symm.map_zero
  have successor : natSurrealIso.toEquiv.symm
      (surrealAlgebra.succ surrealAlgebra.zero) =
        Nat.succ (natSurrealIso.toEquiv.symm surrealAlgebra.zero) :=
    natSurrealIso.symm.map_succ surrealAlgebra.zero
  rw [zero, successor, zero] at mapped
  exact Nat.zero_ne_one mapped

theorem material_two_maps_to_surreal_two :
    (materialSurrealIso.toEquiv (NaturalOrdinalModel.naturalMembers 2 : MaterialNatural.{u})).val =
      Surreal.ofNat 2 :=
  congrArg Subtype.val (materialSurrealIso_encode 2)

/-- The initial surreal algebra is the natural image, not all surreals. -/
theorem surreal_omega_outside_natural_image :
    ¬ ∃ count : Nat, Surreal.ofNat count = Surreal.omega := by
  rintro ⟨count, same⟩
  exact (ne_of_lt (Surreal.ofNat_lt_omega count)) same

/-- The material algebra likewise does not include arbitrary hypersets. -/
theorem quine_outside_material_naturals :
    HSet.quineAtom.{u} ∉ NaturalOrdinalModel.naturals :=
  NaturalOrdinalModel.Controls.quine_not_natural

end Controls

end Mettapedia.TypeTheory.NaturalRepresentations
