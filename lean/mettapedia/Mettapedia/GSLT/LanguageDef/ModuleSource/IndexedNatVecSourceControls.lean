import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecSource
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestDeclarationControls

/-!
# Authored Nat/Vec source controls

The actual text is read by the existing Lean reader. Structural admission agrees
with the independent indexed-polynomial vector example, and therefore reaches
its generated, prefix-checked guest declarations. Runtime reader agreement is
checked separately against the grammar-driven CeTTa parse.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecSourceControls

open Commands IndexedNatVecSource IndexedInductiveNatVec InductiveSyntax

#module_file "../../../../../../metta/gslt/module/IndexedNatVec.module"
#module_roundtrip IndexedNatVec

def names : Names := {}

def natural : Family := ⟨"Nat", [], [], .name "Type",
  [⟨"Zero", [], .name "Nat"⟩, ⟨"Succ", [⟨"previous", .name "Nat"⟩], .name "Nat"⟩]⟩

def vec (length payload tail : String) : Family :=
  ⟨"Vec", [⟨"A", .name "Type"⟩], [⟨"length", .name "Nat"⟩], .name "Type",
    [⟨"Nil", [], .app (.app (.name "Vec") (.name "A")) (.name "Zero")⟩,
     ⟨"Cons", [⟨length, .name "Nat"⟩, ⟨payload, .name "A"⟩,
        ⟨tail, .app (.app (.name "Vec") (.name "A")) (.name length)⟩],
       .app (.app (.name "Vec") (.name "A")) (.app (.name "Succ") (.name length))⟩]⟩

theorem text_selected : select IndexedNatVec.module = some (natural, vec "n" "a" "xs") := rfl

theorem text_lowered : lower names natural (vec "n" "a" "xs") =
    some (IndexedNatVecNames.vectorSource "n" "a" "xs") := rfl

theorem text_natural_admitted : admitNatural names natural = some Natural.admitted := rfl

/-- The parsed source joins the previously independent polynomial construction. -/
theorem text_admitted (A : Type) : admitModule A names IndexedNatVec.module =
    some (Vectors.admitted A) := rfl

theorem alpha_renamed_admitted (A : Type) : admit A names natural (vec "length" "element" "tail") =
    some (Vectors.admitted A) := rfl

theorem shadowed_payload_rejected (A : Type) :
    admit A names natural (vec "n" "n" "xs") = none := rfl

theorem shadowed_recursive_rejected (A : Type) :
    admit A names natural (vec "n" "a" "n") = none := rfl

theorem shadowed_global_rejected (A : Type) :
    admit A names natural (vec "Zero" "a" "xs") = none := rfl

/-- The admitted text reaches the existing formed guest signature. This
conclusion supplies declaration formation, not judgmental iota authority. -/
theorem text_guest_formed (A : Type) (admitted : IndexedInductive.Admitted (Vectors.interface A) [])
    (accepted : admitModule A names IndexedNatVec.module = some admitted) :
    (Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration.Signature.ofList
      (Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.declarations.take 4 ++
        IndexedInductive.Guest.Declarations.entries (IndexedInductive.Guest.TypedControls.indexSyntax A)
          (IndexedInductive.Guest.DeclarationControls.vectorParameters A)
          IndexedInductive.Guest.DeclarationControls.vectorNames admitted)).Formed
      Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Tower.rules := by
  rw [text_admitted] at accepted
  cases Option.some.inj accepted
  exact IndexedInductive.Guest.DeclarationControls.vector_library_formed A

def negativeField : Family := { vec "n" "a" "xs" with constructors :=
  [⟨"Bad", [⟨"f", .arrow (.app (.app (.name "Vec") (.name "A")) (.name "Zero"))
      (.name "A")⟩], .app (.app (.name "Vec") (.name "A")) (.name "Zero")⟩] }

def verdicts : List (String × Bool) := [
  ("executable frontend accepts the authored vector", check names IndexedNatVec.module),
  ("source selects the declared theory", (select IndexedNatVec.module).isSome),
  ("source natural algebra is checked", naturalMatches names natural),
  ("source indexed header is checked", vectorMatches names (vec "n" "a" "xs")),
  ("negative recursive function field is rejected", (lower names natural negativeField).isNone),
  ("shadowing a global operation is rejected", (lower names natural (vec "Zero" "a" "xs")).isNone),
  ("different payload parameter is rejected", (lower names natural
    { vec "n" "a" "xs" with «parameters» := [⟨"B", .name "Type"⟩] }).isNone),
  ("changed natural result is rejected", !(naturalMatches names
    { natural with constructors := [⟨"Zero", [], .name "Vec"⟩,
      ⟨"Succ", [⟨"previous", .name "Nat"⟩], .name "Nat"⟩] })),
  ("ambiguous role names are rejected", (lower { names with vector := "Nat" } natural (vec "n" "a" "xs")).isNone),
  ("wrong entry is rejected", (select { IndexedNatVec.module with entry := some (["Other"], []) }).isNone),
  ("unresolved import is not ignored", (select { IndexedNatVec.module with imports := [⟨"Other.module", "other"⟩] }).isNone),
  ("extra source blocks are not ignored", (select { IndexedNatVec.module with theories :=
    [⟨"Data", [], .extend none [.inductives [natural, vec "n" "a" "xs"], .types ["Extra"]]⟩] }).isNone),
  ("ordinary LanguageDef projection cannot erase inductives", match IndexedNatVec.language with
    | .error .requiresIndexedAdmission => true
    | _ => false)]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

#eval verdicts
#print axioms text_guest_formed

end Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecSourceControls
