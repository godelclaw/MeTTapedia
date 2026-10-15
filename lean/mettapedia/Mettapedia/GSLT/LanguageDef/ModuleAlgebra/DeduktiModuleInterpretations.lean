import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.ClosedTermGluing
import Mettapedia.GSLT.Dedukti.CousineauDowekMorphism
import Mettapedia.GSLT.Dedukti.TwoRoutes
import Mettapedia.GSLT.Dedukti.ConfluenceApplied

/-!
# Joining the Cousineau-Dowek and Holide constant interpretations

The universe/code fragment and the product/HOL fragment have different
constant inventories and share their universe and decoding parameters.
Their closed-term assignments glue through the module algebra. The result
recovers the existing Cousineau-Dowek back interpretation on all terms and
acts identically on the Holide declarations and rewrite template.

The preservation results use the actual existing Dedukti theories. They
give a conversion-preserving map out of every Cousineau-Dowek theory, and a
typing-preserving map on the formalized Holide fragment. The latter is not
a translation from the native OpenTheory kernel. The inventories do not
encode the complete source types or rules, and this construction does not
assert that arbitrary theory joins are conservative or confluent.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleAlgebra.DeduktiModuleInterpretations

open Mettapedia.GSLT
open Mettapedia.GSLT.Dedukti
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (Decl sigT lookupType lookupBody Ctx)
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile)
open ClosedTermGluing

abbrev P := Presentation String String Unit

def namedEntry (name : String) : Entry String String Unit := ⟨name, name, ()⟩

def nameEmbedding : String ↪ Entry String String Unit where
  toFun := namedEntry
  inj' := fun _ _ same => congrArg Entry.origin same

def inventory (names : Finset String) : P :=
  ⟨names.map nameEmbedding, by
    intro first firstMember second secondMember overlap
    obtain ⟨firstName, _, rfl⟩ := Finset.mem_map.mp firstMember
    obtain ⟨secondName, _, rfl⟩ := Finset.mem_map.mp secondMember
    rcases overlap with same | same
    all_goals exact congrArg namedEntry same⟩

def namedMember {names : Finset String} (name : String) (member : name ∈ names) :
    Member (inventory names) :=
  ⟨namedEntry name, Finset.mem_map.mpr ⟨name, member, rfl⟩⟩

theorem inventory_join (left right : Finset String) :
    join (inventory left) (inventory right) = some (inventory (left ∪ right)) := by
  apply join_eq_some_iff.mpr
  exact (Finset.map_union _ _).symm

def sharedNames : Finset String := {"Utype", "Ukind", "etype", "ekind"}
def codeNames : Finset String := {"dottype", "dotkind"}
def productNames : Finset String :=
  {"dotpi_type_type_type", "dotpi_type_type_kind", "dotpi_type_kind_type",
    "dotpi_type_kind_kind", "dotpi_kind_type_type", "dotpi_kind_type_kind",
    "dotpi_kind_kind_type", "dotpi_kind_kind_kind"}
def holNames : Finset String := {"type", "bool", "arr", "term", "eq", "proof", "REFL", "ABS_THM"}

def leftNames : Finset String := sharedNames ∪ codeNames
def rightNames : Finset String := sharedNames ∪ productNames ∪ holNames
def wholeNames : Finset String := leftNames ∪ rightNames

def left : P := inventory leftNames
def right : P := inventory rightNames
def whole : P := inventory wholeNames

theorem joined : join left right = some whole := inventory_join _ _

theorem actual_overlap : leftNames ∩ rightNames = sharedNames := by decide

/-- This branch supplies universe and decoding parameters and sort codes;
it leaves product and foreign constants uninterpreted. -/
def leftValue (name : String) : ClosedTerm :=
  match Symbol.ofName name with
  | some (.univ level) => ⟨.srt level, .srt⟩
  | some (.decode level) => ⟨.lam (.srt level) (.var 0), .lam .srt (.var (by omega))⟩
  | some (.code level) => ⟨.srt level, .srt⟩
  | _ => ⟨.con name, .con⟩

/-- This branch supplies universe and decoding parameters and product
codes; HOL constants retain their native names in the encoding. -/
def rightValue (name : String) : ClosedTerm :=
  match Symbol.ofName name with
  | some (.univ level) => ⟨.srt level, .srt⟩
  | some (.decode level) => ⟨.lam (.srt level) (.var 0), .lam .srt (.var (by omega))⟩
  | some (.prod rule) => ⟨productCombinator rule,
      .lam .srt (.lam (.pi (.var (by omega)) .srt)
        (.pi (.var (by omega)) (.app (.var (by omega)) (.var (by omega)))))⟩
  | _ => ⟨.con name, .con⟩

def leftAssignment : ClosedTermGluing.Assignment left := fun entry => leftValue entry.val.label
def rightAssignment : ClosedTermGluing.Assignment right := fun entry => rightValue entry.val.label

theorem compatible :
    ∀ entry hp hq, leftAssignment ⟨entry, hp⟩ = rightAssignment ⟨entry, hq⟩ := by
  intro entry hp hq
  obtain ⟨name, nameLeft, rfl⟩ := Finset.mem_map.mp hp
  obtain ⟨other, nameRight, same⟩ := Finset.mem_map.mp hq
  have nameSame : other = name := nameEmbedding.injective same
  subst other
  have member : name ∈ sharedNames := actual_overlap ▸ Finset.mem_inter.mpr ⟨nameLeft, nameRight⟩
  simp only [sharedNames, Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with rfl | rfl | rfl | rfl
  all_goals apply Subtype.ext
  all_goals rfl

def combinedAssignment : ClosedTermGluing.Assignment whole :=
  glueDependent joined leftAssignment rightAssignment

noncomputable def combined : Interpretation := interpretation whole combinedAssignment

theorem meaning_left (name : String) (member : name ∈ leftNames) :
    combined.meaning name = (leftValue name).val := by
  exact (glued_meaning_left joined leftAssignment rightAssignment (namedMember name member)).trans
    (interpretation_meaning left leftAssignment (namedMember name member))

theorem meaning_right (name : String) (member : name ∈ rightNames) :
    combined.meaning name = (rightValue name).val := by
  exact (glued_meaning_right joined leftAssignment rightAssignment compatible
    (namedMember name member)).trans
    (interpretation_meaning right rightAssignment (namedMember name member))

private theorem base_member (level : Srt) :
    (Symbol.univ level).name ∈ leftNames ∧ (Symbol.decode level).name ∈ leftNames := by
  cases level <;> decide

private theorem code_member (level : Srt) : (Symbol.code level).name ∈ leftNames := by
  cases level <;> decide

private theorem prod_member (rule : LFProfile.ProductRule) : (Symbol.prod rule).name ∈ rightNames := by
  obtain ⟨domain, codomain, result⟩ := rule
  cases domain <;> cases codomain <;> cases result <;> decide

theorem meaning_symbol (symbol : Symbol) : combined.meaning symbol.name = backMeaning symbol.name := by
  cases symbol with
  | univ level =>
      exact (meaning_left _ (base_member level).1).trans
        (by simp only [leftValue, backMeaning, Symbol.ofName_name])
  | decode level =>
      exact (meaning_left _ (base_member level).2).trans
        (by simp only [leftValue, backMeaning, Symbol.ofName_name])
  | code level =>
      exact (meaning_left _ (code_member level)).trans
        (by simp only [leftValue, backMeaning, Symbol.ofName_name])
  | prod rule =>
      exact (meaning_right _ (prod_member rule)).trans
        (by simp only [rightValue, backMeaning, Symbol.ofName_name])

private theorem ofName_label {name : String} {symbol : Symbol}
    (found : Symbol.ofName name = some symbol) : symbol.name = name := by
  have test : (symbol.name == name) = true :=
    List.find?_some (p := fun s : Symbol => s.name == name) (l := Symbol.all) found
  exact beq_iff_eq.mp test

private theorem left_name_recognized {name : String} (member : name ∈ leftNames) :
    ∃ symbol, Symbol.ofName name = some symbol := by
  simp only [leftNames, sharedNames, codeNames, Finset.mem_union,
    Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with (rfl | rfl | rfl | rfl) | (rfl | rfl)
  all_goals exact ⟨_, rfl⟩

/-- The independent fragment assignments reconstruct the back translation
on the complete lambda-Pi syntax, not only on the listed constants. -/
theorem meaning_eq_back (name : String) : combined.meaning name = back.meaning name := by
  cases found : Symbol.ofName name with
  | some symbol =>
      have same := ofName_label found
      rw [← same]
      exact meaning_symbol symbol
  | none =>
      by_cases member : name ∈ wholeNames
      · have inRight : name ∈ rightNames := by
          rcases Finset.mem_union.mp member with inLeft | inRight
          · obtain ⟨symbol, recognized⟩ := left_name_recognized inLeft
            rw [found] at recognized
            cases recognized
          · exact inRight
        exact (meaning_right name inRight).trans (by simp only [rightValue, back, backMeaning, found])
      · have outside : ¬ ∃ entry : Member whole, entry.val.label = name := by
          rintro ⟨entry, equal⟩
          obtain ⟨other, inWhole, same⟩ := Finset.mem_map.mp entry.property
          have nameSame : other = name := (congrArg Entry.label same).trans equal
          exact member (nameSame ▸ inWhole)
        exact (interpretation_outside whole combinedAssignment name outside).trans
          (by simp only [back, backMeaning, found])

theorem apply_eq_back (term : LF.Term) : combined.apply term = back.apply term := by
  have meanings : combined.meaning = back.meaning := funext meaning_eq_back
  exact congrArg (fun meaning => interpret meaning term) meanings

theorem extends_empty : Theory.empty.Extends TwoRoutes.holTheory where
  constType := fun _ _ impossible => by cases impossible
  body := fun _ _ impossible => by cases impossible
  rule := fun _ impossible => impossible.elim

/-- Every actual universe rule and every one of its instances is preserved
by the reconstructed interpretation into the Holide theory. -/
theorem cd_respects (profile : Profile) : combined.Respects (cdTheory profile) TwoRoutes.holTheory where
  body := fun _ _ impossible => by cases impossible
  rule := fun rule member assignment => by
    rw [apply_eq_back, apply_eq_back]
    exact ((back_respects profile).rule rule member assignment).mono extends_empty

private theorem hol_type_fixed {name : String} {type : LF.Term}
    (declared : TwoRoutes.holTheory.constType name = some type) :
    combined.meaning name = .con name ∧ combined.apply type = type := by
  rcases Phenomena.lookupType_mem declared with member | ⟨_, member⟩
  · simp only [TwoRoutes.holSig, List.mem_cons, Decl.const.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    all_goals exact ⟨(meaning_eq_back _).trans rfl, (apply_eq_back _).trans rfl⟩
  · simp [TwoRoutes.holSig] at member

/-- The Holide template survives the join for arbitrary target assignment
values, including terms outside the HOL constant inventory. -/
theorem hol_respects : combined.Respects TwoRoutes.holTheory TwoRoutes.holTheory where
  body := fun name term defined => by
    have noBody : TwoRoutes.holTheory.body name = none := by
      simp [TwoRoutes.holTheory, Theory.ofSig, TwoRoutes.holSig, lookupBody]
    rw [noBody] at defined
    cases defined
  rule := fun rule member assignment => by
    have same : rule = TwoRoutes.termArrow := List.mem_singleton.mp member
    subst rule
    have left : combined.apply TwoRoutes.termArrow.lhs = TwoRoutes.termArrow.lhs :=
      (apply_eq_back _).trans rfl
    have right : combined.apply TwoRoutes.termArrow.rhs = TwoRoutes.termArrow.rhs :=
      (apply_eq_back _).trans rfl
    rw [combined.apply_instantiate, combined.apply_instantiate, left, right]
    exact Conv.rule (by simp [TwoRoutes.holTheory, Theory.ofSig])
      (fun index => combined.apply (assignment index))

theorem hol_typed (profile : Profile) : combined.Typed profile TwoRoutes.holTheory TwoRoutes.holTheory where
  constType := fun name type declared context => by
    obtain ⟨nameFixed, typeFixed⟩ := hol_type_fixed declared
    rw [nameFixed, typeFixed]
    exact .con declared

noncomputable def cdRoute (profile : Profile) :
    ContextMap (conversionTheory (cdTheory profile)) (conversionTheory TwoRoutes.holTheory) :=
  combined.contextMap (cd_respects profile)

noncomputable def holRoute :
    ContextMap (conversionTheory TwoRoutes.holTheory) (conversionTheory TwoRoutes.holTheory) :=
  combined.contextMap hol_respects

/-- The existing source PTS map composes with the module-built
interpretation. No new hosting or conservativity assertion is inferred. -/
noncomputable def simplyTypedRoute :
    ContextMap (rawTheory simplyTyped) (conversionTheory TwoRoutes.holTheory) :=
  (cdRoute simplyTyped).comp (cdRawMap simplyTyped_respectsErasure)

theorem simplyTypedRoute_erases (term : ValidTerm simplyTyped) :
    Conv TwoRoutes.holTheory (simplyTypedRoute.term (origin := ()) term) term.val.erase := by
  change Conv TwoRoutes.holTheory (combined.apply (Dedukti.translate term.val)) term.val.erase
  rw [apply_eq_back]
  exact (backTranslate_translate term.val).mono extends_empty

/-- Closed images provide substitution laws but cannot replace the
independent obligation to preserve definitions and rewrite rules. -/
theorem closed_identity_does_not_preserve_code_rule :
    ¬ Interpretation.id.Respects (cdTheory simplyTyped) Theory.empty := by
  intro respects
  have converted := respects.rule (codeRule .type .kind) (.code rfl) (fun _ => .srt .type)
  rw [Interpretation.id_apply, Interpretation.id_apply] at converted
  exact not_joinable_of_heads (first := "ekind") (second := "Utype") Theory.empty_headed
    (by simp [Theory.Defines, Theory.empty]) (by simp [Theory.Defines, Theory.empty])
    (by decide) rfl rfl (Unconditional.conv_iff_joinable.mp converted)

end Mettapedia.GSLT.LanguageDef.ModuleAlgebra.DeduktiModuleInterpretations
