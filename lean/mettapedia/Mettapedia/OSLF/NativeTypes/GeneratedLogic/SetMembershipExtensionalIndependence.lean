import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipKripkeSets

/-!
# Excluded middle and weak excluded middle do not follow from the laws of sets, with extensionality

With equality that grows along the stages (`SetMembershipKripkeSets`), the laws of the empty set, the power set,
separation, union, replacement and induction along membership hold together with extensionality and the
indiscernibility of equal sets (`extensionalLaws_hold`), over any listing of stages. Two listings separate the two
principles:

- **Two stages** (`chain`), now and later: "only later" is neither true now nor false later, so **excluded middle
  fails now** (`chain_middle_fails`) and has no proof from these laws (`middle_not_derivable`). Extensionality is no
  help: here `{∅ only later}` and `{∅ from now on}` are equal later, as they should be.
- **A fork** (`fork`), a root below two stages with no common later stage: "true at the left stage" is neither
  refuted at the root nor refuted-refuted, so **weak excluded middle fails at the root** (`fork_weakMiddle_fails`) and
  has no proof from these laws (`weakMiddle_not_derivable`).

So, over these laws:

- the every-split "every split of `1` has a first part that is empty or not empty", weak excluded middle's split, is
  true and has no proof (`emptyOrNonEmpty_not_derivable`), and neither has "… empty or has a member", excluded middle's
  (`emptyOrInhabited_not_derivable_extensional`);
- no hypotheses among them prove every true regional native type (`not_regionalComplete_extensional`).

With a crisp equality the fork is impossible: in a Kripke model whose equality is identity, the three laws force any
two later stages to meet (`KripkeLaws.directed_of_laws`), so weak excluded middle holds wherever they do. The fork
model escapes by letting distinct sets become equal at the later stages: the parts of `P(∅)` are five sets at the
root and only two at each later stage; `{∅ at the left stage}` and `{∅ everywhere}` are two sets at the root and one at
the left stage (`fork_identifies_later`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings.KripkeSets

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.ZFSetHenkinInterpretation (Symbol)

/-! ## Two stages -/

/-- **Two stages**, now (`false`) and later (`true`), with three truth values: never, only later, from now on. -/
def chain : Stages where
  World := Bool
  le now later := now = false ∨ later = true
  le_refl w := by cases w <;> simp
  le_trans := by
    intro u v w first second
    cases u <;> cases v <;> cases w <;> simp_all
  count := 3
  one_lt_count := by decide
  level d w := 2 ≤ d ∨ (1 ≤ d ∧ w = true)
  level_mono := by
    intro d v w later held
    rcases held with two | ⟨one, rfl⟩
    · exact .inl two
    · rcases later with impossible | rfl
      · exact absurd impossible (by decide)
      · exact .inr ⟨one, rfl⟩
  level_zero w := by simp
  level_pos d positive _ := ⟨true, .inr ⟨positive, rfl⟩⟩
  level_onto P up := by
    by_cases now : P false
    · refine ⟨2, by decide, fun w => iff_of_true (.inl le_rfl) (up (show false = false ∨ w = true from .inl rfl) now)⟩
    · by_cases later : P true
      · refine ⟨1, by decide, fun w => ?_⟩
        cases w <;> simp [now, later]
      · refine ⟨0, by decide, fun w => ?_⟩
        cases w <;> simp [now, later]

/-- "Only later". -/
def onlyLater : (frame chain).Val .prop := fun w : Bool => w = true

theorem onlyLater_adm : (frame chain).Adm .prop onlyLater := by
  intro v w later held
  rcases later with rfl | rfl
  · exact absurd held Bool.false_ne_true
  · rfl

/-- **Excluded middle fails now**: "only later" is not true now, and it is not false later. -/
theorem chain_middle_fails : ¬ (model chain).denote middleLaw (model chain).emptyVal false := by
  intro middle
  have admissible : (model chain).ValuationAdm false ((model chain).extend (model chain).emptyVal onlyLater) :=
    (model chain).toKripkePreModel.extend_adm (σ := .prop) (d := onlyLater) ((model chain).emptyVal_adm false)
      onlyLater_adm
  rcases ((model chain).denote_disjunctionFormula _ _ admissible).mp
      (middle false (chain.le_refl false) onlyLater onlyLater_adm) with now | never
  · exact Bool.false_ne_true now
  · exact ((model chain).denote_negation _ admissible).mp never true (.inl rfl) rfl

/-- **Excluded middle is not derivable** from the laws of sets with extensionality and indiscernibility. -/
theorem middle_not_derivable {Δ : List (ClosedFormula Symbol)} (among : ∀ δ ∈ Δ, δ ∈ extensionalLaws)
    (proof : Proof Δ middleLaw) : False :=
  chain_middle_fails (sound chain proof false fun δ listed => extensionalLaws_hold chain false δ (among δ listed))

/-! ## A fork -/

/-- **A fork**: a root (`none`) below two stages with no common later stage, with five truth values: never, at the
left stage, at the right stage, at both, everywhere. -/
def fork : Stages where
  World := Option Bool
  le u v := u = none ∨ u = v
  le_refl w := .inr rfl
  le_trans := by
    rintro u v w (rfl | rfl) second
    · exact .inl rfl
    · exact second
  count := 5
  one_lt_count := by decide
  level d w := 4 ≤ d ∨ (d = 1 ∧ w = some false) ∨ (d = 2 ∧ w = some true) ∨ (d = 3 ∧ w ≠ none)
  level_mono := by
    rintro d v w (rfl | rfl) held
    · rcases held with all | ⟨-, impossible⟩ | ⟨-, impossible⟩ | ⟨-, impossible⟩
      · exact .inl all
      · cases impossible
      · cases impossible
      · exact absurd rfl impossible
    · exact held
  level_zero w := by simp
  level_pos d positive small := by
    rcases (by omega : d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4) with rfl | rfl | rfl | rfl
    · exact ⟨some false, .inr (.inl ⟨rfl, rfl⟩)⟩
    · exact ⟨some true, .inr (.inr (.inl ⟨rfl, rfl⟩))⟩
    · exact ⟨some false, .inr (.inr (.inr ⟨rfl, by simp⟩))⟩
    · exact ⟨none, .inl le_rfl⟩
  level_onto P up := by
    by_cases root : P none
    · exact ⟨4, by decide, fun w => iff_of_true (.inl le_rfl) (up (.inl rfl) root)⟩
    · by_cases left : P (some false) <;> by_cases right : P (some true)
      · refine ⟨3, by decide, fun w => ?_⟩
        rcases w with _ | _ | _ <;> simp [root, left, right]
      · refine ⟨1, by decide, fun w => ?_⟩
        rcases w with _ | _ | _ <;> simp [root, left, right]
      · refine ⟨2, by decide, fun w => ?_⟩
        rcases w with _ | _ | _ <;> simp [root, left, right]
      · refine ⟨0, by decide, fun w => ?_⟩
        rcases w with _ | _ | _ <;> simp [root, left, right]

/-- **The two later stages of the fork have no common later stage.** -/
theorem fork_apart : ¬ ∃ w, fork.le (some false) w ∧ fork.le (some true) w := by
  rintro ⟨w, left | rfl, right | right⟩ <;> simp_all

/-- In the fork, `1` lists the empty set at the left stage only and `4` everywhere. -/
theorem fork_lit_one {w : Option Bool} {z : ℕ} : fork.lit w z 1 ↔ z = 0 ∧ w = some false := by
  constructor
  · intro listed
    have small := Stages.lt_of_lit listed
    obtain rfl : z = 0 := by omega
    rcases listed with impossible | ⟨-, left⟩ | ⟨impossible, -⟩ | ⟨impossible, -⟩ <;>
      first | exact absurd impossible (by decide) | exact ⟨rfl, left⟩
  · rintro ⟨rfl, rfl⟩
    exact .inr (.inl ⟨by decide, rfl⟩)

theorem fork_lit_four {w : Option Bool} {z : ℕ} : fork.lit w z 4 ↔ z = 0 := by
  constructor
  · intro listed
    by_contra nonzero
    have positive : 0 < z := Nat.pos_of_ne_zero nonzero
    have large : 5 ≤ 5 ^ z := by
      calc 5 = 5 ^ 1 := (pow_one 5).symm
        _ ≤ 5 ^ z := Nat.pow_le_pow_right (by decide) positive
    have zero : digit 5 4 z = 0 := by
      unfold digit
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le (by decide : 4 < 5) large), Nat.zero_mod]
    exact fork.level_zero w (zero ▸ listed)
  · rintro rfl
    exact .inl (by decide)

/-- **Two parts of `P(∅)` that the later stages identify**: `{∅ at the left stage}` and `{∅ everywhere}` are two sets
at the root and one set at the left stage. -/
theorem fork_identifies_later : ¬ fork.same 1 4 none ∧ fork.same 1 4 (some false) := by
  constructor
  · intro related
    obtain ⟨z', listed, -⟩ := (Stages.same_iff_members.mp related none (fork.le_refl none) 0).mpr
      (Stages.mem_of_lit (fork_lit_four.mpr rfl))
    exact absurd (fork_lit_one.mp listed).2 (by simp)
  · refine Stages.same_iff_members.mpr fun v later z => ?_
    obtain rfl : v = some false := by rcases later with impossible | rfl; cases impossible; rfl
    constructor
    · rintro ⟨z', listed, related⟩
      obtain ⟨rfl, -⟩ := fork_lit_one.mp listed
      exact ⟨0, fork_lit_four.mpr rfl, related⟩
    · rintro ⟨z', listed, related⟩
      obtain rfl := fork_lit_four.mp listed
      exact ⟨0, fork_lit_one.mpr ⟨rfl, rfl⟩, related⟩

/-- "At the left stage". -/
def atLeft : (frame fork).Val .prop := fun w : Option Bool => w = some false

theorem atLeft_adm : (frame fork).Adm .prop atLeft := by
  rintro v w (rfl | rfl) held
  · exact absurd held (by simp [atLeft])
  · exact held

/-- **Weak excluded middle fails at the root**: "at the left stage" is not refuted at the root, since it holds at the
left stage, and its refutation is not refuted, since it holds at the right stage. -/
theorem fork_weakMiddle_fails : ¬ (model fork).denote weakMiddleLaw (model fork).emptyVal none := by
  intro weakMiddle
  have admissible : (model fork).ValuationAdm none ((model fork).extend (model fork).emptyVal atLeft) :=
    (model fork).toKripkePreModel.extend_adm (σ := .prop) (d := atLeft) ((model fork).emptyVal_adm none) atLeft_adm
  rcases ((model fork).denote_disjunctionFormula _ _ admissible).mp
      (weakMiddle none (fork.le_refl none) atLeft atLeft_adm) with refuted | doublyRefuted
  · exact ((model fork).denote_negation _ admissible).mp refuted (some false) (.inl rfl) rfl
  · refine ((model fork).denote_negation _ admissible).mp doublyRefuted (some true) (.inl rfl) ?_
    refine ((model fork).denote_negation _ ((model fork).toKripkePreModel.valuationAdm_mono
      (show fork.le none (some true) from .inl rfl) admissible)).mpr fun v later held => ?_
    rcases later with impossible | rfl
    · cases impossible
    · exact absurd (show some true = some false from held) (by simp)

/-- **Weak excluded middle is not derivable** from the laws of sets with extensionality and indiscernibility. -/
theorem weakMiddle_not_derivable {Δ : List (ClosedFormula Symbol)} (among : ∀ δ ∈ Δ, δ ∈ extensionalLaws)
    (proof : Proof Δ weakMiddleLaw) : False :=
  fork_weakMiddle_fails (sound fork proof none fun δ listed => extensionalLaws_hold fork none δ (among δ listed))

/-! ## True every-splits without proofs -/

/-- The three laws, among these laws. -/
def lawsOfExtensionalLaws : HasLaws extensionalLaws where
  empty := Proof.cast (atContext_nil _).symm (.hyp ⟨0, by decide⟩)
  power := Proof.cast (atContext_nil _).symm (.hyp ⟨1, by decide⟩)
  separation := Proof.cast (atContext_nil _).symm (.hyp ⟨2, by decide⟩)

/-- **Weak excluded middle's every-split has no proof**: every split of `1` has a first part that is empty or not
empty, and no hypotheses among these laws prove it. -/
theorem emptyOrNonEmpty_not_derivable {Δ : List (ClosedFormula Symbol)} (among : ∀ δ ∈ Δ, δ ∈ extensionalLaws)
    (proof : Proof Δ (nativeTypeSentence emptyOrNonEmpty one)) : False := by
  have holds := sound fork proof none fun δ listed => extensionalLaws_hold fork none δ (among δ listed)
  have gives := sound fork (weakMiddleOfEmptyOrNonEmpty lawsOfExtensionalLaws one_isHF (value := zero)
    (List.mem_singleton.mpr rfl)) none (extensionalLaws_hold fork none)
  exact fork_weakMiddle_fails (gives none (fork.le_refl none) holds)

/-- **Excluded middle's every-split has no proof** either, even with extensionality. -/
theorem emptyOrInhabited_not_derivable_extensional {Δ : List (ClosedFormula Symbol)}
    (among : ∀ δ ∈ Δ, δ ∈ extensionalLaws) (proof : Proof Δ (nativeTypeSentence emptyOrInhabited one)) : False := by
  have holds := sound chain proof false fun δ listed => extensionalLaws_hold chain false δ (among δ listed)
  have gives := sound chain (middleOfEmptyOrInhabited lawsOfExtensionalLaws one_isHF (value := zero)
    (List.mem_singleton.mpr rfl)) false (extensionalLaws_hold chain false)
  exact chain_middle_fails (gives false (chain.le_refl false) holds)

/-- **These laws are not complete for the regional fragment**, extensionality included. -/
theorem not_regionalComplete_extensional :
    ¬ ∀ formula : Formula 0, formula.regional = true → ∀ term : Pattern, IsHF term →
      Membership.sat Env.closed formula term → Nonempty (Proof extensionalLaws (nativeTypeSentence formula term)) := by
  intro complete
  obtain ⟨middle⟩ := (regionalComplete_iff_middle lawsOfExtensionalLaws).mp complete
  exact middle_not_derivable (fun _ => id) middle

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings.KripkeSets
