import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetDriver

/-!
# Controls: the set driver

The membership language read on its hereditary terms, asked through the set driver (`askHereditary`) and evaluated by
the kernel. Each answer is a theorem about the hereditary reading (`HFNative`), by `askHereditary_sound`.

| formula | set | answer |
|---|---|---|
| some set contains it (`◆⊤`) | `0` | yes |
| some empty set contains it (`◆ empty`) | `0` | no |
| `1` contains it (`◆ is 1`) | `0` | yes |
| every set containing it is nonempty (`■ nonempty`) | `0` | yes |
| at least two members | `2` | yes |
| at least two members | `{0, 0}` | no |
| some set is empty (`∃ Set. empty`) | `2` | yes |
| some set satisfies `⊥` | `2` | no |
| every set satisfies `⊤` | `2` | yes |
| an endless chain of containers (`νX. ◆X`) | `0` | yes |
| a well-founded chain of containers (`μX. ◆X`) | `0` | no |
| some member contains it again (`◇ is 0` at `1`, forward) | `1` | yes, as the reference structure says |

Steps back and quantifiers over sets search the representatives of their body (`evalPractical`). These questions were
out of reach of the stage search, whose candidates are all sets below a rank (a tower of twos), and each now takes
under a second:

| formula | set | answer | stage candidates | representative candidates |
|---|---|---|---|---|
| `3` contains it (`◆ is 3`) | `2` | yes | `|V₂₅₇|` | `2⁵` |
| some set is empty and nonempty | `0` | no | `|V₈|` | `2` |
| every set is empty or nonempty | `0` | yes | `|V₈|` | `2` |
| some set has a member with a member (`∃ Set. ◇◇⊤`) | `0` | yes | `|V₈|` | `3` |
| every set has only empty members (`∀ Set. □□⊥`) | `0` | no | `|V₈|` | `3` |
| some set containing it has a member containing `1` (`◆◇◇ is 1`) | `1` | yes | `|V₁₇|` | `2⁶` |

It refuses what no decision covers: counting containers (`≥2` steps back), and a term that is not a hereditary set.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings.SetDriverControls

open Mettapedia.OSLF.MeTTaIL.Syntax

def doubled : Pattern := set [zero, zero]

theorem one_hf : IsHF one := (hereditary_iff _).mp (by decide)

theorem zero_contained : askHereditary (.sometimeBefore .any .top) zero = some true := by decide +kernel

theorem zero_not_in_empty : askHereditary (.sometimeBefore .any (.empty .hashSet)) zero = some false := by
  decide +kernel

theorem zero_in_one : askHereditary (.sometimeBefore .any (.is one)) zero = some true := by decide +kernel

theorem zero_containers_nonempty : askHereditary (.alwaysBefore .any (.nonEmpty .hashSet)) zero = some true := by
  decide +kernel

theorem two_two_members : askHereditary (.atLeast 2 .forward .any .top) two = some true := by decide +kernel

theorem doubled_one_member : askHereditary (.atLeast 2 .forward .any .top) doubled = some false := by
  decide +kernel

theorem some_empty : askHereditary (.someOf (.base "Set") (.empty .hashSet)) two = some true := by decide +kernel

theorem none_bottom : askHereditary (.someOf (.base "Set") .bot) two = some false := by decide +kernel

theorem every_top : askHereditary (.everyOf (.base "Set") .top) two = some true := by decide +kernel

theorem endless_containers : askHereditary (.nu (.sometimeBefore .any (.var 0))) zero = some true := by decide +kernel

theorem no_least_containers : askHereditary (.mu (.sometimeBefore .any (.var 0))) zero = some false := by
  decide +kernel

theorem one_contains_zero : askHereditary (.possibly .any (.is zero)) one = some true := by decide +kernel

theorem two_in_three : askHereditary (.sometimeBefore .any (.is three)) two = some true := by decide +kernel

theorem none_empty_and_nonempty :
    askHereditary (.someOf (.base "Set") (.and (.empty .hashSet) (.nonEmpty .hashSet))) zero = some false := by
  decide +kernel

theorem every_empty_or_nonempty :
    askHereditary (.everyOf (.base "Set") (.or (.empty .hashSet) (.nonEmpty .hashSet))) zero = some true := by
  decide +kernel

theorem some_two_deep :
    askHereditary (.someOf (.base "Set") (.possibly .any (.possibly .any .top))) zero = some true := by
  decide +kernel

theorem not_every_flat :
    askHereditary (.everyOf (.base "Set") (.necessarily .any (.necessarily .any .bot))) zero = some false := by
  decide +kernel

theorem one_deep_in_container :
    askHereditary (.sometimeBefore .any (.possibly .any (.possibly .any (.is one)))) one = some true := by
  decide +kernel

/-- **Counting containers is refused**: no decision covers it. -/
theorem counting_containers_refused : askHereditary (.atLeast 2 .backward .any .top) two = none := by decide +kernel

/-- **A term that is not a hereditary set is refused.** -/
theorem atom_refused : askHereditary (.possibly .any .top) (.apply "Foo" []) = none := by decide +kernel

/-- **The answers hold in the hereditary reading**: `0` lies in some set and in `1`, in no empty set, every container
of `0` is nonempty; `{0, 0}` has one member; there is an empty set and no set satisfies `⊥`; `0` starts an endless
chain of containers and no well-founded one. -/
theorem verdicts :
    HFNative.sat Env.closed (.sometimeBefore .any .top) ⟨zero, zero_hf⟩ ∧
      ¬ HFNative.sat Env.closed (.sometimeBefore .any (.empty .hashSet)) ⟨zero, zero_hf⟩ ∧
      HFNative.sat Env.closed (.sometimeBefore .any (.is one)) ⟨zero, zero_hf⟩ ∧
      HFNative.sat Env.closed (.atLeast 2 .forward .any .top) ⟨two, two_hf⟩ ∧
      HFNative.sat Env.closed (.someOf (.base "Set") (.empty .hashSet)) ⟨two, two_hf⟩ ∧
      ¬ HFNative.sat Env.closed (.someOf (.base "Set") .bot) ⟨two, two_hf⟩ ∧
      HFNative.sat Env.closed (.nu (.sometimeBefore .any (.var 0))) ⟨zero, zero_hf⟩ ∧
      ¬ HFNative.sat Env.closed (.mu (.sometimeBefore .any (.var 0))) ⟨zero, zero_hf⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨_, exact⟩ := askHereditary_sound zero_contained
    exact exact.mp rfl
  · obtain ⟨_, exact⟩ := askHereditary_sound zero_not_in_empty
    exact fun holds => Bool.false_ne_true (exact.mpr holds)
  · obtain ⟨_, exact⟩ := askHereditary_sound zero_in_one
    exact exact.mp rfl
  · obtain ⟨_, exact⟩ := askHereditary_sound two_two_members
    exact exact.mp rfl
  · obtain ⟨_, exact⟩ := askHereditary_sound some_empty
    exact exact.mp rfl
  · obtain ⟨_, exact⟩ := askHereditary_sound none_bottom
    exact fun holds => Bool.false_ne_true (exact.mpr holds)
  · obtain ⟨_, exact⟩ := askHereditary_sound endless_containers
    exact exact.mp rfl
  · obtain ⟨_, exact⟩ := askHereditary_sound no_least_containers
    exact fun holds => Bool.false_ne_true (exact.mpr holds)

/-- **The answers of the representative search hold in the hereditary reading**: `2` lies in `3`; no set is both empty
and nonempty, every set is one or the other; some set has a member with a member, and not every set has only empty
members; some container of `1` has a member containing `1`. -/
theorem representative_verdicts :
    HFNative.sat Env.closed (.sometimeBefore .any (.is three)) ⟨two, two_hf⟩ ∧
      ¬ HFNative.sat Env.closed (.someOf (.base "Set") (.and (.empty .hashSet) (.nonEmpty .hashSet))) ⟨zero, zero_hf⟩ ∧
      HFNative.sat Env.closed (.everyOf (.base "Set") (.or (.empty .hashSet) (.nonEmpty .hashSet))) ⟨zero, zero_hf⟩ ∧
      HFNative.sat Env.closed (.someOf (.base "Set") (.possibly .any (.possibly .any .top))) ⟨zero, zero_hf⟩ ∧
      ¬ HFNative.sat Env.closed (.everyOf (.base "Set") (.necessarily .any (.necessarily .any .bot)))
        ⟨zero, zero_hf⟩ ∧
      HFNative.sat Env.closed (.sometimeBefore .any (.possibly .any (.possibly .any (.is one)))) ⟨one, one_hf⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨_, exact⟩ := askHereditary_sound two_in_three
    exact exact.mp rfl
  · obtain ⟨_, exact⟩ := askHereditary_sound none_empty_and_nonempty
    exact fun holds => Bool.false_ne_true (exact.mpr holds)
  · obtain ⟨_, exact⟩ := askHereditary_sound every_empty_or_nonempty
    exact exact.mp rfl
  · obtain ⟨_, exact⟩ := askHereditary_sound some_two_deep
    exact exact.mp rfl
  · obtain ⟨_, exact⟩ := askHereditary_sound not_every_flat
    exact fun holds => Bool.false_ne_true (exact.mpr holds)
  · obtain ⟨_, exact⟩ := askHereditary_sound one_deep_in_container
    exact exact.mp rfl

/-- **On a forward formula the set driver is the front door of the reference structure**: `0 ∈ 1`. -/
theorem one_contains_zero_membership : Membership.sat Env.closed (.possibly .any (.is zero)) one :=
  (askHereditary_membership rfl one_contains_zero).mp rfl

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings.SetDriverControls
