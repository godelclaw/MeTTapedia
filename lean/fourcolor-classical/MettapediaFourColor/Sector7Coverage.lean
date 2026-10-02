import FourColor.Present7
import MettapediaFourColor.Sector7Region

/-!
# Degree-seven coverage with the shared regional hubcap

Eight ancestor steps are reassembled around `Sector7Region.step`.
Unchanged branches use the pinned reference lemmas. The original
presentation and reducibility catalogue remain intact upstream.

The ancestor proofs derive from Gonthier and Werner's `present7.v`
(CeCILL-B), as ported to Lean by Chris Emery; the dependency retains
both provenance and licensing information.
-/

namespace FourColor.Sector7Coverage

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem s7_step5880 (hred : RedpartSound theRedpart) : SucceedsIn q7_5795 p7_5836r :=
  Sector7Region.step hred

theorem s7_step5882 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5795 p7_5835r := by
  refine succeed_by_split .spoke 4 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 1 5 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-3) <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 0 <|
       Hubcap.one 6 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5881
  intro _
  exact s7_step5880 hred

theorem s7_step5919 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5795 p7_5832r := by
  refine succeed_by_split .hat 0 6 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .fan1 6 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step5918 hred
  intro _
  refine succeed_by_split .spoke 5 6 false (by decide +kernel) ?_ ?_
  · exact s7_step5896 hred
  intro _
  refine succeed_by_split .hat 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5882 hred

theorem s7_step5937 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5795 p7_5830r := by
  refine succeed_by_split .hat 2 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 1 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    refine succeed_by_split .hat 3 5 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact s7_step5936 hred
  intro _
  refine succeed_by_split .hat 2 6 true (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 3 <|
       Hubcap.one 1 4 <|
       Hubcap.one 2 3 <|
       Hubcap.one 3 (-2) <|
       Hubcap.one 6 1 <|
       Hubcap.two 4 5 1 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5920
  intro _
  exact s7_step5919 hred

theorem s7_step5941 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5795 p7_5828r := by
  refine succeed_by_split .spoke 4 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 5 6 true (by decide +kernel) ?_ ?_
    · exact succeed_by_reducibility hred (by decide +kernel)
    intro _
    exact succeed_by_hubcap7 hred
      (Hubcap.one 3 (-3) <|
       Hubcap.one 4 2 <|
       Hubcap.one 5 (-2) <|
       Hubcap.two 0 2 7 <|
       Hubcap.two 1 6 6 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5940
  intro _
  refine succeed_by_split .spoke 5 7 false (by decide +kernel) ?_ ?_
  · exact succeed_by_hubcap7 hred
      (Hubcap.one 0 4 <|
       Hubcap.one 4 0 <|
       Hubcap.one 5 (-2) <|
       Hubcap.two 1 6 6 <|
       Hubcap.two 2 3 2 <|
       Hubcap.nil)
      rfl (by decide +kernel) (by decide +kernel) f7_5938
  intro _
  exact s7_step5937 hred

theorem s7_step6044 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_5795 p7_5795l := by
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · refine succeed_by_split .hat 5 5 true (by decide +kernel) ?_ ?_
    · exact s7_step6043 hred
    intro _
    exact s7_step5990 hred
  intro _
  refine succeed_by_split .spoke 5 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .hat 0 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  exact s7_step5941 hred

theorem s7_step6045 (hred : RedpartSound theRedpart) :
    SucceedsIn q7_4976 p7_4976l := by
  refine succeed_by_split .spoke 3 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
  · exact succeed_by_reducibility hred (by decide +kernel)
  intro _
  refine succeed_by_split .spoke 3 6 false (by decide +kernel) ?_ ?_
  · exact s7_step6044 hred
  intro L3_1
  refine succeed_by_split .spoke 6 6 false (by decide +kernel) ?_ ?_
  · exact succeed_by_similarity 4 true L3_1
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  intro _
  exact s7_step5825 hred L3_1

theorem s7_step6046 (hred : RedpartSound theRedpart) :
    SucceedsIn p7_0 p7_0 := by
  refine succeed_by_split .spoke 0 5 true (by decide +kernel) ?_ ?_
  · refine succeed_by_split .spoke 1 5 true (by decide +kernel) ?_ ?_
    · refine succeed_by_split .spoke 2 5 true (by decide +kernel) ?_ ?_
      · exact s7_step6045 hred
      intro L2_1
      refine succeed_by_split .spoke 6 5 true (by decide +kernel) ?_ ?_
      · exact succeed_by_similarity 6 false L2_1
          (by decide +kernel) (by decide +kernel) (by decide +kernel)
      intro _
      exact s7_step5792 hred L2_1
    intro L1_1
    exact s7_step4975 hred L1_1
  intro L0_1
  exact s7_step876 hred L0_1

/-- The degree-seven presentation consumes the replacement region. -/
theorem exclude7 : ExcludedArity (RedpartSound theRedpart) 7 := by
  apply exclude_arity
  intro hred
  exact s7_step6046 hred

end FourColor.Sector7Coverage
