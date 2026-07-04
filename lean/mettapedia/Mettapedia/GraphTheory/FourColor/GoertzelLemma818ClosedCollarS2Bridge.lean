import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word0
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word1
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word2
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word3
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word4
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word5
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word6
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word7
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word8
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word9
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word10
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarS2Word11

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelLemma818ClosedCollarS2Bridge

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget

theorem closedCollarS2BridgeTarget_proved :
    closedCollarS2BridgeTarget := by
  intro orients horients
  have hcases :
      orients = GoertzelLemma818ClosedCollarS2Word0.word ∨
      orients = GoertzelLemma818ClosedCollarS2Word1.word ∨
      orients = GoertzelLemma818ClosedCollarS2Word2.word ∨
      orients = GoertzelLemma818ClosedCollarS2Word3.word ∨
      orients = GoertzelLemma818ClosedCollarS2Word4.word ∨
      orients = GoertzelLemma818ClosedCollarS2Word5.word ∨
      orients = GoertzelLemma818ClosedCollarS2Word6.word ∨
      orients = GoertzelLemma818ClosedCollarS2Word7.word ∨
      orients = GoertzelLemma818ClosedCollarS2Word8.word ∨
      orients = GoertzelLemma818ClosedCollarS2Word9.word ∨
      orients = GoertzelLemma818ClosedCollarS2Word10.word ∨
      orients = GoertzelLemma818ClosedCollarS2Word11.word := by
    simpa [closedCollarL1Words, tauOrientWords2, tauOrientWords3, bindList,
      GoertzelLemma818ClosedCollarS2Word0.word,
      GoertzelLemma818ClosedCollarS2Word1.word,
      GoertzelLemma818ClosedCollarS2Word2.word,
      GoertzelLemma818ClosedCollarS2Word3.word,
      GoertzelLemma818ClosedCollarS2Word4.word,
      GoertzelLemma818ClosedCollarS2Word5.word,
      GoertzelLemma818ClosedCollarS2Word6.word,
      GoertzelLemma818ClosedCollarS2Word7.word,
      GoertzelLemma818ClosedCollarS2Word8.word,
      GoertzelLemma818ClosedCollarS2Word9.word,
      GoertzelLemma818ClosedCollarS2Word10.word,
      GoertzelLemma818ClosedCollarS2Word11.word] using horients
  rcases hcases with h0 | hcases
  · subst orients
    simpa using GoertzelLemma818ClosedCollarS2Word0.targetForWord
  rcases hcases with h1 | hcases
  · subst orients
    simpa using GoertzelLemma818ClosedCollarS2Word1.targetForWord
  rcases hcases with h2 | hcases
  · subst orients
    simpa using GoertzelLemma818ClosedCollarS2Word2.targetForWord
  rcases hcases with h3 | hcases
  · subst orients
    simpa using GoertzelLemma818ClosedCollarS2Word3.targetForWord
  rcases hcases with h4 | hcases
  · subst orients
    simpa using GoertzelLemma818ClosedCollarS2Word4.targetForWord
  rcases hcases with h5 | hcases
  · subst orients
    simpa using GoertzelLemma818ClosedCollarS2Word5.targetForWord
  rcases hcases with h6 | hcases
  · subst orients
    simpa using GoertzelLemma818ClosedCollarS2Word6.targetForWord
  rcases hcases with h7 | hcases
  · subst orients
    simpa using GoertzelLemma818ClosedCollarS2Word7.targetForWord
  rcases hcases with h8 | hcases
  · subst orients
    simpa using GoertzelLemma818ClosedCollarS2Word8.targetForWord
  rcases hcases with h9 | hcases
  · subst orients
    simpa using GoertzelLemma818ClosedCollarS2Word9.targetForWord
  rcases hcases with h10 | h11
  · subst orients
    simpa using GoertzelLemma818ClosedCollarS2Word10.targetForWord
  · subst orients
    simpa using GoertzelLemma818ClosedCollarS2Word11.targetForWord

theorem section92S2BridgeLemmaTarget_proved :
    section92S2BridgeLemmaTarget :=
  section92S2BridgeLemmaTarget_of_closedCollarS2BridgeTarget
    closedCollarS2BridgeTarget_proved

end GoertzelLemma818ClosedCollarS2Bridge

end Mettapedia.GraphTheory.FourColor
