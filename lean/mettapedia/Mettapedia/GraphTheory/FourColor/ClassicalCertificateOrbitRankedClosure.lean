import Mettapedia.GraphTheory.FourColor.ClassicalCertificateRankedKempe

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankedClosure

open ClassicalCertificateKempeClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateTraceTree

/-- A ranked closure system modulo global permutations.  Each represented
word has a chosen launch spelling in its color orbit, and launch spellings
carry one response for every matching chromogram. -/
structure System (length : Nat) where
  rank? : TraceWord length → Option Nat
  launchPermutation : TraceWord length → PermutationCode
  response : TraceWord length → GramWord length → TraceWord length

namespace System

variable {length : Nat}

def launch (system : System length) (word : TraceWord length) :
    TraceWord length :=
  permute (system.launchPermutation word) word

/-- The doubled rank leaves one strictly decreasing step for canonicalizing a
nonlaunch spelling before the lower-rank chromogram recursion begins. -/
def measure (system : System length) (word : TraceWord length) : Nat :=
  match system.rank? word with
  | none => 0
  | some rank =>
      2 * rank + if system.launch word = word then 0 else 1

end System

/-- Mathematical validity conditions for an orbit-ranked closure system. -/
structure Valid (system : System length)
    (ordinary : List TraceSymbol → Prop) : Prop where
  rank_launch : ∀ word,
    system.rank? (system.launch word) = system.rank? word
  launch_idempotent : ∀ word,
    system.launch (system.launch word) = system.launch word
  ordinary_of_rank_zero : ∀ word,
    system.launch word = word → system.rank? word = some 0 →
      ordinary word.toList
  response_matches : ∀ word rank,
    system.launch word = word → system.rank? word = some (rank + 1) →
      ∀ gram ∈ matchingGramWords word,
        Matches (system.response word gram).toList gram.toList
  response_decreases : ∀ word rank,
    system.launch word = word → system.rank? word = some (rank + 1) →
      ∀ gram ∈ matchingGramWords word,
        ∃ responseRank,
          system.rank? (system.response word gram) = some responseRank ∧
            responseRank < rank + 1

private def gramWordOfMatch (word : TraceWord length)
    (gram : Chromogram) (hmatch : Matches word.toList gram) :
    GramWord length :=
  ⟨gram, hmatch.length_eq.symm.trans word.2⟩

theorem measure_launch_lt (system : System length)
    (valid : Valid system ordinary)
    (word : TraceWord length) (rank : Nat)
    (hrank : system.rank? word = some rank)
    (hnotLaunch : system.launch word ≠ word) :
    system.measure (system.launch word) < system.measure word := by
  have hrankLaunch :
      system.rank? (system.launch word) = some rank := by
    rw [valid.rank_launch, hrank]
  simp [System.measure, hrank, hrankLaunch, hnotLaunch,
    valid.launch_idempotent]

theorem measure_response_lt (system : System length)
    (valid : Valid system ordinary)
    (word : TraceWord length) (rank responseRank : Nat)
    (hlaunch : system.launch word = word)
    (hrank : system.rank? word = some (rank + 1))
    (gram : GramWord length)
    (hresponseRank :
      system.rank? (system.response word gram) = some responseRank)
    (hlower : responseRank < rank + 1) :
    system.measure (system.response word gram) < system.measure word := by
  simp only [System.measure, hresponseRank, hrank, hlaunch, if_pos]
  split
  · omega
  · omega

/-- Valid orbit-ranked rules assemble into a finite Kempe co-closure
derivation.  The recursion alternates at most one global permutation step with
strict descent in the orbit rank. -/
theorem derivation (system : System length)
    (valid : Valid system ordinary)
    (word : TraceWord length) (rank : Nat)
    (hrank : system.rank? word = some rank) :
    CoclosureDerivation ordinary word.toList := by
  by_cases hlaunch : system.launch word = word
  · cases rank with
    | zero =>
        exact .member (valid.ordinary_of_rank_zero word hlaunch hrank)
    | succ rank =>
        refine .chromograms
          (fun gram hmatch =>
            (system.response word
              (gramWordOfMatch word gram hmatch)).toList) ?_ ?_
        · intro gram hmatch
          let fixedGram := gramWordOfMatch word gram hmatch
          have hmem : fixedGram ∈ matchingGramWords word :=
            mem_matchingGramWords word fixedGram hmatch
          simpa [fixedGram, gramWordOfMatch] using
            valid.response_matches word rank hlaunch hrank fixedGram hmem
        · intro gram hmatch
          let fixedGram := gramWordOfMatch word gram hmatch
          have hmem : fixedGram ∈ matchingGramWords word :=
            mem_matchingGramWords word fixedGram hmatch
          obtain ⟨responseRank, hresponseRank, hlower⟩ :=
            valid.response_decreases word rank hlaunch hrank fixedGram hmem
          exact derivation system valid (system.response word fixedGram)
            responseRank hresponseRank
  · apply CoclosureDerivation.permutation
      (system.launchPermutation word).toEquiv
    simpa [System.launch] using
      derivation system valid (system.launch word) rank (by
        simpa [hrank] using valid.rank_launch word)
termination_by system.measure word
decreasing_by
  · exact measure_response_lt system valid word rank responseRank hlaunch
      hrank fixedGram hresponseRank hlower
  · exact measure_launch_lt system valid word rank hrank hlaunch

theorem kempeCoclosure (system : System length)
    (valid : Valid system ordinary)
    (word : TraceWord length) (rank : Nat)
    (hrank : system.rank? word = some rank) :
    KempeCoclosure ordinary word.toList :=
  (derivation system valid word rank hrank).sound

end ClassicalCertificateOrbitRankedClosure

end Mettapedia.GraphTheory.FourColor
