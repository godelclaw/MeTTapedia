import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankResponseSearch

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankWitness

open ClassicalCertificateKempeClosure
open ClassicalCertificateOrbitRankResponseSearch
open ClassicalCertificatePackedRankVector
open ClassicalCertificateRankedKempe
open ClassicalCertificateRankVectorDag
open ClassicalCertificateRankVectorProduct

variable {length : Nat}

set_option maxRecDepth 1000000
set_option maxHeartbeats 200000000

/-- A word carries a configuration rank when some global color permutation
reaches an orbit leaf whose packed vector carries that rank.  This relation
does not privilege the first successful permutation in an executable search. -/
def HasOrbitRank (table : Table length) (config : Nat)
    (word : TraceWord length) (rank : Nat) : Prop :=
  ∃ permutation vector,
    table.vectorAt? (permute permutation word) = some vector ∧
      table.ranks.rankAt? vector config = some rank

/-- The executable first-hit lookup always supplies the permutation-free
semantic orbit-rank relation. -/
theorem hasOrbitRank_of_rankAt?_eq_some (table : Table length)
    (config rank : Nat) (word : TraceWord length)
    (hrank : table.rankAt? config word = some rank) :
    HasOrbitRank table config word rank := by
  exact table.rankAt?_sound config rank word hrank

/-- Concrete data witnessing one occurrence of a rank in a color orbit. -/
structure OrbitRankWitness where
  permutation : PermutationCode
  vector : Nat
  deriving DecidableEq, Repr

def OrbitRankWitness.Valid (table : Table length) (config rank : Nat)
    (word : TraceWord length) (witness : OrbitRankWitness) : Prop :=
  table.vectorAt? (permute witness.permutation word) = some witness.vector ∧
    table.ranks.rankAt? witness.vector config = some rank

/-- Direct validation of an orbit-rank witness performs one trie lookup and
one packed-rank lookup. -/
def OrbitRankWitness.check (table : Table length) (config rank : Nat)
    (word : TraceWord length) (witness : OrbitRankWitness) : Bool :=
  decide
      (table.vectorAt? (permute witness.permutation word) =
        some witness.vector) &&
    decide (table.ranks.rankAt? witness.vector config = some rank)

theorem OrbitRankWitness.valid_of_check_eq_true (table : Table length)
    (config rank : Nat) (word : TraceWord length)
    (witness : OrbitRankWitness)
    (hcheck : witness.check table config rank word = true) :
    witness.Valid table config rank word := by
  simp only [OrbitRankWitness.check, Bool.and_eq_true] at hcheck
  exact ⟨of_decide_eq_true hcheck.1, of_decide_eq_true hcheck.2⟩

theorem OrbitRankWitness.hasOrbitRank_of_valid (table : Table length)
    (config rank : Nat) (word : TraceWord length)
    (witness : OrbitRankWitness)
    (hvalid : witness.Valid table config rank word) :
    HasOrbitRank table config word rank :=
  ⟨witness.permutation, witness.vector, hvalid⟩

theorem OrbitRankWitness.hasOrbitRank_of_check_eq_true
    (table : Table length) (config rank : Nat) (word : TraceWord length)
    (witness : OrbitRankWitness)
    (hcheck : witness.check table config rank word = true) :
    HasOrbitRank table config word rank :=
  witness.hasOrbitRank_of_valid table config rank word
    (witness.valid_of_check_eq_true table config rank word hcheck)

/-- A response witness records both a word in the required chromogram fiber
and an explicit orbit representative carrying its prescribed rank. -/
structure ResponseRankWitness (length : Nat) where
  word : TraceWord length
  orbit : OrbitRankWitness

def ResponseRankWitness.Valid (table : Table length) (config rank : Nat)
    (gram : GramWord length) (witness : ResponseRankWitness length) : Prop :=
  Matches witness.word.toList gram.toList ∧
    witness.orbit.Valid table config rank witness.word

/-- Direct response validation avoids enumeration of the whole chromogram
fiber: it checks the supplied word, orbit representative, and packed rank. -/
def ResponseRankWitness.check (table : Table length) (config rank : Nat)
    (gram : GramWord length) (witness : ResponseRankWitness length) : Bool :=
  decide (Matches witness.word.toList gram.toList) &&
    witness.orbit.check table config rank witness.word

theorem ResponseRankWitness.valid_of_check_eq_true (table : Table length)
    (config rank : Nat) (gram : GramWord length)
    (witness : ResponseRankWitness length)
    (hcheck : witness.check table config rank gram = true) :
    witness.Valid table config rank gram := by
  simp only [ResponseRankWitness.check, Bool.and_eq_true] at hcheck
  exact ⟨of_decide_eq_true hcheck.1,
    witness.orbit.valid_of_check_eq_true table config rank witness.word
      hcheck.2⟩

theorem ResponseRankWitness.exists_matching_hasOrbitRank_of_valid
    (table : Table length) (config rank : Nat) (gram : GramWord length)
    (witness : ResponseRankWitness length)
    (hvalid : witness.Valid table config rank gram) :
    ∃ response : TraceWord length,
      Matches response.toList gram.toList ∧
        HasOrbitRank table config response rank := by
  exact ⟨witness.word, hvalid.1,
    witness.orbit.hasOrbitRank_of_valid table config rank witness.word
      hvalid.2⟩

/-- Semantic response interface for explicit orbit witnesses.  Unlike
`ResponseWitnessValid`, it does not require the chosen rank to be the first
successful value returned by a color-permutation search. -/
def ExplicitResponseWitnessValid (table : Table length)
    (code : ResponseCode) (root : Nat) : Prop :=
  ∀ gram : GramWord length, ∀ responseVector,
    code.lookup root gram.toList = some responseVector →
      ∀ config rank, config < table.ranks.configCount →
        table.ranks.rankAt? responseVector config = some rank →
          ∃ response : TraceWord length,
            Matches response.toList gram.toList ∧
              HasOrbitRank table config response rank

/-- The legacy first-hit witness interface is a special case of explicit
orbit-rank realization. -/
theorem explicitResponseWitnessValid_of_responseWitnessValid
    (table : Table length) (code : ResponseCode) (root : Nat)
    (hvalid : ResponseWitnessValid table code root) :
    ExplicitResponseWitnessValid table code root := by
  intro gram responseVector hlookup config rank hconfig hrank
  obtain ⟨response, hmatches, hresponseRank⟩ :=
    hvalid gram responseVector hlookup config rank hconfig hrank
  exact ⟨response, hmatches,
    hasOrbitRank_of_rankAt?_eq_some table config rank response hresponseRank⟩

/-- Product descent composed with explicit response realization produces a
matching word carrying a strictly smaller orbit rank. -/
theorem exists_lower_explicit_response_of_validities
    (certificate : ClassicalCertificateRankVectorProduct.Certificate length)
    (table : Table length)
    (hranks : certificate.ranks = table.ranks)
    (hproduct : ProductValid certificate)
    (hwitness : ExplicitResponseWitnessValid table certificate.responseCode
      certificate.responseRoot)
    (word : TraceWord length) (sourceVector config sourceRank : Nat)
    (haccepted : certificate.traceCode.lookup length certificate.sourceRoot
      word.toList = some sourceVector)
    (hconfig : config < table.ranks.configCount)
    (hsourceRank : table.ranks.rankAt? sourceVector config = some sourceRank)
    (gram : GramWord length)
    (hmatch : Matches word.toList gram.toList) :
    0 < sourceRank ∧
      ∃ response : TraceWord length, ∃ responseRank,
        Matches response.toList gram.toList ∧
          HasOrbitRank table config response responseRank ∧
            responseRank < sourceRank := by
  have hsourceRank' : certificate.ranks.rankAt? sourceVector config =
      some sourceRank := by simpa [hranks] using hsourceRank
  have hconfig' : config < certificate.ranks.configCount := by
    simpa [hranks] using hconfig
  obtain ⟨hpositive, responseVector, responseRank, hlookup,
      hresponseRank, hlower⟩ :=
    hproduct word sourceVector config sourceRank haccepted hconfig'
      hsourceRank' gram hmatch
  have hresponseRank' : table.ranks.rankAt? responseVector config =
      some responseRank := by simpa [hranks] using hresponseRank
  obtain ⟨response, hmatches, hrank⟩ :=
    hwitness gram responseVector hlookup config responseRank hconfig
      hresponseRank'
  exact ⟨hpositive, response, responseRank, hmatches, hrank, hlower⟩

end ClassicalCertificateOrbitRankWitness

end Mettapedia.GraphTheory.FourColor
