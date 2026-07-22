import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrbitRankTransferClosure
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateOrdinaryTraceEnumeration
import Mettapedia.GraphTheory.FourColor.ClassicalCertificateReductionMetadata

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateOrbitRankOrdinaryClosure

open ClassicalCertificateHypermapColoring
open ClassicalCertificateKempeClosure
open ClassicalCertificateOrbitRankResponseSearch
open ClassicalCertificateOrbitRankTransferClosure
open ClassicalCertificateRankedKempe
open ClassicalCertificateReductionMetadata
open ClassicalCertificateTraceTree

variable {metadata : ClassicalCertificateReductionMetadata.Code}

/-- The exact empty-contract boundary language of one checked catalogue
configuration. -/
def ordinaryBase (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (word : TraceWord (ring metadata).length) : Bool :=
  (ClassicalCertificateOrdinaryTraceEnumeration.enumerate
    valid.partitionValid (ring metadata)).accepts word.toList

theorem ordinaryBase_sound
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (word : TraceWord (ring metadata).length)
    (hbase : ordinaryBase valid word = true) :
    FiniteHypermap.RingTrace
      (ClassicalCertificateFacePartition.checkedHypermap
        valid.partitionValid)
      (ring metadata) (word.toList.map TraceSymbol.toColor) := by
  exact
    (ClassicalCertificateOrdinaryTraceEnumeration.enumerate_accepts_iff_ringTrace
      valid.partitionValid (ring metadata) valid.reverseBoundaryCycle
        word.toList).1 hbase

/-- The rank-vector transfer certificate specialized to genuine ordinary
boundary colorings of one checked catalogue configuration. -/
theorem derivation_to_ringTrace
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (table : Table (ring metadata).length)
    (certificate : ClassicalCertificateRankVectorProduct.Certificate
      (ring metadata).length)
    (config : Nat) (hconfig : config < table.ranks.configCount)
    (hranks : certificate.ranks = table.ranks)
    (hproduct : certificate.checker = true)
    (hwitness : responseWitnessChecker table certificate.responseCode
      certificate.responseRoot = true)
    (hlaunch : launchCoverageChecker table certificate config = true)
    (hbase : baseCoverageChecker table config (ordinaryBase valid) = true)
    (word : TraceWord (ring metadata).length) (rank : Nat)
    (hrank : table.rankAt? config word = some rank) :
    CoclosureDerivation
      (fun otherWord => FiniteHypermap.RingTrace
        (ClassicalCertificateFacePartition.checkedHypermap
          valid.partitionValid)
      (ring metadata) (otherWord.map TraceSymbol.toColor))
      word.toList := by
  exact ClassicalCertificateOrbitRankTransferClosure.derivation
    table certificate config hconfig hranks hproduct hwitness hlaunch
      (ordinaryBase valid) hbase
      (fun otherWord => FiniteHypermap.RingTrace
        (ClassicalCertificateFacePartition.checkedHypermap
          valid.partitionValid)
        (ring metadata) (otherWord.map TraceSymbol.toColor))
      (ordinaryBase_sound valid) word rank hrank

theorem kempeCoclosure_to_ringTrace
    (valid : ClassicalCertificateReductionMetadata.Valid metadata)
    (table : Table (ring metadata).length)
    (certificate : ClassicalCertificateRankVectorProduct.Certificate
      (ring metadata).length)
    (config : Nat) (hconfig : config < table.ranks.configCount)
    (hranks : certificate.ranks = table.ranks)
    (hproduct : certificate.checker = true)
    (hwitness : responseWitnessChecker table certificate.responseCode
      certificate.responseRoot = true)
    (hlaunch : launchCoverageChecker table certificate config = true)
    (hbase : baseCoverageChecker table config (ordinaryBase valid) = true)
    (word : TraceWord (ring metadata).length) (rank : Nat)
    (hrank : table.rankAt? config word = some rank) :
    KempeCoclosure
      (fun otherWord => FiniteHypermap.RingTrace
        (ClassicalCertificateFacePartition.checkedHypermap
          valid.partitionValid)
        (ring metadata) (otherWord.map TraceSymbol.toColor))
      word.toList :=
  (derivation_to_ringTrace valid table certificate config hconfig hranks
    hproduct hwitness hlaunch hbase word rank hrank).sound

end ClassicalCertificateOrbitRankOrdinaryClosure

end Mettapedia.GraphTheory.FourColor
