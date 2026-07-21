import Mettapedia.GraphTheory.FourColor.ClassicalCertificateConfigurationCatalogue

namespace Mettapedia.GraphTheory.FourColor

namespace ClassicalCertificateCataloguePrograms

open ClassicalCertificateConfiguration
open ClassicalCertificateConfigurationCatalogue

set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

/-- Published configuration programs `cf001` through `cf016`. -/
def classicalConfigurationChunk00 : Array Configuration := #[
      { symmetric := true
        contractReferences := [13]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 5, .hexagon, .rotate 5, .yellow, .rotate 4,
                .hexagon, .rotate 4, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 6, .yellow, .rotate 4, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 4, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := true
        contractReferences := [17]
        program :=
          [.hexagon, .rotate 1, .hexagon, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 6, .hexagon, .rotate 6, .hexagon, .rotate 6, .yellow, .yellow,
                .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [1, 2, 12, 13]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 7, .yellow, .rotate 5, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .rotate 2,
                .yellow, .rotate 2, .yellow] },
      { symmetric := true
        contractReferences := [10]
        program :=
          [.hexagon, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon,
                .rotate 4, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [19]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 4, .hexagon, .rotate 7,
                .hexagon, .rotate 2, .hexagon, .rotate 7, .yellow, .rotate 6, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 4, .yellow,
                .rotate 2, .yellow, .yellow] },
      { symmetric := true
        contractReferences := [17]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 8, .hexagon, .rotate 8, .yellow, .rotate 6,
                .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow,
                .rotate 5, .yellow, .rotate 3, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := true
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 7, .yellow, .rotate 3, .hexagon, .rotate 6,
                .yellow, .rotate 2, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .hexagon,
                .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 7, .yellow,
                .rotate 3, .hexagon, .rotate 6, .hexagon, .rotate 6, .yellow, .yellow, .yellow,
                .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [20]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 4, .hexagon, .rotate 2,
                .hexagon, .rotate 8, .yellow, .rotate 3, .hexagon, .rotate 1, .yellow,
                .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2,
                .hexagon, .rotate 4, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := true
        contractReferences := [1, 2, 8, 9]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 6, .hexagon,
                .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 6, .yellow, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 2, .yellow] },
      { symmetric := true
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 3, .hexagon, .rotate 7,
                .yellow, .rotate 3, .hexagon, .rotate 6, .yellow, .rotate 2, .hexagon,
                .rotate 1, .yellow, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 2, .hexagon,
                .rotate 7, .yellow, .rotate 6, .yellow, .rotate 4, .yellow, .rotate 3, .yellow,
                .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [14]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 5, .yellow, .rotate 2, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [8, 9, 15, 16]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow,
                .rotate 6, .hexagon, .rotate 7, .yellow, .rotate 2, .hexagon, .rotate 6,
                .yellow, .yellow, .yellow, .rotate 3, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 5, .hexagon, .rotate 8, .hexagon, .rotate 2, .hexagon,
                .rotate 8, .yellow, .rotate 6, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 2,
                .yellow, .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf017` through `cf032`. -/
def classicalConfigurationChunk01 : Array Configuration := #[
      { symmetric := true
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow,
                .rotate 4, .hexagon, .rotate 7, .hexagon, .rotate 7, .yellow, .rotate 3,
                .yellow, .rotate 4, .yellow, .rotate 3, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 2, .hexagon, .rotate 8, .yellow,
                .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 6,
                .yellow, .rotate 3, .yellow, .rotate 3, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8,
                .yellow, .rotate 3, .hexagon, .rotate 7, .yellow, .rotate 2, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .hexagon, .rotate 5, .yellow, .yellow,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [1, 2, 8, 9]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 7, .hexagon, .rotate 2, .hexagon,
                .rotate 9, .yellow, .rotate 5, .yellow, .rotate 3, .hexagon, .rotate 7,
                .hexagon, .rotate 7, .yellow, .yellow, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow] },
      { symmetric := true
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 3, .hexagon,
                .rotate 7, .yellow, .rotate 2, .hexagon, .rotate 1, .yellow, .hexagon,
                .rotate 5, .yellow, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 2, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 5, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [1, 2, 8, 9]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 5, .yellow, .rotate 6,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 3, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 7, .yellow, .rotate 5, .hexagon, .rotate 1,
                .yellow, .rotate 5, .hexagon, .rotate 5, .hexagon, .rotate 5, .yellow,
                .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := true
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 4, .yellow,
                .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [19]
        program :=
          [.hexagon, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 7,
                .yellow, .rotate 4, .hexagon, .rotate 5, .hexagon, .rotate 1, .yellow,
                .rotate 2, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 6, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 6, .yellow, .rotate 3, .hexagon,
                .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 4, .hexagon, .rotate 3,
                .hexagon, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [4, 5, 21, 25]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 6, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [19]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 4, .hexagon, .rotate 8,
                .hexagon, .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 5,
                .hexagon, .rotate 5, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [18]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 6, .hexagon, .rotate 8,
                .hexagon, .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 2, .hexagon,
                .rotate 7, .yellow, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 3, .hexagon, .rotate 7, .hexagon,
                .rotate 7, .yellow, .rotate 6, .yellow, .rotate 4, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf033` through `cf048`. -/
def classicalConfigurationChunk02 : Array Configuration := #[
      { symmetric := false
        contractReferences := [24]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 6,
                .hexagon, .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 6, .hexagon,
                .rotate 1, .yellow, .rotate 6, .yellow, .rotate 4, .yellow, .yellow, .rotate 2,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [15]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 5, .hexagon, .rotate 2, .hexagon, .rotate 7, .yellow,
                .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .rotate 3, .yellow,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 6, .yellow, .rotate 4, .yellow, .rotate 4, .hexagon, .rotate 4, .yellow,
                .rotate 2, .yellow, .yellow] },
      { symmetric := true
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 8, .yellow, .rotate 4, .hexagon, .rotate 6, .hexagon,
                .rotate 1, .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := true
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 5, .hexagon, .rotate 2, .hexagon, .rotate 7, .yellow,
                .rotate 6, .hexagon, .rotate 6, .yellow, .rotate 4, .yellow, .rotate 2, .yellow,
                .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [10]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 3, .hexagon, .rotate 7,
                .yellow, .rotate 3, .hexagon, .rotate 6, .yellow, .rotate 2, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .hexagon, .rotate 4, .yellow, .yellow,
                .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [1, 2, 8, 9]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 3, .hexagon, .rotate 3, .hexagon, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [11, 12, 21, 26]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 2,
                .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow,
                .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [20]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 5, .hexagon, .rotate 2,
                .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 1, .yellow,
                .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 5, .hexagon, .rotate 5, .yellow, .rotate 3, .yellow, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon, .rotate 2, .hexagon,
                .rotate 8, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 2, .hexagon, .rotate 5, .yellow, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .hexagon,
                .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 7,
                .yellow, .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow] },
      { symmetric := false
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon,
                .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 2, .hexagon, .rotate 7,
                .yellow, .yellow, .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [24]
        program :=
          [.hexagon, .rotate 6, .hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 9,
                .yellow, .rotate 6, .hexagon, .rotate 1, .hexagon, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 7, .yellow, .yellow, .yellow,
                .rotate 4, .hexagon, .rotate 4, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [18]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1,
                .hexagon, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 2, .hexagon,
                .rotate 7, .yellow, .yellow, .rotate 4, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow,
                .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 6, .yellow, .rotate 4, .yellow,
                .rotate 2, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8,
                .yellow, .rotate 3, .hexagon, .rotate 7, .yellow, .rotate 4, .hexagon,
                .rotate 5, .hexagon, .rotate 1, .yellow, .hexagon, .rotate 5, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow] }
    ]

/-- Published configuration programs `cf049` through `cf064`. -/
def classicalConfigurationChunk03 : Array Configuration := #[
      { symmetric := false
        contractReferences := [28]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 4, .hexagon,
                .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 1,
                .yellow, .rotate 5, .yellow, .rotate 4, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 2,
                .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow,
                .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 6,
                .yellow, .rotate 2, .yellow, .rotate 2, .yellow, .rotate 2, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [14]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 6, .hexagon, .rotate 6,
                .yellow, .rotate 3, .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [24]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow,
                .rotate 3, .hexagon, .rotate 7, .yellow, .rotate 2, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 3,
                .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 5, .yellow,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [28]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 7,
                .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 6, .hexagon,
                .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 7, .yellow, .rotate 5, .yellow,
                .yellow, .rotate 3, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [28]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 2, .hexagon, .rotate 8, .yellow,
                .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .rotate 2,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [28]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 5, .hexagon, .rotate 3, .hexagon, .rotate 8, .hexagon,
                .rotate 8, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 5, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [7]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow,
                .rotate 6, .hexagon, .rotate 7, .yellow, .rotate 5, .yellow, .rotate 4,
                .hexagon, .rotate 5, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 3, .hexagon,
                .rotate 8, .hexagon, .rotate 8, .yellow, .rotate 7, .yellow, .rotate 5, .yellow,
                .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [28]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 2,
                .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow,
                .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 6,
                .yellow, .yellow, .yellow, .rotate 2, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [21]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 7, .hexagon, .rotate 2,
                .hexagon, .rotate 9, .yellow, .rotate 5, .hexagon, .rotate 3, .hexagon,
                .rotate 8, .hexagon, .rotate 8, .yellow, .rotate 7, .yellow, .rotate 4, .yellow,
                .rotate 1, .yellow, .rotate 3, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 7, .yellow, .rotate 2, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [8, 9, 15, 16]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .yellow,
                .rotate 4, .hexagon, .rotate 7, .hexagon, .rotate 7, .hexagon, .rotate 7,
                .yellow, .yellow, .yellow, .rotate 4, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 8,
                .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 8, .yellow, .rotate 2,
                .hexagon, .rotate 7, .yellow, .yellow, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [4, 5, 22, 27]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 6, .hexagon, .rotate 7,
                .yellow, .yellow, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf065` through `cf080`. -/
def classicalConfigurationChunk04 : Array Configuration := #[
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 4, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 8, .yellow, .rotate 6, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [1, 2, 8, 9]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 4, .hexagon, .rotate 3, .hexagon, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 6, .hexagon, .rotate 1, .hexagon,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 8,
                .hexagon, .rotate 8, .yellow, .yellow, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .hexagon,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 6, .yellow, .rotate 5,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .hexagon,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 8,
                .yellow, .yellow, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 4,
                .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 2,
                .hexagon, .rotate 9, .yellow, .rotate 5, .hexagon, .rotate 8, .hexagon,
                .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .yellow, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [21]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .hexagon, .rotate 8, .hexagon, .rotate 8, .yellow, .yellow,
                .rotate 1, .yellow, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 6,
                .hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow,
                .rotate 7, .hexagon, .rotate 8, .yellow, .rotate 2, .hexagon, .rotate 7,
                .yellow, .yellow, .yellow, .rotate 4, .hexagon, .rotate 4, .yellow, .rotate 2,
                .yellow, .yellow] },
      { symmetric := false
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon,
                .rotate 8, .yellow, .rotate 3, .hexagon, .rotate 7, .yellow, .rotate 2,
                .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow, .yellow] },
      { symmetric := false
        contractReferences := [15]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1,
                .yellow, .rotate 5, .yellow, .rotate 3, .yellow, .rotate 3, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [15, 29]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 6, .hexagon, .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 7,
                .yellow, .rotate 5, .yellow, .rotate 3, .yellow, .rotate 3, .yellow, .yellow,
                .yellow] },
      { symmetric := true
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 6,
                .hexagon, .rotate 6, .yellow, .rotate 2, .yellow, .rotate 4, .yellow, .yellow,
                .yellow] },
      { symmetric := true
        contractReferences := [14]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8,
                .yellow, .rotate 3, .hexagon, .rotate 7, .yellow, .rotate 3, .hexagon,
                .rotate 6, .yellow, .rotate 2, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [14]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 3, .hexagon,
                .rotate 7, .yellow, .rotate 2, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [18]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon,
                .rotate 8, .yellow, .rotate 3, .hexagon, .rotate 7, .yellow, .rotate 3,
                .hexagon, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 2, .yellow,
                .rotate 1, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow,
                .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 2, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 4, .yellow, .rotate 3,
                .yellow, .yellow, .yellow] }
    ]

/-- Published configuration programs `cf081` through `cf096`. -/
def classicalConfigurationChunk05 : Array Configuration := #[
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon,
                .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 7, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 3,
                .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [14]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon,
                .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .hexagon, .rotate 5, .yellow, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [4, 5, 25, 30]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 8,
                .hexagon, .rotate 8, .yellow, .yellow, .yellow, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [20]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon,
                .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 5, .hexagon, .rotate 4, .hexagon, .rotate 9, .hexagon,
                .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 5, .yellow, .rotate 4, .yellow, .rotate 1, .yellow, .rotate 3,
                .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 3, .hexagon,
                .rotate 5, .hexagon, .rotate 5, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon,
                .rotate 10, .yellow, .rotate 7, .hexagon, .rotate 9, .yellow, .rotate 3,
                .hexagon, .rotate 8, .hexagon, .rotate 8, .yellow, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [8, 9, 15, 16]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 6, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 8,
                .hexagon, .rotate 8, .yellow, .yellow, .rotate 1, .yellow, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [14, 15, 21, 22]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11,
                .yellow, .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 8,
                .yellow, .rotate 3, .hexagon, .rotate 7, .yellow, .yellow, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2,
                .hexagon, .rotate 6, .yellow, .yellow, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [28]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 1, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 2,
                .hexagon, .rotate 8, .yellow, .yellow, .yellow, .rotate 5, .hexagon, .rotate 5,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [22]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 8, .yellow, .yellow, .rotate 5,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .hexagon, .rotate 5, .yellow,
                .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 6, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 8,
                .hexagon, .rotate 8, .yellow, .yellow, .rotate 1, .yellow, .yellow, .rotate 4,
                .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [28]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon,
                .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 2,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 5, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 7, .yellow, .rotate 3, .yellow, .rotate 4,
                .yellow, .yellow, .rotate 1, .yellow, .yellow] }
    ]

/-- Published configuration programs `cf097` through `cf112`. -/
def classicalConfigurationChunk06 : Array Configuration := #[
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon,
                .rotate 8, .yellow, .rotate 4, .hexagon, .rotate 7, .hexagon, .rotate 7,
                .yellow, .yellow, .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 6, .hexagon, .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 7,
                .yellow, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 5, .yellow, .yellow,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [18]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 6,
                .hexagon, .rotate 1, .yellow, .hexagon, .rotate 5, .yellow, .yellow, .yellow,
                .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon,
                .rotate 8, .yellow, .rotate 2, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .hexagon, .rotate 6, .yellow, .yellow, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8,
                .yellow, .rotate 6, .yellow, .rotate 5, .hexagon, .rotate 6, .yellow, .rotate 3,
                .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 6, .yellow, .rotate 3, .yellow, .rotate 4,
                .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 7, .yellow, .rotate 3, .yellow, .rotate 4,
                .yellow, .yellow, .yellow, .yellow] },
      { symmetric := true
        contractReferences := [31, 33]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon,
                .rotate 10, .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9,
                .yellow, .rotate 8, .yellow, .rotate 5, .yellow, .rotate 4, .yellow, .rotate 4,
                .yellow, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon,
                .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 6,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 6, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 2, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 3, .hexagon,
                .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 9,
                .yellow, .rotate 2, .hexagon, .rotate 8, .yellow, .yellow, .yellow, .rotate 3,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 9, .yellow, .rotate 2, .hexagon, .rotate 8,
                .yellow, .yellow, .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .hexagon, .rotate 5, .yellow, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 2, .hexagon, .rotate 7,
                .yellow, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 8, .yellow, .rotate 2, .hexagon,
                .rotate 1, .yellow, .rotate 5, .yellow, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 2,
                .hexagon, .rotate 8, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow,
                .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .yellow, .rotate 3,
                .yellow, .yellow] },
      { symmetric := true
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 6, .hexagon, .rotate 1, .yellow,
                .rotate 6, .yellow, .rotate 3, .hexagon, .rotate 1, .yellow, .rotate 4, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow] }
    ]

/-- Published configuration programs `cf113` through `cf128`. -/
def classicalConfigurationChunk07 : Array Configuration := #[
      { symmetric := true
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 8,
                .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon,
                .rotate 6, .yellow, .rotate 3, .hexagon, .rotate 5, .hexagon, .rotate 5,
                .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon, .rotate 2, .hexagon,
                .rotate 8, .yellow, .rotate 3, .hexagon, .rotate 7, .hexagon, .rotate 7,
                .yellow, .yellow, .yellow, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 9,
                .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon,
                .rotate 8, .hexagon, .rotate 8, .yellow, .yellow, .yellow, .rotate 4, .hexagon,
                .rotate 5, .hexagon, .rotate 5, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := true
        contractReferences := [1, 2, 19, 24]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 4, .hexagon, .rotate 7, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 7, .yellow, .rotate 2, .yellow, .rotate 3, .yellow,
                .rotate 4, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [14]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon,
                .rotate 6, .hexagon, .rotate 6, .yellow, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 2,
                .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow,
                .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .yellow, .rotate 2,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 4, .hexagon, .rotate 2, .hexagon, .rotate 8, .yellow,
                .rotate 2, .yellow, .rotate 4, .hexagon, .rotate 6, .yellow, .rotate 2,
                .hexagon, .rotate 5, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := true
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 6, .hexagon, .rotate 5, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [28]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow,
                .rotate 4, .hexagon, .rotate 7, .hexagon, .rotate 7, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 6,
                .hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow,
                .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7, .yellow, .rotate 5, .yellow,
                .yellow, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 3, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1,
                .yellow, .rotate 5, .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [12, 13, 28]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 4, .hexagon,
                .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .rotate 5,
                .hexagon, .rotate 5, .yellow, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 7, .yellow, .rotate 5, .yellow, .rotate 5, .hexagon,
                .rotate 5, .yellow, .rotate 2, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [13]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 2,
                .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow,
                .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 5,
                .yellow, .yellow, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 2, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 3,
                .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [4, 5, 18, 23]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 5, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 5, .hexagon, .rotate 5, .yellow, .rotate 3,
                .yellow, .yellow, .yellow] }
    ]

/-- Published configuration programs `cf129` through `cf144`. -/
def classicalConfigurationChunk08 : Array Configuration := #[
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 5, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow,
                .rotate 5, .hexagon, .rotate 8, .yellow, .rotate 3, .hexagon, .rotate 7,
                .hexagon, .rotate 7, .yellow, .yellow, .yellow, .yellow, .rotate 3, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 4, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 5, .yellow, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 2, .hexagon,
                .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8, .hexagon, .rotate 8,
                .yellow, .yellow, .yellow, .rotate 3, .hexagon, .rotate 5, .yellow, .rotate 3,
                .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon,
                .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 2,
                .hexagon, .rotate 8, .yellow, .yellow, .yellow, .rotate 2, .yellow, .rotate 3,
                .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .hexagon,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 8,
                .yellow, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 5, .yellow,
                .rotate 1, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [19]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 9,
                .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 6, .yellow,
                .rotate 2, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [13]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow,
                .rotate 3, .hexagon, .rotate 7, .yellow, .rotate 2, .yellow, .rotate 2,
                .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow] },
      { symmetric := false
        contractReferences := [14]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 6, .yellow, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 6,
                .hexagon, .rotate 6, .yellow, .rotate 2, .yellow, .rotate 2, .yellow, .rotate 2,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [18, 19, 29]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 5, .hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 2, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [7]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 8,
                .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7, .yellow,
                .rotate 5, .yellow, .yellow, .rotate 3, .yellow, .rotate 2, .yellow, .rotate 2,
                .yellow] },
      { symmetric := false
        contractReferences := [12, 13, 29]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon,
                .rotate 8, .yellow, .rotate 3, .hexagon, .rotate 7, .yellow, .rotate 4, .yellow,
                .rotate 5, .hexagon, .rotate 5, .yellow, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow] },
      { symmetric := true
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon,
                .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 2, .yellow, .rotate 3, .yellow,
                .rotate 4, .yellow, .rotate 4, .hexagon, .rotate 4, .yellow, .rotate 2, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 7,
                .yellow, .rotate 5, .yellow, .rotate 2, .yellow, .rotate 2, .yellow, .rotate 2,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [17, 22, 23, 28]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 2, .yellow,
                .rotate 3, .yellow, .rotate 5, .yellow, .rotate 4, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [14]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon,
                .rotate 8, .yellow, .rotate 4, .hexagon, .rotate 7, .hexagon, .rotate 7,
                .yellow, .rotate 3, .yellow, .rotate 4, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow, .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf145` through `cf160`. -/
def classicalConfigurationChunk09 : Array Configuration := #[
      { symmetric := false
        contractReferences := [5, 19, 27, 29]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon,
                .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7, .yellow,
                .rotate 5, .yellow, .yellow, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon,
                .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 7, .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow,
                .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow, .yellow] },
      { symmetric := false
        contractReferences := [13]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 7,
                .yellow, .yellow, .yellow, .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 1,
                .yellow, .yellow] },
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 10, .yellow, .rotate 6, .hexagon, .rotate 6, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 2,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 3,
                .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 7,
                .yellow, .rotate 5, .hexagon, .rotate 6, .yellow, .rotate 3, .yellow, .yellow,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 7,
                .hexagon, .rotate 7, .yellow, .yellow, .yellow, .yellow, .rotate 3, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [4, 5, 22, 27]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 2, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 5,
                .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 6, .hexagon, .rotate 8, .yellow, .rotate 6, .yellow, .rotate 4,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 3, .hexagon,
                .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 5, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 11, .hexagon, .rotate 11, .hexagon, .rotate 11,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 8, .yellow, .rotate 5, .yellow,
                .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 5, .yellow, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 11, .hexagon, .rotate 11, .hexagon, .rotate 11,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon,
                .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 8,
                .yellow, .rotate 5, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 5, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 7, .hexagon, .rotate 7,
                .hexagon, .rotate 7, .yellow, .yellow, .rotate 1, .yellow, .rotate 3, .yellow,
                .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 5, .hexagon,
                .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 7, .yellow, .rotate 3,
                .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [1, 2, 32]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 3, .hexagon, .rotate 8, .hexagon, .rotate 8, .yellow, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8,
                .hexagon, .rotate 8, .yellow, .yellow, .yellow, .rotate 3, .hexagon, .rotate 5,
                .yellow, .rotate 3, .yellow, .yellow, .yellow] }
    ]

/-- Published configuration programs `cf161` through `cf176`. -/
def classicalConfigurationChunk10 : Array Configuration := #[
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 8,
                .hexagon, .rotate 8, .yellow, .yellow, .yellow, .rotate 3, .hexagon, .rotate 5,
                .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon,
                .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 2, .hexagon, .rotate 9,
                .yellow, .rotate 2, .hexagon, .rotate 8, .yellow, .yellow, .yellow, .rotate 2,
                .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 4, .hexagon,
                .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 2, .hexagon, .rotate 8, .yellow, .yellow, .yellow, .rotate 2,
                .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 2, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 8,
                .yellow, .rotate 4, .hexagon, .rotate 7, .yellow, .yellow, .rotate 1, .yellow,
                .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [11, 12, 18, 19]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 8,
                .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 6, .hexagon, .rotate 6,
                .yellow, .rotate 5, .yellow, .rotate 4, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 5, .yellow, .rotate 4, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 4, .yellow, .rotate 1, .yellow, .rotate 3, .yellow,
                .yellow] },
      { symmetric := true
        contractReferences := [11, 12, 18, 19]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 9,
                .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .hexagon,
                .rotate 6, .yellow, .rotate 4, .yellow, .rotate 1, .yellow, .rotate 3, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [38]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 5, .hexagon,
                .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 2,
                .hexagon, .rotate 9, .yellow, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow,
                .rotate 2, .yellow, .rotate 4, .yellow, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 4, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 4, .hexagon, .rotate 10, .hexagon,
                .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 6,
                .hexagon, .rotate 6, .yellow, .rotate 3, .yellow, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 2, .hexagon,
                .rotate 10, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 7, .hexagon, .rotate 7, .yellow,
                .rotate 3, .hexagon, .rotate 6, .yellow, .yellow, .rotate 3, .yellow, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1, .hexagon,
                .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 9,
                .hexagon, .rotate 9, .yellow, .yellow, .rotate 1, .yellow, .yellow, .yellow,
                .rotate 4, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 9, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 8,
                .hexagon, .rotate 8, .hexagon, .rotate 8, .yellow, .yellow, .yellow, .yellow,
                .rotate 4, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [20]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2,
                .hexagon, .rotate 6, .yellow, .rotate 2, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [20]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 6, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2,
                .hexagon, .rotate 6, .yellow, .rotate 2, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf177` through `cf192`. -/
def classicalConfigurationChunk11 : Array Configuration := #[
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11,
                .yellow, .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 5,
                .hexagon, .rotate 5, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 7, .yellow, .rotate 6, .yellow, .rotate 4,
                .yellow, .yellow, .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 11, .hexagon, .rotate 11, .hexagon, .rotate 11,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7, .yellow,
                .rotate 6, .hexagon, .rotate 6, .yellow, .rotate 3, .yellow, .rotate 3, .yellow,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [7]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 9,
                .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 8, .hexagon,
                .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .rotate 4, .yellow,
                .rotate 2, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [7, 29, 32]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 4,
                .yellow, .rotate 3, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 7, .yellow, .yellow, .rotate 3, .yellow,
                .rotate 3, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [16, 32]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 4, .yellow, .rotate 3, .hexagon, .rotate 6, .yellow, .rotate 2,
                .yellow, .rotate 3, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon,
                .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 2,
                .yellow, .rotate 3, .yellow, .rotate 6, .yellow, .rotate 3, .hexagon, .rotate 1,
                .yellow, .rotate 4, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [8, 31, 33]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 4, .hexagon, .rotate 8,
                .hexagon, .rotate 8, .yellow, .rotate 3, .yellow, .rotate 4, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [14]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon,
                .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 3,
                .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 6, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [25, 30, 33]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow,
                .rotate 5, .hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 5, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 2, .hexagon, .rotate 8,
                .yellow, .rotate 7, .hexagon, .rotate 7, .yellow, .rotate 2, .yellow, .rotate 2,
                .yellow, .rotate 3, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8,
                .yellow, .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 6, .yellow, .rotate 5,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon,
                .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 2,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 5, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 7, .yellow, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 2, .yellow, .rotate 2, .yellow] }
    ]

/-- Published configuration programs `cf193` through `cf208`. -/
def classicalConfigurationChunk12 : Array Configuration := #[
      { symmetric := false
        contractReferences := [18, 21, 30, 33]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 8, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 2, .yellow, .rotate 4, .yellow, .yellow, .rotate 4, .yellow,
                .rotate 3, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6, 10, 19, 33]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 12, .hexagon, .rotate 12, .hexagon, .rotate 12,
                .yellow, .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .yellow, .rotate 5, .yellow, .rotate 1, .yellow, .rotate 3,
                .yellow, .rotate 3, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [18]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon,
                .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 5, .yellow, .rotate 1, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 12, .hexagon, .rotate 12, .hexagon, .rotate 12,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9,
                .yellow, .rotate 8, .yellow, .rotate 5, .yellow, .rotate 1, .yellow, .rotate 3,
                .yellow, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [24]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon,
                .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 2, .yellow, .rotate 6,
                .hexagon, .rotate 7, .hexagon, .rotate 7, .yellow, .yellow, .rotate 1, .yellow,
                .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon,
                .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 2, .yellow, .rotate 5,
                .hexagon, .rotate 7, .yellow, .rotate 4, .yellow, .rotate 3, .yellow, .rotate 2,
                .hexagon, .rotate 4, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [21, 24, 30, 33]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 6, .hexagon,
                .rotate 6, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 4, .yellow, .rotate 4, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 3, .hexagon,
                .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .yellow, .rotate 5, .yellow, .rotate 1, .yellow, .yellow,
                .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [1, 2, 32]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon,
                .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 5, .yellow, .rotate 4, .yellow, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [10]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon,
                .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 2,
                .hexagon, .rotate 6, .yellow, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [12, 13, 19, 20]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow,
                .rotate 3, .hexagon, .rotate 10, .yellow, .yellow, .rotate 3, .hexagon,
                .rotate 8, .hexagon, .rotate 8, .yellow, .yellow, .yellow, .rotate 3, .hexagon,
                .rotate 5, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 7, .hexagon, .rotate 3, .hexagon,
                .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 7, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 7, .yellow, .rotate 6, .yellow, .rotate 5,
                .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 9,
                .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 9, .hexagon, .rotate 9,
                .yellow, .rotate 7, .yellow, .rotate 7, .yellow, .rotate 6, .hexagon, .rotate 6,
                .yellow, .yellow, .rotate 3, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 7,
                .yellow, .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 4, .yellow, .rotate 1, .yellow, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [18, 19, 25, 26]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 10,
                .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon,
                .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 5, .yellow, .rotate 4, .yellow, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 12, .hexagon, .rotate 12, .hexagon, .rotate 12,
                .yellow, .rotate 10, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 9,
                .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 6,
                .yellow, .rotate 4, .yellow, .rotate 3, .yellow, .rotate 2, .yellow, .rotate 1,
                .yellow] }
    ]

/-- Published configuration programs `cf209` through `cf224`. -/
def classicalConfigurationChunk13 : Array Configuration := #[
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 12, .hexagon, .rotate 12, .hexagon, .rotate 12,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 9, .yellow, .rotate 6, .yellow,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 6, .hexagon, .rotate 6,
                .yellow, .yellow, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 8,
                .hexagon, .rotate 8, .hexagon, .rotate 8, .yellow, .yellow, .rotate 1, .yellow,
                .rotate 4, .yellow, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 3,
                .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 5, .yellow,
                .rotate 2, .hexagon, .rotate 7, .yellow, .yellow, .yellow, .rotate 2, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 5, .hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11, .yellow,
                .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow,
                .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 8, .hexagon, .rotate 8, .yellow, .yellow,
                .yellow, .rotate 3, .hexagon, .rotate 5, .yellow, .rotate 3, .yellow, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [37]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 8, .hexagon, .rotate 8, .yellow, .yellow,
                .yellow, .yellow, .rotate 4, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 4, .hexagon, .rotate 2,
                .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon,
                .rotate 11, .yellow, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow,
                .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [8, 9, 15, 16]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 2,
                .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11, .yellow,
                .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 9, .hexagon,
                .rotate 9, .yellow, .yellow, .yellow, .rotate 5, .hexagon, .rotate 6, .hexagon,
                .rotate 6, .yellow, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [8, 9, 15, 16]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 11,
                .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .hexagon,
                .rotate 7, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 4, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 7, .yellow, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 5,
                .yellow, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [28]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 7, .yellow,
                .rotate 3, .yellow, .rotate 4, .yellow, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 3, .hexagon, .rotate 8,
                .hexagon, .rotate 8, .yellow, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 5, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .yellow, .rotate 2,
                .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 12, .yellow, .rotate 4, .hexagon, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 3,
                .hexagon, .rotate 9, .yellow, .rotate 2, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 5, .yellow, .rotate 3, .yellow, .rotate 1, .yellow,
                .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 5, .hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 4,
                .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 3, .yellow,
                .rotate 6, .yellow, .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [37]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 11,
                .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 8, .yellow, .rotate 2, .yellow, .rotate 5,
                .hexagon, .rotate 6, .yellow, .rotate 2, .yellow, .rotate 4, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 8, .hexagon, .rotate 8, .yellow, .rotate 3, .hexagon,
                .rotate 7, .yellow, .rotate 2, .yellow, .rotate 4, .yellow, .yellow, .rotate 3,
                .yellow, .yellow] }
    ]

/-- Published configuration programs `cf225` through `cf240`. -/
def classicalConfigurationChunk14 : Array Configuration := #[
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon,
                .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3,
                .hexagon, .rotate 8, .yellow, .rotate 3, .hexagon, .rotate 6, .hexagon,
                .rotate 1, .yellow, .rotate 6, .yellow, .rotate 1, .yellow, .rotate 2, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [35, 37]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 2,
                .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 8, .yellow,
                .rotate 6, .yellow, .rotate 5, .yellow, .rotate 4, .yellow, .yellow, .rotate 2,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 2,
                .hexagon, .rotate 12, .yellow, .rotate 9, .hexagon, .rotate 2, .hexagon,
                .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 8, .yellow, .yellow,
                .yellow, .rotate 4, .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 11,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 2, .hexagon,
                .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 7, .yellow,
                .rotate 7, .yellow, .rotate 4, .yellow, .rotate 4, .yellow, .rotate 3, .yellow,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 13, .hexagon, .rotate 13, .yellow, .rotate 10,
                .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 3, .hexagon, .rotate 10,
                .hexagon, .rotate 10, .yellow, .rotate 9, .yellow, .rotate 7, .yellow,
                .rotate 3, .yellow, .rotate 4, .yellow, .rotate 3, .yellow, .rotate 1, .yellow,
                .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [7]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 13, .hexagon, .rotate 13, .hexagon, .rotate 13,
                .yellow, .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow,
                .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 9, .yellow, .rotate 6, .yellow, .rotate 1,
                .yellow, .rotate 4, .yellow, .rotate 3, .yellow, .yellow, .rotate 3, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [19]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 11, .hexagon, .rotate 1, .yellow,
                .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 10, .yellow, .rotate 2, .yellow, .rotate 4, .yellow, .yellow,
                .rotate 5, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [11, 33, 37]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 5, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon,
                .rotate 11, .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 6, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 13, .hexagon, .rotate 13, .yellow, .rotate 11,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 2, .hexagon,
                .rotate 11, .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10,
                .yellow, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 6, .yellow, .rotate 5,
                .yellow, .yellow, .rotate 4, .yellow, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 10, .hexagon, .rotate 2,
                .hexagon, .rotate 12, .yellow, .rotate 7, .hexagon, .rotate 4, .hexagon,
                .rotate 11, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 9, .yellow, .rotate 6, .yellow, .yellow,
                .rotate 5, .yellow, .rotate 3, .yellow, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 11,
                .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 9, .yellow, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow,
                .rotate 6, .hexagon, .rotate 6, .yellow, .yellow, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [10]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 5,
                .hexagon, .rotate 1, .hexagon, .rotate 6, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 9,
                .hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow,
                .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 8, .yellow, .rotate 8, .hexagon,
                .rotate 8, .yellow, .yellow, .rotate 5, .yellow, .rotate 4, .yellow, .yellow,
                .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [43]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 11,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 4, .hexagon,
                .rotate 11, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 10, .yellow, .rotate 2, .hexagon, .rotate 9, .yellow, .yellow,
                .yellow, .rotate 3, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 11, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow,
                .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 5,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 4, .yellow, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [38]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8,
                .hexagon, .rotate 8, .hexagon, .rotate 8, .hexagon, .rotate 8, .yellow,
                .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 5, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .yellow] }
    ]

/-- Published configuration programs `cf241` through `cf256`. -/
def classicalConfigurationChunk15 : Array Configuration := #[
      { symmetric := false
        contractReferences := [37]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 6,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 8, .hexagon,
                .rotate 8, .yellow, .yellow, .yellow, .rotate 2, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [14]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon,
                .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .hexagon, .rotate 5, .yellow, .rotate 4, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 7,
                .hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow,
                .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 8,
                .yellow, .rotate 6, .yellow, .yellow, .rotate 2, .yellow, .rotate 3, .yellow,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 7,
                .hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow,
                .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 8,
                .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 6, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 6,
                .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow,
                .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [1, 2, 30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 8, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 7, .hexagon,
                .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 8, .yellow, .rotate 4,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow,
                .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .yellow, .rotate 3,
                .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 5, .yellow, .rotate 1, .yellow, .yellow, .yellow, .rotate 3,
                .yellow, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 6, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 8,
                .yellow, .yellow, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 5, .hexagon,
                .rotate 5, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [20]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon,
                .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 2, .yellow,
                .rotate 4, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [18]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow,
                .rotate 3, .hexagon, .rotate 1, .yellow, .hexagon, .rotate 4, .yellow, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [18]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 7, .hexagon, .rotate 7, .yellow, .rotate 3, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 9,
                .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .rotate 5, .yellow,
                .rotate 4, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [11, 12, 33]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 8,
                .hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 7, .yellow, .yellow, .rotate 2, .yellow,
                .rotate 3, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 7, .yellow, .yellow, .yellow, .rotate 2,
                .yellow, .rotate 2, .yellow, .rotate 2, .yellow] }
    ]

/-- Published configuration programs `cf257` through `cf272`. -/
def classicalConfigurationChunk16 : Array Configuration := #[
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 6, .yellow, .rotate 3, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [24]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon,
                .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7, .yellow,
                .rotate 5, .yellow, .rotate 5, .hexagon, .rotate 5, .yellow, .rotate 2, .yellow,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [4, 5, 22, 29]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 4, .hexagon, .rotate 8,
                .hexagon, .rotate 8, .yellow, .rotate 3, .yellow, .rotate 5, .yellow, .rotate 1,
                .yellow, .rotate 3, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8,
                .yellow, .rotate 6, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 1,
                .yellow, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [15, 16, 33]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 4, .yellow, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow,
                .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 2,
                .yellow, .rotate 4, .yellow, .yellow, .rotate 4, .yellow, .rotate 4, .hexagon,
                .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [21, 26, 33]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow,
                .rotate 5, .hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 4, .yellow, .yellow, .rotate 4, .yellow,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [5, 30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon,
                .rotate 9, .yellow, .rotate 5, .hexagon, .rotate 8, .hexagon, .rotate 8,
                .hexagon, .rotate 8, .yellow, .rotate 4, .yellow, .yellow, .rotate 4, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [14, 29, 31]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 12, .hexagon, .rotate 12, .hexagon, .rotate 12,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .yellow, .rotate 5, .yellow, .rotate 1, .yellow, .yellow,
                .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [1, 2, 32]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon,
                .rotate 9, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 4, .yellow,
                .rotate 3, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12,
                .yellow, .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 7, .yellow, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 5, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon,
                .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 5,
                .hexagon, .rotate 5, .yellow, .rotate 2, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow,
                .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 5,
                .hexagon, .rotate 7, .hexagon, .rotate 7, .hexagon, .rotate 7, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 9,
                .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .yellow, .yellow, .rotate 4, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [18, 19, 33]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 3, .hexagon,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 8,
                .yellow, .rotate 2, .hexagon, .rotate 7, .yellow, .yellow, .yellow, .rotate 2,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow] }
    ]

/-- Published configuration programs `cf273` through `cf288`. -/
def classicalConfigurationChunk17 : Array Configuration := #[
      { symmetric := false
        contractReferences := [8]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 6, .hexagon,
                .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 4, .yellow, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 4, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 4, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow,
                .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon,
                .rotate 10, .yellow, .rotate 9, .yellow, .rotate 5, .hexagon, .rotate 8,
                .yellow, .yellow, .yellow, .rotate 3, .hexagon, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 6, .hexagon,
                .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 8, .yellow, .rotate 4,
                .hexagon, .rotate 7, .hexagon, .rotate 7, .hexagon, .rotate 7, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 7, .hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 10,
                .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .yellow, .rotate 4, .yellow,
                .yellow, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 5, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow,
                .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 10,
                .yellow, .rotate 3, .yellow, .yellow, .yellow, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 5, .hexagon, .rotate 5, .yellow, .rotate 3, .yellow, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [40]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 11, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon,
                .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 2, .hexagon, .rotate 10,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2,
                .hexagon, .rotate 7, .yellow, .rotate 2, .yellow, .yellow, .rotate 3, .yellow,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [39]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 2,
                .hexagon, .rotate 12, .yellow, .rotate 4, .hexagon, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 4, .yellow,
                .rotate 1, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [27, 30, 33]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 7, .yellow,
                .rotate 6, .yellow, .rotate 4, .yellow, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [21]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 4, .hexagon, .rotate 11,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11, .yellow,
                .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 2, .hexagon,
                .rotate 7, .yellow, .rotate 5, .yellow, .rotate 5, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [7]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 13, .hexagon, .rotate 13, .yellow, .rotate 10,
                .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 9, .hexagon,
                .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 8, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 9, .yellow, .rotate 7, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 2, .yellow, .rotate 2, .yellow, .rotate 3, .yellow,
                .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 3, .hexagon, .rotate 13, .hexagon, .rotate 13,
                .yellow, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 7, .yellow, .yellow,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow] },
      { symmetric := false
        contractReferences := [21]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 4, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 4, .hexagon, .rotate 8,
                .hexagon, .rotate 8, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 5,
                .hexagon, .rotate 5, .yellow, .rotate 2, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 3, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 7, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .yellow, .yellow,
                .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [28, 33, 37]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 3,
                .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 7, .yellow, .yellow,
                .yellow, .rotate 3, .yellow, .rotate 2, .yellow, .rotate 2, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [6, 12, 32, 34]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 13, .hexagon, .rotate 13, .yellow, .rotate 11,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 3, .hexagon,
                .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 8, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 9, .yellow, .rotate 7, .yellow, .yellow,
                .yellow, .rotate 3, .yellow, .rotate 2, .yellow, .yellow, .rotate 2, .yellow] }
    ]

/-- Published configuration programs `cf289` through `cf304`. -/
def classicalConfigurationChunk18 : Array Configuration := #[
      { symmetric := false
        contractReferences := [37]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9,
                .yellow, .rotate 8, .hexagon, .rotate 8, .hexagon, .rotate 8, .yellow,
                .rotate 3, .yellow, .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 11,
                .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 8, .yellow, .rotate 7, .hexagon,
                .rotate 7, .yellow, .rotate 2, .yellow, .yellow, .rotate 3, .yellow, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon,
                .rotate 11, .yellow, .rotate 5, .hexagon, .rotate 8, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 2,
                .yellow, .rotate 4, .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [18, 19, 37]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 13, .hexagon, .rotate 13, .yellow, .rotate 10,
                .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon,
                .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 9, .yellow, .rotate 7, .yellow, .rotate 6, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow,
                .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11, .yellow,
                .rotate 4, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 2,
                .yellow, .rotate 3, .yellow, .rotate 4, .hexagon, .rotate 7, .hexagon,
                .rotate 7, .yellow, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [28, 34, 36]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 10,
                .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .yellow,
                .rotate 5, .yellow, .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon,
                .rotate 11, .yellow, .rotate 5, .hexagon, .rotate 8, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 4, .yellow, .yellow,
                .rotate 5, .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 4, .hexagon,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 6, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 3, .yellow,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [8, 9, 30, 37]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 7, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [26, 33, 35]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 5, .hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 2,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 6, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .yellow, .rotate 3, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [13, 31, 37]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 5, .yellow, .rotate 2, .hexagon, .rotate 7, .yellow, .yellow,
                .yellow, .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 4, .hexagon, .rotate 11,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon,
                .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 2,
                .hexagon, .rotate 1, .yellow, .rotate 7, .yellow, .rotate 7, .hexagon,
                .rotate 7, .yellow, .rotate 3, .yellow, .yellow, .yellow, .rotate 3, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [17]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 4,
                .hexagon, .rotate 12, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow,
                .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 9, .yellow, .rotate 4, .yellow, .yellow,
                .rotate 4, .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [18, 19, 37]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 5, .hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 3,
                .hexagon, .rotate 9, .yellow, .rotate 2, .hexagon, .rotate 8, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .yellow, .rotate 1,
                .yellow] },
      { symmetric := true
        contractReferences := [24, 29, 37]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 7, .hexagon,
                .rotate 6, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 4, .yellow, .rotate 1,
                .yellow, .rotate 4, .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon,
                .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 9,
                .yellow, .rotate 2, .yellow, .yellow, .rotate 4, .yellow, .rotate 1, .hexagon,
                .rotate 5, .yellow, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .yellow] }
    ]

/-- Published configuration programs `cf305` through `cf320`. -/
def classicalConfigurationChunk19 : Array Configuration := #[
      { symmetric := false
        contractReferences := [37]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 5, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow,
                .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 3,
                .yellow, .rotate 5, .hexagon, .rotate 8, .hexagon, .rotate 8, .hexagon,
                .rotate 8, .yellow, .yellow, .rotate 1, .yellow, .rotate 4, .yellow, .yellow,
                .yellow, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 4,
                .hexagon, .rotate 12, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow,
                .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 6, .yellow, .yellow, .rotate 2, .hexagon, .rotate 7, .yellow,
                .yellow, .yellow, .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 4, .hexagon, .rotate 2,
                .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11, .yellow,
                .rotate 5, .hexagon, .rotate 10, .hexagon, .rotate 10, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 2, .yellow, .yellow,
                .yellow, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 5, .yellow, .rotate 3,
                .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [7]
        program :=
          [.hexagon, .rotate 5, .hexagon, .rotate 13, .hexagon, .rotate 13, .hexagon, .rotate 13,
                .hexagon, .rotate 13, .yellow, .rotate 11, .hexagon, .rotate 1, .yellow,
                .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 9, .yellow, .rotate 7, .hexagon,
                .rotate 8, .yellow, .yellow, .rotate 1, .yellow, .rotate 4, .yellow, .yellow,
                .yellow, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon,
                .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 2,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 8, .hexagon,
                .rotate 8, .yellow, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 3,
                .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [7]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 13, .hexagon, .rotate 13, .yellow, .rotate 9,
                .hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow,
                .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 9, .yellow, .rotate 6, .hexagon,
                .rotate 8, .yellow, .rotate 2, .yellow, .yellow, .rotate 4, .yellow, .yellow,
                .yellow, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon,
                .rotate 10, .yellow, .rotate 5, .hexagon, .rotate 7, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .hexagon, .rotate 8, .yellow, .rotate 3, .hexagon,
                .rotate 7, .yellow, .yellow, .rotate 3, .yellow, .rotate 3, .yellow, .yellow,
                .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 5, .hexagon,
                .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 2, .yellow, .rotate 5,
                .hexagon, .rotate 8, .yellow, .rotate 2, .hexagon, .rotate 1, .hexagon,
                .rotate 7, .hexagon, .rotate 7, .yellow, .yellow, .rotate 1, .yellow, .rotate 3,
                .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [42]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon,
                .rotate 10, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 5,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 7, .yellow, .yellow, .rotate 3,
                .yellow, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 5, .hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 4,
                .hexagon, .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 5, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [42]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 9, .hexagon, .rotate 9,
                .hexagon, .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 3, .hexagon, .rotate 8, .yellow, .yellow, .rotate 6, .yellow, .rotate 4,
                .yellow, .rotate 3, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 9, .yellow, .rotate 5,
                .hexagon, .rotate 8, .hexagon, .rotate 8, .hexagon, .rotate 8, .hexagon,
                .rotate 8, .yellow, .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 2, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [46]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 9, .hexagon,
                .rotate 9, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 2, .yellow, .rotate 4, .yellow, .yellow, .rotate 3, .yellow, .rotate 2,
                .yellow] },
      { symmetric := false
        contractReferences := [37]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 13, .hexagon, .rotate 13, .yellow, .rotate 10,
                .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 3, .hexagon, .rotate 10,
                .hexagon, .rotate 10, .yellow, .rotate 9, .yellow, .rotate 7, .yellow, .yellow,
                .rotate 6, .yellow, .rotate 4, .yellow, .rotate 1, .yellow, .rotate 2, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 8, .yellow, .rotate 6, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 2, .yellow, .rotate 2,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [14, 32, 34]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 13, .hexagon, .rotate 13, .hexagon, .rotate 13,
                .yellow, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 8, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 9, .yellow, .rotate 6, .yellow,
                .rotate 1, .yellow, .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow,
                .rotate 2, .yellow] }
    ]

/-- Published configuration programs `cf321` through `cf336`. -/
def classicalConfigurationChunk20 : Array Configuration := #[
      { symmetric := false
        contractReferences := [1, 2, 35]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 9,
                .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8,
                .hexagon, .rotate 8, .hexagon, .rotate 8, .hexagon, .rotate 8, .yellow,
                .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 3,
                .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 8, .yellow,
                .rotate 7, .hexagon, .rotate 7, .yellow, .rotate 2, .yellow, .yellow, .rotate 3,
                .yellow, .yellow, .yellow] },
      { symmetric := true
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 6, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 6, .hexagon, .rotate 6, .hexagon,
                .rotate 6, .yellow, .rotate 4, .yellow, .yellow, .yellow, .yellow] },
      { symmetric := true
        contractReferences := [21]
        program :=
          [.hexagon, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 7,
                .hexagon, .rotate 6, .hexagon, .rotate 2, .hexagon, .rotate 8, .yellow,
                .rotate 7, .hexagon, .rotate 7, .yellow, .yellow, .yellow, .yellow, .yellow,
                .yellow] },
      { symmetric := true
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 2, .hexagon, .rotate 4, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 8,
                .yellow, .rotate 5, .hexagon, .rotate 5, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := true
        contractReferences := [0, 23]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 8,
                .yellow, .rotate 4, .hexagon, .rotate 6, .hexagon, .rotate 1, .yellow,
                .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow,
                .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 7, .yellow, .rotate 4, .hexagon,
                .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [14, 15, 21, 26]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon,
                .rotate 8, .yellow, .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 4,
                .hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 2,
                .hexagon, .rotate 9, .yellow, .rotate 6, .hexagon, .rotate 1, .hexagon,
                .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [24]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 4, .hexagon,
                .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 4, .hexagon, .rotate 8, .hexagon,
                .rotate 8, .hexagon, .rotate 8, .yellow, .rotate 7, .yellow, .rotate 5, .yellow,
                .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [18]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 2,
                .hexagon, .rotate 9, .yellow, .rotate 6, .hexagon, .rotate 2, .hexagon,
                .rotate 8, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 5, .yellow,
                .yellow, .rotate 3, .yellow, .yellow, .rotate 2, .yellow] }
    ]

/-- Published configuration programs `cf337` through `cf352`. -/
def classicalConfigurationChunk21 : Array Configuration := #[
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 2, .hexagon, .rotate 8, .yellow,
                .rotate 6, .hexagon, .rotate 7, .yellow, .rotate 5, .yellow, .yellow, .rotate 4,
                .hexagon, .rotate 4, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 5, .hexagon, .rotate 3, .hexagon, .rotate 8, .hexagon,
                .rotate 8, .yellow, .rotate 7, .hexagon, .rotate 7, .yellow, .rotate 5, .yellow,
                .yellow, .rotate 2, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [12]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon,
                .rotate 8, .yellow, .rotate 2, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow,
                .rotate 5, .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 7, .yellow, .rotate 5, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow,
                .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 9, .yellow, .rotate 5, .hexagon, .rotate 6, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [12, 13, 28]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon,
                .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 5, .yellow, .rotate 4,
                .hexagon, .rotate 5, .yellow, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := true
        contractReferences := [1, 2, 8, 9]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 4, .hexagon, .rotate 7, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 7, .yellow, .rotate 4, .hexagon,
                .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon,
                .rotate 9, .yellow, .rotate 4, .hexagon, .rotate 8, .yellow, .yellow, .yellow,
                .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [28]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 4, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [4, 5, 24, 29]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 3, .hexagon, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 8,
                .yellow, .yellow, .yellow, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [24]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8,
                .hexagon, .rotate 6, .hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon,
                .rotate 9, .yellow, .rotate 8, .hexagon, .rotate 8, .yellow, .yellow, .yellow,
                .yellow, .rotate 4, .hexagon, .rotate 4, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [18]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 6,
                .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 8, .yellow, .yellow, .yellow, .rotate 4, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 1, .hexagon,
                .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 2,
                .hexagon, .rotate 8, .yellow, .rotate 2, .yellow, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [21]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 9, .hexagon,
                .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 7, .yellow, .rotate 1, .yellow, .yellow, .rotate 4, .hexagon,
                .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf353` through `cf368`. -/
def classicalConfigurationChunk22 : Array Configuration := #[
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .hexagon,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 5, .yellow, .rotate 4,
                .hexagon, .rotate 4, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [11]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 6, .hexagon, .rotate 1, .hexagon,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 6, .yellow, .rotate 5,
                .yellow, .rotate 3, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .hexagon,
                .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon,
                .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7, .yellow,
                .rotate 5, .yellow, .yellow, .yellow, .rotate 2, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [12, 13, 29]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon,
                .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 6, .hexagon, .rotate 1,
                .yellow, .rotate 5, .yellow, .rotate 3, .yellow, .yellow, .rotate 3, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [16, 17, 28]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 7, .yellow, .rotate 5, .yellow,
                .rotate 4, .hexagon, .rotate 5, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [19]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon,
                .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 7, .hexagon, .rotate 7,
                .yellow, .rotate 5, .yellow, .rotate 2, .yellow, .rotate 2, .yellow, .rotate 2,
                .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 8, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 6,
                .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow,
                .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 4,
                .hexagon, .rotate 10, .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [28]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 7, .hexagon, .rotate 8, .hexagon, .rotate 8, .yellow, .rotate 6,
                .yellow, .yellow, .rotate 5, .hexagon, .rotate 5, .yellow, .yellow, .rotate 2,
                .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 4, .hexagon, .rotate 8, .hexagon,
                .rotate 8, .hexagon, .rotate 8, .yellow, .rotate 7, .yellow, .rotate 5, .yellow,
                .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon,
                .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 8, .yellow, .rotate 6, .yellow,
                .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .rotate 2,
                .yellow, .yellow] },
      { symmetric := false
        contractReferences := [21]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 6, .hexagon, .rotate 3, .hexagon,
                .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 8, .yellow, .rotate 5,
                .hexagon, .rotate 1, .yellow, .rotate 6, .yellow, .rotate 1, .yellow, .rotate 3,
                .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 4, .hexagon,
                .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 8,
                .yellow, .rotate 6, .yellow, .yellow, .yellow, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 3,
                .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 7, .yellow, .yellow, .yellow, .yellow, .rotate 2, .yellow,
                .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 7, .yellow, .rotate 5, .yellow, .rotate 4, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1,
                .yellow] }
    ]

/-- Published configuration programs `cf369` through `cf384`. -/
def classicalConfigurationChunk23 : Array Configuration := #[
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 8, .yellow, .rotate 6, .yellow, .rotate 5, .hexagon, .rotate 1,
                .hexagon, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 2, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 6, .hexagon, .rotate 8, .yellow, .rotate 6, .yellow, .rotate 4,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [4, 5, 24, 29]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 6, .hexagon, .rotate 3, .hexagon,
                .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 8, .hexagon, .rotate 8,
                .yellow, .yellow, .yellow, .yellow, .rotate 4, .hexagon, .rotate 4, .yellow,
                .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [4, 5, 18, 23]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 8, .yellow, .yellow, .yellow, .rotate 4, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .hexagon, .rotate 4, .yellow, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon,
                .rotate 10, .yellow, .rotate 2, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 7, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 8,
                .hexagon, .rotate 8, .yellow, .rotate 2, .yellow, .yellow, .yellow, .rotate 4,
                .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [37]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 2, .hexagon,
                .rotate 6, .hexagon, .rotate 1, .hexagon, .rotate 2, .hexagon, .rotate 9,
                .yellow, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [21]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 8, .hexagon,
                .rotate 3, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .hexagon,
                .rotate 8, .yellow, .yellow, .rotate 1, .yellow, .yellow, .rotate 4, .hexagon,
                .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 8, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8,
                .yellow, .rotate 6, .yellow, .yellow, .rotate 5, .hexagon, .rotate 5, .yellow,
                .rotate 2, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [18]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon,
                .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 6, .yellow, .yellow, .rotate 3, .yellow,
                .rotate 3, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon,
                .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [30, 33]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon,
                .rotate 10, .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 6, .hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 9,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 6, .hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 9,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .rotate 6, .yellow, .rotate 4,
                .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [14]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 5,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .hexagon, .rotate 5, .yellow,
                .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 4,
                .hexagon, .rotate 11, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 2, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf385` through `cf400`. -/
def classicalConfigurationChunk24 : Array Configuration := #[
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 4,
                .hexagon, .rotate 11, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 7, .yellow, .yellow, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 3,
                .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 8, .hexagon,
                .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 8, .yellow, .yellow, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 7, .hexagon, .rotate 3,
                .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 6, .hexagon,
                .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 8,
                .yellow, .rotate 6, .hexagon, .rotate 7, .yellow, .yellow, .rotate 1, .yellow,
                .rotate 3, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 5, .hexagon, .rotate 9, .hexagon,
                .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 8,
                .yellow, .rotate 5, .hexagon, .rotate 7, .yellow, .rotate 2, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [18]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 5, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow,
                .rotate 2, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 4, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .hexagon,
                .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .hexagon,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 8,
                .yellow, .yellow, .yellow, .rotate 4, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 6, .hexagon, .rotate 9, .hexagon,
                .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 7,
                .hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow,
                .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 9,
                .hexagon, .rotate 9, .yellow, .yellow, .rotate 1, .yellow, .yellow, .yellow,
                .rotate 4, .hexagon, .rotate 4, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [21]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .yellow,
                .rotate 1, .yellow, .yellow, .rotate 4, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [16, 17, 32]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .rotate 5, .hexagon, .rotate 6,
                .yellow, .rotate 3, .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 5, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon,
                .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 2,
                .hexagon, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow, .rotate 5,
                .hexagon, .rotate 5, .yellow, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [18]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .hexagon,
                .rotate 5, .yellow, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 6,
                .hexagon, .rotate 1, .hexagon, .rotate 7, .hexagon, .rotate 7, .yellow, .yellow,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 2,
                .hexagon, .rotate 12, .yellow, .rotate 9, .hexagon, .rotate 2, .hexagon,
                .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 6, .yellow, .yellow, .rotate 2, .hexagon,
                .rotate 1, .yellow, .rotate 4, .yellow, .rotate 3, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [18]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 9, .hexagon, .rotate 2, .hexagon,
                .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .yellow, .rotate 3, .yellow, .rotate 3, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 9, .yellow, .rotate 2,
                .hexagon, .rotate 8, .yellow, .yellow, .yellow, .rotate 4, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1,
                .yellow] }
    ]

/-- Published configuration programs `cf401` through `cf416`. -/
def classicalConfigurationChunk25 : Array Configuration := #[
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 9, .hexagon, .rotate 3,
                .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 3, .hexagon, .rotate 10,
                .hexagon, .rotate 10, .yellow, .rotate 9, .yellow, .rotate 7, .hexagon,
                .rotate 8, .yellow, .rotate 4, .yellow, .rotate 4, .yellow, .yellow, .rotate 1,
                .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 5, .hexagon, .rotate 7,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon,
                .rotate 8, .yellow, .rotate 3, .hexagon, .rotate 7, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 4, .hexagon, .rotate 2, .hexagon, .rotate 8, .yellow,
                .rotate 2, .yellow, .rotate 4, .hexagon, .rotate 6, .yellow, .rotate 2,
                .hexagon, .rotate 5, .yellow, .rotate 2, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [0, 23]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 4, .hexagon, .rotate 7, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 7, .yellow, .rotate 5, .yellow, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 8, .yellow, .rotate 5, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [21]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11,
                .yellow, .rotate 7, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 9, .hexagon, .rotate 9, .yellow, .yellow, .yellow, .yellow, .rotate 4,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [18]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 6,
                .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 9, .yellow, .yellow, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow,
                .rotate 4, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 10, .yellow, .rotate 5, .hexagon, .rotate 9, .hexagon,
                .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 2, .hexagon, .rotate 8,
                .yellow, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 2, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [1, 2, 28]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 5, .hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 2, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 3, .hexagon, .rotate 7,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [28]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon,
                .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 2, .yellow, .rotate 3, .yellow,
                .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .rotate 1, .yellow,
                .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 6, .hexagon, .rotate 7,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 5, .hexagon, .rotate 8,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon,
                .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 4, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 4, .yellow,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 8, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 6,
                .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 5, .hexagon, .rotate 9, .hexagon,
                .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 8,
                .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf417` through `cf432`. -/
def classicalConfigurationChunk26 : Array Configuration := #[
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 6,
                .hexagon, .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 10, .hexagon,
                .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8,
                .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 2, .yellow, .rotate 2,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 3, .yellow, .yellow,
                .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 4, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 7,
                .yellow, .rotate 2, .hexagon, .rotate 6, .yellow, .rotate 3, .yellow, .yellow,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon,
                .rotate 9, .yellow, .rotate 6, .hexagon, .rotate 2, .hexagon, .rotate 8,
                .yellow, .rotate 6, .yellow, .yellow, .rotate 4, .yellow, .yellow, .yellow,
                .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 6, .hexagon, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .rotate 4,
                .hexagon, .rotate 5, .yellow, .rotate 2, .hexagon, .rotate 4, .yellow,
                .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 3,
                .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 7, .hexagon,
                .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 6, .yellow, .yellow, .rotate 3, .yellow, .yellow, .rotate 2,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 4, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow,
                .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 4, .hexagon, .rotate 7, .hexagon, .rotate 1, .yellow,
                .rotate 2, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 1,
                .yellow, .yellow] },
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow,
                .rotate 4, .hexagon, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 4, .yellow, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 5, .hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 5, .yellow,
                .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [28]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 4, .hexagon, .rotate 2, .hexagon, .rotate 8, .yellow,
                .rotate 2, .yellow, .rotate 5, .hexagon, .rotate 6, .hexagon, .rotate 6,
                .yellow, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow,
                .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [19]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 4,
                .hexagon, .rotate 7, .yellow, .rotate 2, .yellow, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 3, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 7,
                .yellow, .rotate 2, .yellow, .yellow, .rotate 2, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 8, .yellow, .rotate 6, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow,
                .rotate 4, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 5, .hexagon, .rotate 8,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon,
                .rotate 9, .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon, .rotate 8,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 7, .hexagon, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 6,
                .yellow, .rotate 4, .hexagon, .rotate 6, .yellow, .yellow, .rotate 1, .yellow,
                .rotate 2, .yellow, .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf433` through `cf448`. -/
def classicalConfigurationChunk27 : Array Configuration := #[
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon,
                .rotate 8, .yellow, .rotate 3, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow,
                .rotate 4, .hexagon, .rotate 1, .yellow, .hexagon, .rotate 4, .yellow, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [1, 2, 9, 22]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 4, .hexagon,
                .rotate 2, .hexagon, .rotate 8, .yellow, .rotate 3, .yellow, .rotate 3,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [11, 12, 30]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 3, .yellow,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [22]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 8,
                .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 9, .yellow, .yellow, .yellow,
                .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [28]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 8, .hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon,
                .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 9,
                .hexagon, .rotate 9, .yellow, .yellow, .yellow, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon,
                .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 9, .yellow, .yellow, .yellow,
                .yellow, .rotate 4, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 11, .yellow, .rotate 5, .hexagon, .rotate 2, .hexagon,
                .rotate 10, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 2,
                .hexagon, .rotate 8, .yellow, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow,
                .rotate 2, .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [12, 28, 32, 35]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 5, .yellow, .rotate 2, .yellow, .rotate 2, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .hexagon, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1,
                .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 5, .hexagon, .rotate 8,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon,
                .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 2,
                .hexagon, .rotate 8, .yellow, .yellow, .yellow, .rotate 2, .yellow, .rotate 2,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 6, .hexagon, .rotate 9, .hexagon, .rotate 2, .hexagon,
                .rotate 9, .yellow, .rotate 2, .hexagon, .rotate 8, .yellow, .yellow, .rotate 5,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 2, .yellow,
                .rotate 4, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 6, .hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 4, .hexagon, .rotate 10, .hexagon,
                .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [8]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 5,
                .hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 3, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [8, 9, 30, 32]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon,
                .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 6, .yellow, .yellow, .rotate 4, .yellow,
                .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 8, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8,
                .yellow, .rotate 6, .yellow, .yellow, .rotate 3, .yellow, .rotate 2, .hexagon,
                .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf449` through `cf464`. -/
def classicalConfigurationChunk28 : Array Configuration := #[
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 5, .hexagon, .rotate 8, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon,
                .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8,
                .hexagon, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .rotate 2, .yellow,
                .rotate 2, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 4, .hexagon, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 2,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 1,
                .yellow, .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [0, 27]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 4, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow,
                .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 3, .hexagon, .rotate 7,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 4,
                .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 2, .hexagon, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [15, 30, 33]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 5, .hexagon, .rotate 8, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3,
                .hexagon, .rotate 8, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8,
                .yellow, .rotate 4, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8, .yellow, .rotate 6, .yellow,
                .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 9,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 11, .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 2,
                .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 4, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 11, .yellow, .rotate 5, .hexagon, .rotate 8, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [16, 17, 32]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 8, .yellow, .rotate 6, .yellow,
                .rotate 4, .hexagon, .rotate 6, .yellow, .rotate 2, .hexagon, .rotate 5,
                .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 4, .hexagon, .rotate 8,
                .hexagon, .rotate 8, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [16, 17, 32]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 7, .hexagon, .rotate 7,
                .yellow, .rotate 5, .yellow, .rotate 4, .hexagon, .rotate 5, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [12, 13, 32]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 2, .hexagon, .rotate 7,
                .yellow, .rotate 5, .yellow, .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 1,
                .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [1, 2, 32]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 2,
                .yellow, .rotate 3, .yellow, .rotate 3, .hexagon, .rotate 6, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf465` through `cf480`. -/
def classicalConfigurationChunk29 : Array Configuration := #[
      { symmetric := false
        contractReferences := [26]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 5, .hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 2, .yellow,
                .rotate 3, .yellow, .rotate 2, .hexagon, .rotate 5, .yellow, .rotate 2, .yellow,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 4, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow,
                .rotate 4, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 8, .yellow, .rotate 3, .yellow, .rotate 5, .yellow, .rotate 1,
                .yellow, .rotate 3, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 8,
                .yellow, .rotate 6, .yellow, .rotate 4, .hexagon, .rotate 6, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon,
                .rotate 9, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow,
                .rotate 4, .hexagon, .rotate 6, .hexagon, .rotate 6, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [1, 2, 13, 23]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon,
                .rotate 9, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow,
                .rotate 3, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1,
                .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [11, 12, 33]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 9,
                .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 5, .yellow, .rotate 1, .yellow, .rotate 3,
                .yellow, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [19, 20, 33]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 1,
                .yellow, .rotate 4, .yellow, .yellow, .rotate 3, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 5, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon,
                .rotate 10, .yellow, .rotate 2, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 6, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 3, .yellow, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [18]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 8, .hexagon, .rotate 8,
                .hexagon, .rotate 8, .hexagon, .rotate 8, .yellow, .yellow, .rotate 1, .yellow,
                .rotate 4, .yellow, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [21]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 6, .hexagon, .rotate 4, .hexagon,
                .rotate 10, .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 9,
                .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 7, .yellow, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [8, 33, 36]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 3, .yellow, .yellow,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 5, .hexagon,
                .rotate 10, .hexagon, .rotate 10, .hexagon, .rotate 10, .hexagon, .rotate 10,
                .yellow, .rotate 9, .yellow, .rotate 7, .yellow, .yellow, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [33, 36]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 7, .yellow, .rotate 4, .hexagon, .rotate 7, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [30, 32, 36]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 4, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow,
                .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 8,
                .yellow, .rotate 5, .hexagon, .rotate 7, .hexagon, .rotate 7, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [15, 16, 33]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 3, .hexagon,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 1,
                .yellow, .rotate 5, .hexagon, .rotate 8, .yellow, .yellow, .rotate 1, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [20, 24, 36]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 9, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 7, .hexagon,
                .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 9,
                .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .yellow] }
    ]

/-- Published configuration programs `cf481` through `cf496`. -/
def classicalConfigurationChunk30 : Array Configuration := #[
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow,
                .rotate 3, .yellow, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 8,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon,
                .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 2, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 6, .hexagon,
                .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 4, .yellow, .yellow, .rotate 5, .yellow,
                .rotate 1, .yellow, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon,
                .rotate 9, .yellow, .rotate 8, .yellow, .rotate 3, .yellow, .yellow, .rotate 3,
                .hexagon, .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11,
                .yellow, .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8, .yellow, .rotate 4,
                .hexagon, .rotate 7, .yellow, .yellow, .rotate 1, .yellow, .rotate 2, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 8,
                .hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 10, .yellow, .yellow, .yellow,
                .rotate 6, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 5,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 4, .hexagon, .rotate 13, .hexagon, .rotate 13,
                .hexagon, .rotate 13, .yellow, .rotate 11, .hexagon, .rotate 1, .yellow,
                .rotate 10, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 6, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [10, 11, 40]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 3, .hexagon, .rotate 13, .hexagon, .rotate 13,
                .yellow, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 6, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [8, 31, 35, 37]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 11,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 2, .hexagon,
                .rotate 11, .yellow, .rotate 8, .hexagon, .rotate 1, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 6, .yellow, .rotate 2, .yellow,
                .rotate 2, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [19]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 4, .hexagon, .rotate 2,
                .hexagon, .rotate 12, .yellow, .rotate 4, .hexagon, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 8,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 2, .hexagon, .rotate 7, .yellow, .rotate 2, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 8, .yellow, .rotate 4, .hexagon, .rotate 2, .hexagon, .rotate 7,
                .yellow, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 5, .yellow,
                .rotate 3, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon,
                .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 2,
                .hexagon, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 1, .yellow,
                .rotate 4, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [26, 27, 37]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 3, .hexagon, .rotate 13, .hexagon, .rotate 13,
                .yellow, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 8, .yellow, .yellow,
                .yellow, .rotate 4, .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [37]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 5, .hexagon,
                .rotate 8, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 9, .yellow, .rotate 2, .hexagon, .rotate 8, .yellow,
                .rotate 2, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2, .yellow,
                .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [37]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 3, .hexagon, .rotate 9,
                .hexagon, .rotate 9, .yellow, .rotate 8, .hexagon, .rotate 8, .yellow,
                .rotate 2, .yellow, .rotate 3, .yellow, .yellow, .rotate 3, .yellow, .yellow,
                .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon,
                .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 2,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 5, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf497` through `cf512`. -/
def classicalConfigurationChunk31 : Array Configuration := #[
      { symmetric := false
        contractReferences := [8]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 5,
                .hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 10, .yellow, .rotate 2, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 4, .yellow,
                .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [29, 34, 36]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11, .yellow,
                .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 6, .yellow, .rotate 5, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 5,
                .hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 4, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow, .rotate 6, .yellow, .rotate 3, .yellow, .rotate 3, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [34, 37]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 9,
                .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8, .yellow,
                .rotate 3, .yellow, .yellow, .yellow, .rotate 4, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon,
                .rotate 11, .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .yellow, .yellow,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 12, .yellow, .rotate 6, .hexagon, .rotate 8, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 10, .yellow, .rotate 2, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 13, .hexagon, .rotate 13, .yellow, .rotate 11,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 4, .hexagon,
                .rotate 11, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 9, .yellow, .rotate 7, .yellow, .yellow,
                .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11, .yellow,
                .rotate 3, .hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 3, .hexagon, .rotate 1,
                .yellow, .rotate 5, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [8]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon,
                .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 3, .hexagon, .rotate 7,
                .yellow, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 3, .yellow,
                .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 4, .hexagon, .rotate 11,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11, .yellow,
                .rotate 5, .hexagon, .rotate 8, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .yellow, .rotate 2,
                .yellow, .rotate 4, .yellow, .yellow, .rotate 3, .yellow, .rotate 3, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [37]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11, .yellow,
                .rotate 3, .hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 3, .hexagon, .rotate 7,
                .yellow, .rotate 4, .yellow, .rotate 1, .yellow, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon,
                .rotate 8, .yellow, .rotate 3, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow,
                .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 5, .yellow, .hexagon,
                .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 4, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [8, 9, 30, 37]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 10,
                .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10,
                .yellow, .rotate 9, .yellow, .rotate 4, .yellow, .yellow, .yellow, .rotate 3,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [21, 25, 37]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 7, .hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 10,
                .yellow, .rotate 9, .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 1,
                .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8, .yellow,
                .rotate 4, .hexagon, .rotate 7, .yellow, .yellow, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf513` through `cf528`. -/
def classicalConfigurationChunk32 : Array Configuration := #[
      { symmetric := false
        contractReferences := [37, 39]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 4, .hexagon, .rotate 11,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11, .yellow,
                .rotate 5, .hexagon, .rotate 8, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 8, .yellow, .yellow, .rotate 1, .yellow, .rotate 4, .yellow, .rotate 4,
                .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 5, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 8, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 9, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow,
                .rotate 7, .yellow, .rotate 1, .yellow, .rotate 4, .yellow, .yellow, .rotate 1,
                .yellow, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 6, .hexagon, .rotate 1,
                .hexagon, .rotate 8, .hexagon, .rotate 8, .yellow, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [37]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 8, .hexagon, .rotate 3, .hexagon,
                .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 2, .hexagon, .rotate 10,
                .yellow, .rotate 8, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 4, .hexagon,
                .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [37]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 2, .hexagon, .rotate 1, .hexagon, .rotate 10, .hexagon, .rotate 10,
                .yellow, .rotate 8, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 4, .hexagon,
                .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [25]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .hexagon,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 9,
                .yellow, .yellow, .yellow, .rotate 4, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .hexagon, .rotate 5, .yellow, .rotate 4, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 7, .hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 10, .yellow, .rotate 2, .yellow, .rotate 4, .hexagon,
                .rotate 1, .yellow, .rotate 7, .yellow, .rotate 1, .yellow, .rotate 3, .yellow,
                .rotate 4, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [1, 2, 31]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon,
                .rotate 10, .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [2, 31]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon,
                .rotate 10, .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .rotate 2, .yellow,
                .rotate 3, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon,
                .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8,
                .yellow, .rotate 3, .yellow, .rotate 3, .hexagon, .rotate 6, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .hexagon, .rotate 6, .yellow, .rotate 2, .yellow,
                .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [3, 36]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 11, .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 2, .hexagon, .rotate 8, .yellow, .yellow, .rotate 2, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 5, .hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 7, .yellow, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 6,
                .yellow, .rotate 2, .yellow, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 2,
                .hexagon, .rotate 9, .yellow, .rotate 6, .yellow, .rotate 1, .yellow, .yellow,
                .yellow, .rotate 4, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 4, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 5, .hexagon, .rotate 8, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 6, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 5, .yellow,
                .rotate 2, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 4, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 7,
                .hexagon, .rotate 7, .yellow, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 2, .yellow, .yellow, .yellow, .rotate 2, .yellow] }
    ]

/-- Published configuration programs `cf529` through `cf544`. -/
def classicalConfigurationChunk33 : Array Configuration := #[
      { symmetric := true
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 5, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon,
                .rotate 10, .yellow, .rotate 5, .hexagon, .rotate 9, .hexagon, .rotate 9,
                .hexagon, .rotate 9, .yellow, .rotate 4, .yellow, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .hexagon, .rotate 6, .yellow,
                .rotate 2, .yellow, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 13, .hexagon, .rotate 13, .yellow, .rotate 11,
                .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 9,
                .yellow, .rotate 7, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 6,
                .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [37]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 2,
                .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 6, .yellow,
                .rotate 1, .yellow, .yellow, .yellow, .rotate 4, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [12, 33, 37]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 2, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 6, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [13, 20, 30]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 13, .hexagon, .rotate 13, .hexagon, .rotate 13,
                .yellow, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 9, .yellow, .rotate 6, .yellow, .rotate 1, .yellow, .rotate 5,
                .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [7]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 13, .hexagon, .rotate 13, .yellow, .rotate 9,
                .hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow,
                .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 9, .yellow, .rotate 7, .yellow, .yellow,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 10,
                .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 8, .yellow, .yellow,
                .yellow, .yellow, .rotate 2, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 6, .hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon, .rotate 9,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .rotate 3, .yellow,
                .rotate 2, .hexagon, .rotate 4, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 5, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon,
                .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3,
                .hexagon, .rotate 8, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow, .rotate 3, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 5, .hexagon, .rotate 8, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 2,
                .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow, .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow,
                .rotate 5, .hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 3, .hexagon, .rotate 1,
                .yellow, .rotate 4, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow] },
      { symmetric := false
        contractReferences := [37]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 2,
                .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 7,
                .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 7, .yellow,
                .rotate 4, .yellow, .yellow, .yellow, .rotate 3, .yellow, .rotate 1, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 12, .yellow, .rotate 4, .hexagon, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 4,
                .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 3, .yellow,
                .rotate 2, .yellow, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 7, .yellow, .rotate 6, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 3, .yellow, .yellow,
                .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 12, .yellow, .rotate 5, .hexagon,
                .rotate 9, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 10, .yellow, .rotate 2, .yellow, .rotate 4, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow,
                .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf545` through `cf560`. -/
def classicalConfigurationChunk34 : Array Configuration := #[
      { symmetric := false
        contractReferences := [4, 5, 36]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon,
                .rotate 10, .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 6, .yellow, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 5, .yellow, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 5, .hexagon, .rotate 13, .hexagon, .rotate 13, .hexagon, .rotate 13,
                .hexagon, .rotate 13, .yellow, .rotate 11, .hexagon, .rotate 1, .yellow,
                .rotate 7, .hexagon, .rotate 4, .hexagon, .rotate 11, .hexagon, .rotate 11,
                .hexagon, .rotate 11, .yellow, .rotate 10, .yellow, .rotate 6, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 11,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 3, .hexagon,
                .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 8, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow,
                .rotate 7, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 4, .yellow,
                .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [38]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 6, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 5, .hexagon, .rotate 10,
                .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 4, .yellow,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 13, .hexagon, .rotate 13, .hexagon, .rotate 13,
                .yellow, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 3, .hexagon, .rotate 10,
                .hexagon, .rotate 10, .yellow, .rotate 9, .yellow, .rotate 6, .yellow,
                .rotate 1, .yellow, .rotate 3, .yellow, .yellow, .rotate 2, .hexagon, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [38]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 9, .yellow, .rotate 7, .yellow,
                .rotate 7, .hexagon, .rotate 7, .hexagon, .rotate 7, .hexagon, .rotate 2,
                .hexagon, .rotate 7, .yellow, .rotate 2, .yellow, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 8, .yellow, .rotate 6, .yellow,
                .rotate 4, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .hexagon, .rotate 5, .yellow, .rotate 4, .yellow, .rotate 1, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [19, 20, 40]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 6, .hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 8, .hexagon,
                .rotate 8, .yellow, .rotate 7, .yellow, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 3, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [36]
        program :=
          [.hexagon, .rotate 4, .hexagon, .rotate 13, .hexagon, .rotate 13, .hexagon, .rotate 13,
                .yellow, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon,
                .rotate 5, .hexagon, .rotate 11, .hexagon, .rotate 11, .hexagon, .rotate 11,
                .hexagon, .rotate 11, .yellow, .rotate 10, .yellow, .rotate 6, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 6, .yellow,
                .rotate 5, .yellow, .yellow, .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [40]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1, .hexagon, .rotate 3,
                .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 2, .hexagon,
                .rotate 8, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 2, .yellow, .rotate 3, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [37]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 3,
                .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon,
                .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 7, .yellow,
                .rotate 7, .hexagon, .rotate 7, .yellow, .rotate 2, .yellow, .yellow, .rotate 3,
                .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 3,
                .hexagon, .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 2, .hexagon, .rotate 8,
                .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 4, .yellow, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [10, 31]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 5, .yellow, .rotate 1,
                .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 3,
                .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 4,
                .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [32]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8, .yellow, .rotate 5,
                .hexagon, .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow,
                .rotate 4, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .yellow, .rotate 3,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .hexagon, .rotate 4, .yellow,
                .yellow, .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf561` through `cf576`. -/
def classicalConfigurationChunk35 : Array Configuration := #[
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 2,
                .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 5, .hexagon, .rotate 3, .hexagon, .rotate 8, .hexagon, .rotate 8,
                .yellow, .rotate 6, .yellow, .yellow, .rotate 2, .hexagon, .rotate 1, .yellow,
                .rotate 2, .yellow, .yellow, .yellow] },
      { symmetric := true
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .rotate 4, .yellow, .rotate 2,
                .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 2,
                .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11, .yellow,
                .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 2,
                .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 6, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 4, .yellow, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [8, 9, 34]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 7, .yellow, .rotate 6, .hexagon,
                .rotate 7, .yellow, .rotate 3, .yellow, .yellow, .yellow, .rotate 3, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 8, .hexagon, .rotate 3,
                .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9,
                .yellow, .rotate 8, .yellow, .rotate 6, .hexagon, .rotate 7, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [17]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .hexagon,
                .rotate 6, .yellow, .rotate 5, .yellow, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow] },
      { symmetric := true
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 7, .hexagon, .rotate 7, .hexagon,
                .rotate 7, .hexagon, .rotate 7, .yellow, .rotate 5, .yellow, .yellow, .yellow,
                .yellow, .yellow] },
      { symmetric := true
        contractReferences := [24]
        program :=
          [.hexagon, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8,
                .hexagon, .rotate 6, .hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon,
                .rotate 9, .yellow, .rotate 8, .hexagon, .rotate 8, .yellow, .yellow, .yellow,
                .yellow, .yellow, .yellow, .yellow] },
      { symmetric := true
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 6, .hexagon, .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 10,
                .hexagon, .rotate 10, .yellow, .rotate 7, .hexagon, .rotate 9, .hexagon,
                .rotate 9, .hexagon, .rotate 9, .yellow, .yellow, .yellow, .yellow, .yellow,
                .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 6, .hexagon, .rotate 5, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 5, .hexagon, .rotate 6, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 8, .yellow, .rotate 5, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 5,
                .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [24]
        program :=
          [.hexagon, .rotate 7, .hexagon, .rotate 4, .hexagon, .rotate 11, .hexagon, .rotate 11,
                .hexagon, .rotate 11, .yellow, .rotate 8, .hexagon, .rotate 9, .hexagon,
                .rotate 1, .yellow, .rotate 9, .hexagon, .rotate 9, .yellow, .yellow, .yellow,
                .yellow, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [33]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 7,
                .hexagon, .rotate 10, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 2, .hexagon, .rotate 9, .yellow, .yellow, .rotate 6, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow,
                .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [12, 13, 28]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon,
                .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 1, .yellow, .rotate 7, .yellow,
                .rotate 5, .yellow, .yellow, .yellow, .rotate 2, .yellow, .rotate 2, .yellow] },
      { symmetric := true
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 5, .hexagon,
                .rotate 6, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 2,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow] }
    ]

/-- Published configuration programs `cf577` through `cf592`. -/
def classicalConfigurationChunk36 : Array Configuration := #[
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 5, .hexagon, .rotate 9, .hexagon,
                .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 8,
                .yellow, .rotate 6, .yellow, .yellow, .yellow, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 3, .hexagon, .rotate 9, .hexagon,
                .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 8, .yellow, .rotate 6, .yellow,
                .yellow, .yellow, .rotate 4, .hexagon, .rotate 4, .yellow, .rotate 2, .yellow,
                .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 4, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon, .rotate 7, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 8,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 6, .hexagon, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .rotate 5,
                .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 1, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon,
                .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 8, .yellow, .rotate 6, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow,
                .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 8, .yellow, .rotate 5, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .hexagon, .rotate 4, .yellow,
                .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [8, 9, 33]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 2,
                .yellow, .rotate 6, .hexagon, .rotate 1, .yellow, .rotate 6, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 9,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon, .rotate 3, .hexagon,
                .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .yellow, .yellow,
                .rotate 2, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 7, .hexagon,
                .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 7, .hexagon, .rotate 8,
                .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 4, .hexagon, .rotate 4,
                .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [24]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 8,
                .yellow, .rotate 6, .yellow, .rotate 6, .hexagon, .rotate 6, .yellow, .rotate 2,
                .yellow, .yellow, .rotate 2, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [16, 17, 31]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon,
                .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 3, .hexagon, .rotate 1, .yellow, .rotate 4,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [7]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 12, .hexagon, .rotate 12, .yellow, .rotate 7,
                .hexagon, .rotate 4, .hexagon, .rotate 11, .hexagon, .rotate 11, .hexagon,
                .rotate 11, .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10,
                .yellow, .rotate 9, .yellow, .rotate 7, .yellow, .yellow, .yellow, .yellow,
                .rotate 3, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 8, .hexagon, .rotate 8, .hexagon, .rotate 8, .hexagon, .rotate 8,
                .yellow, .rotate 6, .yellow, .yellow, .rotate 4, .hexagon, .rotate 5, .yellow,
                .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 8, .yellow, .rotate 6, .yellow, .rotate 6, .hexagon, .rotate 1, .yellow,
                .rotate 4, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .hexagon,
                .rotate 4, .yellow, .yellow, .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf593` through `cf608`. -/
def classicalConfigurationChunk37 : Array Configuration := #[
      { symmetric := false
        contractReferences := [15]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 7, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 7,
                .yellow, .rotate 5, .hexagon, .rotate 7, .hexagon, .rotate 7, .yellow, .yellow,
                .rotate 1, .yellow, .rotate 2, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 5, .hexagon,
                .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .yellow, .rotate 4,
                .hexagon, .rotate 4, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [41]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 2,
                .hexagon, .rotate 11, .yellow, .rotate 4, .hexagon, .rotate 1, .hexagon,
                .rotate 8, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3,
                .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 1, .yellow, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [16, 17, 24]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon,
                .rotate 1, .yellow, .rotate 6, .hexagon, .rotate 8, .yellow, .rotate 6, .yellow,
                .yellow, .rotate 4, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .hexagon,
                .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [19, 20, 36]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 9, .hexagon,
                .rotate 9, .hexagon, .rotate 1, .yellow, .rotate 8, .hexagon, .rotate 9,
                .yellow, .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow,
                .rotate 4, .hexagon, .rotate 5, .yellow, .rotate 3, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 6, .hexagon, .rotate 7,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 8,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 5, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 2, .yellow, .rotate 4, .hexagon, .rotate 7, .yellow, .rotate 2,
                .hexagon, .rotate 6, .yellow, .rotate 2, .hexagon, .rotate 5, .yellow,
                .rotate 2, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 4, .hexagon, .rotate 2, .hexagon, .rotate 9, .yellow,
                .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 7,
                .yellow, .rotate 2, .hexagon, .rotate 6, .yellow, .rotate 2, .yellow, .yellow,
                .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [1, 2, 26, 32]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 4, .hexagon, .rotate 10, .hexagon,
                .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .yellow, .rotate 2,
                .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 5, .hexagon, .rotate 8, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 2,
                .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 4, .yellow, .rotate 3, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 5, .hexagon, .rotate 8, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3,
                .hexagon, .rotate 8, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 4, .hexagon,
                .rotate 2, .hexagon, .rotate 9, .yellow, .rotate 2, .yellow, .rotate 3, .yellow,
                .rotate 2, .hexagon, .rotate 6, .yellow, .rotate 2, .hexagon, .rotate 5,
                .yellow, .rotate 2, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 7, .hexagon, .rotate 3, .hexagon, .rotate 10, .hexagon,
                .rotate 10, .yellow, .rotate 7, .hexagon, .rotate 9, .yellow, .rotate 7,
                .yellow, .yellow, .yellow, .rotate 4, .hexagon, .rotate 5, .yellow, .rotate 2,
                .hexagon, .rotate 4, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 5, .hexagon, .rotate 8,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon,
                .rotate 9, .yellow, .rotate 4, .hexagon, .rotate 7, .hexagon, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 4,
                .hexagon, .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 3, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 8,
                .yellow, .rotate 2, .hexagon, .rotate 7, .yellow, .rotate 2, .yellow, .yellow,
                .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 5, .hexagon, .rotate 9,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon,
                .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 6,
                .yellow, .yellow, .rotate 1, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] }
    ]

/-- Published configuration programs `cf609` through `cf624`. -/
def classicalConfigurationChunk38 : Array Configuration := #[
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 3, .hexagon, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 1,
                .yellow, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [29]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 2, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 5, .yellow, .rotate 3,
                .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 4, .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 8, .yellow, .rotate 6, .yellow, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .hexagon,
                .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [23]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 10,
                .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow,
                .rotate 5, .hexagon, .rotate 1, .yellow, .rotate 4, .yellow, .yellow, .rotate 2,
                .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow,
                .rotate 1, .yellow, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [16, 17, 32]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon,
                .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 9,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 3, .hexagon, .rotate 1,
                .yellow, .rotate 4, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2,
                .yellow] },
      { symmetric := false
        contractReferences := [11, 12, 33]
        program :=
          [.hexagon, .rotate 3, .hexagon, .rotate 13, .hexagon, .rotate 13, .yellow, .rotate 10,
                .hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 8, .hexagon,
                .rotate 3, .hexagon, .rotate 11, .hexagon, .rotate 11, .yellow, .rotate 9,
                .hexagon, .rotate 1, .yellow, .rotate 9, .yellow, .rotate 7, .yellow, .yellow,
                .yellow, .yellow, .rotate 2, .yellow, .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [12, 13, 30, 36]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow,
                .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8,
                .hexagon, .rotate 1, .yellow, .rotate 5, .yellow, .yellow, .rotate 3, .hexagon,
                .rotate 6, .yellow, .rotate 3, .yellow, .yellow, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 2, .hexagon, .rotate 1,
                .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 5,
                .yellow, .rotate 4, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 9, .yellow, .rotate 4, .hexagon, .rotate 7,
                .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 4, .hexagon, .rotate 4, .yellow, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 5, .hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 4,
                .hexagon, .rotate 9, .hexagon, .rotate 9, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow,
                .rotate 2, .yellow, .rotate 1, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 4, .hexagon, .rotate 10, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 2,
                .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 3, .hexagon,
                .rotate 7, .yellow, .yellow, .rotate 1, .yellow, .rotate 4, .yellow, .rotate 3,
                .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 12, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 3, .hexagon, .rotate 11, .yellow, .rotate 3, .hexagon,
                .rotate 10, .yellow, .rotate 3, .hexagon, .rotate 2, .hexagon, .rotate 9,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 2, .hexagon, .rotate 6,
                .yellow, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 1, .yellow, .yellow,
                .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [34]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 3, .hexagon, .rotate 12,
                .yellow, .rotate 5, .hexagon, .rotate 9, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 4,
                .hexagon, .rotate 8, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow,
                .rotate 1, .yellow, .rotate 1, .yellow] },
      { symmetric := true
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .hexagon, .rotate 8, .hexagon, .rotate 8, .hexagon,
                .rotate 8, .hexagon, .rotate 8, .hexagon, .rotate 8, .yellow, .rotate 6,
                .yellow, .yellow, .yellow, .yellow, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 7, .hexagon, .rotate 5, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 2,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 10, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 10,
                .yellow, .rotate 6, .hexagon, .rotate 6, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 3, .yellow, .yellow] }
    ]

/-- Published configuration programs `cf625` through `cf633`. -/
def classicalConfigurationChunk39 : Array Configuration := #[
      { symmetric := false
        contractReferences := [12, 13, 32]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 4, .hexagon, .rotate 10, .hexagon,
                .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 1,
                .yellow, .rotate 8, .yellow, .rotate 6, .yellow, .yellow, .yellow, .yellow,
                .rotate 2, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 5, .hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := true
        contractReferences := [30]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 3, .hexagon, .rotate 10, .yellow, .rotate 6, .hexagon,
                .rotate 6, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 2, .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 2, .yellow] },
      { symmetric := false
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 12, .yellow, .rotate 10, .hexagon, .rotate 1,
                .yellow, .rotate 6, .hexagon, .rotate 4, .hexagon, .rotate 10, .hexagon,
                .rotate 10, .hexagon, .rotate 10, .yellow, .rotate 8, .hexagon, .rotate 9,
                .yellow, .rotate 7, .yellow, .yellow, .yellow, .yellow, .rotate 4, .hexagon,
                .rotate 4, .yellow, .rotate 2, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 4, .hexagon, .rotate 9, .hexagon, .rotate 1, .yellow,
                .rotate 3, .hexagon, .rotate 1, .hexagon, .rotate 1, .hexagon, .rotate 1,
                .yellow, .rotate 3, .yellow, .rotate 1, .yellow, .rotate 2, .hexagon, .rotate 1,
                .yellow, .rotate 5, .yellow, .rotate 1, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := false
        contractReferences := [27]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 13, .yellow, .rotate 11, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 2, .hexagon, .rotate 11, .yellow,
                .rotate 9, .hexagon, .rotate 8, .hexagon, .rotate 2, .hexagon, .rotate 10,
                .yellow, .rotate 9, .yellow, .rotate 7, .yellow, .yellow, .rotate 6, .hexagon,
                .rotate 6, .yellow, .rotate 2, .yellow, .yellow, .rotate 2, .yellow, .rotate 2,
                .yellow] },
      { symmetric := false
        contractReferences := [31]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 6, .hexagon, .rotate 7, .hexagon, .rotate 1, .hexagon,
                .rotate 1, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 9,
                .yellow, .rotate 5, .yellow, .rotate 1, .yellow, .rotate 1, .yellow, .rotate 1,
                .yellow, .rotate 3, .hexagon, .rotate 1, .yellow, .rotate 3, .yellow, .rotate 1,
                .yellow] },
      { symmetric := false
        contractReferences := [35]
        program :=
          [.hexagon, .rotate 11, .hexagon, .rotate 1, .yellow, .rotate 3, .hexagon, .rotate 11,
                .yellow, .rotate 5, .hexagon, .rotate 2, .hexagon, .rotate 10, .yellow,
                .rotate 2, .hexagon, .rotate 1, .yellow, .rotate 4, .hexagon, .rotate 8,
                .yellow, .rotate 2, .hexagon, .rotate 7, .yellow, .rotate 2, .hexagon,
                .rotate 6, .yellow, .rotate 2, .yellow, .yellow, .rotate 3, .yellow, .yellow] },
      { symmetric := true
        contractReferences := [6]
        program :=
          [.hexagon, .rotate 2, .hexagon, .rotate 11, .yellow, .rotate 9, .hexagon, .rotate 1,
                .yellow, .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 9, .hexagon,
                .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 9, .hexagon, .rotate 9,
                .yellow, .rotate 7, .yellow, .yellow, .yellow, .yellow, .yellow, .yellow,
                .yellow] }
    ]

/-- The complete 633-entry classical reducible-configuration catalogue. -/
def classicalConfigurationCatalogue : ProgramCatalogue where
  chunks := #[
    classicalConfigurationChunk00,
    classicalConfigurationChunk01,
    classicalConfigurationChunk02,
    classicalConfigurationChunk03,
    classicalConfigurationChunk04,
    classicalConfigurationChunk05,
    classicalConfigurationChunk06,
    classicalConfigurationChunk07,
    classicalConfigurationChunk08,
    classicalConfigurationChunk09,
    classicalConfigurationChunk10,
    classicalConfigurationChunk11,
    classicalConfigurationChunk12,
    classicalConfigurationChunk13,
    classicalConfigurationChunk14,
    classicalConfigurationChunk15,
    classicalConfigurationChunk16,
    classicalConfigurationChunk17,
    classicalConfigurationChunk18,
    classicalConfigurationChunk19,
    classicalConfigurationChunk20,
    classicalConfigurationChunk21,
    classicalConfigurationChunk22,
    classicalConfigurationChunk23,
    classicalConfigurationChunk24,
    classicalConfigurationChunk25,
    classicalConfigurationChunk26,
    classicalConfigurationChunk27,
    classicalConfigurationChunk28,
    classicalConfigurationChunk29,
    classicalConfigurationChunk30,
    classicalConfigurationChunk31,
    classicalConfigurationChunk32,
    classicalConfigurationChunk33,
    classicalConfigurationChunk34,
    classicalConfigurationChunk35,
    classicalConfigurationChunk36,
    classicalConfigurationChunk37,
    classicalConfigurationChunk38,
    classicalConfigurationChunk39
    ]

theorem classicalConfigurationCatalogue_chunkCount :
    classicalConfigurationCatalogue.chunks.size = 40 := by
  rfl

theorem classicalConfigurationCatalogue_populated :
    classicalConfigurationCatalogue.populatedPrefixBoolean 633 = true := by
  rfl

theorem classicalConfigurationCatalogue_afterLast :
    classicalConfigurationCatalogue.programAt? 633 = none := by
  rfl

end ClassicalCertificateCataloguePrograms

end Mettapedia.GraphTheory.FourColor
