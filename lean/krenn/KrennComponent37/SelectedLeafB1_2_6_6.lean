import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB1_2_6_6

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "78dbe11648eda4b20cf41222c97b122ff23b7d4ec8160047683e7bf35d1f79da"
def certificateSHA256 : String := "ff757cae81cd931c6c989f42a963e74a9a5a4a3261693b10f9ced67078f73888"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 24 → Fin 670 := ![
  13,
  15,
  17,
  25,
  150,
  300,
  301,
  303,
  461,
  470,
  487,
  583,
  586,
  591,
  602,
  603,
  612,
  645,
  655,
  658,
  660,
  661,
  665,
  668
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 24 → SparsePoly (Fin 68) := ![
  [{ coefficient := 1, powers := [(17, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (27, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(27, 1), (43, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (27, 1)] }, { coefficient := 1, powers := [(27, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (43, 1)] }, { coefficient := 1, powers := [(13, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (57, 1)] }, { coefficient := 1, powers := [(31, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (52, 1)] }, { coefficient := 1, powers := [(43, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (41, 1)] }, { coefficient := 1, powers := [(13, 1), (52, 1)] }, { coefficient := 1, powers := [(34, 1), (38, 1)] }, { coefficient := 1, powers := [(45, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(2, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(17, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(27, 1), (67, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 24 → SparsePoly (Fin 68) := ![
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (23, 1), (41, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (23, 1), (52, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (23, 1), (60, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (23, 1), (41, 1), (59, 1), (62, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (23, 1), (52, 1), (59, 1), (62, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (28, 1), (41, 1), (59, 1), (62, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (28, 1), (52, 1), (59, 1), (62, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (59, 1), (62, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(6, 1), (28, 1), (59, 1), (62, 1), (65, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (23, 1), (41, 1), (43, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (23, 1), (43, 1), (52, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (23, 1), (43, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (20, 1), (23, 1), (46, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (41, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (23, 1), (45, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (46, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (34, 1), (37, 1), (41, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(23, 1), (34, 1), (37, 1), (46, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (41, 1), (50, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1), (50, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1), (52, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (50, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (50, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (41, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (46, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (52, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(50, 1), (65, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (41, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (52, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(20, 1), (56, 1), (57, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (43, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (46, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (52, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (41, 1), (65, 1), (67, 1)] }, { coefficient := -2, powers := [(34, 1), (37, 1), (46, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (52, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (57, 1), (65, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (41, 1), (43, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (43, 1), (52, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (43, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(13, 1), (20, 1), (46, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (41, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := -2, powers := [(20, 1), (45, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (41, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1), (46, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (41, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (37, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(50, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (45, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (20, 1), (41, 1), (59, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (52, 1), (59, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1), (62, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(31, 1), (37, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (41, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (52, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (60, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(41, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(46, 1), (50, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(41, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(43, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(43, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(45, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(65, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (31, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(65, 1)] }],
  [{ coefficient := 1, powers := [(41, 1), (65, 1)] }, { coefficient := 1, powers := [(46, 1), (65, 1)] }, { coefficient := 1, powers := [(52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (31, 1), (38, 1), (56, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (41, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (46, 1), (52, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1), (45, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(37, 1), (41, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(37, 1), (46, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(37, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(38, 1), (60, 1), (65, 1)] }, { coefficient := 1, powers := [(41, 1), (43, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(41, 1), (57, 1), (65, 1)] }, { coefficient := 1, powers := [(43, 1), (46, 1), (50, 1), (65, 1)] }, { coefficient := 1, powers := [(43, 1), (50, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(46, 1), (52, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (20, 1), (41, 1), (59, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (52, 1), (59, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (59, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (20, 1), (46, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (41, 1), (50, 1), (56, 1), (65, 1)] }, { coefficient := 2, powers := [(20, 1), (45, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (46, 1), (50, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (41, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(34, 1), (37, 1), (46, 1), (50, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (41, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (46, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (52, 1), (56, 1), (65, 1)] }, { coefficient := -1, powers := [(0, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (20, 1), (41, 1), (56, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(2, 1), (6, 1), (20, 1), (52, 1), (56, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (6, 1), (56, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (20, 1), (28, 1), (41, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (17, 1), (20, 1), (28, 1), (52, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (17, 1), (28, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (28, 1), (41, 1), (43, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (20, 1), (28, 1), (43, 1), (52, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (28, 1), (43, 1), (60, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (41, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (34, 1), (52, 1), (65, 1)] }, { coefficient := -2, powers := [(13, 1), (18, 1), (20, 1), (28, 1), (46, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (28, 1), (41, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := 2, powers := [(18, 1), (20, 1), (28, 1), (45, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (28, 1), (46, 1), (56, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (34, 1), (37, 1), (41, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (34, 1), (37, 1), (46, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1), (41, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1), (52, 1), (56, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(20, 1), (27, 1), (56, 1), (57, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (27, 1), (41, 1), (43, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (27, 1), (43, 1), (46, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(25, 1), (27, 1), (43, 1), (52, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1), (43, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (45, 1), (65, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (37, 1), (41, 1), (65, 1), (67, 1)] }, { coefficient := 2, powers := [(27, 1), (34, 1), (37, 1), (46, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (37, 1), (52, 1), (65, 1), (67, 1)] }, { coefficient := 1, powers := [(27, 1), (34, 1), (37, 1), (57, 1), (65, 1), (67, 1)] }, { coefficient := -1, powers := [(56, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (23, 1), (41, 1), (59, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (23, 1), (52, 1), (59, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (28, 1), (41, 1), (59, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(6, 1), (18, 1), (20, 1), (28, 1), (52, 1), (59, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (23, 1), (59, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (28, 1), (59, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (41, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (52, 1), (56, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (41, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (43, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (43, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (41, 1), (65, 1)] }, { coefficient := 2, powers := [(9, 1), (34, 1), (37, 1), (46, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (52, 1), (65, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1), (57, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (41, 1), (43, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (46, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(20, 1), (43, 1), (50, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (41, 1), (43, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (46, 1), (50, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (41, 1), (43, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (46, 1), (65, 1)] }, { coefficient := -1, powers := [(31, 1), (37, 1), (43, 1), (52, 1), (65, 1)] }, { coefficient := -1, powers := [(43, 1), (50, 1), (65, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (1 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 68 → R) :
    ¬ ∀ index : Fin 24,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB1_2_6_6.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB1_2_6_6
