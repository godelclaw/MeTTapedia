import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_2_6_5_3

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "9bed1d938d341a71f1cf43ff7d7059b8462b0cdf2069cbacd7086ed91a8a3ae4"
def certificateSHA256 : String := "44813b3a92be4cd6054bbba5d7bf504c8d39986c8b323dd3ae33f024040b46d8"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 673 := ![
  17,
  151,
  175,
  179,
  296,
  297,
  300,
  312,
  349,
  401,
  410,
  430,
  435,
  437,
  453,
  455,
  470,
  474,
  476,
  580,
  581,
  583,
  594,
  602,
  603,
  606,
  607,
  612,
  645,
  648,
  655,
  658,
  660,
  661,
  665,
  666,
  669,
  670,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (30, 1), (60, 1)] }, { coefficient := 1, powers := [(23, 1), (54, 1)] }, { coefficient := 1, powers := [(30, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (57, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (41, 1)] }, { coefficient := 1, powers := [(29, 1), (46, 1)] }, { coefficient := 1, powers := [(29, 1), (52, 1)] }, { coefficient := 1, powers := [(29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (46, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (55, 1)] }, { coefficient := 1, powers := [(26, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (55, 1)] }, { coefficient := 1, powers := [(51, 1), (58, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (52, 1)] }, { coefficient := 1, powers := [(3, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (57, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(8, 1), (29, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (54, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (60, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (60, 1)] }, { coefficient := 1, powers := [(20, 1)] }, { coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (61, 1)] }, { coefficient := 1, powers := [(0, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (61, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (45, 1)] }, { coefficient := 1, powers := [(6, 1), (59, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (45, 1)] }, { coefficient := 1, powers := [(9, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(0, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(41, 1)] }, { coefficient := 1, powers := [(46, 1)] }, { coefficient := 1, powers := [(52, 1)] }, { coefficient := 1, powers := [(57, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (38, 1), (60, 1)] }, { coefficient := 1, powers := [(2, 1), (41, 1), (57, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (52, 1)] }, { coefficient := 1, powers := [(18, 1), (29, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(57, 1), (66, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := 1, powers := [(61, 1), (70, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 71) := ![
  [{ coefficient := -1, powers := [(0, 1), (23, 1), (25, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(13, 1), (23, 1), (25, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (25, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (23, 1), (25, 1), (46, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 2), (43, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (34, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (43, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (25, 1), (46, 1), (56, 1), (57, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (46, 1), (56, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (34, 1), (37, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (56, 1), (66, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (56, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1), (41, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(23, 1), (25, 1), (46, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (41, 2), (63, 1)] }, { coefficient := 2, powers := [(25, 1), (28, 1), (41, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (41, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (46, 2), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (28, 1), (46, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (41, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (29, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(28, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(28, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(29, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (47, 1), (60, 1), (68, 1), (70, 1)] }, { coefficient := 1, powers := [(44, 1), (60, 1), (68, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (44, 1), (46, 1), (52, 1), (60, 1), (70, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1), (52, 1), (60, 1), (62, 1), (70, 1)] }, { coefficient := 1, powers := [(30, 1), (47, 1), (60, 1), (68, 1), (70, 1)] }, { coefficient := -1, powers := [(44, 1), (46, 1), (60, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (47, 1), (60, 1), (68, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (45, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (46, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 2), (43, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (34, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(13, 1), (25, 1), (31, 1), (37, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (41, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (46, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (52, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (57, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (31, 1), (37, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (28, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (28, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (25, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (52, 1), (63, 1)] }, { coefficient := 1, powers := [(20, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 2), (52, 1), (63, 1)] }, { coefficient := 2, powers := [(25, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (25, 1), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 2), (62, 1), (63, 1)] }, { coefficient := -1, powers := [(25, 1), (30, 1), (63, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (29, 1), (63, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (23, 1), (25, 1), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 2), (62, 1), (63, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (30, 1), (63, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (20, 1), (25, 1), (41, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (54, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (43, 1)] }],
  [{ coefficient := -1, powers := [(30, 1), (60, 1), (68, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (60, 1), (68, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [] }],
  [{ coefficient := -1, powers := [(25, 1), (30, 1), (46, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (46, 1), (56, 1), (66, 1)] }],
  [{ coefficient := -1, powers := [(23, 1), (25, 1), (63, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (46, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1), (52, 1), (61, 1), (70, 1)] }, { coefficient := 1, powers := [(25, 1), (52, 1), (61, 1), (62, 1), (70, 1)] }, { coefficient := -1, powers := [(46, 1), (61, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (46, 1), (52, 1), (60, 1), (70, 1)] }, { coefficient := -1, powers := [(25, 1), (52, 1), (60, 1), (62, 1), (70, 1)] }, { coefficient := 1, powers := [(46, 1), (60, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(25, 1)] }],
  [{ coefficient := -1, powers := [(20, 1), (25, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (20, 1), (25, 1), (41, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (20, 1), (25, 1), (38, 1), (41, 1), (60, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (25, 1), (41, 2), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (20, 1), (25, 1), (41, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (43, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (45, 1), (50, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (46, 2)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (46, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(20, 1), (46, 1)] }, { coefficient := 1, powers := [(23, 1), (25, 1), (46, 1), (54, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 2), (43, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 2), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(25, 2), (52, 1), (62, 1)] }, { coefficient := -1, powers := [(25, 1), (29, 1), (54, 1), (68, 1)] }, { coefficient := 1, powers := [(25, 1), (30, 1), (52, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (34, 1), (37, 1), (46, 1), (50, 1)] }, { coefficient := -1, powers := [(25, 1), (43, 1), (50, 1)] }, { coefficient := -2, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (18, 1), (25, 1), (28, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := 1, powers := [(0, 1), (25, 1), (46, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1), (34, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (18, 1), (25, 1), (28, 1), (63, 1)] }, { coefficient := -1, powers := [(13, 1), (25, 2), (46, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (25, 1), (28, 1), (45, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (20, 1), (25, 1), (28, 1), (46, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 2), (28, 1), (43, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (28, 1), (34, 1), (37, 1), (46, 1), (63, 1)] }, { coefficient := -1, powers := [(18, 1), (25, 1), (28, 1), (43, 1), (63, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (30, 1), (46, 1), (56, 1), (57, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(20, 1), (25, 1), (30, 1), (46, 1), (56, 1), (68, 1)] }, { coefficient := 1, powers := [(25, 2), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (30, 1), (34, 1), (37, 1), (46, 1), (68, 1)] }, { coefficient := -1, powers := [(25, 1), (30, 1), (46, 1), (56, 1), (66, 1), (68, 1)] }, { coefficient := 1, powers := [(25, 1), (30, 1), (56, 1), (68, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (56, 1), (66, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (25, 1), (31, 1), (46, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (51, 1), (60, 1), (68, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (25, 1), (46, 1), (52, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := -1, powers := [(9, 1), (20, 1), (25, 1), (46, 1), (56, 1), (57, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (25, 1), (46, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (34, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(9, 1), (25, 1), (46, 1), (56, 1), (66, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (56, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (31, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (41, 2)] }, { coefficient := -2, powers := [(20, 1), (25, 1), (41, 1), (46, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (41, 1), (52, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (41, 1), (57, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (46, 2)] }, { coefficient := -1, powers := [(25, 1), (31, 1), (37, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (52, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (37, 1), (46, 1)] }, { coefficient := -1, powers := [(3, 1), (25, 2), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (20, 1), (25, 1), (46, 1)] }, { coefficient := -1, powers := [(6, 1), (25, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (25, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(0, 1), (25, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (30, 1), (60, 1), (68, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(20, 1), (25, 1), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(20, 1), (46, 1)] }, { coefficient := -1, powers := [(25, 2), (46, 1), (52, 1)] }, { coefficient := -1, powers := [(25, 2), (52, 1), (62, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }]
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
    (values : Fin 71 → R) :
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_2_6_5_3.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_2_6_5_3
