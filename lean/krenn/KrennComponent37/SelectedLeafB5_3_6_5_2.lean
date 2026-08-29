import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component37.SelectedLeafB5_3_6_5_2

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "cce8381e8513ed0ffe7aa9d60a61c63192256b91e46222b2bf8358314fab8f4b"
def certificateSHA256 : String := "36d4b87a9170aadb537af03bf4679bbc7845f3effed75b18a3d33490afae8371"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 51 → Fin 673 := ![
  17,
  151,
  167,
  171,
  175,
  176,
  177,
  179,
  180,
  183,
  280,
  294,
  295,
  296,
  300,
  315,
  343,
  410,
  433,
  434,
  438,
  440,
  446,
  447,
  449,
  454,
  472,
  474,
  580,
  583,
  587,
  602,
  603,
  621,
  623,
  624,
  638,
  642,
  655,
  657,
  658,
  660,
  661,
  663,
  665,
  666,
  667,
  669,
  670,
  671,
  672
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 51 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(18, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (30, 1)] }, { coefficient := 1, powers := [(30, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (25, 1)] }, { coefficient := 1, powers := [(18, 1), (20, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (53, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (20, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (20, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (53, 1)] }, { coefficient := -1, powers := [(29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(20, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (51, 1)] }, { coefficient := 1, powers := [(20, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (50, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1), (51, 1)] }, { coefficient := 1, powers := [(51, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (47, 1)] }, { coefficient := 1, powers := [(19, 1), (29, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (25, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (51, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1)] }, { coefficient := 1, powers := [(18, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (36, 1)] }, { coefficient := 1, powers := [(23, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (61, 1)] }, { coefficient := 1, powers := [(12, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (53, 1)] }, { coefficient := 1, powers := [(19, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (33, 1)] }, { coefficient := 1, powers := [(23, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (60, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (46, 1)] }, { coefficient := 1, powers := [(18, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (55, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(30, 1), (48, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1), (54, 1)] }, { coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (46, 1)] }, { coefficient := 1, powers := [(54, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (61, 1)] }, { coefficient := 1, powers := [(25, 1), (47, 1), (51, 1)] }, { coefficient := 1, powers := [(44, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(6, 1), (60, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (40, 1), (57, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (57, 1)] }, { coefficient := 1, powers := [(9, 1)] }, { coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(6, 1), (21, 1), (61, 1)] }, { coefficient := 1, powers := [(21, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(25, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(25, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1)] }, { coefficient := 1, powers := [(20, 1), (56, 1)] }, { coefficient := 1, powers := [(25, 1), (43, 1)] }, { coefficient := 1, powers := [(34, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1)] }, { coefficient := 1, powers := [(20, 1), (50, 1)] }, { coefficient := 1, powers := [(25, 1), (40, 1)] }, { coefficient := 1, powers := [(31, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (23, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (44, 1)] }, { coefficient := 1, powers := [(12, 1), (23, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (44, 1)] }, { coefficient := 1, powers := [(19, 1), (23, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (48, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(18, 1), (33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(12, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (51, 1)] }, { coefficient := 1, powers := [(19, 1), (28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(6, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(6, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (44, 1), (51, 1)] }, { coefficient := 1, powers := [(28, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1), (51, 1), (58, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1), (44, 1)] }, { coefficient := 1, powers := [(30, 1), (49, 1), (51, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1), (44, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (37, 1), (59, 1)] }, { coefficient := 1, powers := [(0, 1), (40, 1), (56, 1)] }, { coefficient := 1, powers := [(0, 1), (43, 1), (50, 1)] }, { coefficient := 1, powers := [(3, 1), (25, 1), (59, 1)] }, { coefficient := 1, powers := [(3, 1), (31, 1), (56, 1)] }, { coefficient := 1, powers := [(3, 1), (34, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (20, 1), (59, 1)] }, { coefficient := 1, powers := [(6, 1), (31, 1), (43, 1)] }, { coefficient := 1, powers := [(6, 1), (34, 1), (40, 1)] }, { coefficient := 1, powers := [(9, 1), (20, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (25, 1), (43, 1)] }, { coefficient := 1, powers := [(9, 1), (34, 1), (37, 1)] }, { coefficient := 1, powers := [(13, 1), (20, 1), (50, 1)] }, { coefficient := 1, powers := [(13, 1), (25, 1), (40, 1)] }, { coefficient := 1, powers := [(13, 1), (31, 1), (37, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (61, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (58, 1)] }, { coefficient := 1, powers := [(2, 1), (49, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (61, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (61, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (58, 1)] }, { coefficient := 1, powers := [(12, 1), (30, 1), (49, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (62, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (63, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(40, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (65, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(57, 1), (67, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(58, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (68, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(30, 1), (69, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(59, 1)] }],
  [{ coefficient := 1, powers := [(60, 1), (70, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(61, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 51 → SparsePoly (Fin 71) := ![
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (23, 1), (36, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (23, 1), (36, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (23, 1), (36, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (25, 1), (36, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (34, 1), (36, 1), (37, 1), (55, 1), (63, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (20, 1), (36, 1), (55, 1), (57, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (36, 1), (55, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (36, 1), (43, 1), (55, 1), (57, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (36, 1), (55, 1), (56, 1), (57, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (36, 1), (55, 1), (56, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (36, 1), (37, 1), (55, 1), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (43, 1), (55, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1), (56, 1), (67, 1), (69, 1)] }],
  [{ coefficient := -1, powers := [(24, 1), (42, 1), (44, 1), (54, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (28, 1), (42, 1), (54, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1), (42, 1), (44, 1), (51, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1), (44, 1), (51, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(24, 1), (42, 1), (44, 1), (51, 1), (54, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(28, 1), (42, 2), (44, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := -1, powers := [(29, 1), (42, 1), (49, 1), (51, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(36, 1), (39, 1), (51, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(21, 1), (29, 1), (42, 1), (51, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(20, 1), (29, 1), (42, 1), (51, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (49, 1)] }, { coefficient := -1, powers := [(19, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (42, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (42, 1), (51, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (19, 1), (21, 1), (42, 1), (54, 1), (63, 1), (65, 1)] }, { coefficient := 1, powers := [(19, 1), (21, 1), (42, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (42, 1), (51, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (21, 1), (29, 1), (42, 1), (51, 1), (54, 1), (62, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (28, 1), (42, 2), (54, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (42, 1), (46, 1), (51, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (23, 1), (31, 1), (51, 1), (55, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (28, 1), (31, 1), (51, 1), (55, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (31, 1), (43, 1), (51, 1), (55, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (31, 1), (43, 1), (51, 1), (55, 1), (65, 1), (68, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (24, 1), (42, 1), (44, 1), (54, 1), (62, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (5, 1), (36, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (36, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (36, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (36, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(5, 1), (34, 1), (36, 1), (37, 1), (55, 1), (63, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (21, 1), (42, 1), (47, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (49, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (42, 1), (54, 1), (63, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(36, 1), (42, 1), (54, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (51, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(42, 1), (49, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (31, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (31, 1), (43, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(28, 1), (42, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (42, 1), (49, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(36, 1), (42, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(19, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (36, 1), (42, 1), (70, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (21, 1), (42, 1), (46, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1), (36, 1), (42, 1), (54, 1), (70, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (36, 1), (55, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (43, 1), (55, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (55, 1), (56, 1), (67, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (13, 1), (23, 1), (31, 1), (55, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (28, 1), (31, 1), (55, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(5, 1), (23, 1), (31, 1), (43, 1), (55, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(5, 1), (28, 1), (31, 1), (43, 1), (55, 1), (65, 1), (68, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (36, 1), (43, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(48, 1)] }],
  [{ coefficient := -1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (54, 1), (65, 1)] }],
  [{ coefficient := -1, powers := [(18, 1), (42, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(18, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(18, 1), (21, 1), (29, 1), (42, 1), (44, 1), (51, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (24, 1), (42, 1), (44, 1), (51, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(18, 1), (28, 1), (42, 2), (44, 1), (54, 1), (65, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := -1, powers := [(2, 1), (21, 1), (42, 1), (47, 1), (51, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (36, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (36, 1), (50, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (25, 1), (36, 1), (43, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (34, 1), (36, 1), (37, 1), (50, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (13, 1), (36, 1), (55, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (18, 1), (28, 1), (36, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (36, 1), (43, 1), (55, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (36, 1), (55, 1), (56, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (34, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (20, 1), (30, 1), (36, 1), (55, 1), (57, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (25, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (13, 1), (30, 1), (36, 1), (55, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (36, 1), (55, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (20, 1), (28, 1), (36, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (20, 1), (28, 1), (36, 1), (55, 1), (56, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (25, 1), (28, 1), (36, 1), (43, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (18, 1), (28, 1), (34, 1), (36, 1), (37, 1), (55, 1), (63, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (30, 1), (36, 1), (43, 1), (55, 1), (57, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (20, 1), (30, 1), (36, 1), (55, 1), (56, 1), (57, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (20, 1), (30, 1), (36, 1), (55, 1), (56, 1), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (36, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (30, 1), (34, 1), (36, 1), (37, 1), (55, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (36, 1), (43, 1), (55, 1), (67, 1), (69, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (36, 1), (55, 1), (56, 1), (67, 1), (69, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (43, 1), (55, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (36, 1), (55, 1), (56, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (23, 1), (25, 1), (31, 1), (44, 1), (55, 1), (68, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (25, 1), (28, 1), (31, 1), (44, 1), (55, 1), (68, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (25, 1), (31, 1), (43, 1), (44, 1), (55, 1), (68, 1)] }, { coefficient := -1, powers := [(5, 1), (25, 1), (28, 1), (31, 1), (43, 1), (44, 1), (55, 1), (68, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (36, 1), (42, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (5, 1), (13, 1), (31, 1), (36, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (36, 1), (43, 1), (55, 1)] }, { coefficient := -1, powers := [(3, 1), (5, 1), (31, 1), (36, 1), (55, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (42, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1)] }, { coefficient := -1, powers := [(12, 1), (23, 1), (48, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (13, 1), (23, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (13, 1), (28, 1), (31, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (23, 1), (31, 1), (43, 1), (44, 1), (55, 1)] }, { coefficient := -1, powers := [(5, 1), (28, 1), (31, 1), (43, 1), (44, 1), (55, 1)] }, { coefficient := 1, powers := [(12, 1), (24, 1), (42, 1), (44, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(12, 1), (36, 1), (39, 1)] }, { coefficient := -1, powers := [(18, 1), (24, 1), (42, 1), (44, 1), (51, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(18, 1), (36, 1), (39, 1), (51, 1)] }],
  [{ coefficient := -1, powers := [(5, 1), (9, 1), (13, 1), (20, 1), (36, 1), (55, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (13, 1), (36, 1), (55, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (36, 1), (43, 1), (55, 1), (57, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (20, 1), (36, 1), (55, 1), (56, 1), (57, 1), (67, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (20, 1), (36, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(5, 1), (9, 1), (34, 1), (36, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (36, 1), (43, 1), (55, 1), (67, 1)] }, { coefficient := 1, powers := [(5, 1), (9, 1), (36, 1), (55, 1), (56, 1), (67, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (5, 1), (36, 1), (37, 1), (55, 1)] }, { coefficient := 1, powers := [(3, 1), (5, 1), (25, 1), (36, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (20, 1), (36, 1), (55, 1)] }],
  [{ coefficient := -1, powers := [(6, 1), (18, 1), (36, 1), (42, 1), (54, 1)] }, { coefficient := -1, powers := [(8, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(2, 1), (6, 1), (21, 1), (42, 1), (46, 1), (54, 1), (65, 1)] }, { coefficient := 1, powers := [(2, 1), (39, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (13, 1), (21, 1), (23, 1), (31, 1), (55, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (13, 1), (21, 1), (28, 1), (31, 1), (55, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (21, 1), (23, 1), (31, 1), (43, 1), (55, 1), (65, 1), (68, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (21, 1), (28, 1), (31, 1), (43, 1), (55, 1), (65, 1), (68, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1)] }, { coefficient := 1, powers := [(6, 1), (18, 1), (24, 1), (42, 1), (54, 1), (65, 1)] }, { coefficient := -1, powers := [(8, 1), (23, 1), (48, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1)] }]
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
    ¬ ∀ index : Fin 51,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component37.SelectedLeafB5_3_6_5_2.selectedHasNoCommonZero

end Krenn.Component37.SelectedLeafB5_3_6_5_2
