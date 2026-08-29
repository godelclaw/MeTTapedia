import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalB4Certificate

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "c691f9978d2ea53ef247385b0f642382edc85f327b95b30291fa89767c827b64"
def certificateSHA256 : String := "7e45b67fef719ebb88d2abcec7976e7a31dc25c1474b3232e44c7ab2fddce709"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 28 → Fin 327 := ![
  0,
  1,
  2,
  9,
  17,
  28,
  32,
  33,
  84,
  124,
  146,
  194,
  200,
  217,
  224,
  227,
  231,
  238,
  301,
  306,
  308,
  314,
  315,
  317,
  318,
  319,
  323,
  324
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 28 → SparsePoly (Fin 59) := ![
  [{ coefficient := 1, powers := [(7, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(7, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(7, 1), (44, 1), (46, 1)] }, { coefficient := 1, powers := [(10, 1), (31, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (34, 1), (49, 1)] }, { coefficient := 1, powers := [(10, 1), (37, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (28, 1), (52, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1), (44, 1)] }, { coefficient := 1, powers := [(13, 1), (37, 1), (42, 1)] }, { coefficient := 1, powers := [(16, 1), (28, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1), (44, 1)] }, { coefficient := 1, powers := [(16, 1), (37, 1), (40, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (46, 1)] }, { coefficient := 1, powers := [(24, 1), (31, 1), (42, 1)] }, { coefficient := 1, powers := [(24, 1), (34, 1), (40, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(7, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (34, 1)] }, { coefficient := 1, powers := [(16, 1), (31, 1)] }, { coefficient := 1, powers := [(28, 1), (46, 1)] }, { coefficient := 1, powers := [(31, 1), (42, 1)] }, { coefficient := 1, powers := [(34, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (37, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1)] }, { coefficient := 1, powers := [(28, 1), (49, 1)] }, { coefficient := 1, powers := [(31, 1), (44, 1)] }, { coefficient := 1, powers := [(37, 1), (40, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(10, 1), (37, 1), (48, 1)] }, { coefficient := 1, powers := [(24, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(44, 1)] }],
  [{ coefficient := 1, powers := [(13, 1), (52, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1)] }, { coefficient := 1, powers := [(24, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(34, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(37, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(39, 1), (41, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (40, 1), (52, 1)] }, { coefficient := 1, powers := [(8, 1), (42, 1), (49, 1)] }, { coefficient := 1, powers := [(8, 1), (44, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (41, 1), (54, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (28, 1)] }, { coefficient := 1, powers := [(22, 1), (28, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(22, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(22, 1), (28, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (43, 1)] }, { coefficient := 1, powers := [(2, 1), (48, 1)] }, { coefficient := 1, powers := [(22, 1), (43, 1)] }, { coefficient := 1, powers := [(22, 1), (45, 1)] }, { coefficient := 1, powers := [(22, 1), (48, 1)] }, { coefficient := 1, powers := [(22, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(22, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (37, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (34, 1), (51, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (36, 1), (49, 1)] }],
  [{ coefficient := 1, powers := [(12, 1), (36, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (41, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(9, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(12, 1), (36, 1), (51, 1)] }, { coefficient := 1, powers := [(23, 1), (39, 1), (41, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (6, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(2, 1), (31, 1), (48, 1)] }, { coefficient := -1, powers := [(2, 1)] }, { coefficient := 1, powers := [(22, 1), (28, 1), (48, 1)] }, { coefficient := 1, powers := [(22, 1), (28, 1), (50, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1), (48, 1)] }, { coefficient := 1, powers := [(22, 1), (31, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (43, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (45, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(48, 1), (56, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 28 → SparsePoly (Fin 59) := ![
  [{ coefficient := -1, powers := [(4, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (24, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (16, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (46, 1), (48, 1), (56, 2)] }, { coefficient := 1, powers := [(4, 1), (46, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (46, 1), (56, 2)] }],
  [{ coefficient := -1, powers := [(4, 1), (7, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (28, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (7, 1), (12, 1), (36, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(12, 1), (24, 1), (36, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (9, 1), (10, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (13, 1), (24, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (13, 1), (44, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (13, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (40, 1), (49, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (9, 1), (10, 1), (16, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (13, 1), (42, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (4, 1), (22, 1), (23, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (13, 1), (23, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (7, 1), (16, 1), (23, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (16, 1), (23, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (23, 1), (40, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (23, 1), (42, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (23, 1), (46, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (10, 1), (16, 1), (23, 1), (37, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (10, 1), (23, 1), (31, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (10, 1), (23, 1), (34, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (23, 1), (24, 1), (34, 1), (56, 1)] }, { coefficient := -2, powers := [(4, 1), (13, 1), (23, 1), (31, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (23, 1), (34, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (23, 1), (34, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (23, 1), (37, 1), (42, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (28, 1), (50, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (31, 1), (42, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (31, 1), (46, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (34, 1), (40, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (40, 1), (52, 1), (56, 2)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (42, 1), (49, 1), (56, 2)] }, { coefficient := 2, powers := [(13, 1), (23, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (23, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (23, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(23, 1), (46, 1), (49, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (55, 1), (56, 2)] }],
  [{ coefficient := 1, powers := [(3, 1), (4, 1), (9, 1), (22, 1), (55, 1)] }, { coefficient := -1, powers := [(4, 1), (7, 1), (9, 1), (16, 1), (44, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (9, 1), (16, 1), (49, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (9, 1), (42, 1), (49, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (9, 1), (46, 1), (49, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (28, 1), (50, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (31, 1), (42, 1), (49, 1), (55, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (31, 1), (46, 1), (49, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (42, 1), (49, 1), (55, 1), (56, 2)] }, { coefficient := -1, powers := [(9, 1), (16, 1), (24, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (16, 1), (49, 1), (55, 1), (56, 1)] }, { coefficient := 1, powers := [(9, 1), (46, 1), (49, 1), (55, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (6, 1), (48, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (6, 1), (50, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (4, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (4, 1), (31, 1)] }, { coefficient := 1, powers := [(3, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (4, 1), (12, 1), (36, 1)] }],
  [{ coefficient := -1, powers := [(4, 1), (10, 1), (16, 1), (36, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (36, 1), (42, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (7, 1), (13, 1), (36, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (36, 1), (40, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (10, 1), (31, 1), (36, 1), (51, 1), (56, 1)] }, { coefficient := -2, powers := [(4, 1), (13, 1), (31, 1), (36, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (40, 1), (51, 1), (56, 2)] }, { coefficient := 2, powers := [(13, 1), (36, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (10, 1), (36, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (24, 1), (36, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (36, 1), (44, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (36, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (36, 1), (40, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (7, 1), (16, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (42, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (46, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (42, 1), (51, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (46, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (42, 1), (51, 1), (56, 2)] }, { coefficient := 1, powers := [(16, 1), (51, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (51, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (7, 1), (13, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (40, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (10, 1), (31, 1), (54, 1), (56, 1)] }, { coefficient := -2, powers := [(4, 1), (13, 1), (31, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (40, 1), (54, 1), (56, 2)] }, { coefficient := 2, powers := [(13, 1), (54, 1), (56, 1)] }],
  [{ coefficient := -1, powers := [(3, 1), (4, 1), (22, 1)] }, { coefficient := -1, powers := [(4, 1), (7, 1), (13, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (16, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (7, 1), (16, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (7, 1), (40, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (7, 1), (42, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (7, 1), (46, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (10, 1), (16, 1), (37, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (10, 1), (31, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (10, 1), (34, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (13, 1), (24, 1), (34, 1), (56, 1)] }, { coefficient := 2, powers := [(4, 1), (13, 1), (31, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (34, 1), (44, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (34, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (13, 1), (37, 1), (42, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (28, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (42, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (46, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (34, 1), (40, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (40, 1), (52, 1), (56, 2)] }, { coefficient := -1, powers := [(4, 1), (42, 1), (49, 1), (56, 2)] }, { coefficient := -2, powers := [(13, 1), (52, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (49, 1), (56, 1)] }, { coefficient := -1, powers := [(46, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (50, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1), (48, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (6, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (3, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (22, 1), (50, 1)] }, { coefficient := 2, powers := [(13, 1), (52, 1), (56, 1)] }, { coefficient := -1, powers := [(16, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(16, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(46, 1), (49, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (31, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := -1, powers := [(3, 1), (4, 1), (9, 1), (22, 1), (41, 1), (54, 1)] }, { coefficient := 1, powers := [(4, 1), (7, 1), (9, 1), (16, 1), (41, 1), (44, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (7, 1), (9, 1), (16, 1), (41, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (7, 1), (9, 1), (41, 1), (42, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (7, 1), (9, 1), (41, 1), (46, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (28, 1), (41, 1), (50, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (31, 1), (41, 1), (42, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (9, 1), (31, 1), (41, 1), (46, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (9, 1), (41, 1), (42, 1), (49, 1), (54, 1), (56, 2)] }, { coefficient := 1, powers := [(4, 1), (40, 1), (52, 1), (56, 2)] }, { coefficient := 1, powers := [(4, 1), (42, 1), (49, 1), (56, 2)] }, { coefficient := 1, powers := [(4, 1), (44, 1), (46, 1), (56, 2)] }, { coefficient := 1, powers := [(9, 1), (16, 1), (24, 1), (41, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (16, 1), (41, 1), (49, 1), (54, 1), (56, 1)] }, { coefficient := -1, powers := [(9, 1), (41, 1), (46, 1), (49, 1), (54, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (28, 1), (46, 1), (49, 1), (56, 1)] }, { coefficient := 1, powers := [(4, 1), (31, 1), (44, 1), (46, 1), (56, 1)] }, { coefficient := -1, powers := [(4, 1), (31, 1)] }, { coefficient := 1, powers := [(4, 1), (37, 1), (40, 1), (46, 1), (56, 1)] }]
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
    (values : Fin 59 → R) :
    ¬ ∀ index : Fin 28,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((1 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (1 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (1 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalB4Certificate.selectedHasNoCommonZero

end Krenn.FrozenCase0NoncollapseType01Chart3BothLiveSumNonzeroB1TerminalB4Certificate
