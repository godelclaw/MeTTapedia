import KrennSparseCertificate

/-!
A selected-row reflection of a strict frozen certificate.
The surrounding carrier tree supplies the semantic route from these
rows to the shared root system and the chart assumptions.
-/

namespace Krenn.Component45.SelectedLeafB4_1

open Krenn.SparseCertificate
open MvPolynomial

def systemSHA256 : String := "4189bb980f299629d9dc9722128bf523ee4f9c6d349d8e074d7263694c99e58a"
def certificateSHA256 : String := "0241e2f2d60d7d6520d2990000ea060e0926af1a2a670d144b0e85fad6f1426a"

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedSourceIndices : Fin 39 → Fin 566 := ![
  4,
  26,
  40,
  42,
  46,
  48,
  200,
  201,
  212,
  220,
  240,
  244,
  245,
  246,
  249,
  252,
  283,
  284,
  360,
  364,
  367,
  379,
  380,
  386,
  388,
  410,
  504,
  513,
  514,
  529,
  530,
  549,
  558,
  559,
  560,
  561,
  562,
  564,
  565
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def selectedEquations : Fin 39 → SparsePoly (Fin 59) := ![
  [{ coefficient := 1, powers := [(6, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(16, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(25, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(28, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (45, 1)] }, { coefficient := 1, powers := [(25, 1), (45, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (46, 1)] }, { coefficient := 1, powers := [(25, 1), (46, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (36, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1)] }],
  [{ coefficient := 1, powers := [(10, 1), (25, 1)] }, { coefficient := 1, powers := [(15, 1), (20, 1)] }],
  [{ coefficient := 1, powers := [(21, 1), (48, 1)] }, { coefficient := 1, powers := [(21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (49, 1)] }, { coefficient := 1, powers := [(29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(26, 1), (41, 1)] }, { coefficient := 1, powers := [(26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(29, 1), (45, 1)] }, { coefficient := 1, powers := [(36, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(30, 1), (41, 1)] }, { coefficient := 1, powers := [(30, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1), (49, 1)] }, { coefficient := 1, powers := [(49, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (21, 1), (55, 1)] }, { coefficient := 1, powers := [(21, 1)] }],
  [{ coefficient := 1, powers := [(6, 1), (24, 1), (55, 1)] }, { coefficient := 1, powers := [(24, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (46, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1)] }],
  [{ coefficient := 1, powers := [(5, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (48, 1)] }, { coefficient := 1, powers := [(18, 1), (21, 1), (52, 1)] }],
  [{ coefficient := 1, powers := [(8, 1), (55, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (41, 1)] }, { coefficient := 1, powers := [(18, 1), (26, 1), (44, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (50, 1)] }, { coefficient := 1, powers := [(30, 1), (42, 1)] }, { coefficient := 1, powers := [(33, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(24, 1), (53, 1)] }, { coefficient := 1, powers := [(30, 1), (46, 1)] }, { coefficient := 1, powers := [(36, 1), (39, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (41, 1), (53, 1)] }, { coefficient := 1, powers := [(26, 1), (45, 1)] }, { coefficient := 1, powers := [(53, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (42, 1), (52, 1)] }, { coefficient := 1, powers := [(21, 1), (49, 1)] }, { coefficient := 1, powers := [(42, 1)] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (55, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (55, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (55, 1)] }],
  [{ coefficient := 1, powers := [(4, 1), (25, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (25, 1), (44, 1)] }, { coefficient := 1, powers := [(15, 1), (25, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (44, 1)] }, { coefficient := 1, powers := [(6, 1), (55, 1)] }, { coefficient := 1, powers := [(25, 1), (41, 1)] }, { coefficient := 1, powers := [(25, 1), (44, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (48, 1)] }, { coefficient := 1, powers := [(3, 1), (55, 1)] }, { coefficient := 1, powers := [(20, 1), (48, 1)] }, { coefficient := 1, powers := [(20, 1), (52, 1)] }, { coefficient := 1, powers := [] }],
  [{ coefficient := 1, powers := [(4, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (55, 1)] }, { coefficient := 1, powers := [(10, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (52, 1)] }, { coefficient := 1, powers := [(15, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (48, 1)] }, { coefficient := 1, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(28, 1), (41, 1)] }, { coefficient := 1, powers := [(28, 1), (44, 1)] }, { coefficient := 1, powers := [(32, 1), (38, 1)] }, { coefficient := 1, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := 1, powers := [(7, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(7, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(7, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(11, 1), (29, 1), (46, 1)] }, { coefficient := 1, powers := [(16, 1), (24, 1), (49, 1)] }, { coefficient := 1, powers := [(16, 1), (29, 1), (42, 1)] }],
  [{ coefficient := 1, powers := [(1, 1), (38, 1), (55, 1)] }, { coefficient := 1, powers := [(1, 1), (41, 1), (52, 1)] }, { coefficient := 1, powers := [(1, 1), (44, 1), (48, 1)] }, { coefficient := 1, powers := [(4, 1), (28, 1), (55, 1)] }, { coefficient := 1, powers := [(4, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(4, 1), (35, 1), (48, 1)] }, { coefficient := 1, powers := [(7, 1), (23, 1), (55, 1)] }, { coefficient := 1, powers := [(7, 1), (32, 1), (44, 1)] }, { coefficient := 1, powers := [(7, 1), (35, 1), (41, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (52, 1)] }, { coefficient := 1, powers := [(10, 1), (28, 1), (44, 1)] }, { coefficient := 1, powers := [(10, 1), (35, 1), (38, 1)] }, { coefficient := 1, powers := [(15, 1), (23, 1), (48, 1)] }, { coefficient := 1, powers := [(15, 1), (28, 1), (41, 1)] }, { coefficient := 1, powers := [(15, 1), (32, 1), (38, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(2, 1), (39, 1), (56, 1)] }, { coefficient := 1, powers := [(2, 1), (42, 1), (53, 1)] }, { coefficient := 1, powers := [(2, 1), (46, 1), (50, 1)] }, { coefficient := 1, powers := [(5, 1), (30, 1), (56, 1)] }, { coefficient := 1, powers := [(5, 1), (33, 1), (53, 1)] }, { coefficient := 1, powers := [(5, 1), (36, 1), (50, 1)] }, { coefficient := 1, powers := [(8, 1), (24, 1), (56, 1)] }, { coefficient := 1, powers := [(8, 1), (33, 1), (46, 1)] }, { coefficient := 1, powers := [(8, 1), (36, 1), (42, 1)] }, { coefficient := 1, powers := [(13, 1), (24, 1), (53, 1)] }, { coefficient := 1, powers := [(13, 1), (30, 1), (46, 1)] }, { coefficient := 1, powers := [(13, 1), (36, 1), (39, 1)] }, { coefficient := 1, powers := [(19, 1), (24, 1), (50, 1)] }, { coefficient := 1, powers := [(19, 1), (30, 1), (42, 1)] }, { coefficient := 1, powers := [(19, 1), (33, 1), (39, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (57, 1)] }, { coefficient := -1, powers := [] }],
  [{ coefficient := 1, powers := [(1, 1)] }],
  [{ coefficient := 1, powers := [(2, 1)] }],
  [{ coefficient := 1, powers := [(41, 1)] }],
  [{ coefficient := 1, powers := [(42, 1), (58, 1)] }, { coefficient := -1, powers := [] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
def multipliers : Fin 39 → SparsePoly (Fin 59) := ![
  [{ coefficient := 2, powers := [(4, 1), (5, 1), (30, 1), (32, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (5, 1), (30, 1), (35, 1), (48, 1), (55, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (24, 1), (32, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (24, 1), (35, 1), (48, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (30, 1), (32, 1), (44, 1), (55, 1)] }, { coefficient := -2, powers := [(5, 1), (10, 1), (30, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := -2, powers := [(8, 1), (10, 1), (24, 1), (35, 1), (38, 1), (55, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (32, 1), (49, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (35, 1), (48, 1), (49, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (5, 1), (23, 1), (26, 1), (33, 1), (45, 1), (55, 1), (57, 2), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (8, 1), (23, 1), (33, 1), (46, 1), (55, 1), (57, 2), (58, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (23, 1), (26, 1), (33, 1), (45, 1), (55, 1), (57, 2), (58, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (8, 1), (23, 1), (33, 1), (46, 1), (55, 1), (57, 2), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (7, 1), (23, 1), (55, 2), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (10, 1), (23, 1), (52, 1), (55, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(3, 1), (15, 1), (23, 1), (48, 1), (55, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (5, 1), (26, 1), (32, 1), (33, 1), (45, 1), (57, 2), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (5, 1), (26, 1), (33, 1), (35, 1), (45, 1), (48, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (32, 1), (33, 1), (46, 1), (57, 2), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (33, 1), (35, 1), (46, 1), (48, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(4, 1), (21, 1), (32, 1), (44, 1), (49, 1), (57, 1), (58, 2)] }, { coefficient := -1, powers := [(4, 1), (23, 1), (55, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (10, 1), (23, 1), (26, 1), (33, 1), (45, 1), (55, 1), (57, 2), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (23, 1), (26, 1), (33, 1), (45, 1), (55, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (26, 1), (32, 1), (33, 1), (44, 1), (45, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (26, 1), (33, 1), (35, 1), (38, 1), (45, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (10, 1), (23, 1), (33, 1), (46, 1), (55, 1), (57, 2), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (8, 1), (23, 1), (33, 1), (46, 1), (55, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (23, 1), (52, 1), (55, 1), (58, 1)] }, { coefficient := -2, powers := [(7, 1), (35, 1), (38, 1), (55, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (24, 1), (35, 1), (44, 1), (45, 1), (49, 1), (58, 1)] }, { coefficient := -2, powers := [(8, 1), (10, 1), (33, 1), (35, 1), (38, 1), (46, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (23, 1), (44, 1), (49, 1), (57, 1), (58, 2)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (48, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(10, 1), (23, 1), (52, 2), (58, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (52, 1), (57, 1), (58, 1)] }, { coefficient := -2, powers := [(10, 1), (35, 1), (38, 1), (52, 1), (58, 1)] }, { coefficient := -2, powers := [(15, 1), (23, 1), (48, 1), (52, 1), (58, 1)] }, { coefficient := -2, powers := [(15, 1), (35, 1), (38, 1), (48, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(7, 1), (55, 1), (58, 1)] }, { coefficient := -2, powers := [(10, 1), (52, 1), (58, 1)] }, { coefficient := -2, powers := [(15, 1), (44, 1), (58, 1)] }, { coefficient := -2, powers := [(15, 1), (48, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (11, 1), (32, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (10, 1), (35, 1), (45, 1)] }, { coefficient := 2, powers := [(5, 1), (16, 1), (32, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (16, 1), (35, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (5, 1), (23, 1), (26, 1), (33, 1), (55, 1), (57, 2)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (23, 1), (26, 1), (33, 1), (55, 1), (57, 2)] }, { coefficient := 2, powers := [(4, 1), (5, 1), (26, 1), (32, 1), (33, 1), (57, 2)] }, { coefficient := -2, powers := [(4, 1), (5, 1), (26, 1), (33, 1), (35, 1), (48, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (10, 1), (23, 1), (26, 1), (33, 1), (55, 1), (57, 2)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (23, 1), (26, 1), (33, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (26, 1), (32, 1), (33, 1), (44, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (10, 1), (26, 1), (33, 1), (35, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (8, 1), (23, 1), (33, 1), (55, 1), (57, 2)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (8, 1), (23, 1), (33, 1), (55, 1), (57, 2)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (32, 1), (33, 1), (57, 2)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (33, 1), (35, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (10, 1), (23, 1), (33, 1), (55, 1), (57, 2)] }, { coefficient := 2, powers := [(7, 1), (8, 1), (23, 1), (33, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (33, 1), (35, 1), (38, 1), (57, 1)] }],
  [{ coefficient := -2, powers := [(5, 1), (32, 1), (50, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (35, 1), (48, 1), (50, 1)] }, { coefficient := -2, powers := [(8, 1), (32, 1), (42, 1), (57, 1)] }, { coefficient := 2, powers := [(8, 1), (35, 1), (42, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(23, 1), (48, 1), (57, 1)] }, { coefficient := 1, powers := [(23, 1), (52, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (18, 1), (23, 1), (36, 1), (50, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (18, 1), (23, 1), (36, 1), (50, 1), (57, 1)] }, { coefficient := 2, powers := [(6, 1), (7, 1), (18, 1), (32, 1), (36, 1), (44, 1), (50, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (23, 1), (36, 1), (50, 1), (57, 1)] }, { coefficient := -2, powers := [(7, 1), (18, 1), (23, 1), (36, 1), (50, 1)] }],
  [{ coefficient := -2, powers := [(8, 1), (10, 1), (35, 1), (45, 1)] }, { coefficient := -2, powers := [(8, 1), (16, 1), (32, 1), (44, 1)] }, { coefficient := 2, powers := [(8, 1), (16, 1), (32, 1), (57, 1)] }, { coefficient := -2, powers := [(8, 1), (16, 1), (35, 1), (48, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (18, 1), (23, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (18, 1), (23, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (18, 1), (23, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -2, powers := [(7, 1), (18, 1), (23, 1), (36, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(5, 1), (10, 1), (35, 1), (50, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (35, 1), (42, 1)] }],
  [{ coefficient := 2, powers := [(0, 1), (4, 1), (5, 1), (32, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (4, 1), (5, 1), (35, 1), (48, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (7, 1), (32, 1), (44, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (10, 1), (35, 1), (38, 1), (56, 1)] }, { coefficient := 2, powers := [(4, 1), (5, 1), (25, 1), (32, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (5, 1), (25, 1), (35, 1), (48, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (25, 1), (32, 1), (44, 1), (56, 1)] }, { coefficient := -2, powers := [(5, 1), (10, 1), (25, 1), (35, 1), (38, 1), (56, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (21, 1), (32, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (24, 1), (35, 1), (45, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (23, 1), (57, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (32, 1), (49, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (49, 1), (57, 1), (58, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (8, 1), (32, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (35, 1), (48, 1), (56, 1)] }, { coefficient := -2, powers := [(7, 1), (19, 1), (32, 1), (44, 1), (50, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (35, 1), (38, 1), (56, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (35, 1), (45, 1), (49, 1)] }],
  [{ coefficient := 2, powers := [(6, 1), (7, 1), (32, 1), (44, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(7, 1), (32, 1), (44, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (23, 1), (36, 1), (50, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (23, 1), (36, 1), (50, 1), (57, 1)] }, { coefficient := -2, powers := [(6, 1), (7, 1), (32, 1), (36, 1), (44, 1), (50, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (23, 1), (36, 1), (50, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (36, 1), (50, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (23, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (23, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (23, 1), (36, 1), (42, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (36, 1), (42, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (19, 1), (23, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (19, 1), (23, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (19, 1), (32, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (19, 1), (35, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (19, 1), (23, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (23, 1), (55, 1)] }, { coefficient := 2, powers := [(7, 1), (19, 1), (32, 1), (44, 1)] }, { coefficient := 2, powers := [(10, 1), (19, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (13, 1), (23, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (13, 1), (23, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (13, 1), (32, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (13, 1), (35, 1), (48, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (13, 1), (23, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (13, 1), (23, 1), (55, 1)] }, { coefficient := 2, powers := [(7, 1), (13, 1), (32, 1), (44, 1)] }, { coefficient := 2, powers := [(10, 1), (13, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (5, 1), (23, 1), (33, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (23, 1), (33, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (5, 1), (32, 1), (33, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (5, 1), (33, 1), (35, 1), (48, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (10, 1), (23, 1), (33, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (23, 1), (33, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (32, 1), (33, 1), (44, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (33, 1), (35, 1), (38, 1)] }],
  [{ coefficient := 2, powers := [(4, 1), (32, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (57, 1), (58, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (23, 1), (56, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (23, 1), (56, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (23, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (56, 1)] }],
  [{ coefficient := 1, powers := [(3, 1), (23, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(23, 1), (52, 1)] }, { coefficient := 1, powers := [(23, 1), (57, 1)] }, { coefficient := -2, powers := [(35, 1), (38, 1)] }],
  [{ coefficient := -2, powers := [(4, 1), (5, 1), (30, 1), (32, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (5, 1), (30, 1), (35, 1), (48, 1), (56, 1)] }, { coefficient := 2, powers := [(4, 1), (21, 1), (32, 1), (49, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (30, 1), (32, 1), (44, 1), (56, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (30, 1), (35, 1), (38, 1), (56, 1)] }, { coefficient := -2, powers := [(8, 1), (10, 1), (24, 1), (35, 1), (45, 1), (49, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (23, 1), (49, 1), (57, 1), (58, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (57, 1)] }],
  [{ coefficient := -1, powers := [(15, 1), (23, 1), (57, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (23, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (23, 1), (25, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(23, 1), (25, 1), (52, 1)] }, { coefficient := 2, powers := [(25, 1), (35, 1), (38, 1)] }, { coefficient := 2, powers := [(28, 1)] }],
  [{ coefficient := 2, powers := [(15, 1)] }],
  [{ coefficient := 2, powers := [(8, 1), (32, 1), (44, 1)] }],
  [{ coefficient := -2, powers := [] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (23, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (23, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (35, 1), (48, 1)] }, { coefficient := -1, powers := [(6, 1), (10, 1), (23, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(7, 1), (23, 1), (55, 1)] }, { coefficient := -2, powers := [(7, 1), (32, 1), (44, 1)] }, { coefficient := -2, powers := [(10, 1), (35, 1), (38, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (5, 1), (23, 1), (26, 1), (33, 1), (45, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (4, 1), (8, 1), (23, 1), (33, 1), (46, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (7, 1), (23, 1), (26, 1), (33, 1), (45, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (7, 1), (8, 1), (23, 1), (33, 1), (46, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (5, 1), (26, 1), (32, 1), (33, 1), (45, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (5, 1), (26, 1), (33, 1), (35, 1), (45, 1), (48, 1)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (32, 1), (33, 1), (46, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (33, 1), (35, 1), (46, 1), (48, 1)] }, { coefficient := -2, powers := [(4, 1), (32, 1), (52, 1)] }, { coefficient := 1, powers := [(5, 1), (6, 1), (10, 1), (23, 1), (26, 1), (33, 1), (45, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (23, 1), (26, 1), (33, 1), (45, 1), (55, 1)] }, { coefficient := 2, powers := [(5, 1), (7, 1), (26, 1), (32, 1), (33, 1), (44, 1), (45, 1)] }, { coefficient := 2, powers := [(5, 1), (10, 1), (26, 1), (33, 1), (35, 1), (38, 1), (45, 1)] }, { coefficient := -1, powers := [(6, 1), (8, 1), (10, 1), (23, 1), (33, 1), (46, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(7, 1), (8, 1), (23, 1), (33, 1), (46, 1), (55, 1)] }, { coefficient := -2, powers := [(8, 1), (10, 1), (33, 1), (35, 1), (38, 1), (46, 1)] }, { coefficient := -2, powers := [(10, 1), (23, 1), (52, 1)] }],
  [{ coefficient := 2, powers := [(38, 1), (55, 1)] }, { coefficient := 2, powers := [(44, 1), (48, 1)] }],
  [{ coefficient := -1, powers := [(0, 1), (4, 1), (23, 1), (42, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (23, 1), (46, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (23, 1), (42, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (23, 1), (46, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (32, 1), (39, 1), (56, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (32, 1), (42, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (32, 1), (46, 1), (50, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (35, 1), (39, 1), (48, 1), (56, 1)] }, { coefficient := 2, powers := [(4, 1), (35, 1), (42, 1), (48, 1), (53, 1)] }, { coefficient := 2, powers := [(4, 1), (35, 1), (46, 1), (48, 1), (50, 1)] }, { coefficient := -2, powers := [(6, 1), (7, 1), (32, 1), (44, 1), (46, 1), (50, 1), (55, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (23, 1), (42, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (10, 1), (23, 1), (46, 1), (50, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (42, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (46, 1), (50, 1), (55, 1)] }, { coefficient := 2, powers := [(7, 1), (32, 1), (39, 1), (44, 1), (56, 1)] }, { coefficient := 2, powers := [(7, 1), (32, 1), (42, 1), (44, 1), (53, 1)] }, { coefficient := 2, powers := [(10, 1), (35, 1), (38, 1), (39, 1), (56, 1)] }, { coefficient := 2, powers := [(10, 1), (35, 1), (38, 1), (42, 1), (53, 1)] }, { coefficient := 2, powers := [(10, 1), (35, 1), (38, 1), (46, 1), (50, 1)] }],
  [{ coefficient := 1, powers := [(0, 2), (4, 1), (5, 1), (23, 1), (33, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 2), (5, 1), (7, 1), (23, 1), (33, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (4, 1), (5, 1), (30, 1), (32, 1), (56, 1), (57, 1)] }, { coefficient := 2, powers := [(0, 1), (4, 1), (5, 1), (30, 1), (35, 1), (48, 1), (56, 1)] }, { coefficient := 2, powers := [(0, 1), (4, 1), (5, 1), (32, 1), (33, 1), (53, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (4, 1), (5, 1), (33, 1), (35, 1), (48, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (5, 1), (6, 1), (10, 1), (23, 1), (33, 1), (53, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (7, 1), (23, 1), (33, 1), (53, 1), (55, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (7, 1), (30, 1), (32, 1), (44, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (7, 1), (32, 1), (33, 1), (44, 1), (53, 1)] }, { coefficient := 2, powers := [(0, 1), (5, 1), (10, 1), (30, 1), (35, 1), (38, 1), (56, 1)] }, { coefficient := -2, powers := [(0, 1), (5, 1), (10, 1), (33, 1), (35, 1), (38, 1), (53, 1)] }, { coefficient := -1, powers := [(0, 1), (15, 1), (23, 1), (57, 1)] }, { coefficient := 2, powers := [(1, 1), (52, 1)] }, { coefficient := -2, powers := [(4, 1), (21, 1), (25, 1), (32, 1), (49, 1), (57, 1), (58, 1)] }, { coefficient := 2, powers := [(7, 1), (35, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (24, 1), (25, 1), (35, 1), (45, 1), (49, 1)] }, { coefficient := -1, powers := [(10, 1), (21, 1), (23, 1), (25, 1), (49, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (25, 1), (57, 1)] }, { coefficient := -1, powers := [(15, 1), (23, 1), (25, 1), (57, 1)] }, { coefficient := -2, powers := [(15, 1), (28, 1)] }],
  [{ coefficient := 1, powers := [(0, 1), (4, 1), (5, 1), (23, 1), (25, 1), (26, 1), (33, 1), (45, 1), (55, 1), (57, 2)] }, { coefficient := -1, powers := [(0, 1), (4, 1), (8, 1), (23, 1), (25, 1), (33, 1), (46, 1), (55, 1), (57, 2)] }, { coefficient := -2, powers := [(0, 1), (4, 1), (32, 1), (52, 1), (57, 1)] }, { coefficient := 1, powers := [(0, 1), (5, 1), (7, 1), (23, 1), (25, 1), (26, 1), (33, 1), (45, 1), (55, 1), (57, 2)] }, { coefficient := -1, powers := [(0, 1), (7, 1), (8, 1), (23, 1), (25, 1), (33, 1), (46, 1), (55, 1), (57, 2)] }, { coefficient := -1, powers := [(0, 1), (10, 1), (23, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (7, 1), (23, 1), (25, 1), (55, 2), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (10, 1), (23, 1), (25, 1), (52, 1), (55, 1), (57, 1)] }, { coefficient := -1, powers := [(3, 1), (15, 1), (23, 1), (25, 1), (48, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (5, 1), (25, 1), (26, 1), (32, 1), (33, 1), (45, 1), (57, 2)] }, { coefficient := -2, powers := [(4, 1), (5, 1), (25, 1), (26, 1), (33, 1), (35, 1), (45, 1), (48, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (8, 1), (25, 1), (32, 1), (33, 1), (46, 1), (57, 2)] }, { coefficient := 2, powers := [(4, 1), (8, 1), (25, 1), (33, 1), (35, 1), (46, 1), (48, 1), (57, 1)] }, { coefficient := 2, powers := [(4, 1), (21, 1), (25, 1), (32, 1), (44, 1), (49, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(4, 1), (23, 1), (25, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(4, 1), (32, 1), (57, 1)] }, { coefficient := -1, powers := [(5, 1), (6, 1), (10, 1), (23, 1), (25, 1), (26, 1), (33, 1), (45, 1), (55, 1), (57, 2)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (23, 1), (25, 1), (26, 1), (33, 1), (45, 1), (55, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (7, 1), (25, 1), (26, 1), (32, 1), (33, 1), (44, 1), (45, 1), (57, 1)] }, { coefficient := -2, powers := [(5, 1), (10, 1), (25, 1), (26, 1), (33, 1), (35, 1), (38, 1), (45, 1), (57, 1)] }, { coefficient := 1, powers := [(6, 1), (8, 1), (10, 1), (23, 1), (25, 1), (33, 1), (46, 1), (55, 1), (57, 2)] }, { coefficient := 2, powers := [(7, 1), (8, 1), (23, 1), (25, 1), (33, 1), (46, 1), (55, 1), (57, 1)] }, { coefficient := 2, powers := [(7, 1), (23, 1), (25, 1), (52, 1), (55, 1)] }, { coefficient := 2, powers := [(7, 1), (25, 1), (35, 1), (38, 1), (55, 1)] }, { coefficient := 2, powers := [(7, 1), (28, 1), (55, 1)] }, { coefficient := -2, powers := [(8, 1), (10, 1), (24, 1), (25, 1), (35, 1), (44, 1), (45, 1), (49, 1)] }, { coefficient := 2, powers := [(8, 1), (10, 1), (25, 1), (33, 1), (35, 1), (38, 1), (46, 1), (57, 1)] }, { coefficient := 1, powers := [(10, 1), (21, 1), (23, 1), (25, 1), (44, 1), (49, 1), (57, 1), (58, 1)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (25, 1), (48, 1), (57, 1)] }, { coefficient := 2, powers := [(10, 1), (23, 1), (25, 1), (52, 2)] }, { coefficient := 1, powers := [(10, 1), (23, 1), (25, 1), (52, 1), (57, 1)] }, { coefficient := -1, powers := [(10, 1), (23, 1), (57, 1)] }, { coefficient := 2, powers := [(10, 1), (25, 1), (35, 1), (38, 1), (52, 1)] }, { coefficient := 2, powers := [(10, 1), (28, 1), (52, 1)] }, { coefficient := 2, powers := [(15, 1), (23, 1), (25, 1), (48, 1), (52, 1)] }, { coefficient := 2, powers := [(15, 1), (25, 1), (35, 1), (38, 1), (48, 1)] }, { coefficient := 2, powers := [(15, 1), (28, 1), (44, 1)] }, { coefficient := 2, powers := [(15, 1), (28, 1), (48, 1)] }]
]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Lean replays the exact selected-row integer certificate. -/
theorem constantIdentity :
    ∑ index, (multipliers index).toPoly *
      (selectedEquations index).toPoly = C (2 : ℤ) := by
  simp (config := { maxSteps := 1000000 })
    [Fin.sum_univ_succ, multipliers, selectedEquations,
    SparsePoly.toPoly, SparseTerm.toPoly]
  ring

/-- The selected rows have no common zero in a characteristic-zero ring. -/
theorem selectedHasNoCommonZero {R : Type*} [CommRing R] [Nontrivial R] [CharZero R]
    (values : Fin 59 → R) :
    ¬ ∀ index : Fin 39,
      eval₂Hom (Int.castRingHom R) values
        (selectedEquations index).toPoly = 0 := by
  have constantNonzero : ((2 : ℤ) : R) ≠ 0 := by
    exact_mod_cast (show (2 : ℤ) ≠ 0 by decide)
  exact noCommonZero_of_sparseConstantCertificate
    selectedEquations multipliers (2 : ℤ)
    constantIdentity constantNonzero values

#print axioms Krenn.Component45.SelectedLeafB4_1.selectedHasNoCommonZero

end Krenn.Component45.SelectedLeafB4_1
