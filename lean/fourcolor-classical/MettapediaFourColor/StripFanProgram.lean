import MettapediaFourColor.BoundaryFourFanRepair
import MettapediaFourColor.StripProtectedEndsGeometry

/-!
# Seven source vertices from a fixed sequence of boundary insertions

The actual D0099 source, with core vertex 2 omitted, is built by seven
three- or four-neighbour insertions. Each step retains a Kempe-closed
relation and reconstructs a colouring of the entire graph built so far.
The initial exterior is unrestricted apart from its ordered source edges
and Kempe closure. Earlier interior colours may change.
-/

namespace FourColor.StripFanProgram

open Color KempeBoundarySplit StripResponseSummary StripSourceExtension
open StripPartialColouring TriangleStripAnchors

variable {V : Type*} (H : SimpleGraph V) (p : Fin 11 → V)

def ring0 := [(p 0),(p 1),(p 2),(p 3),(p 4),(p 5),(p 6),(p 7),(p 8),(p 9),(p 10)]
def graph1 := BoundaryFanRepair.grow H (p 6) (p 7) (p 8)
def ring1 := [(some (p 6)),(none),(some (p 8)),(some (p 9)),(some (p 10)),(some (p 0)),(some (p 1)),(some (p 2)),(some (p 3)),(some (p 4)),(some (p 5))]

def graph2 := BoundaryFourFanRepair.grow (graph1 H p) (some (p 4)) (some (p 5)) (some (p 6)) (none)
def ring2 := [(some (some (p 4))),(none),(some (none)),(some (some (p 8))),(some (some (p 9))),(some (some (p 10))),(some (some (p 0))),(some (some (p 1))),(some (some (p 2))),(some (some (p 3)))]

def graph3 := BoundaryFanRepair.grow (graph2 H p) (none) (some (none)) (some (some (p 8)))
def ring3 := [(some (none)),(none),(some (some (some (p 8)))),(some (some (some (p 9)))),(some (some (some (p 10)))),(some (some (some (p 0)))),(some (some (some (p 1)))),(some (some (some (p 2)))),(some (some (some (p 3)))),(some (some (some (p 4))))]

def graph4 := BoundaryFanRepair.grow (graph3 H p) (some (some (some (p 10)))) (some (some (some (p 0)))) (some (some (some (p 1))))
def ring4 := [(some (some (some (some (p 10))))),(none),(some (some (some (some (p 1))))),(some (some (some (some (p 2))))),(some (some (some (some (p 3))))),(some (some (some (some (p 4))))),(some (some (none))),(some (none)),(some (some (some (some (p 8))))),(some (some (some (some (p 9)))))]

def graph5 := BoundaryFourFanRepair.grow (graph4 H p) (none) (some (some (some (some (p 1))))) (some (some (some (some (p 2))))) (some (some (some (some (p 3)))))
def ring5 := [(some (none)),(none),(some (some (some (some (some (p 3)))))),(some (some (some (some (some (p 4)))))),(some (some (some (none)))),(some (some (none))),(some (some (some (some (some (p 8)))))),(some (some (some (some (some (p 9)))))),(some (some (some (some (some (p 10))))))]

def graph6 := BoundaryFourFanRepair.grow (graph5 H p) (some (some (some (some (some (p 9)))))) (some (some (some (some (some (p 10)))))) (some (none)) (none)
def ring6 := [(some (some (some (some (some (some (p 9))))))),(none),(some (none)),(some (some (some (some (some (some (p 3))))))),(some (some (some (some (some (some (p 4))))))),(some (some (some (some (none))))),(some (some (some (none)))),(some (some (some (some (some (some (p 8)))))))]

def graph7 := BoundaryFourFanRepair.grow (graph6 H p) (some (some (some (none)))) (some (some (some (some (some (some (p 8))))))) (some (some (some (some (some (some (p 9))))))) (none)
def ring7 := [(some (some (some (some (none))))),(none),(some (none)),(some (some (none))),(some (some (some (some (some (some (some (p 3)))))))),(some (some (some (some (some (some (some (p 4)))))))),(some (some (some (some (some (none))))))]

variable (embedding : ∀ i j, input0099.graph.Adj (port i) (port j) → H.Adj (p i) (p j))
  (initial : KempeClosed (GraphTrace H (ring0 p)))

include embedding initial

theorem closed1 : KempeClosed (GraphTrace (graph1 H p) (ring1 p)) := by
  have hr := BoundaryFourFanRepair.rotate_closed H (ring0 p) 6 initial
  change KempeClosed (GraphTrace (BoundaryFanRepair.grow H (p 6) (p 7) (p 8)) (BoundaryFanRepair.newPorts (p 6) (p 8) [(p 9),(p 10),(p 0),(p 1),(p 2),(p 3),(p 4),(p 5)]))
  apply BoundaryFourFanRepair.three_closed H (p 6) (p 7) (p 8) [(p 9),(p 10),(p 0),(p 1),(p 2),(p 3),(p 4),(p 5)]
  · change H.Adj (p 6) (p 7)
    exact embedding 6 7 (by decide +kernel)
  · change H.Adj (p 7) (p 8)
    exact embedding 7 8 (by decide +kernel)
  · simpa [ring0,BoundaryFanRepair.oldPorts,List.rotate] using hr

theorem closed2 : KempeClosed (GraphTrace (graph2 H p) (ring2 p)) := by
  have hr := BoundaryFourFanRepair.rotate_closed (graph1 H p) (ring1 p) 9 (closed1 H p embedding initial)
  change KempeClosed (GraphTrace (BoundaryFourFanRepair.grow (graph1 H p) (some (p 4)) (some (p 5)) (some (p 6)) (none)) (BoundaryFourFanRepair.newPorts (some (p 4)) (none) [(some (p 8)),(some (p 9)),(some (p 10)),(some (p 0)),(some (p 1)),(some (p 2)),(some (p 3))]))
  apply BoundaryFourFanRepair.closed (graph1 H p) (some (p 4)) (some (p 5)) (some (p 6)) (none) [(some (p 8)),(some (p 9)),(some (p 10)),(some (p 0)),(some (p 1)),(some (p 2)),(some (p 3))]
  · change H.Adj (p 4) (p 5)
    exact embedding 4 5 (by decide +kernel)
  · change H.Adj (p 5) (p 6)
    exact embedding 5 6 (by decide +kernel)
  · simp [graph1,BoundaryFanRepair.grow,BoundaryFourFanRepair.grow]
  · simpa [ring1,BoundaryFourFanRepair.oldPorts,List.rotate] using hr

theorem closed3 : KempeClosed (GraphTrace (graph3 H p) (ring3 p)) := by
  have hr := BoundaryFourFanRepair.rotate_closed (graph2 H p) (ring2 p) 1 (closed2 H p embedding initial)
  change KempeClosed (GraphTrace (BoundaryFanRepair.grow (graph2 H p) (none) (some (none)) (some (some (p 8)))) (BoundaryFanRepair.newPorts (none) (some (some (p 8))) [(some (some (p 9))),(some (some (p 10))),(some (some (p 0))),(some (some (p 1))),(some (some (p 2))),(some (some (p 3))),(some (some (p 4)))]))
  apply BoundaryFourFanRepair.three_closed (graph2 H p) (none) (some (none)) (some (some (p 8))) [(some (some (p 9))),(some (some (p 10))),(some (some (p 0))),(some (some (p 1))),(some (some (p 2))),(some (some (p 3))),(some (some (p 4)))]
  · simp [graph1,graph2,BoundaryFanRepair.grow,BoundaryFourFanRepair.grow]
  · simp [graph1,graph2,BoundaryFanRepair.grow,BoundaryFourFanRepair.grow]
  · simpa [ring2,BoundaryFanRepair.oldPorts,List.rotate] using hr

theorem closed4 : KempeClosed (GraphTrace (graph4 H p) (ring4 p)) := by
  have hr := BoundaryFourFanRepair.rotate_closed (graph3 H p) (ring3 p) 4 (closed3 H p embedding initial)
  change KempeClosed (GraphTrace (BoundaryFanRepair.grow (graph3 H p) (some (some (some (p 10)))) (some (some (some (p 0)))) (some (some (some (p 1))))) (BoundaryFanRepair.newPorts (some (some (some (p 10)))) (some (some (some (p 1)))) [(some (some (some (p 2)))),(some (some (some (p 3)))),(some (some (some (p 4)))),(some (none)),(none),(some (some (some (p 8)))),(some (some (some (p 9))))]))
  apply BoundaryFourFanRepair.three_closed (graph3 H p) (some (some (some (p 10)))) (some (some (some (p 0)))) (some (some (some (p 1)))) [(some (some (some (p 2)))),(some (some (some (p 3)))),(some (some (some (p 4)))),(some (none)),(none),(some (some (some (p 8)))),(some (some (some (p 9))))]
  · change H.Adj (p 10) (p 0)
    exact embedding 10 0 (by decide +kernel)
  · change H.Adj (p 0) (p 1)
    exact embedding 0 1 (by decide +kernel)
  · simpa [ring3,BoundaryFanRepair.oldPorts,List.rotate] using hr

theorem closed5 : KempeClosed (GraphTrace (graph5 H p) (ring5 p)) := by
  have hr := BoundaryFourFanRepair.rotate_closed (graph4 H p) (ring4 p) 1 (closed4 H p embedding initial)
  change KempeClosed (GraphTrace (BoundaryFourFanRepair.grow (graph4 H p) (none) (some (some (some (some (p 1))))) (some (some (some (some (p 2))))) (some (some (some (some (p 3)))))) (BoundaryFourFanRepair.newPorts (none) (some (some (some (some (p 3))))) [(some (some (some (some (p 4))))),(some (some (none))),(some (none)),(some (some (some (some (p 8))))),(some (some (some (some (p 9))))),(some (some (some (some (p 10)))))]))
  apply BoundaryFourFanRepair.closed (graph4 H p) (none) (some (some (some (some (p 1))))) (some (some (some (some (p 2))))) (some (some (some (some (p 3))))) [(some (some (some (some (p 4))))),(some (some (none))),(some (none)),(some (some (some (some (p 8))))),(some (some (some (some (p 9))))),(some (some (some (some (p 10)))))]
  · simp [graph1,graph2,graph3,graph4,BoundaryFanRepair.grow,BoundaryFourFanRepair.grow]
  · change H.Adj (p 1) (p 2)
    exact embedding 1 2 (by decide +kernel)
  · change H.Adj (p 2) (p 3)
    exact embedding 2 3 (by decide +kernel)
  · simpa [ring4,BoundaryFourFanRepair.oldPorts,List.rotate] using hr

theorem closed6 : KempeClosed (GraphTrace (graph6 H p) (ring6 p)) := by
  have hr := BoundaryFourFanRepair.rotate_closed (graph5 H p) (ring5 p) 7 (closed5 H p embedding initial)
  change KempeClosed (GraphTrace (BoundaryFourFanRepair.grow (graph5 H p) (some (some (some (some (some (p 9)))))) (some (some (some (some (some (p 10)))))) (some (none)) (none)) (BoundaryFourFanRepair.newPorts (some (some (some (some (some (p 9)))))) (none) [(some (some (some (some (some (p 3)))))),(some (some (some (some (some (p 4)))))),(some (some (some (none)))),(some (some (none))),(some (some (some (some (some (p 8))))))]))
  apply BoundaryFourFanRepair.closed (graph5 H p) (some (some (some (some (some (p 9)))))) (some (some (some (some (some (p 10)))))) (some (none)) (none) [(some (some (some (some (some (p 3)))))),(some (some (some (some (some (p 4)))))),(some (some (some (none)))),(some (some (none))),(some (some (some (some (some (p 8))))))]
  · change H.Adj (p 9) (p 10)
    exact embedding 9 10 (by decide +kernel)
  · simp [graph1,graph2,graph3,graph4,graph5,BoundaryFanRepair.grow,BoundaryFourFanRepair.grow]
  · simp [graph1,graph2,graph3,graph4,graph5,BoundaryFanRepair.grow,BoundaryFourFanRepair.grow]
  · simpa [ring5,BoundaryFourFanRepair.oldPorts,List.rotate] using hr

theorem closed7 : KempeClosed (GraphTrace (graph7 H p) (ring7 p)) := by
  have hr := BoundaryFourFanRepair.rotate_closed (graph6 H p) (ring6 p) 6 (closed6 H p embedding initial)
  change KempeClosed (GraphTrace (BoundaryFourFanRepair.grow (graph6 H p) (some (some (some (none)))) (some (some (some (some (some (some (p 8))))))) (some (some (some (some (some (some (p 9))))))) (none)) (BoundaryFourFanRepair.newPorts (some (some (some (none)))) (none) [(some (none)),(some (some (some (some (some (some (p 3))))))),(some (some (some (some (some (some (p 4))))))),(some (some (some (some (none)))))]))
  apply BoundaryFourFanRepair.closed (graph6 H p) (some (some (some (none)))) (some (some (some (some (some (some (p 8))))))) (some (some (some (some (some (some (p 9))))))) (none) [(some (none)),(some (some (some (some (some (some (p 3))))))),(some (some (some (some (some (some (p 4))))))),(some (some (some (some (none)))))]
  · simp [graph1,graph2,graph3,graph4,graph5,graph6,BoundaryFanRepair.grow,BoundaryFourFanRepair.grow]
  · change H.Adj (p 8) (p 9)
    exact embedding 8 9 (by decide +kernel)
  · simp [graph1,graph2,graph3,graph4,graph5,graph6,BoundaryFanRepair.grow,BoundaryFourFanRepair.grow]
  · simpa [ring6,BoundaryFourFanRepair.oldPorts,List.rotate] using hr

theorem colourable (C : H.Coloring Color) : Nonempty ((graph7 H p).Coloring Color) := by
  obtain ⟨C1⟩ := BoundaryFourFanRepair.three_colourable H (p 6) (p 7) (p 8) C
  have h2 := BoundaryFourFanRepair.rotate_closed (graph1 H p) (ring1 p) 9 (closed1 H p embedding initial)
  have h2' : KempeClosed (GraphTrace (graph1 H p) (BoundaryFourFanRepair.oldPorts (some (p 4)) (some (p 5)) (some (p 6)) (none) [(some (p 8)),(some (p 9)),(some (p 10)),(some (p 0)),(some (p 1)),(some (p 2)),(some (p 3))])) := by
    simpa [ring1,BoundaryFourFanRepair.oldPorts,List.rotate] using h2
  obtain ⟨C2⟩ := BoundaryFourFanRepair.colourable (graph1 H p) (some (p 4)) (some (p 5)) (some (p 6)) (none) [(some (p 8)),(some (p 9)),(some (p 10)),(some (p 0)),(some (p 1)),(some (p 2)),(some (p 3))] h2' C1
  obtain ⟨C3⟩ := BoundaryFourFanRepair.three_colourable (graph2 H p) (none) (some (none)) (some (some (p 8))) C2
  obtain ⟨C4⟩ := BoundaryFourFanRepair.three_colourable (graph3 H p) (some (some (some (p 10)))) (some (some (some (p 0)))) (some (some (some (p 1)))) C3
  have h5 := BoundaryFourFanRepair.rotate_closed (graph4 H p) (ring4 p) 1 (closed4 H p embedding initial)
  have h5' : KempeClosed (GraphTrace (graph4 H p) (BoundaryFourFanRepair.oldPorts (none) (some (some (some (some (p 1))))) (some (some (some (some (p 2))))) (some (some (some (some (p 3))))) [(some (some (some (some (p 4))))),(some (some (none))),(some (none)),(some (some (some (some (p 8))))),(some (some (some (some (p 9))))),(some (some (some (some (p 10)))))])) := by
    simpa [ring4,BoundaryFourFanRepair.oldPorts,List.rotate] using h5
  obtain ⟨C5⟩ := BoundaryFourFanRepair.colourable (graph4 H p) (none) (some (some (some (some (p 1))))) (some (some (some (some (p 2))))) (some (some (some (some (p 3))))) [(some (some (some (some (p 4))))),(some (some (none))),(some (none)),(some (some (some (some (p 8))))),(some (some (some (some (p 9))))),(some (some (some (some (p 10)))))] h5' C4
  have h6 := BoundaryFourFanRepair.rotate_closed (graph5 H p) (ring5 p) 7 (closed5 H p embedding initial)
  have h6' : KempeClosed (GraphTrace (graph5 H p) (BoundaryFourFanRepair.oldPorts (some (some (some (some (some (p 9)))))) (some (some (some (some (some (p 10)))))) (some (none)) (none) [(some (some (some (some (some (p 3)))))),(some (some (some (some (some (p 4)))))),(some (some (some (none)))),(some (some (none))),(some (some (some (some (some (p 8))))))])) := by
    simpa [ring5,BoundaryFourFanRepair.oldPorts,List.rotate] using h6
  obtain ⟨C6⟩ := BoundaryFourFanRepair.colourable (graph5 H p) (some (some (some (some (some (p 9)))))) (some (some (some (some (some (p 10)))))) (some (none)) (none) [(some (some (some (some (some (p 3)))))),(some (some (some (some (some (p 4)))))),(some (some (some (none)))),(some (some (none))),(some (some (some (some (some (p 8))))))] h6' C5
  have h7 := BoundaryFourFanRepair.rotate_closed (graph6 H p) (ring6 p) 6 (closed6 H p embedding initial)
  have h7' : KempeClosed (GraphTrace (graph6 H p) (BoundaryFourFanRepair.oldPorts (some (some (some (none)))) (some (some (some (some (some (some (p 8))))))) (some (some (some (some (some (some (p 9))))))) (none) [(some (none)),(some (some (some (some (some (some (p 3))))))),(some (some (some (some (some (some (p 4))))))),(some (some (some (some (none)))))])) := by
    simpa [ring6,BoundaryFourFanRepair.oldPorts,List.rotate] using h7
  obtain ⟨C7⟩ := BoundaryFourFanRepair.colourable (graph6 H p) (some (some (some (none)))) (some (some (some (some (some (some (p 8))))))) (some (some (some (some (some (some (p 9))))))) (none) [(some (none)),(some (some (some (some (some (some (p 3))))))),(some (some (some (some (some (some (p 4))))))),(some (some (some (some (none)))))] h7' C6
  exact ⟨C7⟩

end FourColor.StripFanProgram
