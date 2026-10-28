import Mettapedia.Machines.SpaceService

/-! Finite service-profile replays and counterexamples. Native receipts are
checked separately by independent CSP1 clients; these are model computations,
not a C evaluator or a proof about a particular executable. -/

namespace Mettapedia.Machines.SpaceService

deriving instance DecidableEq for Except

#guard (insert .bag (insert .bag [] 7) 7).length = 2
#guard (insert .support (insert .support [] 7) 7).length = 1
#guard ((insert .bag (insert .bag [] 7) 7).erase 7).length = 1
#guard ((insert .support (insert .support [] 7) 7).erase 7).length = 0

private def initial : Store := ⟨1, 0, []⟩
private def written : Store := ⟨1, 1, [7]⟩

#guard conditionalWrite initial 1 0 [7] = .ok written
#guard conditionalWrite written 1 0 [7,7] = .error .stale
#guard retry ⟨⟨11,1,0,[7]⟩,written⟩ ⟨11,1,0,[7]⟩ = .ok written
#guard retry ⟨⟨11,1,0,[7]⟩,written⟩ ⟨11,1,0,[8]⟩ = .error .reusedId
#guard retry ⟨⟨11,1,0,[0,7]⟩,written⟩ ⟨11,1,0,[7]⟩ = .error .reusedId

private def journal : Journal := ⟨initial, [written], []⟩
#guard recovered journal = written
#guard (restart ⟨journal,written⟩).visible = written
#guard acknowledgement ⟨⟨initial,[],[written]⟩,written⟩ = none
#guard recovered (compact journal) = written

private def snapshot : Snapshot := capture 100 3 500 ⟨1,1,[1,2]⟩
#guard observedPage ⟨1,2,[3]⟩ snapshot 100 3 20 0 10 = .ok [1,2]
#guard page snapshot 100 3 500 2 10 = .error .expired
#guard page snapshot 100 3 20 2 10 = .ok []
#guard page snapshot 200 3 20 0 10 = .error .identity
#guard conditionalWrite ⟨1,2,[3]⟩ snapshot.source snapshot.revision [4] = .error .stale

end Mettapedia.Machines.SpaceService
