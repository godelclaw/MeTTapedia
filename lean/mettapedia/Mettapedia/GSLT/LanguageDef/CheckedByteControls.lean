import Mettapedia.GSLT.LanguageDef.CheckedByteModules

/-! Positive and refused ownership, reborrowing and loop-control examples. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CheckedBytes

def exampleSignature : Signature := ⟨"example", [], .unit, none, ["heap"], none, some ("allocate", "release")⟩

def readonlyCopies : Plan :=
  .step (.acquire 0 .local)
  (.step (.borrow 1 0 .read false)
  (.step (.borrow 2 1 .read true)
  (.step (.endView 1 .read)
  (.step (.read 2 false)
  (.step (.endView 2 .read)
  (.step (.drop 0 .local) .ret))))))

def nestedBorrow : Plan :=
  .step (.acquire 0 .local)
  (.step (.borrow 1 0 .write)
  (.step (.borrow 2 1 .read)
  (.step (.read 2 false)
  (.step (.endView 2 .read)
  (.step (.read 1 true)
  (.step (.endView 1 .write)
  (.step (.drop 0 .local) .ret)))))))

def loopBody : Plan :=
  .step (.acquire 0 .own)
  (.step (.borrow 1 0 .read)
  (.step (.endView 1 .read)
  (.step (.drop 0 .own)
    (.branch .breakLoop .continueLoop .done))))

def heapLoop : Plan := .loop loopBody .ret

def exampleFunction (body : Plan) : Function := ⟨exampleSignature, [], body⟩

theorem readonlyCopies_admitted :
    admit ⟨[], [exampleFunction readonlyCopies]⟩ = true := by decide

theorem nestedBorrow_admitted :
    admit ⟨[], [exampleFunction nestedBorrow]⟩ = true := by decide

theorem heapLoop_admitted :
    admit ⟨[], [exampleFunction heapLoop]⟩ = true := by decide

def sharedWrite : Plan :=
  .step (.acquire 0 .local)
  (.step (.borrow 1 0 .read)
  (.step (.read 0 true)
  (.step (.endView 1 .read)
  (.step (.drop 0 .local) .ret))))

def danglingRelease : Plan :=
  .step (.acquire 0 .own)
  (.step (.borrow 1 0 .read)
  (.step (.drop 0 .own)
  (.step (.read 1 false)
  (.step (.endView 1 .read) .ret))))

def changedBackedge : Plan :=
  .step (.acquire 0 .own)
  (.loop (.step (.drop 0 .own) .continueLoop)
    (.step (.drop 0 .own) .ret))

def missingPath : Plan := .branch readonlyCopies danglingRelease .done

theorem sharedWrite_refused :
    admit ⟨[], [exampleFunction sharedWrite]⟩ = false := by decide

theorem danglingRelease_refused :
    admit ⟨[], [exampleFunction danglingRelease]⟩ = false := by decide

theorem changedBackedge_refused :
    admit ⟨[], [exampleFunction changedBackedge]⟩ = false := by decide

theorem missingPath_refused :
    admit ⟨[], [exampleFunction missingPath]⟩ = false := by decide

def borrowedSignature : Signature := ⟨"prefix", [.read], .read, some 0, [], none, none⟩

def borrowedReturn : Plan :=
  .step (.borrow 1 0 .read)
  (.step (.borrowResult 1 0 .read)
  (.step (.endView 1 .read)
  (.step (.endView 0 .read) .ret)))

theorem borrowedReturn_admitted :
    admit ⟨[], [⟨borrowedSignature, [(0, .read)], borrowedReturn⟩]⟩ = true := by decide

def localEscape : Plan :=
  .step (.acquire 1 .local)
  (.step (.borrow 2 1 .read)
  (.step (.borrowResult 2 0 .read)
  (.step (.endView 2 .read)
  (.step (.drop 1 .local)
  (.step (.endView 0 .read) .ret)))))

theorem localEscape_refused :
    admit ⟨[], [⟨borrowedSignature, [(0, .read)], localEscape⟩]⟩ = false := by decide

def ownerSignature : Signature := ⟨"identity", [.own], .own, none, [], none, some ("allocate", "release")⟩

theorem ownedTransfer_admitted :
    admit ⟨[], [⟨ownerSignature, [(0, .own)], .step (.take 0) .ret⟩]⟩ = true := by decide

theorem fabricatedOwner_refused :
    admit ⟨[], [exampleFunction (.step (.ownResult 0) (.step (.drop 0 .own) .ret))]⟩ = false := by decide

def transferredCall : Function :=
  ⟨{ ownerSignature with name := "forward" }, [(0, .own)],
    .step (.invoke "identity" [(0, .own)]) .ret⟩

theorem compatibleOwner_admitted :
    admit ⟨[{ ownerSignature with obligation := some "native identity" }], [transferredCall]⟩ = true := by decide

theorem foreignAllocator_refused :
    admit ⟨[{ ownerSignature with
      allocator := some ("other_allocate", "other_release")
      obligation := some "native identity" }], [transferredCall]⟩ = false := by decide

theorem missingAllocator_refused :
    admit ⟨[], [⟨{ ownerSignature with allocator := none }, [(0, .own)],
      .step (.take 0) .ret⟩]⟩ = false := by decide

theorem unrelatedInterface_preserves :
    checkFunction [ownerSignature, { exampleSignature with name := "unrelated" }] transferredCall = true := by
  apply checked_function_extension (supports_append [ownerSignature] _)
  decide

theorem shadowedInterface_refused :
    checkFunction [{ ownerSignature with effects := ["io"] }, ownerSignature] transferredCall = false := by decide

end Mettapedia.GSLT.LanguageDef.CheckedBytes
