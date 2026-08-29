import Mettapedia.DocText.BridgeReadmeCompositional

open Mettapedia.DocText.BridgeReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "Mettapedia/Bridge/README.md" bridgeReadmeMarkdown
