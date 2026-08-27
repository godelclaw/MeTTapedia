import Mettapedia.DocText.BridgeReadmeCompositional

open Mettapedia.DocText.BridgeReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "~/claude/lean-projects/mettapedia/Mettapedia/Bridge/README.md" bridgeReadmeMarkdown
