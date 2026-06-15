import Mettapedia.DocText.BridgeReadmeCompositional

open Mettapedia.DocText.BridgeReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "/home/zar/claude/Mettapedia/lean/mettapedia/Mettapedia/Bridge/README.md" bridgeReadmeMarkdown
