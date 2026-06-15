import Mettapedia.DocText.LogicReadmeCompositional

open Mettapedia.DocText.LogicReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "/home/zar/claude/Mettapedia/lean/mettapedia/Mettapedia/Logic/README.md" logicReadmeMarkdown

