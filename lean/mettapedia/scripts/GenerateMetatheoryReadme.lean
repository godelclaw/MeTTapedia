import Mettapedia.DocText.MetatheoryReadmeCompositional

open Mettapedia.DocText.MetatheoryReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "/home/zar/claude/Mettapedia/lean/mettapedia/Mettapedia/Metatheory/README.md" metatheoryReadmeMarkdown
