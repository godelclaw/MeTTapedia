import Mettapedia.DocText.MmLean4ReadmeCompositional

open Mettapedia.DocText.MmLean4ReadmeCompositional

def main : IO Unit := do
  IO.FS.writeFile "~/claude/hyperon/metamath/mm-lean4/README.md" mmLean4ReadmeMarkdown

