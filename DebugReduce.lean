import Trident
import Trident.Common.Equiv

open Trident

#eval do
  let contents ← IO.FS.readFile "kernels/reduction_kernel.ttir"
  let allLines := contents.splitOn "\n"
  let filtered := allLines.filterMap (fun rawL =>
        let l := (rawL.splitOn " ").filter (fun s => s != "") |> String.intercalate " "
        let l := if rawL.startsWith "\t" then rawL.replace "\t" "" else l
        if l.isEmpty then none
        else if l.startsWith "module" then none
        else if l.startsWith "}" then none
        else if l.startsWith "tt.func" then none
        else if l.startsWith "tt.return" then none
        else if l.startsWith "#" then none
        else if l.startsWith "//" then none
        else if l.startsWith "attributes" then none
        else if l.contains "tt.divisibility" then none
        else if l.startsWith "%" && (l.splitOn " = ").length == 1 then none
        else some (match l.splitOn " loc(" with
          | head :: _ => head
          | [] => l))
    |> String.intercalate "\n"
  let contentLines := filtered.splitOn "\n"
  let rec collapseReduce (lines : List String) (acc : List String) (inReduce : Bool) (reduceResult : String) : List String :=
    match lines with
    | [] => acc.reverse
    | l :: rest =>
      if l.contains "tt.reduce" && l.contains " = " then
        let resultName := match l.splitOn " = " with | r :: _ => r | [] => "_"
        collapseReduce rest acc true resultName
      else if inReduce && l.startsWith "})" then
        let varName := reduceResult.replace "%" ""
        let newLine := reduceResult ++ " = tt.reduce " ++ varName
        collapseReduce rest (newLine :: acc) false ""
      else if inReduce then
        collapseReduce rest acc inReduce reduceResult
      else
        collapseReduce rest (l :: acc) false ""
  let finalContents := collapseReduce contentLines [] false "" |> String.intercalate "\n"
  IO.println "=== Preprocessed TTIR ==="
  IO.println finalContents
  IO.println "=========================="
  match parseKernelVerbose finalContents with
  | .error e => IO.println s!"Parse error: {e}"
  | .ok kernel => do
      IO.println s!"Parsed {kernel.length} instructions:"
      for instr in kernel do
        IO.println s!"  {instr.result} = {repr instr.op} {instr.args}"
      let bs := 1024
      let x := (List.range bs).map (fun i => Int.ofNat (i + 1))
      let ref := runReductionRef x 0 bs 1
      let got := runReductionParsed kernel x 0 bs 1
      IO.println s!"ref: {ref}"
      IO.println s!"got: {got}"
