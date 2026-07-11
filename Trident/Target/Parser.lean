import Trident.Target.Dialect

namespace Trident

def parseOp (opName : String) (rest : List String := []) : Option TritonOp :=
  match opName with
  | "tt.make_range" =>
    let sz := match rest with
      | "{end" :: "=" :: szStr :: _ => szStr.toNat?
      | _ => none
    some (.make_range sz)
  | "tt.splat" =>
    let shapeTok := rest.reverse.find? (fun t => t.startsWith "tensor<") |>.getD ""
    let shape := ((shapeTok.splitOn "<").getD 1 "").splitOn "x"
      |>.takeWhile (fun t => t.toNat?.isSome) |>.filterMap (·.toNat?)
    some (.splat shape)
  | "tt.addptr"         => some .addptr
  | "tt.load" => some .load
  | "tt.store" => some .store
  | "tt.loadf" => some .loadf
  | "tt.storef" => some .storef
  | "arith.constantf" =>
    if rest.any (fun t => t.startsWith "dense<") then
      let shapeTok := rest.reverse.find? (fun t => t.startsWith "tensor<") |>.getD ""
      let shape := ((shapeTok.splitOn "<").getD 1 "").splitOn "x"
        |>.takeWhile (fun t => t.toNat?.isSome) |>.filterMap (·.toNat?)
      some (.constant_tensorf 0.0 shape)
    else
      some (.constantf 0.0)
  | "tt.get_program_id" =>
    let axis := match rest with
      | "y" :: _ => 1
      | _        => 0
    some (.get_program_id axis)
  | "tt.get_num_programs" =>
    let axis := match rest with
      | "y" :: _ => 1
      | _        => 0
    some (.get_num_programs axis)
  | "tt.expand_dims" =>
    let axis := match rest with
      | _ :: "{axis" :: "=" :: axisStr :: _ => axisStr.toNat?.getD 0
      | _ => 0
    some (.expand_dims axis)
  | "tt.broadcast" =>
    let shapeTok := rest.reverse.find? (fun t => t.startsWith "tensor<") |>.getD ""
    let shape := ((shapeTok.splitOn "<").getD 1 "").splitOn "x"
      |>.takeWhile (fun t => t.toNat?.isSome) |>.filterMap (·.toNat?)
    some (.broadcast shape)
  | "tt.dot"            => some .dot
  | "tt.reduce_sum" => some (.reduce_sum 0)
  | "tt.reduce_max" => some (.reduce_max 0)
  | "arith.constant" =>
    if rest.any (fun t => t.startsWith "dense<") then
      let denseTok := rest.find? (fun t => t.startsWith "dense<") |>.getD ""
      let valStr := ((denseTok.splitOn "<").getD 1 "").splitOn ">" |>.head?.getD ""
      let shapeTok := rest.reverse.find? (fun t => t.startsWith "tensor<") |>.getD ""
      let shape := ((shapeTok.splitOn "<").getD 1 "").splitOn "x"
        |>.takeWhile (fun t => t.toNat?.isSome) |>.filterMap (·.toNat?)
      some (.constant_tensor (valStr.toInt?.getD 0) shape)
    else
      let val := rest.filter (fun t => t.toInt?.isSome) |>.head? |>.bind String.toInt?
      some (.constant (val.getD 0))
  | "arith.cmpi"        =>
      -- extract the predicate (slt, sle, sgt, sge, eq, ne)
      let pred := rest.head? |>.getD ""
      match pred with
      | "slt," => some .cmpi_slt
      | "sle," => some .cmpi_sle
      | "sgt," => some .cmpi_sgt
      | "sge," => some .cmpi_sge
      | "eq,"  => some .cmpi_eq
      | "ne,"  => some .cmpi_ne
      | _      => some .cmpi_slt  -- default
  | "arith.cmpf"        =>
      -- treat all float comparisons as cmpi_sge for now (integer model)
      some .cmpi_sge
  | "arith.select"      => some .select
  | "arith.addi"        => some .addi
  | "arith.subi"        => some .subi
  | "arith.muli"        => some .muli
  | "arith.divsi"       => some .divsi
  | "arith.addf"        => some .addf
  | "arith.mulf"        => some .mulf
  | "arith.minsi" => some .minsi
  | "arith.remsi" => some .remsi
  | "arith.truncf" => some .truncf
  | "arith.andi" => some .andi
  | "arith.subf" => some .subf
  | "arith.divf" => some .divf
  | "math.exp" => some .expf
  | "trident.copy"      => some .copy
  | _                   => none

def isSSAVar (s : String) : Bool := s.startsWith "%"
def stripPercent (s : String) : String :=
  let s := if s.endsWith "," then s.dropRight 1 else s
  if s.startsWith "%" then s.drop 1 |>.toString else s

def parseLine (line : String) : Option TritonInstr :=
  let tokens := line.splitOn " " |>.filter (· != "")
  match tokens with
  | [] => none
  | first :: rest =>
    if isSSAVar first then
      match rest with
      | "=" :: opName :: remaining =>
        match parseOp opName remaining with
        | none => none
        | some op =>
          let args := remaining.filter isSSAVar |>.map stripPercent
          some { result := stripPercent first, op := op, args := args }
      | _ => none
    else
      match parseOp first rest with
      | none => none
      | some op =>
        let args := rest.filter isSSAVar |>.map stripPercent
        some { result := "_", op := op, args := args }

def parseKernelVerbose (src : String) : Except String TritonKernel :=
  let lines := src.splitOn "\n"
    |>.map (fun l => l.trim)
    |>.filter (fun l => !l.isEmpty && !l.startsWith "//" &&
                        !l.startsWith "func" && !l.startsWith "}" &&
                        !l.startsWith "module" && !l.startsWith "tt.return" &&
                        !l.startsWith "#" && !l.startsWith "attributes" &&
                        !l.startsWith "tt.func" &&
                        !l.startsWith "llvm." &&           -- llvm.intr.assume: no-op optimizer hints
                        !l.startsWith "scf.for" &&         -- loop header handled by parseMatmulKernel
                        !l.startsWith "scf.yield" &&       -- loop yield handled by parseMatmulKernel
                        -- skip parameter declaration lines:
                        -- these start with % but have no = (SSA assignments always have =)
                        !(l.startsWith "%" && !l.contains " = "))
  let rec go : List String → Nat → Except String TritonKernel
    | [], _ => .ok []
    | l :: ls, n =>
      match parseLine l with
      | none => .error s!"Parse error on line {n}: {l}"
      | some instr =>
        match go ls (n + 1) with
        | .error e => .error e
        | .ok rest => .ok (instr :: rest)
  go lines 1

def parseKernel (src : String) : Option TritonKernel :=
  match parseKernelVerbose src with
  | .ok k => some k
  | .error _ => none


-- ── scf.for support ─────────────────────────────────────────────────────────────
-- Splits a kernel with ONE scf.for into (pre, ForLoop, post). iter_args are threaded
-- via synthetic `trident.copy` instrs: pre gets `ivarName := initVar` copies (init),
-- body gets `ivarName := yieldedVar` copies appended (yield rebind). Trip count is a
-- PARAMETER (the loop bound is a runtime SSA value, not a literal).

/-- Extract iter_arg pairs (ivarName, initVar) from a scf.for header line. -/
def parseIterArgs (header : String) : List (String × String) :=
  match (header.splitOn "iter_args(")[1]? with
  | none => []
  | some afterParen =>
    let inner := (afterParen.splitOn ")").headD ""
    (inner.splitOn ", ").filterMap (fun pair =>
      match pair.splitOn " = " with
      | [lhs, rhs] => some (stripPercent lhs.trim, stripPercent rhs.trim)
      | _ => none)

/-- Extract the induction variable name from a scf.for header. -/
def parseIvName (header : String) : String :=
  match header.splitOn "scf.for %" with
  | _ :: r :: _ => (r.splitOn " ").getD 0 "k"
  | _ => "k"

/-- Extract yielded var names from a scf.yield line. -/
def parseYieldVars (yieldLine : String) : List String :=
  match yieldLine.splitOn "scf.yield " with
  | _ :: r :: _ =>
    let beforeColon := (r.splitOn " :").getD 0 r
    (beforeColon.splitOn ", ").map (fun t => stripPercent t.trim)
  | _ => []

/-- Build a synthetic copy instruction: `dst := src`. -/
def mkCopy (dst src : String) : TritonInstr :=
  { result := dst, op := .copy, args := [src] }

/-- Loop result base name: from `%accumulator_32:3 = scf.for ...` extract `accumulator_32`. -/
def parseLoopResultBase (header : String) : String :=
  let lhs := (header.splitOn " = ").headD ""
  let noPct := stripPercent lhs.trim
  (noPct.splitOn ":").headD noPct

/-- Parse a kernel containing exactly one scf.for into (pre, loop, post).
    `trip` is supplied by the caller (loop bound is runtime). -/
def parseMatmulKernel (src : String) (trip : Nat) : Option (TritonKernel × ForLoop × TritonKernel) :=
  let rawLines := src.splitOn "\n" |>.map (·.trim)
  -- locate the scf.for header and the matching closing brace
  let idxFor := rawLines.findIdx (fun l => l.contains "scf.for")
  if idxFor >= rawLines.length then none
  else
    -- body runs from idxFor+1 until the line that is just "}" or "} loc(...)"
    let afterFor := rawLines.drop (idxFor + 1)
    let bodyLen := afterFor.findIdx (fun l => l.startsWith "}")
    let header  := rawLines.getD idxFor ""
    let preLines := rawLines.take idxFor
    let bodyLines := afterFor.take bodyLen
    let postLines := afterFor.drop (bodyLen + 1)
    let iterArgs := parseIterArgs header
    let ivName   := parseIvName header
    -- yield line inside body
    let yieldLine := (bodyLines.filter (fun l => l.contains "scf.yield")).getD 0 ""
    let yieldVars := parseYieldVars yieldLine
    let bodyNoYield := bodyLines.filter (fun l => !(l.contains "scf.yield"))
    -- parse each region through the flat parser (drop it into a fake module for reuse)
    match parseKernelVerbose (String.intercalate "\n" preLines) with
    | .error _ => none
    | .ok preK =>
    match parseKernelVerbose (String.intercalate "\n" bodyNoYield) with
    | .error _ => none
    | .ok bodyK =>
    match parseKernelVerbose (String.intercalate "\n" postLines) with
    | .error _ => none
    | .ok postK =>
      -- init copies: ivarName := initVar, appended to pre
      let initCopies := iterArgs.map (fun (iv, init) => mkCopy iv init)
      -- yield copies: ivarName := yieldedVar, appended to body end
      let yieldCopies := (iterArgs.map (·.1)).zip yieldVars |>.map (fun (iv, yv) => mkCopy iv yv)
      let loop : ForLoop := { ivName := ivName, trip := trip, body := bodyK ++ yieldCopies }
      -- bridge loop results: post reads `<base>#i`; map each to the i-th iter_arg's final name
      let resultBase := parseLoopResultBase header
      let bridgeCopies := (iterArgs.map (·.1)).zipIdx.map (fun (ivar, i) =>
        mkCopy (resultBase ++ "#" ++ toString i) ivar)
      some (preK ++ initCopies, loop, bridgeCopies ++ postK)

end Trident
