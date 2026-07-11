-- Trident.Target.Semantics
-- Operational semantics of Triton IR.
-- Defines what each instruction DOES when it executes.
--
-- CompCert equivalent: backend/RTL.v semantics section
--
-- DESIGN PRINCIPLE: Written for PROVABILITY, not just executability.
-- Every case is explicit, every helper is named and lemmatized,
-- the recursive structure mirrors what induction proofs need.

import Trident.Target.Dialect
import Trident.Common.Memory

namespace Trident

open TritonValue

-- ── Single Operation Semantics ────────────────────────────────────────────────

/--
`evalOp` gives the meaning of one Triton operation.
Returns `none` if preconditions fail (wrong args, type mismatch).
Returns `some val` on success.
-/
def evalOp (op : TritonOp) (args : List String) (s : MachineState)
    : Option TritonValue :=
  match op with
  | .copy =>
      match args with
      | [v] => s.lookup v
      | _ => none

  | .get_program_id axis =>
      some (scalar (Int.ofNat (if axis == 0 then s.pid else s.pid_y)))
  | .get_num_programs _ =>
      some (scalar (Int.ofNat s.grid_size))
  | .constant v =>
      some (scalar v)

  | .constantf v =>
      some (fscalar v)

  | .make_range sizeOpt =>
      let sz := sizeOpt.getD s.block_size
      some (tensor [sz] ((List.range sz).map Int.ofNat))

  | .splat shape =>
      match args with
      | [v] => match s.lookup v with
        | some (scalar x) =>
            some (tensor shape (List.replicate (shape.foldl (· * ·) 1) x))
        | some (fscalar x) =>
            some (ftensor shape (List.replicate (shape.foldl (· * ·) 1) x))
        | _ => none
      | _ => none

  | .addptr =>
      match args with
      | [p, o] => match s.lookup p, s.lookup o with
        | some (scalar base), some (scalar off) =>
            some (scalar (base + off))
        | some (scalar base), some (tensor sh offs) =>
            some (tensor sh (offs.map (· + base)))
        | some (tensor sh1 bases), some (tensor sh2 offs) =>
            if sh1 == sh2
            then some (tensor sh1 ((bases.zip offs).map fun (b, o) => b + o))
            else none
        | _, _ => none
      | _ => none

  | .load =>
      match args with
      | [p] => match s.lookup p with
        | some (scalar addr) => some (scalar (s.readMem addr.natAbs))
        | some (tensor sh addrs) => some (tensor sh (addrs.map fun a => s.readMem a.natAbs))
        | _ => none
      | [p, m] =>
        match s.lookup p, s.lookup m with
        | some (tensor sh addrs), some (tensor shm masks) =>
            if sh == shm then
              some (tensor sh ((addrs.zip masks).map fun (a, mk) =>
                if mk != 0 then s.readMem a.natAbs else 0))
            else none
        | _, _ => none
      | [p, m, other] =>
        match s.lookup p, s.lookup m, s.lookup other with
        | some (tensor sh addrs), some (tensor _ masks), some (tensor _ others) =>
            some (tensor sh (((addrs.zip masks).zip others).map fun ((a, mk), o) =>
              if mk != 0 then s.readMem a.natAbs else o))
        | _, _, _ => none
      | _ => none

  | .loadf =>
      match args with
      | [p] => match s.lookup p with
        | some (scalar addr) => some (fscalar (s.readMemF addr.natAbs))
        | some (tensor sh addrs) => some (ftensor sh (addrs.map fun a => s.readMemF a.natAbs))
        | _ => none
      | [p, m] =>
        match s.lookup p, s.lookup m with
        | some (tensor sh addrs), some (tensor _ masks) =>
            some (ftensor sh ((addrs.zip masks).map fun (a, mk) =>
              if mk != 0 then s.readMemF a.natAbs else 0.0))
        | _, _ => none
      | [p, m, other] =>
        match s.lookup p, s.lookup m, s.lookup other with
        | some (tensor sh addrs), some (tensor _ masks), some (ftensor _ others) =>
            some (ftensor sh (((addrs.zip masks).zip others).map fun ((a, mk), o) =>
              if mk != 0 then s.readMemF a.natAbs else o))
        | _, _, _ => none
      | _ => none

  | .andi =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          match va, vb with
          | TritonValue.scalar x, TritonValue.scalar y =>
              some (TritonValue.scalar (if x != 0 && y != 0 then 1 else 0))
          | TritonValue.tensor s1 xs, TritonValue.tensor s2 ys =>
              if s1 == s2
              then some (TritonValue.tensor s1 ((xs.zip ys).map fun (x,y) => if x != 0 && y != 0 then 1 else 0))
              else none
          | _, _ => none
      | _ => none

  | .addi =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          match va, vb with
          | TritonValue.scalar x, TritonValue.scalar y =>
              some (TritonValue.scalar (x + y))
          | TritonValue.scalar x, TritonValue.tensor sh ys =>
              some (TritonValue.tensor sh (ys.map (· + x)))
          | TritonValue.tensor sh xs, TritonValue.scalar y =>
              some (TritonValue.tensor sh (xs.map (· + y)))
          | TritonValue.tensor s1 xs, TritonValue.tensor s2 ys =>
              if s1 == s2
              then some (TritonValue.tensor s1 ((xs.zip ys).map (fun (x,y) => x + y)))
              else none
          | _, _ => none
      | _ => none

  | .addf =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          match va, vb with
          | TritonValue.scalar x, TritonValue.scalar y =>
              some (TritonValue.scalar (x + y))
          | TritonValue.scalar x, TritonValue.tensor sh ys =>
              some (TritonValue.tensor sh (ys.map (· + x)))
          | TritonValue.tensor sh xs, TritonValue.scalar y =>
              some (TritonValue.tensor sh (xs.map (· + y)))
          | TritonValue.tensor s1 xs, TritonValue.tensor s2 ys =>
              if s1 == s2
              then some (TritonValue.tensor s1 ((xs.zip ys).map (fun (x,y) => x + y)))
              else none
          | TritonValue.fscalar x, TritonValue.fscalar y =>
            some (TritonValue.fscalar (x + y))
          | TritonValue.fscalar x, TritonValue.ftensor sh ys =>
            some (TritonValue.ftensor sh (ys.map (· + x)))
          | TritonValue.ftensor sh xs, TritonValue.fscalar y =>
            some (TritonValue.ftensor sh (xs.map (· + y)))
          | TritonValue.ftensor s1 xs, TritonValue.ftensor s2 ys =>
            if s1 == s2
            then some (TritonValue.ftensor s1 ((xs.zip ys).map (fun (x,y) => x + y)))
            else none
          | _, _ => none
      | _ => none

  | .subf =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          match va, vb with
          | TritonValue.fscalar x, TritonValue.fscalar y =>
              some (TritonValue.fscalar (x - y))
          | TritonValue.fscalar x, TritonValue.ftensor sh ys =>
              some (TritonValue.ftensor sh (ys.map (x - ·)))
          | TritonValue.ftensor sh xs, TritonValue.fscalar y =>
              some (TritonValue.ftensor sh (xs.map (· - y)))
          | TritonValue.ftensor s1 xs, TritonValue.ftensor s2 ys =>
              if s1 == s2
              then some (TritonValue.ftensor s1 ((xs.zip ys).map (fun (x,y) => x - y)))
              else none
          | _, _ => none
      | _ => none

  | .divf =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          match va, vb with
          | TritonValue.fscalar x, TritonValue.fscalar y =>
              some (TritonValue.fscalar (x / y))
          | TritonValue.fscalar x, TritonValue.ftensor sh ys =>
              some (TritonValue.ftensor sh (ys.map (x / ·)))
          | TritonValue.ftensor sh xs, TritonValue.fscalar y =>
              some (TritonValue.ftensor sh (xs.map (· / y)))
          | TritonValue.ftensor s1 xs, TritonValue.ftensor s2 ys =>
              if s1 == s2
              then some (TritonValue.ftensor s1 ((xs.zip ys).map (fun (x,y) => x / y)))
              else none
          | _, _ => none
      | _ => none

  | .maxsi =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          match va, vb with
          | TritonValue.scalar x, TritonValue.scalar y =>
              some (TritonValue.scalar (max x y))
          | TritonValue.scalar x, TritonValue.tensor sh ys =>
              some (TritonValue.tensor sh (ys.map (max x)))
          | TritonValue.tensor sh xs, TritonValue.scalar y =>
              some (TritonValue.tensor sh (xs.map (max · y)))
          | TritonValue.tensor s1 xs, TritonValue.tensor s2 ys =>
              if s1 == s2
              then some (TritonValue.tensor s1 ((xs.zip ys).map (fun (x,y) => max x y)))
              else none
          | _, _ => none
      | _ => none

  | .minsi =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          match va, vb with
          | TritonValue.scalar x, TritonValue.scalar y =>
              some (TritonValue.scalar (min x y))
          | TritonValue.scalar x, TritonValue.tensor sh ys =>
              some (TritonValue.tensor sh (ys.map (min x)))
          | TritonValue.tensor sh xs, TritonValue.scalar y =>
              some (TritonValue.tensor sh (xs.map (min · y)))
          | TritonValue.tensor s1 xs, TritonValue.tensor s2 ys =>
              if s1 == s2
              then some (TritonValue.tensor s1 ((xs.zip ys).map (fun (x,y) => min x y)))
              else none
          | _, _ => none
      | _ => none

  | .remsi =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          match va, vb with
          | TritonValue.scalar x, TritonValue.scalar y =>
              some (TritonValue.scalar (x % y))
          | TritonValue.scalar x, TritonValue.tensor sh ys =>
              some (TritonValue.tensor sh (ys.map (x % ·)))
          | TritonValue.tensor sh xs, TritonValue.scalar y =>
              some (TritonValue.tensor sh (xs.map (· % y)))
          | TritonValue.tensor s1 xs, TritonValue.tensor s2 ys =>
              if s1 == s2
              then some (TritonValue.tensor s1 ((xs.zip ys).map (fun (x,y) => x % y)))
              else none
          | _, _ => none
      | _ => none

  | .truncf =>
      match args with
      | [v] => s.lookup v
      | _ => none

  | .constant_tensor val shape =>
      some (tensor shape (List.replicate (shape.foldl (· * ·) 1) val))

  | .constant_tensorf val shape =>
      some (ftensor shape (List.replicate (shape.foldl (· * ·) 1) val))

  | .broadcast shape =>
      match args with
      | [v] => match s.lookup v with
        | some (tensor srcShape vals) =>
            match srcShape, shape with
            | [s0, s1], [t0, t1] =>
                let result := (List.range (t0 * t1)).map fun idx =>
                  let i := idx / t1
                  let j := idx % t1
                  let si := if s0 == 1 then 0 else i
                  let sj := if s1 == 1 then 0 else j
                  vals.getD (si * s1 + sj) 0
                some (tensor shape result)
            | _, _ => none
        | _ => none
      | _ => none

  | .subi =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          va.zipWith (· - ·) vb
      | _ => none

  | .muli =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          va.zipWith (· * ·) vb
      | _ => none

  | .divsi =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          va.zipWith (· / ·) vb
      | _ => none

  | .reduce_sum _ =>
      match args with
      | [v] => match s.lookup v with
        | some (tensor _ vals) => some (scalar (vals.foldl (· + ·) 0))
        | some (ftensor _ vals) => some (fscalar (vals.foldl (· + ·) 0.0))
        | _ => none
      | _ => none

  | .reduce_max _ =>
      match args with
      | [v] => match s.lookup v with
        | some (tensor _ (hd :: tl)) => some (scalar (tl.foldl max hd))
        | some (ftensor _ (hd :: tl)) => some (fscalar (tl.foldl max hd))
        | _ => none
      | _ => none

  | .select =>
      match args with
      | [cond, a, b] =>
          (s.lookup cond).bind fun vc =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          match vc, va, vb with
          | TritonValue.tensor sh cs,
            TritonValue.tensor _ as_,
            TritonValue.tensor _ bs_ =>
              some (TritonValue.tensor sh
                ((cs.zip (as_.zip bs_)).map fun (c, av, bv) =>
                  if c != 0 then av else bv))
          | _, _, _ => none
      | _ => none

  | .cmpi_slt =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          match va, vb with
          | TritonValue.tensor sha xs, TritonValue.tensor shb ys =>
              -- shape guard (mirrors addi/addf/muli): mismatched shapes are ill-typed,
              -- so we no-op (return none) rather than silently truncate via zip.
              if sha == shb then
                some (TritonValue.tensor sha
                  ((xs.zip ys).map fun (x, y) => if x < y then 1 else 0))
              else none
          | TritonValue.scalar x, TritonValue.scalar y =>
              some (TritonValue.scalar (if x < y then 1 else 0))
          | _, _ => none
      | _ => none
  | .cmpi_sgt =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          match va, vb with
          | TritonValue.tensor sha xs, TritonValue.tensor shb ys =>
              if sha == shb then
                some (TritonValue.tensor sha
                  ((xs.zip ys).map fun (x, y) => if x > y then 1 else 0))
              else none
          | TritonValue.scalar x, TritonValue.scalar y =>
              some (TritonValue.scalar (if x > y then 1 else 0))
          | _, _ => none
      | _ => none

  | .cmpi_sge =>
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va =>
          (s.lookup b).bind fun vb =>
          match va, vb with
          | TritonValue.tensor sh xs, TritonValue.tensor _ ys =>
              some (TritonValue.tensor sh
                ((xs.zip ys).map fun (x, y) => if x >= y then 1 else 0))
          | TritonValue.scalar x, TritonValue.scalar y =>
              some (TritonValue.scalar (if x >= y then 1 else 0))
          | _, _ => none
      | _ => none

  | .dot =>
      let doDot (va vb : TritonValue) (acc : Option (List Int)) : Option TritonValue :=
        match va, vb with
        | tensor [m, k1] valsA, tensor [k2, n] valsB =>
            if k1 != k2 then none else
            let result := (List.range (m * n)).map fun idx =>
              let i := idx / n
              let j := idx % n
              let sum := (List.range k1).foldl (fun acc' kk =>
                acc' + (valsA.getD (i * k1 + kk) 0) * (valsB.getD (kk * n + j) 0)) 0
              sum + (acc.map (·.getD idx 0)).getD 0
            some (tensor [m, n] result)
        | _, _ => none
      match args with
      | [a, b] =>
          (s.lookup a).bind fun va => (s.lookup b).bind fun vb => doDot va vb none
      | [a, b, accVar] =>
          (s.lookup a).bind fun va => (s.lookup b).bind fun vb =>
          match s.lookup accVar with
          | some (tensor _ accVals) => doDot va vb (some accVals)
          | _ => none
      | _ => none

  | .expand_dims axis =>
      match args with
      | [v] => match s.lookup v with
        | some (tensor sh vals) =>
            some (tensor (sh.take axis ++ [1] ++ sh.drop axis) vals)
        | _ => none
      | _ => none

  | .expf =>
      match args with
      | [v] => match s.lookup v with
        | some (fscalar x) => some (fscalar x.exp)
        | some (ftensor sh xs) => some (ftensor sh (xs.map Float.exp))
        | _ => none
      | _ => none

  -- Store and all unimplemented ops handled in evalInstr
  | _ => none

-- ── Instruction Execution ─────────────────────────────────────────────────────

/--
`evalInstr` executes one full SSA instruction.
- For `store`: writes to memory, returns updated state
- For everything else: evaluates op and binds result variable
-/
def evalInstr (instr : TritonInstr) (s : MachineState) : MachineState :=
  match instr.op with
  | .store =>
      match instr.args with
      | [p, v] => match s.lookup p, s.lookup v with
        | some (scalar addr), some (scalar val) => s.writeMem addr.natAbs val
        | some (tensor _ addrs), some (tensor _ vals) => s.writeTile (addrs.map Int.natAbs) vals
        | _, _ => s
      | [p, v, m] => match s.lookup p, s.lookup v, s.lookup m with
        | some (tensor _ addrs), some (tensor _ vals), some (tensor _ masks) =>
            let kept := ((addrs.zip vals).zip masks).filterMap fun ((a, v), mk) =>
              if mk != 0 then some (a, v) else none
            s.writeTile (kept.map (·.1.natAbs)) (kept.map (·.2))
        | _, _, _ => s
      | _ => s
  | .storef =>
      match instr.args with
      | [p, v] => match s.lookup p, s.lookup v with
        | some (tensor _ addrs), some (ftensor _ vals) => s.writeTileF (addrs.map Int.natAbs) vals
        | _, _ => s
      | [p, v, m] => match s.lookup p, s.lookup v, s.lookup m with
        | some (tensor _ addrs), some (ftensor _ vals), some (tensor _ masks) =>
            let kept := ((addrs.zip vals).zip masks).filterMap fun ((a, v), mk) =>
              if mk != 0 then some (a, v) else none
            s.writeTileF (kept.map (·.1.natAbs)) (kept.map (·.2))
        | _, _, _ => s
      | _ => s
  | _ =>
      match evalOp instr.op instr.args s with
      | some val => s.bind instr.result val
      | none     => s

-- ── Kernel Execution ──────────────────────────────────────────────────────────

/-- Run a complete kernel: fold evalInstr over the instruction list -/
def evalKernel (kernel : TritonKernel) (s : MachineState) : MachineState :=
  kernel.foldl (fun st instr => evalInstr instr st) s

/-- Concrete for-loop: fold the body over range trip, binding the induction var each iteration. -/
def evalForLoop (loop : ForLoop) (s : MachineState) : MachineState :=
  (List.range loop.trip).foldl
    (fun st k => evalKernel loop.body (st.bind loop.ivName (TritonValue.scalar (Int.ofNat k))))
    s

-- ── Semantics Lemmas ──────────────────────────────────────────────────────────
-- Named lemmas for each op.
-- These are the building blocks that simulation proofs use.
-- @[simp] lets the simp tactic apply them automatically.

@[simp]
theorem evalOp_get_program_id (axis : Nat) (args : List String) (s : MachineState) :
    evalOp (.get_program_id axis) args s =
      some (scalar (Int.ofNat (if axis == 0 then s.pid else s.pid_y))) := by
  simp [evalOp]

@[simp]
theorem evalOp_constant (v : Int) (args : List String) (s : MachineState) :
    evalOp (.constant v) args s = some (scalar v) := by
  simp [evalOp]

@[simp]
theorem evalOp_make_range (sizeOpt : Option Nat) (args : List String) (s : MachineState) :
    evalOp (.make_range sizeOpt) args s =
    some (tensor [sizeOpt.getD s.block_size] ((List.range (sizeOpt.getD s.block_size)).map Int.ofNat)) := by
  simp [evalOp]

@[simp]
theorem evalKernel_nil (s : MachineState) :
    evalKernel [] s = s := by
  simp [evalKernel]

@[simp]
theorem evalKernel_cons (i : TritonInstr) (rest : TritonKernel) (s : MachineState) :
    evalKernel (i :: rest) s = evalKernel rest (evalInstr i s) := by
  simp [evalKernel, List.foldl]

theorem evalInstr_non_store_bind
    (instr : TritonInstr) (s : MachineState) (val : TritonValue)
    (h_op : evalOp instr.op instr.args s = some val)
    (h_not_store : instr.op ≠ .store)
    (h_not_storef : instr.op ≠ .storef) :
    evalInstr instr s = s.bind instr.result val := by
  simp [evalInstr, h_op]

theorem evalInstr_lookup_other
    (instr : TritonInstr) (s : MachineState) (v : String)
    (h_diff : v ≠ instr.result)
    (h_not_store : instr.op ≠ .store)
    (h_not_storef : instr.op ≠ .storef)
    (val : TritonValue)
    (h_op : evalOp instr.op instr.args s = some val) :
    (evalInstr instr s).lookup v = s.lookup v := by
  rw [evalInstr_non_store_bind instr s val h_op h_not_store h_not_storef]
  exact MachineState.bind_lookup_other _ _ _ _ (Ne.symm h_diff)

-- ── TargetSemantics Instance ──────────────────────────────────────────────────
-- Packages the target semantics for use with ForwardSimulation.

/-- Build initial state for a kernel given inputs and launch params -/
def buildInitState
    (inputs  : List (List Int))
    (pid bs gs : Nat)
    (extraEnv : String → Option TritonValue := fun _ => none)
    : MachineState :=
  { pid        := pid
  , block_size := bs
  , grid_size  := gs
  , memory     := fun _ => 0
  , env        := extraEnv }

-- ── Additional evalOp simp lemmas for proof engineering ──────────────────────
-- These let proofs use specific targeted lemmas instead of unfolding the full
-- evalOp match (which has 20+ cases and causes term explosion when used wholesale).

@[simp]
theorem evalOp_muli (args : List String) (s : MachineState) :
    evalOp .muli args s =
    match args with
    | [a, b] =>
        (s.lookup a).bind fun va =>
        (s.lookup b).bind fun vb =>
        TritonValue.zipWith (· * ·) va vb
    | _ => none := by simp [evalOp]

@[simp]
theorem evalOp_splat (shape : List Nat) (args : List String) (s : MachineState) :
    evalOp (.splat shape) args s =
    match args with
    | [v] => match s.lookup v with
        | some (TritonValue.scalar x) =>
            some (TritonValue.tensor shape (List.replicate (shape.foldl (· * ·) 1) x))
        | some (TritonValue.fscalar x) =>
            some (TritonValue.ftensor shape (List.replicate (shape.foldl (· * ·) 1) x))
        | _ => none
    | _ => none := by simp [evalOp]

@[simp]
theorem evalOp_addi (args : List String) (s : MachineState) :
    evalOp .addi args s =
    match args with
    | [a, b] =>
        (s.lookup a).bind fun va =>
        (s.lookup b).bind fun vb =>
        match va, vb with
        | TritonValue.scalar x, TritonValue.scalar y => some (TritonValue.scalar (x + y))
        | TritonValue.scalar x, TritonValue.tensor sh ys => some (TritonValue.tensor sh (ys.map (· + x)))
        | TritonValue.tensor sh xs, TritonValue.scalar y => some (TritonValue.tensor sh (xs.map (· + y)))
        | TritonValue.tensor s1 xs, TritonValue.tensor s2 ys =>
            if s1 == s2 then some (TritonValue.tensor s1 ((xs.zip ys).map fun (x,y) => x + y)) else none
        | _, _ => none
    | _ => none := by simp [evalOp]

@[simp]
theorem evalOp_addf (args : List String) (s : MachineState) :
    evalOp .addf args s =
    match args with
    | [a, b] =>
        (s.lookup a).bind fun va =>
        (s.lookup b).bind fun vb =>
        match va, vb with
        | TritonValue.scalar x, TritonValue.scalar y => some (TritonValue.scalar (x + y))
        | TritonValue.scalar x, TritonValue.tensor sh ys => some (TritonValue.tensor sh (ys.map (· + x)))
        | TritonValue.tensor sh xs, TritonValue.scalar y => some (TritonValue.tensor sh (xs.map (· + y)))
        | TritonValue.tensor s1 xs, TritonValue.tensor s2 ys =>
            if s1 == s2 then some (TritonValue.tensor s1 ((xs.zip ys).map fun (x,y) => x + y)) else none
        | TritonValue.fscalar x, TritonValue.fscalar y => some (TritonValue.fscalar (x + y))
        | TritonValue.fscalar x, TritonValue.ftensor sh ys => some (TritonValue.ftensor sh (ys.map (· + x)))
        | TritonValue.ftensor sh xs, TritonValue.fscalar y => some (TritonValue.ftensor sh (xs.map (· + y)))
        | TritonValue.ftensor s1 xs, TritonValue.ftensor s2 ys =>
            if s1 == s2 then some (TritonValue.ftensor s1 ((xs.zip ys).map fun (x,y) => x + y)) else none
        | _, _ => none
    | _ => none := by simp [evalOp]

@[simp]
theorem evalOp_cmpi_slt (args : List String) (s : MachineState) :
    evalOp .cmpi_slt args s =
    match args with
    | [a, b] =>
        (s.lookup a).bind fun va =>
        (s.lookup b).bind fun vb =>
        match va, vb with
        | TritonValue.tensor sha xs, TritonValue.tensor shb ys =>
            if sha == shb then
              some (TritonValue.tensor sha ((xs.zip ys).map fun (x, y) => if x < y then 1 else 0))
            else none
        | TritonValue.scalar x, TritonValue.scalar y =>
            some (TritonValue.scalar (if x < y then 1 else 0))
        | _, _ => none
    | _ => none := by simp [evalOp]

@[simp]
theorem evalOp_addptr (args : List String) (s : MachineState) :
    evalOp .addptr args s =
    match args with
    | [p, o] => match s.lookup p, s.lookup o with
        | some (TritonValue.scalar base), some (TritonValue.scalar off) =>
            some (TritonValue.scalar (base + off))
        | some (TritonValue.scalar base), some (TritonValue.tensor sh offs) =>
            some (TritonValue.tensor sh (offs.map (· + base)))
        | some (TritonValue.tensor sh1 bases), some (TritonValue.tensor sh2 offs) =>
            if sh1 == sh2
            then some (TritonValue.tensor sh1 ((bases.zip offs).map fun (b, o) => b + o))
            else none
        | _, _ => none
    | _ => none := by simp [evalOp]


end Trident
