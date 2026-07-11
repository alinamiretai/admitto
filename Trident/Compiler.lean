import Trident.Source.Lang
import Trident.Target.Dialect

namespace Trident

def compiledVectorAdd : TritonKernel := [
  { result := "pid",    op := .get_program_id 0, args := [] },
  { result := "bstart", op := .muli,              args := ["pid", "bsize"] },
  { result := "range",  op := .make_range none,         args := [] },
  { result := "offset", op := .addi,              args := ["bstart", "range"] },
  { result := "aptrs",  op := .addptr,            args := ["a_base", "offset"] },
  { result := "bptrs",  op := .addptr,            args := ["b_base", "offset"] },
  { result := "cptrs",  op := .addptr,            args := ["c_base", "offset"] },
  { result := "avals",  op := .load,              args := ["aptrs"] },
  { result := "bvals",  op := .load,              args := ["bptrs"] },
  { result := "cvals",  op := .addi,              args := ["avals", "bvals"] },
  { result := "_",      op := .store,             args := ["cptrs", "cvals"] }
]

end Trident
