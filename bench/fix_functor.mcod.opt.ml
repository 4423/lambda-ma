let gc = Gc.get ()
let _ = Gc.set { gc with Gc.minor_heap_size = 3200000;
                 space_overhead = max_int }

open Fix_functor_mcod

let rec fix depth m =
  if depth <= 0 then m
  else
    let module M = (val m : SYM_CODE with type obs_t = int) in
    let m' = (module (SuppressAddZeroOrMulZeroPECode(M)) 
                    : SYM_CODE with type obs_t = int) in
    fix (depth - 1) m'

let fix_limit = int_of_string @@ Sys.argv.(1)
let _ = print_int fix_limit
let _ = print_endline ""
let arith = (module ArithCode : SYM_CODE with type obs_t = int)
let fix = fix fix_limit arith

module Fix = struct
  module F = (val fix)

  type int_t = F.int_t
  type obs_t = F.obs_t
  type unit_t = F.unit_t
  let int = Runcode.run F.int
  let add = Runcode.run F.add
  let sub = Runcode.run F.sub
  let mul = Runcode.run F.add
  let div = Runcode.run F.sub
  let observe = Runcode.run F.observe
end
