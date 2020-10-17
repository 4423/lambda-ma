module type SYM_CODE = sig
  type int_t
  type obs_t
  type unit_t
  val int: (int -> int_t) code
  val add: (int_t -> int_t -> int_t) code
  val sub: (int_t -> int_t -> int_t) code
  val mul: (int_t -> int_t -> int_t) code
  val div: (int_t -> int_t -> int_t) code
  val observe: ((unit_t -> int_t) -> obs_t) code
end

module ArithCode: (SYM_CODE with type obs_t = int) = struct
  type int_t = int
  type obs_t = int
  type unit_t = int
  let int = genlet .< fun n1 -> n1 >.
  let add = genlet .< fun n1 -> fun n2 -> n1 + n2 >.
  let sub = genlet .< fun n1 -> fun n2 -> n1 - n2 >.
  let mul = genlet .< fun n1 -> fun n2 -> n1 * n2 >.
  let div = genlet .< fun n1 -> fun n2 -> n1 / n2 >.
  let observe = genlet .< fun f -> f 0 >.
end

module SuppressAddZeroOrMulZeroPECode (S: SYM_CODE with type obs_t = int)
  : (SYM_CODE with type obs_t = int) = struct
  type int_t = S.int_t * bool
  type obs_t = int
  type unit_t = int
  let int = genlet .< fun n1 -> (.~(S.int) n1, n1 = 0) >.
  let add = genlet .< fun n1 -> fun n2 ->
    match n1, n2 with
      (n1, true), (n2, true) ->
      (.~(S.int) 0, true)
    | (n1, _), (n2, _) ->
      (.~(S.add) n1 n2, false) >.

  let sub = genlet .< fun n1 -> fun n2 ->
    match n1, n2 with
      (n1, _), (n2, _) -> if n1 = n2 then (.~(S.int) 0, true) else (.~(S.sub) n1 n2, false) >.

  let mul = genlet .< fun n1 -> fun n2 ->
    match (n1, n2) with
      (n1, b1), (n2, b2) -> if (b1 || b2) then (.~(S.int) 0, true) else (.~(S.mul) n1 n2, false) >.

  let div = genlet .< fun n1 -> fun n2 ->
    match (n1, n2) with
      (n1, _), (n2, _) -> (.~(S.div) n1 n2, false) >.

  let observe = genlet .< fun f -> 
    match f 0 with
    | (n, _) -> .~(S.observe) (fun _ -> n) >.
end
