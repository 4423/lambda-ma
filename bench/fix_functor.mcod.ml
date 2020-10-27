module type SYM_CODE = sig
  type int_t
  type obs_t
  type unit_t
  val int: int -> int_t
  val add: int_t -> int_t -> int_t
  val sub: int_t -> int_t -> int_t
  val mul: int_t -> int_t -> int_t
  val div: int_t -> int_t -> int_t
  val observe: (unit_t -> int_t) -> obs_t
end mcod

module ArithCode: SYM_CODE with type obs_t = int = .<< struct
  type int_t = int
  type obs_t = int
  type unit_t = int
  let int = fun n1 -> n1
  let add = fun n1 -> fun n2 -> n1 + n2
  let sub = fun n1 -> fun n2 -> n1 - n2
  let mul = fun n1 -> fun n2 -> n1 * n2
  let div = fun n1 -> fun n2 -> n1 / n2
  let observe = fun f -> f 0
end >>.

module SuppressAddZeroOrMulZeroPECode
  = functor (S: SYM_CODE with type obs_t = int) -> 
  (.<< struct
    type int_t = (.%S$int_t) * bool
    type obs_t = int
    type unit_t = int
    let int = fun n1 -> (.~(S$int) n1, n1 == 0)
    let add = fun n1 -> fun n2 ->
      match (n1, n2) with
        (x1, b1), (x2, b2) -> if (b1 && b2) then (.~(S$int) 0, true) else (.~(S$add) x1 x2, false)

    let sub = fun n1 -> fun n2 ->
      match (n1, n2) with
        (x1, _), (x2, _) -> if x1 == x2 then (.~(S$int) 0, true) else (.~(S$sub) x1 x2, false)

    let mul = fun n1 -> fun n2 ->
      match (n1, n2) with
        (x1, b1), (x2, b2) -> if (b1 || b2) then (.~(S$int) 0, true) else (.~(S$mul) x1 x2, false)

    let div = fun n1 -> fun n2 ->
      match (n1, n2) with
        (x1, _), (x2, _) -> (.~(S$div) x1 x2, false)

    let observe = fun f -> 
      match f 0 with
        (n, _) -> .~(S$observe) (fun _ -> n)
  end >>. : SYM_CODE with type obs_t = int)

module X = recapp NUM_ITERATION SuppressAddZeroOrMulZeroPECode ArithCode
(* NUM_ITERATION will be replaced by bench.sh before translation *)

module Fix = Runmod(X : 
  sig
    type int_t
    type obs_t
    type unit_t
    val int: int -> int_t
    val add: int_t -> int_t -> int_t
    val sub: int_t -> int_t -> int_t
    val mul: int_t -> int_t -> int_t
    val div: int_t -> int_t -> int_t
    val observe: (unit_t -> int_t) -> obs_t
  end)