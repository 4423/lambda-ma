let gc = Gc.get ()
let _  = Gc.set { gc with Gc.minor_heap_size = 3200000;
                  space_overhead = max_int }

let bench f =
  let t = Sys.time () in
  ignore (f ()); Printf.printf "%f" (Sys.time () -. t)

let rec sequence n acc =
  if (n >= 0) then 
    sequence (n-1) (n::acc) 
  else
    acc

let sequence n = sequence n []

open Fix_functor
open Fix

let mat_mul x y =
  let kn = Array.length y in
  let xn = Array.length x in
  let yn = if kn = 0 then 0 else Array.length y.(0) in
  let z = Array.make_matrix xn yn (int 0) in
  for i = 0 to xn - 1 do
    for j = 0 to yn - 1 do
      for k = 0 to kn - 1 do
        z.(i).(j) <- mul (add z.(i).(j) x.(i).(k)) y.(k).(j)
      done
    done
  done;
  z
;;
let mat_sum m =
  let d = Array.length m in
  let w = Array.make 1 (int 0) in
  for i = 0 to d - 1 do
    for j = 0 to Array.length m.(i) - 1 do
      w.(0) <- add w.(0) m.(i).(j)
    done
  done;
  w.(0)
;;  
let mat_dim = 30;;
let mat_a = Array.make_matrix mat_dim mat_dim (int 20);;
let mat_b = Array.make_matrix mat_dim mat_dim (int 30);;

let _ =
  bench (fun () -> observe (fun _ ->  mat_sum @@ mat_mul mat_a mat_b))
;;
