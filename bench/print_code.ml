(* This program prints generated code as string *)

open Fix_functor

let print c = Codelib.print_code Format.std_formatter c ;;
print X.int ;;
print X.add ;;
print X.sub ;;
print X.mul ;;
print X.div ;;
print X.observe ;;
