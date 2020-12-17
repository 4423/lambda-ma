module type IDENT =
    sig
        type t
        val create: string -> t
        val name: t -> string
        val equal: t -> t -> bool
        type 'a tbl
        val emptytbl: 'a tbl
        val add: t -> 'a -> 'a tbl -> 'a tbl
        val find: t -> 'a tbl -> 'a
    end

module Ident : IDENT = 
    struct
        type t = {name: string; stamp: int}
        let currstamp = ref 0
        let create s =
            currstamp := !currstamp + 1; {name = s; stamp = !currstamp}
        let name id = id.name
        let equal id1 id2 = (id1.stamp = id2.stamp)
        type 'a tbl = (t * 'a) list
        let emptytbl = []
        let add id data tbl = (id, data) :: tbl
        let rec find id1 = function
            | [] -> raise Not_found
            | (id2, data) :: rem ->
                if equal id1 id2 then data else find id1 rem
    end