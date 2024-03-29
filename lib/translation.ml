open Error
open Identifier

module S = Source.Syntax
module T = Target.Syntax
module SC = S.Core
module TC = T.Core
module SM = S.Mod
module TM = T.Mod

let rec f : S.Mod.toplevel list -> T.Mod.toplevel list =
    fun toplevel_list ->
        List.map toplevel toplevel_list

and toplevel = function
    | SM.SignatureDec (id, mty)  -> TM.SignatureDec (id, mod_type 0 mty)
    | SM.StructureDec (id, modl) -> TM.StructureDec (id, mod_term 0 [] modl)
    | SM.LetDec (id, term)       -> TM.LetDec (id, core_term 0 [] term)
    | SM.LetRecDec (id, term)    -> TM.LetRecDec (id, core_term 0 [] term)
    | SM.TypeDec (id, kind, dty) -> TM.TypeDec (id, core_kind 0 kind, def_type 0 dty)

and path = function
    | S.IdentP id      -> T.IdentP id
    | S.DotP (p, s)    -> T.DotP (path p, s)
    | S.AppP (p1, p2)  -> T.AppP (path p1, path p2)
    | S.DollarP (p, s) -> T.DotP (path p, s)

and mod_term lv d = function
    | SM.Longident p            -> TM.Longident (path p)
    | SM.Structure str          -> TM.Structure (structure lv d str)
    | SM.Constraint (modl, mty) -> TM.Constraint (mod_term lv d modl, mod_type lv mty)
    | SM.FunM (id, mty, body) -> 
        if lv = 0 then TM.FunM (id, mod_type lv mty, mod_term lv d body)
        else error "functor definitions are allowed only at level 0"
    | SM.AppM (funct, arg) ->
        if lv = 0 then TM.AppM (mod_term lv d funct, mod_term lv d arg)
        else error "functor applications are allowed only at level 0"
    | SM.CodM modl -> 
        if lv = 0 then mod_term (lv+1) d modl
        else error "brackets for modules are allowed only at level 0"
    | SM.EscM modl ->
        if lv = 1 then mod_term (lv-1) d modl
        else error "escape for modules is allowed only at level 1"
    | SM.RunM (modl, mty) -> 
        if lv = 0 then runmod (mod_term 0 d modl) mty
        else error "Runmod is allowed only at level 0"
    | SM.DollarM (root, field) -> 
        if lv = 0 then TM.Longident (T.DotP ((path root), field))
        else error "dollar access is allowed only at level 0"
    | SM.RecAppM (n, funct, arg) ->
        let funct' = mod_term lv d funct in
        let arg' = mod_term lv d arg in
        let rec recapp i modl =
            if i = 0 then modl
            else recapp (i-1) (TM.AppM (funct', modl)) in
        recapp n arg'

and structure lv d str =
    definition lv d str
and definition lv d = function
    | [] -> []
    | SM.LetM(id, term) :: rem ->
        let term' = core_term lv d term in
        if lv = 0 then
            let res = TM.LetM (id, term') in
            res :: definition lv d rem
        else
            let res = TM.LetM (id, TC.GenletE (TC.CodE term')) in
            res :: definition lv (id::d) rem
    | SM.LetRecM(id, term) :: rem ->
        let term' = TC.LetRecE (id, core_term lv d term, TC.Longident (T.IdentP id)) in
        if lv = 0 then
            let res = TM.LetRecM (id, term') in
            res :: definition lv d rem
        else
            let res = TM.LetRecM (id, TC.GenletE (TC.CodE term')) in
            res :: definition lv (id::d) rem
    | SM.TypeM(id, kind, dty) :: rem ->
        let res = TM.TypeM (id, core_kind lv kind, def_type lv dty) in
        res :: definition lv d rem
    | SM.ModM(id, modl) :: rem -> 
        let res = TM.ModM (id, mod_term lv d modl) in
        if lv = 0 then
            res :: definition lv d rem
        else
            res :: definition lv (id::d) rem

and runmod (modl : TM.mod_term) (mty : SM.mod_type) =
    let sg = match mty with Signature sg -> sg in
    let mediator_id = Ident.create "X" in
    let mediator_mod = TM.ModM (mediator_id, modl) in
    let components = List.map (fun c -> runmod_component (T.IdentP mediator_id) c) sg in
    TM.Structure (mediator_mod :: components)
and runmod_component (root : T.path) = function
    | SM.ValS (id, vty) -> TM.LetM (id, TC.RunE (TC.Longident (T.DotP (root, Ident.name id))))
    | SM.TypeS (id, _)  -> TM.TypeM (id, 
                            { arity = 0 }, 
                            { params = []; defbody = TC.Typeconstr (T.DotP (root, Ident.name id), []) })
    | SM.ModS (id, mty) -> TM.ModM (id, runmod (TM.Longident (T.DotP (root, Ident.name id))) mty)

and mod_type lv = function
    | SM.LongidentS p -> TM.LongidentS (path p)
    | SM.Signature sg -> TM.Signature (signature lv sg)
    | SM.FunS (id, arg, res) ->
        if lv = 0 then TM.FunS (id, mod_type lv arg, mod_type lv res)
        else error "functor types are allowed only at level 0"
    | SM.CodS mty -> 
        if lv = 0 then mod_type (lv+1) mty
        else error "mcod is allowed only at level 0"
    | SM.SharingS (mty, c) -> TM.SharingS (mod_type lv mty, mod_constraint lv c)

and signature lv sg =
    List.map (fun s -> specification lv s) sg
and specification lv = function
    | SM.ValS (id, vty) -> 
        if lv = 0 then TM.ValS (id, val_type lv vty)
        else
        let vty' = val_type (lv+1) vty in
        TM.ValS (id, { quantif = vty'.quantif; body = TC.code_type vty'.body })
    | SM.TypeS (id, decl) -> TM.TypeS (id, type_decl lv decl)
    | SM.ModS (id, mty)   -> TM.ModS (id, mod_type lv mty)

and mod_constraint lv = function
    | SM.TypeC (id, dty) -> TM.TypeC (id, def_type lv dty)

and type_decl lv decl =
    match decl.manifest with
    | None     -> { kind = core_kind lv decl.kind; manifest = None }
    | Some dty -> { kind = core_kind lv decl.kind; manifest = Some (def_type lv dty) }

and head = function
    | T.IdentP id   -> id
    | T.DotP (p, _) -> head p
    | T.AppP _      -> error "undefined"

and core_term lv d = function
    | SC.IntE c                  -> TC.IntE c
    | SC.StrE s                  -> TC.StrE s
    | SC.BoolE b                 -> TC.BoolE b
    | SC.Longident p ->
        let p' = path p in
        let long = TC.Longident p' in
        if lv = 0 then long
        else begin
            let escape_long = TC.EscE long in
            match p' with
            | T.IdentP id when List.mem id d -> escape_long
            | T.DotP (root, _) when List.mem (head root) d -> escape_long
            | _ -> long
        end
    | SC.FunE (id, term)         -> TC.FunE (id, core_term lv d term)
    | SC.AppE (funct, arg)       -> TC.AppE (core_term lv d funct, core_term lv d arg)
    | SC.LetE (id, arg, body)    -> TC.LetE (id, core_term lv d arg, core_term lv d body)
    | SC.LetRecE (id, arg, body) -> TC.LetRecE (id, core_term lv d arg, core_term lv d body)
    | SC.IfE (t1, t2, t3)        -> TC.IfE (core_term lv d t1, core_term lv d t2, core_term lv d t3)
    | SC.MatchE (t, cs)          -> TC.MatchE (core_term lv d t, List.map (pattern_clauses lv d) cs)
    | SC.CodE term ->
        if lv = 0 then TC.CodE (core_term (lv+1) d term)
        else error "brackets are allowed only at level 0"
    | SC.EscE term -> 
        if lv = 1 then TC.EscE (core_term (lv-1) d term)
        else error "escape is allowed only at level 1"
    | SC.RunE term ->
        if lv = 0 then TC.RunE (core_term lv d term)
        else error "run is allowed only at level 0"
    | SC.DollarE (root, field) ->
        if lv = 0 then TC.Longident (T.DotP ((path root), field))
        else error "dollar access is allowed only at level 0"
and pattern_clauses lv d (pat, term) =
    pattern pat, core_term lv d term
and pattern = function
    | SC.VarPat id -> TC.VarPat id
    | SC.ConsPat (hd, tl) -> TC.ConsPat (pattern hd, tl)
    | SC.PairPat (p1, p2) -> TC.PairPat (pattern p1, pattern p2)
    | SC.WildPat -> TC.WildPat

and core_type lv = function
    | SC.Var tvar           -> TC.Var (type_variable lv tvar)
    | SC.Typeconstr (p, [t]) when p = SC.path_csp -> core_type lv t
    | SC.Typeconstr (p, [t1;t2]) when p = SC.path_dollar ->
        let (root, field) = match (t1, t2) with
        | (SC.Typeconstr (root, []), SC.Typeconstr (IdentP id, [])) -> root, Ident.name id
        | _ -> error "could not deconstruct type of dollar access"
        in
        TC.Typeconstr (T.DotP (path root, field), [])
    | SC.Typeconstr (p, ts) -> TC.Typeconstr (path p, List.map (fun t -> core_type lv t) ts)

and type_variable lv tvar =
    match tvar.repres with
    | None    -> { repres = None; level = tvar.level }
    | Some ty -> { repres = Some (core_type lv ty); level = tvar.level }     

and val_type lv vty =
    { quantif = List.map (fun t -> type_variable lv t) vty.quantif;
        body = core_type lv vty.body }
        
and def_type lv dty =
    { params = List.map (fun t -> type_variable lv t) dty.params;
        defbody = core_type lv dty.defbody }

and core_kind lv kind =
    { arity = kind.arity }