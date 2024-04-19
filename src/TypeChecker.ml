open GT
open Language


type lamaType =  
                  Sexp 
                  | Int 
                  | String 
                  | Array of lamaType 
                  | Any 
                  | Callable of (lamaType list) * lamaType 
                  | Unit 
                  | Union of lamaType list 
                  | Tuple of lamaType list 
                  | TVar of string
                  | VariantType of (string * lamaType) list
                  | RecursiveType of string * lamaType
                  | TyId of string
  
let rec applyTraverse f fctx t =  let applyTraverseList f fctx ts = List.map snd (List.map (applyTraverse f fctx) ts) in
                                  let applyTraverseOne f fctx t = let (_, t) = applyTraverse f fctx t in t in
                                  let (fctx, t) = f fctx t in
                                  let t =  match t with 
                                                  Sexp -> Sexp
                                                  | Int -> Int
                                                  | String -> String
                                                  | Array et -> Array (applyTraverseOne f fctx et)
                                                  | Any -> Any
                                                  | Callable (ts, ret) -> Callable (applyTraverseList f fctx ts, applyTraverseOne f fctx ret)
                                                  | Unit -> Unit
                                                  | Union ts -> Union (applyTraverseList f fctx ts)
                                                  | Tuple ts -> Tuple (applyTraverseList f fctx ts)
                                                  | TVar v -> TVar v
                                                  | VariantType vs -> let ls = List.map fst vs in let ts = List.map snd vs in VariantType (List.combine ls (applyTraverseList f fctx ts))
                                                  | RecursiveType (x, t) -> RecursiveType(x, applyTraverseOne f fctx t)
                                                  | TyId s -> TyId s
                                  in (fctx, t)
                                      
            (*Maybe boundVars is redundant*)
let tySubst tVar s t =  let substF boundVars t = match t with 
                                                        TVar v when (v = tVar) && (not (List.mem v boundVars)) -> (boundVars, s)
                                                        | RecursiveType (x, t) -> ((x::boundVars), RecursiveType (x, t))
                                                        | _ -> (boundVars, t)
                        in snd (applyTraverse substF [] t)
                  (*TODO: remove another*)
let rec lamaTypeAnnotationTolamaType2 ta = match ta with  
                  TA_Sexp -> Sexp
                | TA_Int -> Int
                | TA_String -> String
                | TA_Array ta -> Array (lamaTypeAnnotationTolamaType2 ta)
                | TA_Any -> Any
                | TA_Callable (ls, ta) -> Callable (List.map (lamaTypeAnnotationTolamaType2) ls, lamaTypeAnnotationTolamaType2 ta)
                | TA_Unit -> Unit
                | TA_Union ls -> Union (List.map (lamaTypeAnnotationTolamaType2) ls)
                | TA_Tuple ls -> Tuple (List.map (lamaTypeAnnotationTolamaType2) ls)
                | TA_TypeId t -> TyId t

let rec type_to_string t = match t with
                        | Sexp -> "Sexp"
                        | Int -> "Int"
                        | String -> "String"
                        | Array elemT  -> "Array " ^ (type_to_string elemT)
                        | Any -> "Any"
                        | Callable (args, ret) -> Printf.sprintf "Callable ([%s], %s)" (String.concat "," (List.map type_to_string args)) (type_to_string ret)
                        | Unit  -> "Unit"
                        | Union ls -> Printf.sprintf "Union [%s]" (String.concat "," (List.map type_to_string ls))
                        | Tuple ls -> Printf.sprintf "Tuple [%s]" (String.concat "," (List.map type_to_string ls))
                        | TVar x -> Printf.sprintf "TVar %s" x
                        | VariantType ls -> Printf.sprintf "VariantType [%s]" (String.concat "," (List.map (fun (l, t) -> Printf.sprintf "(%s, %s)" l (type_to_string t)) ls))
                        | RecursiveType (x, t) -> Printf.sprintf "RecursiveType %s.%s" x (type_to_string t)
                        | TyId t ->  t

let rec remove_duplicates lst =
                              match lst with
                              | [] -> []
                              | hd :: tl ->
                                hd :: (remove_duplicates (List.filter (fun x -> x <> hd) tl))

let rec remove_elements lst1 lst2 =
  match lst1 with
  | [] -> []
  | x :: xs ->
      if List.mem x lst2 then
        remove_elements xs lst2
      else
        x :: remove_elements xs lst2

(*Returns Union in normal form*)   
(*TODO?: return Any if t is Union (Int, String, Array Any ...)*)                     
let rec fix_union t =  let rec flattern_type t = match t with 
                                                              | Array et -> Array (flattern_type et)
                                                              | Callable (args, ret) -> Callable (List.map flattern_type args, flattern_type ret)
                                                              | Union ts -> let rec flatterned_types = List.map flattern_type (List.rev ts) in
                                                                            let fixed = List.fold_left (fun ls t -> match t with Union ts -> List.concat [ls;ts] | _ -> t::ls) [] flatterned_types
                                                                            in Union fixed
                                                              | Tuple ts -> Tuple (List.map flattern_type ts)
                                                              | _ -> t
                                in   
                                let t = 
                                          match flattern_type t with 
                                          | Union ls -> Union (remove_duplicates ls)
                                          | t -> t
                                in match t with Union ls -> if List.length ls = 1 then List.hd ls else Union ls | _ -> t

(*Removes loc info. If returns Union, then Union in normal form, i.e Union is flat and dont contains duplicates*)
let type_from_type_flow tf = fix_union (Union (List.map fst tf))



(*Accept only normal unions. Accepts only TyIds. Dont accept Tvar, VariantType, RecursiveType*)
let rec is_consistent_helper t1 t2 = (*Printf.printf "ABOBA\nt1:%s\nt2:%s\nt1 fixed:%s\nt2 fixed:%s\n" (type_to_string t1) (type_to_string t2) (type_to_string (fix_union t1)) (type_to_string (fix_union t2)) ;*) assert ( (t1 = fix_union t1) && (t2 = fix_union t2)) ; match (t1, t2) with 
  | TVar _ , _ -> raise (Failure "Tvar don't describe any value and cant't be used in \"is_consistent\"")
  | _ , TVar _ -> raise (Failure "Tvar don't describe any value and cant't be used in \"is_consistent\"")

  | VariantType _, _ -> raise (Failure "VariantType don't makes sense itself and cant't be used in \"is_consistent\"")
  | _, VariantType _ -> raise (Failure "VariantType don't makes sense itself and cant't be used in \"is_consistent\"")

  | RecursiveType _, _ -> raise (Failure "RecursiveType don't makes sense itself and cant't be used in \"is_consistent\"")
  | _, RecursiveType _ -> raise (Failure "RecursiveType don't makes sense itself and cant't be used in \"is_consistent\"")

  | TyId i1, TyId i2 -> i1 = i2 
  | TyId i1, Union ls -> List.fold_left (||) false (List.map (is_consistent (TyId i1)) ls)
  | TyId _, _ -> false

  | Any, _ -> true
  | _, Any -> true

  | Sexp, Sexp -> true
  | Sexp, Union ls -> List.fold_left (||) false (List.map (is_consistent Sexp) ls)
  | Sexp, _ -> false

  | Int, Int -> true
  | Int, Union ls -> List.fold_left (||) false (List.map (is_consistent Int) ls)
  | Int, _ -> false

  | String, String -> true
  | String, Union ls -> List.fold_left (||) false (List.map (is_consistent String) ls)
  | String, _ -> false

  | Array e1t, Array e2t -> is_consistent e1t e2t
  | Array e1t, Union ls -> List.fold_left (||) false (List.map (is_consistent (Array e1t)) ls)
  | Array _ , _ -> false

  (*Callable may be wrong*)
  | Callable (atls1, rt1), Callable (atls2, rt2) -> is_consistent rt1 rt2 && ( (List.length atls1) = (List.length atls2) && List.fold_left (fun acc (t1, t2) -> acc && (is_consistent t1 t2)) true (List.combine atls1 atls2) )
  | Callable (atls1, rt1), Union ls -> List.fold_left (||) false (List.map (is_consistent (Callable (atls1, rt1))) ls)
  | Callable (_, _), _ -> false
  
  | Unit, Unit -> true
  | Unit, Union ls -> List.fold_left (||) false (List.map (is_consistent Unit) ls)
  | Unit, _ -> false

  | Tuple lts, Tuple rts -> if List.length lts <> List.length rts then false else 
                            List.fold_left (&&) true (List.map (fun (t1,t2) -> is_consistent t1 t2) (List.combine lts rts))
  | Tuple ts, Union ls -> List.fold_left (||) false (List.map (is_consistent (Tuple ts)) ls)
  | Tuple _, _ -> false

  | Union [],_ -> false (*true*) (*OR failure or false?*)
  | Union l, Union r-> List.fold_left (fun acc t -> acc && is_consistent t (Union r)) true l
  | Union _, _ -> false

and is_consistent t1 t2 = is_consistent_helper (fix_union t1) (fix_union t2)  

(*equal = describe the same sets of values*)
(*TODO: possible bug. Should call are_types_equal instead of are_types_equal_helper*)
let are_types_equal t1 t2 =   Printf.printf "Outer f\n"; flush stdout; 
                              let rec are_types_equal_helper t1' t2' =  (Printf.printf "Checking equality of\n %s \nAND\n %s\n" (type_to_string t1') (type_to_string t2'); flush stdout; match (t1', t2') with 
                                                                        | TVar _ , _ -> raise (Failure "Tvar don't describe any value and cant't be used in \"are_types_equal\"")
                                                                        | _ , TVar _ -> raise (Failure "Tvar don't describe any value and cant't be used in \"are_types_equal\"")
                                                                      
                                                                        | VariantType _, _ -> raise (Failure "VariantType don't makes sense itself and cant't be used in \"are_types_equal\"")
                                                                        | _, VariantType _ -> raise (Failure "VariantType don't makes sense itself and cant't be used in \"are_types_equal\"")
                                                                      
                                                                        | RecursiveType _, _ -> raise (Failure "RecursiveType don't makes sense itself and cant't be used in \"are_types_equal\"")
                                                                        | _, RecursiveType _ -> raise (Failure "RecursiveType don't makes sense itself and cant't be used in \"are_types_equal\"")
                                                                      
                                                                        | TyId i1, TyId i2 -> i1 = i2 
                                                                        | TyId i1, Union ls -> List.length ls <> 0 && List.fold_left (fun acc t -> acc && are_types_equal_helper t (TyId i1)) true ls
                                                                        | TyId _, _ -> false                                          

                                                                        | (Any, Any) -> true
                                                                        | (Any, Union ls) -> List.mem Any ls (*|| List.mem ls Int && Array Any && String && Unit ... *)
                                                                        | (Any, _) -> false

                                                                        | (Sexp, Sexp) -> true
                                                                        | Sexp, Union ls -> List.length ls <> 0 && List.fold_left (fun acc t -> acc && are_types_equal_helper t Sexp) true ls
                                                                        | Sexp, _ -> false

                                                                        | (Int, Int) -> true
                                                                        | Int, Union ls -> List.length ls <> 0 && List.fold_left (fun acc t -> acc && are_types_equal_helper t Int) true ls
                                                                        | Int, _ -> false

                                                                        | String, String -> true
                                                                        | String, Union ls -> List.length ls <> 0 && List.fold_left (fun acc t -> acc && are_types_equal_helper t String) true ls
                                                                        | String, _ -> false 

                                                                        | Array t1, Array t2 -> are_types_equal_helper t1 t2
                                                                        | Array t1, Union ls -> List.length ls <> 0 && List.fold_left (fun acc t -> acc && are_types_equal_helper t (Array t1)) true ls
                                                                        | Array _, _ -> false

                                                                        | Callable (atls1, rt1), Callable (atls2, rt2) -> are_types_equal_helper rt1 rt2 && List.length atls1 = List.length atls2 && List.fold_left (fun acc (t1, t2) -> acc && (are_types_equal_helper t1 t2)) true (List.combine atls1 atls2)
                                                                        | Callable (atls1, rt1), Union ls -> List.length ls <> 0 && List.fold_left (fun acc t -> acc && are_types_equal_helper t (Callable (atls1, rt1))) true ls
                                                                        | Callable _ , _ -> false

                                                                        | Unit, Unit -> true
                                                                        | Unit, Union ls -> List.length ls <> 0 && List.fold_left (fun acc t -> acc && are_types_equal_helper t Unit) true ls
                                                                        | Unit, _ -> false

                                                                        | Tuple lts, Tuple rts -> if List.length lts <> List.length rts then false else
                                                                                                  List.fold_left (&&) true (List.map (fun (t1, t2) -> are_types_equal_helper t1 t2) (List.combine lts rts))
                                                                        | Tuple ts, Union ls -> List.length ls <> 0 && List.fold_left (fun acc t -> acc && are_types_equal_helper t (Tuple ts)) true ls
                                                                        | Tuple _, _ -> false

                                                                        | Union l, Union r -> if List.mem Any l || List.mem Any r then let (lFixed, rFixed) = ((if List.mem Any l then Any else Union l), if List.mem Any r then Any else Union r) in
                                                                                              are_types_equal_helper lFixed rFixed
                                                                                              else (List.fold_left (fun acc tl -> acc && List.fold_left (fun acc tr -> acc || are_types_equal_helper tl tr) false r) true l) && (List.fold_left (fun acc tr -> acc && List.fold_left (fun acc tl -> acc || are_types_equal_helper tr tl) false l) true r)
                                                                        | Union ls, t -> (*transform to case t, Un(List.fold_left (fun acc tr -> acc || List.fold_left (fun acc tl -> acc || are_types_equal_helper tl tr) acc l) false r)ion*) are_types_equal_helper t (Union ls)
                                                                        )
                              in are_types_equal_helper (fix_union t1) (fix_union t2)                                           
(*
let rec is_consistent_patt patt t = match patt with 
                                      Pattern.Wildcard -> true
                                      | Pattern.Sexp _ -> is_consistent Sexp t
                                      | Pattern.Array _ -> is_consistent (Array Any) t
                                      | Pattern.Named (_, p) -> is_consistent_patt p t
                                      | Pattern.Const _ -> is_consistent Int t 
                                      | Pattern.String _ -> is_consistent String t 
                                      | Pattern.Boxed -> raise (Failure "not implemented patt")
                                      | Pattern.UnBoxed -> raise (Failure "not implemented patt")
                                      | Pattern.StringTag -> is_consistent String t 
                                      | Pattern.SexpTag -> is_consistent Sexp t 
                                      | Pattern.ArrayTag -> is_consistent (Array Any) t 
                                      | Pattern.ClosureTag -> raise (Failure "not implemented patt")

*)
module TypeContext : sig
  type type_flow_t = (lamaType * Loc.t option) list
  type t = ((string * (lamaType * type_flow_t)) list) * ((string * lamaType) list )(* (variable * (type annotation * (lamaType * typeLoc) list)) * (variant type list)*)
  (*
  val add_type_to_type_flow : t -> string -> (lamaType * Loc.t option) -> t
  val add_types_to_type_flow : t -> string -> type_flow_t -> t
  *)
  val set_type_flow_types : t -> string -> type_flow_t -> t
  val update_ctx : t -> (string * lamaType) list -> t
  val merge_ctxs : t -> t  -> t
  val update_outer_context : t -> t -> string list -> t
  val empty_type_flow : type_flow_t
  val empty_ctx : t
  val get_var_type_flow : t -> string -> type_flow_t
  val get_var_type : t -> string -> lamaType  
  val to_string : t -> string
  (*
  val lamaTypeAnnotationTolamaType : t -> lamaTypeAnnotation -> lamaType
  *)
  (*
  val allDefinedTypes : t -> string list (*TODO: remove?*)
  *)
  val simplifyTy : t -> lamaType -> lamaType
  val getConstrType : t -> string -> lamaType
  val getTypeByCtrName : t -> string -> (string * lamaType)
  val getTyBinding : t -> string -> lamaType
end = struct
  type type_flow_t = (lamaType * Loc.t option) list
  type t = ((string * (lamaType * type_flow_t)) list) * ((string * lamaType) list)
  let empty_type_flow = []
  let empty_ctx = ([], [])
  
  let rec set_type_flow_types' ctx var ts = match ctx with 
                                                  [] -> raise (Failure (Printf.sprintf "Undefined variable %s" var))
                                                  | (v, (va, tf))::ctx -> if var = v then (
                                                                                          v, 
                                                                                          (va, ts)
                                                                                          )::ctx
                                                                          else (v, (va, tf))::(set_type_flow_types' ctx var ts)
  let set_type_flow_types (tf_ctx, td_ctx) var ts = (set_type_flow_types' tf_ctx var ts, td_ctx)
  
  (*Sets ts from inner ctx in outer ctx, excepl local variables of inner ctx*)
  let update_outer_context' outer_ctx inner_ctx inner_locals = List.fold_left (fun o (var, (_, type_flow)) -> if List.mem var inner_locals then o else set_type_flow_types' o var type_flow) outer_ctx inner_ctx
  let update_outer_context (outer_ctx, td_outer) (inner_ctx, td_innner) inner_locals = assert (td_outer = td_innner); (update_outer_context' outer_ctx inner_ctx inner_locals, td_outer)
  
  (*TODO: check that type is compatible with annotation*)
  let rec add_type_to_type_flow' ctx var (new_type, new_type_loc) = match ctx with
                                                          [] -> raise (Failure (Printf.sprintf "Undefined variable %s" var))
                                                        | (v, (va, tf)):: ctx -> if var = v then  (
                                                          v, 
                                                          ( va, (if not (is_consistent new_type va) then raise (Failure (Printf.sprintf "Type %s of value is incompatible with variable \'%s\' type annotation %s" (type_to_string new_type) (var) (type_to_string va)));
                                                                if List.mem (new_type, new_type_loc) tf then tf else (new_type, new_type_loc)::tf)
                                                          )
                                                        ) ::ctx else (v, (va, tf)):: add_type_to_type_flow' ctx var (new_type, new_type_loc)
  let add_type_to_type_flow (ctx, td) var t = (add_type_to_type_flow' ctx var t, td)
                                                       
  let add_types_to_type_flow' ctx var ts = List.fold_left (fun ctx t -> add_type_to_type_flow' ctx var t) ctx ts
  let add_types_to_type_flow (ctx, td) var ts = (add_types_to_type_flow' ctx var ts, td)
  
  (*Updates context with variable names and type annotations. If variable exist in old context, annotation and type flow discarded and replaced with new annotation and empty type flow*)
  let update_ctx' ctx vars = List.fold_left (fun ctx' (var, anType) -> (var, (anType, empty_type_flow))::ctx') (List.filter (fun (vname, _) -> not (List.mem vname (List.map fst vars))) ctx) vars
  let update_ctx (ctx, td) vars = (update_ctx' ctx vars, td)

  (*Merges type flows of contexts*)
  let merge_ctxs' ctx1 ctx2 = List.fold_left (fun o (var, (_, type_flow)) -> add_types_to_type_flow' o var type_flow) ctx1 ctx2
  let merge_ctxs (ctx1, td1) (ctx2, td2) = assert (td1 = td2); (merge_ctxs' ctx1 ctx2, td1)
  

  let rec get_var_type_flow' ctx var = match ctx with 
                                            [] -> raise (Failure (Printf.sprintf "Undefined variable %s" var))
                                            | (v, (_, tflow))::ctx' -> if var = v then tflow else get_var_type_flow' ctx' var
  let get_var_type_flow (ctx, _) var = get_var_type_flow' ctx var
  
  let rec get_var_type' ctx var = match ctx with 
                                        [] -> raise (Failure (Printf.sprintf "Undefined variable %s" var))
                                        | (v, (vt, _ )) :: ctx' -> if var = v then vt else get_var_type' ctx' var
  let get_var_type (ctx, _) = get_var_type' ctx
  
  let to_string (ctx, _) = String.concat "\n" (List.map (fun (var, (vt, vtf)) -> Printf.sprintf "(%s, (%s, %s))" var (type_to_string vt) (String.concat "," (List.map (fun (t, _) -> Printf.sprintf "(%s, ?)" (type_to_string t)) vtf)) ) ctx)
  
  let getTypeByCtrName' ctx c =   try List.find (fun (_, t) -> match t with 
                                                                              RecursiveType (_, VariantType ls) -> List.mem c (List.map fst ls)
                                                                              | _ -> false
                                                ) ctx 
                                  with Not_found -> raise (Failure (Printf.sprintf "Undefined constructor %s" c))

  let getTypeByCtrName ctx c = getTypeByCtrName' (snd ctx) c

  let getConstrType ctx c = let (_, RecursiveType (_, VariantType ls)) = getTypeByCtrName ctx c
                            in List.assoc c ls
  
  (*
  let rec getVariantDefByName' tds tname = match tds with 
                                                      [] -> raise (Failure (Printf.sprintf "Undefined type %s" tname))
                                                      | (vname, ctrs)::tds when vname = tname -> VariantType (vname, ctrs)
                                                      | _ -> getVariantDefByName' (List.tl tds) tname
  let getVariantDefByName (_, tds) tname = getVariantDefByName' tds tname
  *)

  
  (* TODO: remove
  let rec lamaTypeAnnotationTolamaType ta = match ta with  
                                                          TA_Sexp -> Sexp
                                                        | TA_Int -> Int
                                                        | TA_String -> String
                                                        | TA_Array ta -> Array (lamaTypeAnnotationTolamaType ta)
                                                        | TA_Any -> Any
                                                        | TA_Callable (ls, ta) -> Callable (List.map lamaTypeAnnotationTolamaTypels, lamaTypeAnnotationTolamaType ta)
                                                        | TA_Unit -> Unit
                                                        | TA_Union ls -> Union (List.map lamaTypeAnnotationTolamaType ls)
                                                        | TA_Tuple ls -> Tuple (List.map lamaTypeAnnotationTolamaType ls)
                                                        | TA_TypeId t -> TyId t
  *)
  (*
  let rec allDefinedTypes (_, ctx) = List.fold_left (fun ls (tname, _) -> tname::ls) [] ctx
  *)


  let rec getTyBinding' ctx binding = match ctx with
                                               | [] -> raise (Failure (Printf.sprintf "Undefined type binding %s" binding))
                                               | (b, t)::_ when b = binding -> t 
                                               | _ -> getTyBinding' (List.tl ctx) binding
  let getTyBinding ctx binding = getTyBinding' (snd ctx) binding
  
  exception NoRuleApplies
  let computeTy ctx tyT = match tyT with
      TyId tname -> getTyBinding ctx tname
    | _ -> raise NoRuleApplies
  
  let rec simplifyTy ctx tyT =
    try
      let tyT' = computeTy ctx tyT in
      simplifyTy ctx tyT' 
    with NoRuleApplies -> tyT
    
end

let rec collect_refs e = match e with (*TODO: more precise analysis*)
                                Expr.Ref v -> [v]
                                | Expr.Seq ( _ , s2) -> collect_refs s2
                                | Expr.If (_, s1, s2) -> (collect_refs s1) @ (collect_refs s2)
                                | _ -> []

let rec check_pattern_type ctx p =
  match p with 
  Pattern.Wildcard -> (Any, ctx)
  | Pattern.Tuple ps -> let (pts, ctx) = List.fold_left (fun (pts, ctx) p -> let (pt, ctx) = check_pattern_type ctx p in (pt::pts, ctx)) ([], ctx) ps
                        in (Tuple (List.rev pts), ctx)
  | Pattern.Sexp (_, ps) -> let ctx  = List.fold_left (fun ctx p -> let (_, ctx) = check_pattern_type ctx p in ctx) ctx ps in (Sexp, ctx)
  | Pattern.Array ps -> let (ptd, ctx) = List.fold_left (fun (ts, ctx) p -> let (pt, ctx) = check_pattern_type ctx p in ((if List.mem pt ts then ts else pt::ts), ctx)) ([], ctx) ps
                in if List.length ptd = 0 then (Array Any, ctx) else
                  (
                    if List.length ptd = 1 then (Array (List.hd ptd), ctx)
                    else (Array (Union ptd), ctx)
                  )
  | Pattern.Named (name, p) -> let (t, ctx) = check_pattern_type ctx p in (t, TypeContext.update_ctx ctx [(name, t)])
  | Pattern.Const _ -> (Int, ctx)
  | Pattern.String _ -> (String, ctx)
  | Pattern.Boxed -> (Any, ctx) (*???*)
  | Pattern.UnBoxed -> (Any, ctx) (*???*)
  | Pattern.StringTag -> (String, ctx)
  | Pattern.SexpTag -> (Sexp, ctx)
  | Pattern.ArrayTag -> (Array Any, ctx)
  | Pattern.ClosureTag -> (Any, ctx) (*TODO*)
  | Pattern.DataConstr (c, p) ->  let (p_type, _) = check_pattern_type ctx p 
                                  in let ctr_arg_type = TypeContext.getConstrType ctx c
                                  in  if not (is_consistent ctr_arg_type p_type) then
                                                                                   raise (Failure (Printf.sprintf "Type constructor %s has type %s, but type of pattern was %s" c (type_to_string ctr_arg_type) (type_to_string p_type)))
                                      else  let tyName = fst (TypeContext.getTypeByCtrName ctx c) 
                                            in (TyId tyName, ctx)



(*TODO on this stage save locs for the understandable error messages*)


let rec collect_variant_defs' expr = match expr with 
                                            Expr.Scope (ds, e) -> 
                                              let defs = List.fold_left (fun ls (tname, tdecl) -> match tdecl with 
                                                                                                            (_, `Fun _) -> ls
                                                                                                            | (_, `Variable _) -> ls
                                                                                                            | (_, `VariantTypeDecl ctrs) -> (tname, ctrs)::ls                                                       
                                                                        ) [] ds
                                              in List.concat [defs;collect_variant_defs' e]
                                            | Expr.Seq (e1, e2) -> List.concat [collect_variant_defs' e1; collect_variant_defs' e2]
                                            | _ -> []
  
let collect_variant_defs expr = let defs = collect_variant_defs' expr in  
                                              let rec has_cycle node graph visited =
                                                if List.mem node visited then
                                                  raise (Failure "Mutual recursive type defenitions") (* Cycle found *)
                                                else
                                                  match List.assoc_opt node graph with
                                                  | None -> () (*No deps for node *)
                                                  | Some dependencies ->
                                                      List.iter (fun dep -> has_cycle dep graph (node :: visited)) dependencies
                                              in
                                              let check_mutual_recursion defs =
                                                let graph =
                                                  List.map  (fun  (tname, ctrs) -> (tname, List.fold_left (fun ls (_, ctr) ->
                                                                                                                        match ctr with  
                                                                                                                        TA_TypeId t -> t :: ls
                                                                                                                        | _ -> ls 
                                                                                                          ) [] ctrs
                                                                                  )
                                                            ) defs
                                                in
                                                List.iter (fun (node, _) -> has_cycle node graph []) graph
                                              in 
                                              check_mutual_recursion defs;
                                              let rec replaceTyIdWithTyVar typeId typeVar t = match t with 
                                                                                                          Sexp -> Sexp
                                                                                                          | Int -> Int
                                                                                                          | String -> String
                                                                                                          | Array t -> Array (replaceTyIdWithTyVar typeId typeVar t)
                                                                                                          | Any -> Any
                                                                                                          | Callable (ats, rt) -> Callable (List.map (replaceTyIdWithTyVar typeId typeVar) ats, replaceTyIdWithTyVar typeId typeVar rt)
                                                                                                          | Unit -> Unit
                                                                                                          | Union ts -> Union (List.map (replaceTyIdWithTyVar typeId typeVar) ts)
                                                                                                          | Tuple ts -> Tuple (List.map (replaceTyIdWithTyVar typeId typeVar) ts)
                                                                                                          | TVar t -> TVar t
                                                                                                          | VariantType ls -> VariantType (List.combine (List.map fst ls) (List.map (replaceTyIdWithTyVar typeId typeVar) (List.map snd ls)))
                                                                                                          | RecursiveType (v, t) -> RecursiveType (v, replaceTyIdWithTyVar typeId typeVar t)
                                                                                                          | TyId typeId' -> if typeId = typeId' then TVar typeVar else TyId typeId'
                                              in
                                              let make_rec_type def = let tname = fst def in let ctrs = snd def in let freshVar = "TODOfreshVar. FIX: better typename as var" in 
                                                                                                                      RecursiveType (freshVar, replaceTyIdWithTyVar tname freshVar (VariantType ctrs))
                                              in List.fold_left (fun ctx def -> let tname = fst def in (tname, make_rec_type def)::ctx) [] 
                                                                (List.map (fun (tname, ctrs) -> (tname, List.map (fun (c, ta) -> (c,lamaTypeAnnotationTolamaType2 ta)) ctrs)) defs)
                                            

(*

let collect_variant_defs expr = let defs = collect_variant_defs' expr in
                                List.iter (fun (VariantType (tname, _)) -> 
                                    if List.mem tname (List.map fst defs) then 
                                      raise (Failure (Printf.sprintf "Type %s redefenition" tname))) defs; (*check that every type defined only once*)
                                let rec check_variants_defined t ds = match t with 
                                                                          Sexp -> ()
                                                                          | Int -> ()
                                                                          | String -> ()
                                                                          | Array t -> check_variants_defined t ds
                                                                          | Any ->  ()
                                                                          | Callable (ts, t) -> List.map (fun t -> check_variants_defined t ds) ts; check_variants_defined t ds
                                                                          | Unit -> ()
                                                                          | Union ts -> List.map (fun t -> check_variants_defined t ds) ts
                                                                          | Tuple ts -> List.map (fun t -> check_variants_defined t ds) ts
                                                                          | VariantType (vname, ctrs) -> if not (List.mem vname (List.map fst defs)) then raise (Failure (Printf.sprintf "Type %s is not defined")); List.map (fun t -> check_variants_defined t ds) (List.map snd ctrs)
                                in 
                                List.iter (fun t -> check_variants_defined t defs) defs; (*check that all variant types in types of constructors exists*)
                                let allCtrs = List.concat (List.map (fun (VariantType (vname, ctrs)) -> List.map fst ctrs) defs) in
                                let rec getGetVariantNameFromCtrName ctr_name ds = match ds with 
                                                                                            [] -> []
                                                                                            | (VariantType (vname, ctrs))::ds when List.mem ctr_name (List.map fst ctrs) -> vname::(getGetVariantNameFromCtrName ctr_name ds)
                                                                                            | _ -> getGetVariantNameFromCtrName ctr_name (List.tl ds)
                                in
                                let ctrs_and_variants = List.map (fun ctr -> (ctr, getGetVariantNameFromCtrName ctr defs)) allCtrs
                                in List.iter (fun (ctr, vars) -> if List.length vars <> 1 then raise (Failure (Printf.sprintf "Different types [%s] have the same constructor %s" (String.concat "," vars) ctr))) ctrs_and_variants; (*check that ctrs is unique*)
                                () (*TODO: more checks. For example, data X = xc of Y ; data Y = yc of X - invalid defenitions*)
                                      
                                *)

(*only checks annotations. returns type of expresion*)
let rec check_annotations (ctx : TypeContext.t ) (e : Expr.t ) : lamaType =
  match e with 
  | Expr.Const (_, _) -> Int
  | Expr.Array e_ls ->  if List.length e_ls = 0 then Array Any 
                        else(
                          let elem_t_list = List.fold_left 
                                            (fun l e ->  let e_t = check_annotations ctx e 
                                                                in if List.mem e_t l then l else e_t::l ) 
                                            [] e_ls
                          in if List.length elem_t_list = 1 then Array (List.hd elem_t_list) else Array (Union elem_t_list)
                        )
  | Expr.String _ -> String
  | Expr.Sexp (_, ls) -> List.iter (fun e -> ignore (check_annotations ctx e)) ls; Sexp
  | Expr.Var v -> TypeContext.get_var_type ctx v
  | Expr.Ref v -> TypeContext.get_var_type ctx v (*raise (Failure "Error. Never typecheck ref without assign") *) (*TypeContext.get_var_type_flow ctx v, ctx*)
  | Expr.Binop (_, e1, e2) -> let e1_type = check_annotations ctx e1 in
                              let e2_type = check_annotations ctx e2 in
                              if is_consistent e1_type Int && is_consistent e2_type Int then Int else raise (Failure "Binop type check error")
  | Expr.Elem (e, index)   ->   let e_type  = check_annotations ctx e in
                                let index_type = check_annotations ctx index in
                                if not @@ is_consistent e_type (Union [Sexp; Array Any; String]) then 
                                                                                                  raise (Failure ( Printf.sprintf "Elem error. Left is [%s], but not Sexp, Array, String" (type_to_string e_type)))
                                else (
                                      if not @@ is_consistent index_type Int then raise (Failure "Elem error. Right is not int") else
                                
                                      let elem_type = match e_type with 
                                                      Any -> Any
                                                      | Sexp -> Any
                                                      | Array t -> t 
                                                      | String -> Int
                                                      | _ -> raise (Failure (Printf.sprintf "Bug. e_type can be only Any, Sexp, Array, String, but was %s" (type_to_string e_type)))
                                      in elem_type
                                )
  | Expr.ElemRef (e, index)   ->   let e_type  = check_annotations ctx e in
                                let index_type = check_annotations ctx index in
                                if not @@ is_consistent e_type (Union [Sexp; Array Any; String]) then 
                                                                                                  raise (Failure ( Printf.sprintf "ElemRef error. Left is [%s], but not Sexp, Array, String" (type_to_string e_type)))
                                else (
                                      if not @@ is_consistent index_type Int then raise (Failure "ElemRef error. Right is not int") else
                                
                                      let elem_type = match e_type with 
                                                      Any -> Any
                                                      | Sexp -> Any
                                                      | Array t -> t 
                                                      | String -> Int
                                                      | _ -> raise (Failure (Printf.sprintf "Bug. e_type can be only Any, Sexp, Array, String, but was %s" (type_to_string e_type)))
                                      in elem_type
                                )
  | Expr.Assign (v, e) -> let () = ignore (check_annotations ctx v) in
                          let e_type = check_annotations ctx e in
                          let refs = collect_refs v in
                          List.iter (fun ref -> if not (is_consistent ref e_type) then (raise (Failure "assign type error"))) (List.map (fun v -> TypeContext.get_var_type ctx v) refs); e_type
  | Expr.Seq (e1, e2) -> ignore (check_annotations ctx e1); check_annotations ctx e2
  | Expr.Skip -> Unit
  | Expr.If (e, thene, elsee) ->  ignore (check_annotations ctx e); 
                                  let then_type = check_annotations ctx thene in
                                  let else_type = check_annotations ctx elsee in
                                  if then_type <> else_type then  Union [then_type; else_type] else then_type(*Or check that then_t = else_t? Or guess what type is expected and compare with it*)
  | Expr.While (cond, body) ->  let _ = check_annotations ctx cond 
                                in let _ =  check_annotations ctx body
                                in Unit
  | Expr.DoWhile (body, cond) ->  let _ = check_annotations ctx cond 
                                in let _ =  check_annotations ctx body
                                in Unit
  | Expr.Ignore e -> ignore (check_annotations ctx e); Unit        
  | Expr.Unit -> Unit
  | Expr.Scope (ds, e) -> let ctx = List.fold_left  (fun ctx (vname, vdecl) -> 
                                                      match vdecl with    
                                                      
                                                      (_, `Variable (init, v_typea)) ->  
                                                          let v_type = lamaTypeAnnotationTolamaType2 v_typea in 
                                                                                          (
                                                                                          match init with 
                                                                                                Some e -> let init_t = check_annotations ctx e in
                                                                                                          if is_consistent init_t v_type then () (*Ok*) else raise (Failure (Printf.sprintf "Type %s is not consistent with type %s" (type_to_string init_t) (type_to_string v_type) ))
                                                                                                | None -> ()
                                                                                          );
                                                                                          TypeContext.update_ctx ctx [(vname, v_type)]
                                                      | (_, `Fun (_, _, fun_t) ) -> TypeContext.update_ctx ctx [(vname,
                                                                                                                          lamaTypeAnnotationTolamaType2 fun_t)]
                                                      | (_, `VariantTypeDecl _) -> ctx (*TODO*)
                                                    ) ctx ds
                          in
                          List.iter (fun (fname, d) -> match d with 
                          (_, `Variable _) -> ()
                          | (_, `Fun (args, body , TA_Callable (args_t, ret_t)) ) ->  
                                                                if List.length args <> List.length args_t then raise (Failure (Printf.sprintf "Incorrect function %s type. Argument lenght mismatch" fname));
                                                                let ctx = TypeContext.update_ctx ctx (List.combine args (List.map lamaTypeAnnotationTolamaType2 args_t))
                                                                in let actual_ret_type = check_annotations ctx body 
                                                                in if not @@ is_consistent actual_ret_type (lamaTypeAnnotationTolamaType2 ret_t) then raise (Failure (Printf.sprintf "Actual return type %s is not consistent with declared %s" (type_to_string actual_ret_type) (type_to_string (lamaTypeAnnotationTolamaType2 ret_t))))
                          
                          | (_, `Fun (args, body, TA_Any)) ->  let ctx = TypeContext.update_ctx ctx (List.map (fun x -> (x, Any)) args)
                                                            in let _ = check_annotations ctx body in ()
                          | (_, `Fun _) -> raise (Failure "Incorrect function type")
                          | (_, `VariantTypeDecl _) -> () (*TODO*)
                          ) ds;
                          check_annotations ctx e
  | Expr.Call (fun_expr, args) -> let args_t = List.fold_left (fun args_t arg -> (check_annotations ctx arg)::args_t) [] args          
                                  in let args_t = List.rev args_t
                                  in let process_func f_type args_t = match f_type with 
                                                                      Any -> Any (*Any ~ [Any...] - > Any*)
                                                                      | Callable (f_args_t, ret_t) -> 
                                                                                                  if List.length f_args_t <> List.length args_t then raise (Failure (Printf.sprintf "Argument size mismatch. Function requares %d, but %d was given" (List.length f_args_t) (List.length args_t))) else ();
                                                                                                  List.iter (fun (actual_arg, expected_fun_arg) -> if not @@ is_consistent actual_arg expected_fun_arg then raise (Failure "arg type mismatch")) @@ List.combine args_t f_args_t;
                                                                                                  ret_t
                                                                      | _ -> raise (Failure "Invalid function type")
                                    in let return_ts = match check_annotations ctx fun_expr with
                                                                    Union ftls -> List.fold_left (fun acc ft -> (process_func ft args_t)::acc) [] ftls
                                                                    | t -> [process_func t args_t ]
                                    in (match return_ts with 
                                                      [t] -> t
                                                      | _ -> Union return_ts
                                    )
  | Expr.Tuple es -> Tuple (List.map (check_annotations ctx) es)
  | Expr.Case (e, bs, _, _) ->  let e_t = check_annotations ctx e in
                                let pts = List.map fst bs in
                                let ptsTs = List.map (fun p -> let (pt, _ ) = check_pattern_type ctx p in pt) (List.map fst bs)
                                in 
                                (*checking exhaustiveness for non variant types*)
                                if not (is_consistent e_t (Union ptsTs)) then raise (Failure  (Printf.sprintf "Patterns is not exhaustive. Type of e: (%s) type, but patterns decribes (%s)" (type_to_string e_t) (type_to_string (Union ptsTs))  ) );
                                
                                (*checking for unness*)
                                List.iter (fun (p, pt) -> if not (is_consistent pt e_t) then raise (Failure (Printf.sprintf "Scrutinee has type %s, but unnecessary pattern of type %s found" (type_to_string e_t) (type_to_string pt)))) (List.combine (List.map fst bs) ptsTs ); 
                                
                                (*checking exhaustiveness for variant types*)
                                let all_data_type_ctrs = List.fold_left (fun ls p -> match p with Pattern.DataConstr (cname, _) -> cname::ls | _ -> ls) [] pts in
                                let all_data_types = List.fold_left (fun tyIds c -> let tname = fst (TypeContext.getTypeByCtrName ctx c) in if List.mem tname tyIds then tyIds else tname::tyIds) [] all_data_type_ctrs in
                                let all_required_type_ctrs = List.fold_left (fun ctrs t -> match TypeContext.getTyBinding ctx t with 
                                                                                                                              RecursiveType (_, VariantType ls) -> List.append (List.map fst ls) ctrs
                                                                                                                              | _ -> raise (Failure "Bug")
                                                                            ) [] (remove_duplicates all_data_types) in
                                let ctrs_without_pattern = remove_elements all_required_type_ctrs all_data_type_ctrs in
                                if (ctrs_without_pattern <> []) && (not (List.mem Pattern.Wildcard pts)) then raise (Failure (Printf.sprintf "Partial match. List of constructors that don't have appropriate pattern: %s" (String.concat "," ctrs_without_pattern)));
                                

                                (*Checking pattern bodies*)
                                let res_t_ls = List.map (fun (p, b) -> let (_, ctx) = check_pattern_type ctx p in check_annotations ctx b) bs
                                in  let res_t_ls = remove_duplicates res_t_ls in
                                    if List.length res_t_ls = 1 then List.hd res_t_ls else Union res_t_ls
  | Expr.DataConstr _ -> Any
  (*maybe its unnecessary when checking annotations*)
  | Expr.UnRoll ta -> let ty = lamaTypeAnnotationTolamaType2 ta in
                                    (
                                    match TypeContext.simplifyTy ctx ty with 
                                                    RecursiveType (x, t) -> (*TODO assert for x and typename*)
                                                                            Callable ([ty], tySubst x ty t)
                                                  | _ -> raise (Failure  (Printf.sprintf "Recursive type expected"))
                                    )
  | Expr.Roll ta -> let ty = lamaTypeAnnotationTolamaType2 ta in
                                    (
                                    match TypeContext.simplifyTy ctx ty with 
                                                    RecursiveType (x, t) -> (*TODO assert for x and typename*)
                                                                            Callable ([tySubst x ty t], ty)
                                                  | _ -> raise (Failure  (Printf.sprintf "Recursive type expected"))
                                    )
  | _ -> raise (Failure "Not implemented2")


(*returns list of possible types of expression + context updated with new type flow content. *)
let rec check_expr_type_flow (ctx : TypeContext.t ) (e : Expr.t ) : (TypeContext.type_flow_t * TypeContext.t) =
  let rec check_cycle cycle_ctx cycle = (
    let (_, new_ctx) = check_expr_type_flow cycle_ctx cycle
    in  let changed = (cycle_ctx <> TypeContext.merge_ctxs cycle_ctx ctx) (*or even cycle_ctx <> new_ctx*)
        in if changed then check_cycle new_ctx cycle else new_ctx
  )
  in
  match e with
  | Expr.Const (_, l)       -> ([(Int, Some l)], ctx)
  | Expr.Array ls      -> if List.length ls = 0 then ([(Array Any, None)], ctx) else  let (e_ts, ctx) = List.fold_left (fun (t, ctx) e ->   let (e_t, ctx) = check_expr_type_flow ctx e 
                                                                                                                                            in ( List.fold_left ( fun t e_t -> if List.mem e_t t then t else e_t::t ) t e_t, ctx)) ([], ctx) ls 
                                                                                      in ((if List.length e_ts = 1 then [(Array (fst(List.hd e_ts)), None)] else [(Array (Union (List.map fst e_ts)), None)]), ctx)
  | Expr.String _      -> ([(String, None)], ctx)
  | Expr.Sexp (_, ls)  -> ([(Sexp, None)], List.fold_left (fun ctx e -> let (_, inner_ctx) = check_expr_type_flow ctx e in inner_ctx) ctx ls)
  | Expr.Var v         -> (TypeContext.get_var_type_flow ctx v, ctx)
  | Expr.Ref v         -> (TypeContext.get_var_type_flow ctx v, ctx) (*raise (Failure "Error. Never typecheck ref without assign") *) (*TypeContext.get_var_type_flow ctx v, ctx*)
  | Expr.Binop (_, e1, e2) ->  let (e1_type, e1_ctx) = check_expr_type_flow ctx e1 in
                                let (e2_type, e2_ctx) = check_expr_type_flow e1_ctx e2 in
                                if is_consistent (type_from_type_flow e1_type) Int && is_consistent (type_from_type_flow e2_type) Int then ([Int, None], e2_ctx) else raise (Failure "Binop error")
  | Expr.Elem (e, index)   ->   let (e_type, e_ctx)  = check_expr_type_flow ctx e in
                                let (index_type_flow, index_ctx) = check_expr_type_flow e_ctx index in
                                if not @@ is_consistent (type_from_type_flow e_type) (Union [Sexp; Array Any; String]) then 
                                                                                                  raise (Failure ( Printf.sprintf "Elem error. Left is [%s], but not Sexp, Array, String" (type_to_string (Union (List.map fst e_type)))))
                                else (
                                      if not @@ is_consistent (type_from_type_flow index_type_flow) Int then raise (Failure "Elem error. Right is not int") else
                                      let possible_elem_types = List.fold_left (fun ts et -> match et with
                                                                                                      Any -> Any::ts
                                                                                                      | Sexp -> Any::ts
                                                                                                      | Array t -> t ::ts
                                                                                                      | String -> Int::ts     
                                                                                                      | _ -> raise (Failure (Printf.sprintf "Bug. e_type can be only Any, Sexp, Array, String, but was %s" (type_to_string et)))                                                  
                                      ) [] (List.map fst e_type)
                                      in (List.map (fun t -> (t, None)) possible_elem_types, index_ctx)
                                )
                                (*Wrong? Any should be cast to actual type?*)
  | Expr.ElemRef (e, index) ->  let (e_type, e_ctx)  = check_expr_type_flow ctx e in
                                let (index_type_flow, index_ctx) = check_expr_type_flow e_ctx index in
                                if not @@ is_consistent (type_from_type_flow e_type) (Union [Sexp; Array Any; String]) then 
                                                                                                  raise (Failure ( Printf.sprintf "ElemRef error. Left is [%s], but not Sexp, Array, String" (type_to_string (Union (List.map fst e_type))  )))
                                else (
                                      if not @@ is_consistent (type_from_type_flow index_type_flow)  Int then raise (Failure "ElemRef error. Right is not int") else
                                      let possible_elem_types = List.fold_left (fun ts et -> match et with
                                      Any -> Any::ts
                                      | Sexp -> Any::ts
                                      | Array t -> t ::ts
                                      | String -> Int::ts      
                                      | _ -> raise (Failure (Printf.sprintf "Bug. e_type can be only Any, Sexp, Array, String, but was %s" (type_to_string et)))                                                  
) [] (List.map fst e_type)
in (List.map (fun t -> (t, None)) possible_elem_types, index_ctx)
                                )
  | Expr.Call (fun_expr, args) -> (*Printf.printf "\n\n%s" (TypeContext.to_string ctx);*) let (f_type, f_ctx) = check_expr_type_flow ctx fun_expr in
                                  let (args_t, new_ctx) =  List.fold_left (fun (args_t, ctx) arg -> 
                                                                                                  let (arg_t, ctx) = check_expr_type_flow ctx arg in
                                                                                                  (arg_t::args_t, ctx)
                                                                          ) ([], f_ctx) args  in
                                  let process_func f_type args =  match f_type with 
                                                                        Any -> Any (*Any   ~   Any -> Any*)
                                                                        | Callable (fun_args_t, fun_ret_t) -> if List.length fun_args_t <> List.length args then raise (Failure (Printf.sprintf "Argument size mismatch. Function requares %d, but %d was given" (List.length fun_args_t) (List.length args))) else ();
                                                                                                              List.iter (fun (actual_arg, expected_fun_arg) -> if not @@ is_consistent (type_from_type_flow actual_arg) expected_fun_arg then raise (Failure "arg type mismatch")) @@ List.combine args fun_args_t;
                                                                                                              fun_ret_t

                                                                        | _ -> raise (Failure "Invalid f")
                                  in ((match type_from_type_flow f_type with 
                                                  Union ftls -> List.fold_left (fun acc ft -> (process_func ft (*List.rev*) args_t, None) :: acc) [] ftls
                                                  | t -> [(process_func t (*List.rev*) args_t, None)])
                                      , new_ctx)

  | Expr.Assign (v, e) -> let (_, v_vtx) = check_expr_type_flow ctx v in
                          let (e_type, e_ctx) = check_expr_type_flow v_vtx e in
                          let refs = collect_refs v in
                          
                          let ctx = List.fold_left (fun ctx' ref -> TypeContext.set_type_flow_types ctx' ref e_type) e_ctx refs in
                          (e_type, ctx)
                          
                                                      
  | Expr.Seq (e1, e2) ->  let (_, e1_ctx) = check_expr_type_flow ctx e1 in
                          check_expr_type_flow e1_ctx e2
  | Expr.Skip -> ([], ctx)

  | Expr.If (e, thene, elsee) ->  let (_, e_inner_ctx) = check_expr_type_flow ctx e in
                                  let (then_type_flow, then_inner_ctx) = check_expr_type_flow e_inner_ctx thene in
                                  let (else_type_flow, else_inner_ctx) = check_expr_type_flow e_inner_ctx elsee in
                                  let merge_then_else_ctx = TypeContext.merge_ctxs then_inner_ctx else_inner_ctx in
                                  (List.concat [then_type_flow; else_type_flow], merge_then_else_ctx)

  | Expr.While (cond, body)      -> ([], check_cycle ctx (Expr.Seq(cond, body)))
  
  | Expr.DoWhile (body, cond)    ->  ([], check_cycle ctx (Expr.Seq(body, cond)) ) (*Union [], check_cycle ctx (Expr.Seq(e, cond)) *)

  | Expr.Case _ -> ([(Any, None)], ctx) (*TODO*)
  (*
  | Expr.Case (e, ls, _, _) ->    let (e_type_flow, e_ctx) = check_expr_type_flow ctx e in
                                  List.iter (fun t -> if List.fold_left (fun acc patt_t -> is_consistent_patt patt_t t || acc) false (List.map (fun (p, _) -> p) ls ) then () else raise (Failure (Printf.sprintf "No pattern for type %s" (type_to_string t)))  ) e_type_flow;
                                  let (tf, ctx )  = List.fold_left (fun (t_flow, ctx) (_, e) -> let (e_type_flow, e_ctx) = check_expr_type_flow ctx e in (List.concat [t_flow;e_type_flow], e_ctx)) ([], e_ctx) ls      
                                  in (Union tf, ctx) 
*)
  | Expr.Ignore e -> let (_, ctx) = check_expr_type_flow ctx e in ([(Any, None)], ctx)

  | Expr.Unit -> ([(Unit, None)], ctx)                                    

  | Expr.Scope (ds, e) ->   let inner_ctx = List.fold_left  (fun ctx (v, d) -> 
                                                                              match d with 
                                                                              (_, `Fun (_,_, t)) -> TypeContext.update_ctx ctx [(v, lamaTypeAnnotationTolamaType2 t)]
                                                                              | (_, `Variable (_, t)) -> TypeContext.update_ctx ctx [(v, lamaTypeAnnotationTolamaType2 t)]
                                                                              | (_, `VariantTypeDecl _) -> ctx
                                                            ) ctx ds in
                            let inner_ctx = List.fold_left (fun ctx (var, (_, vardecl)) -> 
                                                              match vardecl with
                                                                    `Fun (_, _, t) -> TypeContext.set_type_flow_types ctx var [(lamaTypeAnnotationTolamaType2 t, None)]
                                                                    | `Variable (Some e, _) -> let (type_flow, new_ctx) = check_expr_type_flow ctx e in 
                                                                                            TypeContext.set_type_flow_types new_ctx var type_flow
                                                                    | `Variable (None, _) -> TypeContext.set_type_flow_types ctx var TypeContext.empty_type_flow
                                                                    | `VariantTypeDecl _-> ctx (*TODO*)) inner_ctx ds   in
                            let (tflow, inner_ctx) = check_expr_type_flow inner_ctx e in
                            (tflow, TypeContext.update_outer_context ctx inner_ctx (List.map (fun (var, _) -> var) ds))
  | Expr.Tuple ls ->  let (tls, ctx) = List.fold_left (fun (tls, ctx) e -> let (etls, ctx) = check_expr_type_flow ctx e in ((Union (List.map fst etls))::tls, ctx) ) ([], ctx) ls
                      in ([(Tuple (List.map (fun (Union ts) -> Union (List.rev ts)) tls), None)], ctx)

  | Expr.DataConstr _ -> ([ (Any, None)], ctx)
  | _ -> raise (Failure "Not implemented1")

(* Should also work this:
let check_expr ctx expr = let _ = check_expr_type_flow ctx expr in let _ = check_annotations ctx expr in (); 
*)
let check_expr (ctx, tdctx) expr = let typeDefCtx = collect_variant_defs expr in
                          let ctx = (ctx, List.append tdctx typeDefCtx) in
                          let _ = check_annotations ctx expr in 
                          let _ = check_expr_type_flow ctx expr in 
                          ()