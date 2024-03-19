open GT
open Language

type lamaType = Sexp | Int | String | Array of lamaType | Any | Callable of (lamaType list) * lamaType | Unit | Union of lamaType list

let rec type_to_string t = match t with
                        | Sexp -> "Sexpr"
                        | Int -> "Int"
                        | String -> "String"
                        | Array elemT  -> "Array " ^ (type_to_string elemT)
                        | Any -> "Any"
                        | Callable (args, ret) -> Printf.sprintf "Callable ([%s], %s)" (String.concat "," (List.map type_to_string args)) (type_to_string ret)
                        | Unit  -> "Unit"
                        | Union ls -> Printf.sprintf "Union [%s]" (String.concat "," (List.map type_to_string ls))

let rec fix_union_helper (Union ls) = let fixed_inner_unions = List.map (fun t ->  match t with 
                                                        Union ls -> fix_union_helper (Union ls)
                                                        | t -> t) ls
                                in Union (List.fold_left (fun acc t -> 
                                                                  match t with 
                                                                        Union tls -> List.concat [acc;tls]
                                                                        | t -> t::acc     
                                  ) [] fixed_inner_unions)  

let rec fix_union (Union ls)  = let (Union fixed_ls) = fix_union_helper (Union ls) in if List.length fixed_ls = 1 then List.hd fixed_ls else Union fixed_ls

let fix_maybe_union t = match t with
                              Union ls -> fix_union t 
                              | _ -> t


(*bug. fix union can return not union*)
let rec is_consistent t1 t2 = match (t1, t2) with 
  | Any, _ -> true
  | _, Any -> true
  | Int, Int -> true
  | Int, Union ls -> let (Union ls) = fix_union (Union ls) in List.fold_left (||) false (List.map (is_consistent Int) ls)
  | Int, _ -> false

  | String, String -> true
  | String, Union ls -> let (Union ls) = fix_union (Union ls) in List.fold_left (||) false (List.map (is_consistent String) ls)
  | String, _ -> false

  | Array e1t, Array e2t -> is_consistent e1t e2t
  | Array e1t, Union ls -> let (Union ls) = fix_union (Union ls) in List.fold_left (||) false (List.map (is_consistent (Array e1t)) ls)
  | Array _ , _ -> false

  (*Callable may be wrong*)
  | Callable (atls1, rt1), Callable (atls2, rt2) -> is_consistent rt1 rt2 && ( (List.length atls1) = (List.length atls2) && List.fold_left (fun acc (t1, t2) -> acc && (is_consistent t1 t2)) true (List.combine atls1 atls2) )
  | Callable (atls1, rt1), Union ls -> let (Union ls) = fix_union (Union ls) in List.fold_left (||) false (List.map (is_consistent (Callable (atls1, rt1))) ls)
  | Callable (_, _), _ -> false
  
  | Unit, Unit -> true
  | Unit, Union ls -> let (Union ls) = fix_union (Union ls) in List.fold_left (||) false (List.map (is_consistent Unit) ls)
  | Unit, _ -> false

  | Union l, Union r-> let (Union l, Union r) = (fix_union (Union l), fix_union (Union r)) in List.fold_left (fun acc t -> acc || is_consistent t (Union r)) false l
  | Union ls, t -> (*transform to case Union, Union*) is_consistent (Union ls) (Union [t;t])

(*equal = describe the same sets of values*)
let are_types_equal t1 t2 =   Printf.printf "Outer f\n"; flush stdout; 
                              let rec are_types_equal_helper t1' t2' =  (Printf.printf "Checking equality of\n %s \nAND\n %s\n" (type_to_string t1') (type_to_string t2'); flush stdout; match (t1', t2') with 
                                                                        | (Any, Any) -> true
                                                                        | (Any, Union ls) -> List.mem Any ls (*|| List.mem ls Int && Array Any && String && Unit ... *)
                                                                        | (Any, _) -> false

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

                                                                        | Union l, Union r -> if List.mem Any l || List.mem Any r then let (lFixed, rFixed) = ((if List.mem Any l then Any else Union l), if List.mem Any r then Any else Union r) in
                                                                                              are_types_equal_helper lFixed rFixed
                                                                                              else (List.fold_left (fun acc tl -> acc && List.fold_left (fun acc tr -> acc || are_types_equal_helper tl tr) false r) true l) && (List.fold_left (fun acc tr -> acc && List.fold_left (fun acc tl -> acc || are_types_equal_helper tr tl) false l) true r)
                                                                        | Union ls, t -> (*transform to case t, Un(List.fold_left (fun acc tr -> acc || List.fold_left (fun acc tl -> acc || are_types_equal_helper tl tr) acc l) false r)ion*) are_types_equal_helper t (Union ls)
                                                                        )
                              in are_types_equal_helper (fix_maybe_union t1) (fix_maybe_union t2)                                           


(*
let rec is_consistent t1 t2 = match (t1, t2) with 
  | Any, _ -> true
  | _, Any -> true
  | Union l, Union r -> List.fold_left (fun acc t -> acc && List.mem t r) true l
  | t, Union r -> List.fold_left (||) false (List.map (is_consistent t) r)
  | Callable (atls1, rt1), Callable (atls2, rt2) -> is_consistent rt1 rt2 && ( (List.length atls1)fix_union = (List.length atls2) && List.fold_left (fun acc (t1, t2) -> acc && (is_consistent t1 t2)) true (List.combine atls1 atls2) )
  | t1, t2 -> t1 = t2
*)


(*
let is_consistent_type_flows tf1 tf2 = List.fold_left (fun acc t1 -> List.fold_left (fun acc t2 -> acc && is_consistent t1 t2) acc tf2 ) true tf1
*)

let rec is_consistent_patt patt t = match patt with 
                                      Pattern.Wildcard -> true
                                      | Pattern.Sexp _ -> is_consistent Sexp t
                                      | Pattern.Array _ -> is_consistent (Array Any) t
                                      | Pattern.Named (_, p) -> is_consistent_patt p t
                                      | Pattern.Const _ -> is_consistent Int t 
                                      | Pattern.String _ -> is_consistent String t 
                                      | Pattern.Boxed -> raise (Failure "not implemented")
                                      | Pattern.UnBoxed -> raise (Failure "not implemented")
                                      | Pattern.StringTag -> is_consistent String t 
                                      | Pattern.SexpTag -> is_consistent Sexp t 
                                      | Pattern.ArrayTag -> is_consistent (Array Any) t 
                                      | Pattern.ClosureTag -> raise (Failure "not implemented")


let merge_types t1 t2 = fix_union (Union [t1;t2])

module TypeContext : sig
  type t = ((string * (lamaType * lamaType)) list)
  val add_type_to_type_flow : t -> string -> lamaType -> t
  val update_ctx : t -> (string * lamaType) list -> t
  val update_outer_context : t -> t -> string list -> t
  val empty_ctx : t
  val get_var_type_flow : t -> string -> lamaType
end = struct
  type t = ((string * (lamaType * lamaType)) list)
  let empty_type_flow_context = Union []
  let empty_ctx = []
  let rec add_type_to_type_flow ctx var ts = match ctx with
                                                          [] -> raise (Failure (Printf.sprintf "Undefined variable %s" var))
                                                        | (v, (avctx, tfctx)):: ctx -> if var = v then  (
                                                          v, 
                                                          (
                                                            avctx, fix_union (Union [ts;tfctx])
                                                          )
                                                        ) ::ctx else (v, (avctx,tfctx)) :: add_type_to_type_flow  ctx var ts
  (*Updates context with variable names and type annotations. If variable exist in old context, annotation and type flow discarded and replaced with new annotation and empty type flow*)
  let update_ctx ctx vars = List.fold_left (fun ctx' (var, anType) -> (var, (anType, empty_type_flow_context))::ctx') (List.filter (fun (vname, _) -> not (List.mem vname (List.map fst vars))) ctx) vars

  (*Updates outer ctx with information from inner cxt, excepl local variables of inner ctx*)
  let update_outer_context outer_ctx inner_ctx inner_vars = List.fold_left (fun o (var, (_, type_flow)) -> if List.mem var inner_vars then o else add_type_to_type_flow o var type_flow) outer_ctx inner_ctx

  let rec get_var_type_flow ctx var = match ctx with 
                                            [] -> raise (Failure (Printf.sprintf "Undefined variable %s" var))
                                            | (v, (_, tflow))::ctx' -> if var = v then tflow else get_var_type_flow ctx' var
end


(*returns list of possible types of expression + context updated with new type flow content. *)
let rec check_expr ctx e =
  let rec check_cycle cycle_ctx cycle = (
    let (_, new_ctx) = check_expr cycle_ctx cycle
    in  let changed = List.fold_left (fun acc (ctf, nctf) -> Printf.printf "Wtf: %s\n"(type_to_string ctf); flush stdout;  acc || not (are_types_equal ctf nctf)) false ( let get_flow = fun (var_name, (type_an, type_flow)) -> (*Printf.printf "%s : (%s, %s)\n" var_name (type_to_string type_an) (type_to_string type_flow) ; *)type_flow in List.combine (List.map get_flow cycle_ctx) (List.map get_flow new_ctx))  (*TODO: add assert that ctx's has same structure, i.e fmap fst ctx = fmap fst new_ctx*)
        in if changed then (Printf.printf "Checking..." ; flush stdout; check_cycle new_ctx cycle ) else (Printf.printf "Not checking..." ; flush stdout;  new_ctx)
  )
  in
  match e with
  | Expr.Const _       -> (Int, ctx)
  | Expr.Array ls      -> if List.length ls = 0 then (Array Any, ctx) else List.fold_left (fun (t, ctx) e -> let (e_t, ctx) = check_expr ctx e in (fix_union (Union [e_t; t]), ctx)) (Union [], ctx) ls
  | Expr.String _      -> (String, ctx)
  | Expr.Sexp (_, ls)  -> (Sexp, List.fold_left (fun ctx e -> let (_, inner_ctx) = check_expr ctx e in TypeContext.update_outer_context ctx inner_ctx []) ctx ls)
  | Expr.Var v         -> (TypeContext.get_var_type_flow ctx v, ctx)
  | Expr.Ref v         -> (TypeContext.get_var_type_flow ctx v, ctx) (*raise (Failure "Error. Never typecheck ref without assign") *) (*TypeContext.get_var_type_flow ctx v, ctx*)
  | Expr.Binop (_, e1, e2) ->  let (e1_type, e1_ctx) = check_expr ctx e1 in
                                let (e2_type, e2_ctx) = check_expr e1_ctx e2 in
                                if is_consistent e1_type Int && is_consistent e2_type Int then (Int, e2_ctx) else raise (Failure "Binop error")
  | Expr.Elem (e, index)   ->   let (e_type, e_ctx)  = check_expr ctx e in
                                let (index_type_flow, index_ctx) = check_expr e_ctx index in
                                if not @@ is_consistent e_type (Union [Sexp; Array Any; String]) then 
                                                                                                  raise (Failure ( Printf.sprintf "Elem error. Left is [%s], but not Sexp, Array, String" (type_to_string e_type)))
                                else (
                                      if not @@ is_consistent index_type_flow  Int then raise (Failure "Elem error. Right is not int") else
                                      let elem_type = match e_type with 
                                                      Any -> Any
                                                      | Sexp -> Any
                                                      | Array t -> t 
                                                      | String -> Int
                                      in (elem_type, index_ctx)
                                )
                                (*Wrong? Any should be cast to actual type?*)
  | Expr.ElemRef (e, index) ->  let (e_type, e_ctx)  = check_expr ctx e in
                                let (index_type_flow, index_ctx) = check_expr e_ctx index in
                                if not @@ is_consistent e_type (Union [Sexp; Array Any; String]) then 
                                                                                                  raise (Failure ( Printf.sprintf "ElemRef error. Left is [%s], but not Sexp, Array, String" (type_to_string e_type)))
                                else (
                                      if not @@ is_consistent index_type_flow  Int then raise (Failure "ElemRef error. Right is not int") else
                                      let elem_type = match e_type with 
                                                      Any -> Any
                                                      | Sexp -> Any
                                                      | Array t -> t 
                                                      | String -> Int
                                      in (elem_type, index_ctx)
                                )
  | Expr.Call (fun_expr, args) -> let (f_type, f_ctx) = check_expr ctx fun_expr in
                                  let (args_t, new_ctx) =  List.fold_left (fun (args_t, ctx) arg -> 
                                                                                                  let (arg_t, ctx) = check_expr ctx arg in
                                                                                                  (arg_t::args_t, ctx)
                                                                          ) ([], f_ctx) args  in
                                  let process_func f_type args =  match f_type with 
                                                                        Any -> Any (*Any   ~   Any -> Any*)
                                                                        | Callable (fun_args_t, fun_ret_t) -> if List.length fun_args_t <> List.length args then raise (Failure "Argument size mismatch") else ();
                                                                                                              List.iter (fun (actual_arg, expected_fun_arg) -> if not @@ is_consistent actual_arg expected_fun_arg then raise (Failure "arg type mismatch")) @@ List.combine args fun_args_t;
                                                                                                              fun_ret_t

                                                                        | _ -> raise (Failure "Invalid f")
                                  in ((match f_type with 
                                                  Union ftls -> Printf.printf "a f_type %s\n" (type_to_string f_type); fix_union (List.fold_left (fun acc ft -> Union [acc; process_func ft args_t]) (Union []) ftls)
                                                  | t -> Printf.printf "b f_type %s\n" (type_to_string f_type); process_func t args_t)
                                      , new_ctx)

(*
                                  let (tf, ctx) = (List.fold_left (fun t_flow fun_t -> 
                                                                    match fun_t with
                                                                    Any -> Any::t_flow
                                                                    | Callable (fun_args_t, fun_ret_t) -> if List.length fun_args_t <> List.length args_t then raise (Failure "Argument size mismatch") else ();
                                                                    List.iter (fun (arg_tf, fun_arg) -> if not @@ is_consistent_type_flows arg_tf [fun_arg] then raise (Failure "arg type mismatch")) @@ List.combine (List.rev args_t) fun_args_t;
                                                                    fun_ret_t :: t_flow
                                                                    ) [] f_type_flow, new_ctx)
                                  in (Union tf, ctx)

                                  *)
  (*
  | Expr.Call (fun_expr, args) -> let (f_type_flow, f_ctx) = check_expr ctx fun_expr in
                                  if not @@ is_consistent_type_flows f_type_flow  [Callable ([Any], Any)] then raise (Failure "fun_expr is not callable") 
                                  else  let (args_t, new_ctx) =  List.fold_left (fun (args_t, ctx) arg -> 
                                                                                                        let (arg_t, ctx) = check_expr ctx arg in
                                                                                                        (arg_t::args_t, ctx)
                                                                ) ([], ctx) args  in
                                        let (Callable (fun_args_t, fun_ret_t)) = f_type_flow in
                                        if List.length fun_args_t <> List.length arg_t then raise (Failure "Argument size mismatch") else ();
                                        List.iter (fun (arg_tf, fun_arg) -> if not @@ is_consistent_type_flows arg_tf [fun_arg] then raise (Failure "arg type mismatch")) List.combine (List.rev args_t) fun_args_t;
                                        ([fun_ret_t], new_ctx)
  *)


  | Expr.Assign (v, e) -> let rec collect_refs e = match e with (*TODO: more precise analisys*)
                                                      Expr.Ref v -> [v]
                                                      | Expr.Seq ( _ , s2) -> collect_refs s2
                                                      | Expr.If (_, s1, s2) -> (collect_refs s1) @ (collect_refs s2)
                                                      | _ -> []
                          in (*TODO: Fix left side. Maybe add lvalue/rvalue parameter*)
                          let (_, v_vtx) = check_expr ctx v in
                          let (e_type, e_ctx) = check_expr v_vtx e in
                          let refs = collect_refs v in
                          
                          let ctx = List.fold_left (fun ctx' ref -> TypeContext.add_type_to_type_flow ctx' ref e_type) e_ctx refs in
                          (e_type, ctx)
                          
                                                      
  | Expr.Seq (e1, e2) ->  let (e1_type_flow, e1_ctx) = check_expr ctx e1 in
                          let (e2_type_flow, e2_ctx) = check_expr e1_ctx e2 in
                          (e2_type_flow, e2_ctx)
  | Expr.Skip -> (Union [], ctx)

  | Expr.If (e, thene, elsee) ->  let (_, e_inner_ctx) = check_expr ctx e in
                                  let (then_type_flow, then_inner_ctx) = check_expr e_inner_ctx thene in
                                  let (else_type_flow, else_inner_ctx) = check_expr e_inner_ctx elsee in
                                  let merge_then_else_ctx = TypeContext.update_outer_context (TypeContext.update_outer_context e_inner_ctx then_inner_ctx []) else_inner_ctx [] in
                                  (Union [then_type_flow; else_type_flow], merge_then_else_ctx)

  | Expr.While (cond, body)      -> (Union [], check_cycle ctx body)
  
  | Expr.DoWhile (body, cond)    ->  (Union [], check_cycle ctx body) (*Union [], check_cycle ctx (Expr.Seq(e, cond))*)
(*
  | Expr.Case (e, ls, _, _) ->    let (e_type_flow, e_ctx) = check_expr ctx e in
                                  List.iter (fun t -> if List.fold_left (fun acc patt_t -> is_consistent_patt patt_t t || acc) false (List.map (fun (p, _) -> p) ls ) then () else raise (Failure (Printf.sprintf "No pattern for type %s" (type_to_string t)))  ) e_type_flow;
                                  let (tf, ctx )  = List.fold_left (fun (t_flow, ctx) (_, e) -> let (e_type_flow, e_ctx) = check_expr ctx e in (List.concat [t_flow;e_type_flow], e_ctx)) ([], e_ctx) ls      
                                  in (Union tf, ctx) 
*)
  | Expr.Ignore e -> let (_, ctx) = check_expr ctx e in (Any, ctx)

  | Expr.Unit -> (Unit, ctx)                                    

  | Expr.Scope (ds, e) ->   let inner_ctx = TypeContext.update_ctx ctx (List.map (fun (var, _) -> (var, Any)) ds) in
                            let inner_ctx = List.fold_left (fun ctx (var, (_, vardecl)) -> 
                                                              match vardecl with
                                                                    `Fun (_) -> TypeContext.add_type_to_type_flow ctx var Any
                                                                    | `Variable (Some e) -> let (type_flow, new_ctx) = check_expr ctx e in 
                                                                                            TypeContext.add_type_to_type_flow new_ctx var type_flow
                                                                    | `Variable None -> ctx) inner_ctx ds   in
                            let (tflow, inner_ctx) = check_expr inner_ctx e in
                            (tflow, TypeContext.update_outer_context ctx inner_ctx (List.map (fun (var, _) -> var) ds))
  
  | _ -> raise (Failure "Not implemented")
                                           