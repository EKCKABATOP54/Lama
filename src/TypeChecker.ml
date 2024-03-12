open GT
open Language

type lamaType = Sexp | Int | String | Array | Any | Callable of (lamaType list) * lamaType | Unit

let type_to_string t = match t with
                        Sexp -> "Sexpr"
                        | Int -> "Int"
                        | String -> "String"
                        | Array  -> "Array"
                        | Any -> "Any"
                        | Callable _ -> "Callable"
                        | Unit  -> "Unit"

type type_flow_t = lamaType list

let rec is_consistent t1 t2 = match (t1, t2) with 
  | Any, _ -> true
  | _, Any -> true
  | Callable (atls1, rt1), Callable (atls2, rt2) -> is_consistent rt1 rt2 && ( (List.length atls1) = (List.length atls2) && List.fold_left (fun acc (t1, t2) -> acc && (is_consistent t1 t2)) true (List.combine atls1 atls2) )
  | t1, t2 -> t1 = t2

let is_consistent_type_flows tf1 tf2 = List.fold_left (fun acc t1 -> List.fold_left (fun acc t2 -> acc && is_consistent t1 t2) acc tf2 ) true tf1

module TypeContext : sig
  type t
  val add_types_to_type_flow : t -> string -> lamaType list -> t
  (*val empty_type_flow_context : type_flow_t *)
  val update_ctx : t -> (string * lamaType) list -> t
  val update_outer_context : t -> t -> string list -> t
  val empty_ctx : t
  val get_var_type_flow : t -> string -> type_flow_t
end = struct
  type t = ((string * (lamaType * type_flow_t)) list)
  let empty_type_flow_context = []
  let empty_ctx = []
  let rec add_types_to_type_flow ctx var ts = match ctx with
                                                          [] -> raise (Failure "Undefined variable")
                                                        | (v, (avctx, tfctx)):: ctx -> if var = v then  (
                                                          v, 
                                                          (
                                                            avctx,
                                                            (List.fold_left (fun tfctx nt -> if List.mem nt tfctx then tfctx else nt::tfctx) tfctx ts)
                                                          )
                                                        ) ::ctx else (v, (avctx,tfctx)) :: add_types_to_type_flow  ctx var ts
  (*Updates context with variable names and type annotations. If variable exist in old context, annotation and type flow discarded and replaced with new annotation and empty type flow*)
  let update_ctx ctx vars = List.fold_left (fun ctx (var, anType) -> (var, (anType, empty_type_flow_context))::ctx) (List.filter (fun (vname, _) -> not (List.mem vname (List.map fst vars))) ctx) vars

  (*Updates outer ctx with information from inner cxt, excepl local variables of inner ctx*)
  let update_outer_context outer_ctx inner_ctx inner_vars = List.fold_left (fun o (var, (_, type_flow)) -> if List.mem var inner_vars then o else add_types_to_type_flow o var type_flow) outer_ctx inner_ctx

  let rec get_var_type_flow ctx var = match ctx with 
                                            [] -> raise (Failure (Printf.sprintf "Undefined variable %s" var))
                                            | (v, (_, tflow))::ctx -> if var = v then tflow else get_var_type_flow ctx var
end

(*returns list of possible types of expression + context updated with new type flow content. *)
let rec check_expr ctx = function
  | Expr.Const _       -> ([Int], ctx)
  | Expr.Array ls      -> ([Array], List.fold_left (fun ctx e -> let (_, inner_ctx) = check_expr ctx e in TypeContext.update_outer_context ctx inner_ctx []) ctx ls)
  | Expr.String _      -> ([String], ctx)
  | Expr.Sexp (_, ls)  -> ([Sexp], List.fold_left (fun ctx e -> let (_, inner_ctx) = check_expr ctx e in TypeContext.update_outer_context ctx inner_ctx []) ctx ls)
  | Expr.Var v         -> (TypeContext.get_var_type_flow ctx v, ctx)
  | Expr.Ref v         -> (TypeContext.get_var_type_flow ctx v, ctx)
  | Expr.Binop (op, e1, e2) ->  let (e1_type_flow, e1_ctx) = check_expr ctx e1 in
                                let (e2_type_flow, e2_ctx) = check_expr e1_ctx e2 in
                                if is_consistent_type_flows e1_type_flow [Int] && is_consistent_type_flows e2_type_flow [Int] then ([Int], e2_ctx) else raise (Failure "Binop error")
  | Expr.Elem (e, index)   ->   let (e_type_flow, e_ctx)  = check_expr ctx e in
                                let (index_type_flow, index_ctx) = check_expr e_ctx index in
                                if not @@ is_consistent_type_flows e_type_flow [Sexp; Array; String] then raise (Failure ( Printf.sprintf "Elem error. Left is [%s], but not Sexp, Array, String" (String.concat "; " ( List.map type_to_string e_type_flow))))
                                else (
                                      if not @@ is_consistent_type_flows index_type_flow  [Int] then raise (Failure "Elem error. Right is not int") else
                                      let elem_type_flow = [] in
                                      let elem_type_flow = List.concat [elem_type_flow; if is_consistent_type_flows e_type_flow [Sexp] then [Any] else []] in
                                      let elem_type_flow = List.concat [elem_type_flow; if is_consistent_type_flows e_type_flow [String] then [Int] else []] in
                                      let elem_type_flow = List.concat [elem_type_flow; if is_consistent_type_flows e_type_flow [Array] then [Any] else []] in
                                      (elem_type_flow, index_ctx)
                                )
  | Expr.ElemRef (e, index) ->  let (e_type_flow, e_ctx)  = check_expr ctx e in
                                let (index_type_flow, index_ctx) = check_expr e_ctx index in
                                if not @@ is_consistent_type_flows e_type_flow [Sexp; Array; String] then raise (Failure ( Printf.sprintf "ElemRef error. Left is [%s], but not Sexp, Array, String" (String.concat "; " ( List.map type_to_string e_type_flow))))
                                else (
                                if not @@ is_consistent_type_flows index_type_flow [Int] then raise (Failure "ElemRef error. Right is not int") else
                                let elem_type_flow = [] in
                                let elem_type_flow = List.concat [elem_type_flow; if is_consistent_type_flows e_type_flow [Sexp] then [Any] else []] in
                                let elem_type_flow = List.concat [elem_type_flow; if is_consistent_type_flows e_type_flow [String] then [Int] else []] in
                                let elem_type_flow = List.concat [elem_type_flow; if is_consistent_type_flows e_type_flow [Array] then [Any] else []] in
                                (elem_type_flow, index_ctx)
                                )
  | Expr.Call (fun_expr, args) -> let (f_type_flow, f_ctx) = check_expr ctx fun_expr in
                                  let (args_t, new_ctx) =  List.fold_left (fun (args_t, ctx) arg -> 
                                                                                                  let (arg_t, ctx) = check_expr ctx arg in
                                                                                                  (arg_t::args_t, ctx)
                                                                          ) ([], ctx) args  in
                                  (List.fold_left (fun t_flow fun_t -> 
                                                                    match fun_t with
                                                                    Any -> Any::t_flow
                                                                    | Callable (fun_args_t, fun_ret_t) -> if List.length fun_args_t <> List.length args_t then raise (Failure "Argument size mismatch") else ();
                                                                    List.iter (fun (arg_tf, fun_arg) -> if not @@ is_consistent_type_flows arg_tf [fun_arg] then raise (Failure "arg type mismatch")) @@ List.combine (List.rev args_t) fun_args_t;
                                                                    fun_ret_t :: t_flow
                                                                    ) [] f_type_flow, new_ctx)
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

  | Expr.Assign (v, e) -> let (v_type_flow, v_ctx) = check_expr ctx v in
                          let (e_type_flow, e_ctx) = check_expr v_ctx e in
                          if is_consistent_type_flows v_type_flow e_type_flow then (e_type_flow, v_ctx) else raise (Failure "er")
  | Expr.Seq (e1, e2) ->  let (e1_type_flow, e1_ctx) = check_expr ctx e1 in
                          let (e2_type_flow, e2_ctx) = check_expr e1_ctx e2 in
                          (e2_type_flow, e2_ctx)
  | Expr.Skip -> ([], ctx)

  | Expr.If (e, thene, elsee) ->  let (_, e_inner_ctx) = check_expr ctx e in
                                  let (then_type_flow, then_inner_ctx) = check_expr e_inner_ctx thene in
                                  let (else_type_flow, else_inner_ctx) = check_expr e_inner_ctx elsee in
                                  let merge_then_else_ctx = TypeContext.update_outer_context (TypeContext.update_outer_context e_inner_ctx then_inner_ctx []) else_inner_ctx [] in
                                  (List.concat [then_type_flow; else_type_flow], merge_then_else_ctx)

  | Expr.While (cond, e)      ->  let (_, ctx) = check_expr ctx cond in
                                  let rec update_ctx old_ctx e = let (_, new_ctx) = check_expr old_ctx e in if new_ctx <> old_ctx then update_ctx new_ctx e else new_ctx in
                                  ([], update_ctx ctx e)
  
  | Expr.DoWhile (e, cond)    ->  let (_, ctx)  = check_expr ctx cond in
                                  let rec update_ctx old_ctx e = let (_, new_ctx) = check_expr old_ctx e in if new_ctx <> old_ctx then update_ctx new_ctx e else new_ctx in
                                  ([], update_ctx ctx e)

  | Expr.Case _ -> raise (Failure "Not implemented")

  | Expr.Ignore e -> let (_, ctx) = check_expr ctx e in ([Any], ctx)

  | Expr.Unit -> ([Unit], ctx)                                    

  | Expr.Scope (ds, e) ->   let inner_ctx = TypeContext.update_ctx ctx (List.map (fun (var, _) -> (var, Any)) ds) in
                            let inner_ctx = List.fold_left (fun ctx (var, (_, vardecl)) -> 
                                                              match vardecl with
                                                                    `Fun (_) -> TypeContext.add_types_to_type_flow ctx var [Any]
                                                                    | `Variable (Some e) -> let (type_flow, new_ctx) = check_expr ctx e in 
                                                                                            TypeContext.add_types_to_type_flow new_ctx var type_flow
                                                                    | `Variable None -> ctx) inner_ctx ds   in
                            let (tflow, inner_ctx) = check_expr inner_ctx e in
                            (tflow, TypeContext.update_outer_context ctx inner_ctx (List.map (fun (var, _) -> var) ds))
  
  | _ -> raise (Failure "Not implemented")
                                           