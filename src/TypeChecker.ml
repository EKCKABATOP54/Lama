open GT
open Language

let rec type_to_string t = match t with
                        | Sexp -> "Sexpr"
                        | Int -> "Int"
                        | String -> "String"
                        | Array elemT  -> "Array " ^ (type_to_string elemT)
                        | Any -> "Any"
                        | Callable (args, ret) -> Printf.sprintf "Callable ([%s], %s)" (String.concat "," (List.map type_to_string args)) (type_to_string ret)
                        | Unit  -> "Unit"
                        | Union ls -> Printf.sprintf "Union [%s]" (String.concat "," (List.map type_to_string ls))


(*Returns Union in normal form*)   
(*TODO: return Any if t is Union (Int, String, Array Any ...)*)                     
let rec fix_union t =  let rec flattern_type t = match t with 
                                                              | Array et -> Array (flattern_type et)
                                                              | Callable (args, ret) -> Callable (List.map flattern_type args, flattern_type ret)
                                                              | Union ts -> let rec flatterned_types = List.map flattern_type (List.rev ts) in
                                                                            let fixed = List.fold_left (fun ls t -> match t with Union ts -> List.concat [ls;ts] | _ -> t::ls) [] flatterned_types
                                                                            in Union fixed
                                                              | _ -> t
                                in   
                                let rec remove_duplicates lst =
                                  match lst with
                                  | [] -> []
                                  | hd :: tl ->
                                    hd :: (remove_duplicates (List.filter (fun x -> x <> hd) tl))
                                in  let t = 
                                          match flattern_type t with 
                                          | Union ls -> Union (remove_duplicates ls)
                                          | t -> t
                                    in match t with Union ls -> if List.length ls = 1 then List.hd ls else Union ls | _ -> t

(*Removes loc info. If returns Union, then Union in normal form, i.e Union is flat and dont contains duplicates*)
let type_from_type_flow tf = fix_union (Union (List.map fst tf))



(*Accept only normal unions*)
let rec is_consistent_helper t1 t2 = (*Printf.printf "ABOBA\nt1:%s\nt2:%s\nt1 fixed:%s\nt2 fixed:%s\n" (type_to_string t1) (type_to_string t2) (type_to_string (fix_union t1)) (type_to_string (fix_union t2)) ;*) assert ( (t1 = fix_union t1) && (t2 = fix_union t2)) ; match (t1, t2) with 
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

  | Union [],_ -> false (*true*) (*OR failure or false?*)
  | Union l, Union r-> List.fold_left (fun acc t -> acc && is_consistent t (Union r)) true l
  | Union ls, t -> false

and is_consistent t1 t2 = is_consistent_helper (fix_union t1) (fix_union t2)  

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
                              in are_types_equal_helper (fix_union t1) (fix_union t2)                                           

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


module TypeContext : sig
  type type_flow_t = (lamaType * Loc.t option) list
  type t = ((string * (lamaType * type_flow_t)) list) (* variable * (type annotation * (lamaType * typeLoc) list) *)
  val add_type_to_type_flow : t -> string -> (lamaType * Loc.t option) -> t
  val add_types_to_type_flow : t -> string -> type_flow_t -> t
  val update_ctx : t -> (string * lamaType) list -> t
  val update_outer_context : t -> t -> string list -> t
  val empty_ctx : t
  val get_var_type_flow : t -> string -> type_flow_t
  val get_var_type : t -> string -> lamaType
  val to_string : t -> string
end = struct
  type type_flow_t = (lamaType * Loc.t option) list
  type t = ((string * (lamaType * type_flow_t)) list)
  let empty_type_flow_context = []
  let empty_ctx = []
  (*TODO: check that type is compatible with annotation*)
  let rec add_type_to_type_flow ctx var (new_type, new_type_loc) = match ctx with
                                                          [] -> raise (Failure (Printf.sprintf "Undefined variable %s" var))
                                                        | (v, (va, tf)):: ctx -> if var = v then  (
                                                          v, 
                                                          ( va, if List.mem (new_type, new_type_loc) tf then tf else (new_type, new_type_loc)::tf
                                                          )
                                                        ) ::ctx else (v, (va, tf)):: add_type_to_type_flow ctx var (new_type, new_type_loc)
  let rec add_types_to_type_flow ctx var ts = List.fold_left (fun ctx t -> add_type_to_type_flow ctx var t) ctx ts
  
                                                        (*Updates context with variable names and type annotations. If variable exist in old context, annotation and type flow discarded and replaced with new annotation and empty type flow*)
  let update_ctx ctx vars = List.fold_left (fun ctx' (var, anType) -> (var, (anType, empty_type_flow_context))::ctx') (List.filter (fun (vname, _) -> not (List.mem vname (List.map fst vars))) ctx) vars

  (*Updates outer ctx with information from inner cxt, excepl local variables of inner ctx*)
  let update_outer_context outer_ctx inner_ctx inner_locals = List.fold_left (fun o (var, (_, type_flow)) -> if List.mem var inner_locals then o else add_types_to_type_flow o var type_flow) outer_ctx inner_ctx

  let rec get_var_type_flow ctx var = match ctx with 
                                            [] -> raise (Failure (Printf.sprintf "Undefined variable %s" var))
                                            | (v, (_, tflow))::ctx' -> if var = v then tflow else get_var_type_flow ctx' var

  
  let rec get_var_type ctx var = match ctx with 
                                        [] -> raise (Failure (Printf.sprintf "Undefined variable %s" var))
                                        | (v, (vt, _ )) :: ctx' -> if var = v then vt else get_var_type ctx' var
  let to_string ctx = String.concat "\n" (List.map (fun (var, (vt, vtf)) -> Printf.sprintf "(%s, (%s, %s))" var (type_to_string vt) (String.concat "," (List.map (fun (t, l) -> Printf.sprintf "(%s, ?)" (type_to_string t)) vtf)) ) ctx)
end

let rec collect_refs e = match e with (*TODO: more precise analisys*)
                                Expr.Ref v -> [v]
                                | Expr.Seq ( _ , s2) -> collect_refs s2
                                | Expr.If (_, s1, s2) -> (collect_refs s1) @ (collect_refs s2)
                                | _ -> []


(*only checks annotations. returns type of expresion*)
let rec check_annotations (ctx : TypeContext.t ) (e : Expr.t ) : lamaType =
  match e with 
  | Expr.Const (_, _) -> Int
  | Expr.Array _ -> Array Any (*TODO ARRAY*)
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
                                      in elem_type
                                )
  | Expr.Assign (v, e) -> let v_type = check_annotations ctx v in
                          let e_type = check_annotations ctx e in
                          let refs = collect_refs v in
                          List.iter (fun ref -> if not (is_consistent ref e_type) then (raise (Failure "assign type error"))) (List.map (fun v -> TypeContext.get_var_type ctx v) refs); e_type
  | Expr.Seq (e1, e2) -> ignore (check_annotations ctx e1); check_annotations ctx e2
  | Expr.Skip -> Unit
  | Expr.If (e, thene, elsee) ->  ignore (check_annotations ctx e); 
                                  let then_type = check_annotations ctx thene in
                                  let else_type = check_annotations ctx elsee in
                                  Union [then_type; else_type] (*Or check that then_t = else_t? Or guess what type is expected and compare with it*)
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
                                                      
                                                      (_, `Variable (init, v_type)) ->  (match init with 
                                                                                        Some e -> let init_t = check_annotations ctx e
                                                                                                  in if is_consistent init_t v_type then () (*Ok*) else raise (Failure "ff")
                                                                                        | None -> ());
                                                                                        TypeContext.update_ctx ctx [(vname, v_type)]
                                                      | (_, `Fun (args, _, fun_t) ) -> TypeContext.update_ctx ctx [(vname, fun_t)]
                                                    ) ctx ds
                          in
                          List.iter (fun (fname, d) -> match d with 
                          (_, `Variable _) -> ()
                          | (_, `Fun (args, body , Callable (args_t, ret_t)) ) ->  
                                                                if List.length args <> List.length args_t then raise (Failure "Incorrect function type. Argument lenght mismatch");
                                                                let ctx = TypeContext.update_ctx ctx (List.combine args args_t)
                                                                in let actual_ret_type = check_annotations ctx body 
                                                                in if not @@ is_consistent actual_ret_type ret_t then raise (Failure (Printf.sprintf "Actual return type %s is not consistent with declared %s" (type_to_string actual_ret_type) (type_to_string ret_t)))
                          
                          | (_, `Fun (args, body, Any)) ->  let ctx = TypeContext.update_ctx ctx (List.map (fun x -> (x, Any)) args)
                                                            in let _ = check_annotations ctx body in ()
                          | (_, `Fun _) -> raise (Failure "Incorrect function type")
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
  | _ -> raise (Failure "Not implemented2")     



(*returns list of possible types of expression + context updated with new type flow content. *)
let rec check_expr_type_flow (ctx : TypeContext.t ) (e : Expr.t ) : (TypeContext.type_flow_t * TypeContext.t) =
  let rec check_cycle cycle_ctx cycle = (
    let (_, new_ctx) = check_expr_type_flow cycle_ctx cycle
    in  let changed = (cycle_ctx <> TypeContext.update_outer_context cycle_ctx ctx []) (*or even cycle_ctx <> new_ctx*)
        in if changed then check_cycle new_ctx cycle else new_ctx
  )
  in
  match e with
  | Expr.Const (_, l)       -> ([(Int, Some l)], ctx)
  | Expr.Array ls      -> ([(Array Any, None)], ctx)
  (*TODO ARRAY*)
  (*
  | Expr.Array ls      -> if List.length ls = 0 then ([Array Any], ctx) else List.fold_left (fun (t, ctx) e -> let (e_t, ctx) = check_expr_type_flow ctx e in (fix_union (Union [e_t; t]), ctx)) (Union [], ctx) ls
  *)
  | Expr.String _      -> ([(String, None)], ctx)
  | Expr.Sexp (_, ls)  -> ([(Sexp, None)], List.fold_left (fun ctx e -> let (_, inner_ctx) = check_expr_type_flow ctx e in TypeContext.update_outer_context ctx inner_ctx []) ctx ls)
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
                          
                          let ctx = List.fold_left (fun ctx' ref -> TypeContext.add_types_to_type_flow ctx' ref e_type) e_ctx refs in
                          (e_type, ctx)
                          
                                                      
  | Expr.Seq (e1, e2) ->  let (e1_type_flow, e1_ctx) = check_expr_type_flow ctx e1 in
                          let (e2_type_flow, e2_ctx) = check_expr_type_flow e1_ctx e2 in
                          (e2_type_flow, e2_ctx)
  | Expr.Skip -> ([], ctx)

  | Expr.If (e, thene, elsee) ->  let (_, e_inner_ctx) = check_expr_type_flow ctx e in
                                  let (then_type_flow, then_inner_ctx) = check_expr_type_flow e_inner_ctx thene in
                                  let (else_type_flow, else_inner_ctx) = check_expr_type_flow e_inner_ctx elsee in
                                  let merge_then_else_ctx = TypeContext.update_outer_context (TypeContext.update_outer_context e_inner_ctx then_inner_ctx []) else_inner_ctx [] in
                                  (List.concat [then_type_flow; else_type_flow], merge_then_else_ctx)

  | Expr.While (cond, body)      -> ([], check_cycle ctx (Expr.Seq(cond, body)))
  
  | Expr.DoWhile (body, cond)    ->  ([], check_cycle ctx (Expr.Seq(body, cond)) ) (*Union [], check_cycle ctx (Expr.Seq(e, cond)) *)
(*
  | Expr.Case (e, ls, _, _) ->    let (e_type_flow, e_ctx) = check_expr_type_flow ctx e in
                                  List.iter (fun t -> if List.fold_left (fun acc patt_t -> is_consistent_patt patt_t t || acc) false (List.map (fun (p, _) -> p) ls ) then () else raise (Failure (Printf.sprintf "No pattern for type %s" (type_to_string t)))  ) e_type_flow;
                                  let (tf, ctx )  = List.fold_left (fun (t_flow, ctx) (_, e) -> let (e_type_flow, e_ctx) = check_expr_type_flow ctx e in (List.concat [t_flow;e_type_flow], e_ctx)) ([], e_ctx) ls      
                                  in (Union tf, ctx) 
*)
  | Expr.Ignore e -> let (_, ctx) = check_expr_type_flow ctx e in ([(Any, None)], ctx)

  | Expr.Unit -> ([(Unit, None)], ctx)                                    

  | Expr.Scope (ds, e) ->   let inner_ctx = TypeContext.update_ctx ctx (List.map (fun (var, decl ) -> match decl with (_, `Fun (_,_, t)) -> (var, t) | (_, `Variable (_, t)) -> (var, t)) ds) in
                            let inner_ctx = List.fold_left (fun ctx (var, (_, vardecl)) -> 
                                                              match vardecl with
                                                                    `Fun (_, _, t) -> TypeContext.add_type_to_type_flow ctx var (t, None)
                                                                    | `Variable (Some e, _) -> let (type_flow, new_ctx) = check_expr_type_flow ctx e in 
                                                                                            TypeContext.add_types_to_type_flow new_ctx var type_flow
                                                                    | `Variable (None, _) -> ctx) inner_ctx ds   in
                            let (tflow, inner_ctx) = check_expr_type_flow inner_ctx e in
                            (tflow, TypeContext.update_outer_context ctx inner_ctx (List.map (fun (var, _) -> var) ds))
  | _ -> raise (Failure "Not implemented1")
                                           


(* Should also work this:
let check_expr ctx expr = let _ = check_expr_type_flow ctx expr in let _ = check_annotations ctx expr in (); 
*)
let check_expr ctx expr = let _ = check_annotations ctx expr in let _ = check_expr_type_flow ctx expr in ();