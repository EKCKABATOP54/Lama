(*TODO: open Language*)
(*open Src.Language*)
open Marshal
open Base64
(*test function*)
let rec fib n = if n < 2 then 1 else fib(n-1) + fib(n-2)



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


let marshal_from_b64string s = Marshal.from_string (Base64.decode_exn s) 0

let is_consistent_with_error_reporting t1 t2 = let res = is_consistent t1 t2 in (if not res then Printf.printf "Type error. %s is not consistent with %s" (type_to_string t1) (type_to_string t2)); res

(* Export functions to C *)
let _ = Callback.register "extern_ocaml_fib" fib
let _ = Callback.register "extern_ocaml_is_consistent" (*Language.*)is_consistent
let _ = Callback.register "extern_ocaml_marshal_from_b64string" marshal_from_b64string
let _ = Callback.register "extern_ocaml_type_to_string" type_to_string
