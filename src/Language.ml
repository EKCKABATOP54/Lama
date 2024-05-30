(* Opening a library for generic programming (https://github.com/dboulytchev/GT).
   The library provides "@type ..." syntax extension and plugins like show, etc.
*)
module OrigList = List

[@@@ocaml.warning "-7-8-13-15-20-26-27-32"]

open GT

(* Opening a library for combinator-based syntax analysis *)
open Ostap
open Combinators


@type lamaType =  
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
| TyId of string with show, html, foldl
(*Check show, html, foldl*)

@type lamaTypeAnnotation =  TA_Sexp 
                  | TA_Int 
                  | TA_String 
                  | TA_Array of lamaTypeAnnotation
                  | TA_Any 
                  | TA_Callable of (lamaTypeAnnotation list) * lamaTypeAnnotation
                  | TA_Unit 
                  | TA_Union of lamaTypeAnnotation list 
                  | TA_Tuple of lamaTypeAnnotation list 
                  | TA_TypeId of string
                  with show, html, foldl       

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


module Subst =
  struct

    module H = Hashtbl.Make (struct type t = string let hash = Hashtbl.hash let equal = (=) end)

    let tab = (H.create 1024 : string H.t)

    let attach infix op = H.add tab infix op
    let subst  id       = match H.find_opt tab id with None -> id | Some op -> op

  end

let infix_name infix =
  let b = Buffer.create 64 in
  Buffer.add_string b "i__Infix_";
  Seq.iter (fun c -> Buffer.add_string b (string_of_int @@ Char.code c)) @@ String.to_seq infix;
  let s = Buffer.contents b in
  Subst.attach s ("infix " ^ infix);
  s

let sys_infix_name infix =
  let b = Buffer.create 64 in
  Buffer.add_string b "s__Infix_";
  Seq.iter (fun c -> Buffer.add_string b (string_of_int @@ Char.code c)) @@ String.to_seq infix;
  let s = Buffer.contents b in
  Subst.attach s ("infix " ^ infix);
  s

exception Semantic_error of string

module Loc =
  struct
    @type t = int * int with show, html, foldl

    module H = Hashtbl.Make (struct type t = string let hash = Hashtbl.hash let equal = (==) end)

    let tab = (H.create 1024 : t H.t)

    let attach s loc = H.add tab s loc
    let get          = H.find_opt tab
    let get_exn      = H.find tab

  end

let report_error ?(loc=None) str =
  raise (Semantic_error (str ^ match loc with None -> "" | Some (l, c) -> Printf.sprintf " at (%d, %d)" l c));;

@type k = Unmut | Mut | FVal with show, html, foldl

(* Values *)
module Value =
  struct

    (* The type for name designation: global or local variable, argument, reference to closure, etc. *)
    @type designation =
    | Global of string
    | Local  of int
    | Arg    of int
    | Access of int
    | Fun    of string
    with show, html, foldl

    @type ('a, 'b) t =
    | Empty
    | Var     of designation
    | Elem    of ('a, 'b) t * int
    | Int     of int
    | String  of bytes
    | Array   of ('a, 'b) t array
    | Sexp    of string * ('a, 'b) t array
    | Closure of string list * 'a * 'b
    | FunRef  of string * string list * 'a * int
    | Builtin of string
    | Tuple of ('a, 'b) t array
    | DataConstr of string * ('a, 'b) t
    with show, html, foldl

    let is_int = function Int _ -> true | _ -> false

    let to_int = function
    | Int n -> n
    | x -> failwith (Printf.sprintf "int value expected (%s)\n" (show(t) (fun _ -> "<not supported>") (fun _ -> "<not supported>") x))

    let to_string = function
    | String s -> s
    | _ -> failwith "string value expected"

    let to_array = function
    | Array a -> a
    | _       -> failwith "array value expected"

    let sexp   s vs = Sexp (s, Array.of_list vs)
    let tuple vs = Tuple (Array.of_list vs)
    let of_int    n = Int    n
    let of_string s = String s
    let of_array  a = Array  a

    let tag_of = function
    | Sexp (t, _) -> t
    | _ -> failwith "symbolic expression expected"

    let update_string s i x = Bytes.set s i x; s
    let update_array  a i x = a.(i) <- x; a

    let update_elem x i v =
      match x with
      | Sexp (_, a) | Array a -> ignore (update_array a i v)
      | String a -> ignore (update_string a i (Char.chr @@ to_int v))
      | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__)

    let string_val v =
      let buf      = Buffer.create 128 in
      let append s = Buffer.add_string buf s in
      let rec inner = function
      | Int    n    -> append (string_of_int n)
      | String s    -> append "\""; append @@ Bytes.to_string s; append "\""
      | Array  a    -> append "["; Array.iteri (fun i a -> (if i > 0 then append ", "); inner a) a; append "]"
      | Sexp (t, a) -> let n = Array.length a in
                       if t = "cons"
                       then (
                         append "{";
                         let rec inner_list = function
                         | [||]                    -> ()
                         | [|x; Int 0|]            -> inner x
                         | [|x; Sexp ("cons", a)|] -> inner x; append ", "; inner_list a
                         | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__)
                         in inner_list a;
                         append "}"
                       )
                       else (
                         append t;
                         (if n > 0 then (append " ("; Array.iteri (fun i a -> (if i > 0 then append ", "); inner a) a;
                                         append ")"))
                       )
      | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__)
      in
      inner v;
      Bytes.of_string @@ Buffer.contents buf

  end

(* Builtins *)
module Builtin =
  struct

    let list        = ["read"; "write"; ".elem"; "length"; ".array"; "string"]
    let bindings () = List.map (fun name -> name, Value.Builtin name) list
    let names       = List.map (fun name -> name, (FVal, Any)) list (*TODO: Add correct types*)

    let eval (st, i, o, vs) args = function
    | "read"     -> (match i with z::i' -> (st, i', o, (Value.of_int z)::vs) | _ -> failwith "Unexpected end of input")
    | "write"    -> (st, i, o @ [Value.to_int @@ List.hd args], Value.Empty :: vs)
    | ".elem"    -> (match args with
                     | [b; j] -> (st, i, o, let i = Value.to_int j in
                                  (match b with
                                   | Value.String   s  -> Value.of_int @@ Char.code (Bytes.get s i)
                                   | Value.Array    a  -> a.(i)
                                   | Value.Sexp (_, a) -> a.(i)
                                  | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__)
                                  ) :: vs
                                 )
                     | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__)
                    )
    | "length"     -> (st, i, o, (Value.of_int (match List.hd args with Value.Sexp (_, a) | Value.Array a -> Array.length a | Value.String s -> Bytes.length s | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__)))::vs)
    | ".array"     -> (st, i, o, (Value.of_array @@ Array.of_list args)::vs)
    | "string"     -> (match args with | [a] -> (st, i, o, (Value.of_string @@ Value.string_val a)::vs) | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__))
    | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__)
  end

(* States *)
module State =
  struct

    (* State: global state, local state, scope variables *)
    @type 'a t =
    | I
    | G of (string * (k * lamaType)) list * (string, 'a) arrow
    | L of (string * (k * lamaType)) list * (string, 'a) arrow * 'a t
    with show, html, foldl

    (* Get the depth level of a state *)
    let rec level = function
    | I            -> 0
    | G _          -> 1
    | L (_, _, st) -> 1 + level st

    (* Prune state to a certain level *)
    let prune st n =
      let rec inner n st =
        match st with
        | I              -> st, 0
        | G (xs, s)      -> st, 1
        | L (xs, s, st') ->
           let st'', l = inner n st' in
           (if l >= n then st'' else st), l+1
      in
      fst @@ inner n st

    (* Undefined state *)
    let undefined x =
      report_error ~loc:(Loc.get x) (Printf.sprintf "undefined name \"%s\"" (Subst.subst x))

    (* Create a state from bindings list *)
    let from_list l = fun x -> try List.assoc x l with Not_found -> report_error ~loc:(Loc.get x) (Printf.sprintf "undefined name \"%s\"" (Subst.subst x))

    (* Bind a variable to a value in a state *)
    let bind x v s = fun y -> if x = y then v else s y

    (* empty state *)
    let empty = I

    (* Scope operation: checks if a name is in a scope *)
    let in_scope x s = List.exists (fun (y, _) -> y = x) s

    (* Scope operation: checks if a name designates variable *)
    let is_var x s = try Mut = fst (List.assoc x s) with Not_found -> false

    (* Update: non-destructively "modifies" the state s by binding the variable x
       to value v and returns the new state w.r.t. a scope
    *)
    let update x v s =
      let rec inner = function
      | I -> report_error "uninitialized state"
      | G (scope, s) ->
         if is_var x scope
         then G (scope, bind x v s)
         else report_error ~loc:(Loc.get x) (Printf.sprintf "name \"%s\" is undefined or does not designate a variable" (Subst.subst x))
      | L (scope, s, enclosing) ->
         if in_scope x scope
         then if is_var x scope
              then L (scope, bind x v s, enclosing)
              else report_error ~loc:(Loc.get x) (Printf.sprintf "name \"%s\" does not designate a variable" (Subst.subst x))
         else L (scope, s, inner enclosing)
      in
      inner s

    
    let rec get_type s x = 
      match s with
      | I                       -> report_error "uninitialized state"
      | G (xs, _)                -> (try List.assoc x xs with Not_found -> report_error (Printf.sprintf "undefined variable %s" x))
      | L (scope, _, enclosing) -> if in_scope x scope then try List.assoc x scope with Not_found -> report_error (Printf.sprintf "undefined variable %s" x) else get_type enclosing x      


    (* Evals a variable in a state w.r.t. a scope *)
    let rec eval s x =
      match s with
      | I                       -> report_error "uninitialized state"
      | G (_, s)                -> s x
      | L (scope, s, enclosing) -> if in_scope x scope then s x else eval enclosing x

    (* Drops a scope *)
    let leave st st' =
      let rec get = function
      | I           -> report_error "uninitialized state"
      | G _ as st   -> st
      | L (_, _, e) -> get e
      in
      let g = get st in
      let rec recurse = function
      | I               -> g
      | L (scope, s, e) -> L (scope, s, recurse e)
      | G _             -> g
      in
      recurse st'

    (* Creates a new scope, based on a given state *)
    let rec enter st xs =
      match st with
      | I           -> report_error "uninitialized state"
      | G _         -> L (xs, undefined, st)
      | L (_, _, e) -> enter e xs

    (* Push a new local scope *)
    let push st s xs =
      match st with
      | I -> G (xs @ Builtin.names, List.fold_left (fun s (name, value) -> bind name value s) s (Builtin.bindings ()))
      | _ -> L (xs, s, st)

    (* Drop a local scope *)
    let drop = function L (_, _, e) -> e | G _ -> I | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__)

    (* Observe a variable in a state and print it to stderr *)
    let observe st x =
      Printf.eprintf "%s=%s\n%!" x (try show (Value.t) (fun _ -> "<expr>") (fun _ -> "<state>") @@ eval st x with _ -> "undefined")

  end

(* Patterns *)
module Pattern =
  struct

    (* The type for patterns *)
    @type t =
    (* wildcard "-"     *) | Wildcard
    (*Tuple*)              | Tuple of t list
    (* S-expression     *) | Sexp   of string * t list
    (* array            *) | Array  of t list
    (* identifier       *) | Named  of string * t
    (* ground integer   *) | Const  of int
    (* ground string    *) | String of string
    (* boxed value      *) | Boxed
    (* unboxed value    *) | UnBoxed
    (* any string value *) | StringTag
    (* any sexp value   *) | SexpTag
    (* any array value  *) | ArrayTag
    (* any closure      *) | ClosureTag
    (*type constuctor*)    | DataConstr of string * t
    with show, foldl, html, fmt

    (* Pattern parser *)
    ostap (
      parse:
        !(Ostap.Util.expr
           (fun x -> x)
	   (Array.map (fun (a, s) ->
              a,
              List.map (fun s -> ostap(- $(s)), (fun x y -> Sexp ("cons", [x; y]))) s)
          [|`Righta, [":"]|]
	 )
	 primary);
      primary:
        %"_"                                         {Wildcard}
      | "<" ps:(!(Util.list0)[parse]) ">"            {Tuple ps}
      | t:UIDENT ps:(-"(" !(Util.list)[parse] -")")? {Sexp (t, match ps with None -> [] | Some ps -> ps)}
      | "[" ps:(!(Util.list0)[parse]) "]"            {Array ps}
      | "{" ps:(!(Util.list0)[parse]) "}"            {match ps with
                                                      | [] -> Const 0
                                                      | _  -> List.fold_right (fun x acc -> Sexp ("cons", [x; acc])) ps (Const 0)
                                                     }
      | l:$ x:LIDENT y:(-"@" parse)?                 {Loc.attach x l#coord; match y with None -> Named (x, Wildcard) | Some y -> Named (x, y)}
      | s:("-")? c:DECIMAL                           {Const (match s with None -> c | _ -> ~-c)}
      | s:STRING                                     {String s}
      | c:CHAR                                       {Const  (Char.code c)}
      | %"true"                                      {Const 1}
      | %"false"                                     {Const 0}
      | "#" %"box"                                   {Boxed}
      | "#" %"val"                                   {UnBoxed}
      | "#" %"str"                                   {StringTag}
      | "#" %"sexp"                                  {SexpTag}
      | "#" %"array"                                 {ArrayTag}
      | "#" %"fun"                                   {ClosureTag}
      | "!" t:UIDENT p:parse?                        {DataConstr (t, match p with Some t -> t | _ -> Wildcard)} (*maybe better add Unit to patterns and replace Wildcard with it*)
      | -"(" parse -")"
    )

    let vars p = transform(t) (fun f -> object inherit [string list, _] @t[foldl] f method c_Named s _ name p = name :: f s p end) [] p

  end

  

            
ostap(
  parseLamaTypeAnnotation:
    parseLamaTypeAnnotationSexp: "Sexp" {TA_Sexp}
    | parseLamaTypeAnnotationInt: "Int" {TA_Int}
    | parseLamaTypeAnnotationString: "String" {TA_String}
    | parseLamaTypeAnnotationArray: "Array" elem_t:parseLamaTypeAnnotation {TA_Array elem_t}
    | parseLamaTypeAnnotationAny: "Any" {TA_Any}
    | parseLamaTypeAnnotationCallable: "Callable" "[" args_t:(!(Util.list0)[parseLamaTypeAnnotation]) "]" ret_t:parseLamaTypeAnnotation{TA_Callable (args_t, ret_t)}
    | parseLamaTypeAnnotationUnit : "Unit" {TA_Unit}
    | parseLamaTypeAnnotationUnion : "Union" "[" tls:(!(Util.list0)[parseLamaTypeAnnotation]) "]" {TA_Union tls}
    | parseLamaTypeAnnotationTyple : "Tuple" "[" tls:(!(Util.list0)[parseLamaTypeAnnotation]) "]" {TA_Tuple tls}
    | parseLamaTypeAnnotationVariantType : (typename:UIDENT {TA_TypeId typename})
    )


(* Simple expressions: syntax and semantics *)
module Expr =
  struct
    (* The type of configuration: a state, an input stream, an output stream,
       and a stack of values
    *)
    @type 'a value  = ('a, 'a value State.t array) Value.t with show, html, foldl
    @type 'a config = 'a value State.t * int list * int list * 'a value list with show, html, foldl
    (* Reff : parsed expression should return value Reff (look for ":=");
       Val : -//- returns simple value;
       Void : parsed expression should not return any value;  *)

    @type atr = Reff | Void | Val | Weak with show, html, foldl

    @type qualifier = [ `Local | `Public | `Extern | `PublicExtern ]
        with show, html, foldl

    (* The type for expressions. Note, in regular OCaml there is no "@type..."
       notation, it came from GT.
    *)
    @type t =
    (* integer constant           *) | Const     of int * Loc.t
    (* array                      *) | Array     of t list
    (* string                     *) | String    of string
    (* S-expressions              *) | Sexp      of string * t list
    (* variable                   *) | Var       of string
    (* reference (aka "lvalue")   *) | Ref       of string
    (* binary operator            *) | Binop     of string * t * t
    (* element extraction         *) | Elem      of t * t
    (* reference to an element    *) | ElemRef   of t * t
    (* function call              *) | Call      of t * t list
    (* assignment                 *) | Assign    of t * t
    (* composition                *) | Seq       of t * t
    (* empty statement            *) | Skip
    (* conditional                *) | If        of t * t * t
    (* loop with a pre-condition  *) | While     of t * t
    (* loop with a post-condition *) | DoWhile   of t * t
    (* pattern-matching           *) | Case      of t * (Pattern.t * t) list * Loc.t * atr
    (* ignore a value             *) | Ignore    of t
    (* unit value                 *) | Unit
    (* entering the scope         *) | Scope     of (string * decl) list * t
    (* lambda expression          *) | Lambda    of string list * t
    (* leave a scope              *) | Leave
    (* intrinsic (for evaluation) *) | Intrinsic of (t config, t config) arrow
    (* control (for control flow) *) | Control   of (t config, t * t config) arrow
    (* tuple *)                      | Tuple of t list
    (*constructot of variant type*)  | DataConstr of string * t
    (*type cast*)                    | Roll of lamaTypeAnnotation
    (*type cast*)                    | UnRoll of lamaTypeAnnotation
    and decl = qualifier * [`Fun of string list * t * lamaTypeAnnotation| `Variable of t option * lamaTypeAnnotation | `VariantTypeDecl of (string * lamaTypeAnnotation) list]
    with show, html, foldl

    let notRef = function Reff -> false | _ -> true
    let isVoid = function Void | Weak -> true  | _ -> false

    (* Available binary operators:
        !!                   --- disjunction
        &&                   --- conjunction
        ==, !=, <=, <, >=, > --- comparisons
        +, -                 --- addition, subtraction
        *, /, %              --- multiplication, division, reminder
    *)

    (* Update state *)
    let update st x v =
      match x with
      | Value.Var (Value.Global x) -> State.update x v st
      | Value.Elem (x, i) -> Value.update_elem x i v; st
      | _                 -> report_error (Printf.sprintf "invalid value \"%s\" in update" @@ show(Value.t) (fun _ -> "<expr>") (fun _ -> "<state>") x)

    (* Expression evaluator

          val eval : env -> config -> k -> t -> config


       Takes an environment, a configuration and an expresion, and returns another configuration. The
       environment supplies the following method

           method definition : env -> string -> int list -> config -> config

       which takes an environment (of the same type), a name of the function, a list of actual parameters and a configuration,
       an returns a pair: the return value for the call and the resulting configuration
    *)
    let to_func op =
      let bti   = function true -> 1 | _ -> 0 in
      let itb b = b <> 0 in
      let (|>) f g   = fun x y -> f (g x y) in
      match op with
      | "+"  -> (+)
      | "-"  -> (-)
      | "*"  -> ( * )
      | "/"  -> (/)
      | "%"  -> (mod)
      | "<"  -> bti |> (< )
      | "<=" -> bti |> (<=)
      | ">"  -> bti |> (> )
      | ">=" -> bti |> (>=)
      | "==" -> bti |> (= )
      | "!=" -> bti |> (<>)
      | "&&" -> fun x y -> bti (itb x && itb y)
      | "!!" -> fun x y -> bti (itb x || itb y)
      | _    -> failwith (Printf.sprintf "Unknown binary operator %s" op)

    let seq x = function Skip -> x | y -> Seq (x, y)

    let schedule_list = function h::tl -> List.fold_left seq h tl | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__)

    let rec take = function
    | 0 -> fun rest  -> [], rest
    | n -> function h::tl -> let tl', rest = take (n-1) tl in h :: tl', rest | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__)

    let rec eval ((st, i, o, vs) as conf) k expr =
      (* let print_values vs =
        Printf.eprintf "Values:\n%!";
        List.iter (fun v -> Printf.eprintf "%s\n%!" @@ show(Value.t) (fun _ -> "<expr>") (fun _ -> "<state>") v) vs;
        Printf.eprintf "End Values\n%!"
      in *)
      match expr with
      | Lambda (args, body) ->
         eval (st, i, o, Value.Closure (args, body, [|st|]) :: vs) Skip k
      | Scope (defs, body) ->
         let vars, body, bnds =
           List.fold_left
             (fun (vs, bd, bnd) -> function
              | (name, (_, `Variable (value, t))) -> (name, (Mut, lamaTypeAnnotationTolamaType2 t)) :: vs, (match value with None -> bd | Some v -> Seq (Ignore (Assign (Ref name, v)), bd)), bnd
              | (name, (_, `Fun (args, b, t)))  -> (name, (FVal, lamaTypeAnnotationTolamaType2 t)) :: vs, bd, (name, Value.FunRef (name, args, b, 1 + State.level st)) :: bnd
              | (name, (_, `VariantTypeDecl _ )) -> vs, bd, bnd
             )
             ([], body, [])
             (List.rev @@
              List.map (function
                        | (name, (`Extern, _)) -> report_error (Printf.sprintf "external names (\"%s\") not supported in evaluation" (Subst.subst name))
                        | x -> x
                       )
              defs)
         in
         eval (State.push st (State.from_list bnds) vars, i, o, vs) k (Seq (body, Leave))
      | Unit ->
         eval (st, i, o, Value.Empty :: vs) Skip k
      | Ignore s ->
         eval conf k (schedule_list [s; Intrinsic (fun (st, i, o, vs) -> (st, i, o, List.tl vs))])
      | Control f ->
         let s, conf' = f conf in
         eval conf' k s
      | Intrinsic f ->
         eval (f conf) Skip k
      | Const (n, _) ->
         eval (st, i, o, (Value.of_int n) :: vs) Skip k
      | String s ->
         eval (st, i, o, (Value.of_string @@ Bytes.of_string s) :: vs) Skip k
      | Var x ->
         let v =
           match State.eval st x with
           | Value.FunRef (_, args, body, level) ->
              Value.Closure (args, body, [|State.prune st level|])
           | v -> v
         in
         eval (st, i, o, v :: vs) Skip k
      | Ref x ->
         eval (st, i, o, (Value.Var (Value.Global x)) :: vs) Skip k (* only Value.Global is supported in interpretation *)
      | Array xs ->
         eval conf k (schedule_list (xs @ [Intrinsic (fun (st, i, o, vs) -> let es, vs' = take (List.length xs) vs in Builtin.eval (st, i, o, vs') (List.rev es) ".array")]))
      | Sexp (t, xs) ->
         eval conf k (schedule_list (xs @ [Intrinsic (fun (st, i, o, vs) -> let es, vs' = take (List.length xs) vs in (st, i, o, Value.Sexp (t, Array.of_list (List.rev es)) :: vs'))]))
      | Tuple xs -> 
         eval conf k (schedule_list (xs @ [Intrinsic (fun (st, i, o, vs) -> let es, vs' = take (List.length xs) vs in (st, i, o, Value.Tuple (Array.of_list (List.rev es)) :: vs'))]))
      | Binop (op, x, y) ->
         eval conf k (schedule_list [x; y; Intrinsic (function (st, i, o, y::x::vs) -> (st, i, o, (Value.of_int @@ to_func op (Value.to_int x) (Value.to_int y)) :: vs) | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__))])
      | Elem (b, i) ->
         eval conf k (schedule_list [b; i; Intrinsic (function (st, i, o, j::b::vs) -> Builtin.eval (st, i, o, vs) [b; j] ".elem" | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__))])
      | ElemRef (b, i) ->
         eval conf k (schedule_list [b; i; Intrinsic (function (st, i, o, j::b::vs) -> (st, i, o, (Value.Elem (b, Value.to_int j))::vs) | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__))])
      | Call (f, args) ->
         eval conf k (schedule_list (f :: args @ [Intrinsic (fun (st, i, o, vs) ->
            let es, vs' = take (List.length args + 1) vs in
            match List.rev es with
            | f :: es ->
              (match f with
              | Value.Builtin name ->
                  Builtin.eval (st, i, o, vs') es name
              | Value.Closure (args, body, closure) ->
                  let st' = State.push (State.leave st closure.(0)) (State.from_list @@ List.combine args es) (List.map (fun x -> x, (Mut, Any)) args) in (*TODO : use correct arg type instead Any*)
                  let st'', i', o', vs'' = eval (st', i, o, []) Skip body in
                  closure.(0) <- st'';
                  (State.leave st'' st, i', o', match vs'' with [v] -> v::vs' | _ -> Value.Empty :: vs')
              | _ -> report_error (Printf.sprintf "callee did not evaluate to a function: \"%s\"" (show(Value.t) (fun _ -> "<expr>") (fun _ -> "<state>") f))
              )
            | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__)
            )]))

      | Leave  -> eval (State.drop st, i, o, vs) Skip k
      | Assign (x, e)  ->
         eval conf k (schedule_list [x; e; Intrinsic (function (st, i, o, v::x::vs) -> (update st x v, i, o, v::vs) | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__))])
      | Seq (s1, s2) ->
         eval conf (seq s2 k) s1
      | Skip ->
         (match k with Skip -> conf | _ -> eval conf Skip k)
      | If (e, s1, s2) ->
         eval conf k (schedule_list [e; Control (function (st, i, o, e::vs) -> (if Value.to_int e <> 0 then s1 else s2), (st, i, o, vs) | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__))])
      | While (e, s) ->
         eval conf k (schedule_list [e; Control (function (st, i, o, e::vs) -> (if Value.to_int e <> 0 then seq s expr else Skip), (st, i, o, vs) | _ -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__))])
      | DoWhile (s, e) ->
         eval conf (seq (While (e, s)) k) s
      | Case (e, bs, _, _)->
         let rec branch =
          function (_,_,_,[]) -> failwith (Printf.sprintf "Unexpected pattern: %s: %d" __FILE__ __LINE__)
          | ((st, i, o, v::vs) as conf) -> function
            | [] -> failwith (Printf.sprintf "Pattern matching failed: no branch is selected while matching %s\n" (show(Value.t) (fun _ -> "<expr>") (fun _ -> "<state>") v))
            | (patt, body)::tl ->
                let rec match_patt patt v st =
                  let update x v = function
                  | None   -> None
                  | Some s -> Some (State.bind x v s)
                  in
                  match patt, v with
                  | Pattern.Named (x, p), v                                                                   -> update x v (match_patt p v st )
                  | Pattern.Wildcard    , _                                                                   -> st
                  | Pattern.Sexp (t, ps), Value.Sexp (t', vs) when t = t' && List.length ps = Array.length vs -> match_list ps (Array.to_list vs) st
                  | Pattern.Tuple ps    , Value.Tuple vs when List.length ps = Array.length vs                -> match_list ps (Array.to_list vs) st
                  | Pattern.Array ps    , Value.Array vs when List.length ps = Array.length vs                -> match_list ps (Array.to_list vs) st
                  | Pattern.Const n     , Value.Int n'    when n = n'                                         -> st
                  | Pattern.String s    , Value.String s' when s = Bytes.to_string s'                         -> st
                  | Pattern.Boxed       , Value.String _
                  | Pattern.Boxed       , Value.Array  _
                  | Pattern.UnBoxed     , Value.Int    _
                  | Pattern.Boxed       , Value.Sexp  (_, _)
                  | Pattern.StringTag   , Value.String _
                  | Pattern.ArrayTag    , Value.Array  _
                  | Pattern.ClosureTag  , Value.Closure _
                  | Pattern.SexpTag     , Value.Sexp  (_, _)                                                  -> st
                  | _                                                                                         -> None
                and match_list ps vs s =
                  match ps, vs with
                  | [], []       -> s
                  | p::ps, v::vs -> match_list ps vs (match_patt p v s)
                  | _            -> None
                in
                match match_patt patt v (Some State.undefined) with
                | None     -> branch conf tl
                | Some st' -> eval (State.push st st' (List.map (fun x -> x, (Unmut, Any)) @@ Pattern.vars patt), i, o, vs) k (Seq (body, Leave)) (*TODO : Use correct type instead Any*)
         in
         eval conf Skip (schedule_list [e; Intrinsic (fun conf -> branch conf bs)])

  (* Expression parser. You can use the following terminals:
       LIDENT  --- a non-empty identifier a-z[a-zA-Z0-9_]* as a string
       UIDENT  --- a non-empty identifier A-Z[a-zA-Z0-9_]* as a string
       DECIMAL --- a decimal constant [0-9]+ as a string
  *)

  (* places ignore if expression should be void *)
  let ignore atr expr = match atr with Void -> Ignore expr | _ -> expr

  (* places dummy value if required *)
  let materialize atr l expr =
    match atr with
    | Weak -> Seq (expr, Const (0, l#coord))
    | _    -> expr

  (* semantics for infixes created in runtime *)
  let sem s = (fun x atr y -> ignore atr (Call (Var s, [x; y]))), (fun _ -> Val, Val)

  let sem_init s = fun x atr y ->
    let p x y =
      match s with
      | ":"  -> Sexp   ("cons", [x; y])
      | ":=" -> Assign (x, y)
      | _    -> Binop  (s, x, y)
    in
    match x with
      Ignore x -> Ignore (p x y)
    | _        -> ignore atr (p x y)

    (* ======= *)

    let left  f c x a y = f (c x) a y
    let right f c x a y = c (f x a y)

    let expr f ops opnd atr =
      let ops =
        Array.map
          (fun (assoc, (atrs, list)) ->
            let g = match assoc with `Lefta | `Nona -> left | `Righta -> right in
            assoc = `Nona, (atrs, altl (List.map (fun (oper, sema) -> ostap (!(oper) {g sema})) list))
          )
          ops
      in
      let atrr i atr = snd (fst (snd ops.(i)) atr) in
      let atrl i atr = fst (fst (snd ops.(i)) atr) in
      let n      = Array.length ops  in
      let op   i = snd (snd ops.(i)) in
      let nona i = fst ops.(i)      in
      let id   x = x                in
      let ostap (
        inner[l][c][atr]: f[ostap (
          {n = l                } => x:opnd[atr] {c x}
        | {n > l && not (nona l)} => (-x:inner[l+1][id][atrl l atr] -o:op[l] y:inner[l][o c x atr][atrr l atr] |
                                       x:inner[l+1][id][atr] {c x})
        | {n > l && nona l} => (x:inner[l+1][id][atrl l atr] o:op[l] y:inner[l+1][id][atrr l atr] {c (o id x atr y)} |
                                x:inner[l+1][id][atr] {c x})
          )]
      )
      in
      ostap (inner[0][id][atr])

    let atr' = atr
    let not_a_reference s = new Reason.t (Msg.make "not a reference" [||] (Msg.Locator.Point s#coord))

    (* UGLY! *)
    let predefined_op : (Obj.t -> Obj.t -> Obj.t) ref = Stdlib.ref (fun _ _ -> invalid_arg "must not happen")

    let defCell = Stdlib.ref 0

    (* ======= *)
    let makeParsers env =
    let [@ocaml.warning "-26"] makeParser, makeBasicParser, makeScopeParser =
      let [@ocaml.warning "-20"] def s   = let [@ocaml.warning "-8"] Some def = Obj.magic !defCell in def s in
      let ostap (
      parse[infix][atr]: h:basic[infix][Void] -";" t:parse[infix][atr] {Seq (h, t)} | basic[infix][atr];
      scope[infix][atr]: <(d, infix')> : def[infix] expr: parse[infix'][atr] {Scope (d, expr)} | {isVoid atr} => l:$ <(d, infix')> : def[infix] => {d <> []} => {Scope (d, materialize atr l Skip)};
      basic[infix][atr]: !(expr (fun x -> x) (Array.map (fun (a, (atr, l)) -> a, (atr, List.map (fun (s, _, f) -> ostap (- $(s)), f) l)) infix) (primary infix) atr);
      primary[infix][atr]:
          l:$ s:(s:"-"? {match s with None -> fun x -> x | _ -> fun x -> Binop ("-", Const (0, l#coord), x)})
          b:base[infix][Val] is:(  "." f:LIDENT args:(-"(" !(Util.list)[parse infix Val] -")")? {`Post (f, args)}
                                      | "[" i:parse[infix][Val] "]"                             {`Elem i}
                                      | "(" args:!(Util.list0)[parse infix Val] ")"             {`Call args}
          )+
        => {match (List.hd (List.rev is)), atr with
            | `Elem i, Reff -> true
            |  _,      Reff -> false
            |  _,      _    -> true} =>
        {
          let is =
            let rec fix_is = function
            | [ ]                                                 -> []
            | [x]                                                 -> [x]
            | `Post (f, None) :: `Call args :: tl when args != [] -> `Post (f, Some args) :: fix_is tl
            | x :: tl                                             -> x :: fix_is tl
            in
            fix_is is
          in
          let lastElem = List.hd (List.rev is) in
          let is = List.rev (List.tl (List.rev is)) in
          let b =
            List.fold_left
              (fun b ->
                function
                | `Elem i         -> Elem (b, i)
                | `Post (f, args) -> Call (Var f, b :: match args with None -> [] | Some args -> args)
                | `Call args      -> (match b with Sexp _ -> invalid_arg "retry!" | _ -> Call (b, args))
              )
              b
              is
          in
          let res = match lastElem, atr with
                    | `Elem i        , Reff -> ElemRef (b, i)
                    | `Elem i        , _    -> Elem (b, i)
                    | `Post (f, args), _    -> Call (Var f, b :: match args with None -> [] | Some args -> args)
                    | `Call args     , _    -> (match b with Sexp _ -> invalid_arg "retry!"  | _ -> Call (b, args))
          in
          ignore atr (s res)
        }
      | base[infix][atr];
      base[infix][atr]:
        l:$ n:DECIMAL                              => {notRef atr} :: (not_a_reference l) => {ignore atr (Const (n, l#coord))}
      | l:$ s:STRING                               => {notRef atr} :: (not_a_reference l) => {ignore atr (String s)}
      | l:$ c:CHAR                                 => {notRef atr} :: (not_a_reference l) => {ignore atr (Const  (Char.code c,l#coord))}

      | l:$ c:(%"true" {(Const (1, l#coord))} | %"false" {Const (0, l#coord)}) => {notRef atr} :: (not_a_reference l) => {ignore atr c}

      | l:$ %"infix" s:INFIX => {notRef atr} :: (not_a_reference l) => {
          if ((* UGLY! *) Obj.magic !predefined_op) infix s
          then (
            if s = ":="
            then report_error ~loc:(Some l#coord) (Printf.sprintf "can not capture predefined operator \":=\"")
            else
              let name = sys_infix_name s in Loc.attach name l#coord; ignore atr (Var name)
          )
          else (
            let name = infix_name s in Loc.attach name l#coord; ignore atr (Var name)
          )
      }
      | l:$ %"fun" "(" args:!(Util.list0)[Pattern.parse] ")"
           "{" body:scope[infix][Weak] "}"=> {notRef atr} :: (not_a_reference l) => {
          let args, body =
            List.fold_right
              (fun arg (args, body) ->
                 match arg with
                 | Pattern.Named (name, Pattern.Wildcard) -> name :: args, body
                 | Pattern.Wildcard -> env#get_tmp :: args, body
                 | p ->
                    let arg = env#get_tmp in
                    arg :: args, Case (Var arg, [p, body], l#coord, Weak)
              )
              args
              ([], body)
          in
          ignore atr (Lambda (args, body))
      }

      | l:$ "[" es:!(Util.list0)[parse infix Val] "]" => {notRef atr} :: (not_a_reference l) => {ignore atr (Array es)}
      | l:$ "{" es:!(Util.list0)[parse infix Val] "}" => {notRef atr} :: (not_a_reference l) => {ignore atr (match es with
                                                                                      | [] -> Const (0, l#coord)
                                                                                      | _  -> List.fold_right (fun x acc -> Sexp ("cons", [x; acc])) es (Const (0, l#coord)))
                                                                         }
      | l:$ "<" tuple_elements:!(Util.list0)[parse infix Val] ">" => {notRef atr} :: (not_a_reference l) => {ignore atr (Tuple tuple_elements)
                                                                                        }
      | l:$ t:UIDENT args:(-"(" !(Util.list)[parse infix Val] -")")? => {notRef atr} :: (not_a_reference l) => {ignore atr (Sexp (t, match args with
                                                                                                              | None -> []
                                                                                                              | Some args -> args))
                                                                                        }
      | l:$ "!" tag:UIDENT e:parse[infix][Val]? => {notRef atr} :: (not_a_reference l) => {ignore atr (DataConstr (tag, match e with
                                                                                                              | None -> Unit
                                                                                                              | Some e -> e))
                                                                                        }
      | l:$ x:LIDENT {Loc.attach x l#coord; if notRef atr then ignore atr (Var x) else Ref x}

      | {isVoid atr} => l:$ %"skip" {materialize atr l Skip}

      | %"if" e:parse[infix][Val] %"then" the:scope[infix][atr]
        elif:(%"elif" parse[infix][Val] %"then" scope[infix][atr])*
        els:("else" s:scope[infix][atr] {Some s} | {isVoid atr} => empty {None}) %"fi"
          l:$ {If (e, the, List.fold_right (fun (e, t) elif -> If (e, t, elif)) elif (match els with Some e -> e | _ -> materialize atr l Skip))}
      | l:$ %"while" e:parse[infix][Val] %"do" s:scope[infix][Void]
                                            => {isVoid atr} => %"od" {materialize atr l (While (e, s))}

      | l:$ %"for" i:scope[infix][Void] ","
               c:parse[infix][Val]             ","
               s:parse[infix][Void] %"do" b:scope[infix][Void] => {isVoid atr} => %"od"
               {materialize atr l
                  (match i with
                  | Scope (defs, i) -> Scope (defs, Seq (i, While (c, Seq (b, s))))
                  | _               -> Seq (i, While (c, Seq (b, s))))
               }

      | l:$ %"do" s:scope[infix][Void] %"while" e:parse[infix][Val] => {isVoid atr} =>  %"od" {
          materialize atr l @@
            match s with
            | Scope (defs, s) ->
               let defs, s =
                 List.fold_right (fun (name, def) (defs, s) ->
                     match def with
                     | (`Local, `Variable (Some expr, ta)) ->
                        (name, (`Local, `Variable (None, ta))) :: defs, Seq (Ignore (Assign (Ref name, expr)), s)
                     | def -> (name, def) :: defs, s)
                   defs
                   ([], s)
               in
               Scope (defs, DoWhile (s, e))
            | _  -> DoWhile (s, e)
      }
      | %"case" l:$ e:parse[infix][Val] %"of" bs:!(Util.listBy)[ostap ("|")][ostap (!(Pattern.parse) -"->" scope[infix][atr])] %"esac"{Case (e, bs, l#coord, atr)}
      | l:$ %"lazy" e:basic[infix][Val] => {notRef atr} :: (not_a_reference l) => {env#add_import "Lazy"; ignore atr (Call (Var "makeLazy", [Lambda ([], e)]))}
      | l:$ %"eta"  e:basic[infix][Val] => {notRef atr} :: (not_a_reference l) => {let name = env#get_tmp in ignore atr (Lambda ([name], Call (e, [Var name])))}
      | l:$ %"syntax" "(" e:syntax[infix] ")" => {notRef atr} :: (not_a_reference l) => {env#add_import "Ostap"; ignore atr e}
      | -"(" scope[infix][atr] (*parse[infix][atr]*) -")";
      syntax[infix]: ss:!(Util.listBy)[ostap ("|")][syntaxSeq infix] {
        List.fold_right (fun s -> function
                                  | Var "" -> s
                                  | acc    -> Call (Var "alt", [s; acc])
                        ) ss (Var "")
      };
      syntaxSeq[infix]: ss:syntaxBinding[infix]+ sema:(-"{" scope[infix][Val] -"}")? {
        let sema, ss =
          match sema with
          | Some s -> s, ss
          | None   ->
             let arr, ss =
               List.fold_left (fun (arr, ss) ((loc, omit, p, s) as elem) ->
                                 match omit with
                                 | None   -> (match p with
                                              | None                           -> let tmp = env#get_tmp in
                                                                                  ((Var tmp) :: arr, (loc, omit, Some (Pattern.Named (tmp, Pattern.Wildcard)), s) :: ss)
                                              | Some (Pattern.Named (name, _)) -> ((Var name) :: arr, elem :: ss)
                                              | Some p                         -> let tmp = env#get_tmp in
                                                                                  ((Var tmp) :: arr, (loc, omit, Some (Pattern.Named (tmp, p)), s) :: ss)
                                             )
                                 | Some _ -> (arr, elem :: ss)
                 ) ([], []) ss
             in
             (match arr with [a] -> a | _ -> Array (List.rev arr)), List.rev ss
        in
        let escape = String.map (function '"' -> ' ' | x -> x) in
        List.fold_right (fun (loc, _, p, s) ->
                           let make_right =
                             match p with
                             | None                                          -> (fun body -> Lambda ([env#get_tmp], body))
                             | Some (Pattern.Named (name, Pattern.Wildcard)) -> (fun body -> Lambda ([name], body))
                             | Some p                                        -> (fun body ->
                                                                                   let arg = env#get_tmp in
                                                                                   Lambda ([arg], Case (Var arg, [p, body], loc#coord, Val))
                                                                                )
                           in
                           function
                           | Var "" -> Call (Var (infix_name "@@"), [Array [String (escape (show(t) s)); s]; make_right sema])
                           | acc    -> Call (Var "seq", [s; make_right acc])
                        ) ss (Var "")
      };
      syntaxBinding[infix]: l:$ omit:"-"? p:(!(Pattern.parse) -"=")? s:syntaxPostfix[infix];
      syntaxPostfix[infix]: s:syntaxPrimary[infix] p:("*" {`Rep0} | "+" {`Rep} | "?" {`Opt})? {
        match p with
        | None       -> s
        | Some `Opt  -> Call (Var "opt" , [s])
        | Some `Rep  -> Call (Var "rep" , [s])
        | Some `Rep0 -> Call (Var "rep0", [s])
      };
      syntaxPrimary[infix]: l:$ p:LIDENT args:(-"[" !(Util.list0)[parse infix Val] -"]")* {
        Loc.attach p l#coord;
        List.fold_left (fun acc args -> Call (acc, args)) (Var p) args
      }
      | -"(" syntax[infix] -")"
      | -"$(" parse[infix][Val] -")"
    ) in (fun def -> defCell := Obj.magic !def; parse),
         (fun def -> defCell := Obj.magic !def; basic),
         (fun def -> defCell := Obj.magic !def; scope)
    in
    makeParser, makeBasicParser, makeScopeParser

    (* Workaround until Ostap starts to memoize properly *)
    ostap (
      constexpr:
        l:$ n:DECIMAL                                          {Const (n, l#coord)}
      | s:STRING                                           {String s}
      | l:$ c:CHAR                                             {Const (Char.code c, l#coord)}
      | l:$ %"true"                                            {Const (1, l#coord)}
      | l:$ %"false"                                           {Const (0, l#coord)}
      | "[" es:!(Util.list0)[constexpr] "]"                {Array es}
      | l:$ "{" es:!(Util.list0)[constexpr] "}"                {match es with [] -> Const (0, l#coord) | _  -> List.fold_right (fun x acc -> Sexp ("cons", [x; acc])) es (Const (0, l#coord))}
      | t:UIDENT args:(-"(" !(Util.list)[constexpr] -")")? {Sexp (t, match args with None -> [] | Some args -> args)}
      | l:$ x:LIDENT                                       {Loc.attach x l#coord; Var x}
      | -"(" constexpr -")"
    )
    (* end of the workaround *)

  end

(* Infix helpers *)
module Infix =
  struct

    @type kind     = Predefined | Public | Local with show
    @type ass      = [`Lefta | `Righta | `Nona] with show
    @type loc      = [`Before of string | `After of string | `At of string] with show
    @type export   = (ass * string * loc) list with show
    @type showable = (ass * string * kind) list array with show

    type t = ([`Lefta | `Righta | `Nona] * ((Expr.atr -> (Expr.atr * Expr.atr)) * ((string * kind * (Expr.t -> Expr.atr -> Expr.t -> Expr.t)) list))) array

    let show_infix (infix : t) =
      show(showable) @@ Array.map (fun (ass, (_, l)) -> List.map (fun (str, kind, _) -> ass, str, kind) l) infix

    let extract_exports infix =
      (* let ass_string = function `Lefta -> "L" | `Righta -> "R" | _ -> "I" in *)
      let exported =
        Array.map
          (fun (ass, (_, ops)) ->
            (ass, List.rev @@ List.map (fun (s, kind, _) -> s, kind) @@ List.filter (function (_, Public, _) | (_, Predefined, _) -> true | _ -> false) ops)
          )
          infix
      in
      let _, exports =
        Array.fold_left
          (fun (loc, acc) (ass, list) ->
            let rec inner (loc, acc) = function
              | [] -> (loc, acc)
              | (s, kind) :: tl ->
                 let loc' = match tl with [] -> `After s | _ -> `At s in
                 (fun again ->
                    match kind with
                    | Public -> again (loc', (ass, s, loc) :: acc)
                    | _      -> again (loc', acc)
                 )
                 (match tl with [] -> fun acc -> acc | _ -> fun acc -> inner acc tl)
            in
            inner (loc, acc) list
          )
          (`Before ":=", [])
          exported
      in List.rev exports

    let is_predefined op =
      List.exists (fun x -> op = x) [":"; "!!"; "&&"; "=="; "!="; "<="; "<"; ">="; ">"; "+"; "-"; "*" ; "/"; "%"; ":="]

    (*
    List.iter (fun op ->
        Printf.eprintf "F,%s\n" (sys_infix_name op);
        (*
        Printf.eprintf "// Functional synonym for built-in operator \"%s\";\n" op;
        Printf.eprintf "int L%s (void *p, void *q) {\n" (sys_infix_name op);
        Printf.eprintf "  ASSERT_UNBOXED(\"captured %s:1\", p);\n" op;
        Printf.eprintf "  ASSERT_UNBOXED(\"captured %s:2\", q);\n\n" op;
        Printf.eprintf "  return BOX(UNBOX(p) %s UNBOX(q));\n" op;
        Printf.eprintf "}\n\n"        *)
      ) [":"; "!!"; "&&"; "=="; "!="; "<="; "<"; ">="; ">"; "+"; "-"; "*" ; "/"; "%"]
     *)

    let default : t =
      Array.map (fun (a, s) ->
        a,
        ((fun _ -> (if (List.hd s) = ":=" then Expr.Reff else Expr.Val), Expr.Val),
        List.map (fun s -> s, Predefined, Expr.sem_init s) s)
      )
      [|
        `Righta, [":="];
        `Righta, [":"];
	`Lefta , ["!!"];
	`Lefta , ["&&"];
	`Nona  , ["=="; "!="; "<="; "<"; ">="; ">"];
	`Lefta , ["+" ; "-"];
	`Lefta , ["*" ; "/"; "%"];
      |]

    exception Break of [`Ok of t | `Fail of string]

    let find_op infix op cb ce =
      try
        Array.iteri (fun i (_, (_, l)) -> if List.exists (fun (s, _, _) -> s = op) l then raise (Break (cb i))) infix;
        ce ()
      with Break x -> x

    let predefined_op infix op =
      Array.exists
        (fun (_, (_, l)) ->
           List.exists (fun (s, p, _) -> s = op && p = Predefined) l
        )
        infix;;

    (* UGLY!!! *)
    Expr.predefined_op := (Obj.magic) predefined_op;;

    let no_op op coord = `Fail (Printf.sprintf "infix \"%s\" not found in the scope" op)

    let kind_of = function true -> Public | _ -> Local

    let at coord op newp public (sem, _) (infix : t) =
      find_op infix op
        (fun i ->
          `Ok (Array.init (Array.length infix)
                 (fun j ->
                   if j = i
                   then let (a, (atr, l)) = infix.(i) in (a, ( (*atr*) (fun _ -> Expr.Val, Expr.Val), ((newp, kind_of public, sem) :: (List.filter (fun (op', _, _) -> op' <> newp) l))))
                   else infix.(j)
            ))
        )
        (fun _ -> no_op op coord)

    let before coord op newp ass public (sem, atr) (infix : t) =
      find_op infix op
        (fun i ->
          `Ok (Array.init (1 + Array.length infix)
                 (fun j ->
                   if j < i
                   then infix.(j)
                   else if j = i then (ass, (atr, [newp, kind_of public, sem]))
                   else infix.(j-1)
                 ))
        )
        (fun _ -> no_op op coord)

    let after coord op newp ass public (sem, atr) (infix : t) =
      find_op infix op
        (fun i ->
          `Ok (Array.init (1 + Array.length infix)
                 (fun j ->
                   if j <= i
                   then infix.(j)
                   else if j = i+1 then (ass, (atr, [newp, kind_of public, sem]))
                   else infix.(j-1)
                 ))
        )
        (fun _ -> no_op op coord)

  end

(* Function and procedure definitions *)
module Definition =
  struct

    (* The type for a definition: either a function/infix, or a local variable *)
    type t = string * [`Fun of string list * Expr.t * lamaTypeAnnotation option | `Variable of Expr.t option * lamaTypeAnnotation option | `VariantTypeDecl of (string * lamaTypeAnnotation)list]

    let unopt_mod = function None -> `Local | Some m -> m

    (* I dont understand this part
    ostap (
      (* Workaround until Ostap starts to memoize properly *)
      const_var: l:$ name:LIDENT "=" value:!(Expr.constexpr) {
        Loc.attach name l#coord;
        name, (`Public, `Variable (Some value, Any))
       };
      constdef: %"public" d:!(Util.list (const_var)) ";" {d}
      (* end of the workaround *)
    )
    *)

    let [@ocaml.warning "-26"] makeParser env exprBasic exprScope =
    let ostap (
      arg : l:$ x:LIDENT {Loc.attach x l#coord; x};
      position[pub][ass][coord][newp]:
        %"at" s:INFIX {match ass with
                       | `Nona -> Infix.at coord s newp pub
                       | _     -> report_error ~loc:(Some coord) (Printf.sprintf "associativity for infix \"%s\" can not be specified (it is inherited from that for \"%s\")" newp s)
           }
        | f:(%"before" {Infix.before} | %"after" {Infix.after}) s:INFIX {f coord s newp ass pub};
      head[infix]:
        m:(%"external" {`Extern} | %"public" e:(%"external")? {match e with None -> `Public | _ -> `PublicExtern})? %"fun" l:$ name:LIDENT {Loc.attach name l#coord; unopt_mod m, name, name, infix, false}
    |   m:(%"public" {`Public})? ass:(%"infix" {`Nona} | %"infixl" {`Lefta} | %"infixr" {`Righta})
        l:$ op:(s:INFIX {s})
        md:position[match m with Some _ -> true | _ -> false][ass][l#coord][op] {
          if m <> None && Infix.is_predefined op then report_error ~loc:(Some l#coord) (Printf.sprintf "redefinition of standard infix operator \"%s\" can not be exported" op);
          let name = infix_name op in
          Loc.attach name l#coord;
          match md (Expr.sem name) infix with
          | `Ok infix' -> unopt_mod m, op, name, infix', true
          | `Fail msg  -> report_error ~loc:(Some l#coord) msg
      };
      local_var[m][infix]: l:$ name:LIDENT var_type:(-":" parseLamaTypeAnnotation)? value:(-"=" exprBasic[infix][Expr.Val])? {
        Loc.attach name l#coord;
        match m, value with
        | `Extern, Some _ -> report_error ~loc:(Some l#coord) (Printf.sprintf "initial value for an external variable \"%s\" can not be specified" name)
        | _               -> name, (m,`Variable (value, match var_type with Some t ->t | _ -> TA_Any))
      };

      parse[infix]:
        m:(%"var" {`Local} | %"public" e:(%"external")? {match e with None -> `Public | Some _ -> `PublicExtern} | %"external" {`Extern})
          locs:!(Util.list (local_var m infix)) next:";" {locs, infix}
          
    | "data" typename:UIDENT "=" ctrs:!(Util.listBy)[ostap("|")][ostap(ctr:UIDENT arg:(-"of" parseLamaTypeAnnotation)? {match arg with None -> (ctr, TA_Unit) | Some t -> (ctr, t)})] ";"{[(typename, (`Local, `VariantTypeDecl ctrs ))], infix}

    | - <(m, orig_name, name, infix', flag)> : head[infix] -"(" -args:!(Util.list0)[Pattern.parse] -")" -fun_type:(-":" parseLamaTypeAnnotation)?
          (l:$ "{" body:exprScope[infix'][Expr.Weak] "}" {
            if flag && List.length args != 2 then report_error ~loc:(Some l#coord) "infix operator should accept two arguments";
            match m with
            | `Extern -> report_error ~loc:(Some l#coord) (Printf.sprintf "a body for external function \"%s\" can not be specified" (Subst.subst orig_name))
            | _       ->
               let args, body =
                 List.fold_right
                   (fun arg (args, body) ->
                     match arg with
                     | Pattern.Named (name, Pattern.Wildcard) -> name :: args, body
                     | Pattern.Wildcard -> env#get_tmp :: args, body
                     | p ->
                        let arg = env#get_tmp in
                        arg :: args, Expr.Case (Expr.Var arg, [p, body], l#coord, Expr.Weak)
                   )
                   args
                   ([], body)
               in
               [(name, (m, `Fun (args, body, match fun_type with Some t -> t | _ -> TA_Any)))], infix'
         } |
         l:$ ";" {
            match m with
            | `Extern -> [(name, (m, `Fun (List.map (fun _ -> env#get_tmp) args, Expr.Skip, TA_Any)))], infix'
            | _       -> report_error ~loc:(Some l#coord) (Printf.sprintf "missing body for the function/infix \"%s\"" orig_name)
         })
    ) in parse

  end

module Interface =
  struct

    (* Generates an interface file. *)
    let gen ((imps, ifxs), p) =
      let buf = Buffer.create 256 in
      let append str = Buffer.add_string buf str in
      List.iter (fun i -> append "I,"; append i; append ";\n") imps;
      (match p with
       | Expr.Scope (decls, _) ->
          List.iter
            (function
             | (name, (`Public, item)) | (name, (`PublicExtern, item))  ->
                (match item with
                 | `Fun _      -> append "F,"; append name; append ";\n"
                 | `Variable _ -> append "V,"; append name; append ";\n"
                 | `VariantTypeDecl _ -> append "D,"; append name; append ";\n"
                )
             | _ -> ()
            )
            decls;
       | _ -> ());
      List.iter
        (function (ass, op, loc) ->
           let append_op op = append "\""; append op; append "\"" in
           append (match ass with `Lefta -> "L," | `Righta -> "R," | _ -> "N,");
           append_op op;
           append ",";
           (match loc with `At op -> append "T,"; append_op op | `After op -> append "A,"; append_op op | `Before op -> append "B,"; append_op op);
           append ";\n"
        ) ifxs;
      Buffer.contents buf

    (* Read an interface file *)
    let [@ocaml.warning "-26"] read fname =
      let ostap (
              funspec: "F" "," i:IDENT ";" {`Fun i};
              varspec: "V" "," i:IDENT ";" {`Variable i};
              import : "I" "," i:IDENT ";" {`Import i};
              infix  : a:ass "," op:STRING "," l:loc ";" {`Infix (a, op, l)};
              ass    : "L" {`Lefta} | "R" {`Righta} | "N" {`Nona};
              loc    : m:mode "," op:STRING {m op};
              mode   : "T" {fun x -> `At x} | "A" {fun x -> `After x} | "B" {fun x -> `Before x};
              interface: (funspec | varspec | import | infix)*
            )
      in
      try
        let s = Util.read fname in
        (match Util.parse (object
                             inherit Matcher.t s
                             inherit Util.Lexers.ident [] s
                             inherit Util.Lexers.string s
                             inherit Util.Lexers.skip  [Matcher.Skip.whitespaces " \t\n"] s
                           end)
                          (ostap (interface -EOF))
         with
         | `Ok intfs -> Some intfs
         | `Fail er  -> report_error (Printf.sprintf "malformed interface file \"%s\": %s" fname er)
        )
      with Sys_error _ -> None

    let find import paths =
      (*Printf.printf "Paths to search import in: %s" (show(list) (show(string)) paths); *)
      let rec inner = function
      | [] -> None
      | p::paths ->
         (match read (Filename.concat p (import ^ ".i")) with
          | None   -> inner paths
          | Some i -> Some (p, i)
         )
      in
      match inner paths with
      | Some (path, intfs) -> path, intfs
      | None               -> report_error (Printf.sprintf "could not find an interface file for import \"%s\"" import)

  end

(* The top-level definitions *)

(* Top-level evaluator

     eval : t -> int list -> int list

   Takes a program and its input stream, and returns the output stream
*)
let eval (_, expr) i =
  let _, _, o, _ = Expr.eval (State.empty, i, [], []) Skip expr in
  o

(* Top-level parser *)

ostap (
  imports[cmd]: l:$ is:(%"import" !(Util.list (ostap (UIDENT))) -";")* {
  let is    = "Std" :: List.flatten is in
  let infix =
    List.fold_left
      (fun infix import ->
        List.fold_left
          (fun infix item ->
             let insert name infix md =
               let name = infix_name name in
               match md (Expr.sem name) infix with
               | `Ok infix' -> infix'
               | `Fail msg  -> report_error msg
             in
             match item with
             | `Infix (_  , op, `At     op') -> insert op infix (Infix.at l#coord op' op false)
             | `Infix (ass, op, `Before op') -> insert op infix (Infix.before l#coord op' op ass false)
             | `Infix (ass, op, `After  op') -> insert op infix (Infix.after l#coord op' op ass false)
             | _                             -> infix
          )
          infix
          (snd (Interface.find import cmd#get_include_paths))
      )
      Infix.default
      is
  in
  is, infix
}
(*;

 Also dont understand this part
(* Workaround until Ostap starts to memoize properly *)
    constparse[cmd]: l:$ <(is, infix)> : imports[cmd] d:!(Definition.constdef) {(is, []), Expr.Scope (d, Expr.materialize Expr.Weak l Expr.Skip)}
(* end of the workaround *)
*)
)

let parse cmd =
  let env =
    object
      val imports   = Stdlib.ref ([] : string list)
      val tmp_index = Stdlib.ref 0

      method add_import imp = imports := imp :: !imports
      method get_tmp        = let index = !tmp_index in incr tmp_index; Printf.sprintf "__tmp%d" index
      method get_imports    = !imports
    end
  in

  let makeDefinitions env exprBasic exprScope =
    let def = Definition.makeParser env exprBasic exprScope in
    let ostap (
      definitions[infix]:
         <(def, infix')> : def[infix] <(defs, infix'')> : definitions[infix'] {
           def @ defs, infix''
         }
      | empty {[], infix}
    )
    in
    definitions
  in

  let definitions = Stdlib.ref None in

  let (makeParser, makeBasicParser, makeScopeParser) = Expr.makeParsers env in

  let expr        s = makeParser      definitions s in
  let exprBasic   s = makeBasicParser definitions s in
  let exprScope   s = makeScopeParser definitions s in

  definitions := Some (makeDefinitions env exprBasic exprScope);

  let [@ocaml.warning "-8-20"] Some definitions = !definitions in

  let ostap (
      parse[cmd]:
        <(is, infix)> : imports[cmd]
        <(d, infix')> : definitions[infix]
        l:$ expr:expr[infix'][Expr.Weak]? {
            (env#get_imports @ is, Infix.extract_exports infix'), Expr.Scope (d, match expr with None -> Expr.materialize Expr.Weak l Expr.Skip | Some e -> e)
          }
        )
  in
  parse cmd


let run_parser cmd =
  let s   = Util.read cmd#get_infile in
  let kws = [
    "skip";
    "if"; "then"; "else"; "elif"; "fi";
    "while"; "do"; "od";
    "for";
    "fun"; "var"; "public"; "external"; "import";
    "case"; "of"; "esac";
    "box"; "val"; "str"; "sexp"; "array";
    "infix"; "infixl"; "infixr"; "at"; "before"; "after";
    "true"; "false"; "lazy"; "eta"; "syntax"]
  in
  Util.parse
    (object
       inherit Matcher.t s
       inherit Util.Lexers.decimal s
       inherit Util.Lexers.string s
       inherit Util.Lexers.char   s
       inherit Util.Lexers.infix  s
       inherit Util.Lexers.lident kws s
       inherit Util.Lexers.uident kws s
       inherit Util.Lexers.skip [
        Matcher.Skip.whitespaces " \t\n\r";
        Matcher.Skip.lineComment "--";
        Matcher.Skip.nestedComment "(*" "*)"
       ] s
     end
    )
    (* Dont understand v3
    (if cmd#is_workaround then ostap (p:!(constparse cmd) -EOF)  else ostap (p:!(parse cmd) -EOF))
    *)
    (*replaced with *) (ostap (p:!(parse cmd) -EOF))









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
let typecheck_expr (ctx, tdctx) expr = let typeDefCtx = collect_variant_defs expr in
            let ctx = (ctx, List.append tdctx typeDefCtx) in
            let _ = check_annotations ctx expr in 
            let _ = check_expr_type_flow ctx expr in 
            ()