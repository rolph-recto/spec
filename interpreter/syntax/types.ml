(* Types *)

type ty_var = int
type ty_atom = string

type value_type = I32Type | I64Type | F32Type | F64Type
                  | TyName of ty_name
                  | TyConstrName of ty_constr list * ty_name

(* type constructors *)
and ty_name =
  | TyVar of ty_var
  | TyAtom of ty_atom
  | TyFunc of ty_atom * (ty_name list)

(* subtyping constraints *)
and ty_constr =
  | Subtype of ty_var * ty_atom

type stack_type = value_type list
type block_type = { constrs: ty_constr list; stack: stack_type }

module IntCompare = struct type t = int let compare = compare end
module StrCompare = struct type t = string let compare = compare end
module ConstrCompare =
  struct type t = ty_constr
  let compare (Subtype (v1, a1)) (Subtype (v2, a2)) =
    let c1 = compare v1 v2 in
    let c2 = compare a1 a2 in
    if not (c1 = 0) then c1 else c2
end
module IdMap = Map.Make(IntCompare)
module IdSet = Set.Make(IntCompare)
module ConstrSet = Set.Make(ConstrCompare)
module AtomSet = Set.Make(StrCompare)

(* find the least var that is fresh in the block
 * this is used during generalization when creating fresh variables *)
let rec get_fresh_var (st: stack_type) =
  let rec get_var_tyname = function
  | TyVar v -> [v]
  | TyAtom _ -> []
  | TyFunc (_, args) -> List.map get_var_tyname args |> List.concat
  in
  let get_var = function
  | I32Type | I64Type | F32Type | F64Type -> []
  | TyName name -> get_var_tyname name
  | TyConstrName (constrs, name) ->
    let constr_vars = List.map (fun (Subtype (v,_)) -> v) constrs in
    let name_vars = get_var_tyname name in
    constr_vars @ name_vars
  in
  let vars = List.map get_var st |> List.concat in
  let m = List.fold_right min vars 0 in
  m + 1
;;

let subst_stack_vars (st: stack_type) (repl_map: ty_var IdMap.t) : stack_type =
  let rec repl_tyname tyname = match tyname with
  | TyVar v  -> let v' = IdMap.find v repl_map in TyVar v'
  | TyAtom a -> TyAtom a
  | TyFunc (f, args) -> let args' = List.map repl_tyname args in TyFunc (f, args')
  in
  let repl_constr = function
  | Subtype (v, a) -> let v' = IdMap.find v repl_map in Subtype (v', a)
  in
  let repl_val_type vt = match vt with
  | I32Type | I64Type | F32Type | F64Type -> vt
  | TyName tyname -> let tyname' = repl_tyname tyname in TyName tyname'
  | TyConstrName (constrs, tyname) ->
    let constrs'  = List.map repl_constr constrs in
    let tyname'   = repl_tyname tyname in
    TyConstrName (constrs', tyname')
  in
  List.map repl_val_type st
;;

let truncate_stacks (st1: stack_type) (st2: stack_type)
    : (stack_type * stack_type) =
  let n  = min (List.length st1) (List.length st2) in
  let st1' = Lib.List.drop (List.length st1 - n) st1 in
  let st2' = Lib.List.drop (List.length st2 - n) st2 in
  (st1', st2')
;;

let stack_to_block_type (st: stack_type) : block_type = 
  let hoist_constraints vt = 
    match vt with
    | I32Type | I64Type | F32Type | F64Type | TyName _ -> (vt, [])
    | TyConstrName (constrs, name) -> (TyName name, constrs)
  in
  let (stack, constrs') = st |> List.map hoist_constraints |> List.split in
  let constrs = List.concat constrs' in
  { constrs; stack }
;;

(* check for alpha-equivalence of block types *)
let is_block_equiv (bt1: block_type) (bt2: block_type) : bool = 
  let build_constr_map (Subtype (var,a)) acc =
    if IdMap.mem var acc
    then begin
      let varmap = IdMap.find var acc in
      let varmap' = AtomSet.add a varmap in
      IdMap.add var varmap' acc
    end
    else IdMap.add var (AtomSet.singleton a) acc
  in
  let vconstrs1 = List.fold_right build_constr_map bt1.constrs IdMap.empty in
  let vconstrs2 = List.fold_right build_constr_map bt2.constrs IdMap.empty in
  let rec compare_tynames t1 t2 =
    match t1, t2 with
    (* check if variable constraints are equal *)
    | TyVar v1, TyVar v2 ->
      let vcs1 = IdMap.find v1 vconstrs1 in
      let vcs2 = IdMap.find v2 vconstrs1 in
      AtomSet.equal vcs1 vcs2

    | TyAtom a1, TyAtom a2 when a1 = a2 -> true

    | TyFunc (f1, args1), TyFunc (f2, args2) when f1 = f2 ->
      List.combine args1 args2 |>
      List.map (fun (a1, a2) -> compare_tynames a1 a2) |>
      fun lst -> List.fold_right (&&) lst true

    | _ -> false
  in
  let compare_val_types v1 v2 =
    match v1, v2 with
    | I32Type, I32Type | I64Type, I64Type
    | F32Type, F32Type | F64Type, F64Type -> true
    | TyName t1, TyName t2 -> compare_tynames t1 t2
    | TyConstrName _, _ | _, TyConstrName _ ->
      failwith "constrained tyname not expected in block type"
    | _ -> false
  in
  let rec compare_val_type_list s1 s2 =
    match s1, s2 with
    | [], [] -> true
    | v1::t1, v2::t2 ->
      if compare_val_types v1 v2
      then compare_val_type_list t1 t2
      else false
  in
  let (st1', st2') = truncate_stacks bt1.stack bt2.stack in
  compare_val_type_list st1' st2'
;;

type elem_type = AnyFuncType
type func_type = FuncType of stack_type * stack_type

type 'a limits = {min : 'a; max : 'a option}
type mutability = Immutable | Mutable
type table_type = TableType of Int32.t limits * elem_type
type memory_type = MemoryType of Int32.t limits
type global_type = GlobalType of value_type * mutability
type extern_type =
  | ExternFuncType of func_type
  | ExternTableType of table_type
  | ExternMemoryType of memory_type
  | ExternGlobalType of global_type


(* Attributes *)

let size = function
  | I32Type | F32Type -> 4
  | I64Type | F64Type -> 8


(* Subtyping *)

let match_limits lim1 lim2 =
  I32.ge_u lim1.min lim2.min &&
  match lim1.max, lim2.max with
  | _, None -> true
  | None, Some _ -> false
  | Some i, Some j -> I32.le_u i j

let match_func_type ft1 ft2 =
  ft1 = ft2

let match_table_type (TableType (lim1, et1)) (TableType (lim2, et2)) =
  et1 = et2 && match_limits lim1 lim2

let match_memory_type (MemoryType lim1) (MemoryType lim2) =
  match_limits lim1 lim2

let match_global_type gt1 gt2 =
  gt1 = gt2

let match_extern_type et1 et2 =
  match et1, et2 with
  | ExternFuncType ft1, ExternFuncType ft2 -> match_func_type ft1 ft2
  | ExternTableType tt1, ExternTableType tt2 -> match_table_type tt1 tt2
  | ExternMemoryType mt1, ExternMemoryType mt2 -> match_memory_type mt1 mt2
  | ExternGlobalType gt1, ExternGlobalType gt2 -> match_global_type gt1 gt2
  | _, _ -> false


(* Filters *)

let funcs =
  Lib.List.map_filter (function ExternFuncType t -> Some t | _ -> None)
let tables =
  Lib.List.map_filter (function ExternTableType t -> Some t | _ -> None)
let memories =
  Lib.List.map_filter (function ExternMemoryType t -> Some t | _ -> None)
let globals =
  Lib.List.map_filter (function ExternGlobalType t -> Some t | _ -> None)


(* String conversion *)

let string_of_value_type = function
  | I32Type -> "i32"
  | I64Type -> "i64"
  | F32Type -> "f32"
  | F64Type -> "f64"

let string_of_value_types = function
  | [t] -> string_of_value_type t
  | ts -> "[" ^ String.concat " " (List.map string_of_value_type ts) ^ "]"

let string_of_elem_type = function
  | AnyFuncType -> "anyfunc"

let string_of_limits {min; max} =
  I32.to_string_u min ^
  (match max with None -> "" | Some n -> " " ^ I32.to_string_u n)

let string_of_memory_type = function
  | MemoryType lim -> string_of_limits lim

let string_of_table_type = function
  | TableType (lim, t) -> string_of_limits lim ^ " " ^ string_of_elem_type t

let string_of_global_type = function
  | GlobalType (t, Immutable) -> string_of_value_type t
  | GlobalType (t, Mutable) -> "(mut " ^ string_of_value_type t ^ ")"

let string_of_stack_type ts =
  "[" ^ String.concat " " (List.map string_of_value_type ts) ^ "]"

let string_of_func_type (FuncType (ins, out)) =
  string_of_stack_type ins ^ " -> " ^ string_of_stack_type out

let string_of_extern_type = function
  | ExternFuncType ft -> "func " ^ string_of_func_type ft
  | ExternTableType tt -> "table " ^ string_of_table_type tt
  | ExternMemoryType mt -> "memory " ^ string_of_memory_type mt
  | ExternGlobalType gt -> "global " ^ string_of_global_type gt
