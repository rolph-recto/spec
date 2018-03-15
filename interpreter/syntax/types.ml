(* Types *)

type ty_var = int
type ty_atom = string

type value_type = I32Type | I64Type | F32Type | F64Type
                (* | TyName of ty_name *)
                (* | TyConstrName of ty_constr list * ty_name *)

(* type constructors *)
and ty_name =
  | TyVar of ty_var
  | TyAtom of ty_atom
  | TyFunc of ty_atom * (ty_name list)

(* subtyping constraints *)
and ty_constr =
  | Subtype of ty_var * ty_atom

type block_type = { constrs: ty_constr list; stack: stack_type }

module IntCompare = struct type t = int let compare = compare end
module IdMap = Map.Make(IntCompare)
module IdSet = Set.Make(IntCompare)

(* find the least var that is fresh in the block
 * this is used during generalization when creating fresh variables *)
let rec get_fresh_var (st: stack_type) =
  let rec get_var_tyname = function
  | TyVar v -> [v]
  | TyAtom -> []
  | TyFunc (_, args) -> List.map get_var_tyname args |> List.concat
  in
  let get_var = function
  | I32Type | I64Type | F32Type | F64Type -> []
  | 
  | TyConstrName (constrs, name) ->
    let constr_vars = List.map (fun (Subtype (v,_) -> v) constrs in
    let name_vars = get_var_tyname name in
    constr_vars @ name_vars
  in
  let vars = List.map get_var st |> List.concat in
  let m = List.fold_right min vars 0 in
  m + 1
;;

let subst_stack_vars (st: stack_type) (repl_map: ) : stack_map=


;;


type elem_type = AnyFuncType
type stack_type = value_type list
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
