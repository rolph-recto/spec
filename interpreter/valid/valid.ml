open Ast
open Source
open Types


(* Errors *)

module Invalid = Error.Make ()
exception Invalid = Invalid.Error

let error = Invalid.error
let require b at s = if not b then error at s


(* Context *)

type context =
{
  types : func_type list;
  funcs : func_type list;
  tables : table_type list;
  memories : memory_type list;
  globals : global_type list;
  locals : value_type list;
  results : value_type list;
  labels : stack_type list;
}

let empty_context =
  { types = []; funcs = []; tables = []; memories = [];
    globals = []; locals = []; results = []; labels = [] }

let lookup category list x =
  try Lib.List32.nth list x.it with Failure _ ->
    error x.at ("unknown " ^ category ^ " " ^ Int32.to_string x.it)

let type_ (c : context) x = lookup "type" c.types x
let func (c : context) x = lookup "function" c.funcs x
let table (c : context) x = lookup "table" c.tables x
let memory (c : context) x = lookup "memory" c.memories x
let global (c : context) x = lookup "global" c.globals x
let local (c : context) x = lookup "local" c.locals x
let label (c : context) x = lookup "label" c.labels x


(* Stack typing *)

(*
 * Note: The declarative typing rules are non-deterministic, that is, they
 * have the liberty to locally "guess" the right types implied by the context.
 * In the algorithmic formulation required here, stack types are hence modelled
 * as lists of _options_ of types here, where `None` representss a locally
 * unknown type. Furthermore, an ellipses flag represents arbitrary sequences
 * of unknown types, in order to handle stack polymorphism algorithmically.
 *)

type ellipses = NoEllipses | Ellipses
type infer_stack_type = ellipses * value_type option list
type op_type = {ins : infer_stack_type; outs : infer_stack_type}

let known = List.map (fun t -> Some t)
let stack ts = (NoEllipses, known ts)
let (-~>) ts1 ts2 = {ins = NoEllipses, ts1; outs = NoEllipses, ts2}
let (-->) ts1 ts2 = {ins = NoEllipses, known ts1; outs = NoEllipses, known ts2}
let (-->...) ts1 ts2 = {ins = Ellipses, known ts1; outs = Ellipses, known ts2}

let string_of_infer_type t =
  Lib.Option.get (Lib.Option.map string_of_value_type t) "_"
let string_of_infer_types ts =
  "[" ^ String.concat " " (List.map string_of_infer_type ts) ^ "]"

let eq_ty t1 t2 = (t1 = t2 || t1 = None || t2 = None)
let check_stack ts1 ts2 at =
  require (List.length ts1 = List.length ts2 && List.for_all2 eq_ty ts1 ts2) at
    ("type mismatch: operator requires " ^ string_of_infer_types ts1 ^
     " but stack has " ^ string_of_infer_types ts2)

let pop (ell1, ts1) (ell2, ts2) at =
  let n1 = List.length ts1 in
  let n2 = List.length ts2 in
  let n = min n1 n2 in
  let n3 = if ell2 = Ellipses then (n1 - n) else 0 in
  check_stack ts1 (Lib.List.make n3 None @ Lib.List.drop (n2 - n) ts2) at;
  (ell2, if ell1 = Ellipses then [] else Lib.List.take (n2 - n) ts2)

let push (ell1, ts1) (ell2, ts2) =
  assert (ell1 = NoEllipses || ts2 = []);
  (if ell1 = Ellipses || ell2 = Ellipses then Ellipses else NoEllipses),
  ts2 @ ts1

let peek i (ell, ts) =
  try List.nth (List.rev ts) i with Failure _ -> None


(* Type Synthesis *)

let type_value = Values.type_of
let type_unop = Values.type_of
let type_binop = Values.type_of
let type_testop = Values.type_of
let type_relop = Values.type_of

let type_cvtop at = function
  | Values.I32 cvtop ->
    let open I32Op in
    (match cvtop with
    | ExtendSI32 | ExtendUI32 -> error at "invalid conversion"
    | WrapI64 -> I64Type
    | TruncSF32 | TruncUF32 | ReinterpretFloat -> F32Type
    | TruncSF64 | TruncUF64 -> F64Type
    ), I32Type
  | Values.I64 cvtop ->
    let open I64Op in
    (match cvtop with
    | ExtendSI32 | ExtendUI32 -> I32Type
    | WrapI64 -> error at "invalid conversion"
    | TruncSF32 | TruncUF32 -> F32Type
    | TruncSF64 | TruncUF64 | ReinterpretFloat -> F64Type
    ), I64Type
  | Values.F32 cvtop ->
    let open F32Op in
    (match cvtop with
    | ConvertSI32 | ConvertUI32 | ReinterpretInt -> I32Type
    | ConvertSI64 | ConvertUI64 -> I64Type
    | PromoteF32 -> error at "invalid conversion"
    | DemoteF64 -> F64Type
    ), F32Type
  | Values.F64 cvtop ->
    let open F64Op in
    (match cvtop with
    | ConvertSI32 | ConvertUI32 -> I32Type
    | ConvertSI64 | ConvertUI64 | ReinterpretInt -> I64Type
    | PromoteF32 -> F32Type
    | DemoteF64 -> error at "invalid conversion"
    ), F64Type


(* Expressions *)

let check_memop (c : context) (memop : 'a memop) get_sz at =
  ignore (memory c (0l @@ at));
  let size =
    match get_sz memop.sz with
    | None -> size memop.ty
    | Some sz ->
      require (memop.ty = I64Type || sz <> Memory.Mem32) at
        "memory size too big";
      Memory.mem_size sz
  in
  require (1 lsl memop.align <= size) at
    "alignment must not be larger than natural"

let check_arity n at =
  require (n <= 1) at "invalid result arity, larger than 1 is not (yet) allowed"


(*
 * Conventions:
 *   c  : context
 *   e  : instr
 *   es : instr list
 *   v  : value
 *   t  : value_type var
 *   ts : stack_type
 *   x  : variable
 *
 * Note: To deal with the non-determinism in some of the declarative rules,
 * the function takes the current stack `s` as an additional argument, allowing
 * it to "peek" when it would otherwise have to guess an input type.
 *
 * Furthermore, stack-polymorphic types are given with the `-->...` operator:
 * a type `ts1 -->... ts2` expresses any type `(ts1' @ ts1) -> (ts2' @ ts2)`
 * where `ts1'` and `ts2'` would be chosen non-deterministically in the
 * declarative typing rules.
 *)

let rec check_instr (c : context) (e : instr) (s : infer_stack_type) : op_type =
  match e.it with
  | Unreachable ->
    [] -->... []

  | Nop ->
    [] --> []

  | Block (ts, es) ->
    check_arity (List.length ts) e.at;
    check_block {c with labels = ts :: c.labels} es ts e.at;
    [] --> ts

  | Loop (ts, es) ->
    check_arity (List.length ts) e.at;
    check_block {c with labels = [] :: c.labels} es ts e.at;
    [] --> ts

  | If (ts, es1, es2) ->
    check_arity (List.length ts) e.at;
    check_block {c with labels = ts :: c.labels} es1 ts e.at;
    check_block {c with labels = ts :: c.labels} es2 ts e.at;
    [I32Type] --> ts

  | Br x ->
    label c x -->... []

  | BrIf x ->
    (label c x @ [I32Type]) --> label c x

  | BrTable (xs, x) ->
    let ts = label c x in
    List.iter (fun x' -> check_stack (known ts) (known (label c x')) x'.at) xs;
    (label c x @ [I32Type]) -->... []

  | Return ->
    c.results -->... []

  | Call x ->
    let FuncType (ins, out) = func c x in
    ins --> out

  | CallIndirect x ->
    ignore (table c (0l @@ e.at));
    let FuncType (ins, out) = type_ c x in
    (ins @ [I32Type]) --> out

  | Drop ->
    [peek 0 s] -~> []

  | Select ->
    let t = peek 1 s in
    [t; t; Some I32Type] -~> [t]

  | GetLocal x ->
    [] --> [local c x]

  | SetLocal x ->
    [local c x] --> []

  | TeeLocal x ->
    [local c x] --> [local c x]

  | GetGlobal x ->
    let GlobalType (t, mut) = global c x in
    [] --> [t]

  | SetGlobal x ->
    let GlobalType (t, mut) = global c x in
    require (mut = Mutable) x.at "global is immutable";
    [t] --> []

  | Load memop ->
    check_memop c memop (Lib.Option.map fst) e.at;
    [I32Type] --> [memop.ty]

  | Store memop ->
    check_memop c memop (fun sz -> sz) e.at;
    [I32Type; memop.ty] --> []

  | CurrentMemory ->
    ignore (memory c (0l @@ e.at));
    [] --> [I32Type]

  | GrowMemory ->
    ignore (memory c (0l @@ e.at));
    [I32Type] --> [I32Type]

  | Const v ->
    let t = type_value v.it in
    [] --> [t]

  | Test testop ->
    let t = type_testop testop in
    [t] --> [I32Type]

  | Compare relop ->
    let t = type_relop relop in
    [t; t] --> [I32Type]

  | Unary unop ->
    let t = type_unop unop in
    [t] --> [t]

  | Binary binop ->
    let t = type_binop binop in
    [t; t] --> [t]

  | Convert cvtop ->
    let t1, t2 = type_cvtop e.at cvtop in
    [t1] --> [t2]

and check_seq (c : context) (es : instr list) : infer_stack_type =
  match es with
  | [] ->
    stack []

  | _ ->
    let es', e = Lib.List.split_last es in
    let s = check_seq c es' in
    let {ins; outs} = check_instr c e s in
    push outs (pop ins s e.at)

and check_block (c : context) (es : instr list) (ts : stack_type) at =
  let s = check_seq c es in
  let s' = pop (stack ts) s at in
  require (snd s' = []) at
    ("type mismatch: operator requires " ^ string_of_stack_type ts ^
     " but stack has " ^ string_of_infer_types (snd s))


(* iTalX *)
(* to adapt the inference algorithm, we need to compute a CFG,
 * which is a bit tricky because of wasm's structured control structures.
 *)
type basic_block = { bb_id: int; instrs: instr list; }

(* we need to create a tree of basic blocks to
 * resolve branch targets correctly *)
type ctrl_type = CtrlBlock | CtrlLoop | CtrlIf
type bb_node =
  | NodeBlock of basic_block 
  | Control of ctrl_type * (bb_node list)

type bb_edge = int * int
type cfg = { blocks: basic_block list; edges: bb_edge list; }

(* create tree of basic blocks *)
let create_bb_tree (is: instr list) : bb_node list =
  let rec create_bb_tree' (n: int ref) (is: instr list) : bb_node list =
    let add_to_current_block (i: instr) (blocks: bb_node list) = 
      match blocks with
      | (NodeBlock b)::bs -> (NodeBlock { b with instrs=b.instrs@[i] }) :: bs
      | _ ->
        let blocks' = (NodeBlock { bb_id=(!n); instrs=[i]; }) :: blocks in
        n := !n + 1;
        blocks'
    in
    let process_instr (i: instr) (acc: bb_node list) =
      match i.it with
      (* branch / exception *)
      | Br _ | BrIf _ | Unreachable | Return | Call _ | CallIndirect _ ->
        let acc'  = add_to_current_block i acc in
        let acc'' = (NodeBlock { bb_id=(!n); instrs=[] }) :: acc' in
        n := !n + 1;
        acc''

      (* control structure *)
      | Block (_, binstrs) ->
        (Control (CtrlBlock, create_bb_tree' n binstrs)) :: acc

      | Loop (_, binstrs) ->
        (Control (CtrlLoop, create_bb_tree' n binstrs)) :: acc

      | If (_, tinstrs, einstrs) ->
        (* we split up the branches into separate Control subtrees
         * to prevent accidentally adding spurious edges to the CFG
         * e.g. a br_if instruction at the end of the then branch will fall thru
         * to the else branch if both were in the same control subtree *)
        let acc'      = add_to_current_block i acc in
        let then_ctrl = Control (CtrlIf, create_bb_tree' n tinstrs) in
        let else_ctrl = Control (CtrlIf, create_bb_tree' n einstrs) in
        let acc''     = else_ctrl :: then_ctrl :: acc' in
        acc''

      (* regular instruction; add to current basic block *)
      | _ -> add_to_current_block i acc
    in
    List.fold_right process_instr is []
  in
  let rec remove_empty_blocks (blocks: bb_node list) =
    let remove_empty_block (block: bb_node) : bb_node list =
      match block with
      | Control (ctrl_label, ctrl_blocks) ->
        let ctrl_blocks' = remove_empty_blocks ctrl_blocks in
        [Control (ctrl_label, ctrl_blocks')]

      | NodeBlock { instrs=[]; _ } -> []

      | _ -> [block]
    in
    List.concat (List.map remove_empty_block blocks)
  in
  let n = ref 0 in
  let tree  = create_bb_tree' n is in
  let tree' = remove_empty_blocks tree in
  tree'
;;

type bb_zipper = {
  left: bb_node list;
  right: bb_node list;
  ctrl: ctrl_type;
}
type bb_ctx = {
  zipper: bb_zipper list;
  left: bb_node list;
  right: bb_node list;
  focus: bb_node;
}

(* pop out of the current context *)
let focus_up (ctx: bb_ctx) =
  match ctx.zipper with
  | [] -> error no_region "no context to pop out of!"
  | z::zs ->
    let blocks = (List.rev ctx.left) @ [ctx.focus] @ (ctx.right) in
    let node = Control (z.ctrl, blocks) in
    let ctx' = { zipper=zs; left=z.left; right=z.right; focus=node; } in
    ctx'
;;

(* push into the current context *)
let focus_down (ctx: bb_ctx) =
  match ctx.focus with
  | NodeBlock _ | Control (_, []) ->
    error no_region "no focused context to push into!"

  | Control (ctrl_label, cb::cbs) ->
    let z = { left=ctx.left; right=ctx.right; ctrl=ctrl_label } in
    let ctx' = { zipper=z::ctx.zipper; left=[]; right=cbs; focus=cb } in
    ctx'
;;

(* focus on the next part of the bb_tree, if there is any *)
let rec focus_next (ctx: bb_ctx) =
  match ctx.right with
  | [] ->
    begin match ctx.zipper with
    (* nothing else to process! *)
    | [] -> None

    (* finished processing this block; pop out into the outer block and
     * continue processing there *)
    | _ ->
      ctx |> focus_up |> focus_next
    end

  | b::bs ->
    Some { ctx with left=ctx.focus::ctx.left; right=bs; focus=b; }
;;

(* add edges between basic blocks *)
let create_cfg (bbs: bb_node list) : cfg =
  (* finds the next basic block. if the focus is already a basic block, then
   * this function returns the context unchanged *)
  let rec find_block (ctx: bb_ctx) =
    match ctx.focus with
    | NodeBlock block -> Some (ctx, block)
    | Control (_, []) ->
      begin match focus_next ctx with
      | None -> None
      | Some ctx' -> find_block ctx'
      end

    | _ -> ctx |> focus_down |> find_block
  in
  (* like find block, except it ignores the current focus *)
  let find_next_block (ctx: bb_ctx) =
    match ctx.focus with
    | Control (_, _::_) -> ctx |> focus_down |> find_block
    | _ ->
      begin match focus_next ctx with
      | None -> None
      | Some ctx' -> find_block ctx'
      end
  in
  let rec compute_branch_target (level: int) (ctx: bb_ctx) =
    match (level, ctx.zipper) with
    | (0, z::_)  ->
      let traverse =
        match z.ctrl with
        (* the first basic block AFTER this context is the branch target *)
        | CtrlBlock | CtrlIf ->
          ctx |> focus_up |> find_next_block

        (* the first basic block from this context is the branch target *)
        | CtrlLoop ->
          ctx |> focus_up |> focus_down |> find_block
      in
      begin match traverse with
      | None -> error no_region "could not find branch target"
      | Some (_, block) -> block.bb_id
      end

    | (n, _::_)  ->
      ctx |> focus_up |> compute_branch_target (n-1)

    | (_, [])     -> error no_region "branch target not in scope"
  in
  let process_instr (ctx: bb_ctx) (bb_id: int) (i: instr) (acc: bb_edge list) =
    match i.it with
    | Br target ->
      let target_id = compute_branch_target (Int32.to_int target.it) ctx in
      (bb_id, target_id)::acc

    (* like branch, but this has a fallthrough edge to the next block *)
    | BrIf target ->
      let target_id = compute_branch_target (Int32.to_int target.it) ctx in
      let acc' = (bb_id, target_id)::acc in
      begin match find_next_block ctx with
      (* there is no next block; this block doesn't fallthrough anywhere *)
      | None -> acc'

      (* there is a fallthrough block *)
      | Some (_, fallthru) -> (bb_id, fallthru.bb_id) :: acc'
      end

    (* the next two blocks should be the then/else branches of this
     * conditional. we need to add edges from this block to the first
     * blocks there *)
    | If _ ->
      begin match ctx.right with
      | (Control (CtrlIf, bt::bts))::(Control (CtrlIf, be::bes))::_ ->
        let then_ctx = { zipper=[]; left=[]; right=bts; focus=bt } in
        let else_ctx = { zipper=[]; left=[]; right=bes; focus=be } in
        begin match (find_block then_ctx, find_block else_ctx) with
        | (Some (_,tblock), Some (_,eblock)) ->
          (bb_id, tblock.bb_id)::(bb_id, eblock.bb_id)::acc

        | _ -> error no_region "blocks of then/else branches not found!"
        end

      | _ -> error no_region "then/else branches of conditional not found!"
      end

    (* regular instruction; do nothing *)
    | _ -> acc
  in
  let process_block (ctx: bb_ctx) (b: basic_block) =
    List.fold_right (process_instr ctx b.bb_id) b.instrs []
  in
  let rec create_cfg' (ctx: bb_ctx) =
    let process_next cur_edges =
      match focus_next ctx with
      | None -> cur_edges
      | Some ctx' ->
        let rest = create_cfg' ctx' in
        cur_edges @ rest
    in 
    match ctx.focus with
    | NodeBlock block ->
      let block_edges = process_block ctx block in
      process_next block_edges

    | Control _ -> error no_region "context is not focused on node block!"
  in
  let rec get_basic_blocks (blocks: bb_node list) =
    let get_basic_block (block: bb_node) =
      match block with
      | NodeBlock block -> [block]
      | Control (_, ctrl_blocks) -> get_basic_blocks ctrl_blocks
    in
    List.concat (List.map get_basic_block blocks)
  in
  match bbs with
  | [] -> { blocks=[]; edges=[] }
  | b::bs ->
    let ctx = { zipper=[]; left=[]; right=bs; focus=b; } in
    begin match find_block ctx with
    | Some (ctx', _) ->
      let blocks  = get_basic_blocks bbs in
      let edges   = create_cfg' ctx' in
      { blocks; edges; }

    | None -> error no_region "no basic block found!"
    end
;;


(* Types *)

let check_limits {min; max} at =
  match max with
  | None -> ()
  | Some max ->
    require (I32.le_u min max) at
      "size minimum must not be greater than maximum"

let check_value_type (t : value_type) at =
  ()

let check_func_type (ft : func_type) at =
  let FuncType (ins, out) = ft in
  List.iter (fun t -> check_value_type t at) ins;
  List.iter (fun t -> check_value_type t at) out;
  check_arity (List.length out) at

let check_table_type (tt : table_type) at =
  let TableType (lim, _) = tt in
  check_limits lim at

let check_memory_size (sz : I32.t) at =
  require (I32.le_u sz 65536l) at
    "memory size must be at most 65536 pages (4GiB)"

let check_memory_type (mt : memory_type) at =
  let MemoryType lim = mt in
  check_limits lim at;
  check_memory_size lim.min at;
  Lib.Option.app (fun max -> check_memory_size max at) lim.max

let check_global_type (gt : global_type) at =
  let GlobalType (t, mut) = gt in
  check_value_type t at


(* Functions & Constants *)

(*
 * Conventions:
 *   c : context
 *   m : module_
 *   f : func
 *   e : instr
 *   v : value
 *   t : value_type
 *   s : func_type
 *   x : variable
 *)

let check_type (t : type_) =
  check_func_type t.it t.at

let check_func (c : context) (f : func) =
  let {ftype; locals; body} = f.it in
  let FuncType (ins, out) = type_ c ftype in
  let c' = {c with locals = ins @ locals; results = out; labels = [out]} in
  check_block c' body out f.at


let is_const (c : context) (e : instr) =
  match e.it with
  | Const _ -> true
  | GetGlobal x -> let GlobalType (_, mut) = global c x in mut = Immutable
  | _ -> false

let check_const (c : context) (const : const) (t : value_type) =
  require (List.for_all (is_const c) const.it) const.at
    "constant expression required";
  check_block c const.it [t] const.at


(* Tables, Memories, & Globals *)

let check_table (c : context) (tab : table) =
  let {ttype} = tab.it in
  check_table_type ttype tab.at

let check_memory (c : context) (mem : memory) =
  let {mtype} = mem.it in
  check_memory_type mtype mem.at

let check_elem (c : context) (seg : table_segment) =
  let {index; offset; init} = seg.it in
  check_const c offset I32Type;
  ignore (table c index);
  ignore (List.map (func c) init)

let check_data (c : context) (seg : memory_segment) =
  let {index; offset; init} = seg.it in
  check_const c offset I32Type;
  ignore (memory c index)

let check_global (c : context) (glob : global) =
  let {gtype; value} = glob.it in
  let GlobalType (t, mut) = gtype in
  check_const c value t


(* Modules *)

let check_start (c : context) (start : var option) =
  Lib.Option.app (fun x ->
    require (func c x = FuncType ([], [])) x.at
      "start function must not have parameters or results"
  ) start

let check_import (im : import) (c : context) : context =
  let {module_name = _; item_name = _; idesc} = im.it in
  match idesc.it with
  | FuncImport x ->
    {c with funcs = type_ c x :: c.funcs}
  | TableImport tt ->
    check_table_type tt idesc.at;
    {c with tables = tt :: c.tables}
  | MemoryImport mt ->
    check_memory_type mt idesc.at;
    {c with memories = mt :: c.memories}
  | GlobalImport gt ->
    check_global_type gt idesc.at;
    let GlobalType (_, mut) = gt in
    require (mut = Immutable) idesc.at
      "mutable globals cannot be imported (yet)";
    {c with globals = gt :: c.globals}

module NameSet = Set.Make(struct type t = Ast.name let compare = compare end)

let check_export (c : context) (set : NameSet.t) (ex : export) : NameSet.t =
  let {name; edesc} = ex.it in
  (match edesc.it with
  | FuncExport x -> ignore (func c x)
  | TableExport x -> ignore (table c x)
  | MemoryExport x -> ignore (memory c x)
  | GlobalExport x ->
    let GlobalType (_, mut) = global c x in
    require (mut = Immutable) edesc.at
      "mutable globals cannot be exported (yet)"
  );
  require (not (NameSet.mem name set)) ex.at "duplicate export name";
  NameSet.add name set

let check_module (m : module_) =
  let
    { types; imports; tables; memories; globals; funcs; start; elems; data;
      exports } = m.it
  in
  let c0 =
    List.fold_right check_import imports
      {empty_context with types = List.map (fun ty -> ty.it) types}
  in
  let c1 =
    { c0 with
      funcs = c0.funcs @ List.map (fun f -> type_ c0 f.it.ftype) funcs;
      tables = c0.tables @ List.map (fun tab -> tab.it.ttype) tables;
      memories = c0.memories @ List.map (fun mem -> mem.it.mtype) memories;
    }
  in
  let c =
    { c1 with globals = c1.globals @ List.map (fun g -> g.it.gtype) globals }
  in
  List.iter check_type types;
  List.iter (check_global c1) globals;
  List.iter (check_table c1) tables;
  List.iter (check_memory c1) memories;
  List.iter (check_elem c1) elems;
  List.iter (check_data c1) data;
  List.iter (check_func c) funcs;
  check_start c start;
  ignore (List.fold_left (check_export c) NameSet.empty exports);
  require (List.length c.tables <= 1) m.at
    "multiple tables are not allowed (yet)";
  require (List.length c.memories <= 1) m.at
    "multiple memories are not allowed (yet)"
