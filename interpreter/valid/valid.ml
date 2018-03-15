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

let print_instrs (instrs: instr list) =
  List.iter begin fun i ->
    Printf.printf "%s\n" (Arrange.instr i |> Sexpr.to_string_mach 0)
  end instrs

let rec print_bb_tree ?(indent=0) (bb_tree: bb_node list) =
  let print_ctrl_label = function
    | CtrlBlock -> "block" | CtrlLoop -> "loop" | CtrlIf -> "if"
  in
  let print_block block =
    List.iter begin fun instr ->
      Printf.printf "%s%s\n" (String.make (indent+2) ' ')
        (Arrange.instr instr |> Sexpr.to_string_mach 0)
    end block.instrs
  in
  List.iter begin fun bb_node ->
    match bb_node with
    | NodeBlock block ->
      Printf.printf "%sBasicBlock %d\n" (String.make indent ' ') block.bb_id;
      print_block block

    | Control (ctrl_label, ctrl_block) ->
      Printf.printf "%sControl: %s\n" (String.make indent ' ') (print_ctrl_label ctrl_label);
      print_bb_tree ctrl_block ~indent:(indent+2)

  end bb_tree

let print_cfg (cfg: cfg) = 
  List.iter begin fun (s,t) ->
    Printf.printf "(%d, %d)\n" s t;
  end cfg.edges

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
    let process_instr (acc: bb_node list) (i: instr) =
      match i.it with
      (* branch / exception *)
      | Br _ | BrIf _ | BrTable _ | Unreachable | Return ->
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
        let acc''     = then_ctrl::acc' in
        begin match einstrs with
        | [] -> acc''
        | _ ->
          let else_ctrl = Control (CtrlIf, create_bb_tree' n einstrs) in
          let acc'''    = else_ctrl :: acc'' in
          acc'''
        end

      (* regular instruction; add to current basic block *)
      | _ -> add_to_current_block i acc
    in
    List.fold_left process_instr [] is |> List.rev
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
  let n = ref 1 in
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

    (* don't go into then/else blocks of conditionals *)
    | Control (_, []) | Control (CtrlIf, _) ->
      begin match focus_next ctx with
      | None -> None
      | Some ctx' -> find_block ctx'
      end

    | Control (CtrlBlock, _) | Control (CtrlLoop, _) ->
      ctx |> focus_down |> find_block
  in
  (* like find block, except it ignores the current focus *)
  let find_next_block (ctx: bb_ctx) =
    match focus_next ctx with
    | None -> None
    | Some ctx' -> find_block ctx'
  in
  let rec compute_branch_target (level: int) (ctx: bb_ctx) =
    match (level, ctx.zipper) with
    | (0, z::_)  ->
      begin match z.ctrl with
      (* the first basic block AFTER this context is the branch target *)
      | CtrlBlock | CtrlIf ->
        ctx |> focus_up |> find_next_block

      (* the first basic block from this context is the branch target *)
      | CtrlLoop ->
        ctx |> focus_up |> focus_down |> find_block
      end

    | (n, _::_)  ->
      ctx |> focus_up |> compute_branch_target (n-1)

    | (_, [])     -> error no_region "branch target not in scope"
  in
  let process_instr (ctx: bb_ctx) (bb_id: int) (i: instr) (acc: bb_edge list) =
    let add_target_edge edges target =
      match compute_branch_target (Int32.to_int target.it) ctx with
      | Some (_, target) -> (bb_id, target.bb_id)::edges
      | None -> edges
    in
    match i.it with
    | Br target -> add_target_edge acc target

    (* like branch, but this has a fallthrough edge to the next block *)
    | BrIf target ->
      let acc' =
        match compute_branch_target (Int32.to_int target.it) ctx with
        | Some (_, target) -> (bb_id, target.bb_id)::acc 
        | None -> acc
      in
      begin match find_next_block ctx with
      (* there is no next block; this block doesn't fallthrough anywhere *)
      | None -> acc'

      (* there is a fallthrough block *)
      | Some (_, fallthru) -> (bb_id, fallthru.bb_id) :: acc'
      end

    (* like branch, but there's a list of targets instead of just one *)
    | BrTable (br_targets, def) ->
      let remove_dup_targets acc target =
        if not (List.mem target acc) then target::acc else acc
      in
      let targets = def::br_targets |> List.fold_left remove_dup_targets [] in
      List.fold_left add_target_edge acc targets

    (* the next two blocks should be the then/else branches of this
     * conditional. we need to add edges from this block to the first
     * blocks there *)
    | If _ ->
      begin match ctx.right with
      | (Control (CtrlIf, bt::bts))::tlright ->
        let then_ctx = { zipper=[]; left=[]; right=bts; focus=bt } in
        let acc' =
          match find_block then_ctx with
          | Some (_,tblock) -> (bb_id, tblock.bb_id)::acc
          | _ -> error no_region "blocks of then branch not found!"
        in
        (* add edge to else block, if it exists *)
        let acc'' =
          match tlright with
          | (Control (CtrlIf, be::bes))::_ ->
            let else_ctx = { zipper=[]; left=[]; right=bes; focus=be } in
            begin match find_block else_ctx with
            | Some (_,eblock) -> (bb_id, eblock.bb_id)::acc'
            | _ -> error no_region "blocks of else branch not found!"
            end

          | _ -> acc'
        in
        acc''

      | _ -> error no_region "then branch of conditional not found!"
      end

    (* regular instruction; do nothing *)
    | _ -> acc
  in
  let process_block (ctx: bb_ctx) (b: basic_block) =
    List.fold_right (process_instr ctx b.bb_id) b.instrs []
  in
  let rec create_cfg' (ctx: bb_ctx) =
    let process_next cur_edges =
      match find_next_block ctx with
      | None -> cur_edges
      | Some (ctx',_) ->
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

(* type inference  *)
(* some changes:
    - locals need to be able to change types if they are to have types that are
    more complicated than just variants of Int (e.g objects). because of this,
    instead of being placed in the context they need to be represented in the
    stack directly
    - since locals are represented in the stack directly, instructions such as
    SetLocal can change inner parts of the stack, not just the top. so the
    input/output types of instructions cannot just be concatenated to determine
    the stack type of an instruction list. because of this, we cannot re-use
    check_instr directly, which makes this assumption
*)

let rec pop_stack elems s =
  match (elems, s) with
  | ([], _) -> s
  | (e::es, x::xs) ->
    if e = x 
    then pop_stack es xs
    else begin
      let sx = string_of_value_type x in
      let se = string_of_value_type e in
      let msg = Printf.sprintf "got %s, expected %s" sx se in
      error no_region (Printf.sprintf "pop_stack: unexpected type (%s)" msg)
    end
  | (_::_, []) -> error no_region "pop_stack: stack is empty"

let rec push_stack elems s =
  match elems with
  | [] -> s
  | e::es -> push_stack es (e::s)

let rec peek_stack n s =
  match (n, s) with
  | (0, x::_) -> x
  | (_, _::xs) -> peek_stack (n-1) xs
  | _ -> error no_region "peek_stack: invalid index"

(* get the type of a local in the stack
 * this assumes that locals are at the bottom of the stack *)
let get_local n s =
  let local_ind = List.length s - 1 - (Int32.to_int n.it) in
  List.nth s local_ind

(* set the type of a local in the stack *)
let set_local n t s =
  let local_ind = List.length s - 1 - (Int32.to_int n.it) in
  Lib.List.replace local_ind t s


let resolve_memop_type (t: value_type) (memop: 'a memop) : value_type =
  match t with
  | I32Type | I64Type | F32Type | F64Type -> memop.ty
  (* add case here for constrained type *)
  (* | _ -> *)

let check_instr_no_branch (c: context) (s: stack_type) (e: instr) : stack_type =
  let sintr = Arrange.instr e |> Sexpr.to_string_mach 0 in
  Printf.printf "check_instr %s %s\n" sintr (string_of_stack_type s);
  match e.it with
  | Unreachable -> s

  | Nop -> s

  | Block _ -> s

  | Loop _ -> s

  | If _ -> s |> pop_stack [I32Type]

  | Br _ -> s

  | BrIf _ -> s |> pop_stack [I32Type]

  | BrTable _ ->
    Printf.printf "%s\n" (string_of_stack_type s);
    s |> pop_stack [I32Type]

  | Return -> s |> pop_stack c.results

  | Call x ->
    let FuncType (ins, out) = func c x in
    s |> pop_stack ins |> push_stack out

  | CallIndirect x ->
    ignore (table c (0l @@ e.at));
    let FuncType (ins, out) = type_ c x in
    s |> pop_stack [I32Type] |> pop_stack ins |> push_stack out

  | Drop -> s |> pop_stack [peek_stack 0 s]

  | Select ->
    let t = peek_stack 1 s in
    s |> pop_stack [I32Type] |> pop_stack [t; t] |> push_stack [t]

  | GetLocal x ->
    let t = get_local x s in
    s |> push_stack [t]

  | SetLocal x ->
    let t = peek_stack 0 s in
    s |> pop_stack [t] |> set_local x t

  | TeeLocal x ->
    let t = peek_stack 0 s in
    s |> set_local x t

  | GetGlobal x ->
    let GlobalType (t, mut) = global c x in
    s |> push_stack [t]

  | SetGlobal x ->
    let GlobalType (t, mut) = global c x in
    require (mut = Mutable) x.at "global is immutable";
    s |> pop_stack [t]

  | Load memop ->
    check_memop c memop (Lib.Option.map fst) e.at;
    let in_ty   = peek_stack 0 s in
    let out_ty  = resolve_memop_type in_ty memop in
    s |> pop_stack [in_ty] |> push_stack [out_ty]

  | Store memop ->
    check_memop c memop (fun sz -> sz) e.at;
    let in_ty   = peek_stack 1 s in
    let out_ty  = resolve_memop_type in_ty memop in
    s |> pop_stack [out_ty] |> pop_stack [in_ty]

  | CurrentMemory ->
    ignore (memory c (0l @@ e.at));
    s |> push_stack [I32Type]

  | GrowMemory ->
    ignore (memory c (0l @@ e.at));
    s |> pop_stack [I32Type] |> push_stack [I32Type]

  | Const v ->
    let t = type_value v.it in
    s |> push_stack [t]

  | Test testop ->
    let t = type_testop testop in
    s |> pop_stack [t] |> push_stack [I32Type]

  | Compare relop ->
    let t = type_relop relop in
    s |> pop_stack [t; t] |> push_stack [I32Type]

  | Unary unop ->
    let t = type_unop unop in
    s |> pop_stack [t] |> push_stack [t]

  | Binary binop ->
    let t = type_binop binop in
    s |> pop_stack [t; t] |> push_stack [t]

  | Convert cvtop ->
    let t1, t2 = type_cvtop e.at cvtop in
    s |> pop_stack [t1] |> push_stack [t2]
;;

(* infer the (postcondition) stack type of the basic block by gluing together
 * the stack types of its instructions *)
let infer_block_type (c: context) (pre: stack_type) (b: basic_block) : stack_type =
  List.fold_left (check_instr_no_branch c) pre b.instrs
;;

type genmap = IdSet.t IdMap.t

(* union value types together by creating fresh vars when necessary and mapping
 * fresh vars to old vars *)
let generalize (st1: stack_type) (st2: stack_type) : stack_type * genmap =
  let min_var = min (get_fresh_var st1) (get_fresh_var st2) in
  let fresh_var = ref min_var in
  let collect_genmaps genmap acc =
    IdMap.union (fun _ s1 s2 -> Some (IdSet union s1 s2)) genmap acc
  in
  let rec generalize_names (tn1: ty_name) (tn2: ty_name) =
    match tn1, tn2 ->
    | TyAtom a1, TyAtom n2 when a1 = a2 ->
      (tn1, IdMap.empty)

    | TyFunc (f1, args1), TyFunc (f2, args2) when f1 = f2 ->
      let args = List.combine args1 args2 in
      let (args', genmaps) =
        List.map (fun (a1,a2) -> generalize_names a1 a2) args |> List.split
      in
      let genmap = List.fold_right collect_genmaps genmaps IdMap.empty in
      (TyFunc (f1, args'), genmap)

    | TyVar v1, TyVar v2 when v1 = v2 ->
      (tn1, IdMap.empty)

    | TyVar v1, TyVar v2 when not (v1 = v2) -> 
      let var = !fresh_var in
      let varset = IdSet.empty |> IdSet.add v1 |> IdSet.add v2 in
      let genmap = IdMap.empty |> IdMap.add var varset in
      fresh_var := !fresh_var + 1;
      (TyVar var, genmap)

    | _ -> error no_region "generalize_names: cannot unify type names"
  in
  let generalize_type (v1: value_type) (v2: value_type) =
    match (v1, v2) with
    | I32Type, I32Type | I64Type, I64Type
    | F32Type, F32Type | F64Type, F64Type ->
      (v1, IdMap.empty)

    | TyName n1, TyName n2 ->
      generalize_names n1 n2

    | TyConstrName _, _ | _, TyConstrName _ ->
      error no_region "generalize: constrained type names encountered"
  in
  let 
  let (st', genmaps) =
    List.combine st1 st2
    |> List.map (fun (v1,v2) -> generalize_type v1 v2) 
    |> List.split
  in
  let genmap = List.fold_right collect_genmaps genmaps IdMap.empty in
  (st', genmap)
;;

(* create equiv classes of fresh vars and combine new constraints for them
 * this function takes in a constraint resolver to compute the new constraint
 * given a set of constraints for old_vars to which the fresh var is mapped *)
let factorize (constrs: ty_constr list) (st: stack_type) (genmap: genmap)
              (resolver: ty_atom list -> ty_atom) : block_type =

  (* compute equivalence classes of fresh vars based on
   * the old vars they are mapped to *)
  let equiv_classes =
    let rec add_to_equiv_class var classes =
      match classes with
      (* create new equiv class *)
      | [] -> [[var]]
      | c::cs ->
        let repr = List.hd c in
        if IdSet.equal (IdMap.find repr) (IdMap.find var)
        then let c' = var::c in c'::cs
        else c::(add_to_equiv_class var cs)
    in
    let keys = IdMap.bindings genmap |> List.fst in
    List.fold_right add_to_equiv_class keys []
  in
  (* for each equivalence class, choose a representative and map all other
   * vars in that class to the representative *)
  let (reprs, repl_map) =
    let build_class_map cls =
      let repr = List.hd cls in
      let class_map =
        List.fold_right (fun var acc -> IdMap.add var repr acc) cls
      in
      (repr, class_map)
    in
    let merge_class_map (repr, class_map) (reprs, acc) =
      let merge_err _ _ _ =
        error no_region "factorize: class maps must be disjoint"
      in
      let acc' = IdMap.union merge_err class_map acc in
      (repr::reprs, acc')
    in
    let class_maps_with_repr = List.map build_class_map equiv_classes in
    List.fold_right merge_class_map class_maps ([], IdMap.empty)
  in
  (* rewrite stack type so that fres hvars in equiv class are replaced
   * with their representatives *)
  let st' = subst_stack_vars st repl_map in
  (* map representatives to the constraints of their old vars *)
  let repr_old_constrs =
    let build_repr_old_constrs repr =
      let old_vars = IdMap.find repr genmap in
      let constr_of_old_var (Subtype (c,_)) = IdSet.mem c old_vars in
      let old_constrs = List.filter constr_of_old_var constrs in
      (repr, old_constrs)
    in
    List.map build_repr_old_constrs reprs
  in
  let repr_constrs =
    let resolve_repr_constrs (repr, old_constrs) =
      let new_constr =
        List.map (fun Subtype (_, bound) -> bound) old_constrs |> resolver
      in
      Subtype (repr, new_constr)
    in
    List.map resolve_repr_constrs repr_old_constrs
  in
  { constrs = repr_constrs @ constrs; stack = st' }
;;

let compute_block_join (c: context) (bt1: block_type) (bt2: block_type) : block_type =
  let n  = min (List.length bt1.stack) (List.length bt2.stack) in
  let st1' = Lib.List.drop (List.length bt1.stack - n) bt1.stack in
  let st2' = Lib.List.drop (List.length bt2.stack - n) bt2.stack in
  let (st', genmap) = generalize st1' st2' in
  let constrs' = (* combine bt1 and bt2 constraints here *)
  let resolver = (* build resolver from context *)
  let bt' = factorize constrs' st' genmap resolver in
  bt'
;;

(* given two stack types, compute their join
 * returns the join and whether or not the two types were equivalent *)
let compute_join (st1: stack_type) (st2: stack_type) =
  let n = min (List.length st1) (List.length st2) in
  let st1'  = Lib.List.drop (List.length st1 - n) st1 in
  let st2'  = Lib.List.drop (List.length st2 - n) St2 in
  (st1, true)
;;

let next_blocks (cfg: cfg) (bb_id: int) : basic_block list =
  let remove_dup_successors acc s =
    if not (List.mem s acc) then s::acc else acc
  in
  List.filter (fun (s,t) -> s = bb_id) cfg.edges
  |> List.map snd
  |> List.fold_left remove_dup_successors []
  |> List.map (fun id -> List.find (fun b -> b.bb_id = id) cfg.blocks)
;;

(* worklist algorithm to infer stack types of basic blocks *)
let infer_block_types (c: context) (cfg: cfg) : stack_type IdMap.t =
  (* tymap contains preconditions for the first block, the precondition
   * are the types of the locals, which are assumed to be at the top of
   * the stack when the function is called *)
  let rec go bmap tymap = function
  | []    -> tymap
  | b::bs ->
    let process_next post next (tymap', worklist) = 
      if IdMap.mem next.bb_id tymap'
      (* compute the join of this block's postcondition with
       * the existing precondition *)
      then begin
        let next_pre = IdMap.find next.bb_id tymap' in
        let (join, not_changed) = compute_join next_pre post in
        (* only process the next block if its precondition changed *)
        if not_changed
        then (tymap', worklist)
        else (IdMap.add next.bb_id join tymap', worklist @ [next])
      end
      (* otherwise, if the next block doesn't have a precondition, set it as
       * this block's postcondition *)
      else (IdMap.add next.bb_id post tymap', worklist @ [next])
    in
    let pre = IdMap.find b.bb_id tymap in
    Printf.printf "bb_id: %d; pre: %s\n" b.bb_id (string_of_stack_type pre);
    let post = infer_block_type c pre b in
    let succs = next_blocks cfg b.bb_id in
    let (tymap', worklist) = List.fold_right (process_next post) succs (tymap, bs) in
    go bmap tymap' worklist
  in
  let add_block b acc = IdMap.add b.bb_id b acc in
  let bmap = List.fold_right add_block cfg.blocks IdMap.empty in
  let first_block = List.find (fun b -> b.bb_id = 1) cfg.blocks in
  let init_stack = List.rev c.locals in
  let tymap = IdMap.empty |> IdMap.add first_block.bb_id init_stack in
  go bmap tymap [first_block]
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

let print_tymap (tymap: stack_type IdMap.t) =
  Printf.printf "tymap\n";
  IdMap.iter begin fun id s ->
    Printf.printf "(%d, %s)\n" id (string_of_stack_type s)
  end tymap

let check_func (c : context) (f : func) =
  let {ftype; locals; body} = f.it in
  let FuncType (ins, out) = type_ c ftype in
  let c' = {c with locals = ins @ locals; results = out; labels = [out]} in

  let bb_tree = create_bb_tree body in
  print_bb_tree bb_tree;
  let cfg     = create_cfg bb_tree in
  print_cfg cfg;
  let tymap = infer_block_types c cfg in
  print_tymap tymap;

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

