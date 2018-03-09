type sexpr = Atom of string | Node of string * sexpr list

val output : out_channel -> int -> sexpr -> unit
val print : int -> sexpr -> unit
val to_string : int -> sexpr -> string
val to_string_mach : int -> sexpr -> string
