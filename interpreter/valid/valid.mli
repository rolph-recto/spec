exception Invalid of Source.region * string

val check_module : Ast.module_ -> unit (* raises Invalid *)

val check_module_italx : Ast.module_ -> unit (* raises Invalid *)

val example_module : Ast.module_ (* raises Invalid *)
