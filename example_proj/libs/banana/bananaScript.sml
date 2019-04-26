open preamble basis;

val _ = new_theory "banana";

(* Replace by a translation extends call *)
require basis apple;

val _ = ml_prog_update (open_module "Banana");

val _ = (append_prog o process_topdecs) `
    fun banana x y = TextIO.print ((Int.toString (Apple.apple x y)) ^ "\n")
`;

val _ = ml_prog_update (close_module NONE);
val _ = export_theory ();
