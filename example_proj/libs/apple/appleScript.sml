open preamble basis;

val _ = new_theory "apple";

(* Replace by a translation extends call *)
require basisProg;

val _ = ml_prog_update (open_module "Apple");

val _ = (append_prog o process_topdecs) `
    fun apple x y = x + y
`;

val _ = ml_prog_update (close_module NONE);
val _ = export_theory ();
