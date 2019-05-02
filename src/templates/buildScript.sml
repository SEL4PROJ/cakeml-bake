open preamble basis {{ terminal_module }}Theory;

val _ = new_theory "build";
val _ = translation_extends "{{ terminal_module }}";
val st = ml_translatorLib.get_ml_prog_state();
val maincall =
  ``Dlet unknown_loc (Pcon NONE []) (App Opapp [Var (Short "{{ entry_function }}"); Con NONE []])``;
val prog = ``SNOC ^maincall ^(get_thm st |> concl |> rator |> rator |> rator |> rand)``
           |> EVAL |> concl |> rhs;
val _ = astToSexprLib.write_ast_to_file "{{ sexpr_file }}" prog;
val _ = export_theory ();
