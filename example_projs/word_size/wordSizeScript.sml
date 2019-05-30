(* Simple program to print the word size *)
open preamble basis targetInfoTheory;

val _ = new_theory "wordSize";

require targetInfo;

val _ = (append_prog o process_topdecs) `
    fun main u = TextIO.print (Int.toString (TargetInfo.word_size_bits ()) ^ "\n")
`;

val _ = export_theory ();
