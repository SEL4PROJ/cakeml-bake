(*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)
open preamble basis;

val _ = new_theory "targetInfo";

require basisProg;

val _ = ml_prog_update (open_module "TargetInfo");

val _ = (append_prog o process_topdecs) `
    fun word_size_bytes u = {{ word_size_bytes }}

    fun word_size_bits u = {{ word_size_bits }}

    fun name u = "{{ target_name }}"
`;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
