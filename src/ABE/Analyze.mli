open Eval
open ABE
open BoolForms
open Predicates

val abe_from_pp : public_parameters -> (module ABE)

val set_attributes : public_parameters -> attribute list -> generic_attribute

val get_setup_size : public_parameters -> int

val set_policy : public_parameters -> bool_formula -> generic_attribute
