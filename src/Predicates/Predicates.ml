open BoolForms
open MakeAlgebra

type generic_attribute =
  | BoolForm_Policy of int * int * int * bool_formula
  | BoolForm_Attrs of int * int * attribute list
  | Discriminant of int * int * Zp.t list
  | InnerProduct of int * Zp.t list
  | BroadcastEncVector of int * int * bool list
  | BroadcastEncIndex of int * int * (int * int)
  | GenericAttPair of generic_attribute * generic_attribute


