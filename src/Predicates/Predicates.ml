open BoolForms

type generic_attribute =
  | BoolForm_Policy of int * int * bool_formula
  | BoolForm_Attrs of int * int * attribute list
