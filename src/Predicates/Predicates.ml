open BoolForms

type generic_attribute =
  | BoolForm_Policy of int * int * int * bool_formula
  | BoolForm_Attrs of int * int * attribute list
  | GenericAttPair of generic_attribute * generic_attribute
