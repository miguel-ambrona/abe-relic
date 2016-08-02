open BoolForms
open MakeAlgebra
       
type generic_attribute =
  | BoolForm_Policy of int * int * int * bool_formula
  | BoolForm_Attrs of int * int * attribute list
  | Discriminant of int * int * Zp.t list
  | GenericAttPair of generic_attribute * generic_attribute
