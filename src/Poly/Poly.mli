open AlgebraInterfaces
open PolyInterfaces

module MakePoly (V : Var) (C : Field) : Poly with type var = V.t and type coeff = C.t
