open PredEnc

val make_BF_PredEnc : int -> (module PredEnc)

val make_InnerProduct_PredEnc : int -> (module PredEnc)

val make_BroadcastEnc_PredEnc : int -> int -> (module PredEnc)

val make_ArithmeticSpanProgram_PredEnc : int -> int -> (module PredEnc)

val make_Fast_ArithmeticSpanProgram_PredEnc : int -> int -> (module PredEnc)
