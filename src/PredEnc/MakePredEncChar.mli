open PredEnc

val make_BF_PredEnc_Characterization : ?simplify:bool -> int -> int -> int -> (module PredEnc_Characterization)

val make_ShareRoot_PredEnc_Characterization : int -> int -> (module PredEnc_Characterization)

val make_BroadcastEnc_Characterization : int -> int -> (module PredEnc_Characterization)
