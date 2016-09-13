open Predicates
open AlgStructures
open DualSystemGInterface
open PredEnc
open PairEnc

module type ABE =
  sig
    type mpk
    type msk
    type x
    type y
    type msg
    type sk
    type ct

    val setup  : unit -> mpk * msk
    val enc    : mpk -> x -> msg -> ct
    val keyGen : mpk -> msk -> y -> sk
    val dec    : mpk -> sk -> ct -> msg

    val rand_msg : unit -> msg

    val set_x : generic_attribute -> x
    val set_y : generic_attribute -> y

    val string_of_mpk : mpk -> string
    val string_of_msk : msk -> string
    val string_of_sk  : sk  -> string
    val string_of_ct  : ct  -> string
    val string_of_msg : msg -> string

    val mpk_of_string : string -> mpk
    val msk_of_string : string -> msk
    val sk_of_string  : string -> sk
    val ct_of_string  : string -> ct
    val msg_of_string : string -> msg
end


module PredEncABE : functor (B : BilinearGroup) (DSG: DualSystemGroup) (PE : PredEnc) ->
                    ABE with
                      type mpk = DSG(B).pp * DSG(B).img_mu and
                      type msk = B.G2.t and
                      type x   = PE(B).x and
                      type y   = PE(B).y and
                      type msg = B.Gt.t and
                      type sk  = (B.G2.t * B.G2.t list) * PE(B).y and
                      type ct  = (B.G1.t * B.G1.t list * B.Gt.t) * PE(B).x


module PairEncABE : functor (B : BilinearGroup) (DSG: DualSystemGroup) (PE : PairEnc) ->
                    ABE with
                      type mpk = DSG(B).pp * DSG(B).img_mu and
                      type msk = B.G2.t and
                      type x   = PE.x and
                      type y   = PE.y and
                      type msg = B.Gt.t and
                      type sk  = (B.G2.t list) * PE.y and
                      type ct  = (B.G1.t list * B.Gt.t) * PE.x
