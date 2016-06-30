open Core_kernel.Std

module F = Format
module L = List
module S = String
module R = Relic
module Char = Char

let optional ~d v = Option.value ~default:d v

let fixme s = failwith ("FIXME: "^s)
