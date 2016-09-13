open PredEnc

module PredEnc_from_Characterization : functor (C : PredEnc_Characterization) -> PredEnc

module Disjunction_Characterization : functor
  (C1 : PredEnc_Characterization) (C2 : PredEnc_Characterization) -> PredEnc_Characterization

module Conjunction_Characterization : functor
  (C1 : PredEnc_Characterization) (C2 : PredEnc_Characterization) -> PredEnc_Characterization

module Negation_Characterization : functor (C : PredEnc_Characterization) -> PredEnc_Characterization

module Dual_Characterization : functor (C : PredEnc_Characterization) -> PredEnc_Characterization
