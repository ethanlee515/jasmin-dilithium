require AllCore RealExp Matrix Real Distr.

import Real.RField.
import Real.
import RealExp.

op pi : real.

clone RealExp.Rn with type t <- int.
import Rn.

op continuous_normal_pdf(m : int, v : vector, sigma : real, x : vector) : real =
    (Real.RField.exp (inv (sqrt (2%r * pi * sigma * sigma))) m)
        * RealExp.exp (- norm (x - v) ^ 2 / (2%r * sigma * sigma)).

(* There seems to be no way of computing this *)
op discrete_normal_scaling(m : int, sigma : real) : real.

op discrete_normal_pdf(m : int, v : vector, sigma : real, x : vector) : real =
    (continuous_normal_pdf m v sigma x) / (discrete_normal_scaling m sigma).
    
op discrete_normal(m : int, v : vector, sigma : real) : vector distr.

axiom discrete_normal_1E :
    forall m v sigma x, Distr.mu1 (discrete_normal m v sigma) x = discrete_normal_pdf m v sigma x.

