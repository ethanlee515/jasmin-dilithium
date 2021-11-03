require AllCore RealExp Matrix Real Distr Int List. require import DInterval.

require import IntDiv.
require import Int.
require import Distr.

require ZModP.

op m : int.
op d : int.
op k : int.
op n : int.
op kappa : int.
op sigma : real.
op rej_sample_M : real.
op q : int.
axiom prime_q: prime q.
clone ZModP.ZModRing as ZModQ with op p = q.

op centered_asint(x : ZModQ.zmod) : int =
    let ix = ZModQ.asint x in
    if q %/ 2 < ix then ix - q else ix.

require VarMatrix.
clone import VarMatrix as MatModQ with type ZR.t = ZModQ.zmod.

(* -- Discrete Gaussians -- *)

import Real.RField.
import RealExp.

require import Real.

op pi : real.

op continuous_normal_pdf(v : varMatrix, x : varMatrix) : real =
    (Real.RField.exp (inv (sqrt (2%r * pi * sigma * sigma))) m)
        * RealExp.exp (- (centered_asint (dotp (x + (-v)) (x + (-v))))%r / (2%r * sigma * sigma)).

(* There seems to be no way of computing this *)
op discrete_normal_scaling : real.

op discrete_normal_pdf(v : varMatrix, x : varMatrix) : real =
    (continuous_normal_pdf v x) / discrete_normal_scaling.
    
op discrete_normal(v : varMatrix) : varMatrix distr.

axiom discrete_normal_1E :
    forall v x, Distr.mu1 (discrete_normal v) x = discrete_normal_pdf v x.

(* -- Other misc. building blocks -- *)

op sk_entry_dist : int distr.
axiom sk_entry_supp: forall x, -d <= x <= d <=> support sk_entry_dist x.
axiom sk_entry_unif: is_uniform sk_entry_dist.
axiom sk_entry_ll: is_lossless sk_entry_dist.
op sk_dist : varMatrix distr = dVarMatrix m k (dmap sk_entry_dist ZModQ.inzmod).

op a_entry_dist : ZModQ.zmod distr.
axiom a_entry_funif: is_funiform a_entry_dist.
axiom a_entry_ll: is_lossless a_entry_dist.
op a_dist : varMatrix distr = dVarMatrix n m a_entry_dist.

op c_dist : varMatrix distr.
axiom c_shape: forall c, support c_dist c <=> getDims c = (k, 1).
axiom c_norm: forall c, support c_dist c <=> ZModQ.asint (dotp c c) <= kappa.
axiom c_elem: forall c, support c_dist c <=> (forall ij, -1 <= centered_asint c.[ij] <= 1).
axiom c_dist_unif: is_uniform c_dist.
axiom c_dist_ll: is_lossless c_dist.

type message.

op zero_vec = MatModQ.buildVarMat m 1 (ZModQ.inzmod 0).

op isdone_dist(sc : varMatrix, z : varMatrix) : bool distr.

(* Is there a library function for this? *)
op min_real (a b : real) : real = if a < b then a else b.

axiom isdone_dist_1E :
    forall z sc, Distr.mu1 (isdone_dist sc z) true =
        min_real 1%r ((discrete_normal_pdf zero_vec z)  / (rej_sample_M * (discrete_normal_pdf sc z) )).

(* -- Building Lyu12 -- *)

module Lyu12 = {
    proc keygen() : varMatrix * varMatrix * varMatrix = {
        var a, s, t;
        a <$ a_dist;
        s <$ sk_dist;
        t <- a * s;
        return (a, s, t);
    }
    
    proc sign(msg : message, a : varMatrix, s : varMatrix) : varMatrix * varMatrix = {
        var y, c, z;
        var is_done;
        is_done <- false;

        while(! is_done) {
            y <$ discrete_normal zero_vec;
            c <$ c_dist;
            z <- s * c + y;
            is_done <$ isdone_dist (s * c) z;
        }

        return (z, c);
    }
}.
