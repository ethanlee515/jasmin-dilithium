require AllCore RealExp Matrix Real Distr Int List.
require import DInterval.

import Real.RField.
import Real.
import RealExp.
import List.
import Int.

require import ZModP.

op pi : real.
op m : int.

op q : int.

require import IntDiv.

print Subtype.

(* Attempt 2 *)
clone import Subtype as Mod11 with
    type T <= int,
    type sT <= int, (* Required for insub to be well-defined *)
    pred P <= fun x => 0 <= x < 11,
    op insub <= fun x => if 0 <= x < 11 then Some x else None
proof *.
    realize insubN by smt().
    (* valP: forall (x : int), 0 <= x && x < 11 *)
    (* Clearly not even true *)

(* Attempt 1 *)
clone import Subtype as Mod11 with
    type T <= int,
    pred P <= fun x => 0 <= x < 11
proof *.
    realize insubN.
    print insub.
    (* insub not defined, not enough information to prove this *)

    
    type sT <= int,

axiom eleven_is_prime:
    IntDiv.prime 11.

clone import ZModField as IntMod11 with
    op p <= 11
proof *.
    realize prime_p by apply eleven_is_prime.
    realize Sub.insubN.
        move => x x_bound.
        print insub.
        print zmod.

    


axiom q_is_prime:
    IntDiv.prime q.


clone import ZModField as IntModQ with
    op p <= q
proof *.
    realize prime_p.
        apply q_is_prime.
    qed.
    realize Sub.insubN.
        move => x x_bound.
        print insub.




    
    




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

import Int.

pred intIsUnit(x : int) = (x = 1) || (x = -1).
op intInvr(x : int) = x.

clone import Matrix as Matrix_ with
    type ZR.t <= int,
    op ZR.zeror <= 0,
    op ZR.oner <= 1,
    op ZR.(+) <= Int.(+),
    op ZR.([-]) <= Int.([-]),
    op ZR.( * ) <= Int.( * ),
    op ZR.invr <= intInvr,
    pred ZR.unit <= intIsUnit
proof ZR.*.
    realize ZR.addrA by smt().
    realize ZR.addrC by smt().
    realize ZR.add0r by smt().
    realize ZR.addNr by smt().
    realize ZR.oner_neq0 by smt().
    realize ZR.mulrA by smt().
    realize ZR.mulrC by smt().
    realize ZR.mul1r by smt().
    realize ZR.mulrDl by smt().
    realize ZR.mulVr by smt().
    realize ZR.unitP by smt().
    realize ZR.unitout by smt().
    realize ZR.mulf_eq0 by smt().
    
clone import Matrix as Matrix_modQ with
    type ZR.t <= 



print matrix.
print Matrix.matrix.

module Lyu12 = {
    proc keygen() : int = {
        

    }

}.
