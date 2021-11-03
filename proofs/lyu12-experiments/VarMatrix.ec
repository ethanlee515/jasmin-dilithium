require Ring.
clone import Ring.IDomain as ZR.

type R = t.

type varMatrix.

op tofunm : varMatrix -> int * int * (int -> int -> R).
op offunm : int * int * (int -> int -> R) -> varMatrix.

op "_.[_]" (m : varMatrix) (ij : int * int) = (tofunm m).`3 ij.`1 ij.`2.

op [-] (m : varMatrix) : varMatrix.

op (+) (m1 m2 : varMatrix) : varMatrix.
op (-) (m1 m2 : varMatrix) : varMatrix.
op ( * ) (m1 m2 : varMatrix) : varMatrix.

op buildVarMat (dim1 dim2 : int, val: t) : varMatrix.

(* I don't understand how this is built *)
op dVarMatrix (dim1 dim2 : int, val: R distr) : varMatrix distr.

op getDims(m : varMatrix) = ((tofunm m).`1, (tofunm m).`2).

require Bigalg.
clone import Bigalg.BigComRing as Big with theory CR <- ZR.
import BAdd.

op dotp (v1 v2 : varMatrix) =
    bigi predT (fun i => v1.[0, i] * v2.[0, i]) 0 (getDims v1).`2.
