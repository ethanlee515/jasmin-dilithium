theory VarMatrix.

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

end VarMatrix.
