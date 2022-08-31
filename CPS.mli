(* Through a CPS transformation, the surface language [Lambda] is translated
   down to the intermediate language [Tail]. *)

module TL = TypeLambda
module T = Tail

val cps_block : TL.term -> T.block
val cps_prog : TL.program -> T.program
