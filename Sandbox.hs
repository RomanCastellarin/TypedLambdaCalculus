ST> :type (\x:(B->B) . (\y:(B->B).y)) I as (B -> B) -> B -> B
(B -> B) -> B -> B
ST> :type (\x:(B->B) . (\y:(B->B).y)) (I as (B -> B) -> B -> B)
Error de tipos: se esperaba (B -> B) -> B -> B, pero B -> B fue inferido.


queremos ?
infer' c e (First (Pair t _)) = infer' c e t

porque aceptaría
fst (5, "hola"/0) como un int


