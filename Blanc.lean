import «Blanc».Weth

partial def Bytes.chunks (bs : Bytes) : List Bytes :=
  match bs.splitAt 32 with
  | (_, []) => [bs]
  | (bs', bs'') => bs' :: chunks bs''

def WethByteCode : String :=
  List.foldr
     (λ s0 s1 => s0 ++ "\n" ++ s1)
     "" <| List.map Bytes.toHexString
        <| Bytes.chunks <| Option.getD weth'.compile []

def main : IO Unit := IO.println WethByteCode
