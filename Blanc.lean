import «Blanc».Weth

partial def Bytes.chunks (bs : Bytes) : List Bytes :=
  match bs.splitAt 32 with
  | (_, []) => [bs]
  | (bs', bs'') => bs' :: chunks bs''

def Bytes.toHexString (bs : Bytes) : String :=
  "hex\"" ++ List.foldr (λ b s => b.toString ++ s) "\"" bs

def WethByteCode : String :=
  List.foldr
     (λ s0 s1 => s0 ++ "\n" ++ s1)
     "" <| List.map Bytes.toHexString (Option.getD weth.compile []).chunks

def main : IO Unit :=
  IO.println WethByteCode
