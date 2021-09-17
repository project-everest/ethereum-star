open Client_embedded_proto_alpha

(* open Client_embedded_proto_genesis.Local_environment *)
type public_key = Environment.Ed25519.Public_key.t
let pkey_of_b58check_exn (s:string) : public_key = Environment.Ed25519.Public_key.of_b58check_exn s

open Client_embedded_proto_alpha.Local_environment.Environment

type key_hash = Local_environment.Environment.Ed25519.Public_key_hash.t

let public_key_hash key : key_hash = Ed25519.Public_key.hash key

let pkeyhash_of_b58check_exn x = Local_environment.Environment.Ed25519.Public_key_hash.of_b58check_exn x

type signature = Ed25519.Signature.t

let parse_signature (s:string) =
  Data_encoding.Binary.of_bytes Ed25519.Signature.encoding
                  (MBytes.of_string (Hex_encode.hex_decode s))

let check_signature key signature (message:string) =
      let message = MBytes.of_string message in
      Ed25519.Signature.check key signature message

let gen_keys s =
  (* let of_hex s =      *)
  (*   Hex_encode.hex_decode s *)
  (*   |> Bytes.of_string *)
  (*   |> Sodium.Sign.Bytes.to_seed in *)
  let generate () =     Sodium.Random.Bytes.generate Sodium.Sign.seed_size
    |> Sodium.Sign.Bytes.to_seed
in
  let secret_key, public_key = Sodium.Sign.seed_keypair (generate()) in
      public_key, Ed25519.Public_key.hash public_key
