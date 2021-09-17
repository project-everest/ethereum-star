type public_key
type key_hash

val pkey_of_b58check_exn : string -> public_key
val pkeyhash_of_b58check_exn : string -> key_hash
val public_key_hash : public_key -> key_hash
type signature
val parse_signature: string -> signature option
val check_signature : public_key -> signature -> string -> bool
val gen_keys: string -> public_key * key_hash
