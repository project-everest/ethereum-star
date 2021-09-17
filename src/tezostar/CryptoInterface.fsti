module CryptoInterface
val signature : t:Type0{hasEq t}

val public_key : t:Type0{hasEq t}

val key_hash : t:Type0{hasEq t}

val pkey_of_b58check_exn : string -> public_key
val pkeyhash_of_b58check_exn : string -> key_hash
val public_key_hash : public_key -> key_hash
val parse_signature : string -> option signature
val check_signature : public_key -> signature -> string -> bool
val gen_keys: string -> public_key * key_hash
