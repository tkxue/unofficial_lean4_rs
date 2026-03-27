/// MurmurHash2 64-bit, by Austin Appleby.
/// Matches Lean 4 C++ `MurmurHash64A` in src/runtime/hash.cpp.
pub fn murmur_hash_64a(key: &[u8], seed: u64) -> u64 {
    const M: u64 = 0xc6a4a7935bd1e995;
    const R: u32 = 47;

    let len = key.len();
    let mut h: u64 = seed ^ ((len as u64).wrapping_mul(M));

    // Process 8-byte chunks
    let chunks = len / 8;
    for i in 0..chunks {
        let mut k: u64 = u64::from_le_bytes(key[i * 8..i * 8 + 8].try_into().unwrap());
        k = k.wrapping_mul(M);
        k ^= k >> R;
        k = k.wrapping_mul(M);
        h ^= k;
        h = h.wrapping_mul(M);
    }

    // Process remaining bytes (fallthrough via match without break)
    let tail = &key[chunks * 8..];
    let rem = len & 7;
    if rem >= 7 { h ^= (tail[6] as u64) << 48; }
    if rem >= 6 { h ^= (tail[5] as u64) << 40; }
    if rem >= 5 { h ^= (tail[4] as u64) << 32; }
    if rem >= 4 { h ^= (tail[3] as u64) << 24; }
    if rem >= 3 { h ^= (tail[2] as u64) << 16; }
    if rem >= 2 { h ^= (tail[1] as u64) << 8; }
    if rem >= 1 {
        h ^= tail[0] as u64;
        h = h.wrapping_mul(M);
    }

    h ^= h >> R;
    h = h.wrapping_mul(M);
    h ^= h >> R;
    h
}

/// Lean's `hash_str`: MurmurHash2 with a given init value.
/// `lean_string_hash` calls this with init_value=11.
#[inline]
pub fn hash_str(data: &[u8], init_value: u64) -> u64 {
    murmur_hash_64a(data, init_value)
}

/// Lean's `mixHash` / `lean_uint64_mix_hash`.
/// Used to combine hashes for compound structures (Name, Level, Expr).
#[inline]
pub fn mix_hash(mut h: u64, mut k: u64) -> u64 {
    const M: u64 = 0xc6a4a7935bd1e995;
    const R: u32 = 47;
    k = k.wrapping_mul(M);
    k ^= k >> R;
    k ^= M;
    h ^= k;
    h = h.wrapping_mul(M);
    h
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_hash_str_empty() {
        // hash_str(0, "", 11) should produce a deterministic value
        let h = hash_str(b"", 11);
        assert_ne!(h, 0);
    }

    #[test]
    fn test_mix_hash_known() {
        // mixHash(1723, hash_str("Nat", 11)) must be deterministic
        let s = hash_str(b"Nat", 11);
        let m = mix_hash(1723, s);
        assert_ne!(m, 0);
        // Same inputs must produce same output
        assert_eq!(m, mix_hash(1723, hash_str(b"Nat", 11)));
    }

    #[test]
    fn test_murmur_short_strings() {
        // Different short strings must produce different hashes
        let h1 = hash_str(b"a", 11);
        let h2 = hash_str(b"b", 11);
        let h3 = hash_str(b"ab", 11);
        assert_ne!(h1, h2);
        assert_ne!(h1, h3);
        assert_ne!(h2, h3);
    }

    #[test]
    fn test_murmur_8byte_boundary() {
        // Test strings at and around 8-byte boundary
        let h7 = hash_str(b"1234567", 11);
        let h8 = hash_str(b"12345678", 11);
        let h9 = hash_str(b"123456789", 11);
        assert_ne!(h7, h8);
        assert_ne!(h8, h9);
    }
}
