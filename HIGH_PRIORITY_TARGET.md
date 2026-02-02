# High-Priority Struct Packing Target: euf::enode

## Summary

User confirmed benchmarks show no measurable difference for config struct changes (as predicted). Removed all benchmark infrastructure per request. Now focusing on high-priority targets.

## Primary Target: euf::enode

**Location**: `src/ast/euf/euf_enode.h` lines 40-69

**Why High Priority:**
1. **Frequently instantiated** - One enode per term in SMT problems (thousands to millions)
2. **Hot path** - Accessed constantly during solving (equality reasoning, congruence closure)
3. **Not a config struct** - Core data structure, not singleton configuration

**Current Layout Issues:**
```cpp
class enode {
    expr*         m_expr = nullptr;           // 8 bytes
    bool          m_mark1 = false;            // 1 byte + 7 padding
    bool          m_mark2 = false;            // 1 byte + 7 padding
    bool          m_mark3 = false;            // 1 byte + 7 padding
    bool          m_commutative = false;      // 1 byte + 7 padding
    bool          m_interpreted = false;      // 1 byte + 7 padding
    bool          m_cgc_enabled = true;       // 1 byte + 7 padding
    bool          m_merge_tf_enabled = false; // 1 byte + 7 padding
    bool          m_is_equality = false;      // 1 byte + 7 padding
    bool          m_is_relevant = false;      // 1 byte + 7 padding
    lbool         m_is_shared = l_undef;      // 1 byte + 7 padding
    lbool         m_value = l_undef;          // 1 byte + 7 padding
    sat::bool_var m_bool_var = ...;           // 4 bytes
    unsigned      m_class_size = 1;           // 4 bytes
    unsigned      m_table_id = UINT_MAX;      // 4 bytes
    unsigned      m_generation = 0;           // 4 bytes
    // ... more fields
};
```

**Problems:**
- 9 bool fields scattered = ~9 bytes + ~63 bytes padding = 72 bytes wasted
- 2 lbool fields (1 byte each) = ~2 bytes + ~14 bytes padding = 16 bytes wasted
- **Total waste: ~88 bytes per enode**

**Optimization Opportunity:**
Pack all 11 boolean/lbool fields into bitfields:
- 9 bools → 9 bits
- 2 lbools (2 bits each) → 4 bits
- Total: 13 bits = 2 bytes instead of 88 bytes
- **Potential savings: 86 bytes per enode**

For a problem with 100,000 enodes: **8.6 MB savings**
For a problem with 1,000,000 enodes: **86 MB savings**

## Verification

**No reference access required:**
- Checked for `flet` usage - none found
- All fields accessed by value
- Safe to convert to bitfields

## Next Steps

1. Optimize enode struct field ordering and bitfield packing
2. Verify no performance regression
3. Measure actual memory impact on real problems

This is a genuine high-priority optimization target unlike config structs.
