## `numeric-sort`

A zero-allocation, human-readable sorting library.

This library provides convenient ways to compare or sort strings and keep numeric components in proper numerical order.
For instance `"test-7"` will come before `"test-10"`, contrary to traditional lexicographic comparison of characters.

The primary functions of interest are [`cmp`], [`sort`], and [`sort_unstable`].

## `no-std`

`numeric-sort` is compatible with `no-std` projects out of the box.

However, by default we link to `alloc` in order to support [`sort`] (stable sorts require allocations).
To prevent this, you can disable the default `alloc` feature, which will disable [`sort`] but leave all other functions still available.

```toml
[dependencies]
numeric-sort = { version = "...", default-features = false }
```
