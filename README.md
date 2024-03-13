## `numeric-sort`

A zero-allocation, human-readable sorting library.

This library provides convenient ways to compare or sort strings and keep numeric components in proper numerical order.
For instance `"test-7"` will come before `"test-10"`, contrary to traditional lexicographic comparison of characters.

The primary functions of interest are [`sort`] and [`cmp`].

## `no-std`

`numeric-sort` is compatible with `no-std` projects out of the box.

However, because `[T]::sort_by` is not in-place (i.e., it must allocate memory), we by default link to `alloc` to support our [`sort`] convenience function.
To prevent this, you may disable the default `alloc` feature:

```toml
[dependencies]
numeric-sort = { version = "...", default-features = false }
```

When `alloc` is disabled, you still have access to [`cmp`], which can be used with your choice of non-allocating sorting libraries.
