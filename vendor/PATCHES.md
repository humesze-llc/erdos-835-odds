# Vendored CaDiCaL 2.1.3

Source: <https://github.com/arminbiere/cadical> tag `rel-2.1.3`, `src/` only.
Removed from the copy: `cadical.cpp` and `mobical.cpp` (both define `main`),
`ipasir.cpp` (plain-IPASIR C symbols we do not use), `testing.hpp`.

Built by `build.rs` with the `cc` crate under `--features cdcl`. Assertions are
**left enabled** — CaDiCaL's internal checks caught a real bug in our
propagator (see "reason clauses" in `src/s45/cdcl.rs`), and that is worth more
than the speed of `-DNDEBUG` until the search is trusted.

## Why a shim at all

`ccadical.h`, CaDiCaL's own C API, stops at plain IPASIR: it has no entry point
for `connect_external_propagator`. `vendor/shim/` supplies that surface as a
struct of function pointers, which is the shape Rust can cross FFI with.

## Source patches

One, in `src/cadical.hpp`:

* `CADICAL_ATTRIBUTE_FORMAT` expanded to `__attribute__((format(printf,…)))`
  unconditionally. MSVC has no `__attribute__`. Now guarded by `_MSC_VER`, with
  the original kept for every other compiler. The attribute only enables
  `printf`-style warnings, so dropping it changes no semantics.

Everything else is handled without touching vendored code:

* `vendor/compat/unistd.h` — the sources include `<unistd.h>` unconditionally
  (`internal.hpp:26`, `file.cpp:14`) even though the *features* behind it are
  already `_WIN32`-guarded. This stub maps `access`, `isatty`, `getpid`,
  `unlink`, `popen`/`pclose` and the `S_IS*` mode-bit macros to their MSVC
  spellings.
* `vendor/compat/msvc_compat.h` — force-included via `/FI`. Supplies
  `__builtin_prefetch` (as a real `_mm_prefetch`, since it sits in the solver's
  innermost loop), `__builtin_clz` (via `_BitScanReverse`), and
  `__PRETTY_FUNCTION__` (as `__FUNCSIG__`).
* `-D__WIN32` — CaDiCaL's Windows guards test `__WIN32`, a MinGW spelling MSVC
  does not predefine. Its `file.cpp` separately tests the standard `_WIN32`, so
  both spellings end up satisfied.
* `-DNBUILD` skips the generated `build.hpp` version banner; `-DNUNLOCKED`
  avoids `getc_unlocked`, which the MSVC CRT lacks.
* `psapi.lib` is linked for `GetProcessMemoryInfo` in `resources.cpp`.

## Upgrading

Drop a new `src/` in, re-apply the single `cadical.hpp` patch, and rebuild. The
compat headers are additive and version-independent; the `__WIN32` define is
the only thing likely to change, since it is arguably an upstream typo.
