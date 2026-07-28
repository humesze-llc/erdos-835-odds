/* Force-included (via /FI) into every MSVC translation unit.
 *
 * CaDiCaL is written for gcc/clang; this supplies the handful of builtins it
 * uses that MSVC spells differently. Kept separate from the <unistd.h> stub so
 * that "header the source asked for" and "compiler dialect gap" stay distinct.
 */
#ifndef S45_MSVC_COMPAT_H
#define S45_MSVC_COMPAT_H

#ifdef _MSC_VER

#include <xmmintrin.h>

/* propagate.cpp warms the watch list one iteration ahead. Real prefetch, not a
 * no-op: this sits in the innermost loop of the solver.
 *
 * gcc's third argument is temporal locality 0..3; _MM_HINT_T0/T1/T2/NTA is the
 * same ladder inverted, and the read/write hint has no MSVC counterpart.
 */
#define __builtin_prefetch(addr, ...) \
  _mm_prefetch ((const char *) (addr), _MM_HINT_T0)

/* reap.cpp (the radix heap) uses this to find a bucket index. Undefined for 0
 * in gcc as well, so the missing zero case is not a regression. */
#include <intrin.h>
static __forceinline int s45_builtin_clz (unsigned x) {
  unsigned long i;
  _BitScanReverse (&i, x);
  return 31 - (int) i;
}
#define __builtin_clz(x) s45_builtin_clz (x)

/* contract.cpp names the offending API call in its require/ensure messages. */
#define __PRETTY_FUNCTION__ __FUNCSIG__

#endif /* _MSC_VER */

#endif /* S45_MSVC_COMPAT_H */
