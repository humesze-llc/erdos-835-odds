/* Minimal <unistd.h> stand-in for MSVC.
 *
 * CaDiCaL 2.1.3 carries Windows guards for the POSIX *features* it uses
 * (getrusage, sigalrm, fork), but `internal.hpp` and `file.cpp` include
 * <unistd.h> unconditionally.  Rather than patch vendored sources we put this
 * on the include path ahead of them.  Only the names CaDiCaL actually calls
 * are mapped; anything else stays undefined so a missing case is a compile
 * error rather than silent breakage.
 */
#ifndef S45_COMPAT_UNISTD_H
#define S45_COMPAT_UNISTD_H

#ifdef _MSC_VER

#include <io.h>
#include <process.h>
#include <stdio.h>
#include <sys/stat.h>

#ifndef R_OK
#define R_OK 4
#define W_OK 2
#define X_OK 0
#define F_OK 0
#endif

#define access _access
#define isatty _isatty
#define getpid _getpid
#define unlink _unlink

/* file.cpp probes the mode bits and shells out for compressed inputs. The
 * pipe path is unreachable here -- s45 never hands CaDiCaL a filename -- but
 * it still has to compile. */
#ifndef S_ISDIR
#define S_ISDIR(m) (((m) & _S_IFMT) == _S_IFDIR)
#endif
#ifndef S_ISFIFO
#define S_ISFIFO(m) (((m) & _S_IFMT) == _S_IFIFO)
#endif
#define popen _popen
#define pclose _pclose

#endif /* _MSC_VER */

#endif /* S45_COMPAT_UNISTD_H */
