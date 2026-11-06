#define _GNU_SOURCE
#include <dlfcn.h>
#include <errno.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

/* Executor-specific portability fix. Only the current process's numeric
 * /proc/PID/exe lookup is mapped to /proc/self/exe. Lean is not modified. */
ssize_t readlink(const char *path, char *buffer, size_t size) {
    typedef ssize_t (*readlink_function)(const char *, char *, size_t);
    static readlink_function original;
    if (!original) {
        original = (readlink_function)dlsym(RTLD_NEXT, "readlink");
        if (!original) {
            errno = ENOSYS;
            return -1;
        }
    }
    char expected[64];
    snprintf(expected, sizeof(expected), "/proc/%ld/exe", (long)getpid());
    if (strcmp(path, expected) == 0) {
        return original("/proc/self/exe", buffer, size);
    }
    return original(path, buffer, size);
}
