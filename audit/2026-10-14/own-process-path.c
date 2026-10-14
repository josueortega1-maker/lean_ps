#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <unistd.h>

/* Compatibility only: this runtime exposes our executable at /proc/self/exe,
 * but not at /proc/<our numeric pid>/exe. Other paths are passed unchanged. */
ssize_t readlink(const char *path, char *buffer, size_t size) {
    static ssize_t (*original)(const char *, char *, size_t) = NULL;
    char own_path[64];
    if (original == NULL)
        original = dlsym(RTLD_NEXT, "readlink");
    snprintf(own_path, sizeof own_path, "/proc/%ld/exe", (long)getpid());
    if (strcmp(path, own_path) == 0)
        path = "/proc/self/exe";
    return original(path, buffer, size);
}
