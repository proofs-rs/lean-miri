// Linux x86-64 diagnostic CPU sampling, without perf_event permissions.
// Records monotonic time, interrupted PCs, thread IDs and optional caller PCs.
// Symbol lookup is offline. Optional libunwind mode records local caller PCs.
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/time.h>
#include <time.h>
#include <ucontext.h>
#include <unistd.h>
#ifdef WITH_LIBUNWIND
#define UNW_LOCAL_ONLY
#include <libunwind.h>
#define CALLERS 32
#else
#define CALLERS 0
#endif

static int output = -1;
static void sample(int signal, siginfo_t *info, void *context) {
    (void)signal;
    (void)info;
    int saved_errno = errno;
    struct timespec now;
    if (clock_gettime(CLOCK_MONOTONIC, &now) == 0) {
        ucontext_t *state = context;
        uint64_t row[3 + CALLERS] = {
            (uint64_t)now.tv_sec * 1000000000 + (uint64_t)now.tv_nsec,
            (uint64_t)state->uc_mcontext.gregs[REG_RIP],
            (uint64_t)syscall(SYS_gettid)
        };
#ifdef WITH_LIBUNWIND
        unw_cursor_t cursor;
        if (unw_init_local2(&cursor, (unw_context_t *)context, UNW_INIT_SIGNAL_FRAME) == 0) {
            for (unsigned i = 0; i < CALLERS && unw_step(&cursor) > 0; ++i) {
                unw_word_t pc;
                if (unw_get_reg(&cursor, UNW_REG_IP, &pc) != 0) break;
                row[3 + i] = pc;
            }
        }
#endif
        // A truncated record is rejected by the offline summarizer.
        (void)write(output, row, sizeof(row));
    }
    errno = saved_errno;
}

__attribute__((constructor)) static void start(void) {
    const char *target = getenv("LEAN_MIRI_SAMPLE_EXE");
    const char *prefix = getenv("LEAN_MIRI_SAMPLE_OUTPUT");
    char executable[PATH_MAX], path[PATH_MAX];
    if (!target || !prefix) return;
    ssize_t length = readlink("/proc/self/exe", executable, sizeof(executable)-1);
    if (length < 0) _exit(86);
    executable[length] = 0;
    // Child version probes must not overwrite the main executable's samples.
    if (strcmp(executable, target)) return;
    size_t n = strlen(prefix);
    if (n + 9 >= sizeof(path)) _exit(86);
    memcpy(path, prefix, n);
    strcpy(path+n, ".maps");
    int maps = open("/proc/self/maps", O_RDONLY | O_CLOEXEC);
    int copy = open(path, O_WRONLY | O_CREAT | O_TRUNC | O_CLOEXEC, 0600);
    if (maps < 0 || copy < 0) _exit(86);
    char block[4096];
    while ((length = read(maps, block, sizeof(block))) > 0)
        if (write(copy, block, length) != length) _exit(86);
    close(maps);
    close(copy);
    strcpy(path+n, ".samples");
    output = open(path, O_WRONLY | O_CREAT | O_TRUNC | O_APPEND | O_CLOEXEC, 0600);
    if (output < 0) _exit(86);
    struct sigaction action = {0};
    action.sa_sigaction = sample;
    action.sa_flags = SA_SIGINFO | SA_RESTART;
    sigemptyset(&action.sa_mask);
    if (sigaction(SIGPROF, &action, NULL)) _exit(86);
    struct itimerval timer = { .it_interval = {0, 4000}, .it_value = {0, 4000} };
    if (setitimer(ITIMER_PROF, &timer, NULL)) _exit(86);
}
