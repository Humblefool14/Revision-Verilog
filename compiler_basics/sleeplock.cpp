#ifndef SLEEPLOCK_H
#define SLEEPLOCK_H

#include <stdint.h>
#include <stdbool.h>

// Assume we have a spinlock implementation
#include "spinlock.h"

// Long-term locks for processes
struct sleeplock {
    uint32_t locked;       // Is the lock held?
    struct spinlock spinlk;    // spinlock protecting this sleep lock
    
    // For debugging:
    char *name;            // Name of lock.
    int pid;               // Process holding lock
};

// Function prototypes
void initsleeplock(struct sleeplock *slk, char *name);
void acquiresleep(struct sleeplock *slk);
void releasesleep(struct sleeplock *slk);
bool holdingsleep(struct sleeplock *slk);

// Function implementations

void initsleeplock(struct sleeplock *slk, char *name) {
    initspinlock(&slk->spinlk, "sleep lock");
    slk->name = name;
    slk->locked = 0;
    slk->pid = 0;
}

void acquiresleep(struct sleeplock *slk) {
    acquirespinlock(&slk->spinlk);
    while (slk->locked) {
        sleep(slk, &slk->spinlk);
    }
    slk->locked = 1;
    slk->pid = myproc()->pid;
    releasespinlock(&slk->spinlk);
}

void releasesleep(struct sleeplock *slk) {
    acquirespinlock(&slk->spinlk);
    slk->locked = 0;
    slk->pid = 0;
    wakeup(slk);
    releasespinlock(&slk->spinlk);
}

bool holdingsleep(struct sleeplock *slk) {
    bool ret;
    acquirespinlock(&slk->spinlk);
    ret = (slk->locked && slk->pid == myproc()->pid);
    releasespinlock(&slk->spinlk);
    return ret;
}

#endif // SLEEPLOCK_H