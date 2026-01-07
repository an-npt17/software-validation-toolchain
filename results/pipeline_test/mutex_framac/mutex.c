/* Mutex implementation in C with ACSL */
#include <stdbool.h>

int lock = 0;
int critical_count = 0;

/*@ predicate mutex_invariant = (critical_count <= 1);
  @ predicate lock_valid = (lock == 0 || lock == 1);
  @*/

/*@
  @ requires lock_valid;
  @ requires mutex_invariant;
  @ ensures lock_valid;
  @ ensures mutex_invariant;
  @ assigns lock, critical_count;
  @*/
void acquire_lock(void) {
    /*@ loop invariant lock_valid;
      @ loop assigns lock;
      @*/
    while (lock != 0) {
        /* busy wait */
    }
    lock = 1;
}

/*@
  @ requires lock_valid;
  @ requires lock == 1;
  @ ensures lock_valid;
  @ ensures lock == 0;
  @ assigns lock;
  @*/
void release_lock(void) {
    lock = 0;
}

/*@
  @ requires mutex_invariant;
  @ requires lock_valid;
  @ ensures mutex_invariant;
  @ ensures lock_valid;
  @ assigns lock, critical_count;
  @*/
void enter_critical_section(void) {
    acquire_lock();
    critical_count++;
    /*@ assert critical_count == 1; */ // Mutual exclusion
}

/*@
  @ requires mutex_invariant;
  @ requires critical_count == 1;
  @ ensures mutex_invariant;
  @ ensures critical_count == 0;
  @ assigns critical_count, lock;
  @*/
void leave_critical_section(void) {
    critical_count--;
    /*@ assert critical_count == 0; */
    release_lock();
}
