"""Example formal models for testing without API calls."""

from src.types import ACSLSpecification, PromelaModel

# Mutex example - deliberately has potential for deadlock
MUTEX_PROMELA = PromelaModel(
    source_code="""/* Mutex with two processes - Potential Deadlock */
byte lock = 0;
byte critical = 0;

active proctype Process0() {
    do
    :: atomic {
        lock == 0;
        lock = 1;
        critical++;
        assert(critical == 1); /* Mutual exclusion */
        critical--;
        lock = 0;
    }
    od
}

active proctype Process1() {
    do
    :: atomic {
        lock == 0;
        lock = 1;
        critical++;
        assert(critical == 1); /* Mutual exclusion */
        critical--;
        lock = 0;
    }
    od
}

/* LTL Properties */
ltl mutex { [] (critical <= 1) }
ltl progress { []<> (critical == 1) }
""",
    ltl_properties=[
        "[] (critical <= 1)",  # Mutual exclusion
        "[]<> (critical == 1)",  # Progress - at least one process eventually enters
    ],
    description="Simple mutex with two processes",
)

MUTEX_ACSL = ACSLSpecification(
    c_code="""/* Mutex implementation in C with ACSL */
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
""",
    acsl_annotations=[
        "mutex_invariant: at most 1 in critical section",
        "lock_valid: lock is boolean",
        "Acquire ensures lock is held",
        "Release ensures lock is free",
    ],
    description="Mutex implementation with ACSL contracts",
)


# Dining Philosophers - Classic deadlock example
DINING_PHILOSOPHERS_PROMELA = PromelaModel(
    source_code="""/* Dining Philosophers - Has Deadlock */
#define N 3

byte fork[N];
byte eating[N];

inline pick_forks(i) {
    atomic {
        fork[i] == 0;
        fork[(i+1) % N] == 0;
        fork[i] = 1;
        fork[(i+1) % N] = 1;
    }
}

inline put_forks(i) {
    fork[i] = 0;
    fork[(i+1) % N] = 0;
}

proctype Philosopher(byte i) {
    do
    :: /* think */
       pick_forks(i);
       eating[i] = 1;
       assert(eating[i] == 1);
       eating[i] = 0;
       put_forks(i);
    od
}

init {
    byte i = 0;
    do
    :: i < N ->
        run Philosopher(i);
        i++;
    :: i >= N -> break;
    od
}

/* This should find deadlock */
ltl no_deadlock { []<> (eating[0] == 1 || eating[1] == 1 || eating[2] == 1) }
""",
    ltl_properties=["[]<> (eating[0] == 1 || eating[1] == 1 || eating[2] == 1)"],
    description="Dining Philosophers with potential deadlock",
)


def get_example(name: str) -> tuple[PromelaModel | None, ACSLSpecification | None]:
    """
    Get example models by name.

    Args:
        name: Example name ('mutex' or 'dining_philosophers')

    Returns:
        Tuple of (PromelaModel, ACSLSpecification) - either may be None
    """
    examples = {
        "mutex": (MUTEX_PROMELA, MUTEX_ACSL),
        "dining_philosophers": (DINING_PHILOSOPHERS_PROMELA, None),
    }
    return examples.get(name, (None, None))
