#include <stdbool.h> // For bool type, though not strictly used in this example

// Shared variables, declared as volatile to indicate they can change
// unexpectedly from a single thread's perspective (important for concurrency reasoning).
// 'lock' serves as a simple flag for mutual exclusion.
volatile int lock = 0; // 0: unlocked, 1: locked. This is our flawed mutex.

// 'critical_section_counter' tracks how many processes are currently in the critical section.
// For mutual exclusion, this value should ideally never exceed 1.
volatile int critical_section_counter = 0;

/*@
  @ requires \true; // No specific preconditions for main in this demonstration.
  @ ensures lock == 0 && critical_section_counter == 0; // Ensures system returns to initial state.
  @ assigns lock, critical_section_counter; // main modifies these global variables.
*/
int main() {
    // Initial state assertions: Verify that the system starts in an expected state.
    //@ assert lock == 0;
    //@ assert critical_section_counter == 0;

    // --- Simulation of a specific interleaving that causes a race condition ---
    // This sequence demonstrates how a simple flag-based lock fails to ensure mutual exclusion.
    // We simulate the steps of two processes (P0 and P1) in an interleaved manner.

    // Process 0: Request Access (Step 1 - Check Lock)
    // P0 checks the 'lock' variable. Assume P0 reads 'lock' as 0 (unlocked).
    // At this point, P0 is preempted by the scheduler before it can set the lock.

    // Process 1: Request Access (Step 1 - Check Lock)
    // P1 checks the 'lock' variable. Assume P1 also reads 'lock' as 0 (unlocked).
    // P1 is also preempted before it can set the lock.

    // At this point, both P0 and P1 have observed the lock to be free (lock == 0).
    // They both believe they are clear to enter the critical section.

    // Process 0: Enter Critical Section (Step 2 - Acquire Lock and Enter)
    // P0 resumes execution. It sets the 'lock' to 1 and increments the counter,
    // thereby entering its critical section.
    lock = 1;
    critical_section_counter++;
    //@ assert lock == 1; // P0 believes it has successfully acquired the lock.
    //@ assert critical_section_counter == 1; // P0 believes it is the sole occupant of the CS.

    // P0 is preempted again, while it is inside the critical section.

    // Process 1: Enter Critical Section (Step 2 - Acquire Lock and Enter)
    // P1 resumes execution. It also sets the 'lock' to 1 and increments the counter,
    // thereby entering its critical section.
    // This is where the race condition manifests: P1 enters even though P0 is already inside.
    lock = 1; // P1 overwrites 'lock' with 1 (no change, but it's its attempt to acquire).
    critical_section_counter++; // P1 increments the counter, now it's 2!

    // --- Mutual Exclusion Violation Detection ---
    // At this point, both P0 and P1 are simultaneously in the critical section.
    // This assertion checks the mutual exclusion property: at most one process in CS.
    // Frama-C's value analysis (or WP with appropriate modeling) will report a potential violation here,
    // as 'critical_section_counter' is 2, not 1.
    //@ assert critical_section_counter == 1; // ERROR: This assertion will fail, as critical_section_counter is 2.

    // --- Process 0: Leave Critical Section ---
    // P0 finishes its critical section work and releases the lock.
    critical_section_counter--; // Counter becomes 1.
    lock = 0; // Lock is released (set to 0).

    // --- Process 1: Leave Critical Section ---
    // P1 finishes its critical section work and releases the lock.
    critical_section_counter--; // Counter becomes 0.
    lock = 0; // Lock is released (set to 0).

    // Final state assertions: Verify that the system returns to a clean state.
    //@ assert lock == 0;
    //@ assert critical_section_counter == 0;

    return 0;
}