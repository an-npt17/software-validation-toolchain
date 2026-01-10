/* 
 * Simple mutual exclusion example using a binary semaphore
 * Demonstrates basic SPIN verification with LTL properties
 */

mtype = { acquire, release };
chan sem = [0] of { mtype };  /* binary semaphore */

/* Track critical section occupancy */
bool in_cs[2] = false;

/* LTL Properties to verify */

/* Safety: Mutual exclusion - never both processes in critical section */
ltl mutual_exclusion { []!(in_cs[0] && in_cs[1]) }

/* Liveness: If a process wants to enter, it eventually does */
ltl progress_p0 { [](<> in_cs[0]) }
ltl progress_p1 { [](<> in_cs[1]) }

/* Deadlock freedom - at least one process makes progress */
ltl no_starvation { [](<>(in_cs[0] || in_cs[1])) }

/* Initialize semaphore */
init {
    sem!release;  /* semaphore starts available */
    run process(0);
    run process(1);
}

/* Generic process that repeatedly enters and exits critical section */
proctype process(byte id) {
    do
    :: true ->
        /* Request entry to critical section */
        sem?acquire;
        
        /* Enter critical section */
        in_cs[id] = true;
        
        /* Check mutual exclusion invariant */
        assert(in_cs[1-id] == false);
        
        /* Simulate work in critical section */
        skip;
        
        /* Leave critical section */
        in_cs[id] = false;
        
        /* Release semaphore */
        sem!release;
        
        /* Non-critical section work */
        skip;
    od
}

/*
 * To verify this model with SPIN:
 *
 * 1. Save as mutex.pml
 * 2. Run verification:
 *    spin -a mutex.pml              # Generate verifier
 *    gcc -o pan pan.c              # Compile verifier
 *    ./pan -a                      # Run verification
 *
 * 3. Check specific LTL property:
 *    spin -a -f "[]!(in_cs[0] && in_cs[1])" mutex.pml
 *    gcc -o pan pan.c
 *    ./pan -a
 *
 * 4. For more detailed output:
 *    ./pan -a -f                   # Full statespace search
 *    ./pan -a -N mutual_exclusion  # Check specific LTL claim
 */
