// Promela model for a Mutual Exclusion System using a Binary Semaphore

// Shared variables
byte critical_section_count = 0; // Tracks the number of processes currently in the critical section.
                                 // Used to verify mutual exclusion: should never exceed 1.

byte sem = 1; // Binary semaphore:
              //   1 means the critical section is available (unlocked).
              //   0 means the critical section is taken (locked).
              // Initialized to 1, as the critical section is initially free.

bool P1_request = false; // Flag indicating that Process 1 is requesting access to the critical section.
bool P2_request = false; // Flag indicating that Process 2 is requesting access to the critical section.
                         // These flags are used for verifying liveness properties (deadlock/starvation freedom).

bool P1_in_CS = false; // Flag indicating that Process 1 is currently inside the critical section.
bool P2_in_CS = false; // Flag indicating that Process 2 is currently inside the critical section.
                       // These flags are also used for verifying liveness properties.

// Process P1: Repeatedly tries to enter its critical section
proctype P1() {
    do
    :: non_critical_section_P1:
        // Simulate some work in the non-critical section
        skip;

        P1_request = true; // P1 indicates its intention to enter the critical section.

        // P operation (acquire semaphore / lock mutex):
        // The 'atomic' block ensures that the check (sem > 0) and the decrement (sem--)
        // happen as a single, indivisible operation. This prevents race conditions
        // on the semaphore variable itself, ensuring its integrity.
        // If sem is 0, the process blocks here until sem becomes > 0.
        atomic {
            (sem > 0) -> sem--;
        }

        P1_request = false; // P1 has successfully acquired the mutex; it's no longer just "requesting".

        // Critical Section for P1
        critical_section_count++; // Increment count as P1 enters CS
        P1_in_CS = true;          // Set flag that P1 is in CS
        // Simulate work inside the critical section
        skip;
        P1_in_CS = false;         // Clear flag as P1 leaves CS
        critical_section_count--; // Decrement count as P1 leaves CS

        // V operation (release semaphore / unlock mutex):
        // The 'atomic' block ensures that the increment (sem++) is an indivisible operation.
        // This makes the critical section available for another process.
        atomic {
            sem++;
        }
    od
}

// Process P2: Repeatedly tries to enter its critical section
proctype P2() {
    do
    :: non_critical_section_P2:
        // Simulate some work in the non-critical section
        skip;

        P2_request = true; // P2 indicates its intention to enter the critical section.

        // P operation (acquire semaphore / lock mutex)
        atomic {
            (sem > 0) -> sem--;
        }

        P2_request = false; // P2 has successfully acquired the mutex.

        // Critical Section for P2
        critical_section_count++; // Increment count as P2 enters CS
        P2_in_CS = true;          // Set flag that P2 is in CS
        // Simulate work inside the critical section
        skip;
        P2_in_CS = false;         // Clear flag as P2 leaves CS
        critical_section_count--; // Decrement count as P2 leaves CS

        // V operation (release semaphore / unlock mutex)
        atomic {
            sem++;
        }
    od
}

// Initialization process: Starts both P1 and P2
init {
    run P1();
    run P2();
}