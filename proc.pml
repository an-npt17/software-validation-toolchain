/*
 * Dining Philosophers — Deadlock-prone model
 * N philosophers, N forks
 * Each philosopher picks LEFT fork first, then RIGHT fork
 * This ordering allows circular wait → deadlock
 */

#define N 3

/* fork[i] == 0 : free
 * fork[i] == 1 : held
 */
byte fork[N];
byte eating[N];

/* pick left fork */
inline pick_left(i) {
    fork[i] == 0;        /* guard */
    fork[i] = 1;
}

/* pick right fork */
inline pick_right(i) {
    fork[(i+1)%N] == 0; /* guard */
    fork[(i+1)%N] = 1;
}

/* put both forks back */
inline put_forks(i) {
    fork[i] = 0;
    fork[(i+1)%N] = 0;
}

/* Philosopher process */
proctype Philosopher(byte id)
{
    do
    ::  /* thinking */

        /* critical ordering that allows deadlock */
        pick_left(id);
        pick_right(id);

        /* eating section */
        eating[id] = 1;
        /* safety assertion: a philosopher is indeed eating */
        assert(eating[id] == 1);
        eating[id] = 0;

        put_forks(id);
    od
}

/* system initialization */
init {
    atomic {
        byte i = 0;
        do
        :: i < N ->
            run Philosopher(i);
            i++
        :: else -> break
        od
    }
}
ltl no_deadlock {[]<> (eating[0] || eating[1] || eating[2])}
